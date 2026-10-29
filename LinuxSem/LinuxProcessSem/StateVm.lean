/-
  * LinuxProcessSem.StateVm — VmMaps helpers

  What lives here, in order:

  - the interval arithmetic over unsigned values in `Z` (`iv_overlap`,
    `region_free` and its three lemmas, `map_remove`, `reserved_top`,
    `iv_subtract`, `maps_subtract`, `maps_subtract_all`);
  - the nonemptiness property of a ledger list (`entries_nonzero` and its
    three closure lemmas), the two 64-bit round-trip facts the remnant
    arithmetic needs (`bv_unsigned_range_u64`, `bv_unsigned_Z_to_bv_u64`),
    and the three nonemptiness lemmas that go with them
    (`iv_subtract_nonzero`, `maps_subtract_nonzero`,
    `maps_subtract_all_nonzero`);
  - the backed view of a ledger (`vm_backed_maps`) and the page
    bookkeeping for lazy anonymous mappings (`page_base_of` through
    `materialize_accesses`, `vm_backed_bytes`, `vm_backing_used`,
    `vm_backing_within_limit`, `materialize_model_accesses`,
    `page_outside_range`, `vm_forget_range`, and the two
    `materialize_model_accesses_*` lemmas, plus `write_accesses` /
    `syscall_effect_accesses`);
  - the sparse-backing constructors and movers (`lazy_interior`,
    `vm_add_lazy`, `page_in_half_open`, `move_page_base`,
    `vm_resize_backing`);
  - the placement predicates (`map_contains`, `map_has`,
    `noaccess_pages_owned`, `vm_noaccess_entries_nonzero`,
    `noaccess_pages_owned_nonzero`).

  TRUST BOUNDARY: this file is part of the trusted specification.


  - `vm_limit`, `vm_maps` and `vm_noaccess` are `VmMaps` fields, so they
    are structure projections here (`(m_vmmaps m).vm_limit`, `h.vm_maps`,
    `h.vm_noaccess`).
  - `materialize_model_accesses_frame` names the model's SUBSYSTEM fields
    (`m'.m_fd`, `m'.m_io`, …) rather than through whole-subsystem accessors
    (`m_fd m`/`m_io m`/…): `StateLedger.lean` exposes only the FIELD-level
    accessors (`m_fds`, `m_stdin`, …), and the subsystem ones are absent
    because nothing reads them.  The statement is the same, one projection
    per subsystem.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.StateLedger

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/- =========================================================================
   VmMaps helpers — interval arithmetic in Z over unsigned values
   ========================================================================= -/

/-- Do `[lo1,lo1+n1)` and `[lo2,lo2+n2)` overlap?  Computed in `Z`: the
    sums cannot wrap. -/
def iv_overlap (a1 n1 a2 n2 : word) : Bool :=
  decide ((a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int)) &&
  decide ((a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int))

/-- Is `[lo, lo+n)` disjoint from every live mapping? -/
def region_free (maps : List (word × word)) (lo n : word) : Bool :=
  match maps with
  | [] => true
  | (a, sz) :: r => !(iv_overlap lo n a sz) && region_free r lo n

/-- `region_free` read entry by entry: a free region misses EVERY entry of
    the ledger it was checked against, wherever that entry sits in the
    list. -/
theorem region_free_In :
    ∀ (maps : List (word × word)) (lo n a sz : word),
      region_free maps lo n = true → (a, sz) ∈ maps →
      iv_overlap lo n a sz = false := by
  intro maps
  induction maps with
  | nil =>
      intro lo n a sz _ Hin
      simp at Hin
  | cons hd r ih =>
      intro lo n a sz Hfree Hin
      obtain ⟨b, s⟩ := hd
      simp only [region_free, Bool.and_eq_true, List.mem_cons] at Hfree Hin
      rcases Hin with h | h
      · cases h
        simpa using Hfree.1
      · exact ih lo n a sz Hfree.2 h

/-- …and the converse, which is how a freeness claim is DISCHARGED from a
    per-entry argument. -/
theorem region_free_intro (maps : List (word × word)) (lo n : word)
    (H : ∀ a sz, (a, sz) ∈ maps → iv_overlap lo n a sz = false) :
    region_free maps lo n = true := by
  induction maps with
  | nil => rfl
  | cons hd r ih =>
      obtain ⟨b, s⟩ := hd
      simp only [region_free, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · simpa using H b s (by simp)
      · exact ih (fun a sz hin => H a sz (by simp [hin]))

/-- …and the same fold read the OTHER way: a region the ledger refuses is
    refused by a NAMED entry.  `region_free_In` says what freeness gives
    you; this says what its failure gives you, which is what a caller needs
    in order to ask whether the entry that refused is a real one.
    `vm_noaccess` is where that question has an answer worth writing down —
    see `entries_nonzero` below. -/
theorem region_free_false (maps : List (word × word)) (lo n : word)
    (H : region_free maps lo n = false) :
    ∃ a sz, (a, sz) ∈ maps ∧ iv_overlap lo n a sz = true := by
  induction maps with
  | nil => simp [region_free] at H
  | cons hd r ih =>
      obtain ⟨b, s⟩ := hd
      simp only [region_free, Bool.and_eq_false_iff] at H
      rcases H with H | H
      · exact ⟨b, s, by simp, by simpa using H⟩
      · obtain ⟨a, sz, hin, hov⟩ := ih H
        exact ⟨a, sz, by simp [hin], hov⟩

/-- Drop any mapping based at `lo` (munmap of a whole anonymous mapping). -/
def map_remove (maps : List (word × word)) (lo : word) : List (word × word) :=
  List.filter (fun p => !(p.1 == lo)) maps

/-- Top of the reserved image: the least address at or above every reserved
    (page-rounded LOAD) segment `[a, a+sz)`.  On Linux the initial program
    break `mm->start_brk` sits just above the end of BSS, i.e. above the
    loaded image; a `brk` request BELOW it is invalid and returns the break
    unchanged (see `Mmap.min_brk` / `Mmap.brk_spec`).  Empty image => 0.
    Computed in `Z` over unsigned values (sums cannot wrap, matching the old
    unbounded-`N` semantics). -/
def reserved_top : List (word × word) → Int
  | [] => 0
  | (a, sz) :: r => max ((a.toNat : Int) + (sz.toNat : Int)) (reserved_top r)

/-- Subtract the half-open interval `[lo, hi)` from every mapping, keeping
    the parts that fall OUTSIDE it (each mapping may split into a left
    and/or a right remnant, or vanish).  A `brk` SHRINK uses it in two
    deliberately different ways (see `Mmap.brk_model_next`): `vm_maps`
    drops the logical, byte-granular heap tail `[new_break, old_break)`,
    preserving exact live-byte budget accounting, while `vm_noaccess` drops
    only the page-rounded range named by `Mmap.brk_unmaps`.  The latter is
    the kernel's actual `do_vmi_align_munmap` interval and is also what the
    running program sees in `eff_unmaps`.  Higher anonymous mmaps and lower
    mappings survive, and one straddling record is truncated.

    Arithmetic in `Z` over unsigned values (no wrapping); the remnant
    bases/sizes fit in 64 bits by construction, so the `Z_to_bv`
    round-trips are lossless.  The interval ENDPOINTS are taken in `Z` too,
    for the same reason: an end of exactly 2^64 is a legitimate half-open
    bound, so a caller that reconstructed it as a `word` sum could wrap it
    to 0 and subtract the wrong range.  In `Z` that is unrepresentable —
    callers pass `bv_unsigned lo + bv_unsigned len` directly. -/
def iv_subtract (a sz : word) (loZ hiZ : Int) : List (word × word) :=
  let aZ := (a.toNat : Int)
  let szZ := (sz.toNat : Int)
  let left :=
    if aZ < loZ then [(a, BitVec.ofInt 64 (min szZ (loZ - aZ)))] else []
  let right :=
    if hiZ < aZ + szZ then
      [(BitVec.ofInt 64 (max aZ hiZ),
        BitVec.ofInt 64 (aZ + szZ - max aZ hiZ))]
    else []
  left ++ right

def maps_subtract (maps : List (word × word)) (lo hi : Int) :
    List (word × word) :=
  match maps with
  | [] => []
  | (a, sz) :: r => iv_subtract a sz lo hi ++ maps_subtract r lo hi

/-- Remove every inaccessible interval from `maps`.  The result is the
    model's BACKED view: anonymous bytes that are presently readable and
    writable.  This is intentionally a conservative commit-time backing
    guarantee, not first-touch accounting, physical frames, RSS, swap, or a
    page-table model. -/
def maps_subtract_all (maps cuts : List (word × word)) :
    List (word × word) :=
  match cuts with
  | [] => maps
  | (a, n) :: rest =>
      maps_subtract_all
        (maps_subtract maps (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))
        rest

/-- A ledger list whose every entry names at least one BYTE.

    Why a ledger would want to say so: `iv_overlap` reports an overlap
    against a ZERO-SIZE interval strictly inside the queried range —
    `iv_overlap lo n a 0` is `lo < a && a < lo + n`, which is true for any
    `a` strictly between — so a vacuous entry makes `region_free` false over
    a region it names no byte of.  Every consumer of `region_free` is
    therefore reading a gate that a vacuous entry can close for no reason,
    and a reader who wants to know whether that can happen has to go and
    inspect every writer of the list.  This property, and the three closure
    lemmas under it, are where that inspection is done once.

    The list-building operations are the whole of what has to be checked,
    because no writer in this tree builds a ledger list any other way: the
    lists start empty at `init_model` and grow by `cons`, shrink by
    `maps_subtract`, and (for `brk`) shrink by
    `Mmap.maps_subtract_ranges`, which is a fold of `maps_subtract`.

    `maps_subtract` is the interesting one.  It is not obvious from
    `iv_subtract` that a cut cannot leave an empty remnant, since both
    remnants are built with a `Z.min` and a subtraction; what makes it true
    is that each remnant is EMITTED only under the guard that makes it
    nonempty (`aZ < loZ` for the left, `hiZ < aZ + szZ` for the right).  A
    cut of a nonempty entry is therefore nonempty or absent, never present
    and vacuous. -/
def entries_nonzero (maps : List (word × word)) : Prop :=
  ∀ a n, (a, n) ∈ maps → 0 < (n.toNat : Int)

theorem entries_nonzero_nil : entries_nonzero [] := by
  intro a n h
  simp at h

/-- The computational way in, for a fixture whose list is a literal: a
  `decide` on the `forallb` discharges the property without the call
    site taking the list apart by hand. -/
theorem entries_nonzero_forallb (maps : List (word × word))
    (H : maps.all (fun p => decide (0 < (p.2.toNat : Int))) = true) :
    entries_nonzero maps := by
  induction maps with
  | nil =>
      intro a n h
      simp at h
  | cons hd r ih =>
      intro b s Hin
      obtain ⟨a, n⟩ := hd
      simp only [List.all, Bool.and_eq_true] at H
      rcases List.mem_cons.mp Hin with h | h
      · cases h
        simpa using H.1
      · exact ih H.2 b s h

theorem entries_nonzero_cons (a n : word) (r : List (word × word))
    (Hn : 0 < (n.toNat : Int)) (Hr : entries_nonzero r) :
    entries_nonzero ((a, n) :: r) := by
  intro b s Hin
  rcases List.mem_cons.mp Hin with h | h
  · cases h
    exact Hn
  · exact Hr b s h

/-- The two small round-trip facts the remnant arithmetic needs.  `Mm/Mremap.lean`
    carries its own copies under its own names; these are the ones the
    lemmas in this file use. -/
theorem bv_unsigned_range_u64 (w : word) :
    0 ≤ (w.toNat : Int) ∧ (w.toNat : Int) < two_pow_64 := by
  have h := w.isLt
  have h2 : (w.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast h
  exact ⟨Int.natCast_nonneg w.toNat, by simpa [two_pow_64] using h2⟩

theorem bv_unsigned_Z_to_bv_u64 (z : Int) (hz : 0 ≤ z ∧ z < two_pow_64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z := by
  obtain ⟨h0, h1⟩ := hz
  rw [BitVec.toNat_ofInt]
  have hlt : z < ((2 ^ 64 : Nat) : Int) := by simpa [two_pow_64] using h1
  rw [Int.emod_eq_of_lt h0 hlt]
  exact Int.toNat_of_nonneg h0

/-- Cutting a NONEMPTY entry leaves nonempty remnants: each of the two is
    emitted under exactly the guard that makes its size positive. -/
theorem iv_subtract_nonzero (a sz : word) (loZ hiZ : Int)
    (Hsz : 0 < (sz.toNat : Int)) :
    entries_nonzero (iv_subtract a sz loZ hiZ) := by
  intro b s Hin
  have Ha := bv_unsigned_range_u64 a
  have Hs := bv_unsigned_range_u64 sz
  unfold iv_subtract at Hin
  dsimp only at Hin
  by_cases hl : (a.toNat : Int) < loZ
  · rw [ite_eq_left hl] at Hin
    by_cases hr : hiZ < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left hr] at Hin
      rw [List.singleton_append] at Hin
      rcases List.mem_cons.mp Hin with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bv_unsigned_Z_to_bv_u64 _ ⟨by omega, by omega⟩]
        omega
      · rw [List.mem_singleton] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bv_unsigned_Z_to_bv_u64 _ ⟨by omega, by omega⟩]
        omega
    · rw [ite_eq_right hr] at Hin
      rw [List.singleton_append] at Hin
      rw [List.mem_cons] at Hin
      rcases Hin with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [bv_unsigned_Z_to_bv_u64 _ ⟨by omega, by omega⟩]
        omega
      · simp at h
  · rw [ite_eq_right hl] at Hin
    by_cases hr : hiZ < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left hr] at Hin
      rw [List.nil_append] at Hin
      rw [List.mem_singleton] at Hin
      simp only [Prod.mk.injEq] at Hin
      obtain ⟨rfl, rfl⟩ := Hin
      rw [bv_unsigned_Z_to_bv_u64 _ ⟨by omega, by omega⟩]
      omega
    · rw [ite_eq_right hr] at Hin
      rw [List.nil_append] at Hin
      simp at Hin

theorem maps_subtract_nonzero (maps : List (word × word)) (loZ hiZ : Int)
    (H : entries_nonzero maps) :
    entries_nonzero (maps_subtract maps loZ hiZ) := by
  induction maps with
  | nil =>
      intro b s hin
      simp [maps_subtract] at hin
  | cons hd r ih =>
      obtain ⟨a, sz⟩ := hd
      intro b s hin
      simp only [maps_subtract, List.mem_append] at hin
      rcases hin with hin | hin
      · exact iv_subtract_nonzero a sz loZ hiZ (H a sz (by simp)) b s hin
      · exact ih (fun x y hx => H x y (by simp [hx])) b s hin

theorem maps_subtract_all_nonzero :
    ∀ (cuts maps : List (word × word)),
      entries_nonzero maps → entries_nonzero (maps_subtract_all maps cuts) := by
  intro cuts
  induction cuts with
  | nil =>
      intro maps H
      exact H
  | cons hd rest ih =>
      intro maps H
      obtain ⟨a, n⟩ := hd
      simp only [maps_subtract_all]
      exact ih (maps_subtract maps (a.toNat : Int)
          ((a.toNat : Int) + (n.toNat : Int)))
        (maps_subtract_nonzero maps (a.toNat : Int)
          ((a.toNat : Int) + (n.toNat : Int)) H)

def vm_backed_maps (h : VmMaps) : List (word × word) :=
  maps_subtract_all h.vm_maps h.vm_noaccess

/- ** Atomic first-access accounting

    The instruction interpreter reports successful data-memory accesses as
    `(address, byte_count)` pairs.  These helpers turn the complete report
    for one instruction into the pages that a lazy anonymous mapping would
    need to materialize.  They are deliberately pure:
    `materialize_accesses` returns the complete new ledger or `None`, so a
    cross-page access cannot spend one page and then fail on the next.

    `lazy` contains page-aligned MAP_NORESERVE ranges — enforced by
    `vm_add_lazy`, which records only a reservation's aligned interior, so
    the bytes `vm_backing_used` subtracts are exactly the bytes a first
    touch can charge back.  A reported page is charged only when one lazy
    range contains the whole page; ordinary mapped memory remains part of
    `used` already.  `materialized` stores page bases, and insertion is
    idempotent, so repeated reads or writes do not charge twice.  This is an
    abstract backing guarantee, not physical frames, RSS, swap, or
    page-table state. -/
def page_base_of (z : Int) : word :=
  BitVec.ofInt 64 ((z / page_size) * page_size)

def page_base (a : word) : word := page_base_of (a.toNat : Int)

def page_mem (p : word) (pages : List word) : Bool :=
  pages.any (fun q => p == q)

def page_insert (p : word) (pages : List word) : List word :=
  if page_mem p pages then pages else p :: pages

/-- The byte cursor advances in `Z`, not by bitvector `+`.  BvBase's second
    rule is that range arithmetic is done in `Z` over `bv_unsigned` so it
    cannot wrap; stepping a `word` here would fold the top of the address
    space back onto page 0 and charge a page the access never touched.  That
    direction is an over-charge, and no reported access can reach it while
    `alloc_top` sits far below 2^64 (a stack's width under 2^47 for any
    `Run.valid_sp`) — but the rule is the rule, and the cursor is the one
    place this file broke it. -/
def access_pages_acc (base : Int) (n : Nat) (pages : List word) : List word :=
  match n with
  | 0 => pages
  | k + 1 =>
      access_pages_acc (base + 1) k (page_insert (page_base_of base) pages)

def access_pages (a : word) (n : Nat) : List word :=
  access_pages_acc (a.toNat : Int) n []

def accesses_pages (accesses : List (word × Nat)) (pages : List word) :
    List word :=
  match accesses with
  | [] => pages
  | (a, n) :: rest =>
      accesses_pages rest (access_pages_acc (a.toNat : Int) n pages)

def page_in_ranges (p : word) (ranges : List (word × word)) : Bool :=
  ranges.any (fun r =>
    let lo := (r.1.toNat : Int)
    let hi := lo + (r.2.toNat : Int)
    decide (lo ≤ (p.toNat : Int)) &&
      decide ((p.toNat : Int) + page_size ≤ hi))

def newly_materialized_pages (lazy : List (word × word))
    (materialized : List word) (accesses : List (word × Nat)) : List word :=
  List.filter (fun p => page_in_ranges p lazy && !(page_mem p materialized))
    (accesses_pages accesses [])

def materialize_accesses (lazy : List (word × word))
    (materialized : List word) (used limit : Int)
    (accesses : List (word × Nat)) : Option (List word) :=
  let new := newly_materialized_pages lazy materialized accesses
  match new with
  | [] => some materialized
  | _ =>
      if used + (new.length : Int) * page_size ≤ limit
      then some (new ++ materialized)
      else none

/-- Accessible anonymous bytes in a VM ledger: everything mapped, less every
    inaccessible interval.  This measures a `VmMaps` alone and knows nothing
    of sparse provenance, so it is NOT a live process's backing charge —
    `vm_backing_used` just below is, and the two differ by the lazy ranges
    it cuts out and the materialized pages it adds back.

    BOTH ARE LIVE, and which one is right depends on the question.  Ask this
    one how much of a ledger is accessible: `vm_live_bytes`/
    `vm_backed_bytes` pairs in `Checks/Cases/Mm/Mmap.lean` state a fixed
    commit's two accounts side by side, virtual occupancy against exposed
    capacity, and there is no `Model` at those sites to have a lazy ledger.
    `Common/AllocSim.v`'s pure allocator algebra also asks it, and may: its
    `vm_model` packages a ledger with EMPTY sparse state, so
    `vm_backing_used (vm_model h) = vm_backed_bytes h` holds for every `h`
    by construction, not by accident of the corpus.  The live brk budget is
    a different predicate on a real `Model` (`Sys/Mm/Mmap.brk_grow_ok`) and
    asks `vm_backing_used`.

    It lives here, beside the measure it is contrasted with, because
    separated from that contrast it reads as a duplicate of
    `vm_backing_used` with no callers. -/
def vm_backed_bytes (h : VmMaps) : Int :=
  live_bytes (vm_backed_maps h)

/-- Backing already consumed by a process: eagerly backed readable mappings
    with every lazy reservation cut out, plus the lazy pages charged so far.
    The ledgers are maintained together by the VM syscall helpers below.

    INVARIANT, load-bearing: EVERY LAZY RANGE IS PAGE-ALIGNED.  The
    subtraction here is by whole byte extent, while `page_in_ranges` charges
    a page back only when ONE lazy range contains that whole page.  Those
    two agree only on page-aligned ranges; on an unaligned one the bytes
    between them leave the budget and no access can restore them, which is
    an under-charge — the direction that grants an allocation the kernel
    refuses.

    The invariant holds by construction rather than by argument.  Exactly
    two operations put a range INTO `m_vm_lazy`, and both clip to
    `lazy_interior`: `vm_add_lazy`, for a fresh MAP_NORESERVE mapping, and
    `vm_resize_backing`, for the destination of an mremap that carries lazy
    provenance.  `vm_forget_range` and the `maps_subtract` inside
    `vm_resize_backing` only remove bytes, and removing from an aligned
    range by aligned bounds leaves an aligned range.

    A THIRD way to add one would have to clip the same way; the invariant is not
    re-derivable from the call sites, because neither constructor checks its caller.
    Every write to either ledger goes through `with_vm_backing`, so that is where to
    find the current set of writers, and where a new one has to appear. The
    alternative, making this subtraction page-granular so no precondition is needed
    at all, is deliberately not taken: it would move a definition ~30 sites across
    Common/ and the examples depend on, to close a state nothing can build. that
    witness is in the file's port, `Checks/Cases/Mm/Mmap.lean`, which this file does
    not depend on, so it is not cited here. -/
def vm_backing_used (m : Model) : Int :=
  live_bytes
      (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)) +
    (m_vm_materialized m).length * page_size

/-- The one backed-memory gate used by VM operations.  It is stated over
    `Model`, not `VmMaps`, because sparse-mapping provenance and first-touch
    charges live in `VmState`.  Testing a reconstructed `vm_backed_bytes`
    total here would charge every MAP_NORESERVE reservation eagerly. -/
def vm_backing_within_limit (m : Model) : Bool :=
  decide (vm_backing_used m ≤ (m_vmmaps m).vm_limit)

def materialize_model_accesses (m : Model) (accesses : List (word × Nat)) :
    Option Model :=
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
      (vm_backing_used m) ((m_vmmaps m).vm_limit) accesses with
  | some pages => some (with_vm_backing (m_vm_lazy m) pages m)
  | none => none

def page_outside_range (lo hi : Int) (p : word) : Bool :=
  !(decide (lo ≤ (p.toNat : Int)) && decide ((p.toNat : Int) < hi))

/-- Forget sparse-backing metadata for an unmapped or replaced interval.
    Range subtraction handles partial lazy reservations; materialized pages
    are page aligned, and every caller supplies page-aligned bounds. -/
def vm_forget_range (lo hi : Int) (m : Model) : Model :=
  with_vm_backing
    (maps_subtract (m_vm_lazy m) lo hi)
    (List.filter (page_outside_range lo hi) (m_vm_materialized m)) m

theorem materialize_model_accesses_no_lazy (m : Model)
    (accesses : List (word × Nat)) (Hlazy : m_vm_lazy m = []) :
    materialize_model_accesses m accesses = some m := by
  obtain ⟨fd, vm, io, fs, proc, lim, time⟩ := m
  obtain ⟨maps, lazy, mat⟩ := vm
  simp only [m_vm_lazy] at Hlazy
  subst Hlazy
  have hnil : ∀ ps : List word,
      List.filter
        (fun p => page_in_ranges p ([] : List (word × word)) &&
          !(page_mem p mat)) ps = [] := by
    intro ps
    simp [page_in_ranges]
  unfold materialize_model_accesses materialize_accesses newly_materialized_pages
  dsimp only [m_vm_lazy, m_vm_materialized]
  rw [hnil]
  rfl

/-- User-memory ranges named by a successful syscall effect.  Copy-from-user
    ranges were recorded while selecting the outcome; ordinary byte writes
    are copy-to-user destinations.  Zero-fill and symbolic-copy ranges are
    deliberately absent: creating or moving a lazy anonymous mapping must
    not materialize every untouched page. -/
def write_accesses : List (word × List byte) → List (word × Nat)
  | [] => []
  | (a, bs) :: rest => (a, bs.length) :: write_accesses rest

def syscall_effect_accesses (eff : SyscallEffect) : List (word × Nat) :=
  eff.eff_copyins ++ write_accesses eff.eff_writes

theorem materialize_model_accesses_frame (m : Model)
    (accesses : List (word × Nat)) (m' : Model)
    (Haccount : materialize_model_accesses m accesses = some m') :
    m'.m_fd = m.m_fd ∧
    m_vmmaps m' = m_vmmaps m ∧
    m_vm_lazy m' = m_vm_lazy m ∧
    m'.m_io = m.m_io ∧
    m'.m_fsys = m.m_fsys ∧
    m'.m_proc = m.m_proc ∧
    m'.m_lim = m.m_lim := by
  unfold materialize_model_accesses at Haccount
  cases hpages : materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
      (vm_backing_used m) ((m_vmmaps m).vm_limit) accesses with
  | none => simp [hpages] at Haccount
  | some pages =>
      simp only [hpages, Option.some.injEq] at Haccount
      cases Haccount
      obtain ⟨fd, vm, io, fs, proc, lim, time⟩ := m
      obtain ⟨maps, lazy, mat⟩ := vm
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The page-aligned interior of a reservation: exactly the pages a first
    touch can charge back.

    `vm_backing_used` subtracts a lazy range by its whole byte extent, while
    `page_in_ranges` charges a page back only when ONE range contains that
    whole page.  Those two agree only on page-aligned ranges.  On an
    unaligned one — or on a page split across two adjacent ranges — the
    bytes come off the budget and no access can ever put them back, which
    makes the memory FREE: an under-charge, the direction that lets the
    model grant an allocation the kernel refuses.

    Recording the interior rather than the request keeps both sides over the
    same bytes, so that state cannot be built.  Every caller is page-aligned
    already (`mmap` places on a page boundary and rounds the length up), so
    this is the identity on the reachable domain; it is here so the bad
    state is unconstructible rather than merely unreached.  An unaligned
    caller would record LESS than it asked for, which over-charges — the
    safe direction. -/
def lazy_interior (a n : word) : List (word × word) :=
  let lo := (a.toNat : Int)
  let hi := lo + (n.toNat : Int)
  let lo' := ((lo + page_size - 1) / page_size) * page_size
  let hi' := (hi / page_size) * page_size
  if lo' < hi' then
    [(BitVec.ofInt 64 lo', BitVec.ofInt 64 (hi' - lo'))]
  else []

def vm_add_lazy (a n : word) (m : Model) : Model :=
  with_vm_backing (lazy_interior a n ++ m_vm_lazy m) (m_vm_materialized m) m

/-- Move or resize the sparse-backing metadata belonging to one whole
    anonymous mapping.  `source_lazy` says the source is uniformly
    MAP_NORESERVE; callers reject mixed lazy/eager sources.  Materialized
    pages retain their source-relative offset, pages cut by a shrink are
    released, and a grown lazy tail starts unmaterialized.  Destination
    metadata is removed first so even a hand-built stale ledger cannot
    manufacture backing by colliding with the move. -/
def page_in_half_open (lo hi : Int) (p : word) : Bool :=
  decide (lo ≤ (p.toNat : Int)) && decide ((p.toNat : Int) < hi)

def move_page_base (old dst p : word) : word :=
  BitVec.ofInt 64 ((dst.toNat : Int) + ((p.toNat : Int) - (old.toNat : Int)))

def vm_resize_backing (source_lazy : Bool)
    (old old_n dst new_n : word) (m : Model) : Model :=
  let old_lo := (old.toNat : Int)
  let old_hi := old_lo + (old_n.toNat : Int)
  let dst_lo := (dst.toNat : Int)
  let dst_hi := dst_lo + (new_n.toNat : Int)
  let kept_lazy :=
    maps_subtract
      (maps_subtract (m_vm_lazy m) old_lo old_hi) dst_lo dst_hi
  let kept_pages :=
    List.filter (page_outside_range dst_lo dst_hi)
      (List.filter (page_outside_range old_lo old_hi)
        (m_vm_materialized m))
  let moved_pages :=
    if source_lazy then
      List.map (move_page_base old dst)
        (List.filter
          (fun p => page_in_half_open old_lo old_hi p &&
            decide ((p.toNat : Int) - old_lo < (new_n.toNat : Int)))
          (m_vm_materialized m))
    else []
  with_vm_backing
    (if source_lazy then lazy_interior dst new_n ++ kept_lazy else kept_lazy)
    (moved_pages ++ kept_pages) m

/-- Does ONE ledger interval contain the whole half-open range `[lo,lo+n)`?

    The predicate is NARROWER than the kernel's question, and deliberately
    so: the model never merges adjacent entries, so a range one kernel VMA
    covers can be spread across two model entries and answer "no" here.
    That is the safe direction for every caller — it declines or re-cuts
    where Linux would not, never the reverse.

    A "no" does not mean the same thing at every call site, so read the site
    rather than this comment: some decline on it and some only select a
    different arm.  Which are which is not restated here, because nothing
    would fail when the list went stale. -/
def map_contains (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any (fun p =>
    let aZ := (p.1.toNat : Int)
    let hiZ := aZ + (p.2.toNat : Int)
    decide (aZ ≤ (lo.toNat : Int)) &&
      decide ((lo.toNat : Int) + (n.toNat : Int) ≤ hiZ))

/-- Is `(lo, n)` exactly one of the live-mapping entries?  munmap's modeled
    case: the requested range coincides with a whole recorded mapping (see
    `Mmap.munmap_spec`). -/
def map_has (maps : List (word × word)) (lo n : word) : Bool :=
  maps.any (fun p => p.1 == lo && p.2 == n)

/-- The ledger invariant that keeps allocator placement off protected memory
    WITHOUT `vm_noaccess` ever being consulted.

    `vm_noaccess` is NOT a subset of `vm_maps`, deliberately: purpose (c)
    above documents the one exception, a brk shrink inside its final page,
    which drops the byte-granular tail `[vm_brk, PAGE_ALIGN vm_brk)` from
    `vm_maps` while the page-rounded protected range stays whole.  The
    weaker property below survives that exception and is still enough for
    every placement decision, because placement is PAGE granular:

      every protected byte lies on a page that some live `vm_maps` entry
      still touches.

    In the orphan state the truncated entry `[e0, vm_brk)` is that witness —
    the shrink TRUNCATES the owning entry rather than removing it, so a
    nonempty orphan forces the entry to reach into the orphan's page.
    `Checks/Examples.v` has
    `noaccess_pages_owned_brk_orphan` and
    `noaccess_pages_owned_fails_without_residual`, which check that this
    holds on the real shrunken state and fails on the counterfactual one
    where the residual entry is taken away.  Both halves are now proved on
    BUILT states, in `Checks/Cases/Mm/Mmap.lean`
    (`noaccess_pages_owned_brk_orphan`,
    `noaccess_pages_owned_fails_without_residual`), so this is no longer
    prose: `noaccess_pages_owned` is discharged on the shrunken state and
    refuted on the counterfactual one.

    The nonemptiness conjunct is not decoration: `iv_overlap` reports an
    overlap against a ZERO-size interval strictly inside the queried range,
    so without it a vacuous (empty) protected entry could block a request
    that touches no protected byte.  Every writer of `vm_noaccess` adds
    page-rounded, nonempty ranges and `iv_subtract` keeps remnants nonempty,
    so this costs nothing.

    `Mremap.mremap_fresh_avoids_noaccess` is the consumer: assuming this, a
    destination `mremap_fresh_b` accepts is disjoint from `vm_noaccess`,
    which is the property the predicate's comment argues informally.
    Proving the invariant PRESERVED by the nine writers of `vm_noaccess` is
    the remaining half, and is not done here. -/
def noaccess_pages_owned (h : VmMaps) : Prop :=
  ∀ a n,
    (a, n) ∈ h.vm_noaccess →
    0 < (n.toNat : Int) ∧
    ∀ x,
      ((a.toNat : Int) ≤ x ∧ x < (a.toNat : Int) + (n.toNat : Int)) →
      ∃ b s,
        (b, s) ∈ h.vm_maps ∧
        ((b.toNat : Int) < page_round_down_Z x + page_size ∧
          page_round_down_Z x < (b.toNat : Int) + (s.toNat : Int))

/-- The nonemptiness conjunct of that invariant, on its own.

    The two conjuncts are not equally hard.  The page-ownership half is the
    one no writer is yet shown to preserve, and it is why
    `Mremap.mremap_fresh_avoids_noaccess` takes the whole invariant as a
    hypothesis.  The NONEMPTINESS half is preserved by construction, and it
    is what every `region_free` reader of `vm_noaccess` actually leans on —
    `Madvise.madvise_dontneed_ok`'s third conjunct and `Mremap.mremap_ok`'s
    — because a vacuous entry closes a `region_free` gate over a range it
    names no byte of (see `entries_nonzero` above, and
    `Madvise.madvise_noaccess_decline_names_a_protected_byte` for the
    consumer).

    Separating it is what lets a consumer cite a fact the writers are shown
    to keep instead of assuming an invariant nothing establishes.
    `init_model` starts the list empty, and every writer builds the next one
    with `cons`, `maps_subtract` or `Mmap.maps_subtract_ranges`, so the
    closure lemmas above are the whole of what a writer needs.  `Mm/Mmap.lean`'s
    section "the protected ledger names real bytes" lists every writer, says
    which of the three things each does to the list, and carries a
    preservation lemma for each; `Mm/Mprotect.lean` has the one writer outside
    that file.  The writers that are named post-state functions get a lemma
    about the definition; the ones `mmap_spec` and `munmap_spec` write
    inline get a lemma that RESTATES the record, with the cost of that
    restatement stated where the lemmas are.

    WHAT IS STILL NOT A THEOREM is the composition: no statement in the tree
    concludes that a REACHABLE model satisfies this.  The base case and
    every writer are proved; the induction over the specs' own branch
    structure is not carried out, so a consumer takes this as a hypothesis
    and the step that discharges it is a reader's, made against that list of
    writers. -/
def vm_noaccess_entries_nonzero (h : VmMaps) : Prop :=
  entries_nonzero h.vm_noaccess

/-- The stronger invariant implies the weaker one, so a caller already
    carrying `noaccess_pages_owned` need not carry both. -/
theorem noaccess_pages_owned_nonzero (h : VmMaps)
    (H : noaccess_pages_owned h) : vm_noaccess_entries_nonzero h := by
  intro a n hin
  exact (H a n hin).1

/- =========================================================================
  Sanity checks — `decide` goals
   ========================================================================= -/

/-- Overlapping grants: `[0x1000, 0x3000)` and `[0x2000, 0x3000)` share
    `[0x2000, 0x3000)`. -/
example :
    iv_overlap (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x2000)
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) = true := by decide

/-- Adjacent grants — the second starts exactly where the first ends — do
    NOT overlap, and a region at the end of one entry is free. -/
example :
    iv_overlap (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) = false := by decide

example :
    region_free
      [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000),
       (BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)]
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) = false := by decide

example :
    region_free
      [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)]
      (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) = true := by decide

/-- `map_has` is exact-entry munmap, `map_contains` is containment. -/
example :
    map_has [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)]
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000) = true := by decide

example :
    map_contains [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000)]
      (BitVec.ofInt 64 0x1800) (BitVec.ofInt 64 0x800) = true := by decide

/-- A small ledger: maps `[0x1000, 0x3000)`, protected `[0x1800, 0x2000)`,
    lazy `[0x2000, 0x3000)`, one materialized page at `0x4000`.  The backed
    view is `[(0x1000, 0x800), (0x2000, 0x1000)]` (6144 accessible bytes);
    cutting the lazy range leaves `[(0x1000, 0x800)]` (2048), and the one
    materialized page adds 4096 back — 6144 in total. -/
private def vmFixture : Model :=
  with_vm_backing
    [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)]
    [BitVec.ofInt 64 0x4000]
    (mkModel []
      { mkVmMaps [] [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x2000)]
          0 0 0x100000 with
        vm_noaccess := [(BitVec.ofInt 64 0x1800, BitVec.ofInt 64 0x800)] }
      IEof [] none none none)

example : vm_backed_bytes (m_vmmaps vmFixture) = 6144 := by decide

example : vm_backing_used vmFixture = 6144 := by decide

/-- Lazy materialization: a 4-byte access at `0x2000` (inside the lazy
    reservation `[0x2000, 0x3000)`, all four bytes on page `0x2000`) charges
    exactly one page, and repeating the same access does not charge it
    again. -/
example :
    (materialize_model_accesses vmFixture
      [(BitVec.ofInt 64 0x2000, 4)]).map
        (fun m => m_vm_materialized m) =
      some [BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x4000] := by decide

example :
    (materialize_model_accesses vmFixture
      [(BitVec.ofInt 64 0x2000, 4), (BitVec.ofInt 64 0x2000, 4)]).map
        (fun m => m_vm_materialized m) =
      some [BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x4000] := by decide

example :
    (materialize_model_accesses vmFixture
      [(BitVec.ofInt 64 0x1000, 1)]).map
        (fun m => m_vm_materialized m) =
      some [BitVec.ofInt 64 0x4000] := by decide

/-- `vm_forget_range` on a page-aligned interval: the lazy reservation is
    cut to nothing and the materialized page inside the interval is
    forgotten, while the page outside it survives. -/
private def forgetFixture : Model :=
  with_vm_backing
    [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)]
    [BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x4000]
    (mkModel [] (mkVmMaps [] [] 0 0 0x100000) IEof [] none none none)

example : m_vm_lazy (vm_forget_range 0x2000 0x3000 forgetFixture) = [] := by
  decide

example :
    m_vm_materialized (vm_forget_range 0x2000 0x3000 forgetFixture) =
      [BitVec.ofInt 64 0x4000] := by decide

private def plainModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0x100000) IEof [] none none none

/-- `lazy_interior` clips to whole pages: a 0x800-byte request at 0x2000
    contains no full page and records nothing; a 0x1000-byte one records
    the page.  `vm_add_lazy` prepends exactly that interior. -/
example : lazy_interior (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x800) =
    [] := by decide

example : lazy_interior (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000) =
    [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)] := by decide

example :
    m_vm_lazy (vm_add_lazy (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0x1000)
      plainModel) =
      [(BitVec.ofInt 64 0x2000, BitVec.ofInt 64 0x1000)] := by decide

end LinuxSem.LinuxProcessSem
