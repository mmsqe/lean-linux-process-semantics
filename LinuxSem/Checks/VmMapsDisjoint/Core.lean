/-
  * LinuxSem.Checks.VmMapsDisjoint.Core — the base of the
    VmMapsDisjoint pyramid: PART 1, PART 2, PART 2b, the writers'
    preservation lemmas and the two base lemmas.

  SPLIT NOTE (build latency — no proof, statement, hypothesis or visibility
  changed).  These declarations used to be elaborated by the aggregator
  `Checks/VmMapsDisjoint.lean`, which imports all nine frame modules, so its
  ~9 s sat on the critical path of every arm edit.  They moved here byte for
  byte; the aggregator is now a pure import shim (imports + comments only).

  `bvnorm` MUST stay in THIS module.  A macro quotation resolves its
  identifiers at the MACRO'S DEFINITION SITE: `bvnorm`
  names `bv_unsigned` and `vm_wf`, which are defined here, so it has to be
  elaborated after them.  In a module where those names do not exist it
  expands to `bv_unsigned✝`/`vm_wf✝`, and the surrounding `try` turns that
  into a SILENT no-op — which showed up as 24 downstream `omega` failures
  with no error at the macro.  The move is verified against exactly that
  failure: the PART 1/2/2b proofs below still close.
-/


import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Common.RocqSpelling
import LinuxSem.Checks.Sys.Fs.Readdir
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Mm.Madvise
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Drivers.Char.Random
open LinuxSem.Checks.Sys.Fs.DPath
open LinuxSem.Checks.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Fs.EventPoll
open LinuxSem.Checks.Sys.Fs.Fcntl
open LinuxSem.Checks.Sys.Fs.File
open LinuxSem.Checks.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Fs.Open
open LinuxSem.Checks.Sys.Fs.Pipe
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Fs.Select
open LinuxSem.Checks.Sys.Fs.Stat
open LinuxSem.Checks.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Fs.Timerfd
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Kernel.Groups
open LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Kernel.Time.Time
open LinuxSem.Checks.Sys.Net.Socket

namespace LinuxSem.Checks.VmMapsDisjoint

open LinuxSem.Common.RocqSpelling

/- `bv_unsigned`, `Z_to_bv`, `zeqb`, `zleb`, `zltb`: the shared Rocq
   spellings, from `LinuxSem.Common.RocqSpelling` (imported and opened
   here). -/

/-- The `bv_unsigned` abbreviation as a REWRITE rule.  `bv_unsigned` is an
    `abbrev`, so `simp only [bv_unsigned]` does not pick it up, while
    `omega` treats `bv_unsigned x` and `↑x.toNat` as DISTINCT atoms
    — this states the bridge in the one spelling both
    accept. -/
theorem bv_unsigned_def {n : Nat} (w : BitVec n) : bv_unsigned w = (w.toNat : Int) := rfl

/-- `negb` (`Bool.negb`). -/
abbrev negb (b : Bool) : Bool := !b

/-- `vm_maps` as a function. -/
abbrev vm_maps (h : VmMaps) : List (word × word) := h.vm_maps
/-- `vm_reserved` as a function. -/
abbrev vm_reserved (h : VmMaps) : List (word × word) := h.vm_reserved
/-- `vm_noaccess` as a function. -/
abbrev vm_noaccess (h : VmMaps) : List (word × word) := h.vm_noaccess
/-- `vm_start_brk` as a function. -/
abbrev vm_start_brk (h : VmMaps) : word := h.vm_start_brk
/-- `vm_brk` as a function. -/
abbrev vm_brk (h : VmMaps) : word := h.vm_brk
/-- `vm_limit` as a function. -/
abbrev vm_limit (h : VmMaps) : Int := h.vm_limit
/-- `vm_mmap_base` as a function. -/
abbrev vm_mmap_base (h : VmMaps) : word := h.vm_mmap_base
/-- `vm_init_sp` as a function. -/
abbrev vm_init_sp (h : VmMaps) : word := h.vm_init_sp

/-! * LinuxProcessSem.Checks.VmMapsDisjoint — what [vm_maps] really guarantees -/

/- =========================================================================
   PART 1 — the counterexample, as a chain of modeled syscalls

   Reason 3 of [Checks/Examples]'s taxonomy: this pins MODEL-INTERNAL
   STATE (the [vm_maps] list) that no observation of a real execution
   reveals, and it is a statement about a WHOLE RUN rather than one call.

   The process: the image occupies [4096, 8192) and the ASLR-placed break
   base sits at 0x10000 = 65536, exactly the shape [Checks/Examples]'s
   brk section uses.  [wit_valid_brk] below records that this really is an
   [execve]-admissible placement.
   ========================================================================= -/

def wit_reserved : List (word × word) := [(4096, 4096)]

def wit_brk_base : word := 65536

def wit_limit : Int := 0x40000000

/-- [mm->mmap_base].  Nothing in the spec reads this field, so no
    step below depends on the value.  It is
    pinned to an admissible one ([wit_mmap_base_admissible]) so that the
    whole start state is one [execve] can hand out, which is what makes
    the overlap below reachable rather than hypothetical.  That is the
    only reason: no spec arm reads the value (the ASan plan checker's
    placement gate does, outside the spec; see `State`'s `vm_mmap_base`
    field note). -/
def wit_mmap_base : word := Z_to_bv 64 mmap_base_min

/-- The witness ledger.  [State.mkVmMaps] would default [vm_mmap_base] to
    zero, which is below [State.mmap_base_min]; this fixes it at the
    admissible value instead and is otherwise that same constructor. -/
def wit_vm (maps : List (word × word)) (start_brk brk : word)
    (limit : Int) : VmMaps :=
  VmMaps.mkVmMapsFull wit_reserved maps [] start_brk brk limit wit_mmap_base
    (Z_to_bv 64 sp_window_lo)

def wit_s0 : Model :=
  init_model wit_reserved wit_brk_base wit_mmap_base (Z_to_bv 64 sp_window_lo)
    wit_limit
    (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
      net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false VaSize.Sv48)

/-- The starting state is one [execve] really can hand a process: the
    break base is page aligned and sits at or above the page-rounded
    image top, within the brk ASLR window.  These are exactly
    [Run.valid_brk]'s three conjuncts, spelled on the reservation list so
    that the statement mentions no [MemImageType.Segment] — whose
    primitive-string payload field would otherwise show up under
    [Print Assumptions] as the kernel constant [String].
    [Run.valid_mmap_base]'s three conjuncts, spelled out for the same
    reason the brk ones are below. -/
theorem wit_mmap_base_admissible :
    (mmap_base_min ≤ bv_unsigned wit_mmap_base)
    ∧ (bv_unsigned wit_mmap_base ≤ mmap_base_max)
    ∧ (bv_unsigned wit_mmap_base % page_size = 0) := by
  unfold wit_mmap_base mmap_base_min mmap_base_max sp_window_hi page_size
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem wit_brk_base_admissible :
    (reserved_top wit_reserved ≤ bv_unsigned wit_brk_base)
    ∧ (bv_unsigned wit_brk_base ≤ reserved_top wit_reserved + brk_aslr_max)
    ∧ (bv_unsigned wit_brk_base % page_size = 0) := by
  unfold wit_reserved wit_brk_base brk_aslr_max page_size reserved_top
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- …and that really is [Run.valid_brk] for any image whose LOAD
    reservations are [wit_reserved]. -/
theorem wit_valid_brk : ∀ segs,
    segments_reserved segs = wit_reserved → valid_brk segs wit_brk_base := by
  intro segs Hs
  unfold valid_brk
  rw [Hs]
  exact wit_brk_base_admissible

def brk_in (req : word) : SyscallInput :=
  SyscallInput.mkInput 214 [req, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- STEP 1 — brk(0x11000): an ordinary page-crossing grow.  The gate
    checks [[65536, 69632)] and grants it. -/
def wit_s1 : Model :=
  with_vmmaps (wit_vm [(65536, 4096)] 65536 69632 wit_limit) wit_s0

theorem wit_step1 :
    check_syscall (brk_in 69632) (mkEffect 69632 [] [(65536, 4096)]) wit_s0
    = .CheckOk wit_s1 [] := by rfl

/-- STEP 2 — brk(0x11064): grow 100 bytes past the page boundary.  The
    gate checks the ROUNDED range [[69632, 73728)]; the ledger records
    the LOGICAL range [[69632, 69732)].  The break is now mid-page. -/
def wit_s2 : Model :=
  with_vmmaps
    (wit_vm [(69632, 100), (65536, 4096)] 65536 69732 wit_limit)
    wit_s0

theorem wit_step2 :
    check_syscall (brk_in 69732) (mkEffect 69732 [] [(69632, 4096)]) wit_s1
    = .CheckOk wit_s2 [] := by rfl

/-- STEP 3 — munmap(0x10000, 4096): drop the FIRST heap grant.  Linux
    unmaps those pages and leaves [mm->brk] alone; so does the model. -/
def wit_s3 : Model :=
  with_vmmaps
    (wit_vm [(69632, 100)] 65536 69732 wit_limit) wit_s0

theorem wit_step3 :
    check_syscall
      (SyscallInput.mkInput 215 [65536, 4096, 0, 0, 0, 0]
        (fun _ => none) (fun _ => none))
      (SyscallEffect.mkEffectU 0 [] [] [(65536, 4096)] [] []) wit_s2
    = .CheckOk wit_s3 [] := by rfl

/-- STEP 4 — brk(0x107d0): shrink down into the hole step 3 opened.  The
    remaining grant is above the new break, so the ledger empties; the
    break lands mid-page at 67536, with NOTHING below it owned. -/
def wit_s4 : Model :=
  with_vmmaps (wit_vm [] 65536 67536 wit_limit) wit_s0

theorem wit_step4 :
    check_syscall (brk_in 67536)
      (SyscallEffect.mkEffectU 67536 [] [] [(69632, 4096)] [] []) wit_s3
    = .CheckOk wit_s4 [] := by rfl

/-- STEP 5 — mmap of one page AT AN EXPLICIT HINT of 0x10000, which the
    kernel honors because the range is free of the image and of every
    live mapping, so [region_free] accepts.  The break now points INSIDE
    this fresh mapping — the model's reading of "the brk VMA was
    unmapped and something else was mapped over it", which a real kernel
    permits. -/
def wit_s5 : Model :=
  with_vmmaps (wit_vm [(65536, 4096)] 65536 67536 wit_limit) wit_s0

theorem wit_step5 :
    check_syscall
      (SyscallInput.mkInput 222 [65536, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect 65536 [] [(65536, 4096)]) wit_s4
    = .CheckOk wit_s5 [] := by rfl

/-- THE HINT IS NOT LOAD-BEARING.
    The identical grant with a NULL hint is admitted, because the spec
    says only three things about a preference-free placement — page
    alignment, the user range, and disjointness from every recorded
    mapping — and 0x10000 satisfies all three on this ledger.

    The spec does not pin the search further — at or above a bottom-up
    floor derived from riscv64's [TASK_UNMAPPED_BASE], or else leaving
    no fitting free gap up to the run's [mm->mmap_base] — because such a
    conjunct EXCLUDES placements Linux makes: its highest-fit half would
    be read on a ledger that does not carry the kernel's own vdso/vvar
    VMAs, so a real top-down descent would look impossible to the
    model.  The cost is exactly this: a low placement no ORDINARY
    kernel run produces is admissible.

    That is a provability cost and not a soundness one, and it is
    bounded.  It cannot refute a statement by colliding with a runtime's
    later MAP_FIXED reservation, because [Mmap.mmap_spec] models that
    MAP_FIXED as the replacement Linux performs rather than declining it;
    what remains is that a program whose observable behaviour depends on
    where a mapping landed has a false equivalence statement, which is
    the correct answer under ASLR.  The pair is kept — the hinted step 5
    above and this one — because the two together say what the spec does
    and does not constrain, which is what a reader needs. -/
theorem wit_step5_null_hint_also_admitted :
    check_syscall
      (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect 65536 [] [(65536, 4096)]) wit_s4
    = .CheckOk wit_s5 [] := by rfl

/-- …and the conditions that DO still refuse are pinned here, so the
    accept above is not read as "anything goes": the same NULL-hint
    grant at an unaligned address, and at one that overlaps the live
    mapping step 5 placed, are both rejected. -/
theorem wit_step5_null_hint_unaligned_refused :
    check_syscall
      (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect 65537 [] [(65537, 4096)]) wit_s4
    = .CheckReject := by rfl

theorem wit_step5_null_hint_overlapping_refused :
    check_syscall
      (SyscallInput.mkInput 222 [0, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect 65536 [] [(65536, 4096)]) wit_s5
    = .CheckReject := by rfl

/-- THE OVERLAP, in one more step.  brk(0x10834) grows the break by 100
    bytes without crossing a page boundary, so [brk_grow_ok] computes
    [lo = hi = 69632] and runs NO address-space test at all; the grant
    [[67536, 67636)] lands inside the mapping step 5 placed.  Two live
    [vm_maps] entries now overlap. -/
def wit_overlap : Model :=
  with_vmmaps
    (wit_vm [(67536, 100), (65536, 4096)] 65536 67636 wit_limit)
    wit_s0

theorem wit_overlap_step :
    check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s5
    = .CheckOk wit_overlap [] := by rfl

/-- …and the entries really do overlap.  The grant's OWN entry is
    dropped before the query, because every nonempty interval overlaps
    itself: what is checked is that the step-5 mapping alone already
    covers the range the brk grant just took. -/
theorem wit_overlap_holds :
    region_free (map_remove (vm_maps (m_vmmaps wit_overlap)) 67536) 67536 100
    = false := by rfl

/-- STEP 6 — brk(0x107c6): a ten-byte shrink, still inside one page.  It
    SPLITS the step-5 mapping, and the right-hand remnant is based at the
    OLD break, 67536. -/
def wit_s6 : Model :=
  with_vmmaps
    (wit_vm [(65536, 1990), (67536, 2096)] 65536 67526 wit_limit)
    wit_s0

theorem wit_step6 :
    check_syscall (brk_in 67526) (mkEffect 67526 [] []) wit_s5
    = .CheckOk wit_s6 [] := by rfl

/-- STEP 7 — brk(0x107d0): grow the ten bytes back.  Same page, so again
    no address-space test. -/
def wit_s7 : Model :=
  with_vmmaps
    (wit_vm [(67526, 10), (65536, 1990), (67536, 2096)]
      65536 67536 wit_limit)
    wit_s0

theorem wit_step7 :
    check_syscall (brk_in 67536) (mkEffect 67536 [] []) wit_s6
    = .CheckOk wit_s7 [] := by rfl

/-- STEP 8 — brk(0x10834): one more same-page grow, from a break that is
    now the base of the step-6 remnant.  [brk_grants] records
    [[67536, 67636)] and the ledger ends up with TWO entries based at
    67536. -/
def wit_s8 : Model :=
  with_vmmaps
    (wit_vm
      [(67536, 100), (67526, 10), (65536, 1990), (67536, 2096)]
      65536 67636 wit_limit)
    wit_s0

theorem wit_step8 :
    check_syscall (brk_in 67636) (mkEffect 67636 [] []) wit_s7
    = .CheckOk wit_s8 [] := by rfl

/-- THE VERDICT.  Two DIFFERENT sizes are both "exactly the mapping at
    67536", so [map_has] does not determine the entry [map_remove] would
    drop.  Byte-level base uniqueness is therefore not an invariant of
    reachable states, and no proof of it can exist as the model stands. -/
theorem wit_duplicate_base :
    map_has (vm_maps (m_vmmaps wit_s8)) 67536 100 = true
    ∧ map_has (vm_maps (m_vmmaps wit_s8)) 67536 2096 = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- The duplicated base is NOT page aligned, and Part 2 shows that is no
    accident: a page-aligned break makes [brk_grow_ok] compute
    [lo < hi] and the [region_free] test does run. -/
theorem wit_duplicate_base_is_unaligned :
    (67536 % page_size ≠ 0) := by
  unfold page_size
  decide

/-- A simpler route — [mmap] choosing the mid-page break
    itself as its base — cannot happen, and this is the gate that stops
    it: [mmap]'s placement is page aligned in every branch that grants,
    so the route above (a munmap that opens a hole, then a shrink INTO
    it) is the shorter one that works.  Asked for that base DIRECTLY, by
    the same hinted request step 5 uses and differing only in the
    address, so the refusal is the alignment test and nothing else. -/
theorem mmap_cannot_place_at_the_midpage_break :
    check_syscall
      (SyscallInput.mkInput 222 [67536, 4096, 3, 34, mmap_fd_none, 0]
        (fun _ => none) (fun _ => none))
      (mkEffect 67536 [] [(67536, 4096)]) wit_s4
    = .CheckReject := by rfl

/- =========================================================================
   PART 2 — the invariant that IS maintained

   [owners maps p] counts the live entries that own byte [p].  The
   invariant is that no PAGE-ALIGNED byte has two owners.  Part 1 shows
   the same statement is false for an arbitrary byte.
   ========================================================================= -/

/-- Does the ledger entry [e] own the byte at address [p]? -/
def owns_b (e : word × word) (p : Int) : Bool :=
  decide (bv_unsigned e.1 ≤ p) && decide (p < bv_unsigned e.1 + bv_unsigned e.2)

def owners (maps : List (word × word)) (p : Int) : Nat :=
  match maps with
  | [] => 0
  | e :: r => (if owns_b e p then 1 else 0) + owners r p

/-- THE INVARIANT.  Every page-aligned address is owned by at most one
    live mapping. -/
def page_owner_unique (maps : List (word × word)) : Prop :=
  ∀ p, p % page_size = 0 → owners maps p ≤ 1

/-- The companion well-formedness the ledger's writers also maintain, and
    which the corollaries need: no entry is empty.  An empty entry would
    own nothing, so it would slip past [region_free] and past
    [page_owner_unique] while still answering [map_has]. -/
def sizes_nonzero (maps : List (word × word)) : Prop := entries_nonzero maps

def maps_wf (maps : List (word × word)) : Prop :=
  sizes_nonzero maps ∧ page_owner_unique maps

def vm_wf (h : VmMaps) : Prop := maps_wf (vm_maps h)

/- -------------------------------------------------------------------------
   PART 2b — what the overlap does to the byte total

   Two readings of [State.live_bytes] — "exactly the number of
   granted-and-not-freed bytes", and metering "BYTES, not addresses —
   which is what makes the forced out-of-memory point deterministic" —
   follow from the disjointness Part 1 refutes, and both fail without
   it.  These cases pin the failure so
   that neither sentence can be claimed while the overlap is still
   reachable, and so that closing the gap in [brk_grow_ok] would have to
   break a case here rather than silently re-truth a comment.

   It sits after [owners] rather than beside Part 1's counterexample
   because the distinct-byte measure below is built from it.

   This is a known limitation of the model.
   ------------------------------------------------------------------------- -/

/-- How many of the [n] bytes from [lo] are owned by at least one live
    entry.  [owners] is Part 2's per-address ownership count; this is the
    DISTINCT-byte measure [live_bytes] claims to be, computed the slow
    honest way over a bounded window so the two can be compared. -/
def owned_bytes (maps : List (word × word)) (lo : Int) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => (if 0 < owners maps lo then 1 else 0) + owned_bytes maps (lo + 1) k

/-! ### TODO — four of the five [owned_bytes] computations (PART 2b)

    [owned_bytes] walks its window one byte at a time, so a worked example
    asks the KERNEL to evaluate 4,196 steps of `owners`/`owns_b` arithmetic.
    Kernel reduction needs ~20,000 recursion levels for that, which
    overflows the available stack in this build: a compiled evaluator would
    do it, the kernel does not, and `maxRecDepth` is not the dial for a
    stack overflow.

    It is not a gap in the statements — the definitions are the model's own
    and every one of these is decidable — so what is left is a measuring
    device that no other declaration reads.

    Four of the five are still open:
    `live_bytes_over_counts_the_overlap`,
    `live_bytes_is_exact_when_the_entries_are_disjoint`,
    `placement_changes_the_granted_byte_count` and
    `live_bytes_over_counts_never_under`.  The fifth,
    `live_bytes_over_counts_the_duplicate_base`, is a named
    `theorem` immediately after this block, and `rfl` closes both of its
    conjuncts — so the stack limit was measured on the other four and is
    not universal over this shape.

    `live_bytes` (the Int half of each example) is not open either: it is
    `live_bytes_over_counts_the_overlap`'s first conjunct and every
    `live_bytes`-only statement in this file is proved.

    Nothing depends on the four: `owned_bytes` is only a measuring device
    for this QA section — no lemma in this file or in `Sys/Mm/` reads it —
    and the page-granularity result below does not depend on any of them.
-/

/-- And the duplicate-base state double counts too, by the size of the
    smaller of the two entries sharing base 67536. -/
theorem live_bytes_over_counts_the_duplicate_base :
    live_bytes (vm_maps (m_vmmaps wit_s8)) = (4196 : Int)
    ∧ owned_bytes (vm_maps (m_vmmaps wit_s8)) 65536 4196 = 4096 := by
  refine ⟨?_, ?_⟩ <;> rfl



/-- Normalise `bv_unsigned x` to `↑x.toNat` in every hypothesis and the goal
    — the spelling `omega` needs, since it treats the two as DISTINCT atoms.
    `try` because a goal may hold no occurrence. -/
macro "bvnorm" : tactic =>
  `(tactic| (try dsimp only [bv_unsigned, vm_brk, vm_maps, vm_reserved, vm_noaccess, vm_start_brk, vm_limit, vm_mmap_base, vm_init_sp, vm_wf, m_vmmaps] at *; try simp only [two_pow_64] at *))

/- -------------------------------------------------------------------------
   Arithmetic and counting lemmas
   ------------------------------------------------------------------------- -/

theorem u64 (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z := by
  have hz : 0 ≤ z ∧ z < two_pow_64 := ⟨Hz.1, by simpa [two_pow_64] using Hz.2⟩
  exact bv_unsigned_Z_to_bv_u64 z hz

theorem word_range (w : word) : 0 ≤ bv_unsigned w ∧ bv_unsigned w < 2 ^ 64 := by
  have h := bv_unsigned_range_u64 w
  exact ⟨h.1, by simpa [two_pow_64] using h.2⟩

theorem page_round_up_Z_ge (z : Int) (_Hz : 0 ≤ z) : z ≤ page_round_up_Z z := by
  have h1 := Int.emod_add_mul_ediv (z + 4095) 4096
  have h2 := Int.emod_nonneg (z + 4095) (by decide : (4096 : Int) ≠ 0)
  have h3 := Int.emod_lt_of_pos (z + 4095) (by decide : (0 : Int) < 4096)
  unfold page_round_up_Z page_size
  bvnorm
  omega

/-- The step Part 1 turns on: a PAGE-ALIGNED address at or above [z] is
    at or above [z] ROUNDED UP.  This is exactly why the rounded gate
    covers every page-aligned byte of the range it fails to cover
    byte-for-byte. -/
theorem page_round_up_Z_le_aligned (z p : Int) (Hp : p % page_size = 0)
    (Hzp : z ≤ p) : page_round_up_Z z ≤ p := by
  have h1 := Int.emod_add_mul_ediv (z + 4095) 4096
  have h2 := Int.emod_add_mul_ediv p 4096
  have h3 := Int.emod_nonneg (z + 4095) (by decide : (4096 : Int) ≠ 0)
  have h4 := Int.emod_lt_of_pos (z + 4095) (by decide : (0 : Int) < 4096)
  have h5 : p % 4096 = 0 := by simpa [page_size] using Hp
  unfold page_round_up_Z page_size
  bvnorm
  omega

theorem owns_true (a n : word) (p : Int) (H : owns_b (a, n) p = true) :
    bv_unsigned a ≤ p ∧ p < bv_unsigned a + bv_unsigned n := by
  unfold owns_b at H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  exact H

theorem owns_false (a n : word) (p : Int) (H : owns_b (a, n) p = false) :
    p < bv_unsigned a ∨ bv_unsigned a + bv_unsigned n ≤ p := by
  unfold owns_b at H
  rw [Bool.and_eq_false_iff] at H
  rcases H with H | H
  · left
    simp only [decide_eq_false_iff_not] at H
    bvnorm
    omega
  · right
    simp only [decide_eq_false_iff_not] at H
    bvnorm
    omega

theorem owns_intro (a n : word) (p : Int) (H1 : bv_unsigned a ≤ p)
    (H2 : p < bv_unsigned a + bv_unsigned n) : owns_b (a, n) p = true := by
  unfold owns_b
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  bvnorm
  omega

/-- Two entries that own the same byte overlap — the bridge from
    [owners] to [region_free]. -/
theorem owns_overlap (a n b s : word) (p : Int) (H1 : owns_b (a, n) p = true)
    (H2 : owns_b (b, s) p = true) : iv_overlap a n b s = true := by
  have h1 := owns_true a n p H1
  have h2 := owns_true b s p H2
  unfold iv_overlap
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  bvnorm
  omega

theorem region_free_no_owner (maps : List (word × word)) (a n : word) (p : Int)
    (Hfree : region_free maps a n = true) (Hown : owns_b (a, n) p = true) :
    owners maps p = 0 := by
  induction maps with
  | nil => rfl
  | cons hd r ih =>
    obtain ⟨b, s⟩ := hd
    simp only [region_free, Bool.and_eq_true] at Hfree
    simp only [owners]
    by_cases hb : owns_b (b, s) p = true
    · have hov := owns_overlap a n b s p Hown hb
      rw [hov] at Hfree
      simp at Hfree
    · rw [ite_eq_right hb]
      simpa using ih Hfree.2

theorem owners_app (l1 l2 : List (word × word)) (p : Int) :
    owners (l1 ++ l2) p = owners l1 p + owners l2 p := by
  induction l1 with
  | nil => simp [owners]
  | cons e r ih =>
    simp only [List.cons_append, owners, ih]
    bvnorm
    omega

theorem owners_filter_split (f : word × word → Bool) (maps : List (word × word))
    (p : Int) :
    owners (maps.filter f) p + owners (maps.filter (fun e => !(f e))) p
      = owners maps p := by
  induction maps with
  | nil => rfl
  | cons e r ih =>
    by_cases h : f e = true
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h])]
      simp only [owners]
      by_cases ho : owns_b e p = true <;> simp [ho] <;> omega
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_pos (by simp [h])]
      simp only [owners]
      by_cases ho : owns_b e p = true <;> simp [ho] <;> omega

theorem owners_filter_le (f : word × word → Bool) (maps : List (word × word))
    (p : Int) : owners (maps.filter f) p ≤ owners maps p := by
  have h := owners_filter_split f maps p
  bvnorm
  omega

theorem owners_eq_zero_of_false (l : List (word × word)) (p : Int)
    (H : ∀ e, e ∈ l → owns_b e p = false) : owners l p = 0 := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    simp only [owners]
    rw [H e (by simp)]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    exact ih (fun e' he => H e' (by simp [he]))

theorem owners_pair_le_one (e1 e2 : word × word) (p : Int)
    (h : ¬(owns_b e1 p = true ∧ owns_b e2 p = true)) : owners [e1, e2] p ≤ 1 := by
  simp only [owners, Nat.add_zero]
  by_cases h1 : owns_b e1 p = true
  · have h2 : owns_b e2 p = false := by
      by_cases hh : owns_b e2 p = true
      · exact absurd ⟨h1, hh⟩ h
      · simpa using hh
    rw [ite_eq_left h1, ite_eq_right (by rw [h2]; simp)]
    bvnorm
    omega
  · rw [ite_eq_right h1]
    by_cases h2 : owns_b e2 p = true
    · rw [ite_eq_left h2]
      bvnorm
      omega
    · rw [ite_eq_right h2]
      bvnorm
      omega

theorem sizes_nonzero_filter (f : word × word → Bool) (maps : List (word × word))
    (H : sizes_nonzero maps) : sizes_nonzero (maps.filter f) := by
  intro a n hmem
  exact H a n (List.mem_filter.mp hmem).1

theorem owners_ge1 (maps : List (word × word)) (e : word × word) (p : Int)
    (Hin : e ∈ maps) (Ho : owns_b e p = true) : 1 ≤ owners maps p := by
  induction maps with
  | nil => simp at Hin
  | cons hd r ih =>
    obtain ⟨b, s⟩ := e
    obtain ⟨b', s'⟩ := hd
    simp only [List.mem_cons] at Hin
    simp only [owners]
    rcases Hin with h | h
    · obtain ⟨rfl, rfl⟩ := h
      simp [Ho]
    · have hrec := ih h
      by_cases ho : owns_b (b', s') p = true <;> simp [ho] <;> omega

theorem owners_all_own (l : List (word × word)) (p : Int)
    (H : ∀ e, e ∈ l → owns_b e p = true) : owners l p = l.length := by
  induction l with
  | nil => rfl
  | cons e r ih =>
    simp only [owners, List.length_cons]
    rw [H e (by simp), ih (fun e' he => H e' (by simp [he]))]
    simp
    bvnorm
    omega

theorem owners_map_remove_lt (maps : List (word × word)) (b s : word) (p : Int)
    (Hin : (b, s) ∈ maps) (Ho : owns_b (b, s) p = true) :
    owners (map_remove maps b) p + 1 ≤ owners maps p := by
  induction maps with
  | nil => simp at Hin
  | cons hd r ih =>
    obtain ⟨e1, e2⟩ := hd
    unfold map_remove at *
    by_cases hf : (e1 == b) = true
    · rw [List.filter_cons_of_neg (by simp [hf])]
      have hle : owners (List.filter (fun q => !(q.1 == b)) r) p ≤ owners r p :=
        owners_filter_le _ r p
      simp only [owners]
      rcases List.mem_cons.mp Hin with h | h
      · cases h
        rw [ite_eq_left Ho]
        bvnorm
        omega
      · have hrec := ih h
        by_cases ho : owns_b (e1, e2) p = true <;> simp [ho] <;> omega
    · rw [List.filter_cons_of_pos (by simp [hf])]
      have hmem : (b, s) ∈ r := by
        rcases List.mem_cons.mp Hin with h | h
        · have hb : b = e1 := ((Prod.mk.injEq b s e1 e2).mp h).1
          rw [hb] at hf
          simp at hf
        · exact h
      have hrec := ih hmem
      simp only [owners]
      by_cases ho : owns_b (e1, e2) p = true <;> simp [ho] <;> omega

/- -------------------------------------------------------------------------
   The two ways the ledger grows: a fresh [region_free] grant, and a
   [maps_subtract] that can only shrink coverage
   ------------------------------------------------------------------------- -/

/-- A grant checked by [region_free] against the very list it is
    prepended to keeps the invariant, for EVERY address — page aligned
    or not. -/
theorem maps_wf_cons_free (maps : List (word × word)) (a n : word)
    (Hwf : maps_wf maps) (Hn : bv_unsigned n ≠ 0)
    (Hfree : region_free maps a n = true) : maps_wf ((a, n) :: maps) := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  have hnpos : 0 < (n.toNat : Int) := by
    have := bv_unsigned_range_u64 n
    bvnorm
    omega
  refine ⟨?_, ?_⟩
  · intro b s hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      exact hnpos
    · exact Hnz b s h
  · intro p Hp
    simp only [owners]
    by_cases ho : owns_b (a, n) p = true
    · rw [ite_eq_left ho, region_free_no_owner maps a n p Hfree ho]
      bvnorm
      omega
    · rw [ite_eq_right ho]
      simpa using Hun p Hp

/-- `Z_to_bv` round-trips through `min` while the larger operand fits a word. -/
theorem u64_min_eq (x y : Int) (hx : 0 ≤ x) (hx' : x < 2 ^ 64) (hy : 0 ≤ y) :
    bv_unsigned (BitVec.ofInt 64 (min x y)) = min x y := by
  apply u64
  have h2 : 0 ≤ min x y := by
    by_cases h : x ≤ y
    · rw [Int.min_eq_left h]; exact hx
    · rw [Int.min_eq_right (by omega)]; exact hy
  have h3 : min x y ≤ x := Int.min_le_left x y
  exact ⟨h2, by omega⟩

/-- …and through `max`, the same way. -/
theorem u64_max_eq (x y : Int) (hx : 0 ≤ x) (hx' : x < 2 ^ 64) (hy' : y < 2 ^ 64) :
    bv_unsigned (BitVec.ofInt 64 (max x y)) = max x y := by
  apply u64
  have h2 : 0 ≤ max x y := by have := Int.le_max_left x y; omega
  have h3 : max x y < 2 ^ 64 := by
    rw [Int.max_lt]
    exact ⟨hx', hy'⟩
  exact ⟨h2, h3⟩

/-- …and through a subtraction by a lower bound. -/
theorem u64_sub_eq (x y : Int) (h0 : y ≤ x) (h1 : x - y < 2 ^ 64) :
    bv_unsigned (BitVec.ofInt 64 (x - y)) = x - y := by
  apply u64
  exact ⟨by omega, h1⟩

/-- Every remnant of a cut lies inside the entry it came from. -/
theorem iv_subtract_owns_mono (a sz : word) (lo hi p : Int) (Hhi : hi < 2 ^ 64)
    {e : word × word}
    (Hmem : e ∈ iv_subtract a sz lo hi) (Hown : owns_b e p = true) :
    owns_b (a, sz) p = true := by
  obtain ⟨e1, e2⟩ := e
  have hown := owns_true e1 e2 p Hown
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  have ha2 : (a.toNat : Int) < 2 ^ 64 := by simpa [two_pow_64] using ha.2
  have hs2 : (sz.toNat : Int) < 2 ^ 64 := by simpa [two_pow_64] using hs.2
  unfold iv_subtract at Hmem
  dsimp only at Hmem
  rw [List.mem_append] at Hmem
  rcases Hmem with hmem | hmem
  · by_cases h1 : (a.toNat : Int) < lo
    · rw [ite_eq_left h1, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      obtain ⟨h1', h2'⟩ := hmem
      rw [h1', h2'] at hown
      have hz : bv_unsigned (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))
          = min (sz.toNat : Int) (lo - (a.toNat : Int)) := by
        apply u64_min_eq
        · exact hs.1
        · exact hs2
        · omega
      rw [hz] at hown
      apply owns_intro <;> bvnorm <;> omega
    · rw [ite_eq_right h1] at hmem
      exact absurd hmem (by simp)
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      obtain ⟨h1', h2'⟩ := hmem
      rw [h1', h2'] at hown
      have hzA : bv_unsigned (BitVec.ofInt 64 (max (a.toNat : Int) hi))
          = max (a.toNat : Int) hi := by
        apply u64_max_eq
        · exact ha.1
        · exact ha2
        · exact Hhi
      have hzB : bv_unsigned (BitVec.ofInt 64
            ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))
          = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by
        apply u64_sub_eq
        · rw [Int.max_le]
          exact ⟨by omega, by omega⟩
        · have h1 := Int.le_max_left (a.toNat : Int) hi
          bvnorm
          omega
      rw [hzA, hzB] at hown
      apply owns_intro <;> bvnorm <;> omega
    · rw [ite_eq_right h2] at hmem
      exact absurd hmem (by simp)

theorem iv_subtract_ok (a sz : word) (lo hi p : Int)
    (Hlo : 0 ≤ lo) (Hlh : lo ≤ hi) (Hhi : hi < 2 ^ 64) (Hsz : bv_unsigned sz ≠ 0) :
    owners (iv_subtract a sz lo hi) p ≤ (if owns_b (a, sz) p then 1 else 0)
    ∧ sizes_nonzero (iv_subtract a sz lo hi) := by
  have hszpos : 0 < (sz.toNat : Int) := by
    have := bv_unsigned_range_u64 sz
    bvnorm
    omega
  refine ⟨?_, iv_subtract_nonzero a sz lo hi hszpos⟩
  have mono : ∀ {e : word × word}, e ∈ iv_subtract a sz lo hi →
      owns_b e p = true → owns_b (a, sz) p = true :=
    fun he ho => iv_subtract_owns_mono a sz lo hi p Hhi he ho
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  have ha2 : (a.toNat : Int) < 2 ^ 64 := by simpa [two_pow_64] using ha.2
  have hs2 : (sz.toNat : Int) < 2 ^ 64 := by simpa [two_pow_64] using hs.2
  have hzL : (a.toNat : Int) < lo →
      bv_unsigned (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))
        = min (sz.toNat : Int) (lo - (a.toNat : Int)) := by
    intro h1
    apply u64_min_eq
    · exact hs.1
    · exact hs2
    · omega
  have hzR : bv_unsigned (BitVec.ofInt 64 (max (a.toNat : Int) hi)) = max (a.toNat : Int) hi := by
    apply u64_max_eq
    · exact ha.1
    · exact ha2
    · exact Hhi
  have hzRS : hi < (a.toNat : Int) + (sz.toNat : Int) →
      bv_unsigned (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))
        = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by
    intro h2
    apply u64_sub_eq
    · rw [Int.max_le]
      exact ⟨by omega, by omega⟩
    · have h1 := Int.le_max_left (a.toNat : Int) hi
      bvnorm
      omega
  have hmL : (a.toNat : Int) < lo → (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) ∈ iv_subtract a sz lo hi := by
    intro h1
    unfold iv_subtract
    dsimp only
    rw [ite_eq_left h1]
    simp
  have hmR : hi < (a.toNat : Int) + (sz.toNat : Int) →
      ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) ∈ iv_subtract a sz lo hi := by
    intro h2
    unfold iv_subtract
    dsimp only
    by_cases h1 : (a.toNat : Int) < lo
    · rw [ite_eq_left h1, ite_eq_left h2]
      simp
    · rw [ite_eq_right h1, ite_eq_left h2]
      simp
  unfold iv_subtract
  dsimp only
  by_cases h1 : (a.toNat : Int) < lo
  · rw [ite_eq_left h1]
    by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2, List.singleton_append]
      by_cases hf : owns_b (a, sz) p = true
      · rw [ite_eq_left hf]
        apply owners_pair_le_one
        rintro ⟨hA, hB⟩
        have bA := owns_true a (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))) p hA
        rw [hzL h1] at bA
        have bB := owns_true (BitVec.ofInt 64 (max (a.toNat : Int) hi)) (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi)) p hB
        rw [hzR, hzRS h2] at bB
        have hp1 : p < lo := by
          have h := bA.2
          have hm := Int.min_le_right (sz.toNat : Int) (lo - (a.toNat : Int))
          bvnorm
          omega
        have hp2 : lo ≤ p := by
          have h := bB.1
          have hm := Int.le_max_right (a.toNat : Int) hi
          bvnorm
          omega
        bvnorm
        omega
      · rw [ite_eq_right hf]
        have hA : owns_b (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) p = false := by
          by_cases h : owns_b (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) p = true
          · exact absurd (mono (hmL h1) h) hf
          · simpa using h
        have hB : owns_b ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) p = false := by
          by_cases h : owns_b ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) p = true
          · exact absurd (mono (hmR h2) h) hf
          · simpa using h
        simp [owners, hA, hB]
    · rw [ite_eq_right h2, List.singleton_append]
      by_cases hf : owns_b (a, sz) p = true
      · rw [ite_eq_left hf]
        by_cases hA : owns_b (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) p = true <;> simp [owners, hA]
      · rw [ite_eq_right hf]
        have hA : owns_b (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) p = false := by
          by_cases h : owns_b (a, (BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int))))) p = true
          · exact absurd (mono (hmL h1) h) hf
          · simpa using h
        simp [owners, hA]
  · rw [ite_eq_right h1]
    by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2, List.nil_append]
      by_cases hf : owns_b (a, sz) p = true
      · rw [ite_eq_left hf]
        by_cases hB : owns_b ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) p = true <;> simp [owners, hB]
      · rw [ite_eq_right hf]
        have hB : owns_b ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) p = false := by
          by_cases h : owns_b ((BitVec.ofInt 64 (max (a.toNat : Int) hi)), (BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi))) p = true
          · exact absurd (mono (hmR h2) h) hf
          · simpa using h
        simp [owners, hB]
    · rw [ite_eq_right h2, List.nil_append]
      by_cases hf : owns_b (a, sz) p = true <;> simp [owners]

theorem maps_subtract_ok (maps : List (word × word)) (lo hi : Int)
    (Hlo : 0 ≤ lo) (Hlh : lo ≤ hi) (Hhi : hi < 2 ^ 64) (Hnz : sizes_nonzero maps) :
    sizes_nonzero (maps_subtract maps lo hi)
    ∧ ∀ p, owners (maps_subtract maps lo hi) p ≤ owners maps p := by
  induction maps with
  | nil =>
    refine ⟨?_, ?_⟩
    · intro a n hmem
      exact absurd hmem (by simp [maps_subtract])
    · intro p
      simp [maps_subtract, owners]
  | cons hd r ih =>
    obtain ⟨a, sz⟩ := hd
    have hnz : bv_unsigned sz ≠ 0 := by
      have h := Hnz a sz (by simp)
      bvnorm
      omega
    obtain ⟨ihnz, ihle⟩ := ih (fun x y hx => Hnz x y (by simp [hx]))
    have hok := iv_subtract_ok a sz lo hi 0 Hlo Hlh Hhi hnz
    have hokp := fun p => (iv_subtract_ok a sz lo hi p Hlo Hlh Hhi hnz).1
    refine ⟨?_, ?_⟩
    · intro b s hmem
      simp only [maps_subtract, List.mem_append] at hmem
      rcases hmem with h | h
      · exact hok.2 b s h
      · exact ihnz b s h
    · intro p
      simp only [maps_subtract]
      rw [owners_app]
      have hc := hokp p
      have hr := ihle p
      simp only [owners]
      bvnorm
      omega

theorem maps_wf_subtract (maps : List (word × word)) (lo hi : Int)
    (Hlo : 0 ≤ lo) (Hlh : lo ≤ hi) (Hhi : hi < 2 ^ 64) (Hwf : maps_wf maps) :
    maps_wf (maps_subtract maps lo hi) := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  obtain ⟨ha, hb⟩ := maps_subtract_ok maps lo hi Hlo Hlh Hhi Hnz
  refine ⟨ha, ?_⟩
  intro p Hp
  have h1 := hb p
  have h2 := Hun p Hp
  bvnorm
  omega

/-- Nothing survives a subtraction INSIDE the range subtracted. -/
theorem iv_subtract_region_free (c sz : word) (a n : word)
    (Hhi : bv_unsigned a + bv_unsigned n < 2 ^ 64) (b s : word)
    (Hin : (b, s) ∈ iv_subtract c sz (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) :
    iv_overlap a n b s = false := by
  have ha := bv_unsigned_range_u64 a
  have hn := bv_unsigned_range_u64 n
  have hc := bv_unsigned_range_u64 c
  have hsz := bv_unsigned_range_u64 sz
  unfold iv_subtract at Hin
  dsimp only at Hin
  rw [List.mem_append] at Hin
  rcases Hin with Hin | Hin
  · by_cases h1 : (c.toNat : Int) < bv_unsigned a
    · rw [ite_eq_left h1, List.mem_singleton] at Hin
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Hin
      unfold iv_overlap
      rw [bv_unsigned_Z_to_bv_u64 _ ⟨by bvnorm; omega, by bvnorm; omega⟩]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      bvnorm
      omega
    · rw [ite_eq_right h1] at Hin
      exact absurd Hin (by simp)
  · by_cases h2 : bv_unsigned a + bv_unsigned n < (c.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2, List.mem_singleton] at Hin
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Hin
      unfold iv_overlap
      rw [bv_unsigned_Z_to_bv_u64 _ ⟨by bvnorm; omega, by bvnorm; omega⟩]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      bvnorm
      omega
    · rw [ite_eq_right h2] at Hin
      exact absurd Hin (by simp)

theorem maps_subtract_region_free (maps : List (word × word)) (a n : word)
    (Hhi : bv_unsigned a + bv_unsigned n < 2 ^ 64) :
    region_free (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      a n = true := by
  apply region_free_intro
  induction maps with
  | nil => intro b s hmem; exact absurd hmem (by simp [maps_subtract])
  | cons hd r ih =>
    obtain ⟨c, sz⟩ := hd
    intro b s hmem
    simp only [maps_subtract, List.mem_append] at hmem
    rcases hmem with h | h
    · exact iv_subtract_region_free c sz a n Hhi b s h
    · exact ih b s h

theorem maps_wf_filter (f : word × word → Bool) (maps : List (word × word))
    (Hwf : maps_wf maps) : maps_wf (maps.filter f) := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  refine ⟨sizes_nonzero_filter f maps Hnz, ?_⟩
  intro p Hp
  have h1 := owners_filter_le f maps p
  have h2 := Hun p Hp
  bvnorm
  omega

theorem region_free_filter (f : word × word → Bool) (maps : List (word × word))
    (lo n : word) (H : region_free maps lo n = true) :
    region_free (maps.filter f) lo n = true := by
  apply region_free_intro
  intro a sz hmem
  exact region_free_In maps lo n a sz H (List.mem_filter.mp hmem).1

theorem maps_wf_cons_sub (maps : List (word × word)) (a n0 n : word)
    (Hwf : maps_wf maps) (Hn : bv_unsigned n ≠ 0) (Hin : (a, n0) ∈ maps)
    (Hle : bv_unsigned n ≤ bv_unsigned n0) : maps_wf ((a, n) :: map_remove maps a) := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  have hnpos : 0 < (n.toNat : Int) := by
    have := bv_unsigned_range_u64 n
    bvnorm
    omega
  refine ⟨?_, ?_⟩
  · intro b s hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      exact hnpos
    · exact sizes_nonzero_filter (fun q => !(q.1 == a)) maps Hnz b s h
  · intro p Hp
    simp only [owners]
    by_cases ho : owns_b (a, n) p = true
    · have hb := owns_true a n p ho
      have ho0 : owns_b (a, n0) p = true := by
        apply owns_intro
        · omega
        · omega
      have h1 := owners_map_remove_lt maps a n0 p Hin ho0
      have h2 := Hun p Hp
      rw [ite_eq_left ho]
      bvnorm
      omega
    · have h1 : owners (map_remove maps a) p ≤ owners maps p :=
        owners_filter_le (fun q => !(q.1 == a)) maps p
      have h2 := Hun p Hp
      rw [ite_eq_right ho]
      bvnorm
      omega

/- -------------------------------------------------------------------------
   What the invariant buys: base uniqueness where a syscall can name a
   base, and the [map_has]/[map_remove] agreement munmap needs
   ------------------------------------------------------------------------- -/

theorem map_has_In (maps : List (word × word)) (a n : word)
    (H : map_has maps a n = true) : (a, n) ∈ maps := by
  unfold map_has at H
  rw [List.any_eq_true] at H
  obtain ⟨⟨b, s⟩, Hin, Hb⟩ := H
  simp only [Bool.and_eq_true, beq_iff_eq] at Hb
  obtain ⟨rfl, rfl⟩ := Hb
  exact Hin

/-- THE NARROW FORM the downstream [munmap] argument asks for: at a
    PAGE-ALIGNED base — the only kind [munmap], [mremap], [mprotect] and
    [mmap] can produce or accept — the ledger holds exactly one entry,
    and it is the one [map_has] matched.  So [map_has]'s [(base, size)]
    test and [map_remove]'s base-only removal name the same mapping. -/
theorem base_entry_unique (maps : List (word × word)) (a n : word)
    (Hwf : maps_wf maps) (Ha : bv_unsigned a % page_size = 0)
    (Hhas : map_has maps a n = true) :
    List.filter (fun q => bv_eqb q.1 a) maps = [(a, n)] := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  have Hin : (a, n) ∈ maps := map_has_In maps a n Hhas
  have HinF : (a, n) ∈ List.filter (fun q => bv_eqb q.1 a) maps := by
    rw [List.mem_filter]
    exact ⟨Hin, bv_eqb_refl a⟩
  have Hown : ∀ e, e ∈ List.filter (fun q => bv_eqb q.1 a) maps →
      owns_b e (bv_unsigned a) = true := by
    intro e He
    obtain ⟨b, s⟩ := e
    rw [List.mem_filter] at He
    obtain ⟨He, Hb⟩ := He
    have hb : b = a := (Fs.bv_eqb_eq b a).mp Hb
    subst hb
    have hs : 0 < (s.toNat : Int) := Hnz b s He
    have hb0 : 0 ≤ (b.toNat : Int) := (bv_unsigned_range_u64 b).1
    have hs1 : (s.toNat : Int) < 2 ^ 64 := (bv_unsigned_range_u64 s).2
    apply owns_intro
    · bvnorm
      omega
    · bvnorm
      omega
  have Hall : owners (List.filter (fun q => bv_eqb q.1 a) maps) (bv_unsigned a)
      = (List.filter (fun q => bv_eqb q.1 a) maps).length :=
    owners_all_own _ _ Hown
  have Hsplit := owners_filter_le (fun q => bv_eqb q.1 a) maps (bv_unsigned a)
  have Hun1 := Hun (bv_unsigned a) Ha
  have hlen : (List.filter (fun q => bv_eqb q.1 a) maps).length ≤ 1 := by
    rw [← Hall]
    bvnorm
    omega
  obtain ⟨x, hx⟩ : ∃ x, List.filter (fun q => bv_eqb q.1 a) maps = [x] := by
    match h : List.filter (fun q => bv_eqb q.1 a) maps with
    | [] =>
      rw [h] at HinF
      simp at HinF
    | [x] => exact ⟨x, h⟩
    | _ :: _ :: _ =>
      rw [h] at hlen
      simp at hlen
  have hxa : x = (a, n) := by
    rw [hx] at HinF
    rw [List.mem_singleton] at HinF
    exact HinF.symm
  rw [hx, hxa]

/-- …hence the size in a [map_has] hit is unique. -/
theorem map_has_pins_size (maps : List (word × word)) (a n1 n2 : word)
    (Hwf : maps_wf maps) (Ha : bv_unsigned a % page_size = 0)
    (H1 : map_has maps a n1 = true) (H2 : map_has maps a n2 = true) : n1 = n2 := by
  have E1 := base_entry_unique maps a n1 Hwf Ha H1
  have Hin2 : (a, n2) ∈ maps := map_has_In maps a n2 H2
  have HinF : (a, n2) ∈ List.filter (fun q => bv_eqb q.1 a) maps := by
    rw [List.mem_filter]
    exact ⟨Hin2, bv_eqb_refl a⟩
  rw [E1, List.mem_singleton] at HinF
  have := congrArg Prod.snd HinF
  simpa using this.symm

theorem live_bytes_filter_split (f : word × word → Bool) (maps : List (word × word)) :
    live_bytes maps
      = live_bytes (maps.filter f)
        + live_bytes (maps.filter (fun e => !(f e))) := by
  induction maps with
  | nil => rfl
  | cons hd r ih =>
    obtain ⟨a, s⟩ := hd
    by_cases h : f (a, s) = true
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h])]
      simp only [live_bytes, ih]
      bvnorm
      omega
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_pos (by simp [h])]
      simp only [live_bytes, ih]
      bvnorm
      omega

/-- The budget reading of the same fact: an exact [munmap] gives back
    exactly the bytes [map_has] matched, no more and no less. -/
theorem munmap_returns_matched_bytes (maps : List (word × word)) (a n : word)
    (Hwf : maps_wf maps) (Ha : bv_unsigned a % page_size = 0)
    (Hhas : map_has maps a n = true) :
    live_bytes maps = bv_unsigned n + live_bytes (map_remove maps a) := by
  have Hs := live_bytes_filter_split (fun q => q.1 == a) maps
  have hbe : List.filter (fun q => q.1 == a) maps = [(a, n)] :=
    base_entry_unique maps a n Hwf Ha Hhas
  rw [hbe] at Hs
  simp only [live_bytes] at Hs
  rw [Hs]
  unfold map_remove
  simp only [Int.add_zero]



/- -------------------------------------------------------------------------
   PRESERVATION.  Every syscall that writes [vm_maps] keeps the invariant.
   ------------------------------------------------------------------------- -/

/-- [m_vmmaps] and the setters are structure updates, so every one of these
    is [reflexivity] — the subsystem record is exactly what the setter
    builds — and they give [rewrite] one.  The backing wrappers matter here
    because the memory syscalls update the sparse-backing ledgers in the
    same step as [vm_maps], and none of those wrappers touches [vm_maps]. -/
theorem vmm_vmmaps (h : VmMaps) (m : Model) : m_vmmaps (with_vmmaps h m) = h := rfl

theorem vmm_backing (lz : List (word × word)) (mt : List word) (m : Model) :
    m_vmmaps (with_vm_backing lz mt m) = m_vmmaps m := rfl

theorem vmm_forget_range (lo hi : Int) (m : Model) :
    m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m := rfl

theorem vmm_forget_ranges (rs : List (word × word)) (m : Model) :
    m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m := by
  induction rs generalizing m with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨a, n⟩ := hd
    exact ih (vm_forget_range (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) m)

theorem vmm_mmap_backing (flags a n : word) (m : Model) :
    m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m := by
  unfold with_mmap_backing
  split <;> rfl

theorem vmm_mmap_replacement (flags a n : word) (m : Model) :
    m_vmmaps (with_mmap_replacement flags a n m) = m_vmmaps m := by
  unfold with_mmap_replacement
  rw [vmm_mmap_backing, vmm_forget_range]

theorem vmm_mmap_destroyed (a n : word) (h' : VmMaps) (m : Model) :
    m_vmmaps (with_mmap_destroyed a n h' m) = h' := by
  unfold with_mmap_destroyed
  rw [vmm_forget_range, vmm_vmmaps]

theorem vmm_brk_next (m : Model) (req r : word) :
    m_vmmaps (with_brk_next m req r) = brk_model_next (m_vmmaps m) req r := by
  unfold with_brk_next
  rw [vmm_forget_ranges, vmm_vmmaps]

theorem vmm_mprotect_next (m : Model) (addr n : word) :
    m_vmmaps (mprotect_model_next m addr n)
    = VmMaps.mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
        (maps_subtract (vm_noaccess (m_vmmaps m))
           (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
        (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m))
        (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
        (vm_init_sp (m_vmmaps m)) := by
  unfold mprotect_model_next
  dsimp only
  rfl

theorem vmm_madvise_next (m : Model) (addr n : word) :
    m_vmmaps (madvise_dontneed_next m addr n) = m_vmmaps m := rfl

theorem vmm_resize_backing (b : Bool) (old old_n dst new_n : word) (m : Model) :
    m_vmmaps (vm_resize_backing b old old_n dst new_n m) = m_vmmaps m := rfl

theorem vmm_mremap_next (m : Model) (old old_n dst new_n : word) :
    m_vmmaps (mremap_model_next m old old_n dst new_n)
    = mremap_maps_next (m_vmmaps m) old dst new_n := by
  unfold mremap_model_next
  rw [vmm_resize_backing, vmm_vmmaps]

theorem vmm_fixed_rw_next (h : VmMaps) (addr n : word) :
    vm_maps (mmap_fixed_rw_next h addr n) = vm_maps h := by
  unfold mmap_fixed_rw_next
  rfl

theorem w_is0_false (w : word) (H : w_is0 w = false) : bv_unsigned w ≠ 0 := by
  intro Hc
  have h2 : w.toNat = 0 := by
    bvnorm
    bvnorm
    bvnorm
    omega
  have hw : w = 0 := BitVec.eq_of_toNat_eq (by simpa using h2)
  rw [hw] at H
  simp [w_is0, bv_eqb] at H

theorem page_round_up_pos (z : Int) (H : 0 < z) : 0 < page_round_up_Z z := by
  have h := page_round_up_Z_ge z (by omega)
  bvnorm
  bvnorm
  omega

/-- A grow resolution is gated: [brk_r_ok] can only admit a strictly
    higher break through the branch that evaluates [brk_grow_ok]. -/
theorem brk_r_ok_grow (m : Model) (req r : word)
    (Hok : brk_r_ok m req r = true)
    (Hgrow : brk_is_grow req r (vm_brk (m_vmmaps m)) = true) :
    brk_grow_ok m req r = true := by
  unfold brk_is_grow at Hgrow
  simp only [Bool.and_eq_true] at Hgrow
  obtain ⟨⟨hreq, hposd⟩, hlt⟩ := Hgrow
  have hreq' : w_is0 req = false := by simpa using hreq
  have hpos : 0 < ((vm_brk (m_vmmaps m)).toNat : Int) := by simpa using hposd
  have hlt' : ((vm_brk (m_vmmaps m)).toNat : Int) < (r.toNat : Int) := by simpa using hlt
  unfold brk_r_ok at Hok
  dsimp only at Hok
  rw [hreq'] at Hok
  simp only [Bool.false_or] at Hok
  by_cases hmin : ((req.toNat : Int) < ((min_brk (m_vmmaps m)).toNat : Int))
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact hmin)] at Hok
    rw [beq_iff_eq] at Hok
    rw [Hok] at hlt'
    bvnorm
    bvnorm
    omega
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact hmin)] at Hok
    by_cases hshr : ((req.toNat : Int) < ((vm_brk (m_vmmaps m)).toNat : Int))
    · rw [ite_eq_left (by simp only [decide_eq_true_eq]; exact hshr)] at Hok
      rw [Bool.or_eq_true] at Hok
      rcases Hok with h | h
      · rw [beq_iff_eq] at h
        rw [h] at hlt'
        bvnorm
        bvnorm
        omega
      · rw [beq_iff_eq] at h
        rw [h] at hlt'
        bvnorm
        bvnorm
        omega
    · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact hshr)] at Hok
      rw [Bool.and_eq_true] at Hok
      exact Hok.2

/-- The heart of PART 2, and the exact mirror of PART 1: a brk grant may
    cover bytes the gate never tested, but every PAGE-ALIGNED byte it
    covers lies inside the range [region_free] did test. -/
theorem brk_grant_wf (m : Model) (req r : word)
    (Hok : brk_r_ok m req r = true)
    (Hgrow : brk_is_grow req r (vm_brk (m_vmmaps m)) = true)
    (Hwf : vm_wf (m_vmmaps m)) :
    maps_wf ((vm_brk (m_vmmaps m), (r - vm_brk (m_vmmaps m)))
             :: vm_maps (m_vmmaps m)) := by
  obtain ⟨Hnz, Hun⟩ := Hwf
  have hbrk : bv_unsigned (vm_brk (m_vmmaps m)) = ((m_vmmaps m).vm_brk.toNat : Int) := rfl
  unfold brk_is_grow at Hgrow
  simp only [Bool.and_eq_true] at Hgrow
  obtain ⟨⟨hreq, hposd⟩, hlt⟩ := Hgrow
  have hpos : 0 < ((vm_brk (m_vmmaps m)).toNat : Int) := by simpa using hposd
  have hlt' : ((vm_brk (m_vmmaps m)).toNat : Int) < (r.toNat : Int) := by simpa using hlt
  have hr0 : 0 ≤ (r.toNat : Int) := (bv_unsigned_range_u64 r).1
  have hr1 : (r.toNat : Int) < 2 ^ 64 := by
    have := (bv_unsigned_range_u64 r).2
    simpa [two_pow_64] using this
  have hb0 : 0 ≤ ((vm_brk (m_vmmaps m)).toNat : Int) :=
    (bv_unsigned_range_u64 (vm_brk (m_vmmaps m))).1
  have hb1 : ((vm_brk (m_vmmaps m)).toNat : Int) < 2 ^ 64 := by
    have := (bv_unsigned_range_u64 (vm_brk (m_vmmaps m))).2
    simpa [two_pow_64] using this
  have hle : vm_brk (m_vmmaps m) ≤ r := by
    rw [BitVec.le_def]
    bvnorm
    omega
  have Hsz : bv_unsigned (r - vm_brk (m_vmmaps m))
      = bv_unsigned r - bv_unsigned (vm_brk (m_vmmaps m)) := by
    bvnorm
    rw [BitVec.toNat_sub_of_le hle]
    bvnorm
    omega
  refine ⟨?_, ?_⟩
  · intro a n hmem
    rcases List.mem_cons.mp hmem with h | h
    · cases h
      bvnorm
      bvnorm
      omega
    · exact Hnz a n h
  · intro p Hp
    simp only [owners]
    by_cases ho : owns_b (vm_brk (m_vmmaps m), (r - vm_brk (m_vmmaps m))) p = true
    · rw [ite_eq_left ho]
      have hbnd := owns_true _ _ p ho
      rw [Hsz] at hbnd
      have Hgok := brk_r_ok_grow m req r Hok
        (by
          unfold brk_is_grow
          simp only [Bool.and_eq_true]
          exact ⟨⟨by simp [hreq], by simpa using hpos⟩, by simpa using hlt⟩)
      unfold brk_grow_ok at Hgok
      dsimp only at Hgok
      have e2 : decide (0 < ((vm_brk (m_vmmaps m)).toNat : Int)) = true := by
        simp only [decide_eq_true_eq]; exact hpos
      have e3 : decide (((vm_brk (m_vmmaps m)).toNat : Int) < (r.toNat : Int)) = true := by
        simp only [decide_eq_true_eq]; exact hlt'
      rw [ite_eq_left (by simp only [e2, e3, Bool.true_and])] at Hgok
      rw [Bool.and_eq_true] at Hgok
      obtain ⟨hinner, _hbud⟩ := Hgok
      have hlop : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) ≤ p :=
        page_round_up_Z_le_aligned _ p (by bvnorm; exact Hp) (by bvnorm; omega)
      have hphi : p < page_round_up_Z (r.toNat : Int) := by
        have h1 := page_round_up_Z_ge (r.toNat : Int) (by omega)
        bvnorm
        bvnorm
        omega
      have hlo_hi : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
          < page_round_up_Z (r.toNat : Int) := by omega
      rw [ite_eq_left hlo_hi] at hinner
      rw [Bool.and_eq_true] at hinner
      obtain ⟨hceil, hfree⟩ := hinner
      have hceil' : page_round_up_Z (r.toNat : Int) ≤ alloc_top (m_vmmaps m) := by
        simpa using hceil
      have hfree2 := region_free_app_r _ _ _ _ hfree
      have hlo0 : 0 ≤ page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) :=
        page_round_up_Z_nonneg _ (by omega)
      have hpage : page_size = 4096 := by decide
      have hsz0 : 0 ≤ page_round_up_Z (r.toNat : Int) + page_size
          - page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) := by omega
      have hszle : page_round_up_Z (r.toNat : Int) + page_size
          - page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
          ≤ page_round_up_Z (r.toNat : Int) + page_size := by omega
      have hao := alloc_top_page_lt (m_vmmaps m)
      have hsz1 : page_round_up_Z (r.toNat : Int) + page_size
          - page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) < 2 ^ 64 := by
        have h2 : alloc_top (m_vmmaps m) + page_size < 2 ^ 64 := by
          have := alloc_top_page_lt (m_vmmaps m)
          simpa [two_pow_64] using this
        bvnorm
        omega
      have hlo_lt : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) < 2 ^ 64 := by
        bvnorm
        bvnorm
        omega
      have hsz1' : page_round_up_Z (r.toNat : Int) + page_size
          - page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) < 2 ^ 64 := by
        bvnorm
        bvnorm
        omega
      have hown : owns_b (Z_to_bv 64 (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)),
          Z_to_bv 64 (page_round_up_Z (r.toNat : Int) + page_size
            - page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int))) p = true := by
        apply owns_intro
        · rw [u64 _ ⟨hlo0, hlo_lt⟩]
          exact hlop
        · rw [u64 _ ⟨hlo0, hlo_lt⟩, u64 _ ⟨hsz0, hsz1'⟩]
          bvnorm
          omega
      have hzero := region_free_no_owner (vm_maps (m_vmmaps m)) _ _ p hfree2 hown
      have hone := Hun p Hp
      bvnorm
      omega
    · rw [ite_eq_right ho]
      simpa using Hun p Hp

theorem brk_model_next_wf (m : Model) (req r : word)
    (Hok : brk_r_ok m req r = true) (Hwf : vm_wf (m_vmmaps m)) :
    vm_wf (brk_model_next (m_vmmaps m) req r) := by
  unfold vm_wf brk_model_next brk_maps_next
  try dsimp only
  split
  · rename_i hshrink
    have hlt2 : (r.toNat : Int) < ((vm_brk (m_vmmaps m)).toNat : Int) := by
      rw [Bool.and_eq_true] at hshrink
      simpa only [decide_eq_true_eq] using hshrink.2
    apply maps_wf_subtract
    · exact (bv_unsigned_range_u64 r).1
    · bvnorm; omega
    · have := (bv_unsigned_range_u64 (vm_brk (m_vmmaps m))).2
      simpa [two_pow_64] using this
    · exact Hwf
  · rename_i hnotshrink
    by_cases hgrow : brk_is_grow req r (vm_brk (m_vmmaps m)) = true
    · have hgrants : brk_grants req r (vm_brk (m_vmmaps m))
          = [(vm_brk (m_vmmaps m), (r - vm_brk (m_vmmaps m)))] := by
        unfold brk_grants
        rw [ite_eq_left hgrow]
      rw [hgrants]
      exact brk_grant_wf m req r Hok hgrow Hwf
    · have hgrants : brk_grants req r (vm_brk (m_vmmaps m)) = [] := by
        unfold brk_grants
        rw [ite_eq_right hgrow]
      rw [hgrants, List.nil_append]
      exact Hwf

theorem check_brk_preserves (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_brk req eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  unfold check_brk at H
  cases ws with
  | nil =>
    cases cs with
    | nil =>
      cases ci with
      | nil =>
        by_cases hc : (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (m_vmmaps m).vm_brk)
            && listNN_eqb us (brk_unmaps ret (m_vmmaps m).vm_brk)) = true
        · simp only [hc, ite_true] at H
          obtain ⟨rfl, rfl⟩ := H
          rw [Bool.and_eq_true] at hc
          obtain ⟨hok, _⟩ := hc
          rw [Bool.and_eq_true] at hok
          obtain ⟨hok, _⟩ := hok
          rw [vmm_brk_next]
          exact brk_model_next_wf m req ret hok Hwf
        · simp only [hc] at H
          exact absurd H (by simp)
      | cons _ _ => exact absurd H (by simp)
    | cons _ _ => exact absurd H (by simp)
  | cons _ _ => exact absurd H (by simp)

/-- THE CONTROL LEDGER for PART 2b's byte-total comparison: the same two
    SIZES as [wit_overlap], placed end to end instead of nested.  It is a
    definition rather than a hypothesis so that the open examples above
    can name it; nothing else in the file reads it. -/
def disjoint_ledger : List (word × word) :=
  [(Z_to_bv 64 69632, Z_to_bv 64 100), (Z_to_bv 64 65536, Z_to_bv 64 4096)]

/-- Every arm of `checked_table` is a member: the table's lookup only ever
    answers an arm the table lists. -/
theorem lookup_ca_In : ∀ (l : List CheckedArm) (n : Int) (c : CheckedArm),
    lookup_ca l n = some c → c ∈ l
  | [], n, c, H => by simp [lookup_ca] at H
  | hd :: tl, n, c, H => by
    simp only [lookup_ca] at H
    split at H
    · obtain rfl := Option.some.inj H
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookup_ca_In tl n c H)

/-- [init_model] hands out an EMPTY ledger, so it satisfies [vm_wf]: no
    entry to be nonzero and nothing to own a page.  The base case of the
    invariant. -/
theorem init_model_vm_wf (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    vm_wf (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  have hv : vm_maps (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [] := rfl
  refine ⟨?_, ?_⟩
  · intro a n h
    rw [hv] at h
    simp at h
  · rw [hv]
    intro p hp
    simp [owners]

end LinuxSem.Checks.VmMapsDisjoint

