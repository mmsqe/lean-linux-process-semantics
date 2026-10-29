/-
  * Common.LazyFrame — silent steps through a NON-EMPTY lazy ledger

  TRUST BOUNDARY: image-INDEPENDENT proof library (like
  [Common.DivergeSim], which this file extends).

  WHY THIS EXISTS.  Every silent-step idiom in the simulation library
  ([ShapeAlg.node_instr], [DivergeSim.ts_spin_no_lazy], the [msteps]
  combinators) carries the hypothesis [m_vm_lazy model = []]: with an
  empty lazy ledger the accounting layer erases and a raw
  [RiscvSemantics.step] equality is all a proof needs.  An ASan-style
  binary leaves that regime PERMANENTLY at its first successful
  MAP_NORESERVE reservation, and this file supplies the replacement:
  an instruction whose access report is DISJOINT from every lazy range
  materializes nothing, so the accounted step still preserves the
  model exactly ([materialize_model_accesses_disjoint], the common
  generalization of [State.materialize_model_accesses_no_lazy] and
  [DivergeSim.materialize_model_accesses_nil] — both are its vacuous
  instances), and the [to_spin] smart-constructor family gains the
  disjoint spellings ([ts_spin_disjoint] / [ts_step_disjoint]).

  DOES AN ASAN-STYLE MAP_NORESERVE RESERVATION FORCE A NON-EMPTY
  [m_vm_lazy] UNDER THIS SPEC?  YES — with file/line evidence:

  - [Sys/Mm/Mmap:323] defines [MAP_NORESERVE = 16384 (0x4000)];
    [Mmap:335-336] ([mmap_flags_core]) masks exactly that bit out
    before the anonymous shape is matched, so the ASan reservation
    shape (PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|
    MAP_NORESERVE, fd -1, off 0) IS the modeled shape
    ([mmap_modeled_b], Mmap:796-799), and [Mmap:338-339]
    ([mmap_noreserve_b]) reads the bit back at the one place it
    changes an answer.
  - The modeled grant applies [with_mmap_backing flags a n]
    ([Mmap:944] in [mmap_spec]'s rw branch; [Mmap:963-964] in the
    PROT_NONE branch; [Mmap:1138]/[Mmap:1288-1289] in the two
    MAP_FIXED branches), and [with_mmap_backing] ([Mmap:341-342])
    is [vm_add_lazy a n] whenever the bit is set.
  - [vm_add_lazy] ([State:2316-2317]) prepends
    [lazy_interior a n] to [m_vm_lazy]; [lazy_interior]
    ([State:2307-2314]) is the page-aligned interior, and a modeled
    grant is page-aligned with a page-rounded nonzero length
    ([Mmap:936-942]: [a mod page_size = 0], [0 < a],
    [nZ = page_round_up_Z len] with [len <> 0]), so
    [lazy_interior a n = [(a, n)]] — NON-EMPTY.
  - The entry persists until the range is unmapped or replaced
    ([vm_forget_range], [State:2237-2240]); an ordinary
    instruction step frames it ([Run.mi_account_step_model_frame],
    [Run:308-316]).
  - The reservation is also granted REGARDLESS of the remaining
    backed-memory budget ([mmap_noreserve_backed_ok],
    [Mmap:873-876], is unconditionally [true] for a NORESERVE
    call): the budget is charged per page on first touch, by
    [materialize_model_accesses] inside [mi_account_step]
    ([Run:277-287]).

  CONSEQUENCE FOR PROOFS.  After the shadow reservation succeeds, the
  no-lazy idiom is unavailable for the REST OF THE RUN on the grant
  path.  The constructor real proofs need there is the DISJOINT one:
  ASan's spin loop itself is access-free ([ts_spin_no_access] covers
  it with no hypothesis), but the straight line INTO the spin — and
  every ordinary load/store between the reservation and the program's
  other syscalls — needs [ts_step_disjoint] (its accesses land in the
  binary's data/stack segments, disjoint from the shadow reservation
  by the placement gate [grant_ok]'s region-freeness).  On the
  REFUSAL path of the reservation itself the ledger is still empty
  ([m_vm_lazy = []] before the first NORESERVE grant), so the
  no-lazy spellings — and [SpinAlg.srz_mmap_spin]'s hypotheses —
  apply as-is.

  The hypothesis shape: per access/range pair, the access does not
  wrap 2^64 (its page cursor is computed in [Z], [State:2110-2116])
  and its byte range is disjoint from the lazy range's byte range —
  the same [Z]-over-[bv_unsigned] discipline as every other bound in
  the spec ([BvBase]'s second rule).  When either list is empty the
  hypothesis is vacuous, which is exactly how the two existing lemmas
  fall out as instances.

  NOTES.

  - `Z` is `Int`, `nat` is `Nat`, `bv_unsigned a` is `(a.toNat : Int)`,
    `Z.of_nat n` is `(n : Int)`, records are structures.
 `Common/NoReserve.lean` DEFERS
    exactly that section with the note that restating the two
    predicates there would duplicate this file's definitions, so the
    section is present HERE, at the end, under its own banner (the
    lemmas are stated over this file's predicates and nothing else).
  - `materialize_model_accesses_nil` already exists as
    `Common.DivergeSim.materialize_model_accesses_nil` (its `accs = []`
    vacuous instance of the theorem below) and is NOT duplicated here.
-/

import LinuxSem.Common.DivergeSim

set_option autoImplicit false

namespace LinuxSem.Common.LazyFrame

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.DivergeSim (mi_account_step_of_accesses to_spin)

/- ================================================================= -/
/- The disjointness hypothesis                                       -/
/- ================================================================= -/

/-- `LazyFrame:94`.  Access [a, a + n) does not wrap and is disjoint
    from the byte range [lo, lo + sz).  The no-wrap conjunct is what
    ties the page cursor's unwrapped [Z] arithmetic back to the page's
    [word] base; every real access report satisfies it trivially
    (reported lengths are a few bytes and [alloc_ceiling] sits far below
    2^64). -/
def access_outside_range (a : word) (n : Nat) (lo sz : word) : Prop :=
  (a.toNat : Int) + (n : Int) ≤ 2 ^ 64 ∧
    ((a.toNat : Int) + (n : Int) ≤ (lo.toNat : Int) ∨
      (lo.toNat : Int) + (sz.toNat : Int) ≤ (a.toNat : Int))

/-- `LazyFrame:101`.  Every reported access is outside every lazy
    range.  Vacuously true when either list is empty. -/
def accesses_outside_lazy
    (accs : List (word × Nat)) (lazy : List (word × word)) : Prop :=
  ∀ a n lo sz, (a, n) ∈ accs → (lo, sz) ∈ lazy →
    access_outside_range a n lo sz

/- ================================================================= -/
/- Plumbing                                                          -/
/- ================================================================= -/

/-- `LazyFrame:110`.  A list all of whose elements fail the filter
    filters to the empty list. -/
theorem filter_all_false {A : Type} (f : A → Bool) (l : List A)
    (h : ∀ x, x ∈ l → f x = false) : l.filter f = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  rw [h x hx]
  simp

/-- `LazyFrame:119`.  Rebuilding a model from its own backing ledgers is
    the identity. -/
theorem with_vm_backing_id (m : Model) :
    with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m := rfl

/-- `LazyFrame:125`.  If no page is newly materialized, materialization
    just hands back the ledger it was given. -/
theorem materialize_accesses_no_new (lazy : List (word × word))
    (materialized : List word) (used limit : Int) (accs : List (word × Nat))
    (Hnew : newly_materialized_pages lazy materialized accs = []) :
    materialize_accesses lazy materialized used limit accs = some materialized := by
  simp only [materialize_accesses, Hnew]

/- ================================================================= -/
/- Which pages an access report can name                             -/
/- ================================================================= -/

/-- `LazyFrame:137`.  A page inserted into a list is the inserted page
    or was already there. -/
theorem page_insert_in (p q : word) (pages : List word)
    (h : p ∈ page_insert q pages) : p = q ∨ p ∈ pages := by
  unfold page_insert at h
  split at h
  · exact Or.inr h
  · rcases List.mem_cons.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'

/-- `LazyFrame:147`.  Every page the cursor inserts is the page of some
    byte offset [k < n] past [base] (in unwrapped [Z], matching the
    cursor). -/
theorem access_pages_acc_in (base : Int) (n : Nat) (pages : List word) (p : word)
    (h : p ∈ access_pages_acc base n pages) :
    p ∈ pages ∨ ∃ k, k < n ∧ p = page_base_of (base + (k : Int)) := by
  induction n generalizing base pages with
  | zero => exact Or.inl (by simpa [access_pages_acc] using h)
  | succ k ih =>
    simp only [access_pages_acc] at h
    rcases ih (base + 1) _ h with hin | ⟨j, hj, hp⟩
    · rcases page_insert_in _ _ _ hin with heq | hin
      · subst heq
        exact Or.inr ⟨0, by omega, by simp⟩
      · exact Or.inl hin
    · refine Or.inr ⟨j + 1, by omega, ?_⟩
      rw [hp]
      congr 1
      omega

/-- `LazyFrame:161`.  Every page an access report can name is either
    already in the list or is the page of some byte [k < n] past one of
    the report's accesses. -/
theorem accesses_pages_in (accs : List (word × Nat)) (pages : List word) (p : word)
    (h : p ∈ accesses_pages accs pages) :
    p ∈ pages ∨ ∃ a n k, (a, n) ∈ accs ∧ k < n
      ∧ p = page_base_of ((a.toNat : Int) + (k : Int)) := by
  induction accs generalizing pages with
  | nil => exact Or.inl (by simpa [accesses_pages] using h)
  | cons x accs ih =>
    obtain ⟨aw, n⟩ := x
    simp only [accesses_pages] at h
    rcases ih _ h with hin | ⟨a', n', k, hin', hk, hp⟩
    · rcases access_pages_acc_in (aw.toNat : Int) n pages p hin with hp' | ⟨k, hk, hp'⟩
      · exact Or.inl hp'
      · exact Or.inr ⟨aw, n, k, List.mem_cons_self, hk, hp'⟩
    · exact Or.inr ⟨a', n', k, List.mem_cons_of_mem _ hin', hk, hp⟩

/-- The page base of a non-negative, non-wrapping `Z` offset is that
    offset rounded DOWN to a page, read back into `Z` — the `bv_unsigned`
    side of  inline `rewrite Z_to_bv_unsigned; apply bv_wrap_small`
    step in `page_in_ranges_outside`.  (`page_base_of` is
    `Z_to_bv 64 ((z / page_size) * page_size)`; this reads the `Z` value
    back out of the `word`, which is the identity exactly while the
    rounded value sits in `[0, 2^64)`.) -/
theorem page_base_of_toNat (z : Int) (hz0 : 0 ≤ z) (hzlt : z < 2 ^ 64) :
    ((page_base_of z).toNat : Int) = (z / page_size) * page_size := by
  have hps : page_size = 4096 := rfl
  unfold page_base_of
  generalize hq : (z / page_size) * page_size = q
  rw [BitVec.toNat_ofInt]
  have hq0 : 0 ≤ q := by
    rw [← hq, hps]
    exact Int.mul_nonneg (Int.ediv_nonneg hz0 (by decide)) (by decide)
  have hqlt : q < 2 ^ 64 := by
    have hm0 : 0 ≤ z % 4096 := Int.emod_nonneg z (by decide)
    have hdm := Int.mul_ediv_add_emod z 4096
    simp only [hps] at hq hdm ⊢
    have hcomm : z / 4096 * 4096 = 4096 * (z / 4096) := Int.mul_comm _ _
    omega
  have hcast : ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) := by decide
  rw [hcast, Int.emod_eq_of_lt hq0 hqlt, Int.toNat_of_nonneg hq0]

/-- `LazyFrame:182`.  The page of a byte inside a disjoint,
    non-wrapping access is not wholly contained in any of the lazy
    ranges. -/
theorem page_in_ranges_outside (lazy : List (word × word)) (a : word) (n k : Nat)
    (Hk : k < n)
    (Hout : ∀ lo sz, (lo, sz) ∈ lazy → access_outside_range a n lo sz) :
    page_in_ranges (page_base_of ((a.toNat : Int) + (k : Int))) lazy = false := by
  generalize hz : (a.toNat : Int) + (k : Int) = z
  rw [page_in_ranges, List.any_eq_false]
  rintro ⟨lo, sz⟩ Hin Htrue
  rw [Bool.and_eq_true] at Htrue
  obtain ⟨h1, h2⟩ := Htrue
  have h1' : (lo.toNat : Int) ≤ ((page_base_of z).toNat : Int) := of_decide_eq_true h1
  have h2' : ((page_base_of z).toNat : Int) + page_size
      ≤ (lo.toNat : Int) + (sz.toNat : Int) := of_decide_eq_true h2
  obtain ⟨Hnw, Hdisj⟩ := Hout lo sz Hin
  have hz0 : 0 ≤ z := by rw [← hz]; have := a.isLt; omega
  have hzlt : z < 2 ^ 64 := by rw [← hz]; omega
  have hle : ((page_base_of z).toNat : Int) ≤ z := by
    rw [page_base_of_toNat z hz0 hzlt]
    exact Int.ediv_mul_le z (by decide)
  have hlt : z < ((page_base_of z).toNat : Int) + page_size := by
    rw [page_base_of_toNat z hz0 hzlt]
    have hdm := Int.mul_ediv_add_emod z page_size
    have hmlt := Int.emod_lt_of_pos z (show 0 < page_size by decide)
    have hcomm : (z / page_size) * page_size = page_size * (z / page_size) :=
      Int.mul_comm _ _
    omega
  have hlt' : z < (lo.toNat : Int) + (sz.toNat : Int) := by omega
  rcases Hdisj with hd | hd
  · omega
  · omega

/- ================================================================= -/
/- The idempotence theorem and its accounted-step corollaries         -/
/- ================================================================= -/

/-- `LazyFrame:228`.  Accesses disjoint from every lazy range
    materialize nothing: the accounting layer is the identity on the
    model.  The common generalization of
    [State.materialize_model_accesses_no_lazy] (take
    [m_vm_lazy m = []]: the hypothesis is vacuous) and of
    [DivergeSim.materialize_model_accesses_nil] (take [accs = []]:
    ditto). -/
theorem materialize_model_accesses_disjoint (m : Model) (accs : List (word × Nat))
    (Hout : accesses_outside_lazy accs (m_vm_lazy m)) :
    materialize_model_accesses m accs = some m := by
  have Hnew : newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) accs = [] := by
    unfold newly_materialized_pages
    apply filter_all_false
    intro p Hp
    rcases accesses_pages_in accs [] p Hp with h | ⟨a, n, k, Hin, Hk, rfl⟩
    · simp at h
    · rw [page_in_ranges_outside (m_vm_lazy m) a n k Hk
        (fun lo sz Hlz => Hout a n lo sz Hin Hlz)]
      simp
  unfold materialize_model_accesses
  rw [materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
    (vm_backing_used m) ((m_vmmaps m).vm_limit) accs Hnew]
  simp only [with_vm_backing_id]

/-- `LazyFrame:252`.  An instruction whose access report is disjoint
    from every lazy range steps the machine and leaves the model alone —
    whatever the ledger holds. -/
theorem mi_account_step_disjoint (segs : List Segment) (ms : machine_state)
    (model : Model) (ms' : machine_state) (ranges : List (word × Nat))
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model)) :
    mi_account_step segs ms model = .MachineOk (ms', model) := by
  rw [mi_account_step_of_accesses segs ms model ms' ranges Hstep]
  rw [materialize_model_accesses_disjoint model ranges Hout]

/- ================================================================= -/
/- The disjoint smart constructors for DivergeSim's Layer 2           -/
/- ================================================================= -/

/-- `LazyFrame:270`.  The one-step fixpoint, entered on an
    instruction with a disjoint (rather than empty) access report. -/
theorem ts_spin_disjoint (segs : List Segment) (ms : machine_state)
    (model : Model) (ranges : List (word × Nat))
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model)) :
    to_spin segs ms model :=
  to_spin.ts_spin ms model Hsvc
    (mi_account_step_disjoint segs ms model ms ranges Hstep Hout)

/-- `LazyFrame:286`.  A straight-line step INTO a spin, through a
    load/store whose accesses avoid the lazy ledger — the constructor
    the ASan grant path needs, where [m_vm_lazy] is permanently
    non-empty and [ts_step_no_lazy] is unavailable. -/
theorem ts_step_disjoint (segs : List Segment) (ms : machine_state)
    (model : Model) (ms' : machine_state) (ranges : List (word × Nat))
    (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges))
    (Hout : accesses_outside_lazy ranges (m_vm_lazy model))
    (Hspin : to_spin segs ms' model) :
    to_spin segs ms model :=
  to_spin.ts_step ms model ms' model Hsvc
    (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout) Hspin

/- ================================================================= -/
/- Disjointness plumbing                                             -/
/- ================================================================= -/

/- — this is the "Disjointness plumbing" section of
    `Common/NoReserve.lean`, which leaves it here because the two
    predicates it is about are OWED BY THIS FILE (`LazyFrame`'s own
    introduction, and the section above): restating them in
    NoReserve would duplicate this module's definitions.  It is present
    here, immediately after the predicates it belongs to, and is stated
    only over `access_outside_range` / `accesses_outside_lazy`. -/

/-- `NoReserve:138`.  [access_outside_range] is monotone in the access
    length. -/
theorem access_outside_range_mono (a : word) (n n' : Nat) (lo sz : word)
    (Hle : n' ≤ n) (H : access_outside_range a n lo sz) :
    access_outside_range a n' lo sz := by
  obtain ⟨Hnw, Hd⟩ := H
  refine ⟨by omega, ?_⟩
  rcases Hd with Hd | Hd
  · exact Or.inl (by omega)
  · exact Or.inr Hd

/-- `NoReserve:148`.  Disjointness restricts along access-list
    inclusion. -/
theorem accesses_outside_lazy_incl (accs accs' : List (word × Nat))
    (lazy : List (word × word))
    (Hincl : ∀ x, x ∈ accs' → x ∈ accs)
    (Hout : accesses_outside_lazy accs lazy) :
    accesses_outside_lazy accs' lazy :=
  fun a n lo sz Hin Hlz => Hout a n lo sz (Hincl _ Hin) Hlz

theorem accesses_outside_lazy_app_l (accs1 accs2 : List (word × Nat))
    (lazy : List (word × word))
    (Hout : accesses_outside_lazy (accs1 ++ accs2) lazy) :
    accesses_outside_lazy accs1 lazy :=
  accesses_outside_lazy_incl (accs1 ++ accs2) accs1 lazy
    (fun _ Hx => List.mem_append_left _ Hx) Hout

theorem accesses_outside_lazy_app_r (accs1 accs2 : List (word × Nat))
    (lazy : List (word × word))
    (Hout : accesses_outside_lazy (accs1 ++ accs2) lazy) :
    accesses_outside_lazy accs2 lazy :=
  accesses_outside_lazy_incl (accs1 ++ accs2) accs2 lazy
    (fun _ Hx => List.mem_append_right _ Hx) Hout

/-- `NoReserve:181`.  A shorter access at the same base stays outside
    (the write node's per-delivery instance: disjointness of the FULL
    buffer covers every delivered prefix). -/
theorem accesses_outside_lazy_shrink (a : word) (len n : Nat)
    (lazy : List (word × word))
    (Hle : n ≤ len) (Hout : accesses_outside_lazy [(a, len)] lazy) :
    accesses_outside_lazy [(a, n)] lazy := by
  intro a' n' lo sz Hin Hlz
  rw [List.mem_singleton] at Hin
  cases Hin
  exact access_outside_range_mono a len n lo sz Hle
    (Hout a len lo sz (by simp) Hlz)
