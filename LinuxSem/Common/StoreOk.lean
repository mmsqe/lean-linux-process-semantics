/-
  * Common.StoreOk — discharging the machine-store bound

  `RiscvSemantics.store_ok segs m a n` is the premise every machine store
  carries: each of the `n` bytes from `a` must be writable in `wview`, the
  overlay merged over the 'w' segments.  It is the same view the syscall
  comment at `RiscvSemantics.store_ok` itself for why an unbounded store
  made `strong_universal` falsifiable).

  Proofs never unfold it.  Every store site in the examples is one of three
  shapes, and this file turns each into a one-line side condition:

  - the STACK: an address in the RLIMIT_STACK window
    `[init_sp - stack_max_size, init_sp)` that `Run.init_machine_state`
    (and its proof-side mirror `PropExec.wrap_mem`) zero-maps up front —
    `store_ok_wrap_window`;
  - a HEAP grant: an address inside a range some brk/mmap already
    zero-filled — `store_ok_zeros_hit`, or `store_ok_zmem` for the
    single-grant spelling the examples actually carry;
  - .data/.bss: an address in a WRITABLE segment, where `wview` falls
    through to the segment image whatever the overlay holds.  The per-byte
    condition is decidable, and is exactly `StreamSim.wseg_ok`, so an image
    settles its whole rw- window once by `vm_compute` and every store inside
    it costs two `lia`s — `store_ok_window`.

  On top of that: anywhere the proof has ALREADY stored, or that a syscall
  wrote, the overlay only grows, so an earlier `store_ok` still holds —
  `store_ok_mono` and the `mem_grows` instances below.

  The monotonicity story is what keeps store proofs cheap: a store site deep
  in a long `wbytes`/`apply_zeros` chain proves its bound against the
  ORIGINAL memory and lifts it through the chain, instead of re-deriving it
  against a term that grows with every step.  It is also what a loop
  invariant carries when its memory is quantified existentially and there is
  no `wrap_mem` left to peel back to: the invariant says `mem_grows wmem
  mem` and registers the projection in `store_ok_db`, which is where
  `solve_store_ok_inv` looks.

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  Conventions: `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` →
  `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)` (the spelling
  `Common/PropExec.lean` and `Common/CatExec.lean` use), `Z.of_nat n` →
  `(n : Int)`, `Z.to_N z` → the `Nat` offset this tree's `segment_byte_at`
  takes, `Z.leb a b = true` → the `decide (a ≤ b)` test, `Z.ltb a b` →
  `decide (a < b)`, `list` → `List`, `option` → `Option`, `lia` → `omega`.
 Argument lists are COMMA-separated where a tactic takes
    arguments — the house style of `Common/StepTac.lean`, which this file
    imports for `u_norm`.
  Overlap note: `Common/MemsetLib.lean` already carries a copy of the four
  range lemmas (`store_ok_mono`, `store_ok_all`, `store_ok_of_all`,
  `store_ok_sub`) in its own namespace, because `MemsetLib` needs them
  and was stated first.  This file is their home, and it states
  them at the same types; the two copies do not interact (different
  namespaces, neither imports the other).
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.StreamSim
import LinuxSem.Common.AllocSim
import LinuxSem.Common.Footprint

namespace LinuxSem.Common.StoreOk

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StreamSim
open LinuxSem.Common.AllocSim
open LinuxSem.Common.Footprint

/-- `Local Instance asanreflect_fx : PropExec.FPState :=
    PropExec.fx0` (the same device `Common/MemsetLib.lean` uses): the
    address-arithmetic helpers of `PropExec`/`CatExec` are stated in a
    section over an ambient `FPState` instance even though none of them
    mentions it.  Supplying `fx0` locally keeps this file's own statements
    FP-state-free, as the ones are. -/
local instance storeok_fx : FPState := fx0

-- Lean adds a section variable to a lemma's type only when the statement
-- mentions it, and this tree makes the binding explicit.
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Overlay growth

    `store_ok` only ever asks whether a byte is DEFINED, so the relevant
    order on overlays is definedness, not equality: writing bytes, or
    zero-filling a grant, can only add. -/

/-- Definedness order on memory overlays. -/
def mem_grows (m m' : word → Option byte) : Prop :=
  ∀ x, m x ≠ none → m' x ≠ none

theorem mem_grows_refl (m : word → Option byte) : mem_grows m m :=
  fun _ h => h

theorem mem_grows_trans {m1 m2 m3 : word → Option byte}
    (H12 : mem_grows m1 m2) (H23 : mem_grows m2 m3) : mem_grows m1 m3 :=
  fun x hx => H23 x (H12 x hx)

/-- `wview`'s segment fallback does not depend on the overlay, so a byte that
    was writable stays writable however the overlay grows: if the overlay had
    it, the larger one does; if it did not, both fall through to the same
    segment. -/
theorem wview_grows (segs : List Segment) {m m' : word → Option byte}
    (Hg : mem_grows m m') (x : word) (Hx : wview segs m x ≠ none) :
    wview segs m' x ≠ none := by
  cases hm' : m' x with
  | some b => simp [wview, hm']
  | none =>
    -- `m x` cannot be defined, or `Hg` would make `m' x` defined.
    have hm : m x = none := by
      cases hm1 : m x with
      | none => rfl
      | some b => exact absurd hm' (Hg x (by rw [hm1]; simp))
    -- both views now fall through to the same segment lookup
    simp only [wview, hm] at Hx
    simp only [wview, hm']
    exact Hx

theorem store_ok_mono (segs : List Segment) :
    ∀ (n : Nat) (m m' : word → Option byte) (a : word),
      mem_grows m m' → store_ok segs m a n = true → store_ok segs m' a n = true := by
  intro n
  induction n with
  | zero => intro m m' a _ _; rfl
  | succ n ih =>
    intro m m' a Hg H
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    have hstep' : store_ok segs m' a (n + 1)
        = (match wview segs m' a with
           | some _ => store_ok segs m' (a + 1) n
           | none => false) := rfl
    rw [hstep] at H
    rw [hstep']
    cases hv : wview segs m a with
    | none => rw [hv] at H; exact absurd H (by simp)
    | some b =>
      rw [hv] at H
      have hv' : wview segs m' a ≠ none := wview_grows segs Hg a (by rw [hv]; simp)
      cases hv2 : wview segs m' a with
      | none => exact absurd hv2 hv'
      | some b' => exact ih m m' (a + 1) Hg H

/-! ### The overlay operations grow it -/

theorem wbytes_grows : ∀ (bs : List byte) (m : word → Option byte) (a : word),
    mem_grows m (wbytes m a bs) := by
  intro bs
  induction bs with
  | nil => intro m a; exact mem_grows_refl m
  | cons b rest ih =>
    intro m a x Hx
    have hstep : wbytes m a (b :: rest)
        = wbytes (fun y => if bv_eqb y a then some b else m y) (a + 1) rest := rfl
    rw [hstep]
    refine ih (fun y => if bv_eqb y a then some b else m y) (a + 1) x ?_
    by_cases h : bv_eqb x a
    · simp only [h, ite_true]; simp
    · simp only [h, ite_false]; exact Hx

theorem apply_zeros_grows : ∀ (zs : List (word × word)) (m : word → Option byte),
    mem_grows m (apply_zeros m zs) := by
  intro zs
  induction zs with
  | nil => intro m; exact mem_grows_refl m
  | cons z zs ih =>
    intro m x Hx
    have hstep : apply_zeros m (z :: zs)
        = fun a => if zeros_cover (z :: zs) a then some (BitVec.ofInt 8 0) else m a := rfl
    rw [hstep]
    by_cases h : zeros_cover (z :: zs) x
    · simp only [h, ite_true]; simp
    · simp only [h, ite_false]; exact Hx

theorem zmem_grows (m : word → Option byte) (b l : word) :
    mem_grows m (zmem m b l) := by
  intro x Hx
  unfold zmem
  by_cases h : (decide ((b.toNat : Int) ≤ (x.toNat : Int)) &&
      decide ((x.toNat : Int) < (b.toNat : Int) + (l.toNat : Int)))
  · simp only [h, ite_true]; simp
  · simp only [h, ite_false]; exact Hx

theorem write_to_mem_grows : ∀ (bs : List byte) (m : word → Option byte) (a : word),
    mem_grows m (write_to_mem m a bs) := by
  intro bs
  induction bs with
  | nil => intro m a; exact mem_grows_refl m
  | cons b rest ih =>
    intro m a x Hx
    have hstep : write_to_mem m a (b :: rest)
        = write_to_mem (fun y => if bv_eqb y a then some b else m y) (a + 1) rest := rfl
    rw [hstep]
    refine ih (fun y => if bv_eqb y a then some b else m y) (a + 1) x ?_
    by_cases h : bv_eqb x a
    · simp only [h, ite_true]; simp
    · simp only [h, ite_false]; exact Hx

theorem apply_writes_grows : ∀ (ws : List (word × List byte)) (m : word → Option byte),
    mem_grows m (apply_writes m ws) := by
  intro ws
  induction ws with
  | nil => intro m; exact mem_grows_refl m
  | cons w ws ih =>
    obtain ⟨a, bs⟩ := w
    intro m x Hx
    have hstep : apply_writes m ((a, bs) :: ws)
        = apply_writes (write_to_mem m a bs) ws := rfl
    rw [hstep]
    exact ih (write_to_mem m a bs) x (write_to_mem_grows bs m a x Hx)

/-! ## Ranges

    The workhorse: a range every byte of which the overlay already defines.
    Stated over `wview` so the segment fallback counts too (a store into
    .data needs no overlay entry). -/

/-- A range every byte of which is writable passes `store_ok`.   -/
theorem store_ok_of_all (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word),
      (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (∀ x : word,
        (a.toNat : Int) ≤ (x.toNat : Int) →
        (x.toNat : Int) < (a.toNat : Int) + (n : Int) →
        wview segs m x ≠ none) →
      store_ok segs m a n = true := by
  intro n
  induction n with
  | zero => intro a _ _; rfl
  | succ n ih =>
    intro a Hnw Hall
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep]
    have hwa : wview segs m a ≠ none := Hall a (by omega) (by omega)
    cases hv : wview segs m a with
    | none => exact absurd hv hwa
    | some b =>
      -- The successor address is only ever needed when bytes remain: on the
      -- LAST byte `a + 1` may wrap (a one-byte store at the top of the
      -- address space is legal), and the recursion stops before using it.
      refine ih (a + 1) ?_ ?_
      · by_cases hlt : (a.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int)
        · have hu := u_add1 a hlt
          omega
        · -- no room left, so the remaining range is empty
          have hn : n = 0 := by omega
          subst hn
          have := (u64_range (a + 1)).2
          omega
      · intro x Hx1 Hx2
        by_cases hlt : (a.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int)
        · have hu := u_add1 a hlt
          exact Hall x (by omega) (by omega)
        · omega

/-! ## The stack window

    `PropExec.wrap_mem` is the proof-side mirror of the initial overlay: the
    argv/envp/auxv block, then `some 0` everywhere in
    `[sp - stack_max_size, sp)`.  A store wholly inside that window is
    therefore always in bounds — which is the point of the window, and the
    reason `store_ok` does not need `sp` threaded into `step`. -/

theorem wrap_mem_window_defined (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (x : word) (uid hw : word) (rnd : EntryDraw)
    (Hlo : (sp.toNat : Int) - stack_max_size ≤ (x.toNat : Int))
    (Hhi : (x.toNat : Int) < (sp.toNat : Int)) :
    wrap_mem ph sp argv envp uid hw rnd x ≠ none := by
  unfold wrap_mem
  cases hs : stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x with
  | some b => simp
  | none =>
    -- the zero-fill guard: both comparisons hold, so the byte reads as `0`
    have hcond : (decide ((sp.toNat : Int) - stack_max_size ≤ (x.toNat : Int)) &&
        decide ((x.toNat : Int) < (sp.toNat : Int))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Hlo, Hhi⟩
    simp only [hs, hcond, ite_true]
    simp

theorem store_ok_wrap_window (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (a : word) (n : Nat) (uid hw : word)
    (rnd : EntryDraw)
    (Hlo : (sp.toNat : Int) - stack_max_size ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (sp.toNat : Int)) :
    store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a n = true := by
  refine store_ok_of_all segs _ n a ?_ ?_
  · -- `sp` itself fits the address space, and the window sits below it
    have := (u64_range sp).2
    omega
  · intro x Hx1 Hx2
    unfold wview
    cases hwv : wrap_mem ph sp argv envp uid hw rnd x with
    | some b => simp
    | none =>
      exact absurd hwv (wrap_mem_window_defined ph sp argv envp x uid hw rnd
        (by omega) (by omega))

/-! ## Grants

    A store into a range brk or mmap already zero-filled.  `apply_zeros`
    maps every covered address, so the side condition is exactly
    `zeros_cover` on each byte — and the caller usually has the grant bounds
    in hand already. -/

theorem store_ok_zeros_hit (segs : List Segment) (m : word → Option byte)
    (zs : List (word × word)) (a : word) (n : Nat)
    (Hne : zs ≠ [])
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hcov : ∀ x : word,
      (a.toNat : Int) ≤ (x.toNat : Int) →
      (x.toNat : Int) < (a.toNat : Int) + (n : Int) →
      zeros_cover zs x = true) :
    store_ok segs (apply_zeros m zs) a n = true := by
  refine store_ok_of_all segs _ n a Hnw ?_
  intro x Hx1 Hx2
  cases zs with
  | nil => exact absurd rfl Hne
  | cons z zs =>
    have hz : apply_zeros m (z :: zs) x = some (BitVec.ofInt 8 0) := by
      have hstep : apply_zeros m (z :: zs)
          = fun a => if zeros_cover (z :: zs) a then some (BitVec.ofInt 8 0) else m a := rfl
      rw [hstep]
      simp only [Hcov x Hx1 Hx2, ite_true]
    simp only [wview, hz]
    simp

/-- `AllocSim.zmem` is the single-grant spelling of `apply_zeros` the
    brk/mmap examples carry, and the one their store sites actually face.
    Same fact, without the `zeros_cover` bookkeeping. -/
theorem store_ok_zmem (segs : List Segment) (m : word → Option byte)
    (b l a : word) (n : Nat)
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (zmem m b l) a n = true := by
  refine store_ok_of_all segs _ n a Hnw ?_
  intro x Hx1 Hx2
  have hz : zmem m b l x = some (BitVec.ofInt 8 0) := by
    unfold zmem
    have hcond : (decide ((b.toNat : Int) ≤ (x.toNat : Int)) &&
        decide ((x.toNat : Int) < (b.toNat : Int) + (l.toNat : Int))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by omega⟩
    rw [hcond]
    simp
  simp only [wview, hz]
  simp

/-- The copy-loop lemmas take the memory they write into ABSTRACTLY (a read
    hypothesis), so they cannot appeal to `store_ok_zmem` themselves.
    `store_grant_ok segs m b l` is the hypothesis they carry instead: the
    whole grant is writable in `m`.  One hypothesis at the top covers every
    iteration, since the loop's own stores are peeled off
    (`store_ok_peel`) before it is applied — or lifted through with
    `store_grant_mono` where that is more convenient. -/
def store_grant_ok (segs : List Segment) (m : word → Option byte) (b l : word) : Prop :=
  ∀ (a : word) (n : Nat),
    (b.toNat : Int) ≤ (a.toNat : Int) →
    (a.toNat : Int) + (n : Int) ≤ (b.toNat : Int) + (l.toNat : Int) →
    store_ok segs m a n = true

theorem store_grant_zmem (segs : List Segment) (m : word → Option byte)
    (b l : word)
    (Hnw : (b.toNat : Int) + (l.toNat : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    store_grant_ok segs (zmem m b l) b l := by
  intro a n Hlo Hhi
  exact store_ok_zmem segs m b l a n (by omega) Hlo Hhi

/-- A page-rounded physical grant is also a writable grant for any logical
    prefix at the same base.  `brk` accounts for the prefix in its live-byte
    budget while the kernel maps the enclosing pages. -/
theorem store_grant_zmem_prefix (segs : List Segment) (m : word → Option byte)
    (b logical physical : word)
    (Hle : (logical.toNat : Int) ≤ (physical.toNat : Int))
    (Hnw : (b.toNat : Int) + (physical.toNat : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    store_grant_ok segs (zmem m b physical) b logical := by
  intro a n Hlo Hhi
  exact store_ok_zmem segs m b physical a n (by omega) Hlo (by omega)

theorem store_grant_mono (segs : List Segment) (m m' : word → Option byte)
    (b l : word)
    (Hg : mem_grows m m') (H : store_grant_ok segs m b l) :
    store_grant_ok segs m' b l := by
  intro a n Hlo Hhi
  exact store_ok_mono segs n m m' a Hg (H a n Hlo Hhi)

/-! ## Writable segments

    A store into .data/.bss needs no overlay entry at all: `wview` falls
    through to the segment.  Stated per byte so the caller can reuse
    whatever segment-bound facts it already `vm_compute`d. -/

theorem store_ok_seg_writable (segs : List Segment) (m : word → Option byte)
    (a : word) (n : Nat)
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hall : ∀ x : word,
      (a.toNat : Int) ≤ (x.toNat : Int) →
      (x.toNat : Int) < (a.toNat : Int) + (n : Int) →
      ∃ seg : Segment,
        find_segment segs (x.toNat : Int) 1 = some seg ∧
        seg_writable seg = true ∧
        segment_byte_at seg.seg_bytes (x.toNat - seg.seg_base) ≠ none) :
    store_ok segs m a n = true := by
  refine store_ok_of_all segs _ n a Hnw ?_
  intro x Hx1 Hx2
  obtain ⟨seg, Hfind, Hw, Hb⟩ := Hall x Hx1 Hx2
  unfold wview
  cases hm : m x with
  | some b => simp
  | none =>
    simp only [hm, Hfind, Hw, ite_true]
    exact Hb

/-! ### …decided once per image, for a whole window

    `store_ok_seg_writable` is stated per byte, which is awkward for a
    SYMBOLIC target such as `buf + i`: `find_segment` cannot be computed on
    an open address.  `StreamSim.wseg_ok` decides exactly the same per-byte
    condition on a CONCRETE range, so an image proves its writable window
    good once by `vm_compute` and every store site inside it becomes two
    `lia`s.  Nothing here mentions the overlay: the segment fallback is what
    carries the window, so the fact holds for every memory the proof ever
    reaches. -/
theorem store_ok_wseg (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word), wseg_ok segs a n = true → store_ok segs m a n = true := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a H
    have hw : wseg_ok segs a (n + 1)
        = (match find_segment segs (a.toNat : Int) 1 with
           | some seg =>
               (seg_writable seg &&
                 (match segment_byte_at seg.seg_bytes (a.toNat - seg.seg_base) with
                  | some _ => true
                  | none => false) &&
                 wseg_ok segs (a + 1) n)
           | none => false) := rfl
    rw [hw] at H
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep]
    cases hseg : find_segment segs (a.toNat : Int) 1 with
    | none => rw [hseg] at H; exact absurd H (by simp)
    | some seg =>
      rw [hseg] at H
      simp only [Bool.and_eq_true] at H
      obtain ⟨Hwrbyte, Hrec⟩ := H
      obtain ⟨Hwr, Hbyte⟩ := Hwrbyte
      cases hb : segment_byte_at seg.seg_bytes (a.toNat - seg.seg_base) with
      | none =>
        rw [hb] at Hbyte
        exact absurd Hbyte (by simp)
      | some b =>
        rw [hb] at Hbyte
        unfold wview
        cases hm : m a with
        | some b0 => simp only [hm]; exact ih (a + 1) Hrec
        | none =>
          simp only [hm, hseg, Hwr, hb, ite_true]
          exact ih (a + 1) Hrec

/-- The converse of `store_ok_of_all`: a good range is good byte by byte.
    Only used to cut a window down to one of its sub-ranges
    (`store_ok_sub`), which is what a store site actually needs. -/
theorem store_ok_all (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word),
      (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      store_ok segs m a n = true →
      ∀ x : word,
        (a.toNat : Int) ≤ (x.toNat : Int) →
        (x.toNat : Int) < (a.toNat : Int) + (n : Int) →
        wview segs m x ≠ none := by
  intro n
  induction n with
  | zero =>
    intro a _ _ x Hx1 Hx2
    omega
  | succ n ih =>
    intro a Hnw H x Hx1 Hx2
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep] at H
    cases hv : wview segs m a with
    | none => rw [hv] at H; exact absurd H (by simp)
    | some b =>
      rw [hv] at H
      by_cases heq : (x.toNat : Int) = (a.toNat : Int)
      · have hxa : x = a := by
          apply BitVec.eq_of_toNat_eq
          exact_mod_cast heq
        rw [hxa, hv]
        simp
      · -- `x` is past `a`, so at least one byte remains and `a + 1` cannot
        -- wrap — the only address at which it could is the last one.
        have hlt : (a.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int) := by omega
        have hu : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := u_add1 a hlt
        exact ih (a + 1) (by omega) H x (by omega) (by omega)

theorem store_ok_sub (segs : List Segment) (m : word → Option byte)
    (lo a : word) (N n : Nat)
    (Hnw : (lo.toNat : Int) + (N : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs m lo N = true)
    (Hl : (lo.toNat : Int) ≤ (a.toNat : Int))
    (Hh : (a.toNat : Int) + (n : Int) ≤ (lo.toNat : Int) + (N : Int)) :
    store_ok segs m a n = true := by
  refine store_ok_of_all segs m n a (by omega) ?_
  intro x Hx1 Hx2
  exact store_ok_all segs m N lo Hnw Hok x (by omega) (by omega)

/-- The per-image workhorse.  `base`/`hi` are the window's bounds as `Int`
    NUMERALS, tied to the `word` base and the `Nat` length by two
    conversions: `lia` is no good at `Z.of_nat` of a large decimal literal
    (it stays an `of_num_uint` atom), and every call site would otherwise
    have to work around that.  So the shape is: two `vm_compute`s for the
    numerals, the `vm_compute`d window fact, and the caller's two `Int`
    bounds. -/
theorem store_ok_window (segs : List Segment) (m : word → Option byte)
    (lo a : word) (N n : Nat) (base hi : Int)
    (Hbase : (lo.toNat : Int) = base)
    (Htop : base + (N : Int) = hi)
    (Hnw : hi ≤ ((2 ^ 64 : Nat) : Int))
    (Hw : wseg_ok segs lo N = true)
    (Hl : base ≤ (a.toNat : Int))
    (Hh : (a.toNat : Int) + (n : Int) ≤ hi) :
    store_ok segs m a n = true := by
  refine store_ok_sub segs m lo a N n ?_ (store_ok_wseg segs m N lo Hw) ?_ ?_ <;> omega

/- ######################################################################### -/
/- The KERNEL side of the same view: a read(2) buffer                        -/
/- ######################################################################### -/

/-! ## `store_ok` discharges a read BUFFER's writability too

    `read(2)` into a buffer raises the obligation

      read_bytes_map (ms_writable_byte segs ms) buf cnt = some w

    ("the kernel may copy `cnt` bytes to `buf`", the copy_to_user / EFAULT
    gate).  `StreamSim.wseg_ok`, a decidable predicate over the STATIC
    segment image, settles a buffer in .data/.bss by `vm_compute` but says
    nothing at all about a buffer in memory the process obtained from `mmap`
    or `brk`, where the segment image has no bytes and the whole grant lives
    in the overlay.  That is the `DrainAlg.Hread` obligation for every
    arena-based drain loop.

    No new theory is needed, because it is the SAME view: `store_ok` is
    "every byte of this range is defined in `wview`" and `read_bytes_map`
    over `ms_writable_byte` is "every byte of this range is defined in
    `wview`", and both recurse on `a + 1` in lockstep.  So the bridge below
    is an eight-line induction, and it hands the buffer obligation the
    ENTIRE store-side toolbox above: `store_ok_zmem` / `store_grant_ok` for
    a grant, `store_ok_window` for .data/.bss, `store_ok_wrap_window` for
    the stack, and `store_ok_mono` / `store_ok_peel` to lift any of them
    through the stores the loop has already performed.  In particular a
    per-binary proof discharges a read buffer with the very tactic it
    already uses for stores, `solve_store_ok`.

    Note what is NOT required: no no-wrap side condition.  `store_ok` stops
    before dereferencing the successor of its last byte, exactly as
    `read_bytes_aux` does, so a one-byte buffer at the top of the address
    space is fine on both sides. -/
theorem store_ok_read_aux (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word), store_ok segs m a n = true →
      ∃ w, read_bytes_aux (wview segs m) a n = some w := by
  intro n
  induction n with
  | zero => intro a _; exact ⟨[], rfl⟩
  | succ n ih =>
    intro a H
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep] at H
    cases hv : wview segs m a with
    | none => rw [hv] at H; exact absurd H (by simp)
    | some b =>
      rw [hv] at H
      obtain ⟨w, Hw⟩ := ih (a + 1) H
      refine ⟨b :: w, ?_⟩
      simp only [read_bytes_aux, hv, Hw]

theorem store_ok_wbuf (segs : List Segment) (ms : machine_state) (buf cnt : word)
    (H : store_ok segs ms.ms_mem buf (word_to_nat cnt) = true) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  rw [read_bytes_map_eq]
  exact store_ok_read_aux segs ms.ms_mem (word_to_nat cnt) buf H

/-- The `word_to_nat`/`bv_unsigned` conversion the two sides differ by: the
    buffer LENGTH arrives as a `word` (it is a register), and every bound a
    caller has about it is in `Int`. -/
theorem of_nat_word_to_nat (w : word) :
    ((word_to_nat w : Nat) : Int) = (w.toNat : Int) := rfl

/-! ## The grant case, which is the one that was missing

    A buffer inside an `mmap`/`brk` grant, stated against the
    `store_grant_ok` invariant a loop already carries: the whole grant is
    writable, so every sub-range of it is, so every read INTO it is
    admissible.  The two premises are pure `Int` arithmetic — `lia`-level
    effort at the call site, which is the point. -/
theorem store_grant_wbuf (segs : List Segment) (ms : machine_state)
    (b l buf cnt : word)
    (Hg : store_grant_ok segs ms.ms_mem b l)
    (Hlo : (b.toNat : Int) ≤ (buf.toNat : Int))
    (Hhi : (buf.toNat : Int) + (cnt.toNat : Int) ≤ (b.toNat : Int) + (l.toNat : Int)) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  refine store_ok_wbuf segs ms buf cnt (Hg buf (word_to_nat cnt) Hlo ?_)
  simpa only [of_nat_word_to_nat] using Hhi

/-- The same in `Common/Footprint`'s vocabulary, so a binary that has already
    named its arena `heap_rg base cur` discharges a read buffer by exhibiting
    `covers` — the identical obligation its stores raise, and monotone in the
    bump pointer through `heap_rg_bump`. -/
theorem heap_rg_wbuf (segs : List Segment) (ms : machine_state)
    (b l buf cnt : word) (cur : Int)
    (Hg : store_grant_ok segs ms.ms_mem b l)
    (Hcur : cur ≤ (b.toNat : Int) + (l.toNat : Int) - (b.toNat : Int))
    (Hc : covers (heap_rg b cur) buf (word_to_nat cnt)) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  obtain ⟨Hlo, Hhi⟩ := Hc
  -- `cbn [heap_rg rg_lo rg_hi]`: expose the two `Int` bounds
  simp only [heap_rg, Rg, region.rg_lo, region.rg_hi] at Hlo Hhi
  rw [of_nat_word_to_nat] at Hhi
  refine store_grant_wbuf segs ms b l buf cnt Hg (by omega) (by omega)

/-- A grant straight out of the `mmap`/`brk` step, before any store has been
    layered on: `zmem m b l` is the model's zero-filled overlay
    (`Run.apply_zeros` at one range, `MmapSim.zfill`).  With
    `store_ok_mono`/`store_grant_mono` this is what a loop invariant's
    `store_grant_ok` conjunct is INITIALIZED from. -/
theorem zmem_wbuf (segs : List Segment) (ms : machine_state) (m : word → Option byte)
    (b l buf cnt : word)
    (Hgr : mem_grows (zmem m b l) ms.ms_mem)
    (Hnw : (b.toNat : Int) + (l.toNat : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (buf.toNat : Int))
    (Hhi : (buf.toNat : Int) + (cnt.toNat : Int) ≤ (b.toNat : Int) + (l.toNat : Int)) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  refine store_grant_wbuf segs ms b l buf cnt ?_ Hlo Hhi
  exact store_grant_mono segs _ _ b l Hgr (store_grant_zmem segs m b l Hnw)

/-- Worked example / regression, in exactly the shape `DrainAlg`'s `Hread`
    hypothesis asks for: a drain loop that has already written into its arena
    still has a writable read buffer there, because the stores only GREW the
    overlay.  Two peels and three `lia`-level facts, and — the point — no
    `vm_compute` anywhere, which is what `StreamSim.wseg_ok` could only offer
    over a static segment. -/
theorem drain_buffer_in_grant (segs : List Segment) (ms : machine_state)
    (m : word → Option byte) (b l buf cnt : word) (a : word) (bs : List byte)
    (Hm : ms.ms_mem = wbytes (zmem m b l) a bs)
    (Hnw : (b.toNat : Int) + (l.toNat : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (buf.toNat : Int))
    (Hhi : (buf.toNat : Int) + (cnt.toNat : Int) ≤ (b.toNat : Int) + (l.toNat : Int)) :
    ∃ w, read_bytes_map (ms_writable_byte segs ms) buf cnt = some w := by
  refine zmem_wbuf segs ms m b l buf cnt ?_ Hnw Hlo Hhi
  rw [Hm]
  exact wbytes_grows bs (zmem m b l) a

/-!  This tree states each
    pair as one rule, because a Lean tactic arm that passes the growth lemma
    as an explicit argument to `refine` raises an *elaboration error* — not a
    tactic failure — when the goal's memory is of another shape, and `first`
    cannot backtrack over that.
    declarations: nothing below is a new fact, each is
    `store_ok_mono` composed with one growth lemma of the section above.
    These are also what make the arm list CHECKABLE: a tactic arm of the
    `refine … (grows …) ?_` shape is only elaborated when it fires, so a
    mistake in one arm can sit unnoticed until the call site that needs it —
    the smoke test at the end of this file peels a `wbytes`, a
    `write_to_mem`, an `apply_zeros` and an `apply_writes` chain for exactly
    that reason. -/

/-- A bound on the underlying memory lifts through a `wbytes` chain. -/
theorem store_ok_of_wbytes (segs : List Segment) (m : word → Option byte)
    (a : word) (bs : List byte) (c : word) (n : Nat) :
    store_ok segs m c n = true → store_ok segs (wbytes m a bs) c n = true :=
  fun H => store_ok_mono segs n m (wbytes m a bs) c (wbytes_grows bs m a) H

/-- …through a `write_to_mem` chain. -/
theorem store_ok_of_write_to_mem (segs : List Segment) (m : word → Option byte)
    (a : word) (bs : List byte) (c : word) (n : Nat) :
    store_ok segs m c n = true → store_ok segs (write_to_mem m a bs) c n = true :=
  fun H => store_ok_mono segs n m (write_to_mem m a bs) c (write_to_mem_grows bs m a) H

/-- …through an `apply_zeros` zero-fill. -/
theorem store_ok_of_apply_zeros (segs : List Segment) (m : word → Option byte)
    (zs : List (word × word)) (c : word) (n : Nat) :
    store_ok segs m c n = true → store_ok segs (apply_zeros m zs) c n = true :=
  fun H => store_ok_mono segs n m (apply_zeros m zs) c (apply_zeros_grows zs m) H

/-- …through an `apply_writes` write list. -/
theorem store_ok_of_apply_writes (segs : List Segment) (m : word → Option byte)
    (ws : List (word × List byte)) (c : word) (n : Nat) :
    store_ok segs m c n = true → store_ok segs (apply_writes m ws) c n = true :=
  fun H => store_ok_mono segs n m (apply_writes m ws) c (apply_writes_grows ws m) H

/-- …through a `zmem` grant.  `solve_store_ok` strips this one only AFTER
    `store_ok_base` has failed at the `zmem` layer (see the comment there). -/
theorem store_ok_of_zmem_grows (segs : List Segment) (m : word → Option byte)
    (b l c : word) (n : Nat) :
    store_ok segs m c n = true → store_ok segs (zmem m b l) c n = true :=
  fun H => store_ok_mono segs n m (zmem m b l) c (zmem_grows m b l) H

/-! ## Dispatch

    The tactic every store site calls.  It peels the overlay chain back to
    something with a known shape and closes the bound there; `lia` finishes
    the address arithmetic. -/
macro "store_ok_peel" : tactic =>
  `(tactic|
    repeat (first
      | apply store_ok_of_wbytes
      | apply store_ok_of_write_to_mem
      | apply store_ok_of_apply_zeros
      | apply store_ok_of_apply_writes))

/-- `stack_max_size` has to be unfolded: it is an atom to `lia`, and every
    stack bound is "8 MiB below sp is far enough below sp".
-/
macro "store_ok_base" : tactic =>
  `(tactic|
    first
    | (apply store_ok_wrap_window <;>
        first
        | (simp only [stack_max_size] at *; u_norm; omega)
        | (u_norm; omega))
    | (refine store_ok_zeros_hit _ _ _ _ _ _ ?_ ?_ ?_ <;>
        first
        | (intro h; cases h)
        | (u_norm; omega)
        | (intro x; intro h1; intro h2; u_norm; omega))
    | (apply store_ok_zmem <;> (u_norm; omega)))

/-- `zmem` is NOT part of `store_ok_peel`: a store into the grant is
    discharged AT the `zmem` layer (`store_ok_zmem`, in `store_ok_base`), so
    peeling past it would lose the only fact that closes it.  A store that
    is NOT in the grant — a stack slot, with a grant sitting on top of the
    memory — falls through to the second branch, which strips the `zmem` and
    keeps going.
    This tree runs it in each branch, which is the same thing — the peel is
    deterministic and leaves the goal in the same state — and is what a Lean
    alternative list can express: a `first` alternative is one tactic, and a
    side-effect-free peel in front of the list would have to be spliced as a
    sequence, which a cheap `first` cannot backtrack over. -/
macro "solve_store_ok" : tactic =>
  `(tactic|
    first
    | (store_ok_peel; store_ok_base)
    | (store_ok_peel; apply store_ok_of_zmem_grows; store_ok_peel; store_ok_base))

/-! ## Loop invariants

    Loop invariants quantify their memory EXISTENTIALLY ("some `mem` agreeing
    with `fmem` outside the scratch window"), so a stack store inside such a
    loop has no `wrap_mem` to peel back to.  The invariant carries
    `mem_grows wmem mem` instead — the overlay only ever grows — and the
    bound is lifted through it.

    The `mem_grows` fact is usually bundled into the example's memory
    invariant (`bg_ok mem`, `mem_ok mem`, ...), so the dispatcher cannot
    name it.  Each example registers its own projection here instead.
-/
macro "store_ok_grows" : tactic =>
  `(tactic| (first
    | assumption
    | (simp (config := { failIfUnchanged := false }) (discharger := assumption); done)))

macro "solve_store_ok_inv" : tactic =>
  `(tactic|
    first
    | solve_store_ok
    | (store_ok_peel; apply store_ok_mono <;>
         first
         | store_ok_grows
         | solve_store_ok))

/-- Re-establishing that conjunct after a step: the memory is the invariant's
    own (or the initial one) with writes on top. -/
macro "solve_mem_grows" : tactic =>
  `(tactic|
    repeat (first
      | store_ok_grows
      | exact mem_grows_refl _
      | (refine mem_grows_trans ?_ (wbytes_grows _ _ _))
      | (refine mem_grows_trans ?_ (zmem_grows _ _ _))
      | (refine mem_grows_trans ?_ (write_to_mem_grows _ _ _))
      | (refine mem_grows_trans ?_ (apply_zeros_grows _ _))
      | (refine mem_grows_trans ?_ (apply_writes_grows _ _))))

/-! ## Smoke tests

    One call site per tactic, in the shape the examples use them: the
    tactic layer is otherwise never exercised in this file, and a macro that
    is only defined is not a macro that works. -/

/-- The stack arm: a store wholly inside the RLIMIT_STACK window. -/
example (segs : List Segment) (ph : PhdrInfo) (sp a : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (Hlo : (sp.toNat : Int) - 8388608 ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + 8 ≤ (sp.toNat : Int)) :
    store_ok segs (wrap_mem ph sp argv envp uid hw rnd) a 8 = true := by
  solve_store_ok

/-- The grant arm: a store into a `zmem` grant. -/
example (segs : List Segment) (m : word → Option byte) (b l a : word)
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + 8 ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (zmem m b l) a 8 = true := by
  solve_store_ok

/-- Peel, then the grant arm: the store sits on top of a write chain. -/
example (segs : List Segment) (m : word → Option byte) (b l a c : word)
    (bs : List byte)
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + 8 ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (wbytes (zmem m b l) c bs) a 8 = true := by
  solve_store_ok

/-- The `apply_writes` and `apply_zeros` peel arms, stacked. -/
example (segs : List Segment) (m : word → Option byte) (b l a : word)
    (zs : List (word × word)) (ws : List (word × List byte))
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + 8 ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (apply_writes (apply_zeros (zmem m b l) zs) ws) a 8 = true := by
  solve_store_ok

/-- The `write_to_mem` peel arm. -/
example (segs : List Segment) (m : word → Option byte) (b l a c : word)
    (bs : List byte)
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + 8 ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (write_to_mem (zmem m b l) c bs) a 8 = true := by
  solve_store_ok

/-- A `mem_grows` projection tagged `[simp]`  closes the `inv` dispatcher's premise from the
    invariant. -/
theorem smoke_ok_grows_lem (m : word → Option byte) (a : word)
    (bs : List byte) : mem_grows m (wbytes m a bs) :=
  wbytes_grows bs m a

attribute [local simp] smoke_ok_grows_lem

/-- The `simp` half of `store_ok_grows` (no such fact in the context). -/
example (m : word → Option byte) (a : word) (bs : List byte) :
    mem_grows m (wbytes m a bs) := by
  store_ok_grows

/-- The loop-invariant arm: abstract memory, bound lifted through the
    invariant's registered `mem_grows` conjunct. -/
example (segs : List Segment) (m mem : word → Option byte) (b l a c : word)
    (bs : List byte)
    (Hnw : (c.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int))
    (Hlo : (b.toNat : Int) ≤ (c.toNat : Int))
    (Hhi : (c.toNat : Int) + 8 ≤ (b.toNat : Int) + (l.toNat : Int)) :
    store_ok segs (wbytes (zmem m b l) a bs) c 8 = true := by
  solve_store_ok_inv

/-- `solve_mem_grows` strips the write chain back to a reflexivity step. -/
example (m : word → Option byte) (a : word) (bs : List byte) :
    mem_grows m (wbytes m a bs) := by
  solve_mem_grows

example (m : word → Option byte) (b l a : word) (bs : List byte) :
    mem_grows m (wbytes (zmem m b l) a bs) := by
  solve_mem_grows

/-!  These pin the two
    definitions a store site computes with (the empty range is trivially
    writable, and definedness order has its two canonical instances). -/

example (segs : List Segment) (m : word → Option byte) (a : word) :
    store_ok segs m a 0 = true := rfl

example : mem_grows (fun _ => none) (fun _ => some (BitVec.ofInt 8 0)) := by
  intro x hx
  exact absurd rfl hx

example : ¬ mem_grows (fun _ => some (BitVec.ofInt 8 0)) (fun _ => none) := by
  intro h
  exact absurd rfl (h 0 (by simp))



/-- `testbit_drop_low`: bits at or above `j` do not see the low
    part `r < 2^j`. -/
theorem testbit_drop_low (q r j i : Nat) (hr : r < 2 ^ j) (hji : j ≤ i) :
    Nat.testBit (q * 2 ^ j + r) i = Nat.testBit (q * 2 ^ j) i := by
  have hsum : q * 2 ^ j + r = 2 ^ j * q + r := by rw [Nat.mul_comm q (2 ^ j)]
  have hmul : q * 2 ^ j = 2 ^ j * q := by rw [Nat.mul_comm q (2 ^ j)]
  rw [hsum, hmul, Nat.testBit_two_pow_mul_add (a := q) (b := r) (i := j) hr i,
    ite_eq_right (by omega), Nat.testBit_two_pow_mul]
  simp [hji]


/-- `testbit_mask`: the bits of the high mask `2^64 - 2^j` are
    exactly the positions `j <= i < 64`. -/
theorem testbit_mask_nat (j i : Nat) (hj : j ≤ 64) :
    Nat.testBit (2 ^ 64 - 2 ^ j) i = (decide (j ≤ i) && decide (i < 64)) := by
  have h2 : 2 ^ j * 2 ^ (64 - j) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hm : 2 ^ 64 - 2 ^ j = 2 ^ j * (2 ^ (64 - j) - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, h2]
  rw [hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases hji : j ≤ i
  · have hd : decide (i - j < 64 - j) = decide (i < 64) := by
      rcases Nat.lt_or_ge i 64 with h | h
      · simp [h, show i - j < 64 - j from by omega]
      · simp [h, show ¬ (i - j < 64 - j) from by omega]
    simp [hji, hd]
  · simp [hji]


/-- a value below the half modulus is
    fixed.  The bound `1 <= n` is this tree's `bv_swrap`-at-`0` caveat
    (`bv_swrap 0 z = -1`,); every call site below has
    `n >= 1`. -/
theorem bv_swrap_small (n : Nat) (hn : 1 ≤ n) (z : Int)
    (h : 0 ≤ z ∧ z < ((2 ^ (n - 1) : Nat) : Int)) : bv_swrap n z = z := by
  have hhalf : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    have hn1 : n = (n - 1) + 1 := by omega
    rw [hn1, Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
    rfl
  have hpos : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) := by
    rw [Int.natCast_pos]
    exact Nat.two_pow_pos _
  unfold bv_swrap
  rw [hhalf, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

end LinuxSem.Common.StoreOk
