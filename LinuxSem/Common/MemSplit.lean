/-
  * Common.MemSplit — a three-region view of the writable overlay for walks
      that start from [Run.init_machine_state].

  Image-INDEPENDENT.

  The initial overlay ([PropExec.wrap_mem]) is: the argv/envp/auxv block
  at/above the initial stack pointer [sp0]; [Some 0] on the RLIMIT_STACK
  window [[sp0 - stack_max_size, sp0)]; [None] (fall through to the image)
  everywhere else.  A program's stores land either in the window (stack
  frames) or below it (.data/.bss).  [cmem sp0 mem0 J D] keeps the three
  regions apart:

  - at/above [sp0]:        [mem0] (never written; the initial block),
  - the window:            [J]    ("junk": stack frames),
  - below the window:      [D]    (data overlay, literal addresses).

  so that a store commutes into exactly one of [J]/[D]
  ([wbytes_cmem_win]/[wbytes_cmem_data]), a read selects exactly one
  region ([rdn_cmem_above]/[rdn_cmem_win]/[rdn_cmem_data]), and the store
  bound for a window store is the invariant [wfJ] ([store_ok_cmem_win]).
  [cmem_init] rewrites the initial overlay into this form.

  The entry draw ([Run.en_draw]) fixes the AT_RANDOM bytes
  (at_random_bytes (ed_random draw)); AT_HWCAP is the auxv's fourth pair
  (10 pairs / 20 words, auxv_size 160); the mapped image is
  [Run.entry_stack_image] (block ++ page slack).

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  * `Z` → `Int`, `N`/`nat` → `Nat`, `bv_unsigned w` → `(w.toNat : Int)`,
    `Z.of_nat n` → `(n : Int)`, `Z_to_bv 8 0` → `BitVec.ofInt 8 0`,
    `repeat b n` → `List.replicate n b`, `nth k l d` → `l.getD k d`,
    `forall x, ...` binders → explicit `∀ x, ...`.

  * The  comparisons are stdlib `Z` BOOLEANS
    (`(bv_unsigned sp0 <=? bv_unsigned a)`, `Z.leb`/`Z.ltb`).  This tree
    states the same tests as Lean PROPOSITIONS: [cmem] branches on
    `(sp0.toNat : Int) ≤ (a.toNat : Int)` (Lean's `if` on a decidable
    proposition), and the two selector lemmas [wbytes_select]/
    [wbytes_select_r] take `P : word → Prop` with a `DecidablePred`
    instance instead of `P : word → bool`.
  * The lemmas needing the [FPState]-carrying store/read vocabulary
    ([wbytes_above], [wbytes_below], [rdn_ext], [u64_range]) are proved
    under a local [fx0] instance, exactly as `Common/StoreOk.lean` and
    `Common/MemsetLib.lean` do: no statement below mentions the FP state,
    so fixing the instance to the entry state is invisible in the API.

  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StreamSim

namespace LinuxSem.Common.MemSplit

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamSim
open LinuxSem.Common.StoreOk

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The `FPState` instance this file's proofs run under (see the notes above). -/
local instance memsplit_fx : FPState := fx0

/-! ## Pointwise description of [wbytes] -/

/-- The byte [wbytes] leaves at an address inside the written range. -/
theorem wbytes_inside (bs : List byte) (m : word → Option byte) (a x : word)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hx : (a.toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int)) :
    wbytes m a bs x
      = some (bs.getD ((x.toNat : Int) - (a.toNat : Int)).toNat (BitVec.ofInt 8 0)) := by
  induction bs generalizing m a with
  | nil =>
    simp only [List.length_nil] at Hx
    omega
  | cons b rest ih =>
    simp only [wbytes, List.length_cons, Int.natCast_add, Int.natCast_one] at Hnw Hx ⊢
    by_cases heq : (x.toNat : Int) = (a.toNat : Int)
    · -- [x] is the head: the head store decides it, the tail misses it.
      have hxa : x = a := by
        apply BitVec.eq_of_toNat_eq
        exact_mod_cast heq
      subst hxa
      have hzero : ((x.toNat : Int) - (x.toNat : Int)).toNat = 0 := by omega
      rw [hzero]
      have hne : bv_eqb x x = true := by
        unfold bv_eqb
        simp
      cases rest with
      | nil => simp only [wbytes, hne, ite_true, List.getD_cons_zero]
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at Hnw ⊢
        have hlt : (x.toNat : Int) + 1 < 2 ^ 64 := by omega
        have hu : (x + 1).toNat = x.toNat + 1 := toNat_add_one x (by omega)
        rw [wbytes_below (b' :: rest')
          (fun y => if bv_eqb y x then some b else m y) (x + 1) x
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)
          (by omega)]
        simp only [hne, ite_true, List.getD_cons_zero]
    · -- [x] is past the head: the head store misses it, the tail decides it.
      have hgt : (a.toNat : Int) < (x.toNat : Int) := by omega
      have hne : bv_eqb x a = false :=
        bv_eqb_neq x a (by
          intro hc
          have hx' : (x.toNat : Int) = (a.toNat : Int) := by rw [hc]
          omega)
      cases rest with
      | nil =>
        simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at Hx
        omega
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at Hnw Hx ⊢
        have hlt : (a.toNat : Int) + 1 < 2 ^ 64 := by omega
        have hu : (a + 1).toNat = a.toNat + 1 := toNat_add_one a (by omega)
        have hk : ((x.toNat : Int) - (a.toNat : Int)).toNat
            = ((x.toNat : Int) - ((a + 1).toNat : Int)).toNat + 1 := by
          have hsub : (x.toNat : Int) - ((a + 1).toNat : Int)
              = ((x.toNat : Int) - (a.toNat : Int)) - 1 := by omega
          rw [hsub]
          have h1 : ((((x.toNat : Int) - (a.toNat : Int)).toNat : Nat) : Int)
              = (x.toNat : Int) - (a.toNat : Int) := Int.toNat_of_nonneg (by omega)
          have h2 : ((((x.toNat : Int) - (a.toNat : Int) - 1).toNat : Nat) : Int)
              = (x.toNat : Int) - (a.toNat : Int) - 1 := Int.toNat_of_nonneg (by omega)
          omega
        rw [hk]
        simp only [hne, Bool.false_eq_true, ite_false, List.getD_cons_succ]
        rw [ih (fun y => if bv_eqb y a then some b else m y) (a + 1)
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)]

/-- A byte outside the written range is untouched. -/
theorem wbytes_outside (bs : List byte) (m : word → Option byte) (a x : word)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hx : (x.toNat : Int) < (a.toNat : Int) ∨
      (a.toNat : Int) + (bs.length : Int) ≤ (x.toNat : Int)) :
    wbytes m a bs x = m x := by
  rcases Hx with h | h
  · exact wbytes_below bs m a x Hnw h
  · exact wbytes_above bs m a x h

/-- [wbytes] commutes with any address selector that is constant on the
    written range. -/
theorem wbytes_select (P : word → Prop) [DecidablePred P]
    (f g : word → Option byte) (a : word) (bs : List byte)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (HP : ∀ x : word, (a.toNat : Int) ≤ (x.toNat : Int) →
      (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int) → P x) :
    wbytes (fun x => if P x then f x else g x) a bs
      = (fun x => if P x then wbytes f a bs x else g x) := by
  funext x
  by_cases hlt : (x.toNat : Int) < (a.toNat : Int)
  · -- below the range: BOTH sides reduce to the selector itself
    rw [wbytes_outside bs (fun x => if P x then f x else g x) a x Hnw (Or.inl hlt),
      wbytes_outside bs f a x Hnw (Or.inl hlt)]
  · by_cases hin : (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int)
    · -- inside the range: the selector is true, so both sides are [f]'s byte
      rw [wbytes_inside bs (fun x => if P x then f x else g x) a x Hnw ⟨by omega, hin⟩,
        wbytes_inside bs f a x Hnw ⟨by omega, hin⟩, ite_eq_left (HP x (by omega) hin)]
    · -- above the range: again both sides reduce to the selector itself
      rw [wbytes_outside bs (fun x => if P x then f x else g x) a x Hnw (Or.inr (by omega)),
        wbytes_outside bs f a x Hnw (Or.inr (by omega))]

/-- [wbytes_select] for a selector that is FALSE on the written range. -/
theorem wbytes_select_r (P : word → Prop) [DecidablePred P]
    (f g : word → Option byte) (a : word) (bs : List byte)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (HP : ∀ x : word, (a.toNat : Int) ≤ (x.toNat : Int) →
      (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int) → ¬ P x) :
    wbytes (fun x => if P x then f x else g x) a bs
      = (fun x => if P x then f x else wbytes g a bs x) := by
  funext x
  by_cases hlt : (x.toNat : Int) < (a.toNat : Int)
  · rw [wbytes_outside bs (fun x => if P x then f x else g x) a x Hnw (Or.inl hlt),
      wbytes_outside bs g a x Hnw (Or.inl hlt)]
  · by_cases hin : (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int)
    · rw [wbytes_inside bs (fun x => if P x then f x else g x) a x Hnw ⟨by omega, hin⟩,
        wbytes_inside bs g a x Hnw ⟨by omega, hin⟩, ite_eq_right (HP x (by omega) hin)]
    · rw [wbytes_outside bs (fun x => if P x then f x else g x) a x Hnw (Or.inr (by omega)),
        wbytes_outside bs g a x Hnw (Or.inr (by omega))]

/-- Two stores to the same slot: the later one wins. -/
theorem wbytes_shadow (m : word → Option byte) (a : word) (bs1 bs2 : List byte)
    (Hlen : bs1.length = bs2.length)
    (Hnw : (a.toNat : Int) + (bs2.length : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    wbytes (wbytes m a bs1) a bs2 = wbytes m a bs2 := by
  have Hnw1 : (a.toNat : Int) + (bs1.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [Hlen]; exact Hnw
  funext x
  by_cases hlt : (x.toNat : Int) < (a.toNat : Int)
  · rw [wbytes_outside bs2 (wbytes m a bs1) a x Hnw (Or.inl hlt),
      wbytes_outside bs1 m a x Hnw1 (Or.inl hlt),
      wbytes_outside bs2 m a x Hnw (Or.inl hlt)]
  · by_cases hin : (x.toNat : Int) < (a.toNat : Int) + (bs2.length : Int)
    · rw [wbytes_inside bs2 (wbytes m a bs1) a x Hnw ⟨by omega, hin⟩,
        wbytes_inside bs2 m a x Hnw ⟨by omega, hin⟩]
    · rw [wbytes_outside bs2 (wbytes m a bs1) a x Hnw (Or.inr (by omega)),
        wbytes_outside bs1 m a x Hnw1 (Or.inr (by omega)),
        wbytes_outside bs2 m a x Hnw (Or.inr (by omega))]

/-- A constant region reads back as [List.replicate]. -/
theorem rdn_const (segs : List Segment) (m : word → Option byte) :
    ∀ (a : word) (n : Nat) (b : byte),
      (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (∀ x : word, (a.toNat : Int) ≤ (x.toNat : Int) →
        (x.toNat : Int) < (a.toNat : Int) + (n : Int) → m x = some b) →
      rdn segs m a n = some (List.replicate n b) := by
  intro a n
  induction n generalizing a with
  | zero => intro b _ _; rfl
  | succ n ih =>
    intro b Hnw Hall
    simp only [rdn, List.replicate_succ]
    rw [Hall a (by omega) (by omega)]
    cases n with
    | zero => rfl
    | succ n' =>
      have hu : (a + 1).toNat = a.toNat + 1 := toNat_add_one a (by omega)
      rw [ih (a + 1) b (by omega) (by
        intro x hx1 hx2
        exact Hall x (by omega) (by omega))]

/-! ## The three-region overlay -/

/-- The bottom of the RLIMIT_STACK window: [stack_max_size] below the
    initial stack pointer. -/
def win_lo (sp0 : word) : Int := (sp0.toNat : Int) - stack_max_size

/-- [x] lies in the stack window [[win_lo sp0, sp0)]. -/
def in_win (sp0 : word) (x : word) : Prop :=
  win_lo sp0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < (sp0.toNat : Int)

/-- The three-region overlay: [mem0] at/above [sp0], [J] in the window, [D]
    below it. -/
def cmem (sp0 : word) (mem0 J D : word → Option byte) : word → Option byte :=
  fun a => if (sp0.toNat : Int) ≤ (a.toNat : Int) then mem0 a
           else if win_lo sp0 ≤ (a.toNat : Int) then J a else D a

/-- Window well-formedness: every window byte is mapped (so stores into the
    window are in bounds). -/
def wfJ (sp0 : word) (J : word → Option byte) : Prop :=
  ∀ x : word, in_win sp0 x → J x ≠ none

/-- A constant overlay is window-well-formed. -/
theorem wfJ_const (sp0 : word) (b : byte) : wfJ sp0 (fun _ => some b) :=
  fun _ _ => by simp

/-- Window well-formedness survives any [wbytes] on top of the overlay. -/
theorem wfJ_wbytes (sp0 : word) (J : word → Option byte) (a : word) (bs : List byte)
    (H : wfJ sp0 J) : wfJ sp0 (wbytes J a bs) :=
  fun x Hx => wbytes_grows bs J a x (H x Hx)

/-- "J' agrees with J at/above [lo]" — what a callee summary promises about
    the caller's frames. -/
def agree_above (lo : Int) (J J' : word → Option byte) : Prop :=
  ∀ x : word, lo ≤ (x.toNat : Int) → J' x = J x

theorem agree_above_refl (lo : Int) (J : word → Option byte) : agree_above lo J J :=
  fun _ _ => rfl

theorem agree_above_trans (lo : Int) (J1 J2 J3 : word → Option byte)
    (H12 : agree_above lo J1 J2) (H23 : agree_above lo J2 J3) : agree_above lo J1 J3 :=
  fun x Hx => (H23 x Hx).trans (H12 x Hx)

theorem agree_above_mono (lo lo' : Int) (J J' : word → Option byte)
    (Hle : lo ≤ lo') (H : agree_above lo J J') : agree_above lo' J J' :=
  fun x Hx => H x (by omega)

/-- A store entirely below [lo] keeps [agree_above lo]. -/
theorem agree_above_wbytes (lo : Int) (J : word → Option byte) (a : word) (bs : List byte)
    (Hle : (a.toNat : Int) + (bs.length : Int) ≤ lo) :
    agree_above lo J (wbytes J a bs) :=
  fun x Hx => wbytes_above bs J a x (by omega)

/-- Two overlays that agree at/above [lo] read back identically from [lo]
    onwards. -/
theorem rdn_agree_above (segs : List Segment) (lo : Int) (J J' : word → Option byte)
    (a : word) (n : Nat) (H : agree_above lo J J') (Hlo : lo ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs J' a n = rdn segs J a n :=
  rdn_ext segs n J' J a Hnw (fun x Hx => H x (by omega))

/-! ## [Section CMem]: the overlay at a FIXED [sp0]/[mem0] -/

section CMem

variable (sp0 : word) (mem0 : word → Option byte)

/-- The  local abbreviation `csel := cmem sp0 mem0` (unused there;
    kept as a name for the shorthand).  Locally we keep it out of the way of
    the section variables, so it is spelled fully applied. -/
def csel (J D : word → Option byte) : word → Option byte := cmem sp0 mem0 J D

/-- [stack_max_size] is positive (so [win_lo sp0 < sp0]). -/
theorem stack_max_size_pos : 0 < stack_max_size := by
  unfold stack_max_size
  omega

/-! ### Stores -/

/-- A store whose range lies in the window commutes into [J]. -/
theorem wbytes_cmem_win (J D : word → Option byte) (a : word) (bs : List byte)
    (Hlo : win_lo sp0 ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (bs.length : Int) ≤ (sp0.toNat : Int)) :
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D := by
  have Hsp : (sp0.toNat : Int) < ((2 ^ 64 : Nat) : Int) := (u64_range sp0).2
  have Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by omega
  unfold win_lo at Hlo
  unfold cmem win_lo
  rw [wbytes_select_r (fun x => (sp0.toNat : Int) ≤ (x.toNat : Int)) mem0
    (fun y => if (sp0.toNat : Int) - stack_max_size ≤ (y.toNat : Int) then J y else D y)
    a bs Hnw (fun x _ hx => by omega)]
  funext x
  by_cases h : (sp0.toNat : Int) ≤ (x.toNat : Int)
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    rw [wbytes_select (fun y => (sp0.toNat : Int) - stack_max_size ≤ (y.toNat : Int)) J D
      a bs Hnw (fun y _ hy => by omega)]

/-- A store whose range lies entirely below the window commutes into [D]. -/
theorem wbytes_cmem_data (J D : word → Option byte) (a : word) (bs : List byte)
    (Hhi : (a.toNat : Int) + (bs.length : Int) ≤ win_lo sp0) :
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs) := by
  have Hsp : (sp0.toNat : Int) < ((2 ^ 64 : Nat) : Int) := (u64_range sp0).2
  have Hpos : 0 < stack_max_size := stack_max_size_pos
  have Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    unfold win_lo at Hhi
    omega
  unfold win_lo at Hhi
  unfold cmem win_lo
  rw [wbytes_select_r (fun x => (sp0.toNat : Int) ≤ (x.toNat : Int)) mem0
    (fun y => if (sp0.toNat : Int) - stack_max_size ≤ (y.toNat : Int) then J y else D y)
    a bs Hnw (fun x _ hx => by omega)]
  funext x
  by_cases h : (sp0.toNat : Int) ≤ (x.toNat : Int)
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    rw [wbytes_select_r (fun y => (sp0.toNat : Int) - stack_max_size ≤ (y.toNat : Int)) J D
      a bs Hnw (fun x _ hx => by omega)]

/-! ### Reads -/

/-- A read at/above [sp0] reads [mem0]. -/
theorem rdn_cmem_above (segs : List Segment) (J D : word → Option byte) (a : word) (n : Nat)
    (Hlo : (sp0.toNat : Int) ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs mem0 a n := by
  refine rdn_ext segs n (cmem sp0 mem0 J D) mem0 a Hnw ?_
  intro x Hx
  unfold cmem
  rw [ite_eq_left (by omega)]

/-- A read inside the window reads [J]. -/
theorem rdn_cmem_win (segs : List Segment) (J D : word → Option byte) (a : word) (n : Nat)
    (Hlo : win_lo sp0 ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (sp0.toNat : Int)) :
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs J a n := by
  have Hsp : (sp0.toNat : Int) < ((2 ^ 64 : Nat) : Int) := (u64_range sp0).2
  refine rdn_ext segs n (cmem sp0 mem0 J D) J a (by omega) ?_
  intro x Hx
  unfold cmem
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- A read entirely below the window reads [D]. -/
theorem rdn_cmem_data (segs : List Segment) (J D : word → Option byte) (a : word) (n : Nat)
    (Hhi : (a.toNat : Int) + (n : Int) ≤ win_lo sp0) :
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n := by
  have Hsp : (sp0.toNat : Int) < ((2 ^ 64 : Nat) : Int) := (u64_range sp0).2
  have Hpos : 0 < stack_max_size := stack_max_size_pos
  have Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    unfold win_lo at Hhi
    omega
  refine rdn_ext segs n (cmem sp0 mem0 J D) D a Hnw ?_
  intro x Hx
  unfold cmem
  rw [ite_eq_right (by unfold win_lo at *; omega), ite_eq_right (by unfold win_lo at *; omega)]

/-- Single-address versions (for [mem x = ..] style facts): at/above [sp0]. -/
theorem cmem_at_above (J D : word → Option byte) (x : word)
    (H : (sp0.toNat : Int) ≤ (x.toNat : Int)) : cmem sp0 mem0 J D x = mem0 x := by
  unfold cmem
  rw [ite_eq_left H]

/-- Single-address version: inside the window. -/
theorem cmem_at_win (J D : word → Option byte) (x : word) (H : in_win sp0 x) :
    cmem sp0 mem0 J D x = J x := by
  obtain ⟨Hlo, Hhi⟩ := H
  unfold cmem
  rw [ite_eq_right (by omega), ite_eq_left Hlo]

/-- Single-address version: below the window. -/
theorem cmem_at_data (J D : word → Option byte) (x : word)
    (Hx : (x.toNat : Int) < win_lo sp0) : cmem sp0 mem0 J D x = D x := by
  have Hpos : 0 < stack_max_size := stack_max_size_pos
  unfold cmem
  rw [ite_eq_right (by unfold win_lo at *; omega), ite_eq_right (by unfold win_lo at *; omega)]

/-! ### Store bounds -/

/-- Every window byte must be mapped ([wfJ]): that is exactly the store
    bound for a store into the window. -/
theorem store_ok_cmem_win (segs : List Segment) (J D : word → Option byte)
    (a : word) (n : Nat) (HJ : wfJ sp0 J)
    (Hlo : win_lo sp0 ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (sp0.toNat : Int)) :
    store_ok segs (cmem sp0 mem0 J D) a n = true := by
  have Hsp : (sp0.toNat : Int) < ((2 ^ 64 : Nat) : Int) := (u64_range sp0).2
  refine store_ok_of_all segs (cmem sp0 mem0 J D) n a (by omega) ?_
  intro x hx1 hx2
  have hxw : in_win sp0 x := ⟨by omega, by omega⟩
  have hJ : J x ≠ none := HJ x hxw
  unfold wview
  rw [cmem_at_win sp0 mem0 J D x hxw]
  cases h : J x with
  | none => exact absurd h hJ
  | some b => simp

/-- A store below the window is bounded by [wseg_ok] alone (the segment
    fallback carries it; the overlay is irrelevant). -/
theorem store_ok_cmem_data (segs : List Segment) (J D : word → Option byte)
    (a : word) (n : Nat) (H : wseg_ok segs a n = true) :
    store_ok segs (cmem sp0 mem0 J D) a n = true :=
  store_ok_wseg segs (cmem sp0 mem0 J D) n a H

end CMem

/-- The initial overlay in three-region form. -/
theorem cmem_init (ph : PhdrInfo) (sp0 : word) (av ev : List (List byte))
    (uid hw : word) (rdraw : EntryDraw) :
    wrap_mem ph sp0 av ev uid hw rdraw
      = cmem sp0 (wrap_mem ph sp0 av ev uid hw rdraw)
          (fun _ => some (BitVec.ofInt 8 0)) (fun _ => none) := by
  funext x
  by_cases h : (sp0.toNat : Int) ≤ (x.toNat : Int)
  · unfold cmem
    rw [ite_eq_left h]
  · unfold cmem
    rw [ite_eq_right h]
    have Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = none := by
      unfold stack_to_mem
      rw [ite_eq_right (by omega)]
    unfold wrap_mem
    rw [Hst]
    have hB : decide ((x.toNat : Int) < (sp0.toNat : Int)) = true := by
      simp only [decide_eq_true_eq]
      omega
    rw [hB, Bool.and_true]
    have hP : decide ((sp0.toNat : Int) - stack_max_size ≤ (x.toNat : Int))
        = decide (win_lo sp0 ≤ (x.toNat : Int)) := by
      unfold win_lo
      rfl
    rw [hP]
    simp only [decide_eq_true_eq]

/-!  [sp0] is taken near the top of the user address space, so
    that all three regions are non-empty. -/

/-- [win_lo sp0] is [stack_max_size] below [sp0]. -/
example : win_lo (BitVec.ofInt 64 (2 ^ 48)) = 2 ^ 48 - 8388608 := by decide

/-- At/above [sp0]: the initial block ([mem0]). -/
example :
    cmem (BitVec.ofInt 64 (2 ^ 48)) (fun _ => some (BitVec.ofInt 8 1))
        (fun _ => some (BitVec.ofInt 8 2)) (fun _ => some (BitVec.ofInt 8 3))
        (BitVec.ofInt 64 (2 ^ 48)) = some (BitVec.ofInt 8 1) := by decide

/-- In the window: the junk overlay ([J]). -/
example :
    cmem (BitVec.ofInt 64 (2 ^ 48)) (fun _ => some (BitVec.ofInt 8 1))
        (fun _ => some (BitVec.ofInt 8 2)) (fun _ => some (BitVec.ofInt 8 3))
        (BitVec.ofInt 64 (2 ^ 48 - 1)) = some (BitVec.ofInt 8 2) := by decide

/-- Below the window: the data overlay ([D]). -/
example :
    cmem (BitVec.ofInt 64 (2 ^ 48)) (fun _ => some (BitVec.ofInt 8 1))
        (fun _ => some (BitVec.ofInt 8 2)) (fun _ => some (BitVec.ofInt 8 3))
        (BitVec.ofInt 64 (2 ^ 48 - 9000000)) = some (BitVec.ofInt 8 3) := by decide
