/-
  * Common.AgentLib — small binary-agnostic lemmas used by the per-binary proof.

    Contents:

      - shape algebra: [t_emit_app], congruences, [rz_eq];
      - [readable_bytes] / [read_bytes_map] bridges from [rdn] / [store_ok];
      - fd-table normal forms;
      - arithmetic of a few instruction idioms (zero-extension masks,
        the [slliw/sraiw/not/srliw] sign probe).

    NOTES.

    - The shape algebra is `Common/ShapeAlg.lean`, so
      `TSet`/`t_eq`/`t_emit`/`t_alt2`/`realizes` are that module's, opened
      below — the same objects the rest of the `Common` tree uses.  `CatSim`'s
      `is_prefix_app_mono` is opened too; the other prefix helpers are
      `ShapeAlg`'s.
    - Values are `Int`, counts `Nat`, sequences `List`.  `Z_to_bv 64 z` is
      `BitVec.ofInt 64 z`, and `bv_unsigned w` is `(w.toNat : Int)` — the
      `Int`-valued spelling `PropExec`/`StepTac` use for it (`u_Z2bv`).
    - `0 ≤ z < 2 ^ 64` is carried as the conjunction `0 ≤ z ∧ z < 2 ^ 64`,
      which destructures as `Hz.1`, `Hz.2`.
    - The comparison tests are stated at `decide` (`decide (a < b)`,
      `decide (a = b)`), the same `Bool` a comparison primitive would return,
      and proved through `decide_eq_decide`.
    - The three proof helpers are `macro`s: [show_goal_marker] is
      `trace_state`, and [rdn_at]/[rdn_at_hyp] drive [rdn_addr_eq] with the
      same two closers (`f_equal; lia` and a closed `bv_eq` by computation).
    - `zall` takes its count as a `Nat`, and `zallN_spec` is stated at the same
      `Nat` count: the unary literal that motivated a separate bounded form
      does not arise with Lean's binary literals.
-/

import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Common.PropExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.StoreOk
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StreamExec
import LinuxSem.Common.ShapeAlg

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LinuxSem.Common.AgentLib

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.Common.PropExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StoreOk
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.CatSim

/-! =========================================================================
    Shape algebra
    ========================================================================= -/

/-- Emitting `a` then `b` is emitting `a ++ b`. -/
theorem t_emit_app (a b : List event) (T : TSet) :
    t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)) := by
  intro tr
  unfold t_emit
  constructor
  · rintro (Hp | ⟨tr', he, HT⟩)
    · rcases is_prefix_app_split a b tr Hp with Hp' | ⟨b', rfl, Hp'⟩
      · exact Or.inl Hp'
      · exact Or.inr ⟨b', rfl, Or.inl Hp'⟩
    · subst he
      exact Or.inr ⟨b ++ tr', by rw [List.append_assoc], Or.inr ⟨tr', rfl, HT⟩⟩
  · rintro (Hp | ⟨tr', he, Hrest⟩)
    · exact Or.inl (is_prefix_app_r a b tr Hp)
    · subst he
      rcases Hrest with Hp | ⟨tr'', he2, HT⟩
      · exact Or.inl (is_prefix_app_mono a tr' b Hp)
      · subst he2
        exact Or.inr ⟨tr'', by rw [List.append_assoc], HT⟩

/-- [t_emit] respects [t_eq] in its continuation. -/
theorem t_emit_congr (e : List event) (T T' : TSet) (H : t_eq T T') :
    t_eq (t_emit e T) (t_emit e T') := by
  intro tr
  unfold t_emit
  exact or_congr Iff.rfl (exists_congr fun tr' => and_congr Iff.rfl (H tr'))

/-- [t_alt2] respects [t_eq] in both arguments. -/
theorem t_alt2_congr (A A' B B' : TSet)
    (HA : t_eq A A') (HB : t_eq B B') :
    t_eq (t_alt2 A B) (t_alt2 A' B') := by
  intro tr
  unfold t_alt2
  exact or_congr (HA tr) (HB tr)

/-- A shape prefixed by no events is that shape.  (The `ShapeAlg` lemma,
    restated with the nonemptiness premise in the convenient position.) -/
theorem t_emit_nil_l (T : TSet) (H0 : T []) : t_eq (t_emit [] T) T :=
  t_emit_nil_eq T H0

/-- [realizes] up to shape equality, premises in the convenient order. -/
theorem rz_eq (segs : List Segment) (c : config) (T T' : TSet)
    (Heq : t_eq T' T) (H : realizes segs c T') : realizes segs c T :=
  realizes.rz_conseq c T' T H Heq

/-- Three consecutive emissions are one. -/
theorem t_emit_app3 (a b c : List event) (T : TSet) :
    t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T) := by
  rw [List.append_assoc]
  exact t_eq_sym (t_eq_trans (t_emit_app a (b ++ c) T)
    (t_emit_congr a _ _ (t_emit_app b c T)))

/-- [map] distributes, for the [W ch] spelling of write blocks. -/
theorem map_app3 {A B : Type} (f : A → B) (a b c : List A) :
    (a ++ b ++ c).map f = a.map f ++ b.map f ++ c.map f := by
  rw [List.map_append, List.map_append]

/-! =========================================================================
    readable_bytes / read_bytes_map bridges
    ========================================================================= -/

/-- [len_word] of a list read back by [rdn]. -/
theorem len_word_of_nat (bs : List byte) :
    len_word bs = BitVec.ofInt 64 (bs.length : Int) :=
  (BitVec.ofInt_natCast 64 bs.length).symm

/-! `BitVec.toNat_ofInt`/`BitVec.toInt_ofInt` present the width
    as the *Nat* cast `↑(2^n)`, while every bound in this file
    is the `Int` power `2^n`; the two are the same numeral, but `omega` treats
    them as different atoms, so the three casts below put a width into the
    `Int` spelling the hypotheses use. -/

theorem two_pow64_cast : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by omega

theorem two_pow63_cast : ((2 ^ 63 : Nat) : Int) = 2 ^ 63 := by omega

/-- The `toNat` of a `Z_to_bv 64` literal, as a `Nat` (the form the
    `read_bytes_map` length needs). -/
theorem toNat_ofInt_lit (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt, two_pow64_cast,
    Int.emod_eq_of_lt (a := z) (b := 2 ^ 64) Hz.1 Hz.2]

/-- [word_to_nat] of a small non-negative literal is that literal. -/
theorem word_to_nat_ofInt_lit (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    word_to_nat (BitVec.ofInt 64 (n : Int)) = n := by
  unfold word_to_nat
  rw [toNat_ofInt_lit (n : Int) ⟨by omega, Hn⟩]
  omega

/-- The writable view of a byte range established by [store_ok]: every
    [read_bytes_map] over [wview] inside it succeeds. -/
theorem read_bytes_map_of_store_ok (segs : List Segment) (mem : word → Option byte)
    (a : word) (n : Nat) (H : store_ok segs mem a n = true)
    (Hn : (n : Int) < 2 ^ 64) :
    ∃ w, read_bytes_map (wview segs mem) a (BitVec.ofInt 64 (n : Int)) = some w := by
  rw [read_bytes_map_eq, word_to_nat_ofInt_lit n Hn]
  exact store_ok_read_aux segs mem n a H

/-! =========================================================================
    fd tables
    ========================================================================= -/

theorem fd_insert_head_same (fds : List (word × FdEntry)) (fd : word)
    (e e' : FdEntry) :
    fd_insert ((fd, e) :: fds) fd e' = fd_insert fds fd e' := by
  simp [fd_insert, List.filter]

theorem filter_fd_id : ∀ (fds : List (word × FdEntry)) (fd : word),
    fd_lookup fds fd = none →
    List.filter (fun p => !(p.1 == fd)) fds = fds := by
  intro fds
  induction fds with
  | nil => intro fd _; rfl
  | cons ke r ih =>
    intro fd H
    obtain ⟨k, e⟩ := ke
    simp only [fd_lookup] at H
    split at H
    · rename_i heq
      simp at H
    · rename_i hne
      have hk : (k == fd) = false := by simpa using hne
      simp only [List.filter, hk, Bool.not_false]
      rw [ih fd H]

theorem fd_insert_fresh_eq (fds : List (word × FdEntry)) (fd : word) (e : FdEntry)
    (H : fd_lookup fds fd = none) : fd_insert fds fd e = (fd, e) :: fds := by
  unfold fd_insert
  rw [filter_fd_id fds fd H]

/-! =========================================================================
    Small word arithmetic
    ========================================================================= -/

theorem u64_lit (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  u_Z2bv z Hz.1 Hz.2

/-- [v_add] of two in-range literals. -/
theorem v_add_lit (a b : Int) (Ha : 0 ≤ a) (Hb : 0 ≤ b) (Hab : a + b < 2 ^ 64) :
    v_add (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (a + b) := by
  unfold v_add
  rw [u64_lit a ⟨Ha, by omega⟩, u64_lit b ⟨Hb, by omega⟩]

theorem v_sub_lit (a b : Int) (Hb : 0 ≤ b ∧ b ≤ a) (Ha : a < 2 ^ 64) :
    v_sub (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (a - b) := by
  unfold v_sub
  rw [u64_lit a ⟨by omega, Ha⟩, u64_lit b ⟨Hb.1, by omega⟩]

theorem v_addi_lit (a i : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) :
    v_addi (BitVec.ofInt 64 a) i = BitVec.ofInt 64 (a + i) := by
  unfold v_addi
  rw [u64_lit a Ha]

/-- Equality of [Z_to_bv 64] literals modulo 2^64. -/
theorem Z_to_bv_64_mod (z : Int) :
    BitVec.ofInt 64 z = BitVec.ofInt 64 (z % ((2 ^ 64 : Nat) : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  exact congrArg Int.toNat (Int.emod_emod z _).symm

/-- Two `Bool`s equal their `decide`.  (`==` on `Int` is `decide`, while
    `bv_eqb` is the `BEq` of `BitVec`, which is lawful but does not reduce to
    `decide` definitionally.) -/
theorem beq_eq_decide {α : Type} [DecidableEq α] [LawfulBEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : (a == b) = false := by
      cases hb : a == b with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb) h
    rw [h', decide_eq_false h]

/-- Unsigned comparison of literals. -/
theorem c_ltu_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    c_ltu (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) := by
  unfold c_ltu bv_ltu
  rw [toNat_ofInt_lit a Ha, toNat_ofInt_lit b Hb]
  exact decide_eq_decide.mpr (by omega)

theorem c_eq_lit (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    c_eq (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a = b) := by
  unfold c_eq bv_eqb
  rw [beq_eq_decide]
  refine decide_eq_decide.mpr ?_
  rw [← BitVec.toNat_inj, toNat_ofInt_lit a Ha, toNat_ofInt_lit b Hb]
  omega

/-- Signed comparison against zero for a small non-negative literal and for
    an errno return. -/
theorem bv_signed_small (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 63) :
    (BitVec.ofInt 64 z).toInt = z := by
  rw [BitVec.toInt_ofInt, Int.bmod_def, two_pow64_cast]
  have hmod : z % 2 ^ 64 = z :=
    Int.emod_eq_of_lt (a := z) (b := 2 ^ 64) Hz.1 (by omega)
  rw [hmod]
  split <;> omega

theorem bv_signed_neg (e : Int) (He : 0 < e ∧ e ≤ 2 ^ 63) :
    (BitVec.ofInt 64 (-e)).toInt = -e := by
  rw [BitVec.toInt_ofInt, Int.bmod_def, two_pow64_cast]
  have hmod : (-e) % 2 ^ 64 = 2 ^ 64 - e := by
    rw [show -e = (2 ^ 64 - e) + 2 ^ 64 * (-1) from by omega,
      Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (a := 2 ^ 64 - e) (b := 2 ^ 64) (by omega) (by omega)]
  rw [hmod]
  split <;> omega

theorem c_lts_zero_nonneg (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 63) :
    c_lts (BitVec.ofInt 64 z) (BitVec.ofInt 64 0) = false := by
  unfold c_lts bv_lts
  rw [bv_signed_small z Hz, show (BitVec.ofInt 64 0).toInt = 0 from by decide]
  exact decide_eq_false (by omega)

theorem c_lts_zero_errno (e : Int) (He : 0 < e ∧ e ≤ 2 ^ 63) :
    c_lts (BitVec.ofInt 64 (-e)) (BitVec.ofInt 64 0) = true := by
  unfold c_lts bv_lts
  rw [bv_signed_neg e He, show (BitVec.ofInt 64 0).toInt = 0 from by decide]
  exact decide_eq_true (by omega)

/-- [errno_ret e] is the literal [Z_to_bv 64 (-e)]. -/
theorem errno_ret_lit (e : Int) : errno_ret e = BitVec.ofInt 64 (-e) := rfl

/-- Debug helper: print the current goal with a marker. -/
macro "show_goal_marker" : tactic => `(tactic| trace_state)

/-- Respell the address of an [rdn] goal: [rdn_at b] turns
    [rdn segs m a n = r] into [rdn segs m b n = r] when [a = b] by
    [f_equal; lia] (both are [Z_to_bv 64 <Z expression>]). -/
theorem rdn_addr_eq (segs : List Segment) (m : word → Option byte) (a b : word)
    (n : Nat) (r : Option (List byte)) (Hab : a = b) (H : rdn segs m b n = r) :
    rdn segs m a n = r := by
  rw [Hab]
  exact H

macro "rdn_at " b:term : tactic =>
  `(tactic|
    (refine rdn_addr_eq ?_ ?_ ?_ $b ?_ ?_ ?_ ?_ <;>
      first
      | bv_omega
      | (apply BitVec.eq_of_toNat_eq <;> decide)
      | assumption
      | skip))

/-- [rdn_at_hyp Hb]: close an [rdn segs m a n = Some _] goal with hypothesis
    [Hb : rdn segs m b n = Some _] whose address is spelled differently.
    The hypothesis is used as the second premise of [rdn_addr_eq], which
    leaves the address equality [a = b] as the only goal — so no inspection
    of the hypothesis type is needed here. -/
macro "rdn_at_hyp " h:ident : tactic =>
  `(tactic|
    (refine rdn_addr_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first
      | bv_omega
      | (apply BitVec.eq_of_toNat_eq <;> decide)
      | exact $h
      | skip))

/-! =========================================================================
    Brute-force range checking (reflection over a bounded Z interval)
    ========================================================================= -/

/-- Check [f] on the `n` consecutive values starting at [z]. -/
def zall : Nat → (Int → Bool) → Int → Bool
  | 0, _, _ => true
  | n + 1, f, z => if f z then zall n f (z + 1) else false

theorem zall_spec : ∀ (n : Nat) (f : Int → Bool) (z : Int),
    zall n f z = true → ∀ x, z ≤ x ∧ x < z + (n : Int) → f x = true := by
  intro n
  induction n with
  | zero => intro f z _ x hx; omega
  | succ n ih =>
    intro f z H x hx
    simp only [zall] at H
    split at H
    · rename_i hf
      by_cases hxz : x = z
      · subst hxz; exact hf
      · exact ih f (z + 1) H x ⟨by omega, by omega⟩
    · simp at H

/-- [zall] from 0 with a count: the form the instruction-idiom lemmas use.
    (The count is a `Nat`; see the header.) -/
theorem zallN_spec (n : Nat) (f : Int → Bool) (H : zall n f 0 = true) :
    ∀ x, 0 ≤ x ∧ x < (n : Int) → f x = true :=
  fun x hx => zall_spec n f 0 H x ⟨hx.1, by simpa using hx.2⟩

/-! ### Sanity checks for [zall] (evaluated) -/

example : zall 3 (fun z => decide (0 ≤ z)) 0 = true := by decide

example : zall 3 (fun z => decide (z < 3)) 0 = true := by decide

example : zall 3 (fun z => decide (z < 2)) 0 = false := by decide

example : zall 0 (fun z => decide (z = 5)) 5 = true := by decide

example : zall 2 (fun z => decide (z = 5)) 4 = false := by decide

end LinuxSem.Common.AgentLib
