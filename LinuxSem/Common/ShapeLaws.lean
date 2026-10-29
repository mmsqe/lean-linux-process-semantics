/-
  * Common.ShapeLaws — the [t_eq] algebra a proof needs to match executor-built
    shapes against a specification shape: the six laws no other Common file states.

    Pure shape algebra over [ShapeAlg] ([TSet], [t_eq], [t_emit], [t_alt2],
    [t_exit], [t_nil]); image-independent, imports [ShapeAlg] only.

    Companions elsewhere: [SrcShape.t_alt2_comm]/[t_alt2_nil_l]/[t_alt2_nil_r],
    [AgentLib.t_emit_app]/[t_alt2_congr], [RefNodes.t_alt2_idem]/[t_alt3_idem]
    ([t_alt3 A B C := t_alt2 A (t_alt2 B C)]), [ShapeAlg.t_emit_nil_eq]/
    [t_emit_has_nil]/[t_alt_wall] (short-write chunking is invisible — see
    [LibWritev.t_alt_wall_nat]), [AgentNodes.bv_and_255_small].

  NOTES.

  - values are `Int`, lists are `List`, and the section-free statements are
    carried as explicit binders: every law takes its shapes ([A] [B] [C]) /
    its block ([e]) as arguments, exactly as `Common/ShapeAlg.lean` does.
  - `bv_and a b` is `a &&& b`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, and
    `bv_unsigned w` is `(w.toNat : Int)` (Run.lean's convention).   - `map (WriteEv ch) []` in [exit_leaf_eq] is `List.map (event.WriteEv ch)
    []`, which is definitionally `[]`; the `cbn [map]`  performs
    before `t_emit_nil_eq` therefore has no Lean counterpart to write.
-/

import LinuxSem.Common.ShapeAlg

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.ShapeAlg

namespace LinuxSem.Common.ShapeLaws

/- =========================================================================
   Binary choice: associative, absorbing
   ========================================================================= -/

/-- [t_alt2] is associative: the grouping of a choice does not matter. -/
theorem t_alt2_assoc (A B C : TSet) :
    t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)) := by
  intro tr
  unfold t_alt2
  exact or_assoc

/-- Absorption: a repeated alternative anywhere in a right comb. -/
theorem t_alt2_absorb (A B : TSet) :
    t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B) := by
  intro tr
  unfold t_alt2
  constructor
  · rintro (hA | hA' | hB)
    · exact Or.inl hA
    · exact Or.inl hA'
    · exact Or.inr hB
  · intro h
    exact Or.inr h

/-- A three-way node is a right comb of binary ones (definitional for
    [RefNodes.t_alt3]; restated on the unfolded form so no RefNodes import is
    needed). -/
theorem t_alt3_as_alt2 (A B C : TSet) :
    t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C) :=
  t_eq_sym (t_alt2_assoc A B C)

/- =========================================================================
   Fault leaves ([t_nil]) after a COMMON prefix are absorbed
   ========================================================================= -/

/-- [t_emit e t_nil] is absorbed by a sibling that starts with the same block. -/
theorem t_alt2_emit_nil_l (e : List event) (T : TSet) (H0 : T []) :
    t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T) := by
  intro tr
  unfold t_alt2 t_emit t_nil
  constructor
  · rintro ((Hp | ⟨tr', he, hnil⟩) | H)
    · exact Or.inl Hp
    · subst hnil
      exact Or.inr ⟨[], he, H0⟩
    · exact H
  · intro H
    exact Or.inr H

/- =========================================================================
   Emission blocks
   ========================================================================= -/

/-- Distributing a common prefix over a choice (needed when a node's
    alternatives are compared ABOVE an already-merged prefix). -/
theorem t_emit_alt2_distr (e : List event) (A B : TSet) :
    t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)) := by
  intro tr
  unfold t_emit t_alt2
  constructor
  · rintro (Hp | ⟨tr', he, HA | HB⟩)
    · exact Or.inl (Or.inl Hp)
    · exact Or.inl (Or.inr ⟨tr', he, HA⟩)
    · exact Or.inr (Or.inr ⟨tr', he, HB⟩)
  · rintro ((Hp | ⟨tr', he, HA⟩) | (Hp | ⟨tr', he, HB⟩))
    · exact Or.inl Hp
    · exact Or.inr ⟨tr', he, Or.inl HA⟩
    · exact Or.inl Hp
    · exact Or.inr ⟨tr', he, Or.inr HB⟩

/- =========================================================================
   Leaves
   ========================================================================= -/

/-- The exit node's [bv_and .. 255] code on a small literal. -/
theorem bv_and_255_lit (c : Int) (Hc : 0 ≤ c ∧ c < 256) :
    (BitVec.ofInt 64 c) &&& (BitVec.ofInt 64 255) = BitVec.ofInt 64 c := by
  refine BitVec.eq_of_toNat_eq ?_
  have h255 : (BitVec.ofInt 64 255 : word).toNat = 255 := by decide
  have hlt : (BitVec.ofInt 64 c).toNat < 256 := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt Hc.1 (by omega)]
    exact (Int.toNat_lt Hc.1).mpr Hc.2
  rw [BitVec.toNat_and, h255, show (255 : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

/-- The reference's exit leaf with nothing pending on the channel and its
    [bv_and] code is the specification's exit leaf. -/
theorem exit_leaf_eq (ch : word) (c : Int) (fs : Fs.Fs) (Hc : 0 ≤ c ∧ c < 256) :
    t_eq (t_emit (([] : List byte).map (event.WriteEv ch))
          (t_exit ((BitVec.ofInt 64 c) &&& (BitVec.ofInt 64 255)) fs))
      (t_exit (BitVec.ofInt 64 c) fs) := by
  rw [bv_and_255_lit c Hc]
  exact t_emit_nil_eq _ (t_emit_has_nil _ _)

/- =========================================================================
   Sanity checks .
   ========================================================================= -/

example : (BitVec.ofInt 64 200) &&& (BitVec.ofInt 64 255) = BitVec.ofInt 64 200 := by
  decide

example : (BitVec.ofInt 64 256) &&& (BitVec.ofInt 64 255) ≠ BitVec.ofInt 64 256 := by
  decide

end LinuxSem.Common.ShapeLaws
