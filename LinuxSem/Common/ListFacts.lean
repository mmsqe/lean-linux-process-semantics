/-
  * Common.ListFacts — designated home for generic list facts.

  TRUST BOUNDARY: shared proof library, not the trusted specification.
  Image-INDEPENDENT and domain-free: pure [take]/[drop]/[getD]/[∈] facts
  with no byte/word/RISC-V content.

  This file is the single canonical home for the generic list lemmas
  ([firstn_S_nth] for the snoc-peel fact; [In_firstn] for take-membership;
  plus [skipn_cons_nth] and [firstn_all_len]).  Each fact is stated ONCE
  here, in the development's stdlib vocabulary ([firstn]/[skipn]/[nth]/
  [In]) — which is what every use site speaks — and proved by DEFERRING to
  the list library's own facts (`List.take_append_getElem`,
  `List.drop_eq_getElem_cons`, `List.take_length`,
  `List.mem_take_iff_getElem`) rather than by fresh induction wherever the
  library already has the fact.  Each of those is the same statement in the
  core vocabulary, so the bridge is definitional.

  To keep this module at the bottom of the Common dependency DAG it
  imports nothing at all.

  ENCODING NOTE.  The terms are `List.take` for `firstn`, `List.drop` for
  `skipn`, `l.getD i d` for `nth i l d`, and `x ∈ l` for `In x l`; the
  declaration names keep the [firstn]/[skipn]/[nth]/[In] spelling because
  that is the vocabulary every use site speaks.
-/

namespace LinuxSem.Common.ListFacts

/-! ## `firstn_S_nth` — peel the last element off a `List.take (i + 1)` -/

/-- Peel the last element off a [firstn (S i)]: canonical form of the
    per-example [firstn_S_nth] / [firstn_snoc] / [firstn_snoc_nth].
    Polymorphic with an explicit default [d]; the byte-specialised sites
    (default [Z_to_bv 8 0]) are instances.  Argument order [(A l i d)]
    matches the existing [firstn_S_nth] call sites. -/
theorem firstn_S_nth {A : Type} (l : List A) (i : Nat) (d : A)
    (Hi : i < l.length) : List.take (i + 1) l = List.take i l ++ [l.getD i d] := by
  rw [← List.take_append_getElem Hi, List.getElem_eq_getD]

/-! ## `In_firstn` — membership in a prefix implies membership in the list -/

/-- Membership in a prefix implies membership in the whole list: canonical
    form of the per-example [In_firstn] / [In_firstn_incl]. -/
theorem In_firstn {A : Type} (x : A) (n : Nat) (l : List A) :
    x ∈ List.take n l → x ∈ l := by
  intro H
  obtain ⟨i, Hi, rfl⟩ := List.mem_take_iff_getElem.mp H
  exact List.getElem_mem (Nat.lt_of_lt_of_le Hi (Nat.min_le_right n l.length))

/-! ## `skipn_cons_nth` — expose the head of a `List.drop i` -/

/-- Expose the head of a [skipn i]: canonical form of the per-example
    [skipn_cons_nth].  Polymorphic with an explicit default [d]; argument
    order [(l i d)] matches Common's neighbouring [CatExec.skipn_nth].
    The byte-specialised sites (default [Z_to_bv 8 0]) supply that default
    explicitly. -/
theorem skipn_cons_nth {A : Type} (l : List A) (i : Nat) (d : A)
    (Hi : i < l.length) : List.drop i l = l.getD i d :: List.drop (i + 1) l := by
  rw [List.drop_eq_getElem_cons Hi, List.getElem_eq_getD]

/-! ## `firstn_all_len` — `firstn` of the full length is the list -/

/-- [firstn] of a list's full length is the list: canonical form of the
    per-example [firstn_all_len].  It is exactly `List.take_length`; kept
    under its own name for the existing call sites. -/
theorem firstn_all_len {A : Type} (l : List A) : List.take l.length l = l :=
  List.take_length

end LinuxSem.Common.ListFacts
