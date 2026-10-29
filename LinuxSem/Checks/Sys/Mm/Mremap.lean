/-
  * LinuxProcessSem.Checks.Sys.Mm.Mremap — the mremap (216) checkers, and their proofs

  Answers to Linux [mm/mremap.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous constructor
  pattern `⟨r, [], zs, us, cs, []⟩` over `SyscallEffect` (`State.lean`).
  `MemCopy.mkCopy` is the copy record's constructor, which lives in the
  structure's namespace.

  [`new_nZ < old_nZ`] — the shrink test — is written as the `Prop` it is in
  `mremap_spec`, so the checker and the spec share one term and one
  `ite_eq_left`/`ite_eq_right` lemma applies to both.  The move arm's test is inside a
  `&&` chain, where a `Bool` is required, so it is
  `decide (old_nZ < new_nZ)`.

  Each proof peels the spec's model reader with `bind_getModel`, which
  rewrites `bind getModel k i m o` to `k m i m o` in one go (see
  `Checks/Sys/Mm/Mprotect.lean` for the same idiom).  A `Bool` gate is
  `by_cases` plus `rw [ite_eq_left h]` / `rw [ite_eq_right h]`, `dsimp only` performs
  the beta/iota/zeta reduction, and a `CheckX = CheckY` equation is
  eliminated by `nomatch`.  The completeness proofs invert the spec's three
  answered arms with the three `private` inversion lemmas below, then replay
  the checker's own tests on the resulting concrete effect.

  `mremap_source_ret_not_errno` and `mremap_fresh_ret_not_errno` both need
  the same arithmetic: an address that passes the gate's `alloc_top`
  conjunct is more than 4096 below `2^64`, hence can never be read as an
  encoded errno.  The proof cites `State.alloc_top_room`
  (`alloc_top h + stack_max_size < two_pow_64`) and
  `State.stack_max_size_val`.  Three further `private` facts are stated
  here, each named where it is used: the three inversion lemmas for the
  spec's answered arms, the rounding non-negativity that
  `State.page_round_up_Z_nonneg` would give, and `unmodeled_ne_ok` (the
  constructor disjointness the inverted arms end in).
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap

namespace LinuxSem.Checks.Sys.Mm.Mremap

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Sys.Prelude

/-- The `mremap` (216) checker.

    The same argument gates as `mremap_spec`, in the same order, each of
    which the spec answers with one `err_ret` / `ret_only` (or, for the
    flag test and the zero rounded source length, with `unmodeled`), then
    the source gate (whose decline is `CheckUnmodeled`), then the
    equal-size no-op, and finally the four answered resizing shapes:

    - an injected errno: the spec's `alt` offers one, the checker accepts
      it when the value is in `mremap_errnos` and the effect is the lone
      ledger-free `errno_ret`, with no zero ledger / unmap ledger /
      copy ledger;
    - a shrink at `old`: the effect must be `r = old`, no zero ledger,
      the unmapped tail `[(old + new_n, old_nZ - new_nZ)]` and no copies,
      and the post-state is `mremap_model_next`;
    - a grow in place at `old`: the budget/placement gate
      `mremap_inplace_grow_b` must hold, the zero ledger must be exactly
      `mremap_tail old old_n old_nZ new_nZ`, nothing unmapped, no copies;
    - a grow by moving to a fresh `r`: `old_nZ < new_nZ`,
      `mremap_fresh_b`, the tail at `r`, the unmapped whole source
      `[(old, old_n)]` and the one copy `mkCopy old r old_n`.

    Every other effect shape, and every ledger that is not exactly the
    arm's, is `CheckReject`: the spec's `alt` admits no other event. -/
def check_mremap (old old_size new_size flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !((flags.toNat : Int) == MREMAP_MAYMOVE) then .CheckUnmodeled
  else if !(((old.toNat : Int) % page_size) == 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else if page_align_is0_b new_size then
    check_ret_only eff (errno_ret EINVAL) m []
  else if page_align_is0_b old_size then .CheckUnmodeled
  else
    let old_nZ := page_round_up_Z (old_size.toNat : Int)
    let new_nZ := page_round_up_Z (new_size.toNat : Int)
    let old_n := BitVec.ofInt 64 old_nZ
    let new_n := BitVec.ofInt 64 new_nZ
    if !(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
         mremap_backing_uniform_b m old old_n) then .CheckUnmodeled
    else if old_nZ == new_nZ then check_ret_only eff old m []
    else
      match eff with
      | ⟨r, [], zs, us, cs, []⟩ =>
          if errno_ret_in mremap_errnos r then
            match zs, us, cs with
            | [], [], [] => .CheckOk m []
            | _, _, _ => .CheckReject
          else if bv_eqb r old then
            if new_nZ < old_nZ then
              if listNN_eqb zs [] &&
                 listNN_eqb us [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                 listCopy_eqb cs [] then
                .CheckOk (mremap_model_next m old old_n old new_n) []
              else .CheckReject
            else if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ then
              if listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) &&
                 listNN_eqb us [] && listCopy_eqb cs [] then
                .CheckOk (mremap_model_next m old old_n old new_n) []
              else .CheckReject
            else .CheckReject
          else if decide (old_nZ < new_nZ) &&
                  mremap_fresh_b m old_nZ new_nZ old old_n r new_n &&
                  listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ) &&
                  listNN_eqb us [(old, old_n)] &&
                  listCopy_eqb cs [MemCopy.mkCopy old r old_n] then
            .CheckOk (mremap_model_next m old old_n r new_n) []
          else .CheckReject
      | _ => .CheckReject

/-! ## The gate's own arithmetic

    An address the source gate (or the fresh-destination gate) accepts
    ends at or below `alloc_top`, which is a whole stack width below
    `2^64`; so it lies strictly below the error-encoding window and can
    never be read as an injected errno.  [errno_ret_in_below] is the
    consumer in `Prelude`. -/

/-- The source gate's `alloc_top` conjunct puts `old` out of reach of
    every encoded errno. -/
theorem mremap_source_ret_not_errno (h : VmMaps) (old old_n : word) (old_nZ : Int)
    (Hn : 0 ≤ old_nZ) (Hsrc : mremap_source_b h old old_n old_nZ = true) :
    errno_ret_in mremap_errnos old = false := by
  unfold mremap_source_b at Hsrc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at Hsrc
  -- the conjunction is left-nested: `bound && reserved-free && has && noaccess-free`
  have Hbound : (old.toNat : Int) + old_nZ ≤ alloc_top h := Hsrc.1.1.1
  apply errno_ret_in_below mremap_errnos old (by decide)
  have hroom := alloc_top_room h
  have hs : stack_max_size = 8388608 := stack_max_size_val
  omega

/-- The fresh-destination gate's `alloc_top` conjunct puts `dst` out of
    reach of every encoded errno. -/
theorem mremap_fresh_ret_not_errno (m : Model) (old_nZ new_nZ : Int)
    (old old_n dst new_n : word)
    (Hn : 0 ≤ new_nZ)
    (Hfresh : mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) :
    errno_ret_in mremap_errnos dst = false := by
  unfold mremap_fresh_b at Hfresh
  dsimp only at Hfresh
  simp only [Bool.and_eq_true, decide_eq_true_eq] at Hfresh
  -- the conjunction is left-nested: `!dst==old && align && pos && bound && free && budget`
  have Hbound : (dst.toNat : Int) + new_nZ ≤ alloc_top (m_vmmaps m) := Hfresh.1.1.2
  apply errno_ret_in_below mremap_errnos dst (by decide)
  have hroom := alloc_top_room (m_vmmaps m)
  have hs : stack_max_size = 8388608 := stack_max_size_val
  omega

/-- A fresh destination is never the source's own address — the conjunct
    the SPEC's [choose] needs to keep the move arm from producing
    move-shaped effects at [old] (see `Sys/Mm/Mremap.lean`'s note on
    [mremap_fresh_b]: the checker dispatches on `r = old` first and never
    evaluates it). -/
theorem mremap_fresh_neq_old (m : Model) (old_nZ new_nZ : Int)
    (old old_n dst new_n : word)
    (H : mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) :
    bv_eqb dst old = false := by
  unfold mremap_fresh_b at H
  dsimp only at H
  simp only [Bool.and_eq_true] at H
  have h1 : (!(dst == old)) = true := H.1.1.1.1.1
  have hb : (dst == old) = false := by
    cases hbe : (dst == old) with
    | true => rw [hbe] at h1; exact nomatch h1
    | false => rfl
  simpa [bv_eqb] using hb

/-! ## The spec's answered arms, inverted

    The three shapes the spec offers past its gates.  `inv_ok` would
    destructure each of them inline; each is stated once here, as the
    `private` lemmas below, and the completeness proofs then rewrite the
    checker's goal to the concrete effect the arm produced.  They add no
    public surface. -/

/-- The injected errno, inverted: an errno from the injectable set with no
    ledger at all. -/
private theorem errno_from_ok_inv (es : List Int) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.bind (errno_from es)
      (fun e => err_ret e) i m (.ok eff m' evs)) :
    ∃ e, e ∈ es ∧ eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  obtain ⟨e, m1, evs1, evs2, hc, hk, hevs⟩ := H
  unfold errno_from choose at hc
  obtain ⟨e0, hmem, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨rfl, rfl, rfl⟩ := hok
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
    Outcome.ok.injEq] at hk
  obtain ⟨heff, hm, hevs2⟩ := hk
  subst hevs2
  refine ⟨e, hmem, heff, hm, ?_⟩
  simpa using hevs

/-- The in-place resolution (a shrink or an in-place grow), inverted: the
    spec's effect verbatim, the model stepped to `mremap_model_next`, and
    no events. -/
private theorem inplace_ok_inv (old old_n new_n : word) (old_nZ new_nZ : Int)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event) (i : SyscallInput)
    (H : LinuxSem.LinuxProcessSem.bind
      (modify (fun _ => mremap_model_next m old old_n old new_n))
      (fun _ => pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
      i m (.ok eff m' evs)) :
    eff = mremap_inplace_effect old old_n new_n old_nZ new_nZ ∧
      m' = mremap_model_next m old old_n old new_n ∧ evs = [] := by
  obtain ⟨u, m1, evs1, evs2, hc, hk, hevs⟩ := H
  -- `modify` and `pure`, at the constructors they produce
  have hc' : (Outcome.ok u m1 evs1 : Outcome Unit Model event) =
      Outcome.ok () (mremap_model_next m old old_n old new_n) [] := hc
  simp only [Outcome.ok.injEq] at hc'
  obtain ⟨-, rfl, rfl⟩ := hc'
  have hk' : (Outcome.ok eff m' evs2 : Outcome SyscallEffect Model event) =
      Outcome.ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ)
        (mremap_model_next m old old_n old new_n) [] := hk
  simp only [Outcome.ok.injEq] at hk'
  obtain ⟨heff, hm, hevs2⟩ := hk'
  rw [hevs2] at hevs
  refine ⟨heff, hm, ?_⟩
  simpa using hevs

/-- The move resolution, inverted: the fresh destination the spec chose,
    its gate, the move effect verbatim, the stepped model, and no events. -/
private theorem move_ok_inv (m : Model) (old old_n new_n : word)
    (old_nZ new_nZ : Int) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (i : SyscallInput)
    (H : LinuxSem.LinuxProcessSem.bind
      (choose (fun dst => mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true))
      (fun dst => LinuxSem.LinuxProcessSem.bind
        (modify (fun _ => mremap_model_next m old old_n dst new_n))
        (fun _ => pure (mremap_move_effect old old_n dst old_nZ new_nZ)))
      i m (.ok eff m' evs)) :
    ∃ dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true ∧
      eff = mremap_move_effect old old_n dst old_nZ new_nZ ∧
      m' = mremap_model_next m old old_n dst new_n ∧ evs = [] := by
  obtain ⟨dst, m1, evs1, evs2, hc, hk, hevs⟩ := H
  -- the `choose`: any witness of the fresh-destination predicate
  have hc0 : ∃ x, mremap_fresh_b m old_nZ new_nZ old old_n x new_n = true ∧
      (Outcome.ok dst m1 evs1 : Outcome word Model event) = Outcome.ok x m [] := hc
  obtain ⟨x, hfresh, hok⟩ := hc0
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hx, hm1, hevs1⟩ := hok
  -- the witness is the destination itself, at the model the step started in
  rw [← hx] at hfresh
  rw [hm1] at hk
  rw [hevs1] at hevs
  obtain ⟨u, m2, evs2', evs3, hc2, hk2, hevs2⟩ := hk
  -- `modify` and `pure`, at the constructors they produce
  have hc2' : (Outcome.ok u m2 evs2' : Outcome Unit Model event) =
      Outcome.ok () (mremap_model_next m old old_n dst new_n) [] := hc2
  simp only [Outcome.ok.injEq] at hc2'
  obtain ⟨-, rfl, rfl⟩ := hc2'
  have hk2' : (Outcome.ok eff m' evs3 : Outcome SyscallEffect Model event) =
      Outcome.ok (mremap_move_effect old old_n dst old_nZ new_nZ)
        (mremap_model_next m old old_n dst new_n) [] := hk2
  simp only [Outcome.ok.injEq] at hk2'
  obtain ⟨heff, hm, hevs3⟩ := hk2'
  rw [hevs3] at hevs2
  rw [hevs2] at hevs
  refine ⟨dst, hfresh, heff, hm, ?_⟩
  simpa using hevs

/-- `unmodeled` is not an `ok` outcome — the shape every inverted spec arm
    rules out when the spec is asked for an `unmodeled` answer.  (Stated as
    a simp rule because the arms above are `bind chains of `choose` /
    `modify` / `pure`, whose `unmodeled` case is exactly this equality.) -/
private theorem unmodeled_ne_ok {A M E : Type} (x : A) (m : M) (evs : List E) :
    (Outcome.unmodeled : Outcome A M E) ≠ .ok x m evs := by
  intro h
  exact nomatch h

/-! ## The four agreement theorems -/

section

-- The checker's last arm is a `match` on the effect nested under six
-- tests, and the proofs below drive the same test tree on both sides, so
-- the default recursion budget is not enough to unify the instantiated
-- arms.  (The same option guards the analogous proofs in
-- `Checks/Sys/Mm/Mprotect.lean`.)
set_option maxRecDepth 1000000

theorem check_mremap_sound_ok (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_mremap old old_size new_size flags eff m = .CheckOk m' evs) :
    mremap_spec old old_size new_size flags i m (.ok eff m' evs) := by
  unfold check_mremap at H
  unfold mremap_spec
  dsimp only at H ⊢
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hshape] at H
    exact nomatch H
  · rw [ite_eq_right hshape] at H ⊢
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      exact pure_ok _ i _
    · rw [ite_eq_right halign] at H ⊢
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        exact pure_ok _ i _
      · rw [ite_eq_right hnew] at H ⊢
        by_cases hold : page_align_is0_b old_size = true
        · rw [ite_eq_left hold] at H
          exact nomatch H
        · rw [ite_eq_right hold] at H ⊢
          rw [bind_getModel]
          try dsimp only
          -- name the two roundings once; both sides now carry them verbatim
          generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H ⊢
          generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H ⊢
          generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H ⊢
          generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H ⊢
          by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
              mremap_backing_uniform_b m old old_n)) = true
          · -- the model does not track this source: the checker declines
            rw [ite_eq_left hsrc] at H
            exact nomatch H
          · rw [ite_eq_right hsrc] at H ⊢
            by_cases heq : (old_nZ == new_nZ) = true
            · -- the equal-size no-op
              rw [ite_eq_left heq] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff old m [] m' evs).mp H
              exact pure_ok _ i _
            · rw [ite_eq_right heq] at H ⊢
              -- the four answered resizing shapes
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases copyins <;> dsimp only at H
              · -- an empty write ledger and an empty copy-in ledger
                by_cases herr : errno_ret_in mremap_errnos r = true
                · -- the injected errno, state untouched, no ledgers
                  rw [ite_eq_left herr] at H
                  cases zs <;> cases us <;> cases cs <;> dsimp only at H
                  · simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    have hm' : m' = m := hm.symm
                    have hevs' : evs = [] := hevs.symm
                    rw [hm', hevs']
                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mremap_errnos r).mp herr
                    rw [hr]
                    refine Or.inl ?_
                    exact bind_ok0 (errno_from mremap_errnos) (fun e => err_ret e) i m e m
                      (mkEffect (errno_ret e) [] []) m []
                      (choose_ok _ e i m hmem) (pure_ok _ i m)
                  all_goals (exact nomatch H)
                · rw [ite_eq_right herr] at H
                  by_cases hret : bv_eqb r old = true
                  · -- the answer is the source address: a shrink or an in-place grow
                    rw [ite_eq_left hret] at H
                    have hr : r = old := (Fs.bv_eqb_eq r old).mp hret
                    rw [hr]
                    by_cases hlt : new_nZ < old_nZ
                    · -- the shrink: the tail is unmapped
                      rw [ite_eq_left hlt] at H ⊢
                      by_cases hshrink : (listNN_eqb zs [] &&
                          listNN_eqb us
                            [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                          listCopy_eqb cs []) = true
                      · rw [ite_eq_left hshrink] at H
                        simp only [Bool.and_eq_true] at hshrink
                        have hzs : zs = [] := (listNN_eqb_eq zs []).mp hshrink.1.1
                        have hus : us = [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] :=
                          (listNN_eqb_eq us _).mp hshrink.1.2
                        have hcs : cs = [] := (listCopy_eqb_eq cs []).mp hshrink.2
                        rw [hzs, hus, hcs]
                        simp only [check_result.CheckOk.injEq] at H
                        obtain ⟨hm, hevs⟩ := H
                        have hm' : m' = mremap_model_next m old old_n old new_n := hm.symm
                        have hevs' : evs = [] := hevs.symm
                        rw [hm', hevs']
                        refine Or.inr ?_
                        -- the spec's shrink effect, at the shape the checker read
                        have hEff : mremap_inplace_effect old old_n new_n old_nZ new_nZ =
                            SyscallEffect.mkEffectU old [] []
                            [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] [] [] := by
                          unfold mremap_inplace_effect
                          rw [ite_eq_left hlt]
                        rw [hEff]
                        exact bind_ok0
                          (modify (fun _ => mremap_model_next m old old_n old new_n))
                          (fun _ => pure (SyscallEffect.mkEffectU old [] []
                            [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] [] []))
                          i m () (mremap_model_next m old old_n old new_n)
                          (SyscallEffect.mkEffectU old [] []
                            [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] [] [])
                          (mremap_model_next m old old_n old new_n) []
                          (modify_ok _ i m) (pure_ok _ i _)
                      · rw [ite_eq_right hshrink] at H
                        exact nomatch H
                    · -- not a shrink: an in-place grow, or a move
                      rw [ite_eq_right hlt] at H ⊢
                      by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                      · rw [ite_eq_left hgrow] at H ⊢
                        by_cases hcond : (listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) &&
                            listNN_eqb us [] && listCopy_eqb cs []) = true
                        · rw [ite_eq_left hcond] at H
                          simp only [Bool.and_eq_true] at hcond
                          have hzs : zs = mremap_tail old old_n old_nZ new_nZ :=
                            (listNN_eqb_eq zs _).mp hcond.1.1
                          have hus : us = [] := (listNN_eqb_eq us []).mp hcond.1.2
                          have hcs : cs = [] := (listCopy_eqb_eq cs []).mp hcond.2
                          rw [hzs, hus, hcs]
                          simp only [check_result.CheckOk.injEq] at H
                          obtain ⟨hm, hevs⟩ := H
                          have hm' : m' = mremap_model_next m old old_n old new_n := hm.symm
                          have hevs' : evs = [] := hevs.symm
                          rw [hm', hevs']
                          refine Or.inr ?_
                          refine Or.inl ?_
                          -- the spec's in-place grow effect, at the shape the checker read
                          have hEff : mremap_inplace_effect old old_n new_n old_nZ new_nZ =
                              mkEffect old [] (mremap_tail old old_n old_nZ new_nZ) := by
                            unfold mremap_inplace_effect
                            rw [ite_eq_right hlt]
                          rw [hEff]
                          exact bind_ok0
                            (modify (fun _ => mremap_model_next m old old_n old new_n))
                            (fun _ => pure (mkEffect old [] (mremap_tail old old_n old_nZ new_nZ)))
                            i m () (mremap_model_next m old old_n old new_n)
                            (mkEffect old [] (mremap_tail old old_n old_nZ new_nZ))
                            (mremap_model_next m old old_n old new_n) []
                            (modify_ok _ i m) (pure_ok _ i _)
                        · rw [ite_eq_right hcond] at H
                          exact nomatch H
                      · rw [ite_eq_right hgrow] at H
                        exact nomatch H
                  · -- a fresh destination: the move
                    rw [ite_eq_right hret] at H
                    by_cases hcond : (decide (old_nZ < new_nZ) &&
                        mremap_fresh_b m old_nZ new_nZ old old_n r new_n &&
                        listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ) &&
                        listNN_eqb us [(old, old_n)] &&
                        listCopy_eqb cs [MemCopy.mkCopy old r old_n]) = true
                    · rw [ite_eq_left hcond] at H
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
                      have hlt' : old_nZ < new_nZ := hcond.1.1.1.1
                      have hfresh : mremap_fresh_b m old_nZ new_nZ old old_n r new_n = true :=
                        hcond.1.1.1.2
                      have hzs : zs = mremap_tail r old_n old_nZ new_nZ :=
                        (listNN_eqb_eq zs _).mp hcond.1.1.2
                      have hus : us = [(old, old_n)] := (listNN_eqb_eq us _).mp hcond.1.2
                      have hcs : cs = [MemCopy.mkCopy old r old_n] :=
                        (listCopy_eqb_eq cs _).mp hcond.2
                      rw [hzs, hus, hcs]
                      simp only [check_result.CheckOk.injEq] at H
                      obtain ⟨hm, hevs⟩ := H
                      have hm' : m' = mremap_model_next m old old_n r new_n := hm.symm
                      have hevs' : evs = [] := hevs.symm
                      rw [hm', hevs']
                      -- the move body, built once for both of the spec's routes to it
                      have hmove :
                          bind (choose (fun dst =>
                              mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true))
                            (fun dst =>
                              bind (modify (fun _ => mremap_model_next m old old_n dst new_n))
                                (fun _ => pure (mremap_move_effect old old_n dst old_nZ new_nZ)))
                            i m (.ok (SyscallEffect.mkEffectU r [] (mremap_tail r old_n old_nZ new_nZ)
                              [(old, old_n)] [MemCopy.mkCopy old r old_n] [])
                              (mremap_model_next m old old_n r new_n) ([] : List event)) := by
                        refine bind_ok0 (choose (fun dst =>
                            mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true))
                          (fun dst =>
                            bind (modify (fun _ => mremap_model_next m old old_n dst new_n))
                              (fun _ => pure (mremap_move_effect old old_n dst old_nZ new_nZ)))
                          i m r m _ _ []
                          (choose_ok _ r i m hfresh) ?_
                        refine bind_ok0
                          (modify (fun _ => mremap_model_next m old old_n r new_n))
                          (fun _ => pure (mremap_move_effect old old_n r old_nZ new_nZ))
                          i m () (mremap_model_next m old old_n r new_n)
                          (SyscallEffect.mkEffectU r [] (mremap_tail r old_n old_nZ new_nZ)
                            [(old, old_n)] [MemCopy.mkCopy old r old_n] [])
                          (mremap_model_next m old old_n r new_n) []
                          (modify_ok _ i m) ?_
                        exact pure_ok _ i _
                      by_cases hlt : new_nZ < old_nZ
                      · omega
                      · rw [ite_eq_right hlt]
                        by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                        · rw [ite_eq_left hgrow]
                          exact Or.inr (Or.inr hmove)
                        · rw [ite_eq_right hgrow]
                          exact Or.inr hmove
                    · rw [ite_eq_right hcond] at H
                      exact nomatch H
              all_goals (exact nomatch H)

theorem check_mremap_sound_unmodeled (old old_size new_size flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_mremap old old_size new_size flags eff m = .CheckUnmodeled) :
    mremap_spec old old_size new_size flags i m .unmodeled := by
  unfold check_mremap at H
  unfold mremap_spec
  dsimp only at H ⊢
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · -- the flag gate declines exactly where the spec does
    rw [ite_eq_left hshape] at H ⊢
    exact unmodeled_intro i m
  · rw [ite_eq_right hshape] at H ⊢
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · -- the spec answers -EINVAL here; the checker cannot decline
      rw [ite_eq_left halign] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right halign] at H ⊢
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      · rw [ite_eq_right hnew] at H ⊢
        by_cases hold : page_align_is0_b old_size = true
        · -- a zero rounded source length: both sides decline
          rw [ite_eq_left hold] at H ⊢
          exact unmodeled_intro i m
        · rw [ite_eq_right hold] at H ⊢
          rw [bind_getModel]
          try dsimp only
          generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H ⊢
          generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H ⊢
          generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H ⊢
          generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H ⊢
          by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
              mremap_backing_uniform_b m old old_n)) = true
          · -- the source gate declines
            rw [ite_eq_left hsrc] at H ⊢
            exact unmodeled_intro i m
          · rw [ite_eq_right hsrc] at H ⊢
            by_cases heq : (old_nZ == new_nZ) = true
            · rw [ite_eq_left heq] at H
              exact absurd H (check_ret_only_no_unmodeled eff old m [])
            · -- past the gates the checker never answers `CheckUnmodeled`:
              -- every arm accepts or rejects, so the hypothesis is impossible
              rw [ite_eq_right heq] at H
              exfalso
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases copyins <;> dsimp only at H
              · by_cases herr : errno_ret_in mremap_errnos r = true
                · rw [ite_eq_left herr] at H
                  cases zs <;> cases us <;> cases cs <;> dsimp only at H
                  all_goals (exact nomatch H)
                · rw [ite_eq_right herr] at H
                  by_cases hret : bv_eqb r old = true
                  · rw [ite_eq_left hret] at H
                    by_cases hlt : new_nZ < old_nZ
                    · rw [ite_eq_left hlt] at H
                      by_cases hshrink : (listNN_eqb zs [] &&
                          listNN_eqb us
                            [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                          listCopy_eqb cs []) = true
                      · rw [ite_eq_left hshrink] at H
                        exact nomatch H
                      · rw [ite_eq_right hshrink] at H
                        exact nomatch H
                    · rw [ite_eq_right hlt] at H
                      by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                      · rw [ite_eq_left hgrow] at H
                        by_cases hcond : (listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) &&
                            listNN_eqb us [] && listCopy_eqb cs []) = true
                        · rw [ite_eq_left hcond] at H
                          exact nomatch H
                        · rw [ite_eq_right hcond] at H
                          exact nomatch H
                      · rw [ite_eq_right hgrow] at H
                        exact nomatch H
                  · rw [ite_eq_right hret] at H
                    by_cases hcond : (decide (old_nZ < new_nZ) &&
                        mremap_fresh_b m old_nZ new_nZ old old_n r new_n &&
                        listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ) &&
                        listNN_eqb us [(old, old_n)] &&
                        listCopy_eqb cs [MemCopy.mkCopy old r old_n]) = true
                    · rw [ite_eq_left hcond] at H
                      exact nomatch H
                    · rw [ite_eq_right hcond] at H
                      exact nomatch H
              all_goals (exact nomatch H)

/-- The rounding of a non-negative length is non-negative.  (The fact is
    used only here, at the two `page_align_is0_b` call sites, which is why
    it is stated privately rather than beside the other rounding lemmas.) -/
private theorem page_round_up_Z_nonneg' (n : Int) (h : 0 ≤ n) :
    0 ≤ page_round_up_Z n := by
  unfold page_round_up_Z page_size
  have h1 : 0 ≤ (n + 4096 - 1) / 4096 := Int.ediv_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (n + 4096 - 1) / 4096 * 4096 := Int.mul_nonneg h1 (by omega)
  exact h2

theorem check_mremap_complete_ok (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : mremap_spec old old_size new_size flags i m (.ok eff m' evs)) :
    check_mremap old old_size new_size flags eff m = .CheckOk m' evs := by
  unfold check_mremap
  unfold mremap_spec at H
  dsimp only at H ⊢
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · -- the spec declines the flag word: there is no `ok` outcome
    rw [ite_eq_left hshape] at H
    exact absurd H (by simp [LinuxSem.LinuxProcessSem.unmodeled])
  · rw [ite_eq_right hshape] at H ⊢
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · -- -EINVAL, state untouched
      rw [ite_eq_left halign] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right halign] at H ⊢
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ := H
        simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hnew] at H ⊢
        by_cases hold : page_align_is0_b old_size = true
        · rw [ite_eq_left hold] at H
          exact absurd H (by simp [LinuxSem.LinuxProcessSem.unmodeled])
        · rw [ite_eq_right hold] at H ⊢
          rw [bind_getModel] at H
          try dsimp only at H
          generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H ⊢
          generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H ⊢
          generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H ⊢
          generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H ⊢
          by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
              mremap_backing_uniform_b m old old_n)) = true
          · rw [ite_eq_left hsrc] at H
            exact absurd H (by simp [LinuxSem.LinuxProcessSem.unmodeled])
          · rw [ite_eq_right hsrc] at H ⊢
            -- the spec's own source gate, positively
            have hsrc' : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                mremap_backing_uniform_b m old old_n) = true := by
              cases h : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                  mremap_backing_uniform_b m old old_n) <;> simp [h] at hsrc ⊢
            have hsource : mremap_source_b (m_vmmaps m) old old_n old_nZ = true :=
              (Bool.and_eq_true ..).mp hsrc' |>.1
            -- a source address below `alloc_top` is never an encoded errno
            have hold_nonneg : 0 ≤ old_nZ := by
              rw [← hOldN]
              exact page_round_up_Z_nonneg' _ (word_unsigned_range old_size).1
            have hold_errno : errno_ret_in mremap_errnos old = false :=
              mremap_source_ret_not_errno (m_vmmaps m) old old_n old_nZ hold_nonneg hsource
            have hold_notin : ¬ (errno_ret_in mremap_errnos old = true) := by
              rw [hold_errno]; simp
            by_cases heq : (old_nZ == new_nZ) = true
            · -- the equal-size no-op
              rw [ite_eq_left heq] at H ⊢
              obtain ⟨rfl, rfl, rfl⟩ := H
              simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right heq] at H ⊢
              simp only [alt] at H
              rcases H with herr | hrest
              · -- the injected errno: no ledger, state untouched
                obtain ⟨e, hmem, heff, hm, hevs⟩ :=
                  errno_from_ok_inv mremap_errnos i m eff m' evs herr
                rw [heff, hm, hevs]
                dsimp only
                rw [ite_eq_left (errno_ret_in_intro mremap_errnos e hmem)]
              · by_cases hlt : new_nZ < old_nZ
                · -- a shrink: the in-place resolution's first branch
                  rw [ite_eq_left hlt] at hrest
                  obtain ⟨heff, hm, hevs⟩ :=
                    inplace_ok_inv old old_n new_n old_nZ new_nZ m eff m' evs i hrest
                  have heff' : eff = SyscallEffect.mkEffectU old [] []
                      [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] [] [] := by
                    rw [heff]
                    unfold mremap_inplace_effect
                    rw [ite_eq_left hlt]
                  rw [heff', hm, hevs]
                  dsimp only
                  have hshrink : (listNN_eqb [] [] &&
                      listNN_eqb [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))]
                        [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                      listCopy_eqb [] []) = true := by
                    rw [(listNN_eqb_eq _ _).mpr rfl]
                    simp [listNN_eqb, listCopy_eqb, bv_eqb_refl]
                  rw [ite_eq_right hold_notin, ite_eq_left (bv_eqb_refl old), ite_eq_left hlt, ite_eq_left hshrink]
                · rw [ite_eq_right hlt] at hrest
                  -- past the shrink the spec offers the in-place grow (when its
                  -- gate accepts) beside the move; either resolution is enough
                  have hcases :
                      (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true ∧
                        LinuxSem.LinuxProcessSem.bind
                          (modify (fun _ => mremap_model_next m old old_n old new_n))
                          (fun _ => pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
                          i m (.ok eff m' evs)) ∨
                      LinuxSem.LinuxProcessSem.bind
                        (choose (fun dst =>
                          mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true))
                        (fun dst => LinuxSem.LinuxProcessSem.bind
                          (modify (fun _ => mremap_model_next m old old_n dst new_n))
                          (fun _ => pure (mremap_move_effect old old_n dst old_nZ new_nZ)))
                        i m (.ok eff m' evs) := by
                    by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                    · rw [ite_eq_left hgrow] at hrest
                      simp only [alt] at hrest
                      rcases hrest with hinp | hmv
                      · exact Or.inl ⟨hgrow, hinp⟩
                      · exact Or.inr hmv
                    · rw [ite_eq_right hgrow] at hrest
                      exact Or.inr hrest
                  rcases hcases with ⟨hgrow, hinplace⟩ | hmove
                  · -- the in-place grow: the in-place resolution's second branch
                    obtain ⟨heff, hm, hevs⟩ :=
                      inplace_ok_inv old old_n new_n old_nZ new_nZ m eff m' evs i hinplace
                    have heff' : eff = mkEffect old [] (mremap_tail old old_n old_nZ new_nZ) := by
                      rw [heff]
                      unfold mremap_inplace_effect
                      rw [ite_eq_right hlt]
                    rw [heff', hm, hevs]
                    dsimp only
                    have hcond : (listNN_eqb (mremap_tail old old_n old_nZ new_nZ)
                          (mremap_tail old old_n old_nZ new_nZ) &&
                        listNN_eqb [] [] && listCopy_eqb [] []) = true := by
                      rw [(listNN_eqb_eq _ _).mpr rfl]
                      simp [listNN_eqb, listCopy_eqb]
                    rw [ite_eq_right hold_notin, ite_eq_left (bv_eqb_refl old), ite_eq_right hlt,
                      ite_eq_left hgrow, ite_eq_left hcond]
                  · -- the move, at the fresh destination the spec chose
                    obtain ⟨dst, hfresh, heff, hm, hevs⟩ :=
                      move_ok_inv m old old_n new_n old_nZ new_nZ eff m' evs i hmove
                    have hnew_nonneg : 0 ≤ new_nZ := by
                      rw [← hNewN]
                      exact page_round_up_Z_nonneg' _ (word_unsigned_range new_size).1
                    have hdst_errno : errno_ret_in mremap_errnos dst = false :=
                      mremap_fresh_ret_not_errno m old_nZ new_nZ old old_n dst new_n
                        hnew_nonneg hfresh
                    have hdst_notin : ¬ (errno_ret_in mremap_errnos dst = true) := by
                      rw [hdst_errno]; simp
                    have hdst_ne : bv_eqb dst old = false :=
                      mremap_fresh_neq_old m old_nZ new_nZ old old_n dst new_n hfresh
                    have hdst_ne' : ¬ (bv_eqb dst old = true) := by
                      rw [hdst_ne]; simp
                    -- the checker's own move test
                    have hne : old_nZ ≠ new_nZ := by simpa [beq_iff_eq] using heq
                    have hltmove : old_nZ < new_nZ := by omega
                    rw [heff, hm, hevs]
                    unfold mremap_move_effect
                    dsimp only
                    have hchain : (decide (old_nZ < new_nZ) &&
                        mremap_fresh_b m old_nZ new_nZ old old_n dst new_n &&
                        listNN_eqb (mremap_tail dst old_n old_nZ new_nZ)
                          (mremap_tail dst old_n old_nZ new_nZ) &&
                        listNN_eqb [(old, old_n)] [(old, old_n)] &&
                        listCopy_eqb [MemCopy.mkCopy old dst old_n]
                          [MemCopy.mkCopy old dst old_n]) = true := by
                      rw [(listNN_eqb_eq _ _).mpr rfl, (listNN_eqb_eq _ _).mpr rfl,
                        (listCopy_eqb_eq _ _).mpr rfl, hfresh]
                      simp [hltmove]
                    rw [ite_eq_right hdst_notin, ite_eq_right hdst_ne', ite_eq_left hchain]

/-- Completeness, declining side: wherever the spec leaves the modeled
    surface, the checker declines too.  The three failing gates are the
    spec's own; past them the spec is a chain of `choose`/`alt`/`modify`/
    `pure`, none of which can answer `unmodeled`, so the last branch is
    vacuous. -/
theorem check_mremap_complete_unmodeled (old old_size new_size flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : mremap_spec old old_size new_size flags i m .unmodeled) :
    check_mremap old old_size new_size flags eff m = .CheckUnmodeled := by
  unfold check_mremap
  unfold mremap_spec at H
  dsimp only at H ⊢
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · -- both sides decline the flag word
    rw [ite_eq_left hshape] at H ⊢
  · rw [ite_eq_right hshape] at H ⊢
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · -- the spec answers -EINVAL; it cannot be `unmodeled`
      rw [ite_eq_left halign] at H
      exact absurd H (by simp [err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure])
    · rw [ite_eq_right halign] at H ⊢
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        exact absurd H (by simp [err_ret, ret_only,
          LinuxSem.LinuxProcessSem.pure])
      · rw [ite_eq_right hnew] at H ⊢
        by_cases hold : page_align_is0_b old_size = true
        · -- a zero rounded source length: both sides decline
          rw [ite_eq_left hold] at H ⊢
        · rw [ite_eq_right hold] at H ⊢
          rw [bind_getModel] at H
          try dsimp only at H
          generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H
          generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H
          generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H
          generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H
          by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
              mremap_backing_uniform_b m old old_n)) = true
          · -- the source gate declines
            rw [ite_eq_left hsrc] at H ⊢
          · rw [ite_eq_right hsrc] at H ⊢
            by_cases heq : (old_nZ == new_nZ) = true
            · -- the equal-size no-op answers `ok`, not `unmodeled`
              rw [ite_eq_left heq] at H
              exact absurd H (by simp [ret_only,
                LinuxSem.LinuxProcessSem.pure])
            · rw [ite_eq_right heq] at H ⊢
              -- the alternative's arms are built from `choose` / `modify` /
              -- `pure`, none of which can answer `unmodeled`
              exfalso
              unfold LinuxSem.LinuxProcessSem.modify at H
              by_cases hlt : new_nZ < old_nZ
              · rw [ite_eq_left hlt] at H
                simp [LinuxSem.LinuxProcessSem.alt,
                  LinuxSem.LinuxProcessSem.bind,
                  LinuxSem.LinuxProcessSem.choose,
                  LinuxSem.LinuxProcessSem.pure,
                  errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
              · rw [ite_eq_right hlt] at H
                by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                · rw [ite_eq_left hgrow] at H
                  simp [LinuxSem.LinuxProcessSem.alt,
                    LinuxSem.LinuxProcessSem.bind,
                    LinuxSem.LinuxProcessSem.choose,
                    LinuxSem.LinuxProcessSem.pure,
                    errno_from, err_ret, ret_only, unmodeled_ne_ok] at H
                · rw [ite_eq_right hgrow] at H
                  simp [LinuxSem.LinuxProcessSem.alt,
                    LinuxSem.LinuxProcessSem.bind,
                    LinuxSem.LinuxProcessSem.choose,
                    LinuxSem.LinuxProcessSem.pure,
                    errno_from, err_ret, ret_only, unmodeled_ne_ok] at H

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the checker
    and its four proofs, nothing else.  The checks below are sanity checks:
    they pin that the four argument gates are the spec's, in the spec's
    order, so each of them answers exactly the `err_ret` / `unmodeled` the
    spec does.  They are equalities of `check_result`s, not `decide` goals,
    because `check_result`'s `CheckOk` carries a `Model`, and `Model` has
    no `DecidableEq`. -/

/-- The one flag word the model answers is `MREMAP_MAYMOVE` (1). -/
example : MREMAP_MAYMOVE = 1 := by decide

/-- Any other flag word is the fail-closed decline, before any other
    argument is read. -/
example (old old_size new_size : word) (eff : SyscallEffect) (m : Model) :
    check_mremap old old_size new_size (BitVec.ofInt 64 0) eff m = .CheckUnmodeled := by
  unfold check_mremap
  rw [ite_eq_left (by decide)]

/-- A misaligned source address is the -EINVAL gate. -/
example (old_size new_size : word) (eff : SyscallEffect) (m : Model) :
    check_mremap (BitVec.ofInt 64 0x1001) old_size new_size
        (BitVec.ofInt 64 MREMAP_MAYMOVE) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mremap
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A rounded new length of zero is the second -EINVAL gate. -/
example (old_size : word) (eff : SyscallEffect) (m : Model) :
    check_mremap (BitVec.ofInt 64 0x1000) old_size (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 MREMAP_MAYMOVE) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mremap
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A rounded SOURCE length of zero is the clone shape: fail closed, after
    the two -EINVAL gates and before the source gate. -/
example (eff : SyscallEffect) (m : Model) :
    check_mremap (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 MREMAP_MAYMOVE) eff m =
      .CheckUnmodeled := by
  unfold check_mremap
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

end
