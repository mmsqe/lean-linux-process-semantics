/-
  * LinuxProcessSem.Checks.Sys.Kernel.Time.Time — the gettimeofday (169) checker, and its proofs

  Answers to Linux [kernel/time/time.c]: this file holds the checkers for the syscalls
  defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); `in_wmem i` is the record field `i.in_wmem`; an
  effect literal is the anonymous constructor pattern
  `⟨r, [(a, bs)], [], [], [], []⟩` over `SyscallEffect`; and the spec's own
  predicates are cited through the `Sys.Kernel.Time` namespace the spec file
  keeps (`timeval_ok_b`, `gettimeofday_spec`), while
  `copy_bytes_map`/`access_okb` are `StateMemory`'s.

  The checker's answered arm is one match — a single 16-byte write at `tv`,
  a zero return, and nothing else — and both `sound_*` proofs read it
  backwards.  That read is done once, by `eff_shape_ok` /
  `one_write_ne_unmodeled`.  The spec's steps are peeled with
  `input_bind_ok_inv` / `input_bind_unmodeled_inv` from
  `Checks.Sys.Prelude` and this file's `choose_bind_ok_inv`.  The count `16`
  in `copy_bytes_map i.in_wmem tv 16` stays a literal, matching the spec's
  own spelling.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Time

namespace LinuxSem.Checks.Sys.Kernel.Time.Time

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time
open LinuxSem.Checks.Sys.Prelude

/-- gettimeofday: a NULL [tz] (the model has no [sys_tz]), a non-NULL
    [tv], a fully writable 16 bytes there, and a reading
    [Time.timeval_ok_b] admits — the same boolean the spec
    chooses against.  The effect must be exactly one write of those
    bytes at [tv] and nothing else, with a 0 return.  No model state
    moves: the wall clock is chosen afresh per call, and
    [Time.gettimeofday_spec] says why there is nothing to
    record.  A [tv] whose first 8-byte [put_user] range [access_ok]
    refuses is -EFAULT with nothing written; the range test is asked
    through [State.copy_bytes_map] before the walk is consulted, and
    8 rather than 16 on the faulting arm for the reason
    [Time.gettimeofday_spec] gives. -/
def check_gettimeofday (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !w_is0 tz then .CheckUnmodeled
  else if w_is0 tv then .CheckUnmodeled
  else
    match copy_bytes_map i.in_wmem tv 16 with
    | none =>
        if !access_okb tv 8 then
          check_ret_only eff (errno_ret EFAULT) m []
        else .CheckUnmodeled
    | some _ =>
        match eff with
        | ⟨r, [(a, bs)], [], [], [], []⟩ =>
            if bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tv && timeval_ok_b bs then
              .CheckOk m []
            else .CheckReject
        | _ => .CheckReject

/-! ## Inversion helpers for the effect shape

    The checker's answered arm ends with one match — exactly one write of
    a byte list at an address, a zero return, and nothing else — and both
    `sound_*` proofs have to read it backwards, in each answer shape.
    (The same two, for the same reason, head
    `Checks/Sys/Kernel/Time/PosixTimers.lean`.) -/

/-- The one-write arm never answers `CheckUnmodeled`: its branch body is a
    `CheckOk`/`CheckReject` test, and the fallback is `CheckReject`. -/
private theorem one_write_ne_unmodeled (m : Model) (tv : word) (eff : SyscallEffect) :
    ((match eff with
      | ⟨r, [(a, bs)], [], [], [], []⟩ =>
          if bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tv && timeval_ok_b bs then
            check_result.CheckOk m [] else check_result.CheckReject
      | _ => check_result.CheckReject) : check_result) ≠ check_result.CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro hh
  split at hh
  · split at hh <;> exact nomatch hh
  · exact nomatch hh

/-- An accepted outcome forces the effect's shape: exactly one write, at
    some address, of some byte list — and the branch body accepted it. -/
private theorem eff_shape_ok {f : word → word → List byte → check_result}
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : (match eff with
          | ⟨r, [(a, bs)], [], [], [], []⟩ => f r a bs
          | _ => .CheckReject) = .CheckOk m' evs) :
    ∃ r a bs, eff = ⟨r, [(a, bs)], [], [], [], []⟩ ∧ f r a bs = .CheckOk m' evs := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  split at H
  · rename_i r' a' bs' heq
    exact ⟨r', a', bs', heq, H⟩
  · exact nomatch H

/-- `bind` over the environment's `choose`: an accepted outcome names the
    chosen value and its evidence.  (`choose` has no inversion lemma, and
    the checker needs one in the accepted shape.) -/
private theorem choose_bind_ok_inv {B : Type} (P : List byte → Prop)
    (k : List byte → SysSpec B) (i : SyscallInput) (m : Model) (y : B)
    (m' : Model) (evs : List event)
    (H : bind (choose P) k i m (.ok y m' evs)) :
    ∃ x, P x ∧ k x i m (.ok y m' evs) := by
  unfold LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.choose at H
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := H
  obtain ⟨x0, hP, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hx, hm1, hevs1⟩ := hok
  subst hx; subst hm1; subst hevs1
  simp only [List.nil_append] at hevs
  subst hevs
  exact ⟨_, hP, hk⟩

/-! ## The four agreement theorems -/

section

-- The proofs below drive the same test tree on both sides of the goal and
-- read the checker's one-write match backwards through the effect's
-- shape; the default recursion budget is not enough to unify the
-- instantiated arms.
set_option maxRecDepth 1000000

theorem check_gettimeofday_sound_ok (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_gettimeofday i tv tz eff m = .CheckOk m' evs) :
    gettimeofday_spec tv tz i m (.ok eff m' evs) := by
  unfold check_gettimeofday at H
  unfold gettimeofday_spec
  by_cases htz : (!w_is0 tz) = true
  · rw [ite_eq_left htz] at H
    exact nomatch H
  · rw [ite_eq_right htz] at H ⊢
    by_cases htv : w_is0 tv = true
    · rw [ite_eq_left htv] at H
      exact nomatch H
    · rw [ite_eq_right htv] at H ⊢
      refine bind_ok0 inputSpec _ i m i m _ m' evs rfl ?_
      try dsimp only
      cases hw : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        rw [hw] at H
        dsimp only
        by_cases ho : (!access_okb tv 8) = true
        · -- the first 8-byte store is refused: -EFAULT, nothing written
          rw [ite_eq_left ho] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
          exact pure_ok _ i _
        · rw [ite_eq_right ho] at H
          exact nomatch H
      | some bs0 =>
        dsimp only
        rw [hw] at H
        dsimp only at H
        obtain ⟨r, a, bs, heff, hcond⟩ := eff_shape_ok H
        subst heff
        by_cases hok : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tv
          && timeval_ok_b bs) = true
        · rw [ite_eq_left hok] at hcond
          simp only [check_result.CheckOk.injEq] at hcond
          obtain ⟨hm, hevs⟩ := hcond
          subst hm; subst hevs
          simp only [Bool.and_eq_true] at hok
          obtain ⟨⟨hr, ha⟩, hts⟩ := hok
          rw [Fs.bv_eqb_eq] at hr ha
          subst hr; subst ha
          refine bind_ok0 (choose (fun bs : List byte => timeval_ok_b bs = true)) _
            i m bs m _ m [] ?_ ?_
          · exact choose_ok _ bs i m hts
          · exact pure_ok _ i _
        · rw [ite_eq_right hok] at hcond
          exact nomatch hcond

theorem check_gettimeofday_sound_unmodeled (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_gettimeofday i tv tz eff m = .CheckUnmodeled) :
    gettimeofday_spec tv tz i m .unmodeled := by
  unfold check_gettimeofday at H
  unfold gettimeofday_spec
  by_cases htz : (!w_is0 tz) = true
  · rw [ite_eq_left htz] at H ⊢
    exact unmodeled_intro i m
  · rw [ite_eq_right htz] at H ⊢
    by_cases htv : w_is0 tv = true
    · rw [ite_eq_left htv] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right htv] at H ⊢
      refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
      try dsimp only
      cases hw : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        rw [hw] at H
        dsimp only
        by_cases ho : (!access_okb tv 8) = true
        · rw [ite_eq_left ho] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
        · -- the torn band, or a destination not wholly mapped: decline
          rw [ite_eq_right ho] at H ⊢
          exact unmodeled_intro i m
      | some bs0 =>
        rw [hw] at H
        exact absurd H (one_write_ne_unmodeled m tv eff)

theorem check_gettimeofday_complete_ok (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : gettimeofday_spec tv tz i m (.ok eff m' evs)) :
    check_gettimeofday i tv tz eff m = .CheckOk m' evs := by
  unfold check_gettimeofday
  unfold gettimeofday_spec at H
  by_cases htz : (!w_is0 tz) = true
  · rw [ite_eq_left htz] at H ⊢
    exact nomatch H
  · rw [ite_eq_right htz] at H ⊢
    by_cases htv : w_is0 tv = true
    · rw [ite_eq_left htv] at H ⊢
      exact nomatch H
    · rw [ite_eq_right htv] at H ⊢
      have hbody := input_bind_ok_inv _ i m eff m' evs H
      try dsimp only at hbody
      cases hw : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        rw [hw] at hbody
        dsimp only
        by_cases ho : (!access_okb tv 8) = true
        · rw [ite_eq_left ho] at hbody ⊢
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at hbody
          obtain ⟨heff, hm, hevs⟩ := hbody
          subst heff; subst hm; subst hevs
          try dsimp only
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right ho] at hbody ⊢
          exact nomatch hbody
      | some bs0 =>
        dsimp only
        rw [hw] at hbody
        dsimp only at hbody
        obtain ⟨bs, hP, hk⟩ := choose_bind_ok_inv _ _ _ _ _ _ _ hbody
        simp only [LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at hk
        obtain ⟨heff, hm, hevs⟩ := hk
        subst heff; subst hm; subst hevs
        try dsimp only
        rw [ite_eq_left (by simp [bv_eqb_refl, hP])]

theorem check_gettimeofday_complete_unmodeled (i : SyscallInput) (tv tz : word)
    (m : Model) (eff : SyscallEffect)
    (H : gettimeofday_spec tv tz i m .unmodeled) :
    check_gettimeofday i tv tz eff m = .CheckUnmodeled := by
  unfold check_gettimeofday
  unfold gettimeofday_spec at H
  by_cases htz : (!w_is0 tz) = true
  · -- both sides decline at the `tz` gate, and `rw` closes the goal
    rw [ite_eq_left htz] at H ⊢
  · rw [ite_eq_right htz] at H ⊢
    by_cases htv : w_is0 tv = true
    · -- both sides decline at the `tv` gate
      rw [ite_eq_left htv] at H ⊢
    · rw [ite_eq_right htv] at H ⊢
      have hbody := input_bind_unmodeled_inv _ i m H
      try dsimp only at hbody
      cases hw : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        rw [hw] at hbody
        dsimp only
        by_cases ho : (!access_okb tv 8) = true
        · -- the spec answers -EFAULT here; it cannot be `unmodeled`
          rw [ite_eq_left ho] at hbody ⊢
          exact nomatch hbody
        · -- both sides decline
          rw [ite_eq_right ho] at hbody ⊢
      | some bs0 =>
        dsimp only
        rw [hw] at hbody
        rcases hbody with h | ⟨bs, m1, evs1, h1, h2⟩
        · -- `choose` never declines
          obtain ⟨x, -, hx⟩ := h
          exact nomatch hx
        · -- nor does `pure`
          exact nomatch h2

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the checker
    and its four proofs, nothing else.  The checks below are sanity checks:
    they pin that the checker's gates are the spec's, in the spec's order.
    They are equalities of `check_result`s, not `decide` goals, because
    `check_result`'s `CheckOk` carries a `Model`, and `Model` has no
    `DecidableEq`. -/

/-- A non-NULL `tz` declines unconditionally — the first gate. -/
example (i : SyscallInput) (m : Model) (eff : SyscallEffect) (tv : word) :
    check_gettimeofday i tv (BitVec.ofInt 64 0x1000) eff m = .CheckUnmodeled := by
  unfold check_gettimeofday
  rw [ite_eq_left (by decide)]

/-- A NULL `tv` declines next: the spec does too, rather than commit to
    Linux's "write nothing, answer 0". -/
example (i : SyscallInput) (m : Model) (eff : SyscallEffect) :
    check_gettimeofday i (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) eff m
      = .CheckUnmodeled := by
  unfold check_gettimeofday
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A destination the 16-byte range test refuses AND whose first 8-byte
    store the range test refuses is the -EFAULT arm with an empty ledger —
    the one arm of the `none` case that answers.  (The other, where the
    first store passes and the second does not, declines.) -/
example (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (hw : copy_bytes_map i.in_wmem (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF) 16 = none)
    (ho : access_okb (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF) 8 = false) :
    check_gettimeofday i (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF) (BitVec.ofInt 64 0)
        eff m =
      check_ret_only eff (errno_ret EFAULT) m [] := by
  unfold check_gettimeofday
  rw [ite_eq_right (by decide), ite_eq_right (by decide), hw, ite_eq_left (by
    simp only [ho, Bool.not_false])]

end LinuxSem.Checks.Sys.Kernel.Time.Time
