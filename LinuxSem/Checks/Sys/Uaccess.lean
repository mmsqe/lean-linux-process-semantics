/-
  * LinuxProcessSem.Checks.Sys.Uaccess — the user-buffer boundary checkers, and their proofs

  The spec side of the same boundary is `Sys.Uaccess`.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The boundary checkers answer with `CheckOk` / `CheckReject` /
  `CheckUnmodeled`, a closed boolean is settled by `decide` rather than by a
  compute-then-reflexivity step, and `dsimp only` performs the
  beta/iota/zeta reduction.  `err_ret`, `ret_only` and `pure` are the
  `Sys.Syscall` / `Monad` definitions, and the statements below spell the
  canonical `Sys.Syscall` ones rather than `Sys.Uaccess`'s own copies.

  The three helper tactics are `macro`s of the same name and with the same
  steps, so other modules can call them as the proofs below do.
  `unfold f in *` is `try simp only [f] at *`, because `simp only` is an
  error where there is nothing to rewrite and the split runs over hypotheses
  and goal whether or not both definitions occur there; `dsimp only` is the
  beta/iota/zeta reduction; and `sys_unfold` / `inv_ok` are the tactics of
  `Checks.Sys.Prelude`.  Every call site passes plain identifiers, so the
  macro arguments are `ident`s.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Uaccess

namespace LinuxSem.Checks.Sys.Uaccess

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.Checks.Sys.Prelude

def check_access_ok_zero (buf count : word)
    (eff : SyscallEffect) (m : Model) (k : check_result) : check_result :=
  if access_okb buf (count.toNat : Int) then k
  else check_ret_only eff (errno_ret EFAULT) m []

def check_efault_or (fallback : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if eff_is_errno EFAULT eff then .CheckOk m []
  else check_ret_only eff fallback m []

/-- The two cases of [check_access_ok_zero] and [Uaccess.access_ok_zero]
    at once: they make the same test, so one split serves the hypothesis
    and the goal.  Leaves the arm's own answer first and the -EFAULT the
    range verdict forces second. -/
macro "ok_zero_cases " H:ident b:ident c:ident : tactic =>
  `(tactic| (try simp only [check_access_ok_zero] at $H:ident
             try simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.access_ok_zero]
             cases hok : access_okb $b (($c).toNat : Int)
             all_goals (try dsimp only at $H:ident ⊢)))

/-- The same split for the completeness direction, where the guard is a
    hypothesis about the spec rather than about the checker. -/
macro "ok_zero_split " b:ident c:ident : tactic =>
  `(tactic| (try simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.access_ok_zero,
                            check_access_ok_zero] at *
             cases access_okb $b (($c).toNat : Int)
             all_goals (sys_unfold; try dsimp only at *; try inv_ok)))

macro "ok_zero_complete " b:ident c:ident : tactic =>
  `(tactic| (try simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.access_ok_zero,
                            check_access_ok_zero] at *
             cases access_okb $b (($c).toNat : Int)
             all_goals (sys_unfold; try dsimp only at *; try inv_ok)
             all_goals rfl))

theorem check_efault_or_sound_ok (fallback : word) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_efault_or fallback eff m = .CheckOk m' evs) :
    alt (err_ret EFAULT) (ret_only fallback) i m (.ok eff m' evs) := by
  unfold check_efault_or at H
  by_cases hf : eff_is_errno EFAULT eff = true
  · rw [ite_eq_left hf] at H
    have heff : eff = mkEffect (errno_ret EFAULT) [] [] :=
      eff_is_errno_true EFAULT eff hf
    subst heff
    simp only [check_result.CheckOk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    unfold alt err_ret ret_only LinuxSem.LinuxProcessSem.pure
    left
    rfl
  · rw [ite_eq_right hf] at H
    obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff eff fallback m [] m' evs).mp H
    subst heff
    subst hevs
    subst hm
    unfold alt err_ret ret_only LinuxSem.LinuxProcessSem.pure
    right
    rfl

theorem check_efault_or_no_unmodeled (fallback : word) (eff : SyscallEffect)
    (m : Model) : check_efault_or fallback eff m ≠ .CheckUnmodeled := by
  unfold check_efault_or
  by_cases hf : eff_is_errno EFAULT eff = true
  · rw [ite_eq_left hf]
    simp
  · rw [ite_eq_right hf]
    exact check_ret_only_no_unmodeled eff fallback m []

theorem check_efault_or_complete_ok (fallback : word) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : alt (err_ret EFAULT) (ret_only fallback) i m (.ok eff m' evs)) :
    check_efault_or fallback eff m = .CheckOk m' evs := by
  unfold alt err_ret ret_only LinuxSem.LinuxProcessSem.pure at H
  simp only [Outcome.ok.injEq] at H
  rcases H with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [check_efault_or]
    rw [ite_eq_left (by simp [eff_is_errno, bv_eqb_refl])]
  · simp only [check_efault_or]
    -- a fallback that also reads as [-EFAULT] is accepted by the first arm
    by_cases hf : eff_is_errno EFAULT (mkEffect fallback [] []) = true
    · rw [ite_eq_left hf]
    · rw [ite_eq_right hf]
      simp [check_ret_only, bv_eqb_refl]

theorem efault_or_no_unmodeled (fallback : word) (i : SyscallInput)
    (m : Model) : ¬ alt (err_ret EFAULT) (ret_only fallback) i m .unmodeled := by
  intro H
  unfold alt err_ret ret_only LinuxSem.LinuxProcessSem.pure at H
  rcases H with H | H <;> exact nomatch H

theorem check_efault_or_not_einval (fallback : word) (m m' : Model)
    (evs : List event)
    (Hne : bv_eqb (errno_ret EINVAL) fallback = false) :
    check_efault_or fallback (mkEffect (errno_ret EINVAL) [] []) m
      = .CheckOk m' evs → False := by
  intro H
  unfold check_efault_or at H
  have hfv : eff_is_errno EFAULT (mkEffect (errno_ret EINVAL) [] []) = false := by
    simp only [eff_is_errno]
    decide
  rw [hfv] at H
  simp only [Bool.false_eq_true, ite_false] at H
  dsimp only [check_ret_only] at H
  rw [ite_eq_right (by simpa using Hne)] at H
  exact nomatch H

/-! ## Sanity checks (not library lemmas)

  `check_result` carries no `DecidableEq` instance, so the
  checks below state the two branches of each checker as equations rather
  than as `decide` goals; [ok_zero_cases] gets one smoke test. -/

/-- The range verdict passes the arm's own answer through. -/
example (buf count : word) (eff : SyscallEffect) (m : Model) (k : check_result)
    (h : access_okb buf (count.toNat : Int) = true) :
    check_access_ok_zero buf count eff m k = k := by
  simp [check_access_ok_zero, h]

/-- The range verdict's other answer is exactly the -EFAULT return. -/
example (buf count : word) (eff : SyscallEffect) (m : Model) (k : check_result)
    (h : access_okb buf (count.toNat : Int) = false) :
    check_access_ok_zero buf count eff m k
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  simp [check_access_ok_zero, h]

/-- An -EFAULT effect is accepted as it stands, whatever the fallback. -/
example (fallback : word) (m : Model) :
    check_efault_or fallback (mkEffect (errno_ret EFAULT) [] []) m
      = .CheckOk m [] := by
  simp [check_efault_or, eff_is_errno, bv_eqb_refl]

/-- Smoke test for [ok_zero_cases]: the split builds the two range cases. -/
example (buf count : word) (eff : SyscallEffect) (m : Model) (k : check_result)
    (_H : check_access_ok_zero buf count eff m k = k) (P : Prop) (hP : P) : P := by
  -- `_H` is consumed only by the tactic, which is why it is underscore-named.
  ok_zero_cases _H buf count
  all_goals exact hP

end LinuxSem.Checks.Sys.Uaccess
