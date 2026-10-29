/-
  * LinuxProcessSem.Checks.Sys.Kernel.Exit — the exit (93), exit_group (94), wait4 (260) checkers, and their proofs

  Answers to Linux [kernel/exit.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`; the
  effect type's single constructor is `mkEffectU`, whose no-unmap/no-copy
  shape is the `mkEffect` abbreviation.

  `check_wait4`'s `i` and `stat_addr` are never read — `stat_addr` IS the
  behaviour, not an omission: the spec does not judge the pointer either,
  and the section in [Sys/Kernel/Exit.lean] says why.  The Lean
  unused-variable linter is switched off for the declaration rather than the
  parameters being renamed, so the signature keeps the argument surface the
  spec's prose is about.  The same goes for the witness file.

  Each proof steps the spec's model reader with `bind_getModel`, one
  rewrite; `dsimp only` performs the beta/iota/zeta reduction; an outcome
  equality is inverted with `cases`; and a `CheckUnmodeled = CheckOk`
  equation is eliminated by `nomatch`.

  `wait4_spec` is a `SysSpec`, a FUNCTION, so its body is an `if` at
  function type (`(if … then unmodeled else …) i m o`).  Lean's `whnf` on a
  goal that mentions it tries to reduce that `if`, which means deciding
  `!((upid.toNat : Int) == WAIT_ANY32)` on an opaque word; `by_cases`
  normalises its goal, so each proof here `generalize`s its conclusion into
  a local `Q : Prop` first, splits against `Q` (an opaque variable, so no
  reduction happens), and only then rewrites `Q` back into the spec and
  discharges the branch with `simp only`.  This is the pattern
  `Checks/Sys/Kernel/Groups.lean` documents at length.

  The all-`nil` shape of the effect is reached by a five-way `cases` chain
  in which only that shape survives.  The chain is written out
  (`cases ws <;> cases zs <;> … <;> dsimp only at H`), the all-`nil` case is
  taken with a `case` label, and every other case is closed with
  `all_goals exact nomatch H`.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Exit

namespace LinuxSem.Checks.Sys.Kernel.Exit

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Prelude

/-- [exit] (93) and [exit_group] (94): one answer, 0, and one state
    change, the low byte of the status recorded as the halted code.
    [Kernel.Exit.exit_spec] is exactly that pair, so the checker is
    [check_ret_only] against it: no ledger is nonempty and no other
    return is admitted. -/
def check_exit (code : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (BitVec.ofInt 64 0)
    (with_halted (code &&& BitVec.ofInt 64 255) m) []

theorem check_exit_sound_ok (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_exit code eff m = .CheckOk m' evs) :
    exit_spec code i m (.ok eff m' evs) := by
  obtain ⟨heff, hm, hevs⟩ :=
    (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
      (with_halted (code &&& BitVec.ofInt 64 255) m) [] m' evs).mp H
  subst heff
  subst hm
  subst hevs
  exact ⟨(), with_halted (code &&& BitVec.ofInt 64 255) m, [], [], rfl, rfl, rfl⟩

theorem check_exit_sound_unmodeled (code : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_exit code eff m = .CheckUnmodeled) :
    exit_spec code i m .unmodeled :=
  absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
    (with_halted (code &&& BitVec.ofInt 64 255) m) [])

theorem check_exit_complete_ok (code : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : exit_spec code i m (.ok eff m' evs)) :
    check_exit code eff m = .CheckOk m' evs := by
  obtain ⟨u, m1, evs1, evs2, hm, hk, hevs⟩ := H
  cases hm
  cases hk
  simp only [List.nil_append] at hevs
  subst hevs
  simp only [check_exit, check_ret_only, bv_eqb_refl, ite_eq_left]

theorem check_exit_complete_unmodeled (code : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : exit_spec code i m .unmodeled) :
    check_exit code eff m = .CheckUnmodeled := by
  rcases H with h | ⟨u, m1, evs1, h1, h2⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at h2
    exact nomatch h2

/- ------------------------------------------------- set_tid_address

   (This section is empty: the [set_tid_address] checker lives in
   [Checks/Sys/Kernel/Fork.lean].) -/

/- ----------------------------------------------------------------- wait4 -/

set_option linter.unusedVariables false in
/-- [wait4] (260): three argument guards and one answer.
    [Exit.wait4_spec] is a caller with no children, so -ECHILD is the
    whole of what a modeled call admits and every other kernel answer —
    a reaped pid, WNOHANG's bare 0, an -EFAULT through [stat_addr] — is
    REJECTED rather than accepted. [stat_addr] is not read here for the
    same reason it is not read there: [kernel_wait4]'s copy-out is
    guarded on [ret > 0], so no -ECHILD touches it.

    The guards are in the spec's order — [upid], [options], [rusage],
    the [m_has_children] gate — and the effect match is last, so a call
    that passes the guards and carries any ledger or any other return is
    [CheckReject]. -/
def check_wait4 (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !((upid.toNat : Int) == WAIT_ANY32) then .CheckUnmodeled
  else if !((options.toNat : Int) == WNOHANG) then .CheckUnmodeled
  else if !(w_is0 rusage) then .CheckUnmodeled
  else if m_has_children m then .CheckUnmodeled
  else
    match eff with
    | ⟨ret, [], [], [], [], []⟩ =>
        if bv_eqb ret (errno_ret ECHILD) then .CheckOk m [] else .CheckReject
    | _ => .CheckReject

/-- Every effect field but the return must be empty: a -ECHILD moves no
    memory. Five case splits, one per ledger, each closing its cons case
    on the checker's catch-all (see the `cases` chain in the header). -/

theorem check_wait4_sound_ok (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_wait4 i upid stat_addr options rusage eff m = .CheckOk m' evs) :
    wait4_spec upid stat_addr options rusage i m (.ok eff m' evs) := by
  generalize hP : (wait4_spec upid stat_addr options rusage i m (.ok eff m' evs)) = Q at *
  simp only [check_wait4] at H
  by_cases h1 : (!((upid.toNat : Int) == WAIT_ANY32)) = true
  · rw [ite_eq_left h1] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!((options.toNat : Int) == WNOHANG)) = true
    · rw [ite_eq_left h2] at H
      exact nomatch H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (!(w_is0 rusage)) = true
      · rw [ite_eq_left h3] at H
        exact nomatch H
      · rw [ite_eq_right h3] at H
        by_cases h4 : m_has_children m = true
        · rw [ite_eq_left h4] at H
          exact nomatch H
        · rw [ite_eq_right h4] at H
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
            dsimp only at H
          case nil.nil.nil.nil.nil =>
            by_cases hr : bv_eqb ret (errno_ret ECHILD) = true
            · rw [ite_eq_left hr] at H
              obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj H
              have hret : ret = errno_ret ECHILD :=
                (Fs.bv_eqb_eq ret (errno_ret ECHILD)).mp hr
              subst hret
              rw [← hP]
              simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, getModelSpec,
                bind_getModel, ite_eq_right h4, err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure]
            · rw [ite_eq_right hr] at H
              exact nomatch H
          all_goals exact nomatch H

theorem check_wait4_sound_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_wait4 i upid stat_addr options rusage eff m = .CheckUnmodeled) :
    wait4_spec upid stat_addr options rusage i m .unmodeled := by
  generalize hP : (wait4_spec upid stat_addr options rusage i m .unmodeled) = Q at *
  simp only [check_wait4] at H
  by_cases h1 : (!((upid.toNat : Int) == WAIT_ANY32)) = true
  · rw [ite_eq_left h1] at H
    rw [← hP]
    simp only [wait4_spec, ite_eq_left h1, unmodeled]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!((options.toNat : Int) == WNOHANG)) = true
    · rw [ite_eq_left h2] at H
      rw [← hP]
      simp only [wait4_spec, ite_eq_right h1, ite_eq_left h2, unmodeled]
    · rw [ite_eq_right h2] at H
      by_cases h3 : (!(w_is0 rusage)) = true
      · rw [ite_eq_left h3] at H
        rw [← hP]
        simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, unmodeled]
      · rw [ite_eq_right h3] at H
        by_cases h4 : m_has_children m = true
        · rw [ite_eq_left h4] at H
          rw [← hP]
          simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, getModelSpec,
            bind_getModel, ite_eq_left h4, unmodeled]
        · rw [ite_eq_right h4] at H
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
            dsimp only at H
          case nil.nil.nil.nil.nil =>
            by_cases hr : bv_eqb ret (errno_ret ECHILD) = true
            · rw [ite_eq_left hr] at H
              exact nomatch H
            · rw [ite_eq_right hr] at H
              exact nomatch H
          all_goals exact nomatch H

theorem check_wait4_complete_ok (i : SyscallInput) (upid stat_addr options rusage : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : wait4_spec upid stat_addr options rusage i m (.ok eff m' evs)) :
    check_wait4 i upid stat_addr options rusage eff m = .CheckOk m' evs := by
  generalize hP : (check_wait4 i upid stat_addr options rusage eff m = .CheckOk m' evs) = Q at *
  simp only [wait4_spec] at H
  by_cases h1 : (!((upid.toNat : Int) == WAIT_ANY32)) = true
  · rw [ite_eq_left h1] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!((options.toNat : Int) == WNOHANG)) = true
    · rw [ite_eq_left h2] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (!(w_is0 rusage)) = true
      · rw [ite_eq_left h3] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right h3] at H
        simp only [getModelSpec, bind_getModel] at H
        by_cases h4 : m_has_children m = true
        · -- a caller with a child: the spec's continuation is [unmodeled],
          -- which admits no [Ok] at all
          rw [ite_eq_left h4] at H
          simp only [unmodeled] at H
          exact nomatch H
        · rw [ite_eq_right h4] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          obtain ⟨hEff, hm', hevs⟩ := Outcome.ok.inj H
          subst hEff
          subst hm'
          subst hevs
          rw [← hP]
          simp only [check_wait4, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
            bv_eqb_refl, ite_eq_left]

theorem check_wait4_complete_unmodeled (i : SyscallInput) (upid stat_addr options rusage : word)
    (m : Model) (eff : SyscallEffect)
    (H : wait4_spec upid stat_addr options rusage i m .unmodeled) :
    check_wait4 i upid stat_addr options rusage eff m = .CheckUnmodeled := by
  generalize hP : (check_wait4 i upid stat_addr options rusage eff m = .CheckUnmodeled) = Q at *
  by_cases h1 : (!((upid.toNat : Int) == WAIT_ANY32)) = true
  · rw [← hP]
    simp only [check_wait4, ite_eq_left h1]
  · by_cases h2 : (!((options.toNat : Int) == WNOHANG)) = true
    · rw [← hP]
      simp only [check_wait4, ite_eq_right h1, ite_eq_left h2]
    · by_cases h3 : (!(w_is0 rusage)) = true
      · rw [← hP]
        simp only [check_wait4, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
      · by_cases h4 : m_has_children m = true
        · rw [← hP]
          simp only [check_wait4, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
        · -- no children: the continuation is [err_ret ECHILD], which
          -- answers, so the spec cannot be [Unmodeled] here
          rw [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at H
          simp only [getModelSpec, bind_getModel] at H
          rw [ite_eq_right h4] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the branch
    order the proofs above follow, one per claim the matching spec's prose
    makes: `exit` accepts exactly a 0 return with every ledger empty and
    the low byte recorded as the halted code; any other return and any
    nonempty ledger are rejected; `wait4` answers -ECHILD for a childless
    caller, declines a caller the model gave a child, declines on each of
    its three argument guards, and rejects a return that is not -ECHILD.

    They are sanity checks, not library lemmas.  `check_result` carries no
    `DecidableEq`, so each states the branch as an equation and closes it
    by unfolding the checker and discharging the branch tests with
    `decide`. -/

/-- A model whose process has no child — `mkModel`'s default, which is the
    one state `wait4` answers. -/
private def port_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The same model after the creating arm: `with_children`, which is what
    `Kernel.Fork.clone_resolve` applies on its success branch. -/
private def port_model_child : Model := with_children port_model

/-- The one accepted `exit` effect: return 0, no ledger, and the model
    halted at the LOW BYTE of `code`. -/
example (code : word) (m : Model) :
    check_exit code (mkEffect (BitVec.ofInt 64 0) [] []) m
      = .CheckOk (with_halted (code &&& BitVec.ofInt 64 255) m) [] := by
  simp only [check_exit, check_ret_only, bv_eqb_refl, ite_eq_left]

/-- Any other return is rejected — `exit` has one answer. -/
example (code : word) (m : Model) :
    check_exit code (mkEffect (BitVec.ofInt 64 1) [] []) m = .CheckReject := by
  simp only [check_exit, check_ret_only]
  rw [ite_eq_right (by decide)]

/-- …and so is a ledger that is not empty: `exit` writes no memory. -/
example (code : word) (m : Model) (w : word × List byte)
    (ws : List (word × List byte)) :
    check_exit code ⟨BitVec.ofInt 64 0, w :: ws, [], [], [], []⟩ m
      = .CheckReject := by
  simp only [check_exit, check_ret_only]

/-- `wait4(-1, _, WNOHANG, 0)` on a childless caller: -ECHILD, no ledger,
    model unchanged.  This is the one answered shape. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 4294967295) (BitVec.ofInt 64 (-1))
        (BitVec.ofInt 64 1) 0 (mkEffect (errno_ret ECHILD) [] []) port_model
      = .CheckOk port_model [] := by
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]

/-- A caller the model GAVE a child is declined, not answered — the
    `m_has_children` gate. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 4294967295) 0 (BitVec.ofInt 64 1) 0
        (mkEffect (errno_ret ECHILD) [] []) port_model_child
      = .CheckUnmodeled := by
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- `upid > 0` — one child — declines, and it is refused FIRST: the other
    guards and the effect are never looked at. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 5) (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 2)
        (BitVec.ofInt 64 4096) (mkEffect (errno_ret ECHILD) [] []) port_model
      = .CheckUnmodeled := by
  simp only [check_wait4]
  rw [ite_eq_left (by decide)]

/-- `options = 0` — a BLOCKING wait4 — declines. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 4294967295) 0 0 0
        (mkEffect (errno_ret ECHILD) [] []) port_model
      = .CheckUnmodeled := by
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A non-NULL `rusage` declines: it asks for accounting the model does not
    carry. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 4294967295) 0 (BitVec.ofInt 64 1)
        (BitVec.ofInt 64 4096) (mkEffect (errno_ret ECHILD) [] []) port_model
      = .CheckUnmodeled := by
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A return that is not -ECHILD is rejected: a reaped pid and WNOHANG's
    bare 0 are answers this model does not admit. -/
example (i : SyscallInput) :
    check_wait4 i (BitVec.ofInt 64 4294967295) 0 (BitVec.ofInt 64 1) 0
        (mkEffect (BitVec.ofInt 64 0) [] []) port_model
      = .CheckReject := by
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)]

end LinuxSem.Checks.Sys.Kernel.Exit
