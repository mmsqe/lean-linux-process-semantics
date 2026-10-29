/-
  * LinuxProcessSem.Checks.Sys.Fs.EventPoll — the epoll_create1 (20),
    epoll_ctl (21), epoll_pwait (22) checkers, and their proofs

  Answers to Linux `fs/eventpoll.c`: this file holds the checkers for the
  syscalls defined there, and no others.

  `Checks/ExecutableSpecs.lean` keeps the dispatcher and the four top-level
  theorems and re-exports this module.  The checkers here are executable,
  and their proofs relate them to the relational specs in the matching
  `Sys` module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`, and
  the spec monad's sequencing is `Monad.bind`: `epoll_ctl_spec` and
  `epoll_pwait_spec` are the `bind inputSpec … (bind getModelSpec …)` chains.

  `epoll_ctl`'s fourth word argument is named `eventPtr`: `event` IS the
  observable-trace type (`State.event`), and a word binder of that name would
  shadow it in the very signatures below that need `List event` for the
  events.  Every signature is otherwise the spec's, in the spec's order, and
  every use site passes the argument positionally.

  The tactic macros the proofs cite live in `Checks.Sys.Prelude` (`srw`,
  `hrw`, `hall`, `bool_true`, `inv_ok`, `sys_unfold`), and a branch equation
  is split with `cases H : …`.  Two points about how those macros are used:

  - a `bind` hypothesis is peeled with `Prelude.bind_input_model_inv` rather
    than by unfolding it and letting `inv_ok` take the existential apart
    (`inv_ok`'s own note explains why the generic hypothesis selector
    cannot);
  - a case split on the arm's `*_outcome` is done with `generalize … at H ⊢`
    + `cases`, so the goal AND the hypothesis reduce together; a split that
    leaves the goal's `match` standing needs `dsimp only` afterwards.

  `check_ret_only` never answers `CheckUnmodeled`, so in the `some r` branch
  of the `_sound_unmodeled` proofs the file cites
  `Prelude.check_ret_only_no_unmodeled` rather than re-destructing the
  effect's five ledgers.  Same statement, no extra assumption.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll

namespace LinuxSem.Checks.Sys.Fs.EventPoll

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxSem.Checks.Sys.Prelude

/- All three arms are deterministic and write no user memory, so each
    acceptor is the spec's own computation plus one equality on the
    return value.  `check_ret_only` carries the rest of the obligation:
    it rejects any effect with a non-empty write, zero, unmap, copy or
    copy-in ledger, which is what pins that a conforming run may not
    smuggle a store past an arm that stores nothing.

    Everything that makes epoll hard — readiness, the interest set, the
    ready list, blocking — is decided by the spec's `*_outcome`
    answering `none`, which is `CheckUnmodeled` here. -/

/-! ## epoll_create1 (20) -/

def check_epoll_create1 (flags32 : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match epoll_create1_outcome flags32 with
  | none => .CheckUnmodeled
  | some r => check_ret_only eff r m []

theorem check_epoll_create1_sound_ok (flags32 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_epoll_create1 flags32 eff m = .CheckOk m' evs) :
    epoll_create1_spec flags32 i m (.ok eff m' evs) := by
  unfold check_epoll_create1 at H
  unfold epoll_create1_spec
  generalize h : epoll_create1_outcome flags32 = oc at H ⊢
  cases oc with
  | none => exact nomatch H
  | some r =>
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
    exact pure_ok (mkEffect r [] []) i _

theorem check_epoll_create1_sound_unmodeled (flags32 : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_epoll_create1 flags32 eff m = .CheckUnmodeled) :
    epoll_create1_spec flags32 i m .unmodeled := by
  unfold check_epoll_create1 at H
  unfold epoll_create1_spec
  generalize h : epoll_create1_outcome flags32 = oc at H ⊢
  cases oc with
  | none => exact unmodeled_intro i m
  | some r => exact absurd H (check_ret_only_no_unmodeled eff r m [])

theorem check_epoll_create1_complete_ok (flags32 : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : epoll_create1_spec flags32 i m (.ok eff m' evs)) :
    check_epoll_create1 flags32 eff m = .CheckOk m' evs := by
  unfold epoll_create1_spec at H
  unfold check_epoll_create1
  generalize h : epoll_create1_outcome flags32 = oc at H ⊢
  cases oc with
  | none => exact nomatch H
  | some r =>
    obtain ⟨rfl, rfl, rfl⟩ := H
    exact (check_ret_only_ok_iff (mkEffect r [] []) r m [] _ _).mpr
      ⟨rfl, rfl, rfl⟩

theorem check_epoll_create1_complete_unmodeled (flags32 : word)
    (m : Model) (eff : SyscallEffect) (i : SyscallInput)
    (H : epoll_create1_spec flags32 i m .unmodeled) :
    check_epoll_create1 flags32 eff m = .CheckUnmodeled := by
  unfold epoll_create1_spec at H
  unfold check_epoll_create1
  generalize h : epoll_create1_outcome flags32 = oc at H ⊢
  cases oc with
  | none => rfl
  | some r => exact nomatch H

/-! ## epoll_ctl (21) -/

def check_epoll_ctl (i : SyscallInput) (epfd op32 tfd eventPtr : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_ctl_outcome i m epfd op32 tfd eventPtr with
  | none => .CheckUnmodeled
  | some r => check_ret_only eff r m []

theorem check_epoll_ctl_sound_ok (i : SyscallInput)
    (epfd op32 tfd eventPtr : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_epoll_ctl i epfd op32 tfd eventPtr eff m = .CheckOk m' evs) :
    epoll_ctl_spec epfd op32 tfd eventPtr i m (.ok eff m' evs) := by
  unfold check_epoll_ctl at H
  unfold epoll_ctl_spec
  refine bind_ok0 _ _ i m i m _ _ _ ?_ ?_
  · exact input_ok i m
  · refine bind_ok0 _ _ i m m m _ _ _ ?_ ?_
    · exact getModel_ok i m
    · generalize h : epoll_ctl_outcome i m epfd op32 tfd eventPtr = oc at H ⊢
      cases oc with
      | none => exact nomatch H
      | some r =>
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
        exact pure_ok (mkEffect r [] []) i _

theorem check_epoll_ctl_sound_unmodeled (i : SyscallInput)
    (epfd op32 tfd eventPtr : word) (eff : SyscallEffect) (m : Model)
    (H : check_epoll_ctl i epfd op32 tfd eventPtr eff m = .CheckUnmodeled) :
    epoll_ctl_spec epfd op32 tfd eventPtr i m .unmodeled := by
  unfold check_epoll_ctl at H
  unfold epoll_ctl_spec
  refine bind_unmodeled2 _ _ i m i m [] ?_ ?_
  · exact input_ok i m
  · refine bind_unmodeled2 _ _ i m m m [] ?_ ?_
    · exact getModel_ok i m
    · generalize h : epoll_ctl_outcome i m epfd op32 tfd eventPtr = oc at H ⊢
      cases oc with
      | none => exact unmodeled_intro i m
      | some r => exact absurd H (check_ret_only_no_unmodeled eff r m [])

theorem check_epoll_ctl_complete_ok (i : SyscallInput)
    (epfd op32 tfd eventPtr : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : epoll_ctl_spec epfd op32 tfd eventPtr i m (.ok eff m' evs)) :
    check_epoll_ctl i epfd op32 tfd eventPtr eff m = .CheckOk m' evs := by
  unfold epoll_ctl_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      match epoll_ctl_outcome i0 m0 epfd op32 tfd eventPtr with
      | none => unmodeled
      | some r => pure (mkEffect r [] []))
    i m (.ok eff m' evs) H
  unfold check_epoll_ctl
  generalize h : epoll_ctl_outcome i m epfd op32 tfd eventPtr = oc at H' ⊢
  cases oc with
  | none => exact nomatch H'
  | some r =>
    obtain ⟨rfl, rfl, rfl⟩ := H'
    exact (check_ret_only_ok_iff (mkEffect r [] []) r m [] _ _).mpr
      ⟨rfl, rfl, rfl⟩

theorem check_epoll_ctl_complete_unmodeled (i : SyscallInput)
    (epfd op32 tfd eventPtr : word) (m : Model) (eff : SyscallEffect)
    (H : epoll_ctl_spec epfd op32 tfd eventPtr i m .unmodeled) :
    check_epoll_ctl i epfd op32 tfd eventPtr eff m = .CheckUnmodeled := by
  unfold epoll_ctl_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      match epoll_ctl_outcome i0 m0 epfd op32 tfd eventPtr with
      | none => unmodeled
      | some r => pure (mkEffect r [] []))
    i m .unmodeled H
  unfold check_epoll_ctl
  generalize h : epoll_ctl_outcome i m epfd op32 tfd eventPtr = oc at H' ⊢
  cases oc with
  | none => rfl
  | some r => exact nomatch H'

/-! ## epoll_pwait (22) -/

def check_epoll_pwait (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => .CheckUnmodeled
  | some r => check_ret_only eff r m []

theorem check_epoll_pwait_sound_ok (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
      = .CheckOk m' evs) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
      (.ok eff m' evs) := by
  unfold check_epoll_pwait at H
  unfold epoll_pwait_spec
  refine bind_ok0 _ _ i m i m _ _ _ ?_ ?_
  · exact input_ok i m
  · refine bind_ok0 _ _ i m m m _ _ _ ?_ ?_
    · exact getModel_ok i m
    · generalize h :
        epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize = oc
        at H ⊢
      cases oc with
      | none => exact nomatch H
      | some r =>
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
        exact pure_ok (mkEffect r [] []) i _

theorem check_epoll_pwait_sound_unmodeled (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
      = .CheckUnmodeled) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m .unmodeled := by
  unfold check_epoll_pwait at H
  unfold epoll_pwait_spec
  refine bind_unmodeled2 _ _ i m i m [] ?_ ?_
  · exact input_ok i m
  · refine bind_unmodeled2 _ _ i m m m [] ?_ ?_
    · exact getModel_ok i m
    · generalize h :
        epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize = oc
        at H ⊢
      cases oc with
      | none => exact unmodeled_intro i m
      | some r => exact absurd H (check_ret_only_no_unmodeled eff r m [])

theorem check_epoll_pwait_complete_ok (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
      (.ok eff m' evs)) :
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
      = .CheckOk m' evs := by
  unfold epoll_pwait_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      match epoll_pwait_outcome i0 m0 epfd events maxevents32 sigmask sigsetsize with
      | none => unmodeled
      | some r => pure (mkEffect r [] []))
    i m (.ok eff m' evs) H
  unfold check_epoll_pwait
  generalize h :
      epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize = oc
      at H' ⊢
  cases oc with
  | none => exact nomatch H'
  | some r =>
    obtain ⟨rfl, rfl, rfl⟩ := H'
    exact (check_ret_only_ok_iff (mkEffect r [] []) r m [] _ _).mpr
      ⟨rfl, rfl, rfl⟩

theorem check_epoll_pwait_complete_unmodeled (i : SyscallInput)
    (epfd events maxevents32 sigmask sigsetsize : word)
    (m : Model) (eff : SyscallEffect)
    (H : epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
      .unmodeled) :
    check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m
      = .CheckUnmodeled := by
  unfold epoll_pwait_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      match epoll_pwait_outcome i0 m0 epfd events maxevents32 sigmask sigsetsize with
      | none => unmodeled
      | some r => pure (mkEffect r [] []))
    i m .unmodeled H
  unfold check_epoll_pwait
  generalize h :
      epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize = oc
      at H' ⊢
  cases oc with
  | none => rfl
  | some r => exact nomatch H'

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the three
    acceptors and their twelve proofs, nothing else.  The checks below
    are sanity checks: they pin that each acceptor answers
    `CheckUnmodeled` exactly where its arm's `*_outcome` declines.  That
    branch is stated with the outcome equation as a hypothesis rather
    than by `decide`, because `check_result` carries a `Model` in its
    `CheckOk` constructor and `Model` has no `DecidableEq`. -/

example (m : Model) (flags32 : word)
    (h : epoll_create1_outcome flags32 = none) :
    check_epoll_create1 flags32 (mkEffect 0 [] []) m = .CheckUnmodeled := by
  rw [check_epoll_create1, h]

example (i : SyscallInput) (m : Model)
    (h : epoll_ctl_outcome i m 0 0 0 0 = none) :
    check_epoll_ctl i 0 0 0 0 (mkEffect 0 [] []) m = .CheckUnmodeled := by
  rw [check_epoll_ctl, h]

example (i : SyscallInput) (m : Model)
    (h : epoll_pwait_outcome i m 0 0 0 0 0 = none) :
    check_epoll_pwait i 0 0 0 0 0 (mkEffect 0 [] []) m = .CheckUnmodeled := by
  rw [check_epoll_pwait, h]

end LinuxSem.Checks.Sys.Fs.EventPoll
