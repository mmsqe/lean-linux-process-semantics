/-
  * LinuxProcessSem.Checks.Witness.Fs.EventPoll — the epoll_create1 (20),
    epoll_ctl (21), epoll_pwait (22) witnesses, and their proofs

  Answers to Linux `fs/eventpoll.c`: this file holds the witnesses for
  the syscalls defined there, and no others.

  `Checks/Progress.lean` keeps the dispatcher and re-exports this module.
  A witness here exhibits one admissible outcome for a spec in the matching
  `Sys` module, which is what progress is proved from.  A witness answers
  with `Outcome SyscallEffect Model event`, declining as `.unmodeled`;
  `ret_outcome` is `Checks.Witness.Prelude`'s "return `r`, change nothing,
  emit nothing", and `srw` is the macro of that name in the same module.

  `epoll_ctl`'s fourth word argument is named `eventPtr`, not `event`:
  `event` is the observable-trace TYPE, and these signatures need
  `Outcome SyscallEffect Model event` in scope, so a binder of that name
  would shadow it.  Every signature is otherwise the spec's, in the spec's
  order.

  The case split is `generalize … at ⊢` + `cases`: splitting the goal
  directly would reduce only the spec's `match` and leave the witness's
  to `dsimp`, whereas the generalization reduces both — the spec's and the
  witness's, both on the same term — at once.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll

namespace LinuxSem.Checks.Witness.Fs.EventPoll

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxSem.Checks.Witness.Prelude

/- Each of the three arms is deterministic: the spec admits exactly one
    outcome per input, and where it admits none it is `Unmodeled`.  So
    every witness here is the spec's own `*_outcome` read back, and
    `Unmodeled` is itself the admissible outcome on the declining
    inputs — which is what makes progress hold for a syscall whose
    success arm is not modeled at all. -/

/-! ## epoll_create1 (20) -/

def epoll_create1_witness (flags32 : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match epoll_create1_outcome flags32 with
  | none => .unmodeled
  | some r => ret_outcome r m

theorem epoll_create1_witness_ok (flags32 : word) (i : SyscallInput)
    (m : Model) :
    epoll_create1_spec flags32 i m (epoll_create1_witness flags32 m) := by
  unfold epoll_create1_spec epoll_create1_witness
  generalize h : epoll_create1_outcome flags32 = oc at ⊢
  cases oc with
  | none => exact unmodeled_intro i m
  | some r => exact pure_ok (mkEffect r [] []) i m

/-! ## epoll_ctl (21) -/

def epoll_ctl_witness (epfd op32 tfd eventPtr : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  match epoll_ctl_outcome i m epfd op32 tfd eventPtr with
  | none => .unmodeled
  | some r => ret_outcome r m

theorem epoll_ctl_witness_ok (epfd op32 tfd eventPtr : word)
    (i : SyscallInput) (m : Model) :
    epoll_ctl_spec epfd op32 tfd eventPtr i m
      (epoll_ctl_witness epfd op32 tfd eventPtr i m) := by
  unfold epoll_ctl_spec epoll_ctl_witness
  refine bind_step _ _ i m i m _ ?_ ?_
  · exact input_ok i m
  · refine bind_step _ _ i m m m _ ?_ ?_
    · exact getModel_ok i m
    · generalize h : epoll_ctl_outcome i m epfd op32 tfd eventPtr = oc at ⊢
      cases oc with
      | none => exact unmodeled_intro i m
      | some r => exact pure_ok (mkEffect r [] []) i m

/-! ## epoll_pwait (22) -/

def epoll_pwait_witness (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => .unmodeled
  | some r => ret_outcome r m

theorem epoll_pwait_witness_ok (epfd events maxevents32 sigmask sigsetsize : word)
    (i : SyscallInput) (m : Model) :
    epoll_pwait_spec epfd events maxevents32 sigmask sigsetsize i m
      (epoll_pwait_witness epfd events maxevents32 sigmask sigsetsize i m) := by
  unfold epoll_pwait_spec epoll_pwait_witness
  refine bind_step _ _ i m i m _ ?_ ?_
  · exact input_ok i m
  · refine bind_step _ _ i m m m _ ?_ ?_
    · exact getModel_ok i m
    · generalize h :
        epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize = oc
        at ⊢
      cases oc with
      | none => exact unmodeled_intro i m
      | some r => exact pure_ok (mkEffect r [] []) i m

/-! ## Sanity checks

    There is no `vm_compute` goal in this module's proofs, so the check
    below is sanity checking rather than a lemma: it pins that the witness
    really is the spec's own
    `*_outcome` read back, i.e. that its declining branch is
    `.unmodeled` (which is what makes a `none`-answering arm receptive).
    It is stated with the outcome equation as a hypothesis because
    `Outcome` carries a `Model` and `Model` has no `DecidableEq`. -/

example (m : Model) (flags32 : word)
    (h : epoll_create1_outcome flags32 = none) :
    epoll_create1_witness flags32 m = .unmodeled := by
  rw [epoll_create1_witness, h]

example (i : SyscallInput) (m : Model)
    (h : epoll_ctl_outcome i m 0 0 0 0 = none) :
    epoll_ctl_witness 0 0 0 0 i m = .unmodeled := by
  rw [epoll_ctl_witness, h]

end LinuxSem.Checks.Witness.Fs.EventPoll
