/-
  * LinuxProcessSem.Checks.Sys.Fs.EventFd — the eventfd2 (19) checker, and its proofs

  Answers to Linux `fs/eventfd.c`: this file holds the checkers for the
  syscalls defined there, and no others.

  `Checks/ExecutableSpecs.lean` keeps the dispatcher and the four top-level
  theorems and re-exports this module.  The checkers here are
  executable, and their proofs relate them to the relational specs in
  the matching `Sys` module.

  Flags are read UNSIGNED (`(flags.toNat : Int)`), and the mask difference is
  `Fs.File.z_ldiff` — `a & ~b`, i.e. `a - (a & b)` for a non-negative `a`;
  `Sys/Fs/EventFd.lean` carries the argument and `Sys/Fs/File.lean` the
  definition.  The checker answers with `CheckOk` / `CheckReject` /
  `CheckUnmodeled`.

  The gate is one tactic macro below, named after the step it performs, and
  three of its properties are worth recording:

  - `by_cases` keeps the equation it splits on, and this macro USES that
    equation — `ite_eq_left`/`ite_eq_right` need it — so it takes the hypothesis name as
    a second argument, and its branches are selected with `case pos`/`case
    neg` rather than with a `·` bullet (a macro whose expansion ends in
    bullets swallows the bullets that follow it in the same tactic sequence);
  - the `simp only` folds in the negation, and its `first` picks `ite_eq_left` or
    `ite_eq_right` — whichever one typechecks against the equation — so the
    assembled condition in every hypothesis reduces to the branch just
    chosen;
  - the split is still on the raw equality `(z_ldiff … == 0)`, not on either
    side's assembled gate: nothing here depends on the two files spelling the
    gate the same way.

  Each proof keeps `Checks/Sys/Kernel/Groups.lean`'s habit of
  `generalize`-ing its conclusion into an opaque `Q : Prop` before any case
  split, because `eventfd2_spec` is a `SysSpec` — a FUNCTION — and its `if`
  therefore sits at function type.  The macro's `… at *` reaches that
  equation (`hP`) as well, so by the time a leaf runs, `hP`'s spec side is
  already the branch's body: the two `sound` proofs close with
  `simp only [err_ret, ret_only, pure]` (or `[unmodeled]`) rather than with a
  second unfold — the unfold has already happened, in the macro.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.EventFd

namespace LinuxSem.Checks.Sys.Fs.EventFd

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Prelude

/-- The gate is WRITTEN OUT rather than taken from
    [Sys.Fs.EventFd.eventfd2_einval_b], and the four lemmas below are
    what make the repetition worth its cost: they force this statement
    and the spec's to coincide.  Importing the spec's predicate would
    leave a wrong gate agreeing with itself, which is the reason
    [Checks/Sys/Fs/Timerfd] restates its own gate instead of sharing it.

    Note what the repetition does NOT buy, because the difference
    matters here more than usual: an identical MISTAKE made in both
    files still closes every proof.  These lemmas relate the checker to
    the spec and never either to Linux.  They do not show that the
    admitted mask really is Linux's [EFD_FLAGS_SET].

    [check_ret_only] carries the rest of the obligation: it rejects any
    effect with a non-empty write, zero, unmap, copy or copy-in ledger,
    which is what pins that a conforming run may not smuggle a store
    past an arm that stores nothing.  [eventfd2] reads no user memory
    and writes none, so all six ledgers are empty on the one answer this
    arm gives. -/
def check_eventfd2 (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(z_ldiff (flags.toNat : Int) EFD_FLAGS_SET == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else .CheckUnmodeled

/-- Both sides of every proof below branch on the same equality.
    Splitting THAT — rather than the assembled condition — is what keeps
    the tactic from depending on the two files spelling the gate with
    the same negation, which is exactly the coincidence the restatement
    exists to avoid relying on.

    The macro takes the hypothesis name as well as `flags`, because
    `by_cases` keeps the equation it splits on and the leaves below need
    it. -/
macro "eventfd2_gate " flags:term " as " hg:ident : tactic =>
  `(tactic|
    (unfold eventfd2_spec eventfd2_einval_b at *
     by_cases $hg:ident : (!(z_ldiff (($flags).toNat : Int) EFD_FLAGS_SET == 0)) = true <;>
       first
         | simp only [ite_eq_left $hg:ident] at *
         | simp only [ite_eq_right $hg:ident] at *))

theorem check_eventfd2_sound_ok (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_eventfd2 flags eff m = .CheckOk m' evs) :
    eventfd2_spec flags i m (.ok eff m' evs) := by
  generalize hP : (eventfd2_spec flags i m (.ok eff m' evs)) = Q at *
  unfold check_eventfd2 at H
  eventfd2_gate flags as hg
  case pos =>
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  case neg =>
    exact nomatch H

theorem check_eventfd2_sound_unmodeled (flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_eventfd2 flags eff m = .CheckUnmodeled) :
    eventfd2_spec flags i m .unmodeled := by
  generalize hP : (eventfd2_spec flags i m .unmodeled) = Q at *
  unfold check_eventfd2 at H
  eventfd2_gate flags as hg
  case pos =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  case neg =>
    rw [← hP]
    simp only [LinuxSem.LinuxProcessSem.unmodeled]

theorem check_eventfd2_complete_ok (flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : eventfd2_spec flags i m (.ok eff m' evs)) :
    check_eventfd2 flags eff m = .CheckOk m' evs := by
  generalize hP : (check_eventfd2 flags eff m = .CheckOk m' evs) = Q at *
  eventfd2_gate flags as hg
  case pos =>
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    unfold check_eventfd2
    rw [ite_eq_left hg]
    simp [check_ret_only, bv_eqb_refl]
  case neg =>
    simp only [LinuxSem.LinuxProcessSem.unmodeled] at H
    exact nomatch H

theorem check_eventfd2_complete_unmodeled (flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : eventfd2_spec flags i m .unmodeled) :
    check_eventfd2 flags eff m = .CheckUnmodeled := by
  generalize hP : (check_eventfd2 flags eff m = .CheckUnmodeled) = Q at *
  eventfd2_gate flags as hg
  case pos =>
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  case neg =>
    rw [← hP]
    unfold check_eventfd2
    rw [ite_eq_right hg]

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal — it is one checker
    and its four proofs.  The checks below pin the two arms the proofs
    follow and the ledger obligation `check_ret_only` adds: the word with
    an unknown bit is -EINVAL, every word that survives the gate is
    declined (`EFD_SEMAPHORE` alone included, since `eventfd2(0, 1)` is a
    descriptor and not -EINVAL), any other return is rejected, and so is
    any effect that claims a write.  `check_result` has no
    `DecidableEq`, so each states the branch as an equation and closes it
    by unfolding the checker and discharging the gate by `decide` — the
    same style as `Checks/Sys/Fs/EventPoll.lean`. -/

/-- The model the checks run in: no fds, an empty VM ledger, an empty file
    system, EOF on stdin, no halt, no rlimit and no credentials.  Nothing
    in it can matter to eventfd2 — the answer is a function of the flag
    word alone. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- THE -EINVAL ARM: an unknown bit in the flag word is refused, and the
    bare return carries that errno and nothing else. -/
example : check_eventfd2 8 (mkEffect (errno_ret EINVAL) [] []) demoModel
    = .CheckOk demoModel [] := by
  unfold check_eventfd2
  rw [ite_eq_left (by decide)]
  simp [check_ret_only, bv_eqb_refl]

/-- …and so is a foreign bit SET ALONGSIDE the admitted ones. -/
example : check_eventfd2 (EFD_FLAGS_SET + 8) (mkEffect (errno_ret EINVAL) [] [])
    demoModel = .CheckOk demoModel [] := by
  unfold check_eventfd2
  rw [ite_eq_left (by decide)]
  simp [check_ret_only, bv_eqb_refl]

/-- THE DECLINE: every word that survives the gate is `CheckUnmodeled`,
    whatever the effect is — the counter, the descriptor number, the
    -EMFILE limit and the allocation failures are what the model does not
    carry. -/
example : check_eventfd2 0 (mkEffect (errno_ret EINVAL) [] []) demoModel
    = .CheckUnmodeled := by
  unfold check_eventfd2
  rw [ite_eq_right (by decide)]

/-- `EFD_SEMAPHORE` ALONE SURVIVES THE GATE — the one input that separates
    this gate from `timerfd_create`'s.  `eventfd2(0, 1)` hands back a
    descriptor, so the checker declines rather than answering -EINVAL. -/
example : check_eventfd2 EFD_SEMAPHORE (mkEffect (errno_ret EINVAL) [] [])
    demoModel = .CheckUnmodeled := by
  unfold check_eventfd2
  rw [ite_eq_right (by decide)]

/-- A RETURN OTHER THAN -EINVAL IS REJECTED on the gate's own arm:
    `check_ret_only` compares the word. -/
example : check_eventfd2 8 (mkEffect 0 [] []) demoModel = .CheckReject := by
  unfold check_eventfd2
  rw [ite_eq_left (by decide)]
  simp [check_ret_only]
  decide

/-- …AND SO IS A WRITE LEDGER: `eventfd2` writes no user memory, so an
    effect that claims a write is rejected on the ledger rather than on
    the return value. -/
example : check_eventfd2 8 (mkEffect (errno_ret EINVAL) [(0, [1])] []) demoModel
    = .CheckReject := by
  unfold check_eventfd2
  rw [ite_eq_left (by decide)]
  simp [check_ret_only]

end LinuxSem.Checks.Sys.Fs.EventFd
