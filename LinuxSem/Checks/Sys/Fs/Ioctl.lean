/-
  * LinuxProcessSem.Checks.Sys.Fs.Ioctl — the ioctl (29) checkers, and their proofs

  Answers to Linux [fs/ioctl.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); the spec monad `Sys SyscallEffect` is
  `SysSpec SyscallEffect` (`MonadInstances`); and the eight request words
  `tty_only_request` tests come from `Sys/Uapi.lean`, the predicate itself
  being the spec's — the checker tests the same one the spec does, so the
  two arms cannot drift.

  The `match` groups the nine non-`FdUrandom` open-fd constructors into ONE
  arm whose body is the `tty_only_request` test (`| p1 | p2 … => body` is
  one arm in Lean), in the spec's order of alternatives, while
  `FdUrandom` — the one kind that is `unmodeled` on every request — keeps
  its own arm.

  A scrutinee is split by `generalize … at H ⊢` + `cases`, with
  `dsimp only at H ⊢` after each split to reduce the `match` on the
  generalized scrutinee; a `tty_only_request req` test becomes a `by_cases`
  on the `Bool` equation plus `simp only [ite_eq_left …]` / `[ite_eq_right …]` on both
  the hypothesis and the goal.  `refine bind_ok0 getModelSpec _ … rfl ?_`
  peels the model reader and `exact pure_ok _ i _` closes a pure leaf; a
  `CheckUnmodeled`-vs-`CheckOk` equality is eliminated by `nomatch`, or by
  `check_ret_only_no_unmodeled` for the never-declining arm.

  The arms differ only in the word they answer, so the two directions of
  the `check_ret_only` correspondence and the spec's never-`unmodeled` fact
  are stated once below, as `arm_ok`, `arm_check_ok` and
  `arm_ne_unmodeled` — private helpers with no public surface, and the same
  three the `Sync` checker carries.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl

namespace LinuxSem.Checks.Sys.Fs.Ioctl

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Prelude

/-- The `ioctl` (29) checker: -EBADF for a closed fd (the fd is resolved
    before the request is examined), -ENOTTY for one of the eight
    terminal-only requests on any open fd, and `CheckUnmodeled`
    everywhere else.

    The two `CheckUnmodeled` arms are the spec's two `unmodeled` arms,
    arm for arm: `/dev/urandom` on every request, and any other request on
    every other open fd.  Everything that would write its result through
    the third argument — and so needs state `ioctl_spec` does not take —
    lands there, which is why the accepted arm is exactly the -ENOTTY
    one. -/
def check_ioctl (fd req : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) | some (FdEntry.FdFile _ _)
  | some (FdEntry.FdFileW _ _) | some FdEntry.FdDir
  | some (FdEntry.FdSocket _) | some (FdEntry.FdPipe _ _)
  | some (FdEntry.FdFileA _ _) | some (FdEntry.FdFileRW _ _)
  | some (FdEntry.FdDevNull _ _) =>
      if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else .CheckUnmodeled
  | some FdEntry.FdUrandom => .CheckUnmodeled

/- =========================================================================
   Private helpers: the arm correspondence

   Every answered arm of `check_ioctl` answers through `check_ret_only`
   with one word, and the spec's matching arm is `ret_only`/`err_ret` with
   the same word; writing the resulting three-line proof out in every arm
   of all four theorems would repeat it, so it is stated twice.  The third
   helper is the spec's side of the two `unmodeled` arms' absence: no
   `ret_only` (hence no `err_ret`) answers `unmodeled`.
   ========================================================================= -/

/-- Checker → spec, for one arm: an accepted `check_ret_only` *is* the
    spec's `ret_only` at that word, with the claimed model and events. -/
private theorem arm_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    ret_only r i m (.ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  exact pure_ok _ i _

/-- Spec → checker, for one arm: an outcome of the spec's `ret_only` at
    that word is accepted by `check_ret_only` at the same word. -/
private theorem arm_check_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : ret_only r i m (.ok eff m' evs)) :
    check_ret_only eff r m [] = .CheckOk m' evs := by
  obtain ⟨rfl, rfl, rfl⟩ := H
  simp [check_ret_only, bv_eqb_refl]

/-- Neither of the spec's two arm shapes can answer `unmodeled`: both are
    `ret_only`, whose only outcome is `.ok … []`. -/
private theorem arm_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  exact nomatch H

/-- The nine enumerated open-fd arms answer alike — the [tty_only_request]
    test — so each of them closes with this, in the accept direction.
    (The test is the same one in each of them.) -/
private theorem grouped_ok (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : (if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
          else .CheckUnmodeled) = .CheckOk m' evs) :
    (if tty_only_request req then err_ret ENOTTY else unmodeled) i m
      (.ok eff m' evs) := by
  by_cases ht : tty_only_request req = true
  · simp only [ite_eq_left ht] at H ⊢
    exact arm_ok (errno_ret ENOTTY) eff m m' evs i H
  · simp only [ite_eq_right ht] at H ⊢
    exact nomatch H

/-- …and in the decline direction: the checker declines only on a request
    outside the eight, which is exactly the spec's `unmodeled` arm. -/
private theorem grouped_unmodeled (req : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput)
    (H : (if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
          else .CheckUnmodeled) = .CheckUnmodeled) :
    (if tty_only_request req then err_ret ENOTTY else unmodeled) i m .unmodeled := by
  by_cases ht : tty_only_request req = true
  · simp only [ite_eq_left ht] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTTY) m [])
  · simp only [ite_eq_right ht] at H ⊢
    exact unmodeled_intro i m

/-- …and in the completeness direction, accept: a spec outcome in the open-fd
    arm is the checker's -ENOTTY arm (or, on a request outside the eight,
    nothing). -/
private theorem grouped_complete_ok (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : (if tty_only_request req then err_ret ENOTTY else unmodeled) i m
          (.ok eff m' evs)) :
    (if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else .CheckUnmodeled) = .CheckOk m' evs := by
  by_cases ht : tty_only_request req = true
  · simp only [ite_eq_left ht] at H ⊢
    exact arm_check_ok (errno_ret ENOTTY) eff m m' evs i H
  · simp only [ite_eq_right ht] at H ⊢
    exact nomatch H

/-- …and in the completeness direction, decline. -/
private theorem grouped_complete_unmodeled (req : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : (if tty_only_request req then err_ret ENOTTY else unmodeled) i m .unmodeled) :
    (if tty_only_request req then check_ret_only eff (errno_ret ENOTTY) m []
      else .CheckUnmodeled) = .CheckUnmodeled := by
  by_cases ht : tty_only_request req = true
  · simp only [ite_eq_left ht] at H ⊢
    exact absurd H (arm_ne_unmodeled _ i m)
  · -- the checker declines and so does the spec: both sides are `CheckUnmodeled`
    simp only [ite_eq_right ht] at H ⊢

theorem check_ioctl_sound_ok (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_ioctl fd req eff m = .CheckOk m' evs) :
    ioctl_spec fd req i m (.ok eff m' evs) := by
  unfold check_ioctl at H
  unfold ioctl_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    -- the match on the entry is enumerated, so `e` must be destructed for
    -- it to reduce; every constructor of the group answers alike
    cases e with
    | FdChannel _ => exact grouped_ok req eff m m' evs i H
    | FdFile _ _ => exact grouped_ok req eff m m' evs i H
    | FdFileW _ _ => exact grouped_ok req eff m m' evs i H
    | FdDir => exact grouped_ok req eff m m' evs i H
    | FdSocket _ => exact grouped_ok req eff m m' evs i H
    | FdPipe _ _ => exact grouped_ok req eff m m' evs i H
    | FdFileA _ _ => exact grouped_ok req eff m m' evs i H
    | FdFileRW _ _ => exact grouped_ok req eff m m' evs i H
    | FdDevNull _ _ => exact grouped_ok req eff m m' evs i H
    | FdUrandom => exact nomatch H

theorem check_ioctl_sound_unmodeled (fd req : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_ioctl fd req eff m = .CheckUnmodeled) :
    ioctl_spec fd req i m .unmodeled := by
  unfold check_ioctl at H
  unfold ioctl_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdChannel _ => exact grouped_unmodeled req eff m i H
    | FdFile _ _ => exact grouped_unmodeled req eff m i H
    | FdFileW _ _ => exact grouped_unmodeled req eff m i H
    | FdDir => exact grouped_unmodeled req eff m i H
    | FdSocket _ => exact grouped_unmodeled req eff m i H
    | FdPipe _ _ => exact grouped_unmodeled req eff m i H
    | FdFileA _ _ => exact grouped_unmodeled req eff m i H
    | FdFileRW _ _ => exact grouped_unmodeled req eff m i H
    | FdDevNull _ _ => exact grouped_unmodeled req eff m i H
    | FdUrandom =>
      -- the one arm where the checker declines exactly as the spec does
      exact unmodeled_intro i m

theorem check_ioctl_complete_ok (fd req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : ioctl_spec fd req i m (.ok eff m' evs)) :
    check_ioctl fd req eff m = .CheckOk m' evs := by
  unfold check_ioctl
  simp only [ioctl_spec, getModelSpec, bind_getModel] at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdChannel _ => exact grouped_complete_ok req eff m m' evs i H
    | FdFile _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdFileW _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdDir => exact grouped_complete_ok req eff m m' evs i H
    | FdSocket _ => exact grouped_complete_ok req eff m m' evs i H
    | FdPipe _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdFileA _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdFileRW _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdDevNull _ _ => exact grouped_complete_ok req eff m m' evs i H
    | FdUrandom => exact nomatch H

theorem check_ioctl_complete_unmodeled (fd req : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : ioctl_spec fd req i m .unmodeled) :
    check_ioctl fd req eff m = .CheckUnmodeled := by
  unfold check_ioctl
  simp only [ioctl_spec, getModelSpec, bind_getModel] at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (arm_ne_unmodeled _ i m)
  | some e =>
    cases e with
    | FdChannel _ => exact grouped_complete_unmodeled req eff m i H
    | FdFile _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdFileW _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdDir => exact grouped_complete_unmodeled req eff m i H
    | FdSocket _ => exact grouped_complete_unmodeled req eff m i H
    | FdPipe _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdFileA _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdFileRW _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdDevNull _ _ => exact grouped_complete_unmodeled req eff m i H
    | FdUrandom => rfl

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal either — it is one
   definition, four proofs and the prose above.  The checks below pin the
   three things those proofs follow against a concrete fd table:

   - a closed fd is -EBADF whatever the request is, because the fd is
     resolved first;
   - one of the eight terminal-only requests is -ENOTTY on every open-fd
     kind the group covers, `/dev/null` included;
   - a request OUTSIDE the eight is `CheckUnmodeled` (fail closed), and so
     is every request on `/dev/urandom`, whose `random_ioctl` the model
     declines to derive.

   `check_result` carries no `DecidableEq`, so each check states the
   expected `check_result` — or the expected `check_ret_only` — as an
   equation and closes it by unfolding the checker. -/

/-- A six-descriptor table: 0 a channel, 1 a regular file (`out`), 2 a
    directory, 3 a pipe end, 4 `/dev/null`, 5 `/dev/urandom`. -/
private def portFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdDevNull true false),
    (5, FdEntry.FdUrandom) ]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and no rlimit. -/
private def portModel : Model :=
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- FIONREAD (0x541B) is **not** one of the eight, although it shares the
    0x54 magic: `tty_only_request` is an explicit list, not a magic-letter
    test.  A `private def` so that the same word is handed back below
    without being re-elaborated as a different numeral. -/
private def fionreadWord : word := BitVec.ofInt 64 21531

/-- The predicate the two arms share really is the spec's; the eight
    requests are listed in `Sys/Fs/Ioctl.lean`'s own checks. -/
example : tty_only_request fionreadWord = false := by decide

/-- A CLOSED FD IS -EBADF, and the fd lookup is what decides: the request
    is never examined, so `ioctl(9, TCGETS, …)` is -EBADF rather than the
    -ENOTTY the request would earn on an open fd. -/
example (req : word) (eff : SyscallEffect) :
    check_ioctl 9 req eff portModel
      = check_ret_only eff (errno_ret EBADF) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]

/-- A CHANNEL FD ANSWERS -ENOTTY FOR A TERMINAL REQUEST: TIOCGWINSZ on
    stdin.  The channels are pipes in this model, and `pipe_ioctl`'s
    default arm is -ENOIOCTLCMD, which `vfs_ioctl` maps to -ENOTTY. -/
example (eff : SyscallEffect) :
    check_ioctl 0 TIOCGWINSZ eff portModel
      = check_ret_only eff (errno_ret ENOTTY) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_left (by decide : tty_only_request TIOCGWINSZ = true)]

/-- A REGULAR FILE ANSWERS THE SAME, and the answer does not depend on the
    access mode or on the file's contents: `__ext4_ioctl`'s default arm is
    -ENOTTY. -/
example (eff : SyscallEffect) :
    check_ioctl 1 TCGETS eff portModel
      = check_ret_only eff (errno_ret ENOTTY) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_left (by decide : tty_only_request TCGETS = true)]

/-- …AND `/dev/null` TOO — the one open-fd kind that reaches -ENOTTY through
    `vfs_ioctl`'s first branch rather than through -ENOIOCTLCMD. -/
example (eff : SyscallEffect) :
    check_ioctl 4 TIOCSWINSZ eff portModel
      = check_ret_only eff (errno_ret ENOTTY) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 4 = some (FdEntry.FdDevNull true false) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_left (by decide : tty_only_request TIOCSWINSZ = true)]

/-- A REQUEST OUTSIDE THE EIGHT IS DECLINED, not answered: FIONREAD on an
    open fd is `CheckUnmodeled`, because its success value depends on the
    fd's kind. -/
example (eff : SyscallEffect) :
    check_ioctl 0 fionreadWord eff portModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_right (by decide : ¬(tty_only_request fionreadWord = true))]

/- `/dev/urandom` IS DECLINED ON EVERY REQUEST, the eight included:
    `random_ioctl` answers -EINVAL for requests outside its own switch
    rather than -ENOTTY, so no constant here would be right. -/
example (eff : SyscallEffect) :
    check_ioctl 5 TCGETS eff portModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds portModel) 5 = some FdEntry.FdUrandom := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]

/-- THE ANSWERED ARM ACCEPTS THE BARE -ENOTTY EFFECT: one return word and
    nothing else, which is what makes the request modeled at all (it writes
    its result through no argument). -/
example :
    check_ioctl 0 TCGETS (mkEffect (errno_ret ENOTTY) [] []) portModel
      = .CheckOk portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_left (by decide : tty_only_request TCGETS = true)]
  simp [check_ret_only, bv_eqb_refl]

/-- …and it REJECTS anything whose shape is not that: the checker is the
    spec's shape, not just its return word.  A write alongside the -ENOTTY
    is not something `vfs_ioctl` can produce for a request it refuses. -/
example :
    check_ioctl 0 TCGETS ⟨errno_ret ENOTTY, [(0, [1])], [], [], [], []⟩ portModel
      = .CheckReject := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_ioctl, hlook]
  rw [ite_eq_left (by decide : tty_only_request TCGETS = true)]
  simp [check_ret_only]

/-- The two errnos really are the kernel's numbers in the return word —
    the encoding every answered arm above hands back. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret ENOTTY = BitVec.ofInt 64 (-25) := by decide

end LinuxSem.Checks.Sys.Fs.Ioctl
