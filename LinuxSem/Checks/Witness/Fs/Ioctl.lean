/-
  * LinuxProcessSem.Checks.Witness.Fs.Ioctl — the ioctl (29) witnesses, and their proofs

  Answers to Linux [fs/ioctl.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome r m` is `Checks.Witness.Prelude`'s shorthand
  for "return `r`, change nothing, emit nothing".

  The nine non-`FdUrandom` open-fd constructors are ONE arm in the `match`,
  the alternatives in the spec's order, and the `tty_only_request` test is
  its body.

  Each proof peels the spec's fixed steps with
  `refine bind_step getModelSpec _ i m m m _ rfl ?_` and reduces with
  `try dsimp only`.  A scrutinee equation is handled by
  `generalize … at ⊢` followed by `cases`; the arm's two possible answers
  are the `by_cases` on `tty_only_request` in `grouped_witness` below, one
  branch per answer.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl

namespace LinuxSem.Checks.Witness.Fs.Ioctl

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxSem.Checks.Witness.Prelude

/-- The `ioctl` (29) witness: the answer `ioctl_spec` gives for the fd's
    kind and the request, and no other.

    A closed fd is -EBADF (the fd is resolved first); one of the eight
    terminal-only requests on any other open fd is -ENOTTY; every other
    request, and every request on `/dev/urandom`, is `Unmodeled` — the
    same two declines the spec answers.  So the witness is exact: it
    declines precisely where the model does, and nowhere else. -/
def ioctl_witness (fd req : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) | some (FdEntry.FdFile _ _)
  | some (FdEntry.FdFileW _ _) | some FdEntry.FdDir
  | some (FdEntry.FdSocket _) | some (FdEntry.FdPipe _ _)
  | some (FdEntry.FdFileA _ _) | some (FdEntry.FdFileRW _ _)
  | some (FdEntry.FdDevNull _ _) =>
      if tty_only_request req then ret_outcome (errno_ret ENOTTY) m
      else .unmodeled
  | some FdEntry.FdUrandom => .unmodeled

/-- The nine enumerated open-fd arms answer alike — the [tty_only_request]
    test — so each of them closes with this: -ENOTTY for one of the eight
    requests, `unmodeled` for anything else.  The nine arms share the
    test because the spec gives them the same one, so one proof closes
    all of them. -/
private theorem grouped_witness (req : word) (i : SyscallInput) (m : Model) :
    (if tty_only_request req then err_ret ENOTTY else unmodeled) i m
      (if tty_only_request req then ret_outcome (errno_ret ENOTTY) m
       else .unmodeled) := by
  by_cases ht : tty_only_request req = true
  · simp only [ite_eq_left ht]
    exact pure_ok _ i _
  · simp only [ite_eq_right ht]
    exact unmodeled_intro i m

theorem ioctl_witness_ok (fd req : word) (i : SyscallInput) (m : Model) :
    ioctl_spec fd req i m (ioctl_witness fd req m) := by
  unfold ioctl_spec ioctl_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at ⊢
  cases e with
  | none =>
    dsimp only
    exact pure_ok _ i _
  | some e =>
    -- the open-fd arms are enumerated, so `e` must be destructed for the
    -- match to reduce; every constructor of the group answers alike
    cases e with
    | FdChannel _ => exact grouped_witness req i m
    | FdFile _ _ => exact grouped_witness req i m
    | FdFileW _ _ => exact grouped_witness req i m
    | FdDir => exact grouped_witness req i m
    | FdSocket _ => exact grouped_witness req i m
    | FdPipe _ _ => exact grouped_witness req i m
    | FdFileA _ _ => exact grouped_witness req i m
    | FdFileRW _ _ => exact grouped_witness req i m
    | FdDevNull _ _ => exact grouped_witness req i m
    | FdUrandom => exact unmodeled_intro i m

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal either — it is one
   definition and one proof.  The checks below pin the arms that proof
   follows against a concrete fd table: the closed-fd -EBADF, the -ENOTTY
   arm on a channel and on a regular file, and the two declines — a
   request outside the eight, and `/dev/urandom` on one of the eight.
   `Outcome` carries no `DecidableEq`, so each states the branch as an
   equation with `ret_outcome`. -/

/-- A six-descriptor table: 0 a channel, 1 a regular file (`out`), 2 a
    directory, 3 a pipe end, 4 `/dev/null`, 5 `/dev/urandom`.  Descriptors
    6 and up are free. -/
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
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof []

/-- FIONREAD (0x541B): a request outside the eight, although it shares the
    0x54 magic with some of them.  A `private def` so the same word is
    handed back below without being re-elaborated as a different numeral. -/
private def fionreadWord : word := BitVec.ofInt 64 21531

/-- A CLOSED FD IS -EBADF whatever the request is: the fd is resolved
    first. -/
example (req : word) :
    ioctl_witness 9 req portModel = ret_outcome (errno_ret EBADF) portModel := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]

/-- A CHANNEL ANSWERS -ENOTTY FOR A TERMINAL REQUEST: TIOCGWINSZ on
    stdin. -/
example : ioctl_witness 0 TIOCGWINSZ portModel
    = ret_outcome (errno_ret ENOTTY) portModel := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]
  rw [ite_eq_left (by decide : tty_only_request TIOCGWINSZ = true)]

/-- …AND SO DOES A REGULAR FILE — the same constant, which is the point of
    the arm. -/
example : ioctl_witness 1 TCGETS portModel
    = ret_outcome (errno_ret ENOTTY) portModel := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]
  rw [ite_eq_left (by decide : tty_only_request TCGETS = true)]

/-- A REQUEST OUTSIDE THE EIGHT IS DECLINED — the same fail-closed move the
    spec makes, not an errno. -/
example : ioctl_witness 0 fionreadWord portModel = .unmodeled := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]
  rw [ite_eq_right (by decide : ¬(tty_only_request fionreadWord = true))]

/-- `/dev/urandom` IS DECLINED ON EVERY REQUEST, the eight included. -/
example : ioctl_witness 5 TCGETS portModel = .unmodeled := by
  have hlook : fd_lookup (m_fds portModel) 5 = some FdEntry.FdUrandom := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]

/-- The witness is exact rather than merely admissible: it answers -ENOTTY
    exactly where the checker accepts, and declines exactly where the spec
    does.  The two sides are pinned against each other on the words the
    arms return. -/
example : (match ioctl_witness 0 TCGETS portModel with
    | .ok eff _ _ => eff.eff_ret
    | .unmodeled => BitVec.ofInt 64 0) = errno_ret ENOTTY := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [ioctl_witness, hlook]
  rw [ite_eq_left (by decide : tty_only_request TCGETS = true)]
  simp [ret_outcome, mkEffect]

end LinuxSem.Checks.Witness.Fs.Ioctl
