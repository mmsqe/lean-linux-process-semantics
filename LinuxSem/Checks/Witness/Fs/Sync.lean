/-
  * LinuxProcessSem.Checks.Witness.Fs.Sync — the fsync (82), fdatasync (83) witnesses, and their proofs

  Answers to Linux [fs/sync.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome r m` is `Checks.Witness.Prelude`'s shorthand
  for "return `r`, change nothing, emit nothing".

  Each proof peels the spec's model reader with
  `refine bind_step getModelSpec _ i m m m _ rfl ?_` — the `rfl` is
  `getModel_ok` by definition — and reduces with `try dsimp only`.  A
  scrutinee equation is handled by `generalize … at ⊢` followed by `cases`,
  which reduces the scrutinee in the goal directly.  Every arm ends in
  `exact pure_ok _ i _`.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Sync

namespace LinuxSem.Checks.Witness.Fs.Sync

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Sync
open LinuxSem.Checks.Witness.Prelude

/-- The `fsync` (82) / `fdatasync` (83) witness: the answer
    `fsync_spec` gives for the fd's kind, and no other.

    The spec is deterministic on every input — it reads the fd table and
    answers a constant — so the witness is the spec's own answer, arm for
    arm: -EBADF for a closed fd, -EINVAL for the five kinds whose
    operations table carries no `.fsync`, and 0 for a file (whatever its
    access mode) or a directory.  Nothing here is `Unmodeled`, which is
    what makes progress on `fsync` immediate. -/
def fsync_witness (fd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdSocket _) => ret_outcome (errno_ret EINVAL) m
    -- no [.fsync] on a socket
  | some (FdEntry.FdPipe _ _) => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m
  | some FdEntry.FdUrandom => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdFileA _ _) => ret_outcome (BitVec.ofInt 64 0) m
  | some (FdEntry.FdFileRW _ _) => ret_outcome (BitVec.ofInt 64 0) m
  | some (FdEntry.FdFile _ _) => ret_outcome (BitVec.ofInt 64 0) m
  | some (FdEntry.FdFileW _ _) => ret_outcome (BitVec.ofInt 64 0) m
  | some FdEntry.FdDir => ret_outcome (BitVec.ofInt 64 0) m

theorem fsync_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    fsync_spec fd i m (fsync_witness fd m) := by
  unfold fsync_spec fsync_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at ⊢
  cases e with
  | none =>
    dsimp only
    exact pure_ok _ i _
  | some e =>
    cases e with
    | FdChannel _ =>
      dsimp only
      exact pure_ok _ i _
    | FdSocket _ =>
      dsimp only
      exact pure_ok _ i _
    | FdPipe _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdDevNull _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdUrandom =>
      dsimp only
      exact pure_ok _ i _
    | FdFileA _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdFileRW _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdFile _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdFileW _ _ =>
      dsimp only
      exact pure_ok _ i _
    | FdDir =>
      dsimp only
      exact pure_ok _ i _

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal either — it is one
   definition and one proof.  The checks below pin each arm of the
   witness against a concrete fd table: the closed-fd -EBADF, two of the
   -EINVAL kinds (a channel and a pipe end), and the two 0 answers (a
   regular file and a directory).  `Outcome` carries no `DecidableEq`, so
   each states the branch as an equation with `ret_outcome`. -/

/-- A four-descriptor table: 0 a channel, 1 a regular file (`out`), 2 a
    directory, 3 a pipe end.  Descriptors 4 and up are free. -/
private def portFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true) ]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and no rlimit. -/
private def portModel : Model :=
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A CLOSED FD IS -EBADF: the fd is resolved before the object is
    examined. -/
example : fsync_witness 9 portModel = ret_outcome (errno_ret EBADF) portModel := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook]

/-- A CHANNEL IS -EINVAL. -/
example : fsync_witness 0 portModel = ret_outcome (errno_ret EINVAL) portModel := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook]

/-- …AND SO IS A PIPE END — the arm whose `.fsync`-less table the model
    owns (`pipeanon_fops`). -/
example : fsync_witness 3 portModel = ret_outcome (errno_ret EINVAL) portModel := by
  have hlook : fd_lookup (m_fds portModel) 3 = some (FdEntry.FdPipe 0 true) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook]

/-- A REGULAR FILE IS 0, whatever the access mode. -/
example : fsync_witness 1 portModel
    = ret_outcome (BitVec.ofInt 64 0) portModel := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook]

/-- A DIRECTORY IS 0 AS WELL — the key-publish case. -/
example : fsync_witness 2 portModel = ret_outcome (BitVec.ofInt 64 0) portModel := by
  have hlook : fd_lookup (m_fds portModel) 2 = some FdEntry.FdDir := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook]

/-- The witness never declines: no arm is `Unmodeled`, which is what makes
    `fsync`'s progress argument immediate. -/
example : fsync_witness 9 portModel ≠ .unmodeled := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [fsync_witness, hlook, ret_outcome]
  exact fun h => nomatch h

/- =========================================================================
   prlimit64 (261) — witness: the modeled arms are deterministic apart
   from the environment's first choice of the inherited limit, and 16
   zero bytes are a well-formed pair (soft = hard = 0), so they serve.
   =========================================================================

   (The heading is kept for the file's structure: the prlimit64 witness
   it announces is stated elsewhere, so nothing follows it here.) -/

end LinuxSem.Checks.Witness.Fs.Sync
