/-
  * LinuxProcessSem.Checks.Witness.Fs.Readdir — the getdents64 (61) witness, and its proof

  Answers to Linux [fs/readdir.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r [] []` abbreviates `mkEffectU r [] [] [] [] []`
  (`State.lean`).  The monadic step is [bind_step] from
  `Checks.Witness.Prelude`: `getModelSpec …` is definitionally
  `.ok _ _ []`, so `refine bind_step getModelSpec … rfl ?_` peels it, and
  `dsimp only` reduces the beta/iota redexes after it.  A scrutinee
  equation is handled by `cases` on the scrutinee, which performs the
  rewrite AND reduces the `match` it unblocks, because both matches sit in
  the target — so no hypothesis rewrite is needed here, unlike in the
  checker's proofs.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Readdir

namespace LinuxSem.Checks.Witness.Fs.Readdir

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
open LinuxSem.Checks.Witness.Prelude

/-- On the directory arm the witness takes -EINVAL rather than the
    injected -ENOENT: it is the answer the model actually derives from
    [count], while a directory removed out from under the fd is a
    condition no modeled state decides.  Above the small-buffer band,
    failing closed is itself the admissible outcome. -/
def getdents64_witness (fd count : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdFile _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdFileW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdFileA _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdFileRW _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdPipe _ _)  => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdSocket _)  => ret_outcome (errno_ret ENOTDIR) m
  | some (FdEntry.FdDevNull _ _) => ret_outcome (errno_ret ENOTDIR) m
  | some FdEntry.FdUrandom => ret_outcome (errno_ret ENOTDIR) m
  | some FdEntry.FdDir =>
      if getdents64_no_room count
      then ret_outcome (errno_ret EINVAL) m
      else .unmodeled

theorem getdents64_witness_ok (fd count : word) (i : SyscallInput) (m : Model) :
    getdents64_spec fd count i m (getdents64_witness fd count m) := by
  unfold getdents64_spec getdents64_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  | some e =>
    cases e
    case FdDir =>
      generalize _hroom : getdents64_no_room count = b at ⊢
      cases b
      · -- above the small-buffer band: the listing is declined
        dsimp only
        rw [ite_eq_right (by decide : ¬((false : Bool) = true))]
        simp only [unmodeled]
        rfl
      · -- inside it: -EINVAL, the answer the model derives from `count`
        dsimp only
        rw [ite_eq_left rfl]
        refine alt_r _ _ i m (ret_outcome (errno_ret EINVAL) m) ?_
        simp only [err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]
    all_goals
      (simp only [err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure])

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal either.  These pin
    each arm of the witness against a concrete fd table — the closed-fd
    -EBADF, the -ENOTDIR of a non-directory, -EINVAL on a directory with
    a 23-byte buffer, and the decline above it — which is the claim the
    proof above follows. -/

/-- A tiny fd table: 0 a channel, 1 a directory, 2 a pipe end. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdDir),
    (2, FdEntry.FdPipe 0 true) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A closed fd is -EBADF: the witness answers the spec's first arm. -/
example : getdents64_witness 9 24 demoModel
    = ret_outcome (errno_ret EBADF) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [getdents64_witness, hlook]

/-- A CHANNEL IS -ENOTDIR, with no branch on the buffer. -/
example : getdents64_witness 0 24 demoModel
    = ret_outcome (errno_ret ENOTDIR) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [getdents64_witness, hlook]

/-- …and a PIPE END is too. -/
example : getdents64_witness 2 24 demoModel
    = ret_outcome (errno_ret ENOTDIR) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 2 = some (FdEntry.FdPipe 0 true) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [getdents64_witness, hlook]

/-- A DIRECTORY WITH A 23-BYTE BUFFER takes the deterministic -EINVAL,
    not the injected -ENOENT. -/
example : getdents64_witness 1 23 demoModel
    = ret_outcome (errno_ret EINVAL) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [getdents64_witness, hlook]
  rw [ite_eq_left (by decide : getdents64_no_room (23 : word) = true)]

/-- …and above the band it declares the listing unmodeled. -/
example : getdents64_witness 1 24 demoModel = .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [getdents64_witness, hlook]
  rw [ite_eq_right (by decide : ¬(getdents64_no_room (24 : word) = true))]

end LinuxSem.Checks.Witness.Fs.Readdir
