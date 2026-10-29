/-
  * LinuxProcessSem.Checks.Witness.Fs.Locks — the flock (32) witness, and its proof

  Answers to Linux [fs/locks.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r [] []` abbreviates
  `mkEffectU r [] [] [] [] []` (`State.lean`).  The monadic step is
  `bind_step` of `Checks.Witness.Prelude` — `getModelSpec …` is
  definitionally `.ok _ _ []`, so
  `refine bind_step getModelSpec … rfl ?_` peels it — and `dsimp only`
  reduces what follows.

  The `FdEntry` split is an `rcases` with the same ten alternatives, which
  names the bound fields — `cases` on its own leaves them inaccessible, and
  the file arms, the only arms that read the path, need `p` by name.  The
  four file arms then share one script under `first`: for the six non-file
  arms the branch's `p` does not elaborate (or, for `FdPipe` and
  `FdDevNull`, has the wrong type), the branch fails, and `first` falls
  through to the decline.  `set_option autoImplicit false` is what keeps a
  missing `p` an error rather than an auto-bound variable.

  The four tests the witness branches on are the spec's own, and they
  appear in the goal as well as in the witness, so `by_cases` has to
  reduce neither: `flock_mand_b` / `flock_cmd_ok_b` / `flock_unlock_b` /
  `flock_sole_opener` all get stuck on `cmd.toNat` / `m_fds m` rather than
  diverging, which is why a plain `by_cases` chain suffices here.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Locks

set_option autoImplicit false

namespace LinuxSem.Checks.Witness.Fs.Locks

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Locks
open LinuxSem.Checks.Witness.Prelude

/-- flock witness: every modeled arm is deterministic — the spec draws
    no errno and chooses nothing — so the witness is the answer itself,
    and [Unmodeled] on the shapes the spec declines. -/
def flock_witness (fd cmd : word) (m : Model) : Outcome SyscallEffect Model event :=
  if flock_mand_b cmd then ret_outcome (BitVec.ofInt 64 0) m
  else if !(flock_cmd_ok_b cmd) then ret_outcome (errno_ret EINVAL) m
  else
    match fd_lookup (m_fds m) fd with
    | none => ret_outcome (errno_ret EBADF) m
    | some e =>
        if flock_unlock_b cmd then ret_outcome (BitVec.ofInt 64 0) m
        else
          match e with
          | FdEntry.FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (BitVec.ofInt 64 0) m else .unmodeled
          | FdEntry.FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (BitVec.ofInt 64 0) m else .unmodeled
          | FdEntry.FdFileA p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (BitVec.ofInt 64 0) m else .unmodeled
          | FdEntry.FdFileRW p _ =>
              if flock_sole_opener (m_fds m) p
              then ret_outcome (BitVec.ofInt 64 0) m
              else .unmodeled
          | FdEntry.FdChannel _ => .unmodeled
          | FdEntry.FdDir       => .unmodeled
          | FdEntry.FdSocket _  => .unmodeled
          | FdEntry.FdPipe _ _  => .unmodeled
          | FdEntry.FdDevNull _ _ => .unmodeled
          | FdEntry.FdUrandom => .unmodeled

theorem flock_witness_ok (fd cmd : word) (i : SyscallInput) (m : Model) :
    flock_spec fd cmd i m (flock_witness fd cmd m) := by
  unfold flock_spec flock_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  by_cases hmand : flock_mand_b cmd = true
  · simp only [ite_eq_left hmand, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hmand]
    by_cases hok : (!(flock_cmd_ok_b cmd)) = true
    · simp only [ite_eq_left hok, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hok]
      cases hfd : fd_lookup (m_fds m) fd with
      | none =>
        simp only [err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]
      | some e =>
        by_cases hun : flock_unlock_b cmd = true
        · simp only [ite_eq_left hun, ret_only, ret_outcome, mkEffect,
            LinuxSem.LinuxProcessSem.pure]
        · simp only [ite_eq_right hun]
          rcases e with ⟨c⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | _ | ⟨sk⟩
            | ⟨id, w⟩ | ⟨rd, wr⟩ | _
          all_goals
            (first
             | (by_cases hsole : flock_sole_opener (m_fds m) p = true
                · simp only [ite_eq_left hsole, ret_only, ret_outcome, mkEffect,
                    LinuxSem.LinuxProcessSem.pure]
                · simp only [ite_eq_right hsole, unmodeled])
             | simp only [unmodeled])

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal either.  These pin
    each arm of the witness against a concrete fd table: LOCK_MAND is 0
    without reading the fd, a bad operation is -EINVAL, a closed fd is
    -EBADF, a lock on a sole opener is 0, a lock on a doubled path
    declines, an unlock is 0 even there, and a channel declines. -/

/-- The path `out` for the table checks. -/
private def outPath : Fs.path := [0x6f, 0x75, 0x74]

/-- The path `dup` for the table checks. -/
private def dupPath : Fs.path := [0x64, 0x75, 0x70]

/-- A tiny fd table: 0 a channel, 1 a regular file (`out`), 3 and 4 two
    regular files naming the SAME path (`dup`). -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile outPath 0),
    (3, FdEntry.FdFile dupPath 0),
    (4, FdEntry.FdFileW dupPath 5) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- LOCK_MAND is 0 without reading the fd — even a closed one. -/
example : flock_witness 9 32 demoModel
    = ret_outcome (BitVec.ofInt 64 0) demoModel := by
  simp only [flock_witness]
  rw [ite_eq_left (by decide : flock_mand_b (32 : word) = true)]

/-- A bad operation is -EINVAL before the descriptor is resolved. -/
example : flock_witness 9 0 demoModel
    = ret_outcome (errno_ret EINVAL) demoModel := by
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (0 : word) = true)),
    ite_eq_left (by decide : (!(flock_cmd_ok_b (0 : word))) = true)]

/-- A closed fd is -EBADF. -/
example : flock_witness 9 2 demoModel
    = ret_outcome (errno_ret EBADF) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true)), hlook]

/-- A lock on a sole opener is 0. -/
example : flock_witness 1 2 demoModel
    = ret_outcome (BitVec.ofInt 64 0) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some (FdEntry.FdFile outPath 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, outPath, fd_lookup]
  have hsole : flock_sole_opener (m_fds demoModel) outPath = true := by decide
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true)), ite_eq_left hsole]

/-- A lock on a doubled path declares the model incomplete. -/
example : flock_witness 3 2 demoModel = .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3 = some (FdEntry.FdFile dupPath 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, dupPath, fd_lookup]
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true)),
    ite_eq_right (by decide : ¬(flock_sole_opener (m_fds demoModel) dupPath = true))]

/-- …but an UNLOCK on that same path is 0. -/
example : flock_witness 4 8 demoModel
    = ret_outcome (BitVec.ofInt 64 0) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 4 = some (FdEntry.FdFileW dupPath 5) := by
    simp [m_fds, demoModel, mkModel, demoFds, dupPath, fd_lookup]
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (8 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (8 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_left (by decide : flock_unlock_b (8 : word) = true)]

/-- A channel declines, and it declines without reading the buffer. -/
example : flock_witness 0 2 demoModel = .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [flock_witness]
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true))]

end LinuxSem.Checks.Witness.Fs.Locks
