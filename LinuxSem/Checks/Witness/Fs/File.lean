/-
  * LinuxProcessSem.Checks.Witness.Fs.File — the dup (23) and dup3 (24) witnesses, and their proofs

  Answers to Linux [fs/file.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  dup allocates, so its witness takes the environment-failure branch,
  as openat's does; dup3 is deterministic on every arm it answers and
  has none to take.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r [] []` abbreviates
  `mkEffectU r [] [] [] [] []` (`State.lean`).  The monadic step is
  `bind_step` of `Checks.Witness.Prelude` — `getModelSpec …` is
  definitionally `.ok _ _ []`, so
  `refine bind_step getModelSpec … rfl ?_` peels it — and `dsimp only`
  reduces what follows it.  A scrutinee equation is handled by `cases` on
  the scrutinee, which reduces the matches in the goal directly because
  they are in the target.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.File

namespace LinuxSem.Checks.Witness.Fs.File

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   dup (23)
   ========================================================================= -/

/-- dup's witness: -EBADF for a closed [oldfd], the fail-closed
    [Unmodeled] for an entry the model cannot duplicate, and otherwise
    the environment-failure branch the spec's [alt] offers — the fresh
    descriptor itself is chosen by the kernel, so the witness takes the
    errno arm (as openat's does), headed by [witness_errno]. -/
def dup_witness (oldfd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) oldfd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if !(dup_modeled_entry e) then .unmodeled
      else ret_outcome (errno_ret witness_errno) m

theorem dup_witness_ok (oldfd : word) (i : SyscallInput) (m : Model) :
    dup_spec oldfd i m (dup_witness oldfd m) := by
  unfold dup_spec dup_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  | some e =>
    by_cases hk : Bool.not (dup_modeled_entry e) = true
    · simp only [ite_eq_left hk, unmodeled]
    · simp only [ite_eq_right hk]
      refine alt_l _ _ i m (ret_outcome (errno_ret witness_errno) m) ?_
      refine bind_step (errno_from dup_errnos) (fun er => err_ret er) i m witness_errno m
        _ ?_ ?_
      · exact errno_head_witness witness_errno [EMFILE] i m
      · simp only [err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]

/- =========================================================================
   dup3 (24)
   ========================================================================= -/

/-- dup3's witness: every arm the spec answers deterministically is
    answered with the same value it does — -EINVAL for a bad flag word or
    equal descriptors, -EBADF above the limit or for a closed [oldfd],
    and [newfd] with the entry installed otherwise.  Only the two
    declined arms (an unmodeled entry, and a free [newfd] at or above
    [NR_OPEN_DEFAULT]) answer [Unmodeled], exactly where the spec does. -/
def dup3_witness (oldfd newfd flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(dup3_flags_ok flags) then ret_outcome (errno_ret EINVAL) m
  else if bv_eqb oldfd newfd then ret_outcome (errno_ret EINVAL) m
  else if !(dup3_newfd_under_limit newfd m)
       then ret_outcome (errno_ret EBADF) m
  else
    match fd_lookup (m_fds m) oldfd with
    | none => ret_outcome (errno_ret EBADF) m
    | some e =>
        if !(dup_modeled_entry e) then .unmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | none =>
              if decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT)
              then ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)
              else .unmodeled
          | some _ =>
              ret_outcome newfd (with_fds (fd_insert (m_fds m) newfd e) m)

theorem dup3_witness_ok (oldfd newfd flags : word) (i : SyscallInput) (m : Model) :
    dup3_spec oldfd newfd flags i m (dup3_witness oldfd newfd flags m) := by
  unfold dup3_spec dup3_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  by_cases hf : Bool.not (dup3_flags_ok flags) = true
  · simp only [ite_eq_left hf, err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hf]
    by_cases hne : bv_eqb oldfd newfd = true
    · simp only [ite_eq_left hne, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hne]
      by_cases hl : Bool.not (dup3_newfd_under_limit newfd m) = true
      · simp only [ite_eq_left hl, err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]
      · simp only [ite_eq_right hl]
        cases hfd : fd_lookup (m_fds m) oldfd with
        | none =>
          simp only [err_ret, ret_only, ret_outcome, mkEffect,
            LinuxSem.LinuxProcessSem.pure]
        | some e =>
          by_cases hk : Bool.not (dup_modeled_entry e) = true
          · simp only [ite_eq_left hk, unmodeled]
          · simp only [ite_eq_right hk]
            cases hnf : fd_lookup (m_fds m) newfd with
            | some x =>
              refine bind_step (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                (fun _ => ret_only newfd) i m () _ _ rfl ?_
              simp only [ret_only, ret_outcome, mkEffect,
                LinuxSem.LinuxProcessSem.pure]
            | none =>
              by_cases hb : decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) = true
              · simp only [ite_eq_left hb]
                refine bind_step (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                  (fun _ => ret_only newfd) i m () _ _ rfl ?_
                simp only [ret_only, ret_outcome, mkEffect,
                  LinuxSem.LinuxProcessSem.pure]
              · simp only [ite_eq_right hb, unmodeled]


/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal either.  These pin
   each arm of the two witnesses against a concrete fd table — the
   closed-fd -EBADF, the two declines, the errno dup's witness takes, and
   dup3's deterministic arms — which is the claim each proof above
   follows. -/

/-- A three-descriptor table: 0 a channel, 1 a directory, 2 a regular
    file.  Descriptors 3 and up are free. -/
private def portFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdDir), (2, FdEntry.FdFile [] 0)]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt, and the default
    RLIMIT_NOFILE. -/
private def portModel : Model :=
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A closed `oldfd` is -EBADF: the witness answers the spec's first arm. -/
example : dup_witness 9 portModel = ret_outcome (errno_ret EBADF) portModel := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [dup_witness, hlook]

/-- A [FdFile] entry takes the decline, not a copied entry. -/
example : dup_witness 2 portModel = .unmodeled := by
  have hlook : fd_lookup (m_fds portModel) 2 = some (FdEntry.FdFile [] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [dup_witness, hlook]
  rw [ite_eq_left (by decide : Bool.not (dup_modeled_entry (FdEntry.FdFile [] 0)) = true)]

/-- A modeled entry takes the environment-failure branch, with the errno
    that heads `dup_errnos` — the descriptor is the kernel's choice. -/
example :
    dup_witness 0 portModel = ret_outcome (errno_ret witness_errno) portModel := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [dup_witness, hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]

/-- dup3's witness answers -EINVAL for equal descriptors, before any
    validity test — fd 9 is closed. -/
example : dup3_witness 9 9 0 portModel
    = ret_outcome (errno_ret EINVAL) portModel := by
  simp only [dup3_witness]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_left (by decide : bv_eqb (9 : word) 9 = true)]

/-- A free `newfd` at or above `NR_OPEN_DEFAULT` declines, exactly where
    the spec does. -/
example : dup3_witness 0 70 0 portModel = .unmodeled := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have hnew : fd_lookup (m_fds portModel) 70 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [dup3_witness]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (0 : word) 70 = true))]
  rw [ite_eq_right (by decide :
    ¬(Bool.not (dup3_newfd_under_limit (70 : word) portModel) = true))]
  simp only [hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]
  simp only [hnew]
  rw [ite_eq_right (by decide :
    ¬(decide (((70 : word).toNat : Int) < NR_OPEN_DEFAULT) = true))]

/-- An open `newfd` is overwritten with `oldfd`'s entry and returned. -/
example : dup3_witness 0 1 0 portModel
    = ret_outcome 1
        (with_fds (fd_insert (m_fds portModel) 1 (FdEntry.FdChannel 7)) portModel) := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have hnew : fd_lookup (m_fds portModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [dup3_witness]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (0 : word) 1 = true))]
  rw [ite_eq_right (by decide :
    ¬(Bool.not (dup3_newfd_under_limit (1 : word) portModel) = true))]
  simp only [hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]
  simp only [hnew]

end LinuxSem.Checks.Witness.Fs.File
