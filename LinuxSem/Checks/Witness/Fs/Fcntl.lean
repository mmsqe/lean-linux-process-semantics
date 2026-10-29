/-
  * LinuxProcessSem.Checks.Witness.Fs.Fcntl — the fcntl (25) witness, and its proof

  Answers to Linux [fs/fcntl.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome r m` is the `Checks.Witness.Prelude` shorthand
  for "return `r`, change nothing, emit nothing" (`mkEffect r ws []`).  The
  three command words and the two fd-kind predicates are the spec's own, as
  in the checker.

  Each proof peels the spec's fixed steps with
  `refine bind_step getModelSpec _ i m m m _ rfl ?_` and reduces with
  `try dsimp only`.  A scrutinee equation is handled by
  `generalize … at ⊢` followed by `cases`, and the split is made on
  `getfl_f_flags e` rather than on `FdEntry`, which spares a case split on
  the entry.  Each `if` guard occurs TWICE in the goal — once in the spec,
  once in the witness — so the splits use `simp only [ite_eq_left h]` /
  `[ite_eq_right h]` rather than `rw`, which would rewrite only one of the two
  occurrences.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl

namespace LinuxSem.Checks.Witness.Fs.Fcntl

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxSem.Checks.Witness.Prelude

/-- fcntl witness: -EBADF on a closed fd, 0 for F_SETFD and for an
    F_SETFL that provably changes nothing, the derived flag word for an
    F_GETFL on an fd kind [Fcntl.getfl_f_flags] answers for, and
    [Unmodeled] on every other command.

    A witness, not a second checker: it commits to ONE outcome, so the
    `Unmodeled` arms are the spec's own declines rather than a refusal to
    choose — an admissible outcome of a fail-closed spec, exactly as
    `socket_witness` and `Select`'s witnesses take their declinations. -/
def fcntl_witness (fd cmd arg : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if bv_eqb cmd F_SETFD then ret_outcome (BitVec.ofInt 64 0) m
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then ret_outcome (BitVec.ofInt 64 0) m
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => ret_outcome fl m
        | none => .unmodeled
      else .unmodeled

/-- The fcntl witness is admissible: it is an outcome of `fcntl_spec` for
    every input.  The four answered arms are `ret_only` at the word the
    witness returns; the declines are the spec's `unmodeled`. -/
theorem fcntl_witness_ok (fd cmd arg : word) (i : SyscallInput) (m : Model) :
    fcntl_spec fd cmd arg i m (fcntl_witness fd cmd arg m) := by
  unfold fcntl_spec fcntl_witness
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at ⊢
  cases e with
  | none =>
    dsimp only
    exact pure_ok _ i _
  | some e =>
    dsimp only
    by_cases hd : bv_eqb cmd F_SETFD = true
    · simp only [ite_eq_left hd]
      exact pure_ok _ i _
    · simp only [ite_eq_right hd]
      by_cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) = true
      · simp only [ite_eq_left hl]
        exact pure_ok _ i _
      · simp only [ite_eq_right hl]
        by_cases hg : bv_eqb cmd F_GETFL = true
        · simp only [ite_eq_left hg]
          generalize hfl : getfl_f_flags e = fl
          cases fl with
          | none => exact unmodeled_intro i m
          | some fl => exact pure_ok _ i _
        · simp only [ite_eq_right hg]
          exact unmodeled_intro i m

/- =========================================================================
   Sanity checks (not library lemmas)

   The module's proofs contain no `vm_compute` goal either — it is one
   definition and one proof.  The checks below pin the witness against a
   concrete fd table: -EBADF on a closed fd, 0 for F_SETFD, `O_RDWR` for
   F_GETFL on the socket, and the two declines.  `Outcome` carries no
   `DecidableEq`, so each states its branch as an equation with
   `ret_outcome` (the `.unmodeled` arms compare by the constructor).
   ========================================================================= -/

/-- The model the checks run in: a regular file on fd 3, a pipe read end
    on fd 4 and a socket on fd 5; fd 9 is absent.  (The same fixture
    `Sys/Fs/Fcntl.lean`'s own checks use.) -/
private def demoModel : Model :=
  mkModel
    [(BitVec.ofNat 64 3, FdEntry.FdFile [] (BitVec.ofInt 64 0)),
     (BitVec.ofNat 64 4, FdEntry.FdPipe (BitVec.ofNat 64 0) false),
     (BitVec.ofNat 64 5, FdEntry.FdSocket SockState.SkFresh)]
    (mkVmMaps [] [] 0 0 0) IEof []

/-- The fd table, without unfolding the whole `Model` (whose `NetStream`
    field has no decidable equality). -/
private theorem demoModel_fds :
    m_fds demoModel =
      [(BitVec.ofNat 64 3, FdEntry.FdFile [] (BitVec.ofInt 64 0)),
       (BitVec.ofNat 64 4, FdEntry.FdPipe (BitVec.ofNat 64 0) false),
       (BitVec.ofNat 64 5, FdEntry.FdSocket SockState.SkFresh)] := rfl

/-- A closed fd is -EBADF, whatever the command. -/
example (cmd arg : word) :
    fcntl_witness 9 cmd arg demoModel
      = ret_outcome (errno_ret EBADF) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [fcntl_witness, hlook]

/-- F_SETFD answers 0 for any arg. -/
example (arg : word) :
    fcntl_witness 3 F_SETFD arg demoModel
      = ret_outcome (BitVec.ofInt 64 0) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [fcntl_witness, hlook]
  rw [ite_eq_left (by decide : bv_eqb F_SETFD F_SETFD = true)]

/-- F_GETFL on the socket answers `O_RDWR` — the one fd kind whose flag
    word the model can derive. -/
example :
    fcntl_witness 5 F_GETFL 0 demoModel
      = ret_outcome (BitVec.ofInt 64 O_RDWR) demoModel := by
  have hlook : fd_lookup (m_fds demoModel) 5
      = some (FdEntry.FdSocket SockState.SkFresh) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [fcntl_witness, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFL F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFL F_SETFL && setfl_noop_on
    (FdEntry.FdSocket SockState.SkFresh) 0) = true))]
  rw [ite_eq_left (by decide : bv_eqb F_GETFL F_GETFL = true)]
  rfl

/-- …and on the other kinds it declines, exactly where the spec does. -/
example :
    fcntl_witness 3 F_GETFL 0 demoModel = .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [fcntl_witness, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFL F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFL F_SETFL && setfl_noop_on
    (FdEntry.FdFile [] (BitVec.ofInt 64 0)) 0) = true))]
  rw [ite_eq_left (by decide : bv_eqb F_GETFL F_GETFL = true)]
  rfl

/-- Every other command — `F_GETFD` (1), `F_DUPFD` (0), unknown words —
    declines. -/
example :
    fcntl_witness 5 F_GETFD 0 demoModel = .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 5
      = some (FdEntry.FdSocket SockState.SkFresh) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [fcntl_witness, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFD F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFD F_SETFL && setfl_noop_on
    (FdEntry.FdSocket SockState.SkFresh) 0) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFD F_GETFL = true))]

/-- The two errno words this file returns really are the kernel's numbers
    in the return word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : O_RDWR = 2 := by decide

end LinuxSem.Checks.Witness.Fs.Fcntl
