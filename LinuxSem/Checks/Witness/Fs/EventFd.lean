/-
  * LinuxProcessSem.Checks.Witness.Fs.EventFd — the eventfd2 (19) witness, and its proof

  Answers to Linux `fs/eventfd.c`: this file holds the witnesses for the
  syscalls defined there, and no others.

  `Checks/Progress.lean` keeps the dispatcher and re-exports this module.
  A witness here exhibits one admissible outcome for a spec in the matching
  `Sys` module, which is what progress is proved from.

  The flags test reads the register UNSIGNED (`flags.toNat : Int`), and the
  mask difference is `Fs.File.z_ldiff`, i.e. `a & ~b` — the spec file
  carries the argument for the non-negative operand.  A witness answers
  with `Outcome SyscallEffect Model event`, and `ret_outcome` is
  `Checks.Witness.Prelude`'s shorthand for "return `r`, change nothing,
  emit nothing".

  The proof splits on the assembled negation `!(…) = true` and rewrites
  with `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]`, because once the
  spec and the witness are unfolded the SAME guard occurs TWICE — once in
  `eventfd2_spec`'s `if`, once in the witness's own — and `simp only`
  rewrites both occurrences where `rw` rewrites only the first.  The
  `generalize`d conclusion is `Checks/Sys/Kernel/Groups.lean`'s habit:
  `eventfd2_spec` is a `SysSpec`, a FUNCTION, so its `if` sits at function
  type and a `by_cases` aimed at the goal would whnf into the decision
  procedure rather than into a branch.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.EventFd

namespace LinuxSem.Checks.Witness.Fs.EventFd

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
open LinuxSem.Checks.Witness.Prelude

/-- The gate is written out for the third time; [Checks/Sys/Fs/EventFd]
    says why the three layers restate it rather than share one
    predicate.

    [Unmodeled] IS an admissible outcome, so the declined half needs no
    invented answer — the spec's own arm is [unmodeled], and exhibiting
    it is what makes this total.  [timerfd_create_witness] takes the
    same shape for the same reason. -/
def eventfd2_witness (flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(z_ldiff (flags.toNat : Int) EFD_FLAGS_SET == 0)
  then ret_outcome (errno_ret EINVAL) m
  else .unmodeled

theorem eventfd2_witness_ok (flags : word) (i : SyscallInput) (m : Model) :
    eventfd2_spec flags i m (eventfd2_witness flags m) := by
  generalize hP : (eventfd2_spec flags i m (eventfd2_witness flags m)) = Q at *
  by_cases hg : (!(z_ldiff (flags.toNat : Int) EFD_FLAGS_SET == 0)) = true
  · rw [← hP]
    unfold eventfd2_spec eventfd2_einval_b eventfd2_witness
    simp only [ite_eq_left hg]
    exact pure_ok _ i _
  · rw [← hP]
    unfold eventfd2_spec eventfd2_einval_b eventfd2_witness
    simp only [ite_eq_right hg]
    exact unmodeled_intro i m

/-! ## Sanity checks (not library lemmas)

    There is no `vm_compute` goal in this module — it is one definition and
    one proof — so what follows checks the witness rather than proving
    library lemmas.  The checks pin the witness's two arms and the
    input that separates this gate from `timerfd_create`'s:
    `EFD_SEMAPHORE` alone survives the gate, so the witness declines
    rather than inventing an -EINVAL Linux does not give.  `Outcome` has
    no `DecidableEq`, so each states its arm as an equation and closes
    it by unfolding the witness and discharging the guard by `decide`. -/

/-- The model the checks run in: no fds, an empty VM ledger, an empty file
    system, EOF on stdin, no halt, no rlimit and no credentials.  Nothing
    in it can matter to eventfd2 — the answer is a function of the flag
    word alone. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- BAD FLAGS ARE -EINVAL: the witness answers the errno word on the one
    arm the kernel answers it on. -/
example : eventfd2_witness 8 demoModel
    = ret_outcome (errno_ret EINVAL) demoModel := by
  unfold eventfd2_witness
  rw [ite_eq_left (by decide)]

/-- …and so is a foreign bit alongside the admitted ones. -/
example : eventfd2_witness (EFD_FLAGS_SET + 8) demoModel
    = ret_outcome (errno_ret EINVAL) demoModel := by
  unfold eventfd2_witness
  rw [ite_eq_left (by decide)]

/-- THE DECLINED HALF: a word that survives the gate has no invented
    answer — `Unmodeled` is the spec's own arm, which is what makes the
    witness total. -/
example : eventfd2_witness 0 demoModel = .unmodeled := by
  unfold eventfd2_witness
  rw [ite_eq_right (by decide)]

/-- `EFD_SEMAPHORE` ALONE DECLINES: `eventfd2(0, 1)` is a descriptor, not
    -EINVAL, so the witness does not fabricate that errno. -/
example : eventfd2_witness EFD_SEMAPHORE demoModel = .unmodeled := by
  unfold eventfd2_witness
  rw [ite_eq_right (by decide)]

end LinuxSem.Checks.Witness.Fs.EventFd
