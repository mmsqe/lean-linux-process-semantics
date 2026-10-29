/-
  * LinuxProcessSem.Checks.Witness.Fs.Timerfd — the timerfd_create (85) witness, and its proof

  Answers to Linux [fs/timerfd.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome r m` is `Checks.Witness.Prelude`'s shorthand
  for "return `r`, change nothing, emit nothing", and the mask difference
  is `Sys.Fs.File.z_ldiff` (`a & ~b`).

  The gate is written out here again; [Checks/Sys/Fs/Timerfd] says why the
  three layers restate it rather than share one predicate.  The expression
  is the kernel's text, flattened where the spec's disjunction is
  right-nested, and `gate_eq` below is the same six-way split the checker's
  `gate_eq` performs — so the witness does not depend on the two files'
  parenthesization agreeing either.

  `gate_eq` turns the six comparisons of the raw gate into a single split
  of the assembled predicate, and each of the two leaves is the arm it
  names.  `solve [apply pure_ok | apply unmodeled_intro]` is spelled out
  per branch, since Lean has no `solve` over a goal-selecting loop.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd

namespace LinuxSem.Checks.Witness.Fs.Timerfd

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxSem.Checks.Witness.Prelude

/-- The gate, written out for the third time (see
    [Checks/Sys/Fs/Timerfd]).  A `false` gate admits the call, a `true`
    one is the kernel's -EINVAL. -/
private def timerfd_create_gate (clkid flags : word) : Bool :=
  !(z_ldiff (flags.toNat : Int) TFD_CREATE_FLAGS == 0) ||
    !((clkid.toNat : Int) == CLOCK_REALTIME ||
      (clkid.toNat : Int) == CLOCK_MONOTONIC ||
      (clkid.toNat : Int) == CLOCK_BOOTTIME ||
      (clkid.toNat : Int) == CLOCK_REALTIME_ALARM ||
      (clkid.toNat : Int) == CLOCK_BOOTTIME_ALARM)

/-- The restated gate and the spec's predicate coincide, by exhaustive
    split of the six comparisons. -/
private theorem gate_eq (clkid flags : word) :
    timerfd_create_gate clkid flags = timerfd_create_einval_b clkid flags := by
  unfold timerfd_create_gate timerfd_create_einval_b
  generalize h1 : (z_ldiff (flags.toNat : Int) TFD_CREATE_FLAGS == 0) = a
  generalize h2 : ((clkid.toNat : Int) == CLOCK_REALTIME) = b
  generalize h3 : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = c
  generalize h4 : ((clkid.toNat : Int) == CLOCK_BOOTTIME) = d
  generalize h5 : ((clkid.toNat : Int) == CLOCK_REALTIME_ALARM) = e
  generalize h6 : ((clkid.toNat : Int) == CLOCK_BOOTTIME_ALARM) = f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- timerfd_create witness: -EINVAL where the kernel's gate is taken, and
    [Unmodeled] where it is not.

    [Unmodeled] IS an admissible outcome, so the declined half needs no
    invented answer — the spec's own arm is `unmodeled`, and exhibiting
    it is what makes this total.  (`socket_witness` takes the same shape
    for the same reason.)  The witness therefore declines precisely where
    the model does, and nowhere else. -/
def timerfd_create_witness (clkid flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if timerfd_create_gate clkid flags
  then ret_outcome (errno_ret EINVAL) m
  else .unmodeled

/-- The timerfd_create witness is admissible: an outcome of
    `timerfd_create_spec` for every input. -/
theorem timerfd_create_witness_ok (clkid flags : word) (i : SyscallInput)
    (m : Model) :
    timerfd_create_spec clkid flags i m (timerfd_create_witness clkid flags m) := by
  unfold timerfd_create_spec timerfd_create_witness
  rw [gate_eq clkid flags]
  by_cases hg : timerfd_create_einval_b clkid flags = true
  · simp only [ite_eq_left hg]
    exact pure_ok _ i _
  · simp only [ite_eq_right hg]
    exact unmodeled_intro i m

/- =========================================================================
   Sanity checks (not library lemmas)

   The module's proofs contain no `vm_compute` goal either — it is one
   definition and one proof.  The checks below pin the two arms against
   concrete words: the -EINVAL of a stray flag bit and of an unknown
   clock id, and the decline of an admitted clock (the alarm clocks
   included, since -EINVAL is an errno Linux does not produce for them).
   ========================================================================= -/

/-- A model for the checks: an empty fd table, an empty VM ledger, an
    empty file system, EOF on stdin, no halt.  `timerfd_create_witness`
    reads none of it. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A STRAY FLAG BIT IS -EINVAL, whatever the clock id — here the alarm
    clock, so the answer is the gate's -EINVAL and never the -EPERM of
    the capability check below it. -/
example :
    timerfd_create_witness (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 1 demoModel
      = ret_outcome (errno_ret EINVAL) demoModel := by
  rw [timerfd_create_witness, ite_eq_left (by decide)]

/-- AN UNKNOWN CLOCK ID IS -EINVAL, the id `clock_gettime` answers
    included. -/
example :
    timerfd_create_witness (BitVec.ofInt 64 CLOCK_PROCESS_CPUTIME_ID) 0 demoModel
      = ret_outcome (errno_ret EINVAL) demoModel := by
  rw [timerfd_create_witness, ite_eq_left (by decide)]

/-- WITH THE GATE PASSED THE WITNESS DECLINES — the spec's own arm, which
    is what makes the witness total. -/
example :
    timerfd_create_witness (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 demoModel
      = .unmodeled := by
  rw [timerfd_create_witness, ite_eq_right (by decide)]

example :
    timerfd_create_witness (BitVec.ofInt 64 CLOCK_BOOTTIME_ALARM) 0 demoModel
      = .unmodeled := by
  rw [timerfd_create_witness, ite_eq_right (by decide)]

/-- The errno word really is the kernel's number, and the admitted flag
    mask is `O_CLOEXEC | O_NONBLOCK` (526336). -/
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : TFD_CREATE_FLAGS = 526336 := by decide

end LinuxSem.Checks.Witness.Fs.Timerfd
