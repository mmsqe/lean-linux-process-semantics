/-
  * LinuxProcessSem.Checks.Witness.Kernel.Groups — the getgroups (158) and setgroups (159) witnesses, and their proofs

  Answers to Linux [kernel/groups.c]: this file holds the witnesses for the syscalls
  defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` / `ret_only` come from
  `Checks.Witness.Prelude` and `Sys.Syscall`.  The length of a group list is
  compared as an `Int` (`((…).length : Int)`), so the tests are the `Int`
  comparisons `n < 0` and `n = 0`, as in `Sys/Kernel/Groups.lean`.

  A proof steps the spec's leading `get_model` with `bind_getModel`, one
  rewrite.

  The spec's body is an `if` at FUNCTION type (`getgroups_spec` is a
  `SysSpec`), so Lean's `whnf` on a goal that mentions it tries to decide
  `sint32 gidsetsize < 0`, and `sint32` on an opaque word does not reduce
  far enough for that guard to be decided (while `sint32` had the earlier
  `narrow` body the same attempt ran out of recursion depth instead).
  `by_cases`
  normalises its goal, so each proof `generalize`s its conclusion into a
  local `Q : Prop` first, splits against `Q`, and only then rewrites `Q`
  back into the spec and discharges the branch with `simp only`.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Groups

namespace LinuxSem.Checks.Witness.Kernel.Groups

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
open LinuxSem.Checks.Witness.Prelude

/-! ## getgroups (158) -/

/-- [getgroups] (158) is deterministic on every branch, so the witness
    is the branch itself: the count, an -EINVAL, or the [Unmodeled] the
    writing path and the over-long-list guard both answer.  Failing
    closed is an admissible outcome, which is what makes progress hold
    on those two. -/
def getgroups_witness (gidsetsize : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  let n := sint32 gidsetsize
  if n < 0 then ret_outcome (errno_ret EINVAL) m
  else
    let ng : Int := ((m_creds m).cr_groups.length : Int)
    if NGROUPS_MAX < ng then .unmodeled
    else if n = 0 then ret_outcome (BitVec.ofInt 64 ng) m
    else if n < ng then ret_outcome (errno_ret EINVAL) m
    else if ng = 0 then ret_outcome (BitVec.ofInt 64 0) m
    else .unmodeled

theorem getgroups_witness_ok (gidsetsize : word) (i : SyscallInput) (m : Model) :
    getgroups_spec gidsetsize i m (getgroups_witness gidsetsize m) := by
  generalize hP : (getgroups_spec gidsetsize i m (getgroups_witness gidsetsize m)) = Q at *
  by_cases hneg : sint32 gidsetsize < 0
  · rw [← hP]
    simp only [getgroups_spec, getModelSpec, getgroups_witness, ite_eq_left hneg, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure, ret_outcome]
  · by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
    · rw [← hP]
      simp only [getgroups_spec, getModelSpec, bind_getModel, getgroups_witness, ite_eq_right hneg,
        ite_eq_left hmax, unmodeled]
    · by_cases hzero : sint32 gidsetsize = 0
      · rw [← hP]
        simp only [getgroups_spec, getModelSpec, bind_getModel, getgroups_witness, ite_eq_right hneg,
          ite_eq_right hmax, ite_eq_left hzero, ret_only, LinuxSem.LinuxProcessSem.pure,
          ret_outcome]
      · by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
        · rw [← hP]
          simp only [getgroups_spec, getModelSpec, bind_getModel, getgroups_witness, ite_eq_right hneg,
            ite_eq_right hmax, ite_eq_right hzero, ite_eq_left hsmall, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure, ret_outcome]
        · by_cases hempty : ((m_creds m).cr_groups.length : Int) = 0
          · rw [← hP]
            simp only [getgroups_spec, getModelSpec, bind_getModel, getgroups_witness,
              ite_eq_right hneg, ite_eq_right hmax, ite_eq_right hzero, ite_eq_right hsmall, ite_eq_left hempty, ret_only,
              LinuxSem.LinuxProcessSem.pure, ret_outcome]
          · rw [← hP]
            simp only [getgroups_spec, getModelSpec, bind_getModel, getgroups_witness,
              ite_eq_right hneg, ite_eq_right hmax, ite_eq_right hzero, ite_eq_right hsmall, ite_eq_right hempty, unmodeled]

/-! ## setgroups (159) -/

/-- [Unmodeled] is itself the admissible outcome on the privileged half:
    progress asks for an outcome the spec admits, and failing closed is
    one. -/
def setgroups_witness (m : Model) : Outcome SyscallEffect Model event :=
  if creds_privileged (m_creds m) then .unmodeled
  else ret_outcome (errno_ret EPERM) m

theorem setgroups_witness_ok (i : SyscallInput) (m : Model) :
    setgroups_spec i m (setgroups_witness m) := by
  generalize hP : (setgroups_spec i m (setgroups_witness m)) = Q at *
  by_cases hp : creds_privileged (m_creds m) = true
  · rw [← hP]
    simp only [setgroups_spec, getModelSpec, bind_getModel, setgroups_witness, ite_eq_left hp,
      unmodeled]
  · rw [← hP]
    simp only [setgroups_spec, getModelSpec, bind_getModel, setgroups_witness, ite_eq_right hp,
      err_ret, ret_only, LinuxSem.LinuxProcessSem.pure, ret_outcome]

end LinuxSem.Checks.Witness.Kernel.Groups
