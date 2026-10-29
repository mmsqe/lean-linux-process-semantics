/-
  * LinuxProcessSem.Checks.Witness.Kernel.Time.Hrtimer — the nanosleep (101) witness, and its proof

  Answers to Linux [kernel/time/hrtimer.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r ws []` abbreviates `mkEffectU r ws [] [] [] []`.

  Each proof peels the spec's reader with
  `refine bind_step inputSpec _ i m i m _ rfl ?_` — the reader is
  definitionally `.ok` — and reduces with `dsimp only`.  The branch
  booleans are split with `cases h : …` rather than `by_cases` for the
  reason `Checks.Sys.Kernel.Time.Hrtimer`'s header records: the spec's
  first test stands over an `if` at FUNCTION type, which `by_cases` would
  try to decide.  The branch tests are then literal, so the
  `ite_true_cond` / `ite_false_cond` pair below discharges them.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer

namespace LinuxSem.Checks.Witness.Kernel.Time.Hrtimer

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxSem.Checks.Witness.Prelude

/-- An `if` whose test `cases` has already rewritten to the literal `true`
    — `if true = true then a else b` — is its THEN arm. -/
private theorem ite_true_cond {α : Sort _} (a b : α) :
    (if (true = true) then a else b) = a := by
  rw [ite_eq_left rfl]

/-- …and one whose test has become `false = true` is its ELSE arm. -/
private theorem ite_false_cond {α : Sort _} (a b : α) :
    (if (false = true) then a else b) = b := by
  rw [ite_eq_right (show ¬(false = true) by decide)]

/-- nanosleep: the witness always takes the COMPLETED-SLEEP arm.  That
    arm needs nothing chosen — no remainder is written — so it is
    available for every model state the guards let through, and the
    interrupted arm, whose remainder would have to be constructed, is
    never needed to show the spec is receptive.

    It reads the model only to compute the new clock: there is no gate
    on `m_clock` to re-play, `Kernel.Time.Hrtimer.nanosleep_clock`
    clamping a saturating deadline rather than the spec declining it,
    and none on the request's seconds field either — a `tv_sec` at or
    above `Uapi.KTIME_SEC_MAX` is a sleep toward `Uapi.KTIME_MAX` and
    the completed arm exhibits it like any other.

    Every outcome it exhibits is reached through a successful read of
    the request, so every one of them carries that read in its ledger:
    `nanosleep_spec` wraps the whole arm in `record_copyins`, and a
    witness that left the ledger empty would no longer be an outcome
    the spec admits. -/
def nanosleep_witness (rqtp rmtp : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  match read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => .unmodeled                          -- unreadable request
  | some req =>
      if !(timespec_valid_b req)
      then .ok (with_copyins [(rqtp, 16)] (mkEffect (errno_ret EINVAL) [] []))
             m []
      else
        let done :=
          .ok (with_copyins [(rqtp, 16)] (mkEffect (BitVec.ofInt 64 0) [] []))
             (with_clock (nanosleep_clock (m_clock m) req []) m) []
        if w_is0 rmtp then done
        else match read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
             | none => .unmodeled               -- unwritable remainder
             | some _ => done

theorem nanosleep_witness_ok (i : SyscallInput) (rqtp rmtp : word) (m : Model) :
    nanosleep_spec rqtp rmtp i m (nanosleep_witness rqtp rmtp i m) := by
  unfold nanosleep_spec nanosleep_witness
  refine bind_step inputSpec _ i m i m _ rfl ?_
  cases hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
  | none => exact unmodeled_intro _ _
  | some req =>
    dsimp only
    cases hv : (!(timespec_valid_b req)) with
    | true =>
      rw [ite_true_cond]
      refine record_copyins_ok_empty (eff := mkEffect (errno_ret EINVAL) [] []) rfl ?_
      exact pure_ok _ i m
    | false =>
      rw [ite_false_cond]
      cases hrm : w_is0 rmtp with
      | true =>
        rw [ite_true_cond]
        refine record_copyins_ok_empty (eff := mkEffect (BitVec.ofInt 64 0) [] []) rfl ?_
        refine bind_step getModelSpec _ i m m m _ rfl ?_
        refine alt_l _ _ i m _ ?_
        refine bind_step (modifySpec (with_clock (nanosleep_clock (m_clock m) req []))) _
          i m () (with_clock (nanosleep_clock (m_clock m) req []) m) _ rfl ?_
        exact pure_ok _ _ _
      | false =>
        cases hwm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
        | none =>
          rw [ite_false_cond]
          refine record_copyins_unmodeled ?_
          refine bind_step getModelSpec _ i m m m _ rfl ?_
          rw [ite_false_cond]
          exact unmodeled_intro i m
        | some bs0 =>
          rw [ite_false_cond]
          refine record_copyins_ok_empty (eff := mkEffect (BitVec.ofInt 64 0) [] []) rfl ?_
          refine bind_step getModelSpec _ i m m m _ rfl ?_
          refine alt_l _ _ i m _ ?_
          refine bind_step (modifySpec (with_clock (nanosleep_clock (m_clock m) req []))) _
            i m () (with_clock (nanosleep_clock (m_clock m) req []) m) _ rfl ?_
          exact pure_ok _ _ _

end LinuxSem.Checks.Witness.Kernel.Time.Hrtimer
