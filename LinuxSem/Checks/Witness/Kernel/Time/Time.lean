/-
  * LinuxProcessSem.Checks.Witness.Kernel.Time.Time — the gettimeofday (169) witness, and its proof

  Answers to Linux [kernel/time/time.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect r ws []` abbreviates `mkEffectU r ws [] [] [] []`,
  and `in_wmem i` is the record field `i.in_wmem`.  `copy_bytes_map` /
  `access_okb` are `StateMemory`'s, `Z_to_le_bytes` is `BvBase`'s, and
  `timeval_ok_b` / `gettimeofday_spec` come from `Sys.Kernel.Time.Time`;
  opening `…Sys.Kernel.Time` resolves the spec file's own `Time.<ident>`
  spelling.

  Each proof peels the spec's reader with
  `refine bind_step inputSpec _ i m i m _ rfl ?_` — the reader is
  definitionally `.ok` — and reduces with `try dsimp only`; a `choose` is
  discharged by `refine choose_ok _ _ i m ?_`.  A closed branch test is
  settled by `decide`.  A scrutinee equation is split with `cases h : …`,
  and where the same test occurs on BOTH sides of the goal (the witness
  repeats the spec's gates) `repeat rw` reaches every copy, as
  `Checks/Witness/Mm/Mprotect.lean` records.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Time

namespace LinuxSem.Checks.Witness.Kernel.Time.Time

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Witness.Prelude

/-- gettimeofday: the witness reports the epoch — [tv_sec = 0],
    [tv_usec = 0].  A wall-clock reading is constrained against nothing
    the model remembers, so one constant serves every input and every
    model state, and the witness moves no state at all. -/
def timeval_zero : List byte :=
  Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0

/-- gettimeofday: the null-[tz] / non-null-[tv] / writable-destination
    gates of [Time.gettimeofday_spec], in the spec's order, and then one
    admissible reading — the epoch.  The refused-destination arm answers
    -EFAULT exactly where the spec does, and the destination the model
    cannot vouch for (the torn band of a 16-byte range whose first 8-byte
    store is writable) declines. -/
def gettimeofday_witness (tv tz : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !w_is0 tz then .unmodeled
  else if w_is0 tv then .unmodeled
  else match copy_bytes_map i.in_wmem tv 16 with
       | none =>
           -- 8, not 16: see [Time.gettimeofday_spec]'s None arm
           if !access_okb tv 8 then ret_outcome (errno_ret EFAULT) m
           else .unmodeled
       | some _ =>
           .ok (mkEffect (BitVec.ofInt 64 0) [(tv, timeval_zero)] []) m []

theorem gettimeofday_witness_ok (i : SyscallInput) (tv tz : word) (m : Model) :
    gettimeofday_spec tv tz i m (gettimeofday_witness tv tz i m) := by
  unfold gettimeofday_spec gettimeofday_witness
  by_cases htz : (!w_is0 tz) = true
  · repeat rw [ite_eq_left htz]
    exact unmodeled_intro i m
  · repeat rw [ite_eq_right htz]
    by_cases htv : w_is0 tv = true
    · repeat rw [ite_eq_left htv]
      exact unmodeled_intro i m
    · repeat rw [ite_eq_right htv]
      refine bind_step inputSpec _ i m i m _ rfl ?_
      try dsimp only
      cases hw : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        by_cases ho : (!access_okb tv 8) = true
        · -- the first 8-byte store is refused: -EFAULT, nothing written
          repeat rw [ite_eq_left ho]
          try dsimp only
          exact pure_ok _ i m
        · -- the torn band, or a destination not wholly mapped: decline
          repeat rw [ite_eq_right ho]
          exact unmodeled_intro i m
      | some _ =>
        -- the epoch is a well-formed reading: [timeval_ok_b] holds of it
        refine bind_step (choose (fun bs : List byte => timeval_ok_b bs = true)) _
          i m timeval_zero m _ ?_ ?_
        · refine choose_ok _ _ i m ?_
          decide
        · exact pure_ok _ i m

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the witness
    and its one proof.  The checks below are sanity checks: they pin the one
    computable definition here, the epoch's sixteen zero bytes, and its
    well-formedness (which is the side condition the proof discharges with
    `decide`). -/

/-- The epoch is sixteen zero bytes: both fields are `0`. -/
example : timeval_zero = List.replicate 16 0 := by decide

/-- …and it is a well-formed `struct __kernel_old_timeval`: exactly 16
    bytes, `tv_usec = 0`, `tv_sec = 0`. -/
example : timeval_zero.length = 16 := by decide

example : tv_sec_of timeval_zero = 0 := by decide

example : tv_frac_of timeval_zero = 0 := by decide

example : timeval_ok_b timeval_zero = true := by decide

/-- A non-NULL `tz` declines unconditionally, before anything else is
    looked at. -/
example (i : SyscallInput) (m : Model) (tv : word) :
    gettimeofday_witness tv (BitVec.ofInt 64 0x1000) i m = .unmodeled := by
  unfold gettimeofday_witness
  rw [ite_eq_left (by decide)]

/-- A null `tv` declines next, at a NULL `tz`: the spec does too,
    rather than commit to Linux's "write nothing, answer 0". -/
example (i : SyscallInput) (m : Model) :
    gettimeofday_witness (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) i m
      = .unmodeled := by
  unfold gettimeofday_witness
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

end LinuxSem.Checks.Witness.Kernel.Time.Time
