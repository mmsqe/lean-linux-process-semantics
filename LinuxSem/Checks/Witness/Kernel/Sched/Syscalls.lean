/-
  * LinuxProcessSem.Checks.Witness.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) witnesses, and their proofs

  Answers to Linux [kernel/sched/syscalls.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled` and answering `.ok …` on the accepted arms; `ret_outcome` is
  `Checks/Witness/Prelude`'s.  `Ok (with_copyins [(param, 4%nat)]
  (mkEffect r [] [])) m []` is spelled the same way here, with the `Nat` of
  `4%nat` inferred from `List (word × Nat)`.

  The spec's prologue is one iff lemma, `bind_inputSpec` — `LinuxProcessSem`'s,
  reached through the `open` below — plus
  `Monad.bind_getModel`, so the whole step is a `simp only` in both
  directions; `dsimp only` performs the beta reduction after it.

  `sched_getaffinity_spec` and `sched_setscheduler_spec` are `SysSpec`s,
  i.e. FUNCTIONS, so their bodies are `if`s at FUNCTION type.  Lean's
  `whnf` on a goal mentioning one tries to reduce such an `if` — deciding
  `affinity_len_einval_b len` / `sint32 policy < 0` on an opaque word — and
  does not bottom out there (with the `sint32` spelling of the time it ran
  into `maximum recursion depth`; with today's `setWidth`/`toInt` spelling
  it is stuck rather than divergent, which is why the proofs below are still
  written against an opaque `Q`).
  `by_cases`/`cases` normalise their goal, so each proof `generalize`s its
  conclusion into a local `Q : Prop` first, splits against the (opaque)
  `Q`, and only at a leaf rewrites `Q` back with `rw [← hP]` and
  discharges the now-concrete branch with one `simp only`.  The same device
  keeps `cases` off the `read_bytes_map` match.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
import LinuxSem.Common.SharedFacts

namespace LinuxSem.Checks.Witness.Kernel.Sched.Syscalls
open LinuxSem.Common.SharedFacts

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Witness.Prelude

/-! ## The prologue peel, as one rewrite

    `sched_setscheduler_witness_ok` opens the spec's
    `i <- input ;; m <- get_model ;; …` prologue.  Stated as an iff, that
    step is a `simp only`.

    The iff itself is `LinuxSem.LinuxProcessSem.bind_inputSpec`, stated once
    next to the monad it is about; it reaches this file through the `open
    LinuxSem.LinuxProcessSem` above. -/

/-! ## sched_getaffinity (123) -/

/-- [sched_getaffinity] (123) is deterministic on both branches, so the
    witness is the branch itself: the -EINVAL, or the [Unmodeled] every
    length the two gates let through answers.  Failing closed is an
    admissible outcome, which is what makes progress hold on the
    second. -/
def sched_getaffinity_witness (len : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if affinity_len_einval_b len then ret_outcome (errno_ret EINVAL) m
  else .unmodeled

theorem sched_getaffinity_witness_ok (len : word) (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec len i m (sched_getaffinity_witness len m) := by
  generalize hP : (sched_getaffinity_spec len i m
    (sched_getaffinity_witness len m)) = Q at *
  by_cases hlen : affinity_len_einval_b len = true
  · rw [← hP]
    simp only [sched_getaffinity_spec, sched_getaffinity_witness, ite_eq_left hlen, err_ret,
      ret_only, LinuxSem.LinuxProcessSem.pure, ret_outcome]
  · rw [← hP]
    simp only [sched_getaffinity_spec, sched_getaffinity_witness, ite_eq_right hlen, unmodeled]

/-! ## sched_setscheduler (119) -/

/-- [sched_setscheduler] (119) is deterministic on every branch — it
    draws nothing and the one success changes no model state — so the
    witness is the branch itself, ledger included.  Failing closed is an
    admissible outcome, which is what makes progress hold on the three
    declines. -/
def sched_setscheduler_witness (pid policy param : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if sint32 policy < 0 then ret_outcome (errno_ret EINVAL) m
  else if w_is0 param || decide (sint32 pid < 0) then ret_outcome (errno_ret EINVAL) m
  else
  match read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
  | none =>
      if !access_okb param 4
      then ret_outcome (errno_ret EFAULT) m
      else .unmodeled
  | some bs =>
      if !sched_targets_self_b pid m then .unmodeled
      else
        match sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
        | some r => .ok (with_copyins [(param, 4)] (mkEffect r [] [])) m []
        | none => .unmodeled

theorem sched_setscheduler_witness_ok (i : SyscallInput) (pid policy param : word)
    (m : Model) :
    sched_setscheduler_spec pid policy param i m
      (sched_setscheduler_witness pid policy param i m) := by
  generalize hP : (sched_setscheduler_spec pid policy param i m
    (sched_setscheduler_witness pid policy param i m)) = Q at *
  by_cases hpolneg : sint32 policy < 0
  · rw [← hP]
    simp only [sched_setscheduler_spec, sched_setscheduler_witness, ite_eq_left hpolneg,
      err_ret, ret_only, LinuxSem.LinuxProcessSem.pure, ret_outcome]
  · by_cases hearly : (w_is0 param || decide (sint32 pid < 0)) = true
    · rw [← hP]
      simp only [sched_setscheduler_spec, sched_setscheduler_witness, ite_eq_right hpolneg,
        ite_eq_left hearly, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        ret_outcome]
    · cases hread : read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
      | none =>
          by_cases hacc : (!access_okb param 4) = true
          · rw [← hP]
            simp only [sched_setscheduler_spec, sched_setscheduler_witness, ite_eq_right hpolneg,
              ite_eq_right hearly, bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_left hacc,
              err_ret, ret_only, LinuxSem.LinuxProcessSem.pure, ret_outcome]
          · rw [← hP]
            simp only [sched_setscheduler_spec, sched_setscheduler_witness, ite_eq_right hpolneg,
              ite_eq_right hearly, bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_right hacc,
              unmodeled]
      | some bs =>
          by_cases hself : (!sched_targets_self_b pid m) = true
          · rw [← hP]
            simp only [sched_setscheduler_spec, sched_setscheduler_witness, ite_eq_right hpolneg,
              ite_eq_right hearly, bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_left hself]
            exact record_copyins_unmodeled (unmodeled_intro i m)
          · cases hans : sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
            | some r =>
                rw [← hP]
                simp only [sched_setscheduler_spec, sched_setscheduler_witness,
                  ite_eq_right hpolneg, ite_eq_right hearly, bind_inputSpec, getModelSpec, bind_getModel,
                  hread, ite_eq_right hself, hans]
                exact record_copyins_ret_only_ok [(param, 4)] r i m
            | none =>
                rw [← hP]
                simp only [sched_setscheduler_spec, sched_setscheduler_witness,
                  ite_eq_right hpolneg, ite_eq_right hearly, bind_inputSpec, getModelSpec, bind_getModel,
                  hread, ite_eq_right hself, hans]
                exact record_copyins_unmodeled (unmodeled_intro i m)

/-! ## sched_yield (124) -/

/-- [sched_yield] (124) has one outcome and no branch at all, so the
    witness is that outcome.  It is also the only arm here whose witness
    is never [Unmodeled]: the spec has no fail-closed branch to exhibit
    (see [Kernel.Sched.Syscalls.sched_yield_spec]). -/
def sched_yield_witness (m : Model) : Outcome SyscallEffect Model event :=
  ret_outcome (BitVec.ofInt 64 0) m

theorem sched_yield_witness_ok (i : SyscallInput) (m : Model) :
    sched_yield_spec i m (sched_yield_witness m) := by
  simp only [sched_yield_spec, sched_yield_witness, ret_only, ret_outcome,
    LinuxSem.LinuxProcessSem.pure]

/-! ## Sanity checks (not library lemmas)

    The library proofs leave no `vm_compute` goal here, so these checks
    cover the witness definitions, one per branch the matching spec's prose
    argues for:
    the -EINVAL, the fail-closed [Unmodeled] on a length the gates let
    through, and `sched_yield`'s single outcome. -/

/-- A malformed length (3 is not a multiple of 8) witnesses the -EINVAL. -/
example (m : Model) :
    sched_getaffinity_witness 3 m = ret_outcome (errno_ret EINVAL) m := by
  simp only [sched_getaffinity_witness, ite_eq_left (by decide : affinity_len_einval_b 3 = true)]

/-- …and a length the gates let through witnesses the decline. -/
example (m : Model) : sched_getaffinity_witness 8 m = .unmodeled := by
  simp only [sched_getaffinity_witness,
    ite_eq_right (by decide : ¬ (affinity_len_einval_b 8 = true))]

/-- `sched_yield`'s witness is the single outcome, `0` with an empty
    effect. -/
example (m : Model) : sched_yield_witness m
    = .ok (mkEffect (BitVec.ofInt 64 0) [] []) m [] := rfl

end LinuxSem.Checks.Witness.Kernel.Sched.Syscalls

