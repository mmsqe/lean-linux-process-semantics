/-
  * LinuxProcessSem.Checks.Sys.Kernel.Sched.Syscalls — the sched_getaffinity (123), sched_setscheduler (119) and sched_yield (124) checkers, and their proofs

  Answers to Linux [kernel/sched/syscalls.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks/Sys/Prelude.lean`, spelled `.CheckOk` etc.); a signed test is the
  `Int` comparison itself (`sint32 policy < 0`, with the `Bool` unboxed);
  and `outcome` / `Sys A` are `Outcome SyscallEffect Model event` /
  `SysSpec SyscallEffect` (`MonadInstances`).

  The spec's two readers are one iff lemma, `bind_inputSpec` (below), plus
  `Monad.bind_getModel`, so the whole prologue is a `simp only` step in both
  directions.  `sys_unfold` / `inv_ok` give way to the `simp only` lists
  spelled out at each leaf; `dsimp only` performs the beta/iota reduction;
  and a `CheckUnmodeled = CheckOk` equation is eliminated by `nomatch`.

  `sched_getaffinity_spec` and `sched_setscheduler_spec` are `SysSpec`s,
  i.e. FUNCTIONS, so their bodies are `if`s at FUNCTION type.  Lean's `whnf`
  on a goal that mentions one tries to reduce such an `if` — deciding
  `affinity_len_einval_b len` / `sint32 policy < 0` on a still-opaque word —
  and the reduction recurses without bottoming out (`maximum recursion
  depth`).  `by_cases`/`cases` normalise their goal, so every proof below
  `generalize`s its conclusion into a local `Q : Prop` FIRST, does all the
  case splits against the (opaque) `Q`, and only at a leaf rewrites `Q` back
  with `rw [← hP]` and discharges the now-concrete branch with one
  `simp only`.  The same device keeps `cases` off the `read_bytes_map`
  match.

  The `constructorNameAsVariable` linter normalises binder types, and
  therefore attempts the same reduction; on
  `check_sched_setscheduler_complete_ok` and
  `check_sched_setscheduler_complete_unmodeled` — the two declarations whose
  hypothesis is the `sched_setscheduler_spec` application — it fails with
  the recursion error above rather than a finding.  It is switched off for
  exactly those two declarations, and nowhere else.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls

namespace LinuxSem.Checks.Sys.Kernel.Sched.Syscalls

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Sys.Prelude

/-- The spec monad's `bind` under an unambiguous name: Lean's root `bind`
    is `Bind.bind`, so the unqualified name would be ambiguous. -/
local notation "bind" => LinuxSem.LinuxProcessSem.bind

/-! ## The prologue peel, as one rewrite

    Both `sched_setscheduler` proofs open the spec's
    `i <- input ;; m <- get_model ;; …` prologue.  Stated as an iff, that
    step is a `simp only` on either side of the proof. -/

private theorem bind_inputSpec {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event) :
    bind inputSpec k i m o ↔ k i i m o := by
  cases o with
  | ok x m' evs =>
      constructor
      · exact input_bind_ok_inv k i m x m' evs
      · intro h
        exact bind_ok0 inputSpec k i m i m x m' evs (input_ok i m) h
  | unmodeled =>
      constructor
      · exact input_bind_unmodeled_inv k i m
      · intro h
        exact bind_unmodeled2 inputSpec k i m i m [] (input_ok i m) h

/-- `record_copyins reads (ret_only r)`: the answer `r`, no writes, and
    `reads` on the copy-in ledger.  (`record_copyins` prepends to
    `eff.eff_copyins`, which is `[]` for `ret_only`, so the
    `reads ++ []` it builds is that same list.) -/
private theorem record_copyins_ret_only_ok (reads : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) :
    record_copyins reads (ret_only r) i m
      (.ok (with_copyins reads (mkEffect r [] [])) m []) := by
  refine ⟨mkEffect r [] [], m, [], [], rfl, ?_, rfl⟩
  simp [LinuxSem.LinuxProcessSem.pure, with_copyins, List.append_nil]

/-! ## sched_getaffinity (123) -/

/-- [sched_getaffinity] (123): -EINVAL on a length either kernel gate
    refuses, and [CheckUnmodeled] on every length they let through.
    Mirrors [Kernel.Sched.Syscalls.sched_getaffinity_spec] branch for
    branch — read that spec for why neither [pid] nor [user_mask_ptr] is
    an argument here either, and for what the decline costs. -/
def check_sched_getaffinity (len : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if affinity_len_einval_b len
  then check_ret_only eff (errno_ret EINVAL) m []
  else .CheckUnmodeled

theorem check_sched_getaffinity_sound_ok (len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_sched_getaffinity len eff m = .CheckOk m' evs) :
    sched_getaffinity_spec len i m (.ok eff m' evs) := by
  generalize hP : (sched_getaffinity_spec len i m (.ok eff m' evs)) = Q at *
  simp only [check_sched_getaffinity] at H
  by_cases hlen : affinity_len_einval_b len = true
  · simp only [ite_eq_left hlen] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [sched_getaffinity_spec, ite_eq_left hlen, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hlen] at H
    exact nomatch H

/-- The one decline is every length the gates let through: the answer
    there depends on [nr_cpu_ids] and [cpumask_size()], which this model
    does not carry. -/
theorem check_sched_getaffinity_sound_unmodeled (len : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_sched_getaffinity len eff m = .CheckUnmodeled) :
    sched_getaffinity_spec len i m .unmodeled := by
  generalize hP : (sched_getaffinity_spec len i m .unmodeled) = Q at *
  simp only [check_sched_getaffinity] at H
  by_cases hlen : affinity_len_einval_b len = true
  · simp only [ite_eq_left hlen] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · simp only [ite_eq_right hlen] at H
    rw [← hP]
    simp only [sched_getaffinity_spec, ite_eq_right hlen, unmodeled]

theorem check_sched_getaffinity_complete_ok (len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : sched_getaffinity_spec len i m (.ok eff m' evs)) :
    check_sched_getaffinity len eff m = .CheckOk m' evs := by
  generalize hP : (check_sched_getaffinity len eff m = .CheckOk m' evs) = Q at *
  simp only [sched_getaffinity_spec] at H
  by_cases hlen : affinity_len_einval_b len = true
  · simp only [ite_eq_left hlen] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_sched_getaffinity, ite_eq_left hlen]
    simp [check_ret_only, bv_eqb_refl]
  · simp only [ite_eq_right hlen] at H
    simp only [unmodeled] at H
    exact nomatch H

theorem check_sched_getaffinity_complete_unmodeled (len : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : sched_getaffinity_spec len i m .unmodeled) :
    check_sched_getaffinity len eff m = .CheckUnmodeled := by
  generalize hP : (check_sched_getaffinity len eff m = .CheckUnmodeled) = Q at *
  simp only [sched_getaffinity_spec] at H
  by_cases hlen : affinity_len_einval_b len = true
  · simp only [ite_eq_left hlen] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · simp only [ite_eq_right hlen] at H
    rw [← hP]
    simp only [check_sched_getaffinity, ite_eq_right hlen]

/-! ## sched_setscheduler (119) -/

/-- [sched_setscheduler] (119).  Mirrors
    [Kernel.Sched.Syscalls.sched_setscheduler_spec] branch for branch,
    and shares [sched_setscheduler_answer] with it rather than
    transcribing the kernel's ordered chain a second time — read that
    spec for the envelope, for what the SCHED_IDLE answer assumes, and
    for why the model carries no scheduling state.

    The [i] is here for the four bytes at [param]: the copy-in runs
    before the task lookup, so its ledger rides on every path past it. -/
def check_sched_setscheduler (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if sint32 policy < 0 then check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 param || decide (sint32 pid < 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else
  match read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
  | none =>
      if !access_okb param 4
      then check_ret_only eff (errno_ret EFAULT) m []
      else .CheckUnmodeled
  | some bs =>
      if !sched_targets_self_b pid m then .CheckUnmodeled
      else
        match sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
        | some r => check_ret_only_copyins [(param, 4)] eff r m []
        | none => .CheckUnmodeled

theorem check_sched_setscheduler_sound_ok (i : SyscallInput)
    (pid policy param : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_sched_setscheduler i pid policy param eff m = .CheckOk m' evs) :
    sched_setscheduler_spec pid policy param i m (.ok eff m' evs) := by
  generalize hP : (sched_setscheduler_spec pid policy param i m (.ok eff m' evs)) = Q at *
  simp only [check_sched_setscheduler] at H
  by_cases hpolneg : sint32 policy < 0
  · simp only [ite_eq_left hpolneg] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [sched_setscheduler_spec, ite_eq_left hpolneg, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hpolneg] at H
    by_cases hearly : (w_is0 param || decide (sint32 pid < 0)) = true
    · simp only [ite_eq_left hearly] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [← hP]
      simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_left hearly, err_ret,
        ret_only, LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hearly] at H
      cases hread : read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
      | none =>
          simp only [hread] at H
          by_cases hacc : (!access_okb param 4) = true
          · simp only [ite_eq_left hacc] at H
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
            rw [← hP]
            simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_right hearly,
              bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_left hacc, err_ret,
              ret_only, LinuxSem.LinuxProcessSem.pure]
          · simp only [ite_eq_right hacc] at H
            exact nomatch H
      | some bs =>
          simp only [hread] at H
          by_cases hself : (!sched_targets_self_b pid m) = true
          · simp only [ite_eq_left hself] at H
            exact nomatch H
          · simp only [ite_eq_right hself] at H
            cases hans : sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
            | none =>
                simp only [hans] at H
                exact nomatch H
            | some r =>
                simp only [hans] at H
                obtain ⟨heff, hm', hevs⟩ :=
                  (check_ret_only_copyins_ok_iff [(param, 4)] eff r m [] m' evs).mp H
                rw [← hP]
                rw [heff, hm', hevs]
                simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_right hearly,
                  bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_right hself, hans]
                exact record_copyins_ret_only_ok [(param, 4)] r i m

/-- The four declines, in the order the kernel reaches them: a [param]
    range [access_ok] admits but memory does not back, a pid naming a
    task this model has no representation of, and the two shapes
    [sched_setscheduler_answer] answers [None] for. -/
theorem check_sched_setscheduler_sound_unmodeled (i : SyscallInput)
    (pid policy param : word) (eff : SyscallEffect) (m : Model)
    (H : check_sched_setscheduler i pid policy param eff m = .CheckUnmodeled) :
    sched_setscheduler_spec pid policy param i m .unmodeled := by
  generalize hP : (sched_setscheduler_spec pid policy param i m .unmodeled) = Q at *
  simp only [check_sched_setscheduler] at H
  by_cases hpolneg : sint32 policy < 0
  · simp only [ite_eq_left hpolneg] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · simp only [ite_eq_right hpolneg] at H
    by_cases hearly : (w_is0 param || decide (sint32 pid < 0)) = true
    · simp only [ite_eq_left hearly] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · simp only [ite_eq_right hearly] at H
      cases hread : read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
      | none =>
          simp only [hread] at H
          by_cases hacc : (!access_okb param 4) = true
          · simp only [ite_eq_left hacc] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          · simp only [ite_eq_right hacc] at H
            rw [← hP]
            simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_right hearly,
              bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_right hacc, unmodeled]
      | some bs =>
          simp only [hread] at H
          by_cases hself : (!sched_targets_self_b pid m) = true
          · simp only [ite_eq_left hself] at H
            rw [← hP]
            simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_right hearly,
              bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_left hself]
            exact record_copyins_unmodeled (unmodeled_intro i m)
          · simp only [ite_eq_right hself] at H
            cases hans : sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
            | none =>
                rw [← hP]
                simp only [sched_setscheduler_spec, ite_eq_right hpolneg, ite_eq_right hearly,
                  bind_inputSpec, getModelSpec, bind_getModel, hread, ite_eq_right hself, hans]
                exact record_copyins_unmodeled (unmodeled_intro i m)
            | some r =>
                simp only [hans] at H
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled [(param, 4)] eff r m [])

set_option linter.constructorNameAsVariable false in
theorem check_sched_setscheduler_complete_ok (i : SyscallInput)
    (pid policy param : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : sched_setscheduler_spec pid policy param i m (.ok eff m' evs)) :
    check_sched_setscheduler i pid policy param eff m = .CheckOk m' evs := by
  generalize hP : (check_sched_setscheduler i pid policy param eff m = .CheckOk m' evs) = Q at *
  simp only [sched_setscheduler_spec] at H
  by_cases hpolneg : sint32 policy < 0
  · simp only [ite_eq_left hpolneg] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_sched_setscheduler, ite_eq_left hpolneg]
    simp [check_ret_only, bv_eqb_refl]
  · simp only [ite_eq_right hpolneg] at H
    by_cases hearly : (w_is0 param || decide (sint32 pid < 0)) = true
    · simp only [ite_eq_left hearly] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      rw [← hP]
      simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_left hearly]
      simp [check_ret_only, bv_eqb_refl]
    · simp only [ite_eq_right hearly] at H
      simp only [bind_inputSpec, getModelSpec, bind_getModel] at H
      cases hread : read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
      | none =>
          simp only [hread] at H
          by_cases hacc : (!access_okb param 4) = true
          · simp only [ite_eq_left hacc] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            rw [← hP]
            simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_right hearly, hread,
              ite_eq_left hacc]
            simp [check_ret_only, bv_eqb_refl]
          · simp only [ite_eq_right hacc] at H
            simp only [unmodeled] at H
            exact nomatch H
      | some bs =>
          simp only [hread] at H
          obtain ⟨core, Hcore, heff⟩ :=
            record_copyins_ok_inv [(param, 4)] _ i m eff m' evs H
          by_cases hself : (!sched_targets_self_b pid m) = true
          · simp only [ite_eq_left hself] at Hcore
            simp only [unmodeled] at Hcore
            exact nomatch Hcore
          · simp only [ite_eq_right hself] at Hcore
            cases hans : sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
            | none =>
                simp only [hans] at Hcore
                simp only [unmodeled] at Hcore
                exact nomatch Hcore
            | some r =>
                simp only [hans] at Hcore
                simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at Hcore
                obtain ⟨hcore, hm', hevs⟩ := Hcore
                rw [← hP]
                rw [heff, hcore, hm', hevs]
                simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_right hearly, hread,
                  ite_eq_right hself, hans]
                exact check_ret_only_copyins_refl [(param, 4)] r m []

set_option linter.constructorNameAsVariable false in
theorem check_sched_setscheduler_complete_unmodeled (i : SyscallInput)
    (pid policy param : word) (eff : SyscallEffect) (m : Model)
    (H : sched_setscheduler_spec pid policy param i m .unmodeled) :
    check_sched_setscheduler i pid policy param eff m = .CheckUnmodeled := by
  generalize hP : (check_sched_setscheduler i pid policy param eff m = .CheckUnmodeled) = Q at *
  simp only [sched_setscheduler_spec] at H
  by_cases hpolneg : sint32 policy < 0
  · simp only [ite_eq_left hpolneg] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · simp only [ite_eq_right hpolneg] at H
    by_cases hearly : (w_is0 param || decide (sint32 pid < 0)) = true
    · simp only [ite_eq_left hearly] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · simp only [ite_eq_right hearly] at H
      simp only [bind_inputSpec, getModelSpec, bind_getModel] at H
      cases hread : read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
      | none =>
          simp only [hread] at H
          by_cases hacc : (!access_okb param 4) = true
          · simp only [ite_eq_left hacc] at H
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · simp only [ite_eq_right hacc] at H
            rw [← hP]
            simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_right hearly, hread,
              ite_eq_right hacc]
      | some bs =>
          simp only [hread] at H
          by_cases hself : (!sched_targets_self_b pid m) = true
          · simp only [ite_eq_left hself] at H
            rw [← hP]
            simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_right hearly, hread,
              ite_eq_left hself]
          · simp only [ite_eq_right hself] at H
            have H' : (match sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                    ((le_bytes_to_word bs).toNat : Int) with
                | some r => ret_only r
                | none => unmodeled) i m .unmodeled :=
              record_copyins_unmodeled_inv [(param, 4)] _ i m H
            cases hans : sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                ((le_bytes_to_word bs).toNat : Int) with
            | none =>
                rw [← hP]
                simp only [check_sched_setscheduler, ite_eq_right hpolneg, ite_eq_right hearly, hread,
                  ite_eq_right hself, hans]
            | some r =>
                simp only [hans] at H'
                simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H'
                exact nomatch H'

/-! ## sched_yield (124) -/

/-- [sched_yield] (124): 0, no writes, no state change, no events, and
    nothing else admitted.  Mirrors
    [Kernel.Sched.Syscalls.sched_yield_spec], which is where the reading
    of [SYSCALL_DEFINE0(sched_yield)] lives — above all why ignoring
    every argument word is exact here rather than an approximation.  The
    arm has no decline at all, which is what the two [_unmodeled]
    obligations below come to. -/
def check_sched_yield (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_ret_only eff (BitVec.ofInt 64 0) m []

theorem check_sched_yield_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_sched_yield eff m = .CheckOk m' evs) :
    sched_yield_spec i m (.ok eff m' evs) := by
  simp only [check_sched_yield] at H
  obtain ⟨rfl, rfl, rfl⟩ :=
    (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
  simp only [sched_yield_spec, ret_only, LinuxSem.LinuxProcessSem.pure]

/-- Vacuously: the checker never declines, so there is no answer to
    carry over.  That is the honest shape for an arm with no
    fail-closed branch — see [check_sched_yield_complete_unmodeled] for
    the direction that has content. -/
theorem check_sched_yield_sound_unmodeled (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_sched_yield eff m = .CheckUnmodeled) :
    sched_yield_spec i m .unmodeled := by
  simp only [check_sched_yield] at H
  exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])

theorem check_sched_yield_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : sched_yield_spec i m (.ok eff m' evs)) :
    check_sched_yield eff m = .CheckOk m' evs := by
  simp only [sched_yield_spec, ret_only, LinuxSem.LinuxProcessSem.pure,
    Outcome.ok.injEq] at H
  obtain ⟨rfl, rfl, rfl⟩ := H
  simp only [check_sched_yield]
  simp [check_ret_only, bv_eqb_refl]

/-- The spec has no [Unmodeled] outcome either, so this side is the one
    that says so: [sched_yield_spec] going unmodeled is impossible, and
    the proof is the impossibility rather than an appeal to the
    checker. -/
theorem check_sched_yield_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : sched_yield_spec i m .unmodeled) :
    check_sched_yield eff m = .CheckUnmodeled := by
  simp only [sched_yield_spec, ret_only, LinuxSem.LinuxProcessSem.pure] at H
  exact nomatch H

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the branch
    order the proofs above follow, one per claim the matching spec's prose
    makes: the malformed-length gate answers -EINVAL before anything else
    is read; a negative policy and a negative pid are -EINVAL at the two
    head gates; and `sched_yield` is the bare `ret_only 0`.

    They are sanity checks, not library lemmas.  `check_result` carries no
    `DecidableEq`, so each states the branch as an equation and closes it
    by unfolding the checker and discharging the branch tests with
    `decide`. -/

/-- A malformed length (3 is not a multiple of 8) is -EINVAL. -/
example (eff : SyscallEffect) (m : Model) :
    check_sched_getaffinity 3 eff m = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_sched_getaffinity, ite_eq_left (by decide : affinity_len_einval_b 3 = true)]

/-- …and a length the gates let through is DECLINED, not answered. -/
example (eff : SyscallEffect) (m : Model) :
    check_sched_getaffinity 8 eff m = .CheckUnmodeled := by
  simp only [check_sched_getaffinity,
    ite_eq_right (by decide : ¬ (affinity_len_einval_b 8 = true))]

/-- A NEGATIVE policy is -EINVAL, before the pid and the pointer. -/
example (i : SyscallInput) (pid param : word) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler i pid (BitVec.ofInt 64 (-1)) param eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  have h : sint32 (BitVec.ofInt 64 (-1)) < 0 := by decide
  simp only [check_sched_setscheduler, ite_eq_left h]

/-- A NEGATIVE pid is -EINVAL at the second gate, policy sign included. -/
example (i : SyscallInput) (param : word) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler i (BitVec.ofInt 64 (-1)) 5 param eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : (w_is0 param || decide (sint32 (BitVec.ofInt 64 (-1)) < 0)) = true := by
    rw [show decide (sint32 (BitVec.ofInt 64 (-1)) < 0) = true from by decide]
    exact Bool.or_true _
  simp only [check_sched_setscheduler, ite_eq_right h1, ite_eq_left h2]

/-- A NULL [param] is -EINVAL, after the policy sign test. -/
example (i : SyscallInput) (pid : word) (eff : SyscallEffect) (m : Model) :
    check_sched_setscheduler i pid 5 0 eff m
      = check_ret_only eff (errno_ret EINVAL) m [] := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : (w_is0 (0 : word) || decide (sint32 pid < 0)) = true := by
    rw [show w_is0 (0 : word) = true from by decide]
    rfl
  simp only [check_sched_setscheduler, ite_eq_right h1, ite_eq_left h2]

/-- `sched_yield` is the bare `ret_only 0`, with no branch at all. -/
example (eff : SyscallEffect) (m : Model) :
    check_sched_yield eff m = check_ret_only eff (BitVec.ofInt 64 0) m [] := rfl

/-- A syscall input whose memory holds a `struct sched_param` at address 4
    — `sched_priority = 0`, little-endian — and nothing else.  Address 4
    and not 0: a zero `param` is the null-pointer gate, a different arm. -/
private def portInput : SyscallInput :=
  { in_sysno := 119, in_args := [],
    in_mem := sanityMem [0, 0, 0, 0, 0, 0, 0, 0], in_wmem := fun _ => none }

/-- A model with no pinned tid: only a zero pid can name the caller. -/
private def portModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A zero pid always names the caller, whatever the model's tid is. -/
private theorem port_self (m : Model) :
    sched_targets_self_b (0 : word) m = true := by
  unfold sched_targets_self_b
  rw [show w_is0 (pid32 (0 : word)) = true from by decide]
  rfl

/-- THE SUCCESS ARM: SCHED_IDLE at priority 0 on the calling task answers
    0, and the four bytes at `param` are on the copy-in ledger. -/
example :
    check_sched_setscheduler portInput 0 5 4
        (with_copyins [(4, 4)] (mkEffect (BitVec.ofInt 64 0) [] [])) portModel
      = .CheckOk portModel [] := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by decide
  have hread : read_bytes_map portInput.in_mem (4 : word) (BitVec.ofInt 64 4)
      = some [0, 0, 0, 0] := by decide
  have hans : sched_setscheduler_answer ((abi_low32 (5 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = some 0 := by decide
  have hself : ¬ ((!sched_targets_self_b (0 : word) portModel) = true) := by
    rw [port_self]
    simp
  simp only [check_sched_setscheduler, ite_eq_right h1, ite_eq_right h2, hread, ite_eq_right hself, hans]
  exact check_ret_only_copyins_refl [(4, 4)] 0 portModel []

/-- A bad policy (4, the unimplemented SCHED_ISO) is -EINVAL, and the
    copy-in IS on the ledger: `copy_from_user` ran before the policy was
    looked at. -/
example :
    check_sched_setscheduler portInput 0 4 4
        (with_copyins [(4, 4)] (mkEffect (errno_ret EINVAL) [] [])) portModel
      = .CheckOk portModel [] := by
  have h1 : ¬ (sint32 (4 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by decide
  have hread : read_bytes_map portInput.in_mem (4 : word) (BitVec.ofInt 64 4)
      = some [0, 0, 0, 0] := by decide
  have hans : sched_setscheduler_answer ((abi_low32 (4 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = some (errno_ret EINVAL) := by
    decide
  have hself : ¬ ((!sched_targets_self_b (0 : word) portModel) = true) := by
    rw [port_self]
    simp
  simp only [check_sched_setscheduler, ite_eq_right h1, ite_eq_right h2, hread, ite_eq_right hself, hans]
  exact check_ret_only_copyins_refl [(4, 4)] (errno_ret EINVAL) portModel []

/-- A NONZERO pid that is not the caller is DECLINED, with the copy-in
    still recorded — the ledger rides on every path past the read. -/
example :
    check_sched_setscheduler portInput 7 5 4
        (with_copyins [(4, 4)] (mkEffect (BitVec.ofInt 64 0) [] [])) portModel
      = .CheckUnmodeled := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (7 : word) < 0)) = true) := by decide
  have hread : read_bytes_map portInput.in_mem (4 : word) (BitVec.ofInt 64 4)
      = some [0, 0, 0, 0] := by decide
  have hself : (!sched_targets_self_b (7 : word) portModel) = true := by
    unfold sched_targets_self_b
    rw [show w_is0 (pid32 (7 : word)) = false from by decide]
    rfl
  simp only [check_sched_setscheduler, ite_eq_right h1, ite_eq_right h2, hread, ite_eq_left hself]

end LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
