/-
  * LinuxSem.Checks.ExecutableSpecs — verified executable acceptors for each syscall

  Representation: syscall inputs/returns are `word = BitVec 64`,
  buffer bytes are `byte = BitVec 8`, errnos are `Int`, and length/bound
  comparisons happen in `Int` over unsigned values, mirroring `Specs.lean`
  exactly.  `bytes_ok` / `Forall (b < 256)` checker conditions are
  unnecessary — they are enforced by the `byte` type.

  The relational specs in `Specs.lean` are the TRUSTED semantics; they are
  not executable (non-determinism is set-valued).  For conformance
  testing against real Linux we need a runnable acceptor: given the
  syscall's input, the OBSERVED effect (return value + captured output
  buffers), and the model
  state, decide whether the observation is admissible.

  `check_syscall` decides the syscall body and returns:
  - `CheckOk m' evs` — admissible; the model steps to `m'` emitting `evs`;
  - `CheckUnmodeled` — the spec relation says `unmodeled` (unmodeled syscall
                        number / unmodeled use of a modeled syscall /
                        invalid user buffer); independent of the observed
                        effect;
  - `CheckReject`    — the observed effect is NOT admissible: the real
                       kernel did something the model forbids (a
                       conformance failure).

  VERIFICATION (below): the checker is proved sound AND complete
  against the relational specs —
    `check_syscall i eff m = CheckOk m' evs  ↔  syscall_spec i m (ok eff m' evs)`
    `check_syscall i eff m = CheckUnmodeled  ↔  syscall_spec i m unmodeled`
  so `CheckReject` means exactly "no admissible outcome has this effect".

  The public entry point `check_syscall_for_run` then applies the
  same atomic first-touch accounting as `Run.sstep.syscall` to a successful
  post-model.  Its OUTER `none` is the modeled error transition for a
  backing-limit failure, kept distinct from both checker rejection and
  unmodeled behavior.  That "same as `Run.sstep.syscall`" cannot be a
  theorem HERE — this file does not import `Run` — so `Checks/Examples.lean`
  proves it, reading each outcome back as the transition it stands for.
  These proofs are QA on the checker, not part of the trust story: the spec
  stays the definition.

  Placement.  `Checks/Sys/Dispatch.lean` §3 proves `check_syscall` and the
  four soundness/completeness results for an ARBITRARY table (with the
  table/spec-surface agreement as an explicit argument), and §4 holds the
  `checked_table` instances in `namespace CheckedTable`, under the same
  names.  That placement is forced by the direction of the dependencies:
  this file and `Checks/Progress.lean` take `Dispatch.lean` for the table
  and the generic proofs, so the reverse dependency is impossible, and the
  §3 versions already hold the unqualified names.  This file therefore
  restates them under the plain names and statements, in the
  `ExecutableSpecs` namespace (distinct from `CheckedTable`, so nothing
  clashes): `check_syscall` is the `CheckedTable` definition and each of
  the four proofs is one line handing over to the `CheckedTable` result.
  Nothing is reproved and nothing here grows when a syscall is added.

  What is NEW here, because `Dispatch.lean` has no reason to hold it, is the
  run boundary: `syscall_post_model`, `check_syscall_for_run`, the two
  post-model lemmas and the four `check_syscall_for_run_*` results.  Those
  carry real proofs.

  Spelling.  `option check_result` is `Option check_result`,
  `Ok` / `Unmodeled` are `.ok` / `.unmodeled`, `Some` / `None` on the
  option are `some` / `none`, and `syscall_spec` is `Specs.syscall_spec`.
  In `Run.lean`, `sstep_syscall` and
  `sstep_syscall_materialization_fault` are the constructors
  `sstep.syscall` and `sstep.syscall_materialization_fault` of the
  inductive `sstep`, and `sstep_exit` — the halted model
  that stays unchanged — is `sstep.exit`.  `destruct … eqn:` is
  `cases … :`; `discriminate` is `cases` on the impossible equation, and
  `inversion H; subst` is `simp only [… , Option.some.injEq,
  check_result.CheckOk.injEq] at H` followed by `obtain ⟨rfl, rfl⟩ := H`.
  The checked/witness modules are reached transitively
  through `Checks.Sys.Dispatch`, which names exactly that set.
-/
import LinuxSem.Checks.Sys.Dispatch

namespace LinuxSem.Checks.ExecutableSpecs

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs (syscall_spec)
-- `check_result` is `Checks.Sys.Prelude`'s inductive; it is only opened for
-- the two definitions and two theorems whose signatures name it.
open LinuxSem.Checks.Sys.Prelude (check_result)
-- The checked table, and through it `CheckedTable.check_syscall` and the
-- five concrete theorems.  Every use below is written with the
-- `CheckedTable.` prefix: the generic §3 names (`check_syscall`,
-- `check_syscall_sound_ok`, …) come along with this `open`, and the
-- restatements in this file must not be confused with them.
open LinuxSem.Checks.Sys.Dispatch

/- =========================================================================
   §1  The public checker, and the run boundary
   ========================================================================= -/

/-- Dispatch on the syscall number, through the one table the relational
    spec dispatches over as well.  The two cannot disagree about which
    numbers are modeled, because they read the same list.

    The body is the arm match itself; it is `CheckedTable`'s
    definition, which is `Dispatch.check_syscall checked_table`:

      `match lookup_ca checked_table (i.in_sysno.toNat : Int) with`
      `| some c => c.ca_check i eff m`
      `| none   => .CheckUnmodeled`

    Restated here so the name reads at this module. -/
def check_syscall (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_result :=
  CheckedTable.check_syscall i eff m

/-- Postprocess the relational syscall post-model exactly as the run does.
    A halted model is `sstep.exit` and stays unchanged.  A running model
    is one of `sstep.syscall` / `sstep.syscall_materialization_fault`,
    decided by the same shared access aggregation and atomic materializer. -/
def syscall_post_model (m : Model) (eff : SyscallEffect) :
    Option Model :=
  match m_halted m with
  | some _ => some m
  | none => materialize_model_accesses m (syscall_effect_accesses eff)

/-- Public conformance-checker boundary.  The outer option is the run's
    error-transition boundary: `none` exposes no partially updated model and
    is deliberately not conflated with either `CheckReject` or
    `CheckUnmodeled`. -/
def check_syscall_for_run (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : Option check_result :=
  match check_syscall i eff m with
  | .CheckOk m' evs =>
      match syscall_post_model m' eff with
      | some m'' => some (.CheckOk m'' evs)
      | none => none
  | .CheckReject => some .CheckReject
  | .CheckUnmodeled => some .CheckUnmodeled

/- =========================================================================
   Verification: the checker is sound and complete for the relational specs
   ========================================================================= -/

-- Section marker kept so the section boundaries line up.  Nothing
-- prlimit64-specific follows it: the statement it used to head is now the
-- general `check_syscall` result below.
/- --------------------------------------------------------- prlimit64 -/

/-- `lookup_ca_arm` is what lets a goal about `Specs.syscall_spec` — which
    dispatches over `spec_table` — be closed by a `CheckedArm`'s field: the
    two tables are the same surface (`checked_table_arms`).  Both sides of
    every theorem below therefore turn on the SAME lookup, so each one is a
    destruct and a field.

    None of the four mentions a syscall, and none of them grows when one is
    added. -/

theorem check_syscall_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_syscall i eff m = .CheckOk m' evs) :
    syscall_spec i m (.ok eff m' evs) :=
  CheckedTable.check_syscall_sound_ok i eff m m' evs H

theorem check_syscall_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) (H : check_syscall i eff m = .CheckUnmodeled) :
    syscall_spec i m .unmodeled :=
  CheckedTable.check_syscall_sound_unmodeled i eff m H

theorem check_syscall_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : syscall_spec i m (.ok eff m' evs)) :
    check_syscall i eff m = .CheckOk m' evs :=
  CheckedTable.check_syscall_complete_ok i eff m m' evs H

theorem check_syscall_complete_unmodeled (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (H : syscall_spec i m .unmodeled) :
    check_syscall i eff m = .CheckUnmodeled :=
  CheckedTable.check_syscall_complete_unmodeled i m eff H

theorem check_syscall_ok_iff (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    check_syscall i eff m = .CheckOk m' evs ↔ syscall_spec i m (.ok eff m' evs) :=
  CheckedTable.check_syscall_ok_iff i eff m m' evs

theorem check_syscall_err_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = .CheckUnmodeled ↔ syscall_spec i m .unmodeled :=
  CheckedTable.check_syscall_err_iff i eff m

/- =========================================================================
   Verification: the public checker, against the relational spec

   These four cover `Option check_result` exhaustively.  They are stated
   against `syscall_spec` and `syscall_post_model` rather than against
   `Run.sstep`, because this file does not import `Run`;
   `Checks.Examples.checker_ok_is_run_step` and its two companions close
   that last step.
   ========================================================================= -/

theorem syscall_post_model_running (m : Model) (eff : SyscallEffect)
    (H : m_halted m = none) :
    syscall_post_model m eff =
      materialize_model_accesses m (syscall_effect_accesses eff) := by
  simp [syscall_post_model, H]

theorem syscall_post_model_halted (m : Model) (eff : SyscallEffect) (code : word)
    (H : m_halted m = some code) : syscall_post_model m eff = some m := by
  simp [syscall_post_model, H]

/-- A public-checker success contains exactly a relational syscall outcome
    followed by the post-model premise shared with the run constructors. -/
theorem check_syscall_for_run_ok_iff (i : SyscallInput) (eff : SyscallEffect)
    (m m'' : Model) (evs : List event) :
    check_syscall_for_run i eff m = some (.CheckOk m'' evs) ↔
      ∃ m', syscall_spec i m (.ok eff m' evs) ∧ syscall_post_model m' eff = some m'' := by
  constructor
  · intro H
    cases hck : check_syscall i eff m with
    | CheckOk m' evs' =>
      cases hpost : syscall_post_model m' eff with
      | none =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
      | some macc =>
        have hH : (.CheckOk macc evs' : check_result) = .CheckOk m'' evs := by
          simpa only [check_syscall_for_run, hck, hpost, Option.some.injEq] using H
        obtain ⟨rfl, rfl⟩ := check_result.CheckOk.inj hH
        exact ⟨m', CheckedTable.check_syscall_sound_ok i eff m m' evs' hck, hpost⟩
    | CheckReject =>
      simp only [check_syscall_for_run, hck] at H
      cases H
    | CheckUnmodeled =>
      simp only [check_syscall_for_run, hck] at H
      cases H
  · rintro ⟨m', hspec, hpost⟩
    simp only [check_syscall_for_run, check_syscall,
      CheckedTable.check_syscall_complete_ok i eff m m' evs hspec, hpost]

/-- The outer `none` is exactly the non-halting materialization-fault premise
    of `sstep.syscall_materialization_fault`. -/
theorem check_syscall_for_run_fault_iff (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    check_syscall_for_run i eff m = none ↔
      ∃ m' evs,
        syscall_spec i m (.ok eff m' evs) ∧
        m_halted m' = none ∧
        materialize_model_accesses m' (syscall_effect_accesses eff) = none := by
  constructor
  · intro H
    cases hck : check_syscall i eff m with
    | CheckOk m' evs =>
      cases hpost : syscall_post_model m' eff with
      | none =>
        cases hhalt : m_halted m' with
        | some code =>
          rw [syscall_post_model_halted m' eff code hhalt] at hpost
          cases hpost
        | none =>
          have hmat : materialize_model_accesses m' (syscall_effect_accesses eff) = none := by
            rw [← syscall_post_model_running m' eff hhalt]
            exact hpost
          exact ⟨m', evs, CheckedTable.check_syscall_sound_ok i eff m m' evs hck, hhalt, hmat⟩
      | some macc =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
    | CheckReject =>
      simp only [check_syscall_for_run, hck] at H
      cases H
    | CheckUnmodeled =>
      simp only [check_syscall_for_run, hck] at H
      cases H
  · rintro ⟨m', evs, hspec, hhalt, hmat⟩
    simp only [check_syscall_for_run, check_syscall,
      CheckedTable.check_syscall_complete_ok i eff m m' evs hspec,
      syscall_post_model_running m' eff hhalt, hmat]

/-- Raw rejection stays raw rejection; accounting faults use the outer
    `none` and cannot reach this result. -/
theorem check_syscall_for_run_reject_iff (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    check_syscall_for_run i eff m = some .CheckReject ↔
      check_syscall i eff m = .CheckReject := by
  constructor
  · intro H
    cases hck : check_syscall i eff m with
    | CheckOk m' evs =>
      cases hpost : syscall_post_model m' eff with
      | none =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
      | some m'' =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
    | CheckReject => rfl
    | CheckUnmodeled =>
      simp only [check_syscall_for_run, hck] at H
      cases H
  · intro H
    simp only [check_syscall_for_run, H]

/-- Fail-closed syscall outcomes pass through the run adapter unchanged. -/
theorem check_syscall_for_run_unmodeled_iff (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) :
    check_syscall_for_run i eff m = some .CheckUnmodeled ↔ syscall_spec i m .unmodeled := by
  constructor
  · intro H
    cases hck : check_syscall i eff m with
    | CheckUnmodeled =>
      exact CheckedTable.check_syscall_sound_unmodeled i eff m hck
    | CheckOk m' evs =>
      cases hpost : syscall_post_model m' eff with
      | none =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
      | some m'' =>
        simp only [check_syscall_for_run, hck, hpost] at H
        cases H
    | CheckReject =>
      simp only [check_syscall_for_run, hck] at H
      cases H
  · intro Hspec
    simp only [check_syscall_for_run, check_syscall,
      CheckedTable.check_syscall_complete_unmodeled i m eff Hspec]

/-! ## Sanity checks

    Beyond the minimum: the checker's own answers are
    pinned by the arms' checks in `Dispatch.lean`.  These pin the RUN
    ADAPTER's shape — the three pass-throughs and the accounting step —
    because the adapter is the part of this file that is new. -/

/-- A raw rejection passes through the adapter unchanged. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_syscall i eff m = .CheckReject) :
    check_syscall_for_run i eff m = some .CheckReject := by
  simp only [check_syscall_for_run, h]

/-- And so does a fail-closed `unmodeled` answer. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : check_syscall i eff m = .CheckUnmodeled) :
    check_syscall_for_run i eff m = some .CheckUnmodeled := by
  simp only [check_syscall_for_run, h]

/-- An accepted effect with no post-model is the outer `none` — the
    materialization fault, not a rejection. -/
example (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h : check_syscall i eff m = .CheckOk m' evs)
    (hpost : syscall_post_model m' eff = none) :
    check_syscall_for_run i eff m = none := by
  simp only [check_syscall_for_run, h, hpost]

/-- An accepted effect with a post-model hands back the accounted model. -/
example (i : SyscallInput) (eff : SyscallEffect) (m m' m'' : Model) (evs : List event)
    (h : check_syscall i eff m = .CheckOk m' evs)
    (hpost : syscall_post_model m' eff = some m'') :
    check_syscall_for_run i eff m = some (.CheckOk m'' evs) := by
  simp only [check_syscall_for_run, h, hpost]

end LinuxSem.Checks.ExecutableSpecs
