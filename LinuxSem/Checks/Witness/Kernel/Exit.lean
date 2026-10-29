/-
  * LinuxProcessSem.Checks.Witness.Kernel.Exit — the exit (93), exit_group (94), wait4 (260) witnesses, and their proofs

  Answers to Linux [kernel/exit.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` is `Checks/Witness/Prelude.lean`'s helper,
  the "return `r`, change nothing, emit nothing" outcome.

  [wait4_witness] takes the [SyscallInput] and never reads it — the same
  is true of [wait4_spec], whose only environment-reading step is a
  [get_model] — so the Lean unused-variable linter is switched off for the
  declaration rather than the parameter being dropped, which keeps the
  signature the spec's.

  A proof steps the spec's leading `get_model` with `bind_getModel`, one
  rewrite, and builds the continuation with `bind_step`.

  `wait4_spec` is a `SysSpec`, a FUNCTION, so its body is an `if` at
  function type (`(if … then unmodeled else …) i m o`); `whnf` on a goal
  that mentions it tries to reduce that `if`, which means deciding
  `!((upid.toNat : Int) == WAIT_ANY32)` on an opaque word, and `by_cases`
  normalises its goal.  Each proof therefore `generalize`s its conclusion
  into a local `Q : Prop` first, splits against `Q` (opaque, so no
  reduction happens), and only then rewrites `Q` back into the spec and
  discharges the branch with `simp only`.  See
  `Checks/Sys/Kernel/Groups.lean` for the same pattern at length.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Exit

namespace LinuxSem.Checks.Witness.Kernel.Exit

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.Checks.Witness.Prelude

/-! ## exit (93) and exit_group (94) -/

/-- [exit] answers 0 and halts with the LOW BYTE of the status — the
    whole of what [Kernel.Exit.exit_spec] does, so the witness is the
    spec's single step, not a choice. -/
def exit_witness (code : word) (m : Model) : Outcome SyscallEffect Model event :=
  ret_outcome (BitVec.ofInt 64 0) (with_halted (code &&& BitVec.ofInt 64 255) m)

theorem exit_witness_ok (code : word) (i : SyscallInput) (m : Model) :
    exit_spec code i m (exit_witness code m) := by
  exact ⟨(), with_halted (code &&& BitVec.ofInt 64 255) m, [], [], rfl, rfl, rfl⟩

/- =========================================================================
   set_tid_address (96) / ioctl (29)
   ========================================================================= -/

/- `set_tid_address` witness: the pinned tid if one is recorded; on the
   first call the environment pins the valid identity 1.

   (A comment, not a declaration: the witness itself lives in the file
   that holds `Fork`'s witnesses.) -/

/- =========================================================================
   wait4 (260) — witness: -ECHILD, the one answer a modeled call admits.
   ========================================================================= -/

set_option linter.unusedVariables false in
/-- [wait4] is deterministic on every branch, so the witness is the
    branch itself: the fail-closed [Unmodeled] at each of the three
    argument guards and at the [m_has_children] gate, and -ECHILD for
    the childless caller the spec answers.  Failing closed is an
    admissible outcome, which is what makes progress hold on the
    declined shapes. -/
def wait4_witness (upid stat_addr options rusage : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !((upid.toNat : Int) == WAIT_ANY32) then .unmodeled
  else if !((options.toNat : Int) == WNOHANG) then .unmodeled
  else if !(w_is0 rusage) then .unmodeled
  else if m_has_children m then .unmodeled
  else ret_outcome (errno_ret ECHILD) m

theorem wait4_witness_ok (upid stat_addr options rusage : word) (i : SyscallInput)
    (m : Model) :
    wait4_spec upid stat_addr options rusage i m
      (wait4_witness upid stat_addr options rusage i m) := by
  generalize hP :
    (wait4_spec upid stat_addr options rusage i m
      (wait4_witness upid stat_addr options rusage i m)) = Q at *
  by_cases h1 : (!((upid.toNat : Int) == WAIT_ANY32)) = true
  · rw [← hP]
    simp only [wait4_spec, ite_eq_left h1, wait4_witness, unmodeled]
  · by_cases h2 : (!((options.toNat : Int) == WNOHANG)) = true
    · rw [← hP]
      simp only [wait4_spec, ite_eq_right h1, ite_eq_left h2, wait4_witness, unmodeled]
    · by_cases h3 : (!(w_is0 rusage)) = true
      · rw [← hP]
        simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, wait4_witness, unmodeled]
      · by_cases h4 : m_has_children m = true
        · rw [← hP]
          simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, getModelSpec,
            bind_getModel, ite_eq_left h4, wait4_witness, unmodeled]
        · rw [← hP]
          simp only [wait4_spec, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, getModelSpec,
            bind_getModel, ite_eq_right h4, wait4_witness, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure, ret_outcome]

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the two
    computable definitions above against the prose: the `exit` witness is
    `ret_outcome 0` on the halted model; a `wait4` guard failure makes the
    witness the fail-closed `Unmodeled`; and the childless caller gets the
    -ECHILD `ret_outcome` the spec answers. -/

/-- A model whose process has no child — `mkModel`'s default, which is the
    one state `wait4` answers. -/
private def port_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- The `exit` witness is exactly the spec's one step: return 0, halt at
    the LOW BYTE of `code`. -/
example (code : word) (m : Model) :
    exit_witness code m
      = ret_outcome (BitVec.ofInt 64 0)
          (with_halted (code &&& BitVec.ofInt 64 255) m) := rfl

/-- A guard failure makes the witness the fail-closed `Unmodeled` — the
    admissible outcome progress needs on the declined shapes. -/
example (i : SyscallInput) (m : Model) :
    wait4_witness 0 0 0 0 i m = .unmodeled := by
  simp only [wait4_witness]
  rw [ite_eq_left (by decide)]

/-- The childless caller gets -ECHILD, changing nothing. -/
example (i : SyscallInput) :
    wait4_witness (BitVec.ofInt 64 4294967295) 0 (BitVec.ofInt 64 1) 0 i
        port_model
      = ret_outcome (errno_ret ECHILD) port_model := by
  simp only [wait4_witness]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

end LinuxSem.Checks.Witness.Kernel.Exit
