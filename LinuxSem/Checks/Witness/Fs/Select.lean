/-
  * LinuxProcessSem.Checks.Witness.Fs.Select — the pselect6 (72) and ppoll (73) witnesses, and their proofs

  Answers to Linux [fs/select.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  Each proof peels the spec's two fixed steps with `bind_step` from
  `Checks.Witness.Prelude` — `inputSpec` and `getModelSpec` are
  definitionally `.ok _ _ []`, so `rfl` discharges their premise — and
  reduces with `dsimp only`.  The final split is `cases` on the generalized
  outcome, which reduces the `match` in both the spec and the witness; a
  closed branch test is discharged by `decide`.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Select

namespace LinuxSem.Checks.Witness.Fs.Select

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Select
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   pselect6 (72)
   ========================================================================= -/

/-- pselect6 witness: the single outcome [Select.pselect6_outcome] names,
    or [Unmodeled] where it declines (fail closed, but never stuck). -/
def pselect6_witness (i : SyscallInput) (m : Model)
    (n32 inp outp exp tsp sig : word) : Outcome SyscallEffect Model event :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => .unmodeled
  | some (r, ws) => .ok (mkEffect r ws []) m []

theorem pselect6_witness_ok (n32 inp outp exp tsp sig : word) (i : SyscallInput)
    (m : Model) :
    pselect6_spec n32 inp outp exp tsp sig i m
      (pselect6_witness i m n32 inp outp exp tsp sig) := by
  unfold pselect6_spec pselect6_witness
  refine bind_step inputSpec _ i m i m _ rfl ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  generalize hdef : pselect6_outcome i m n32 inp outp exp tsp sig = out at ⊢
  cases out with
  | none => exact unmodeled_intro _ _
  | some p =>
    obtain ⟨r, ws⟩ := p
    exact pure_ok _ _ _

/- =========================================================================
   ppoll (73)
   ========================================================================= -/

/-- ppoll witness: the single outcome [Select.ppoll_outcome] names, or
    [Unmodeled] where it declines (fail closed, but never stuck). -/
def ppoll_witness (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) : Outcome SyscallEffect Model event :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => .unmodeled
  | some (r, ws) => .ok (mkEffect r ws []) m []

theorem ppoll_witness_ok (ufds nfds tsp sig sigsetsize : word) (i : SyscallInput)
    (m : Model) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m
      (ppoll_witness i m ufds nfds tsp sig sigsetsize) := by
  unfold ppoll_spec ppoll_witness
  refine bind_step inputSpec _ i m i m _ rfl ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  generalize hdef : ppoll_outcome i m ufds nfds tsp sig sigsetsize = out at ⊢
  cases out with
  | none => exact unmodeled_intro _ _
  | some p =>
    obtain ⟨r, ws⟩ := p
    exact pure_ok _ _ _

end LinuxSem.Checks.Witness.Fs.Select
