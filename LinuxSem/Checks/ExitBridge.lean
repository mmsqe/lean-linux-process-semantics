/-
  * LinuxSem.Checks.ExitBridge — accepting and rejecting
    witnesses for the exit common artifact

  The exit bridge relates two local denotations to shared syntax, not to
  Linux. These accepting and rejecting witnesses pin the semantic mistakes
  a common artifact or its interpreter could otherwise hide.

  Spelling.  `outcome SyscallEffect` is
  `Outcome SyscallEffect Model event`; `in_sysno` and `in_arg` keep their
  names, and `mkInput` is the structure's constructor
  `SyscallInput.mkInput`.  Lean namespaces constructors under their type,
  so `halt` / `decline` are `Clause.halt` / `Clause.decline`
  here.  `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_and` is `&&&`,
  `bv_unsigned w` is `(w.toNat : Int)`, `option_map f` is `Option.map f`,
  `Ok` / `Unmodeled` are `.ok` / `.unmodeled`, and the artifact
  vocabulary's `PrimString.string` is Lean's `String`.  `rewrite E`
  is `rw [E]` and `reflexivity` is `rfl`.  A closed computation
  is `decide`, except where the goal reduces through a non-instance
  definition (`input255`, `in_arg`, `serialize`, `read_artifact`), which
  the `decide` reducer does not see through: there the same computation is
  done by `simp only [...]` and the result closed by `decide`.  Finally,
  computing in a hypothesis (`… in H`) followed by `discriminate` is a
  `simp` that computes the two sides followed by `decide` on the closed
  equation it leaves.

  The `Clause`, `denote`, `evaluate`, `exit_clause`, `read_artifact` and
  `exit_dispatch_normal_form` this file speaks about are
  `LinuxProcessSem.Bridge.Exit`'s; nothing here restates them.
-/
import LinuxSem.LinuxProcessSem.Bridge.Exit

namespace LinuxSem.Checks.ExitBridge

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Syscall

def input255 : SyscallInput :=
  SyscallInput.mkInput (BitVec.ofInt 64 93)
    [BitVec.ofInt 64 255, BitVec.ofInt 64 7]
    (fun _ => none) (fun _ => none)

theorem input255_exit : exit_number input255.in_sysno := by
  left
  rfl

theorem correct_answer_accepted (m : Model) :
    syscall_spec input255 m (evaluate exit_clause input255 m) :=
  (exit_dispatch_normal_form input255 m (evaluate exit_clause input255 m)
    input255_exit).mpr rfl

def group_input255 : SyscallInput :=
  SyscallInput.mkInput (BitVec.ofInt 64 94)
    [BitVec.ofInt 64 255, BitVec.ofInt 64 7]
    (fun _ => none) (fun _ => none)

theorem group_input255_exit : exit_number group_input255.in_sysno := by
  right
  rfl

theorem group_answer_accepted (m : Model) :
    syscall_spec group_input255 m (evaluate exit_clause group_input255 m) :=
  (exit_dispatch_normal_form group_input255 m (evaluate exit_clause group_input255 m)
    group_input255_exit).mpr rfl

def halted (o : Outcome SyscallEffect Model event) : Option word :=
  match o with
  | .ok _ m _ => m_halted m
  | .unmodeled => none

def returned (o : Outcome SyscallEffect Model event) : Option word :=
  match o with
  | .ok eff _ _ => some eff.eff_ret
  | .unmodeled => none

def wide_input : SyscallInput :=
  SyscallInput.mkInput (BitVec.ofInt 64 93) [BitVec.ofInt 64 0x1ff]
    (fun _ => none) (fun _ => none)

theorem wide_input_exit : exit_number wide_input.in_sysno := by
  left
  rfl

theorem wide_status_accepted (m : Model) :
    syscall_spec wide_input m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (BitVec.ofInt 64 255) m) []) := by
  apply (exit_dispatch_normal_form wide_input m _ wide_input_exit).mpr
  unfold evaluate exit_clause
  -- `change` is spelled `show` here, and the constructor is
  -- spelled `Outcome.ok` because its type is not otherwise determined.
  show (Outcome.ok (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_halted (BitVec.ofInt 64 255) m) [])
    = (Outcome.ok (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_halted ((BitVec.ofInt 64 0x1ff) &&& (BitVec.ofInt 64 255)) m) [])
  have Hmask : ((BitVec.ofInt 64 0x1ff : word) &&& (BitVec.ofInt 64 255 : word))
      = BitVec.ofInt 64 255 := by decide
  rw [Hmask]

theorem unmasked_wide_status_rejected (m : Model) :
    ¬ syscall_spec wide_input m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_halted (BitVec.ofInt 64 0x1ff) m) []) := by
  intro H
  have H' := (exit_dispatch_normal_form wide_input m _ wide_input_exit).mp H
  have h3 := congrArg (fun o => Option.map (fun w : word => (w.toNat : Int)) (halted o))
    H'
  simp only [halted, evaluate, exit_clause, in_arg, wide_input, Option.map_some,
    m_halted_with_halted] at h3
  exact absurd (Option.some.inj h3) (by decide)

theorem wrong_mask_rejected (m : Model) :
    ¬ syscall_spec input255 m
      (evaluate (Clause.halt (BitVec.ofInt 8 0) (BitVec.ofInt 8 127)
        (BitVec.ofInt 8 0)) input255 m) := by
  intro H
  have H' := (exit_dispatch_normal_form input255 m _ input255_exit).mp H
  have h3 := congrArg (fun o => Option.map (fun w : word => (w.toNat : Int)) (halted o))
    H'
  simp only [halted, evaluate, exit_clause, in_arg, input255, Option.map_some,
    m_halted_with_halted] at h3
  exact absurd (Option.some.inj h3) (by decide)

theorem wrong_argument_rejected (m : Model) :
    ¬ syscall_spec input255 m
      (evaluate (Clause.halt (BitVec.ofInt 8 1) (BitVec.ofInt 8 255)
        (BitVec.ofInt 8 0)) input255 m) := by
  intro H
  have H' := (exit_dispatch_normal_form input255 m _ input255_exit).mp H
  have h3 := congrArg (fun o => Option.map (fun w : word => (w.toNat : Int)) (halted o))
    H'
  simp only [halted, evaluate, exit_clause, in_arg, input255, Option.map_some,
    m_halted_with_halted] at h3
  exact absurd (Option.some.inj h3) (by decide)

theorem wrong_return_rejected (m : Model) :
    ¬ syscall_spec input255 m
      (evaluate (Clause.halt (BitVec.ofInt 8 0) (BitVec.ofInt 8 255)
        (BitVec.ofInt 8 1)) input255 m) := by
  intro H
  have H' := (exit_dispatch_normal_form input255 m _ input255_exit).mp H
  have h3 := congrArg (fun o => Option.map (fun w : word => (w.toNat : Int)) (returned o))
    H'
  simp only [returned, evaluate, exit_clause, in_arg, input255, Option.map_some] at h3
  exact absurd (Option.some.inj h3) (by decide)

theorem unmodeled_rejected (m : Model) : ¬ syscall_spec input255 m .unmodeled := by
  intro H
  have H' := (exit_dispatch_normal_form input255 m _ input255_exit).mp H
  simp only [evaluate, exit_clause] at H'
  exact nomatch H'

theorem decline_unmodeled_accepted (i : SyscallInput) (m : Model) :
    denote Clause.decline i m .unmodeled := by
  simp only [denote, unmodeled]

theorem decline_success_rejected (i : SyscallInput) (m : Model) :
    ¬ denote Clause.decline i m (evaluate exit_clause i m) := by
  intro H
  simp only [denote, evaluate, exit_clause] at H
  exact nomatch H

theorem wrong_mask_has_different_serialization :
    serialize (Clause.halt (BitVec.ofInt 8 0) (BitVec.ofInt 8 127)
        (BitVec.ofInt 8 0)) ≠
      serialize exit_clause := by
  simp only [serialize, exit_clause]
  decide

theorem decline_decoded : read_artifact "01" = some Clause.decline := by
  decide

theorem unknown_tag_rejected : read_artifact "02" = none := by
  decide

theorem wrong_arity_rejected : read_artifact "00" = none := by
  decide

theorem odd_length_rejected : read_artifact "0000ff0" = none := by
  decide

theorem trailing_byte_rejected : read_artifact "0000ff0000" = none := by
  decide

theorem invalid_hex_rejected : read_artifact "0000gg00" = none := by
  decide

theorem high_status_normalized :
    (((BitVec.ofInt 64 0x1000001ff : word) &&& (BitVec.ofInt 64 255 : word)).toNat : Int)
      = 255 := by
  decide

theorem full_status_rejected :
    (((BitVec.ofInt 64 0x1000001ff : word) &&& (BitVec.ofInt 64 255 : word)).toNat : Int)
      ≠ 0x1000001ff := by
  decide

theorem seven_bit_remainder_rejected :
    (((BitVec.ofInt 64 255 : word) &&& (BitVec.ofInt 64 255 : word)).toNat : Int)
      ≠ ((BitVec.ofInt 64 255 : word).toNat : Int) % 128 := by
  decide

end LinuxSem.Checks.ExitBridge
