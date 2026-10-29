/-
  * LinuxProcessSem.Sys.Dispatch — a syscall as a value, and the dispatcher
    over them.

  Every other file under `Sys/` answers to one kernel SOURCE file; this one
  answers to none, like `Syscall`, `Uapi` and `Uaccess`.  It is the
  mechanism a number reaches a spec by — what `arch/riscv/kernel/traps.c`
  does with `regs->a7` before the table is consulted.

  TRUST BOUNDARY: this file is part of the trusted specification.

  An arm is a value: its number and what it admits.  Dispatch is a lookup
  in a list, so the dispatcher is written once and does not grow, and adding
  a syscall is one entry in one list.
-/
import LinuxSem.LinuxProcessSem.MonadInstances

namespace LinuxSem.LinuxProcessSem.Sys.Dispatch

open LinuxSem.LinuxProcessSem

/-- One modeled syscall: the number it answers to, and the effects it
    admits given the raw `SyscallInput`.  The arm reads its own arguments
    out of the input rather than being handed them, which is what lets one
    lookup serve every syscall whatever its arity. -/
structure SpecArm where
  sa_no : Int
  sa_spec : SysSpec SyscallEffect

/-- The first arm answering to `n`, if any.  A `none` is the fail-closed
    case and there is exactly one of it. -/
def lookup_arm : List SpecArm → Int → Option SpecArm
  | [], _ => none
  | a :: r, n => if a.sa_no == n then some a else lookup_arm r n

/-- Dispatch: the arm for this input's syscall number, or `unmodeled`.

    FAIL CLOSED, in one place.  A number with no arm yields `unmodeled`. -/
def dispatch (t : List SpecArm) : SysSpec SyscallEffect :=
  fun i m o =>
    match lookup_arm t (i.in_sysno.toNat : Int) with
    | some a => a.sa_spec i m o
    | none => unmodeled i m o

/-- The numbers a table covers, in the table's order. -/
def arm_numbers (t : List SpecArm) : List Int := t.map SpecArm.sa_no

/-- A number the table does not carry is declined. -/
theorem dispatch_unmodeled (t : List SpecArm) (i : SyscallInput) (m : Model)
    (h : lookup_arm t (i.in_sysno.toNat : Int) = none) :
    dispatch t i m .unmodeled := by
  unfold dispatch
  rw [h]
  exact unmodeled_intro i m

/-- And a number it does carry is answered by that arm, both ways. -/
theorem dispatch_arm (t : List SpecArm) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (a : SpecArm)
    (h : lookup_arm t (i.in_sysno.toNat : Int) = some a) :
    dispatch t i m o ↔ a.sa_spec i m o := by
  unfold dispatch
  rw [h]

end LinuxSem.LinuxProcessSem.Sys.Dispatch
