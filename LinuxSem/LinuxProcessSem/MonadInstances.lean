/-
  * MonadInstances — the specification monad at the concrete types.

  `Monad.lean` defines `Sys` generically over the state/input/event types,
  so it does not depend on `State.lean`; the concrete instance is fixed
  below at `Model`/`SyscallInput`/`event`.

      Definition Sys (A : Type) := SyscallInput -> Model -> outcome A -> Prop

  up to argument order (`Sys Model SyscallInput event A`).  Everything
  downstream (`Sys/*.v`) should use `SysSpec`, not the bare `Sys`.

  This retires the parameterisation note in: the monad laws
  proved in `Monad.lean` are the same theorems, at the same types.
-/
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.State

namespace LinuxSem.LinuxProcessSem

open LinuxSem.Riscv

/-- `LinuxProcessSem.Monad.Sys A`, at the concrete state. -/
abbrev SysSpec (A : Type) : Type := Sys Model SyscallInput event A

/-- The current syscall input. -/
def inputSpec : SysSpec SyscallInput := input

/-- The syscall number (`a7` at ecall). -/
def sysno : SysSpec word :=
  fun i m o => o = .ok i.in_sysno m []

/-- The `k`-th syscall argument (`a0..a5`). -/
def arg (k : Nat) : SysSpec word :=
  fun i m o => o = .ok (in_arg i k) m []

/-- Read the model. -/
def getModelSpec : SysSpec Model := getModel

/-- Update the model. -/
def modifySpec (f : Model → Model) : SysSpec Unit := modify f

/-- Unit-returning sequencing, `c;; k`. -/
def seqSpec {A : Type} (c : SysSpec Unit) (k : SysSpec A) : SysSpec A :=
  bind c (fun _ => k)

/-- The three monad laws, restated at the concrete types (they are the
    generic theorems instantiated, not new proofs). -/
theorem sysspec_bind_pure_l {A B : Type} (a : A) (k : A → SysSpec B) :
    sysEquiv (bind (pure a) k) (k a) :=
  bind_pure_l a k

theorem sysspec_bind_pure_r {A : Type} (c : SysSpec A) :
    sysEquiv (bind c pure) c :=
  bind_pure_r c

theorem sysspec_bind_assoc {A B C : Type} (c : SysSpec A) (k : A → SysSpec B)
    (h : B → SysSpec C) :
    sysEquiv (bind (bind c k) h) (bind c (fun x => bind (k x) h)) :=
  bind_assoc c k h

end LinuxSem.LinuxProcessSem
