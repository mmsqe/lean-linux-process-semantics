/-
  * Common.RocqSpelling — the Rocq vocabulary the ported files still speak.

  NOT A TRUST BOUNDARY, and it changes no statement: every entry below is a
  transparent `abbrev`, so a statement written with the Rocq spelling is
  DEFINITIONALLY the same statement as one written with the Lean spelling
  (`bv_unsigned w` is `(w.toNat : Int)`, `Z_to_bv n z` is `BitVec.ofInt n z`,
  `nth_error l n` is `l[n]?`, and a field shim is the projection it names).
  Being abbreviations, they are also invisible to `unfold`, to `simp`'s
  definitional folding, and to the kernel: deleting one and writing the body
  in place changes no proof.

  WHY THEY LIVE HERE.  The `Checks/` worked examples are literal
  translations of the upstream Rocq files and keep the upstream spelling.
  That spelling used to be re-declared in every file that needed it — 27
  files carried the whole fifteen-name block, 35 carried at least
  `bv_unsigned` — which both duplicated the block and made the shims LEAK
  between modules: a file that opened two of those namespaces could see two
  different `bv_unsigned`s and fail with an ambiguity error
  (`Checks/Cases/Kernel/Time/Hrtimer.lean` opening
  `Checks/Cases/Kernel/Time/PosixTimers.lean` is the case that was hit).
  There is now one definition of each, and a consumer reaches it with

      open LinuxSem.Common.RocqSpelling

  A local declaration of the same name is never needed; if one is met, it is
  the copy that should go, not this module.

  The list is deliberately the set the examples actually use.  Adding to it
  is fine — put the abbreviation here rather than in the file that needs it.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Sys.Syscall

namespace LinuxSem.Common.RocqSpelling

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem

/-! ## Bitvector and integer spellings -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in `Int`
    so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `bv_signed`: the signed value of a bitvector, as an `Int`. -/
abbrev bv_signed {n : Nat} (w : BitVec n) : Int := w.toInt

/-- `Z_to_bv`: an `Int` re-wrapped at width `n` (two's complement). -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-- `nth_error`: `Option`-returning list indexing (`List.getElem?`). -/
abbrev nth_error {α : Type} [Inhabited α] (l : List α) (n : Nat) : Option α := l[n]?

/-- `Nat`-valued `Int` re-wrapping, as the upstream byte encoders read it.
    `u_small` below is the round trip the proofs about those encoders use. -/
theorem u_small {z : Int} (Hz : 0 ≤ z ∧ z < 2 ^ 64) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt]
  have h2 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by decide
  rw [h2, Int.emod_eq_of_lt Hz.1 Hz.2, Int.toNat_of_nonneg Hz.1]

/-! ## Field projections, as functions

    The upstream files pass a record projection where a function is wanted
    (`in_mem i`, `eff_writes e`); Lean reaches the same thing by dot
    notation, but the ported statements read better with the projection as a
    function.  These are the only field shims that earned their keep. -/

/-- `in_mem` as a function (a `SyscallInput` field projection). -/
abbrev in_mem (i : SyscallInput) : word → Option byte := i.in_mem
/-- `in_wmem` as a function. -/
abbrev in_wmem (i : SyscallInput) : word → Option byte := i.in_wmem
/-- `eff_ret` as a function. -/
abbrev eff_ret (e : SyscallEffect) : word := e.eff_ret
/-- `eff_writes` as a function. -/
abbrev eff_writes (e : SyscallEffect) : List (word × List byte) := e.eff_writes
/-- `eff_zeros` as a function. -/
abbrev eff_zeros (e : SyscallEffect) : List (word × word) := e.eff_zeros
/-- `eff_unmaps` as a function. -/
abbrev eff_unmaps (e : SyscallEffect) : List (word × word) := e.eff_unmaps
/-- `eff_copies` as a function. -/
abbrev eff_copies (e : SyscallEffect) : List MemCopy := e.eff_copies
/-- `eff_copyins` as a function. -/
abbrev eff_copyins (e : SyscallEffect) : List (word × Nat) := e.eff_copyins

end LinuxSem.Common.RocqSpelling
