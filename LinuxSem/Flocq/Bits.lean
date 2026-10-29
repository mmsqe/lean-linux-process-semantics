/-
  * Bits — the bit operations `Fpu` needs, over `Int`.

  Lean's core `Int` has shifts (`<<<`, `>>>`) but no `land`/`lor`/`lxor`/
  `testBit`; the Rocq source uses `Z.land`, `Z.lor`, `Z.lxor`,
  `Z.testbit` and `Z.ones`.  This file provides them.

  All uses in `Fpu.v` are on NON-NEGATIVE integers (raw IEEE bit patterns,
  field masks, address-sized values).  The operations below are exact for
  non-negative operands, which is the documented precondition; `int_wrap`
  needs the two's-complement truncation of a possibly negative value and
  is written as a Euclidean `%` at its use site instead of `land`.
-/
namespace LinuxSem.Flocq

/-- `Z.ones n` = 2^n − 1 (n ≥ 0). -/
def zones (n : Int) : Int := ((2 ^ n.toNat : Nat) : Int) - 1

/-- Bit test (`Z.testbit`), for non-negative values. -/
def ztestBit (z : Int) (i : Nat) : Bool := z.toNat.testBit i

/-- Bitwise and (`Z.land`), for non-negative values. -/
def zland (a b : Int) : Int := (Nat.land a.toNat b.toNat : Int)

/-- Bitwise or (`Z.lor`), for non-negative values. -/
def zlor (a b : Int) : Int := (Nat.lor a.toNat b.toNat : Int)

/-- Bitwise xor (`Z.lxor`), for non-negative values. -/
def zlxor (a b : Int) : Int := (Nat.xor a.toNat b.toNat : Int)

/-- Two's-complement truncation to `bits` bits (`Z.land v (Z.ones bits)`),
    correct for negative `v` too: the Euclidean remainder has the same low
    bits. -/
def ztrunc (bits : Int) (v : Int) : Int := v % (2 ^ bits.toNat : Nat)

end LinuxSem.Flocq
