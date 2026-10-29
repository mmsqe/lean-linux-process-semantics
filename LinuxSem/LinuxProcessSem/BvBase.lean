/-
  * LinuxProcessSem.BvBase — shared bitvector helpers for the spec layer

  TRUST BOUNDARY: this file is part of the trusted specification.

  Bitvector representation follows two rules:

  - machine QUANTITIES (register values, addresses, syscall args and
    returns, fds, channel ids, sizes, offsets, exit codes) are
    `word = BitVec 64`; memory/file/event BYTES are `byte = BitVec 8`;
  - RANGE and DISJOINTNESS arithmetic is done in `Int` over
    `toNat`/`toInt` (no wrap-around), so bound checks keep a precise
    meaning.  Only data that lands back in registers or memory is
    re-wrapped with `BitVec.ofInt`.

  `word`, `reg`, `bv_eqb`, `bv_ltu`, `bv_lts` come from the ISA prelude
  (`LinuxSem.Riscv.Prelude`).

  `byte` and `bv_leu` live in `Riscv/Prelude.lean` rather than
  here, so that modules which only need bytes (e.g. `Fs`) do not have to
  depend on the whole of BvBase.  They are re-exported below.

  `bytes_le_to_Z_of_le_bytes` is proved at the bottom of this file, from the `Nat` byte recursion alone — `BvBase` still imports
  nothing beyond the ISA prelude.  Three later modules (`Sys/Uapi.lean`,
  `Common/LibWritev.lean`, `Common/AsanPlanSound2.lean`) each carry a
  private 8-byte instance of the round trip, written when this general
  statement was absent; those copies remain (they are stated over
  `bytes_le_to_Nat` directly and are what their local proofs consume) but
  the general theorem is no longer a gap.
-/
import LinuxSem.Riscv.Prelude

namespace LinuxSem.LinuxProcessSem

open LinuxSem.Riscv

export LinuxSem.Riscv (byte bv_leu)

/-- List length as a 64-bit word (all modeled lengths are far below 2^64,
    so this never wraps). -/
def len_word {α : Type} (l : List α) : word := BitVec.ofNat 64 l.length

/-- Word/nat bridges for list indexing and fuel. -/
def word_to_nat (w : word) : Nat := w.toNat

def nat_to_word (n : Nat) : word := BitVec.ofNat 64 n

/-- Convert a word to a `Nat`, but never construct a unary numeral larger
    than `bound`.  Extensionally this is just `min`; the spelling is
    load-bearing for extraction (the huge branch is never evaluated). -/
def word_to_nat_bounded (w : word) (bound : Nat) : Nat :=
  if w.toNat ≤ bound then w.toNat else bound

theorem word_to_nat_bounded_eq_min (w : word) (bound : Nat) :
    word_to_nat_bounded w bound = min (word_to_nat w) bound := by
  unfold word_to_nat_bounded word_to_nat
  by_cases h : w.toNat ≤ bound
  · simp [h, Nat.min_eq_left h]
  · have h' : bound ≤ w.toNat := by omega
    simp [h, Nat.min_eq_right h']

/-! ## Little-endian byte (de)composition -/

/-- The 8 little-endian bytes of a 64-bit word (index 0 = least
    significant). -/
def word_le8 (v : word) : List byte :=
  [ bits 0 8 v, bits 8 8 v, bits 16 8 v, bits 24 8 v,
    bits 32 8 v, bits 40 8 v, bits 48 8 v, bits 56 8 v ]

/-- Little-endian assembly (`BitVec.append` puts its FIRST argument in
    the high bits). -/
def le2 (b1 b0 : byte) : BitVec 16 := b1.append b0

def le4 (b3 b2 b1 b0 : byte) : BitVec 32 := (le2 b3 b2).append (le2 b1 b0)

def le8 (b7 b6 b5 b4 b3 b2 b1 b0 : byte) : word :=
  (le4 b7 b6 b5 b4).append (le4 b3 b2 b1 b0)

/-- The value of a little-endian byte list (index 0 = least significant),
    as an EXACT non-negative integer: it walks the whole list and
    truncates nothing, so a list longer than 8 bytes yields a number above
    2^64.  The 64-bit truncation belongs to `le_bytes_to_word` below.

  computed in `Nat` (Lean's `Int` has no bitwise operations in
    the core library); the result is non-negative, so the `Int` view is
    exact. -/
def bytes_le_to_Nat : List byte → Nat
  | [] => 0
  | b :: rest => b.toNat ||| (bytes_le_to_Nat rest <<< 8)

/-- `bytes_le_to_Nat` as an `Int`. -/
def bytes_le_to_Z (bs : List byte) : Int := (bytes_le_to_Nat bs : Int)

/-- The same value truncated to 64 bits; callers never pass more than 8
    bytes, where the truncation does nothing. -/
def le_bytes_to_word (bs : List byte) : word := BitVec.ofInt 64 (bytes_le_to_Z bs)

/-- The `n` little-endian bytes of `z` (index 0 = least significant) —
    `bytes_le_to_Z`'s inverse, truncating `z` to `8n` bits. -/
def Z_to_le_bytes : Nat → Int → List byte
  | 0, _ => []
  | n+1, z => BitVec.ofInt 8 z :: Z_to_le_bytes n (z >>> 8)

theorem length_Z_to_le_bytes (n : Nat) (z : Int) :
    (Z_to_le_bytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [Z_to_le_bytes, ih]

/-! ### The little-endian round trip `bytes_le_to_Z (Z_to_le_bytes k z)`

    `BvBase.lean:117` `bytes_le_to_Z_of_le_bytes`.  The port's
    `bytes_le_to_Nat` is a `Nat` recursion (Lean's `Int` has no bitwise
    operations in core), so the work is done at `Nat` and cast back: the
    `Nat` statement is the whole content, since `bytes_le_to_Nat` is
    non-negative by construction. -/

/-- One byte off the front of a little-endian read: the byte is the low
    eight bits and the rest is shifted up by eight. -/
theorem bytes_le_to_Nat_cons (b : byte) (rest : List byte) :
    bytes_le_to_Nat (b :: rest) = bytes_le_to_Nat rest * 256 + b.toNat := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [bytes_le_to_Nat]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb]
  simp [Nat.shiftLeft_eq]

/-- The byte `Z_to_le_bytes` emits first is the low byte. -/
private theorem ofInt8_toNat (m : Nat) :
    (BitVec.ofInt 8 (m : Int)).toNat = m % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_emod (Int.natCast_nonneg m) (by decide)]
  rw [show ((2 ^ 8 : Nat) : Int) = (256 : Int) by decide]
  simp

/-- `Z_to_le_bytes`'s shift, at a `Nat`-valued argument. -/
private theorem shiftRight8_natCast (m : Nat) :
    ((m : Int) >>> 8) = ((m / 256 : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.ofNat_ediv_ofNat]

/-- Splitting the low byte off a `Nat` and reducing modulo `2^(8k+8)`:
    the low byte is what survives, the high part is reduced modulo
    `2^(8k)` and shifted back up. -/
private theorem mod_pow8_succ (k m : Nat) :
    (m / 256 % 2 ^ (8 * k)) * 256 + m % 256 = m % 2 ^ (8 * (k + 1)) := by
  have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
    rw [show 8 * (k + 1) = 8 * k + 8 from by omega, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 from by decide]
  rw [hpow]
  have hC : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _
  have hlt : m % 256 < 256 := Nat.mod_lt _ (by decide)
  have hq : m / 256 % 2 ^ (8 * k) < 2 ^ (8 * k) := Nat.mod_lt _ hC
  conv =>
    rhs
    rw [show m = 256 * (m / 256) + m % 256 from (Nat.div_add_mod m 256).symm,
      Nat.mul_comm (2 ^ (8 * k)) 256]
  rw [Nat.add_mod, Nat.mul_mod_mul_left,
    Nat.mod_eq_of_lt (show m % 256 < 256 * 2 ^ (8 * k) from by omega),
    Nat.mod_eq_of_lt (show 256 * (m / 256 % 2 ^ (8 * k)) + m % 256
        < 256 * 2 ^ (8 * k) from by omega),
    Nat.mul_comm 256 (m / 256 % 2 ^ (8 * k))]

/-- The round trip at `Nat`: the `k` low bytes of `m` read back as `m`
    truncated to `8k` bits. -/
theorem bytes_le_to_Nat_Z_to_le_bytes (k : Nat) (m : Nat) :
    bytes_le_to_Nat (Z_to_le_bytes k (m : Int)) = m % 2 ^ (8 * k) := by
  induction k generalizing m with
  | zero => rw [Z_to_le_bytes, Nat.mod_one]; rfl
  | succ k ih =>
    show bytes_le_to_Nat (BitVec.ofInt 8 (m : Int) :: Z_to_le_bytes k ((m : Int) >>> 8))
      = m % 2 ^ (8 * (k + 1))
    rw [bytes_le_to_Nat_cons, shiftRight8_natCast, ih (m / 256), ofInt8_toNat]
    exact mod_pow8_succ k m

/-- `BvBase.lean:117`: `Z_to_le_bytes` keeps exactly the low `8k`
    bits.  (`0 ≤ z` is own side condition.) -/
theorem bytes_le_to_Z_of_le_bytes (k : Nat) (z : Int) (Hz : 0 ≤ z) :
    bytes_le_to_Z (Z_to_le_bytes k z) = z % ((2 ^ (8 * k) : Nat) : Int) := by
  have hz : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg Hz
  conv => lhs; rw [← hz]
  conv => rhs; rw [← hz]
  unfold bytes_le_to_Z
  rw [bytes_le_to_Nat_Z_to_le_bytes, Int.natCast_emod]

/-! ## The `Int`/`BitVec` round trips

The three facts below are the ones the byte-level proofs reach for when a
`Nat` (a byte, a length, a shift) has to pass through an `Int` and come back.
They used to be restated privately in every module that needed them —
`ofInt_toNat` in seven files, `toNat_ofInt_8_nat` and
`int_shiftRight_8_natCast` in six each (`Common/AxSymExec3Sound`,
`Common/AllocSim`, `Common/BackingAlgebra`, `Common/FileSim`,
`Common/StepTac`, `LinuxProcessSem/Sys/Uapi`, `Checks/Witness/...`) — so
they live here once, next to the encoders they are about. -/

/-- Re-wrapping the unsigned value of a word at 64 bits gives the word back. -/
theorem ofInt_toNat (w : word) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt]

/-- The low byte of a `Nat`, as the byte encoders write it. -/
theorem toNat_ofInt_8_nat (m : Nat) : (BitVec.ofInt 8 (m : Int)).toNat = m % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_emod (Int.natCast_nonneg m) (by decide)]
  rw [show ((2 ^ 8 : Nat) : Int) = (256 : Int) by decide]
  simp

/-- Dropping the low byte of a `Nat` read as an `Int` is its quotient by 256. -/
theorem int_shiftRight_8_natCast (m : Nat) :
    ((m : Int) >>> 8) = ((m / 256 : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.ofNat_ediv_ofNat]

end LinuxSem.LinuxProcessSem


