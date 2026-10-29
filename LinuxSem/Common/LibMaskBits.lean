/-
  * Common.LibMaskBits — word-level arithmetic facts for the mallocng summaries.
    Image-independent; pure Z / bv lemmas:
      masks (`land` with 2^k-1 / with -4096 / with 126), shifts as mul/div,
      the packed-word field extractions, and the 32-bit mask test
      `lw mask; sllw 1 idx; and` = 0  <-  bit idx of mask clear.

     banner (carried over): written by the OSS-Fuzz proof
    collaborators.

    NOTES.

    - `Z` is `Int`, `list` stays `List`.  `Z.land` has no Lean core
      counterpart on `Int`, so `zland`/`zshiftl`/`zshiftr` are
      `Common/PropExec.lean`'s .
    - `Z.testbit a k` is `Nat.testBit a.toNat k`: Lean core states bit tests
      on the `Nat` representative, which is where `Z.testbit` is defined, and
      every witness below carries the `0 ≤ a` that makes the two agree.  Bit
      INDICES  are `Nat` — this tree's §4.3 convention.
      Shift AMOUNTS and register values stay `Int`, converted with `.toNat` at
      the exponent, the spelling `PropExec.zshiftl`/`v_slli` already use.
    - `2^n` at `Int` level has two spellings in Lean — the `HPow` one and the
      `↑(2^n)` one the `BitVec`/`zland` library unfolds to.  Lean's `omega`
      already handles `Int` division and modulus by numerals, so nothing has
      to be added for it.
    - HELPERS.  The private block below does the `Int`↔`Nat` and bit-indexed
      work the proofs need as `Nat`-level facts (`Nat.land_ones`,
      `Nat.testBit_shiftLeft`, `Nat.div_pow2_bits`, `Nat.lor_add_nocarry`,
      `Nat.eq_of_testBit_eq`, …) that Lean core does not have.
      No  statement mentions them.  Closed numeral identities are
      settled by `decide` (`2^64 - 4096 = 2^12 * (2^52 - 1)` and friends);
      the `Int` steps around them are `omega`.
-/

import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Common.PropExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac

set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.unusedVariables false

namespace LinuxSem.Common.LibMaskBits

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.StepTac

/- PropExec's `Z_bounded_by_bits` (used by `mask_test_clear`) lives in its
   `FPState` section; pin the instance the way `ShapeAlg`/`LibWritev` do. -/
local instance maskbits_fx : PropExec.FPState := PropExec.fx0

/-! =========================================================================
    HELPERS — the `Nat`/`Int` and bit-indexed facts the
    core library does not supply
    ========================================================================= -/

/-- `2^n` is positive at `Int` level. -/
private theorem int_two_pow_pos (n : Nat) : (0 : Int) < 2 ^ n :=
  Int.ofNat_lt.mpr (Nat.two_pow_pos n)

/-- `2^n` is non-negative at `Int` level. -/
private theorem int_two_pow_nonneg (n : Nat) : (0 : Int) ≤ 2 ^ n :=
  Int.natCast_nonneg (2 ^ n)

/-- `2^(n+m) = 2^n * 2^m` at `Int` level. -/
private theorem int_two_pow_mul (n m : Nat) :
    (2 : Int) ^ (n + m) = (2 : Int) ^ n * (2 : Int) ^ m :=
  Int.pow_add 2 n m

/-- `2^32 * (2^32 - 1) = 2^64 - 2^32`, the mask/errno numeral identity. -/
private theorem int_two_pow32_mul_sub_one :
    (2 : Int) ^ 32 * ((2 : Int) ^ 32 - 1) = (2 : Int) ^ 64 - (2 : Int) ^ 32 := by
  rw [Int.mul_sub, Int.mul_one, show (64 : Nat) = 32 + 32 from rfl, int_two_pow_mul]

/-- `toNat` of a power of two, at `Int` level. -/
private theorem toNat_int_two_pow (n : Nat) : ((2 : Int) ^ n).toNat = 2 ^ n :=
  Int.toNat_natCast (2 ^ n)

/-- `toNat` of `2^n - 1`, at `Int` level. -/
private theorem toNat_int_two_pow_sub_one (n : Nat) : ((2 : Int) ^ n - 1).toNat = 2 ^ n - 1 := by
  have h : ((2 : Int) ^ n - 1) = ((2 ^ n - 1 : Nat) : Int) :=
    (Int.natCast_sub (Nat.one_le_two_pow)).symm
  rw [h, Int.toNat_natCast]

/-- The same for a NEGATIVE literal: the 64-bit wrap is `z + 2^64`. -/
private theorem toNat_ofInt_64_neg (z : Int) (h0 : -(2 : Int) ^ 64 < z) (h1 : z < 0) :
    (BitVec.ofInt 64 z).toNat = (z + 2 ^ 64).toNat := by
  have h2 : z % ((2 ^ 64 : Nat) : Int) = z + ((2 ^ 64 : Nat) : Int) := by
    have hz : (z + ((2 ^ 64 : Nat) : Int))
        + ((2 ^ 64 : Nat) : Int) * (-1) = z := by omega
    calc z % ((2 ^ 64 : Nat) : Int)
        = ((z + ((2 ^ 64 : Nat) : Int))
            + ((2 ^ 64 : Nat) : Int) * (-1)) % ((2 ^ 64 : Nat) : Int) := by rw [hz]
      _ = (z + ((2 ^ 64 : Nat) : Int)) % ((2 ^ 64 : Nat) : Int) :=
            Int.add_mul_emod_self_left _ _ _
      _ = z + ((2 ^ 64 : Nat) : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [BitVec.toNat_ofInt, h2]
  rfl

/-- `toNat` of an `Int` modulus by a `Nat` cast. -/
private theorem toNat_emod_natCast (x : Int) (m : Nat) (hx : 0 ≤ x) :
    (x % ((m : Nat) : Int)).toNat = x.toNat % m := by
  have h : x % ((m : Nat) : Int) = ((x.toNat % m : Nat) : Int) := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg hx]
  rw [h, Int.toNat_natCast]

/-- `toNat` of an `Int` division by a `Nat` cast. -/
private theorem toNat_ediv_natCast (x : Int) (m : Nat) (hx : 0 ≤ x) :
    (x / ((m : Nat) : Int)).toNat = x.toNat / m := by
  have h : x / ((m : Nat) : Int) = ((x.toNat / m : Nat) : Int) := by
    rw [Int.natCast_ediv, Int.toNat_of_nonneg hx]
  rw [h, Int.toNat_natCast]

/-- `toNat` of an `Int` product by `2^n`. -/
private theorem toNat_mul_two_pow (a : Int) (n : Nat) (ha : 0 ≤ a) :
    (a * (2 : Int) ^ n).toNat = a.toNat * 2 ^ n := by
  rw [Int.toNat_mul ha (int_two_pow_nonneg n), toNat_int_two_pow n]

/-- **The bit-splitting identity for `&&&`.**  Masking the high part of a
    value that is split as `2^n * q + r` is masking `q`, then shifting back:
    the low `n` bits of the mask are zero, so `r` cannot contribute. -/
private theorem nat_land_shift (n q r M : Nat) (hr : r < 2 ^ n) :
    (2 ^ n * q + r) &&& (2 ^ n * M) = 2 ^ n * (q &&& M) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hL : (2 ^ n * q + r).testBit i
      = (if i < n then r.testBit i else q.testBit (i - n)) :=
    Nat.testBit_two_pow_mul_add q hr i
  rw [Nat.testBit_and, hL, Nat.mul_comm (2 ^ n) M, Nat.testBit_mul_two_pow,
    Nat.mul_comm (2 ^ n) (q &&& M), Nat.testBit_mul_two_pow, Nat.testBit_and]
  by_cases hi : i < n
  · rw [ite_eq_left hi, decide_eq_false (by omega)]
    simp
  · rw [ite_eq_right hi, decide_eq_true (by omega)]
    simp

/-- `&&&` with a single power of two is zero exactly when that bit is clear. -/
private theorem nat_land_pow2_eq_zero (y n : Nat) :
    y &&& 2 ^ n = 0 ↔ y.testBit n = false := by
  constructor
  · intro h
    have h' := congrArg (fun z => z.testBit n) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit] using h'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : i = n
    · subst hi; rw [h]; simp
    · rw [decide_eq_false (by omega)]; simp

/- `(x - x % 2^n)` is `2^n * (x / 2^n)`. -/
private theorem nat_sub_mod_eq_mul_div (x n : Nat) :
    x - x % 2 ^ n = 2 ^ n * (x / 2 ^ n) := by
  have h := Nat.div_add_mod x (2 ^ n)
  omega

private theorem nat_and_pagemask (y : Nat) (hy : y < 2 ^ 64) :
    y &&& (2 ^ 64 - 4096) = y - y % 4096 := by
  obtain ⟨q, r, hyq, hr⟩ : ∃ q r : Nat, y = 2 ^ 12 * q + r ∧ r < 2 ^ 12 :=
    ⟨y / 2 ^ 12, y % 2 ^ 12, (Nat.div_add_mod y (2 ^ 12)).symm,
      Nat.mod_lt _ (by decide)⟩
  have hmask : 2 ^ 64 - 4096 = 2 ^ 12 * (2 ^ 52 - 1) := by
    have h4096 : (4096 : Nat) = 2 ^ 12 := by decide
    have h64 : (2 : Nat) ^ 64 = 2 ^ 12 * 2 ^ 52 := by
      rw [show (64 : Nat) = 12 + 52 from rfl, Nat.pow_add]
    rw [h64, h4096, Nat.mul_sub, Nat.mul_one]
  have hq : q < 2 ^ 52 := by
    have h64 : (2 : Nat) ^ 64 = 2 ^ 12 * 2 ^ 52 := by
      rw [show (64 : Nat) = 12 + 52 from rfl, Nat.pow_add]
    have h1 : 2 ^ 12 * q < 2 ^ 12 * 2 ^ 52 := by
      rw [h64] at hy
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  calc y &&& (2 ^ 64 - 4096) = (2 ^ 12 * q + r) &&& (2 ^ 12 * (2 ^ 52 - 1)) := by
        rw [hyq, hmask]
    _ = 2 ^ 12 * (q &&& (2 ^ 52 - 1)) := nat_land_shift 12 q r _ hr
    _ = 2 ^ 12 * (q % 2 ^ 52) := by rw [Nat.and_two_pow_sub_one_eq_mod]
    _ = 2 ^ 12 * q := by rw [Nat.mod_eq_of_lt hq]
    _ = y - y % 4096 := by
        have hmod : (2 ^ 12 * q + r) % 2 ^ 12 = r := by
          rw [Nat.add_comm (2 ^ 12 * q) r, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hr]
        rw [hyq, show (4096 : Nat) = 2 ^ 12 from by decide, hmod, Nat.add_sub_cancel]

/-- `↑k = 0` at `Nat` level. -/
private theorem natCast_eq_zero_int {k : Nat} : ((k : Int) = 0 ↔ k = 0) := by
  constructor
  · intro h; omega
  · intro h; rw [h]; rfl

/-! =========================================================================
    testbit toolbox
    ========================================================================= -/

/-- Above a width that fits, every bit is clear. -/
theorem testbit_high (n : Nat) (a : Int) (k : Nat) (Ha : 0 ≤ a)
    (Hb : a < (2 : Int) ^ n) (Hk : n ≤ k) :
    Nat.testBit a.toNat k = false := by
  apply Nat.testBit_lt_two_pow
  have h : (a.toNat : Int) < ((2 ^ n : Nat) : Int) := by
    rw [Int.toNat_of_nonneg Ha]; exact Hb
  exact Nat.lt_of_lt_of_le (Int.ofNat_lt.mp h) (Nat.pow_le_pow_right (by decide) Hk)

/-- Bit `k` of `2^n` is set exactly at `k = n`. -/
theorem testbit_pow2 (n k : Nat) : Nat.testBit (2 ^ n) k = decide (k = n) := by
  rw [Nat.testBit_two_pow]
  exact decide_eq_decide.mpr (by omega)

/-- Adding a multiple of `2^32` does not change the low 32 bits. -/
theorem testbit_add_high (a m : Int) (k : Nat) (Ha : 0 ≤ a ∧ a < (2 : Int) ^ 32)
    (Hm : 0 ≤ m) (Hk : k < 32) :
    Nat.testBit (a + (2 : Int) ^ 32 * m).toNat k = Nat.testBit a.toNat k := by
  have ha : a.toNat < 2 ^ 32 := by
    have h : (a.toNat : Int) < ((2 ^ 32 : Nat) : Int) := by
      rw [Int.toNat_of_nonneg Ha.1]; exact Ha.2
    exact Int.ofNat_lt.mp h
  have hsum : (a + (2 : Int) ^ 32 * m).toNat = 2 ^ 32 * m.toNat + a.toNat := by
    rw [Int.toNat_add Ha.1 (Int.mul_nonneg (int_two_pow_nonneg 32) Hm),
      Int.toNat_mul (int_two_pow_nonneg 32) Hm, toNat_int_two_pow 32, Nat.add_comm]
  rw [hsum, Nat.testBit_two_pow_mul_add m.toNat ha k, ite_eq_left Hk]

/-- The same, one level up: bit `k >= 32` of `a + 2^32 * m` is bit `k - 32`
    of `m`. -/
theorem testbit_add_high2 (a m : Int) (k : Nat) (Ha : 0 ≤ a ∧ a < (2 : Int) ^ 32)
    (Hm : 0 ≤ m) (Hk : 32 ≤ k) :
    Nat.testBit (a + (2 : Int) ^ 32 * m).toNat k = Nat.testBit m.toNat (k - 32) := by
  have ha : a.toNat < 2 ^ 32 := by
    have h : (a.toNat : Int) < ((2 ^ 32 : Nat) : Int) := by
      rw [Int.toNat_of_nonneg Ha.1]; exact Ha.2
    exact Int.ofNat_lt.mp h
  have hsum : (a + (2 : Int) ^ 32 * m).toNat = 2 ^ 32 * m.toNat + a.toNat := by
    rw [Int.toNat_add Ha.1 (Int.mul_nonneg (int_two_pow_nonneg 32) Hm),
      Int.toNat_mul (int_two_pow_nonneg 32) Hm, toNat_int_two_pow 32, Nat.add_comm]
  rw [hsum, Nat.testBit_two_pow_mul_add m.toNat ha k, ite_eq_right (by omega)]

/-! =========================================================================
    Masks
    ========================================================================= -/

/-- `land` with `2^k - 1` is `mod 2^k`. -/
theorem land_ones_mod (x : Int) (k : Nat) (Hx : 0 ≤ x) :
    zland x ((2 : Int) ^ k - 1) = x % (2 : Int) ^ k := by
  unfold zland
  rw [toNat_int_two_pow_sub_one k, Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod,
    Int.toNat_of_nonneg Hx]
  rfl

/-- `and` with 0xffff_ffff_ffff_f000 rounds a 64-bit value down to a page. -/
theorem land_pagemask (x : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64) :
    zland x ((2 : Int) ^ 64 - 4096) = x - x % 4096 := by
  have hx : x.toNat < 2 ^ 64 := by
    have h : (x.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
      rw [Int.toNat_of_nonneg Hx.1]; exact Hx.2
    exact Int.ofNat_lt.mp h
  have hm : ((2 : Int) ^ 64 - 4096).toNat = 2 ^ 64 - 4096 := by
    have hle : (4096 : Nat) ≤ 2 ^ 64 := by
      rw [show (4096 : Nat) = 2 ^ 12 from by decide]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have h : ((2 : Int) ^ 64 - 4096) = ((2 ^ 64 - 4096 : Nat) : Int) :=
      (Int.natCast_sub hle).symm
    rw [h, Int.toNat_natCast]
  unfold zland
  rw [hm, nat_and_pagemask x.toNat hx]
  have hxeq : ((x.toNat : Int)) = x := Int.toNat_of_nonneg Hx.1
  have hmod : x % 4096 = ((x.toNat % 4096 : Nat) : Int) := by
    rw [Int.natCast_emod, hxeq]
    rfl
  rw [hmod]
  rw [Int.natCast_sub (Nat.mod_le _ _)]
  rw [hxeq]


/-! =========================================================================
    Packed meta word fields
    ========================================================================= -/

/-- The residue of `zshiftl W 52` modulo `2^64`, as a `Nat`.
 Keeping it a
    separate constant is what keeps the kernel check cheap: `rw` inlines
    the proof it rewrites with, once per occurrence, and this term's
    inlined copies recurse past `maxRecDepth` ("deep recursion detected",
    after ~100 s of checking).  As a named lemma it is checked once. -/
private theorem sc_shift_emod (W : Int) (HW : 0 ≤ W ∧ W < (2 : Int) ^ 64) :
    zshiftl W 52 % ((2 ^ 64 : Nat) : Int) = ((W.toNat * 2 ^ 52 % 2 ^ 64 : Nat) : Int) := by
  have hnn : 0 ≤ zshiftl W 52 % ((2 ^ 64 : Nat) : Int) := by
    unfold zshiftl
    exact Int.emod_nonneg (a := W * (2 : Int) ^ 52) (b := ((2 ^ 64 : Nat) : Int)) (by decide)
  have ht : (zshiftl W 52 % ((2 ^ 64 : Nat) : Int)).toNat
      = W.toNat * 2 ^ 52 % 2 ^ 64 := by
    rw [toNat_emod_natCast _ (2 ^ 64)
        (by unfold zshiftl; exact Int.mul_nonneg HW.1 (int_two_pow_nonneg 52)),
      show zshiftl W 52 = W * (2 : Int) ^ 52 from rfl, toNat_mul_two_pow W 52 HW.1]
  rw [← Int.toNat_of_nonneg hnn, ht]

/-- slli 52 ; srli 58  =  bits 6..11. -/
theorem sc_extract (W : Int) (HW : 0 ≤ W ∧ W < (2 : Int) ^ 64) :
    zshiftr (zshiftl W 52 % (2 : Int) ^ 64) 58 = (W / 64) % 64 := by
  change zshiftr (zshiftl W 52 % ((2 ^ 64 : Nat) : Int)) 58 = (W / 64) % 64
  have hkey : W.toNat * 2 ^ 52 % 2 ^ 64 / 2 ^ 58 = W.toNat / 64 % 64 := by
    have h1 : W.toNat * 2 ^ 52 % 2 ^ 64 = 2 ^ 52 * (W.toNat % 2 ^ 12) := by
      rw [Nat.mul_comm W.toNat (2 ^ 52),
        show (2 : Nat) ^ 64 = 2 ^ 52 * 2 ^ 12 from by decide]
      exact Nat.mul_mod_mul_left _ _ _
    rw [h1, show (2 : Nat) ^ 58 = 2 ^ 52 * 2 ^ 6 from by decide,
      Nat.mul_div_mul_left _ _ (by decide : 0 < 2 ^ 52),
      show (2 : Nat) ^ 12 = 2 ^ 6 * 2 ^ 6 from by decide,
      Nat.mod_mul_right_div_self, show (64 : Nat) = 2 ^ 6 from by decide]
  -- Both sides in the `↑(… : Nat)` spelling, so that `hkey` is the last
  -- step and no `Int.toNat` reasoning is needed at the end.
  have hlhs : zshiftr (zshiftl W 52 % ((2 ^ 64 : Nat) : Int)) 58
      = ((W.toNat * 2 ^ 52 % 2 ^ 64 / 2 ^ 58 : Nat) : Int) := by
    unfold zshiftr
    rw [sc_shift_emod W HW, ← Int.natCast_ediv]
  have hrhs : (W / 64) % 64 = ((W.toNat / 64 % 64 : Nat) : Int) := by
    have h1 : (W / 64).toNat = W.toNat / 64 := toNat_ediv_natCast W 64 HW.1
    rw [← Int.toNat_of_nonneg (Int.ediv_nonneg HW.1 (by decide)), h1]
    exact (Int.natCast_emod (W.toNat / 64) 64).symm
  rw [hlhs, hrhs, hkey]

/-- srli 5 ; andi 126  =  2 * sizeclass. -/
theorem sc2_extract (W : Int) (HW : 0 ≤ W) :
    zland (zshiftr W 5) 126 = 2 * ((W / 64) % 64) := by
  have hkey : W.toNat / 2 ^ 5 &&& 126 = 2 * (W.toNat / 64 % 64) := by
    have hq : W.toNat / 2 ^ 5 / 2 ^ 1 = W.toNat / 64 := by
      rw [Nat.div_div_eq_div_mul, show (2 : Nat) ^ 5 * 2 ^ 1 = 64 from by decide]
    have hsplit : W.toNat / 2 ^ 5 = 2 ^ 1 * (W.toNat / 64) + W.toNat / 2 ^ 5 % 2 ^ 1 := by
      rw [← hq]
      exact (Nat.div_add_mod (W.toNat / 2 ^ 5) (2 ^ 1)).symm
    rw [hsplit, show (126 : Nat) = 2 ^ 1 * (2 ^ 6 - 1) from by decide,
      nat_land_shift 1 _ _ _ (Nat.mod_lt _ (by decide)), Nat.and_two_pow_sub_one_eq_mod]
  have hshift : (zshiftr W 5).toNat = W.toNat / 2 ^ 5 := by
    unfold zshiftr
    exact toNat_ediv_natCast W (2 ^ 5) HW
  unfold zland
  rw [show (126 : Int) = ((126 : Nat) : Int) from rfl, Int.toNat_natCast, hshift, hkey,
    Int.natCast_mul]
  congr 1
  have hr : ((W / 64) % 64).toNat = W.toNat / 64 % 64 := by
    have h2 : ((W / 64) % 64).toNat = (W / 64).toNat % 64 :=
      toNat_emod_natCast (W / 64) 64 (Int.ediv_nonneg HW (by decide))
    have h1 : (W / 64).toNat = W.toNat / 64 := toNat_ediv_natCast W 64 HW
    rw [h2, h1]
  rw [← Int.toNat_of_nonneg (Int.emod_nonneg (a := W / 64) (b := 64) (by decide)), hr]

/-! =========================================================================
    The 32-bit mask test: lw mask ; li 1 ; sllw by idx ; and  =  0
    ========================================================================= -/

/-- unsigned value of a sign-extended 32-bit quantity -/
theorem swrap32_cases (a : Int) (Ha : 0 ≤ a ∧ a < (2 : Int) ^ 32) :
    (a < 2 ^ 31 ∧ bv_swrap 32 a = a) ∨
      (2 ^ 31 ≤ a ∧ bv_swrap 32 a = a - 2 ^ 32) := by
  have Ha' : 0 ≤ a ∧ a < ((2 ^ 32 : Nat) : Int) := Ha
  have h31nat : 2 ^ 31 + 2 ^ 31 = (2 ^ 32 : Nat) := by decide
  have h31 : ((2 ^ 31 : Nat) : Int) + ((2 ^ 31 : Nat) : Int) = ((2 ^ 32 : Nat) : Int) := by
    rw [← Int.natCast_add, h31nat]
  have hp31 : (0 : Int) < ((2 ^ 31 : Nat) : Int) := by decide
  have hp32 : (0 : Int) < ((2 ^ 32 : Nat) : Int) := by decide
  unfold bv_swrap
  rw [show 32 - 1 = 31 from rfl]
  by_cases h : a < ((2 ^ 31 : Nat) : Int)
  · left
    refine ⟨h, ?_⟩
    rw [Int.emod_eq_of_lt (a := a + ((2 ^ 31 : Nat) : Int))
      (b := ((2 ^ 32 : Nat) : Int)) (by omega) (by omega)]
    omega
  · right
    refine ⟨by omega, ?_⟩
    have hsub : (a + ((2 ^ 31 : Nat) : Int)) % ((2 ^ 32 : Nat) : Int)
        = (a + ((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int))
          % ((2 ^ 32 : Nat) : Int) := by
      rw [show a + ((2 ^ 31 : Nat) : Int)
          = (a + ((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int))
            + ((2 ^ 32 : Nat) : Int) * 1 from by rw [Int.mul_one]; omega,
        Int.add_mul_emod_self_left]
      congr 1
      omega
    rw [hsub, Int.emod_eq_of_lt
      (a := a + ((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int))
      (b := ((2 ^ 32 : Nat) : Int)) (by omega) (by omega)]
    omega

theorem u_lw_lo (a : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 31) :
    (v_lw (BitVec.ofInt 64 a)).toNat = a := by
  have h64 : a < 2 ^ 64 := by omega
  unfold v_lw
  rw [u_Z2bv a Ha.1 h64]
  rcases swrap32_cases a ⟨Ha.1, by omega⟩ with ⟨_, HE⟩ | ⟨Hge, _⟩
  · rw [HE, toNat_ofInt_of_range a Ha.1 h64, Int.toNat_of_nonneg Ha.1]
  · omega

theorem u_lw_hi (a : Int) (Ha : 2 ^ 31 ≤ a ∧ a < (2 : Int) ^ 32) :
    (v_lw (BitVec.ofInt 64 a)).toNat = a + 2 ^ 32 * (2 ^ 32 - 1) := by
  have h64 : a < 2 ^ 64 := by omega
  unfold v_lw
  rw [u_Z2bv a (by omega) h64]
  rcases swrap32_cases a ⟨by omega, Ha.2⟩ with ⟨Hlt, _⟩ | ⟨_, HE⟩
  · omega
  · rw [HE, toNat_ofInt_64_neg (a - 2 ^ 32) (by omega) (by omega),
      Int.toNat_of_nonneg (a := a - 2 ^ 32 + 2 ^ 64) (by omega)]
    have hnum := int_two_pow32_mul_sub_one
    omega

theorem u_sllw1 (idx : Int) (Hi : 0 ≤ idx ∧ idx ≤ 31) :
    (v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat =
      if idx = 31 then 2 ^ 31 + 2 ^ 32 * (2 ^ 32 - 1) else (2 : Int) ^ idx.toNat := by
  have hidx : idx < 2 ^ 64 := by omega
  unfold v_sllw zshiftl
  rw [toNat_ofInt_of_range 1 (by decide) (by decide), toNat_ofInt_of_range idx Hi.1 hidx,
    show idx.toNat % 32 = idx.toNat from Nat.mod_eq_of_lt (by omega),
    show (((1 : Int).toNat : Int)) = 1 from rfl, Int.one_mul]
  by_cases h : idx = 31
  · subst h
    rw [show ((31 : Int).toNat) = 31 from rfl, ite_eq_left rfl]
    rcases swrap32_cases ((2 ^ 31 : Nat) : Int) ⟨by decide, by decide⟩ with ⟨Hlt, _⟩ | ⟨_, HE⟩
    · omega
    · have HE' : bv_swrap 32 (((2 ^ 31 : Nat)) : Int)
          = ((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int) := HE
      rw [HE', toNat_ofInt_64_neg (((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int))
          (by decide) (by decide),
        Int.toNat_of_nonneg (a := ((2 ^ 31 : Nat) : Int) - ((2 ^ 32 : Nat) : Int)
          + 2 ^ 64) (by omega)]
      have hnum := int_two_pow32_mul_sub_one
      rw [show (2 : Int) ^ 31 + (2 : Int) ^ 32 * ((2 : Int) ^ 32 - 1)
          = (2 : Int) ^ 31 + ((2 : Int) ^ 64 - (2 : Int) ^ 32) from by rw [hnum]]
      omega
  · rw [ite_eq_right h]
    have hlt30 : idx.toNat ≤ 30 := by omega
    have hlt31 : ((2 ^ idx.toNat : Nat) : Int) < ((2 ^ 31 : Nat) : Int) := by
      have h2 : (2 : Nat) ^ idx.toNat < 2 ^ 31 :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      exact_mod_cast h2
    rcases swrap32_cases ((2 ^ idx.toNat : Nat) : Int)
        ⟨int_two_pow_nonneg _, by
          calc ((2 ^ idx.toNat : Nat) : Int) < ((2 ^ 31 : Nat) : Int) := hlt31
            _ < ((2 ^ 32 : Nat) : Int) := by decide⟩ with ⟨Hlt, HE⟩ | ⟨Hge, _⟩
    · have HE' : bv_swrap 32 (((2 ^ idx.toNat : Nat)) : Int) = ((2 ^ idx.toNat : Nat) : Int) := HE
      rw [HE', toNat_ofInt_of_range ((2 ^ idx.toNat : Nat) : Int) (int_two_pow_nonneg _) (by
        have h2 : (2 : Nat) ^ idx.toNat < 2 ^ 64 := by
          calc (2 : Nat) ^ idx.toNat ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
            _ < 2 ^ 64 := by decide
        exact_mod_cast h2), Int.toNat_natCast]
      rfl
    · omega


/-- If bit `n` of a non-negative value is clear, the `land` with `2^n` is 0. -/
theorem land_pow2_testbit (a : Int) (n : Nat) (Ha : 0 ≤ a) :
    zland a ((2 : Int) ^ n) = 0 ↔ Nat.testBit a.toNat n = false := by
  unfold zland
  rw [toNat_int_two_pow n, natCast_eq_zero_int, nat_land_pow2_eq_zero]

/-- THE bridge: if bit `idx` of the 32-bit mask is clear, the machine test
    computes 0. -/
theorem mask_test_clear (mask idx : Int) (Hm : 0 ≤ mask ∧ mask < (2 : Int) ^ 32)
    (Hi : 0 ≤ idx ∧ idx ≤ 31) (Hb : Nat.testBit mask.toNat idx.toNat = false) :
    v_and (v_lw (BitVec.ofInt 64 mask)) (v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx))
      = BitVec.ofInt 64 0 := by
  have hx : (v_lw (BitVec.ofInt 64 mask)).toNat =
      if mask < 2 ^ 31 then mask.toNat else mask.toNat + 2 ^ 32 * (2 ^ 32 - 1) := by
    by_cases h : mask < 2 ^ 31
    · rw [ite_eq_left h]
      have h1 := u_lw_lo mask ⟨Hm.1, h⟩
      omega
    · rw [ite_eq_right h]
      have h1 := u_lw_hi mask ⟨by omega, Hm.2⟩
      omega
  have hy : (v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat =
      if idx = 31 then 2 ^ 31 + 2 ^ 32 * (2 ^ 32 - 1) else 2 ^ idx.toNat := by
    by_cases h : idx = 31
    · rw [ite_eq_left h]
      have h1 : ((v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat : Int)
          = ((2 ^ 31 : Nat) : Int) + ((2 ^ 32 : Nat) : Int) * (((2 ^ 32 : Nat) : Int) - 1) := by
        rw [u_sllw1 idx Hi, ite_eq_left h]
        rfl
      omega
    · rw [ite_eq_right h]
      have h1 : ((v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat : Int)
          = ((2 ^ idx.toNat : Nat) : Int) := by
        rw [u_sllw1 idx Hi, ite_eq_right h]
        rfl
      omega
  -- `idx = 31` forces `mask < 2^31`, because bit 31 would otherwise be set
  have hmask_of_idx : idx = 31 → mask < 2 ^ 31 := by
    intro hidx
    have hb : Nat.testBit mask.toNat 31 = false := by
      have h := Hb
      rw [hidx] at h
      rwa [show ((31 : Int).toNat) = 31 from rfl] at h
    have hmask32 : mask.toNat < 2 ^ 32 := by
      have h : (mask.toNat : Int) < ((2 ^ 32 : Nat) : Int) := by
        rw [Int.toNat_of_nonneg Hm.1]; exact Hm.2
      exact Int.ofNat_lt.mp h
    have h : mask.toNat < 2 ^ 31 := by
      apply Z_bounded_by_bits 31 mask.toNat
      intro k hk
      rcases Nat.lt_or_ge k 32 with hk32 | hk32
      · have hk31 : k = 31 := by omega
        rw [hk31]; exact hb
      · exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hmask32 (Nat.pow_le_pow_right (by decide) hk32))
    have h2 : (mask.toNat : Int) < ((2 ^ 31 : Nat) : Int) := by exact_mod_cast h
    rw [Int.toNat_of_nonneg Hm.1] at h2
    exact h2
  have hzero : (v_lw (BitVec.ofInt 64 mask)).toNat
      &&& (v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat = 0 := by
    rw [hx, hy]
    by_cases hidx : idx = 31
    · rw [ite_eq_left hidx]
      have hmask : mask < 2 ^ 31 := hmask_of_idx hidx
      rw [ite_eq_left hmask]
      have hy2 : 2 ^ 31 + 2 ^ 32 * (2 ^ 32 - 1) = 2 ^ 31 * (2 ^ 33 - 1) := by decide
      rw [hy2, show mask.toNat &&& (2 ^ 31 * (2 ^ 33 - 1))
          = (2 ^ 31 * 0 + mask.toNat) &&& (2 ^ 31 * (2 ^ 33 - 1)) from by
        rw [Nat.mul_zero, Nat.zero_add],
          nat_land_shift 31 0 mask.toNat (2 ^ 33 - 1) (by omega), Nat.zero_and]
    · rw [ite_eq_right hidx]
      have hidxlt : idx.toNat < 31 := by omega
      by_cases hmask : mask < 2 ^ 31
      · rw [ite_eq_left hmask, nat_land_pow2_eq_zero]
        exact Hb
      · rw [ite_eq_right hmask, nat_land_pow2_eq_zero,
          Nat.add_comm mask.toNat (2 ^ 32 * (2 ^ 32 - 1)),
          Nat.testBit_two_pow_mul_add (2 ^ 32 - 1) (by omega) idx.toNat, ite_eq_left (by omega)]
        exact Hb
  unfold v_and
  rw [show zland (v_lw (BitVec.ofInt 64 mask)).toNat
        (v_sllw (BitVec.ofInt 64 1) (BitVec.ofInt 64 idx)).toNat = 0 from by
    unfold zland
    rw [Int.toNat_natCast, Int.toNat_natCast, hzero]
    rfl]

/-! =========================================================================
    Small word arithmetic in [Z_to_bv 64 z] form
    ========================================================================= -/

theorem v_andi_Z (x m : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64)
    (Hm : 0 ≤ m ∧ m < (2 : Int) ^ 64) :
    v_andi (BitVec.ofInt 64 x) m = BitVec.ofInt 64 (zland x m) := by
  unfold v_andi bv_wrap
  rw [u_Z2bv x Hx.1 Hx.2, Int.emod_eq_of_lt (b := ((2 ^ 64 : Nat) : Int)) Hm.1 (by omega)]

theorem v_and_Z (x y : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64)
    (Hy : 0 ≤ y ∧ y < (2 : Int) ^ 64) :
    v_and (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (zland x y) := by
  unfold v_and
  rw [u_Z2bv x Hx.1 Hx.2, u_Z2bv y Hy.1 Hy.2]

theorem v_slli_Z (x k : Int) (Hx : 0 ≤ x) (Hk : 0 ≤ k)
    (Hb : x * (2 : Int) ^ k.toNat < (2 : Int) ^ 64) :
    v_slli (BitVec.ofInt 64 x) k = BitVec.ofInt 64 (x * (2 : Int) ^ k.toNat) := by
  have h1 : (1 : Int) ≤ (2 : Int) ^ k.toNat := by
    have hp : (0 : Int) < (2 : Int) ^ k.toNat := int_two_pow_pos k.toNat
    omega
  have h2 : x ≤ x * (2 : Int) ^ k.toNat := by
    calc x = x * 1 := (Int.mul_one x).symm
      _ ≤ x * (2 : Int) ^ k.toNat := Int.mul_le_mul_of_nonneg_left h1 Hx
  have hx64 : x < 2 ^ 64 := by omega
  unfold v_slli zshiftl
  -- `zshiftl` spells the exponent's base as `↑(2 : Nat)`; the statement
  -- uses the `HPow` spelling.  The two are definitionally equal, so the
  -- `rfl` closes what `rw` leaves (a `rw` does not try conversion here).
  rw [u_Z2bv x Hx hx64, Int.natCast_pow]
  rfl

theorem v_srli_Z (x k : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64) (Hk : 0 ≤ k) :
    v_srli (BitVec.ofInt 64 x) k = BitVec.ofInt 64 (x / (2 : Int) ^ k.toNat) := by
  unfold v_srli zshiftr
  rw [u_Z2bv x Hx.1 Hx.2, Int.natCast_pow]
  rfl

theorem v_mul_Z (x y : Int) (Hx : 0 ≤ x) (Hy : 0 ≤ y)
    (Hx64 : x < 2 ^ 64) (Hy64 : y < 2 ^ 64) :
    v_mul (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (x * y) := by
  unfold v_mul
  rw [u_Z2bv x Hx Hx64, u_Z2bv y Hy Hy64]

theorem v_add_ZZ (x y : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64)
    (Hy : 0 ≤ y ∧ y < (2 : Int) ^ 64) :
    v_add (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (x + y) := by
  unfold v_add
  rw [u_Z2bv x Hx.1 Hx.2, u_Z2bv y Hy.1 Hy.2]

theorem v_sub_ZZ (x y : Int) (Hx : 0 ≤ y ∧ y ≤ x) (Hy : x < 2 ^ 64) :
    v_sub (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (x - y) := by
  unfold v_sub
  rw [u_Z2bv x (by omega) Hy, u_Z2bv y Hx.1 (by omega)]

theorem c_ltu_Z (x y : Int) (Hx : 0 ≤ x ∧ x < (2 : Int) ^ 64)
    (Hy : 0 ≤ y ∧ y < (2 : Int) ^ 64) :
    c_ltu (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = decide (x < y) := by
  unfold c_ltu bv_ltu
  rw [toNat_ofInt_of_range x Hx.1 Hx.2, toNat_ofInt_of_range y Hy.1 Hy.2]
  exact decide_eq_decide.mpr (by omega)

end LinuxSem.Common.LibMaskBits


