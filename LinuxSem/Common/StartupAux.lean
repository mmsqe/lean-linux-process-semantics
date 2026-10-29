/-
  * Common.StartupAux — small value lemmas and tactics for the reference
      startup walk (image-independent part).

      Small value lemmas and tactics for the reference startup walk
      (image-independent part).

    ---------------------------------------------------------------------
    NOTES
    ---------------------------------------------------------------------

    * `Z` → `Int`, `N`/`nat` → `Nat`, `bv_unsigned w` → `(w.toNat : Int)`,
      `Z_to_bv n z` → `BitVec.ofInt n z`, `repeat b n` →
      `List.replicate n b`, `firstn` → `List.take`, `nth` → `getD`.

    * `Z.land` has NO `Int` counterpart in Lean core (`Int.land` does not
      exist), so every statement below uses `PropExec.zland` — the same
      operation on the `toNat` representatives, exact for the non-negative
      operands used here (see `PropExec`'s notes).  The one `Int`
      power whose exponent is negative , `Z.ones k`, is spelled
      `2^k - 1` (`Nat` power, cast).

    * `2^k` / `2^64` are this tree's `((2 ^ k : Nat) : Int)` spelling (the
      one `Common/CatExec.lean`/`Common/MemSplit.lean` use); `omega` treats
      `((2^k : Nat) : Int)` and `(2 : Int)^k` as different atoms, so the two
      bridge lemmas [two_pow64_cast]/[two_pow_natCast] below restate one in
      the other's spelling.

    Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StreamSim
import LinuxSem.Common.MemSplit

namespace LinuxSem.Common.StartupAux

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.StoreOk
open LinuxSem.Common.StreamSim
open LinuxSem.Common.MemSplit

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-- The `FPState` instance the `PropExec` value lemmas carry an unused
    section argument for.  No statement below mentions the FP state. -/
local instance startup_fx : FPState := fx0

/-! ## Two spellings of a power of two -/

/-- the `Nat`-power cast of `2^k` is the `Int` power.  `omega`
    does not identify the two spellings on its own. -/
theorem two_pow_natCast (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k :=
  Int.natCast_pow 2 k

/-- `2^n` is positive at `Int`. -/
theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  rw [two_pow_natCast]
  exact Int.pow_pos (by decide)

/-- the same at `k = 64`. -/
theorem two_pow64_cast : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 :=
  two_pow_natCast 64

/-- `bv_unsigned` of a `Z_to_bv 64` literal
    in range, in this tree's `Nat`-power cast spelling. -/
theorem u_Z2bv' (z : Int) (h0 : 0 ≤ z) (h1 : z < ((2 ^ 64 : Nat) : Int)) :
    ((BitVec.ofInt 64 z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt]
  have h : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := two_pow64_cast
  rw [h, Int.emod_eq_of_lt h0 (by rw [← h]; exact h1), Int.toNat_of_nonneg h0]

/-- `bv_unsigned` of a `Z_to_bv n` literal is the value modulo
    `2^n`, in the `Nat`-cast
    spelling the `BitVec` lemmas use. -/
theorem toNat_ofInt_emod' {n : Nat} (z : Int) :
    ((BitVec.ofInt n z).toNat : Int) = z % ((2 ^ n : Nat) : Int) := by
  rw [BitVec.toNat_ofInt,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int n; omega))]

/-! =================================================================
    Registers
    ================================================================= -/

/-- The empty register file reads zero everywhere. -/
theorem getr_empty (r : reg) : getr (bvmap_empty : BvMap word) r = BitVec.ofInt 64 0 := by
  unfold getr
  by_cases h : bv_eqb r 0 = true
  · rw [ite_eq_left h]
    decide
  · rw [ite_eq_right h]
    simp [reg_get, bvmapGet, bvmap_get, bvmap_empty, w0]

/-! =================================================================
    Bit-level value facts
    ================================================================= -/

/-- the bits of
    the high mask `2^64 - 2^j` are exactly the positions `j <= i < 64`. -/
theorem testbit_mask_nat (j i : Nat) (hj : j ≤ 64) :
    Nat.testBit (2 ^ 64 - 2 ^ j) i = (decide (j ≤ i) && decide (i < 64)) := by
  have h2 : 2 ^ j * 2 ^ (64 - j) = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hm : 2 ^ 64 - 2 ^ j = 2 ^ j * (2 ^ (64 - j) - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, h2]
  rw [hm, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases hji : j ≤ i
  · have hd : decide (i - j < 64 - j) = decide (i < 64) := by
      rcases Nat.lt_or_ge i 64 with h | h
      · simp [h, show i - j < 64 - j from by omega]
      · simp [h, show ¬ (i - j < 64 - j) from by omega]
    simp [hji, hd]
  · simp [hji]

/-- bits at or above `j` do not
    see the low part `r < 2^j`. -/
theorem testbit_drop_low (q r j i : Nat) (hr : r < 2 ^ j) (hji : j ≤ i) :
    Nat.testBit (q * 2 ^ j + r) i = Nat.testBit (q * 2 ^ j) i := by
  have hsum : q * 2 ^ j + r = 2 ^ j * q + r := by rw [Nat.mul_comm q (2 ^ j)]
  have hmul : q * 2 ^ j = 2 ^ j * q := by rw [Nat.mul_comm q (2 ^ j)]
  rw [hsum, hmul, Nat.testBit_two_pow_mul_add (a := q) (b := r) (i := j) hr i,
    ite_eq_right (by omega), Nat.testBit_two_pow_mul]
  simp [hji]

/-- masking with
    `2^64 - 2^j` clears the low `j` bits, i.e. rounds `x` down to a multiple
    of `2^j`. -/
theorem and_highmask_nat (x j : Nat) (hj : j ≤ 64) (hx : x < 2 ^ 64) :
    x &&& (2 ^ 64 - 2 ^ j) = x - x % 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testbit_mask_nat j i hj]
  have hxr : x - x % 2 ^ j = 2 ^ j * (x / 2 ^ j) := by
    have h1 : 2 ^ j * (x / 2 ^ j) + x % 2 ^ j = x := Nat.div_add_mod x (2 ^ j)
    omega
  rw [hxr, Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases hji : j ≤ i
  · rw [Nat.sub_add_cancel hji]
    by_cases hi : i < 64
    · cases hb : Nat.testBit x i <;> simp [hji, hi, hb]
    · have hxi : x < 2 ^ i :=
        Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
      have hfalse : Nat.testBit x i = false := Nat.testBit_lt_two_pow hxi
      simp [hji, hi, hfalse]
  · cases hb : Nat.testBit x i <;> simp [hji, hb]

/-- An aligned value survives the high mask.   `land_align_mask`
    (`Z.land a (2^64 - 2^k) = a` under `a mod 2^k = 0`), at this tree's
    [zland] and with the `Nat`-power spelling of the mask. -/
theorem land_align_mask (a : Int) (k : Nat)
    (Ha : 0 ≤ a ∧ a < ((2 ^ 64 : Nat) : Int)) (Hk : k ≤ 64)
    (Hmod : a % ((2 ^ k : Nat) : Int) = 0) :
    zland a (((2 ^ 64 : Nat) : Int) - ((2 ^ k : Nat) : Int)) = a := by
  have hk64 : (2 ^ k : Nat) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) Hk
  have hsub : (((2 ^ 64 : Nat) : Int) - ((2 ^ k : Nat) : Int))
      = (((2 ^ 64 - 2 ^ k : Nat)) : Int) := (Int.natCast_sub hk64).symm
  have hxN : a.toNat < 2 ^ 64 := (Int.toNat_lt Ha.1).mpr Ha.2
  have hmodN : a.toNat % 2 ^ k = 0 := by
    have h : ((a.toNat % 2 ^ k : Nat) : Int) = 0 := by
      rw [Int.natCast_emod, Int.toNat_of_nonneg Ha.1]
      exact Hmod
    exact Int.ofNat_inj.mp (by simpa using h)
  rw [hsub]
  unfold zland
  rw [Int.toNat_natCast, and_highmask_nat a.toNat k Hk hxN, hmodN, Nat.sub_zero]
  exact Int.toNat_of_nonneg Ha.1

/-- `andi x, -16` on a 16-aligned value. -/
theorem v_andi_m16_aligned (x : word) (Hm : x.toNat % 16 = 0) :
    v_andi x (-16) = x := by
  have hw : bv_wrap 64 (-16) = ((2 ^ 64 : Nat) : Int) - ((2 ^ 4 : Nat) : Int) := by
    decide
  have hz : (x.toNat : Int) % ((2 ^ 4 : Nat) : Int) = 0 := by
    rw [← Int.natCast_emod, (by decide : (2 ^ 4 : Nat) = 16), Hm]
    rfl
  unfold v_andi
  rw [hw, land_align_mask (x.toNat : Int) 4 ⟨by omega, by omega⟩ (by decide) hz,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

/-- `andi x, -8` on an 8-aligned value. -/
theorem v_andi_m8_aligned (x : word) (Hm : x.toNat % 8 = 0) :
    v_andi x (-8) = x := by
  have hw : bv_wrap 64 (-8) = ((2 ^ 64 : Nat) : Int) - ((2 ^ 3 : Nat) : Int) := by
    decide
  have hz : (x.toNat : Int) % ((2 ^ 3 : Nat) : Int) = 0 := by
    rw [← Int.natCast_emod, (by decide : (2 ^ 3 : Nat) = 8), Hm]
    rfl
  unfold v_andi
  rw [hw, land_align_mask (x.toNat : Int) 3 ⟨by omega, by omega⟩ (by decide) hz,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

/-- `andi x, k` with `k + 1` a power of two dividing `x`: zero.

    `Z.ones k` (the `k` low bits set) is spelled `2^k - 1`; the
     hypothesis `0 <= k` is free here, `k` being a `Nat` index. -/
theorem land_low_zero (a : Int) (k : Nat) (Ha : 0 ≤ a)
    (Hmod : a % ((2 ^ k : Nat) : Int) = 0) :
    zland a (((2 ^ k : Nat) : Int) - 1) = 0 := by
  have hsub : (((2 ^ k : Nat) : Int) - 1) = (((2 ^ k - 1 : Nat)) : Int) := by
    rw [Int.natCast_sub (Nat.one_le_two_pow)]
    rfl
  have hmodN : a.toNat % 2 ^ k = 0 := by
    have h : ((a.toNat % 2 ^ k : Nat) : Int) = 0 := by
      rw [Int.natCast_emod, Int.toNat_of_nonneg Ha]
      exact Hmod
    exact Int.ofNat_inj.mp (by simpa using h)
  rw [hsub]
  unfold zland
  rw [Int.toNat_natCast, Nat.and_two_pow_sub_one_eq_mod, hmodN]
  rfl

/-- `andi x, 3` on a 4-aligned value: zero. -/
theorem v_andi_3_aligned (x : word) (Hm : x.toNat % 4 = 0) :
    v_andi x 3 = BitVec.ofInt 64 0 := by
  have hw : bv_wrap 64 3 = ((2 ^ 2 : Nat) : Int) - 1 := by decide
  have hz : (x.toNat : Int) % ((2 ^ 2 : Nat) : Int) = 0 := by
    rw [← Int.natCast_emod, (by decide : (2 ^ 2 : Nat) = 4), Hm]
    rfl
  unfold v_andi
  rw [hw, land_low_zero (x.toNat : Int) 2 (by omega) hz]

/-- A value 8-aligned has bit 2 clear: `Z.land a 4 = 0`. -/
theorem land_4_aligned8 (a : Int) (Ha : 0 ≤ a) (Hm : a % 8 = 0) :
    zland a 4 = 0 := by
  have h8 : ((a.toNat % 8 : Nat) : Int) = 0 := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg Ha]
    exact Hm
  have h7 : a.toNat &&& 7 = 0 := by
    have h := Nat.and_two_pow_sub_one_eq_mod a.toNat 3
    rw [show (2 ^ 3 - 1 : Nat) = 7 from by decide] at h
    rw [h]
    exact Int.ofNat_inj.mp (by simpa using h8)
  unfold zland
  rw [show ((4 : Int)).toNat = 4 from by decide,
    show (4 : Nat) = 7 &&& 4 from by decide, ← Nat.and_assoc, h7, Nat.zero_and]
  rfl

/-- `andi x, 4` on an 8-aligned value: zero. -/
theorem v_andi_4_aligned8 (x : word) (Hm : x.toNat % 8 = 0) :
    v_andi x 4 = BitVec.ofInt 64 0 := by
  have hw : bv_wrap 64 4 = 4 := by decide
  have hz : (x.toNat : Int) % 8 = 0 := by
    show (x.toNat : Int) % ((8 : Nat) : Int) = 0
    rw [← Int.natCast_emod, Hm]
    rfl
  unfold v_andi
  rw [hw, land_4_aligned8 (x.toNat : Int) (by omega) hz]

/-- `andi` of a 0/1-valued word with 1 is the identity. -/
theorem v_andi_1_of01 (z : Int) (Hz : z = 0 ∨ z = 1) :
    v_andi (BitVec.ofInt 64 z) 1 = BitVec.ofInt 64 z := by
  rcases Hz with rfl | rfl <;> decide

/-- a
    modulus by `2^k` (`k >= 2`) reduces further modulo 4. -/
theorem mod4_mod_pow2_gen (t : Int) (k j : Nat) (hjk : j ≤ k) :
    (t % (2 : Int) ^ k) % (2 : Int) ^ j = t % (2 : Int) ^ j := by
  rw [← two_pow_natCast k, ← two_pow_natCast j]
  refine Int.emod_emod_of_dvd t ⟨((2 ^ (k - j) : Nat) : Int), ?_⟩
  rw [← Int.natCast_mul]
  congr 1
  rw [← Nat.pow_add]
  congr 1
  omega

/-- Reducing a modulus by a divisor of the outer one.  
    `mod4_mod_pow2`. -/
theorem mod4_mod_pow2 (t : Int) (k : Nat) (hk : 2 ≤ k) :
    (t % (2 : Int) ^ k) % 4 = t % 4 := by
  rw [show (4 : Int) = (2 : Int) ^ 2 from by decide]
  exact mod4_mod_pow2_gen t k 2 hk

/-- `bv_swrap` only
    depends on its argument modulo the divisors of the half modulus. -/
theorem bv_swrap_emod (n : Nat) (z : Int) (k : Int)
    (hk : k ∣ ((2 ^ n : Nat) : Int)) (hk' : k ∣ ((2 ^ (n - 1) : Nat) : Int)) :
    bv_swrap n z % k = z % k := by
  unfold bv_swrap
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, Int.zero_dvd] at hk
    have hp := two_pow_pos_int n
    omega
  rw [Int.sub_emod]
  have hA : ((z + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int)) % k
      = (z + ((2 ^ (n - 1) : Nat) : Int)) % k := Int.emod_emod_of_dvd _ hk
  have hH : ((2 ^ (n - 1) : Nat) : Int) % k = 0 := Int.emod_eq_zero_of_dvd hk'
  rw [hA, hH, Int.sub_zero, Int.emod_emod, Int.add_emod, hH, Int.add_zero,
    Int.emod_emod]

/-- a value below the half modulus is
    fixed.  The bound `1 <= n` is this tree's `bv_swrap`-at-`0` caveat
    (`bv_swrap 0 z = -1`,); every call site below has
    `n >= 1`. -/
theorem bv_swrap_small (n : Nat) (hn : 1 ≤ n) (z : Int)
    (h : 0 ≤ z ∧ z < ((2 ^ (n - 1) : Nat) : Int)) : bv_swrap n z = z := by
  have hhalf : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    have hn1 : n = (n - 1) + 1 := by omega
    rw [hn1, Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]
    rfl
  have hpos : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) := by
    rw [Int.natCast_pos]
    exact Nat.two_pow_pos _
  unfold bv_swrap
  rw [hhalf, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- `negw rd, rs` (= `subw rd, x0, rs`) then `andi rd, rd, 3`: zero on a
    4-aligned value. -/
theorem negw_and3_aligned (x : word) (Hm : x.toNat % 4 = 0) :
    v_andi (v_subw (BitVec.ofInt 64 0) x) 3 = BitVec.ofInt 64 0 := by
  have h4_64 : (4 : Int) ∣ ((2 ^ 64 : Nat) : Int) := ⟨((2 ^ 62 : Nat) : Int), by decide⟩
  have h4_32 : (4 : Int) ∣ ((2 ^ 32 : Nat) : Int) := ⟨((2 ^ 30 : Nat) : Int), by decide⟩
  have h4_31 : (4 : Int) ∣ ((2 ^ (32 - 1) : Nat) : Int) := ⟨((2 ^ 29 : Nat) : Int), by decide⟩
  have hm4 : ((x.toNat : Int)) % 4 = 0 := by
    show (x.toNat : Int) % ((4 : Nat) : Int) = 0
    rw [← Int.natCast_emod, Hm]
    rfl
  have hneg : (0 - (x.toNat : Int)) % 4 = 0 := by
    rw [show (0 : Int) - (x.toNat : Int) = -(x.toNat : Int) from by omega, Int.neg_emod,
      ite_eq_left (Int.dvd_of_emod_eq_zero hm4)]
  have hmod : ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat : Int) % 4
      = 0 := by
    rw [toNat_ofInt_emod', Int.emod_emod_of_dvd _ h4_64,
      bv_swrap_emod 32 (0 - (x.toNat : Int)) 4 h4_32 h4_31, hneg]
  have hland : zland ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat : Int) 3
      = 0 := by
    have h1 : ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat &&& 3)
        = (BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat % 4 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod
        (BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat 2
    unfold zland
    rw [Int.toNat_natCast, show Int.toNat 3 = 3 from by decide, h1, Int.natCast_emod]
    exact hmod
  unfold v_andi v_subw
  rw [show ((BitVec.ofInt 64 0).toNat : Int) = 0 from by decide,
    show bv_wrap 64 3 = 3 from by decide, hland]

/-! =================================================================
    Narrow loads of a 64-bit slot / small values
    ================================================================= -/

/-- taking `k` bytes of `k`-and-more little-endian bytes. -/
theorem firstn_Z_to_le_bytes (k n : Nat) (z : Int) (Hk : k ≤ n) :
    (Z_to_le_bytes n z).take k = Z_to_le_bytes k z := by
  induction k generalizing n z with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      show BitVec.ofInt 8 z :: (Z_to_le_bytes n (z >>> 8)).take k
        = BitVec.ofInt 8 z :: Z_to_le_bytes k (z >>> 8)
      rw [ih n (z >>> 8) (by omega)]

/-- [word_to_le_bytes] inherits the prefix property. -/
theorem firstn_word_to_le_bytes (k n : Nat) (v : word) (Hk : k ≤ n) :
    (word_to_le_bytes n v).take k = word_to_le_bytes k v := by
  unfold word_to_le_bytes
  exact firstn_Z_to_le_bytes k n (v.toNat : Int) Hk

/-- [rdn] of the low `k` bytes of an 8-byte slot. -/
theorem rdn_low_bytes (segs : List Segment) (m : word → Option byte) (a v : word) (k : Nat)
    (Hk : k ≤ 8) (H : rdn segs m a 8 = some (word_to_le_bytes 8 v)) :
    rdn segs m a k = some (word_to_le_bytes k v) := by
  rw [rdn_firstn segs m 8 a (word_to_le_bytes 8 v) k H Hk,
    firstn_word_to_le_bytes k 8 v Hk]

/-- splitting one byte off the front of a little-endian read. -/
private theorem bytes_le_to_Nat_cons (b : byte) (rest : List byte) :
    bytes_le_to_Nat (b :: rest) = bytes_le_to_Nat rest * 256 + b.toNat := by
  have hb : b.toNat < 2 ^ 8 := b.isLt
  simp only [bytes_le_to_Nat]
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hb]
  simp [Nat.shiftLeft_eq]

/-- one limb of the modulus arithmetic below. -/
private theorem mod_mul_256_of (q r M : Nat) (hr : r < 256) (hM : 0 < M) :
    (256 * q + r) % (256 * M) = 256 * (q % M) + r := by
  have hqM : q % M < M := Nat.mod_lt _ hM
  have hrM : r < 256 * M := by omega
  rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt (by omega)]

/-- `Z_to_le_bytes`'s shift, at a `Nat`-valued argument. -/
private theorem int_shiftRight_8_natCast (m : Nat) :
    ((m : Int) >>> 8) = ((m / 256 : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow, ← Int.ofNat_ediv_ofNat]

/-- the low byte of a `Nat`, as `Z_to_le_bytes` encodes it. -/
private theorem toNat_ofInt_8_nat (m : Nat) :
    (BitVec.ofInt 8 (m : Int)).toNat = m % 256 := by
  rw [BitVec.toNat_ofInt, Int.toNat_emod (Int.natCast_nonneg m) (by decide)]
  rw [show ((2 ^ 8 : Nat) : Int) = (256 : Int) by decide]
  simp

/-- `x % (256 * M) = 256 * ((x / 256) % M) + x % 256`. -/
private theorem mod_mul_256 (x M : Nat) (hM : 0 < M) :
    x % (256 * M) = 256 * ((x / 256) % M) + x % 256 := by
  have h := mod_mul_256_of (x / 256) (x % 256) M (Nat.mod_lt _ (by decide)) hM
  rwa [Nat.div_add_mod] at h

/-- lean`, same proof as
    `Common/LibWritev.lean`'s): reading back `k` little-endian bytes of `m`
    gives `m` truncated to `8k` bits. -/
theorem bytes_le_to_Nat_Z_to_le_bytes (k m : Nat) :
    bytes_le_to_Nat (Z_to_le_bytes k (m : Int)) = m % 2 ^ (8 * k) := by
  induction k generalizing m with
  | zero => simp [Z_to_le_bytes, bytes_le_to_Nat, Nat.mod_one]
  | succ k ih =>
    rw [Z_to_le_bytes, int_shiftRight_8_natCast m]
    rw [bytes_le_to_Nat_cons, ih (m / 256), toNat_ofInt_8_nat]
    have hM : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    rw [Nat.mul_comm (2 ^ (8 * k)) (2 ^ 8)]
    rw [show 2 ^ 8 = 256 by decide, mod_mul_256 m (2 ^ (8 * k)) hM]
    omega

/-- A narrow load of a small word is the word's unsigned value. -/
theorem bytes_le_to_Z_4_small (v : word) (Hv : v.toNat < 2 ^ 32) :
    bytes_le_to_Z (word_to_le_bytes 4 v) = (v.toNat : Int) := by
  unfold bytes_le_to_Z word_to_le_bytes
  rw [bytes_le_to_Nat_Z_to_le_bytes]
  rw [show 8 * 4 = 32 by omega, Nat.mod_eq_of_lt Hv]

/-- `lw` of a value below `2^31` is the value. -/
theorem v_lw_small (v : word) (Hv : v.toNat < 2 ^ 31) : v_lw v = v := by
  have hsw : bv_swrap 32 (v.toNat : Int) = (v.toNat : Int) :=
    bv_swrap_small 32 (by decide) _ ⟨by omega, by omega⟩
  unfold v_lw
  rw [hsw, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

/-- [v_add x (Z_to_bv 64 k)] in offset form. -/
theorem v_add_lit_r (x : word) (k : Int) (Hk : 0 ≤ k ∧ k < ((2 ^ 64 : Nat) : Int)) :
    v_add x (BitVec.ofInt 64 k) = BitVec.ofInt 64 ((x.toNat : Int) + k) := by
  unfold v_add
  rw [u_Z2bv' k Hk.1 Hk.2]

/-- The same, literal on the left. -/
theorem v_add_lit_l (x : word) (k : Int) (Hk : 0 ≤ k ∧ k < ((2 ^ 64 : Nat) : Int)) :
    v_add (BitVec.ofInt 64 k) x = BitVec.ofInt 64 ((x.toNat : Int) + k) := by
  unfold v_add
  rw [u_Z2bv' k Hk.1 Hk.2, Int.add_comm]

/-- `slli x 3` then `add base x` then `addi 8`: the envp pointer. -/
theorem v_slli_lit (z : Int) (sh : Nat) (Hz : 0 ≤ z)
    (Hb : z * ((2 ^ sh : Nat) : Int) < ((2 ^ 64 : Nat) : Int)) :
    v_slli (BitVec.ofInt 64 z) sh = BitVec.ofInt 64 (z * ((2 ^ sh : Nat) : Int)) := by
  have hpow : (1 : Int) ≤ ((2 ^ sh : Nat) : Int) := by
    have h := two_pow_pos_int sh
    omega
  have hz64 : z < ((2 ^ 64 : Nat) : Int) := by
    have h1 : z * 1 ≤ z * ((2 ^ sh : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left hpow Hz
    omega
  unfold v_slli zshiftl
  rw [u_Z2bv' z Hz hz64, show ((sh : Int)).toNat = sh from Int.toNat_natCast sh]

/-! =================================================================
    Register-set inclusion, decided by computation
    ================================================================= -/

/-- `Bool`-decided subset inclusion between register lists. -/
theorem in_sub_bv (l1 l2 : List reg) (r : reg)
    (H : l1.all (fun x => l2.any (fun y => bv_eqb x y)) = true) (Hin : r ∈ l1) :
    r ∈ l2 := by
  induction l1 with
  | nil => simp at Hin
  | cons x l1 ih =>
    rw [List.all_cons, Bool.and_eq_true] at H
    rcases List.mem_cons.mp Hin with rfl | Hin
    · have hany : l2.any (fun y => bv_eqb r y) = true := H.1
      clear H ih
      induction l2 with
      | nil => simp at hany
      | cons y l2 ih2 =>
        rw [List.any_cons, Bool.or_eq_true] at hany
        rcases hany with hxy | hxy
        · exact List.mem_cons.mpr (Or.inl (by simpa [bv_eqb] using hxy))
        · exact List.mem_cons.mpr (Or.inr (ih2 hxy))
    · exact ih H.2 Hin

/-- A word is the literal of its unsigned value. -/
theorem Z_to_bv_u_eq (a : word) (z : Int) (H : z = (a.toNat : Int)) :
    BitVec.ofInt 64 z = a := by
  subst H
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

/-- The symmetric form. -/
theorem Z_to_bv_u_eq_sym (a : word) (z : Int) (H : z = (a.toNat : Int)) :
    a = BitVec.ofInt 64 z :=
  (Z_to_bv_u_eq a z H).symm
