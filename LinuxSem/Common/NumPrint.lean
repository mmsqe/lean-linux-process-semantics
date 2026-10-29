/-
  * Common.NumPrint — unsigned decimal rendering spec and algebra.

  TRUST BOUNDARY: image-INDEPENDENT proof library, no dependency on the
  machine semantics at all (pure list/`Int` facts, plus [byte = BitVec 8]
  for the rendered digit bytes).

  [udec v] is the most-significant-digit-first ASCII decimal rendering of
  [v] (fixed at 24 fuel steps, comfortably more than the 20 digits needed
  for any [v < 2^64]).  Factored out of the number-printing examples
  (oob_read_bug_ns, which prints a decimal number followed by other bytes,
  and modprint_ns, whose whole output is one) so any future one reuses it
  instead of re-deriving the same ~100 lines.

  The rendered VALUE lives in unbounded [Int] (callers pass [bv_unsigned w]
  of a machine word) while the rendered digit BYTES are [byte = BitVec 8],
  spelled [BitVec.ofInt 8 (48 + v % 10)]:

  - [udec : Int -> List byte];
  - lemmas whose proof walks the value downward ([udec_aux_fuel],
    [udec_len_le]) carry an explicit [0 <= v] hypothesis ([Z] division
    truncates toward -infinity, so a negative value never reaches 0).
    Callers instantiate [v] with [bv_unsigned w], where it follows from
    [bv_unsigned_in_range].

  ENCODING NOTES
  ==============

  - Digit bytes are `BitVec.ofInt 8` of the digit value, and the equality
    test is `==` on `Bool`, so the `if` conditions keep their shape.
  - In Lean 4.31 `Int`'s `/` and `%` ARE the Euclidean division/modulus
    (`Int.ediv`/`Int.emod`), which for a positive divisor coincides with
    floor-based division on *every* sign — so the rendering is exact, not a
    non-negative-inputs-only reading.
  - `Int`'s power takes a `Nat` exponent, so `10 ^ f` is written
    `(10 : Int) ^ f`.
  - `lia` goals are `omega` goals, and the closed arithmetic goals
    (`pow10_20_gt`) are `decide`.
  - `udec_aux_S` is declared BEFORE `udec_aux_fuel`: Lean has no forward
    references, and `udec_aux_fuel` rewrites with the `S`-equation.  Every
    other declaration keeps the order its proofs need.
  - `udec_of_ne_zero` unfolds `udec` at a non-zero value, the step the fuel
    lemmas need; it is the one declaration here with no separate
    counterpart, and it exists so that step is a rewrite rather than
    repeated inline case work.
-/
import LinuxSem.LinuxProcessSem.BvBase

namespace LinuxSem.Common.NumPrint

open LinuxSem.Riscv

/-! ## The rendering -/

/-- Unsigned decimal rendering, most-significant digit first. -/
def udec_aux (v : Int) (fuel : Nat) : List byte :=
  match fuel with
  | 0 => []
  | f + 1 =>
      if v == 0 then []
      else udec_aux (v / 10) f ++ [BitVec.ofInt 8 (48 + v % 10)]

/-- Unsigned decimal rendering of a value (the single digit `0` for zero,
    24 fuel steps otherwise). -/
def udec (v : Int) : List byte :=
  if v == 0 then [BitVec.ofInt 8 48] else udec_aux v 24

/-- Unfold `udec` at a non-zero value.  The condition is a `Bool`, so the
    bridge from `v ≠ 0` goes through `simpa`. -/
theorem udec_of_ne_zero (v : Int) (H : v ≠ 0) : udec v = udec_aux v 24 := by
  unfold udec
  rw [ite_eq_right (by simpa using H)]

/-! ## `udec` decomposition (pure) -/

theorem udec_aux_S (f : Nat) (v : Int) :
    udec_aux v (f + 1) =
      (if v == 0 then []
       else udec_aux (v / 10) f ++ [BitVec.ofInt 8 (48 + v % 10)]) :=
  rfl

theorem udec_aux_fuel (f g : Nat) (v : Int) (Hv0 : 0 ≤ v)
    (Hv : v < (10 : Int) ^ f) (Hfg : f ≤ g) : udec_aux v g = udec_aux v f := by
  induction f generalizing g v with
  | zero =>
      have hv : v = 0 := by
        have h0 : (10 : Int) ^ 0 = 1 := by decide
        omega
      subst hv
      cases g with
      | zero => rfl
      | succ g => rfl
  | succ f ih =>
      cases g with
      | zero => exact absurd Hfg (by omega)
      | succ g =>
          have Hfg' : f ≤ g := by omega
          have Hn : 0 ≤ v / 10 := Int.ediv_nonneg Hv0 (by decide)
          have Hlt : v / 10 < (10 : Int) ^ f := by
            rw [Int.ediv_lt_iff_lt_mul (by decide : (0 : Int) < 10)]
            have Hv' : v < (10 : Int) ^ f * 10 := by
              simpa [Int.pow_succ] using Hv
            exact Hv'
          rw [udec_aux_S g v, udec_aux_S f v, ih g (v / 10) Hn Hlt Hfg']

theorem pow10_20_gt : (2 : Int) ^ 64 < (10 : Int) ^ 20 := by
  decide

/-- Single digit. -/
theorem udec_single (v : Int) (Hv : 1 ≤ v ∧ v ≤ 9) :
    udec v = [BitVec.ofInt 8 (48 + v)] := by
  obtain ⟨H1, H2⟩ := Hv
  have Hnz : v ≠ 0 := by omega
  have Hfuel : udec_aux v 24 = udec_aux v 1 :=
    udec_aux_fuel 1 24 v (by omega) (by
      have h : (10 : Int) ^ 1 = 10 := by decide
      omega) (by decide)
  rw [udec_of_ne_zero v Hnz, Hfuel, show (1 : Nat) = 0 + 1 from rfl,
    udec_aux_S 0 v, ite_eq_right (by simpa using Hnz)]
  have Hd : v / 10 = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have Hm : v % 10 = v := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Hd, Hm]
  rfl

/-- Peel the least significant digit. -/
theorem udec_step (v : Int) (Hv10 : 10 ≤ v) (Hv64 : v < 2 ^ 64) :
    udec v = udec (v / 10) ++ [BitVec.ofInt 8 (48 + v % 10)] := by
  have Hnz : v ≠ 0 := by omega
  have Hdnz : v / 10 ≠ 0 := by
    intro H
    have Hle : v / 10 ≤ 0 := by omega
    have H10 := (Int.ediv_le_iff_le_mul (k := 10) (x := v) (y := 0)
      (by decide : (0 : Int) < 10)).mp Hle
    omega
  rw [udec_of_ne_zero v Hnz, udec_of_ne_zero (v / 10) Hdnz,
    show (24 : Nat) = 23 + 1 from rfl, udec_aux_S 23 v,
    ite_eq_right (by simpa using Hnz)]
  have Hn : 0 ≤ v / 10 := Int.ediv_nonneg (by omega) (by decide)
  have Hlt : v / 10 < (10 : Int) ^ 23 := by
    rw [Int.ediv_lt_iff_lt_mul (by decide : (0 : Int) < 10)]
    have hm : (10 : Int) ^ 23 * 10 = (10 : Int) ^ 24 := by
      rw [← Int.pow_succ]
    rw [hm]
    have hpow : (2 : Int) ^ 64 < (10 : Int) ^ 24 := by decide
    omega
  rw [udec_aux_fuel 23 24 (v / 10) Hn Hlt (by decide)]

theorem udec_aux_len (f : Nat) (v : Int) : (udec_aux v f).length ≤ f := by
  induction f generalizing v with
  | zero => exact Nat.le_refl 0
  | succ f ih =>
      rw [udec_aux_S f v]
      by_cases H : v == 0
      · simp [H]
      · have ih' := ih (v / 10)
        simp [H, List.length_append]
        omega

theorem udec_len_le (v : Int) (Hv0 : 0 ≤ v) (Hv : v < 2 ^ 64) :
    (udec v).length ≤ 20 := by
  have H20 : v < (10 : Int) ^ 20 := by
    have hpow : (2 : Int) ^ 64 < (10 : Int) ^ 20 := pow10_20_gt
    omega
  by_cases Hnz : v = 0
  · subst Hnz
    simp [udec]
  · rw [udec_of_ne_zero v Hnz,
      udec_aux_fuel 20 24 v Hv0 H20 (by decide)]
    exact udec_aux_len 20 v

theorem udec_len_pos (v : Int) : 1 ≤ (udec v).length := by
  by_cases Hnz : v = 0
  · subst Hnz
    simp [udec]
  · rw [udec_of_ne_zero v Hnz,
      show (24 : Nat) = 23 + 1 from rfl, udec_aux_S 23 v,
      ite_eq_right (by simpa using Hnz)]
    simp [List.length_append]

/-! ## Sanity checks

    These evaluation checks pin the rendering (ASCII `'0' .. '9'` = 48 .. 57). -/

example : udec 0 = [BitVec.ofInt 8 48] := by decide

example : udec 7 = [BitVec.ofInt 8 55] := by decide

example : udec 42 = [BitVec.ofInt 8 52, BitVec.ofInt 8 50] := by decide

example : udec 100 =
    [BitVec.ofInt 8 49, BitVec.ofInt 8 48, BitVec.ofInt 8 48] := by
  decide

end LinuxSem.Common.NumPrint
