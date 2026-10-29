/-
  * Common.Decimal — signed decimal rendering ("%d") as byte values

  [sdecZ v : List Int] is the ASCII rendering printf's "%d" produces for the
  C [int] value [v]: an optional '-' (45) followed by the decimal digits
  of |v|, most significant first, no leading zeros, "0" for 0.
  [udecZ] is the unsigned rendering ("%u").  Byte VALUES are unbounded [Int]
  (always in 48..57, or 45 for the sign); [to_bytes] converts to
  [byte = BitVec 8] and [udecZ_udec] bridges to [Common/NumPrint.udec].

  Pure and computable: [sdecZ (-3)] evaluates to [[45, 51]] by the kernel.

  TRUST BOUNDARY: image-INDEPENDENT proof library, no dependency on the
  machine semantics at all (pure list/`Int` facts, plus [byte = BitVec 8]
  for the rendered digit bytes).  It sits next to [Common/NumPrint], whose
  unsigned rendering it mirrors: the two files carry the same lemmas, the
  same shapes of statement and the same proof strategies, so a caller can
  switch between the value-level rendering ([Int] digit VALUES, used when
  the digits take part in further arithmetic) and the byte-level one
  ([byte] digit BYTES, used when they are written to memory) without
  re-deriving anything.  [udecZ_udec] is the bridge: [to_bytes (udecZ v)]
  is exactly [NumPrint.udec v].

  ENCODING NOTES
  ==============

  - Digit values are `Int`; `BitVec.ofInt 8 z` makes the byte, and `==` on
    `Bool` is the equality test, so the `if` conditions keep their shape.
    The sign test is the `Prop` `<` with its decidable instance, so
    `if v < 0` drives `sdecZ`.
  - `Int`'s power takes a `Nat` exponent, so `10 ^ f` is written
    `(10 : Int) ^ f` with `f : Nat`.
  - `lia` goals are `omega` goals, and the closed arithmetic goals
    (`pow10_20_gt'`) are `decide`.
  - A for-all over a list is spelled `∀ x ∈ l, P x`, the repo-wide
    convention: the Lean 4.31 core library has no `List.Forall`, and this
    is the same predicate in the same places.
  - Every declaration keeps the order the lemmas are used in (unlike
    `NumPrint`, whose `udec_aux_S` has to precede `udec_aux_fuel`), and the
    evaluation checks are named theorems rather than anonymous examples, as
    in `NumPrint`'s sanity block.
-/
import LinuxSem.Common.NumPrint

namespace LinuxSem.Common.Decimal

open LinuxSem.Riscv

/-! ## The rendering -/

/-- Digits of [v > 0], most significant first; [[]] for [v = 0].  24 fuel
    steps render any [v < 10^24] completely. -/
def udigits_aux (v : Int) (fuel : Nat) : List Int :=
  match fuel with
  | 0 => []
  | f + 1 =>
      if v == 0 then []
      else udigits_aux (v / 10) f ++ [48 + v % 10]

/-- The fuel `udecZ` uses: enough for any `2^64`. -/
def dec_fuel : Nat := 24

/-- "%u" -/
def udecZ (v : Int) : List Int :=
  if v == 0 then [48] else udigits_aux v dec_fuel

/-- "%d" -/
def sdecZ (v : Int) : List Int :=
  if v < 0 then 45 :: udecZ (- v) else udecZ v

/-- Conversion of byte values to machine bytes. -/
def to_bytes (l : List Int) : List byte := l.map (BitVec.ofInt 8)

/-! ## Examples -/

theorem sdecZ_ex0 : sdecZ 0 = [48] := by decide

theorem sdecZ_ex1 : sdecZ 7 = [55] := by decide

theorem sdecZ_ex2 : sdecZ (-3) = [45, 51] := by decide

theorem sdecZ_ex3 : sdecZ 1024 = [49, 48, 50, 52] := by decide

theorem sdecZ_ex4 : sdecZ (-12) = [45, 49, 50] := by decide

theorem udecZ_ex5 : udecZ 67108864 = [54, 55, 49, 48, 56, 56, 54, 52] := by
  decide

/-! ## Algebra (mirrors `Common/NumPrint`) -/

/-- The `S`-equation of `udigits_aux`, by computation.  It is declared
    before `udigits_aux_fuel`, which rewrites with it. -/
theorem udigits_aux_S (f : Nat) (v : Int) :
    udigits_aux v (f + 1) =
      (if v == 0 then []
       else udigits_aux (v / 10) f ++ [48 + v % 10]) :=
  rfl

/-- Fuel is immaterial as long as the value is below `10 ^ f`. -/
theorem udigits_aux_fuel (f g : Nat) (v : Int) (Hv0 : 0 ≤ v)
    (Hv : v < (10 : Int) ^ f) (Hfg : f ≤ g) : udigits_aux v g = udigits_aux v f := by
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
          rw [udigits_aux_S g v, udigits_aux_S f v, ih g (v / 10) Hn Hlt Hfg']

theorem udecZ_0 : udecZ 0 = [48] := rfl

/-- Single digit. -/
theorem udecZ_single (v : Int) (Hv : 1 ≤ v ∧ v ≤ 9) :
    udecZ v = [48 + v] := by
  obtain ⟨H1, H2⟩ := Hv
  have Hnz : v ≠ 0 := by omega
  unfold udecZ dec_fuel
  rw [ite_eq_right (by simpa using Hnz)]
  have Hfuel : udigits_aux v 24 = udigits_aux v 1 :=
    udigits_aux_fuel 1 24 v (by omega) (by
      have h : (10 : Int) ^ 1 = 10 := by decide
      omega) (by decide)
  rw [Hfuel, show (1 : Nat) = 0 + 1 from rfl, udigits_aux_S 0 v,
    ite_eq_right (by simpa using Hnz)]
  have Hd : v / 10 = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have Hm : v % 10 = v := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Hd, Hm]
  rfl

/-- The fuel allowance is generous: `2^64` is below `10^20`, so a single
    20-digit block covers every machine value. -/
theorem pow10_20_gt' : (2 : Int) ^ 64 < (10 : Int) ^ 20 := by
  decide

/-- Peel the least significant digit (any size: fuel 24 covers v < 10^24;
    we state it for v < 2^64, which is all any caller needs). -/
theorem udecZ_step (v : Int) (Hv10 : 10 ≤ v) (Hv64 : v < 2 ^ 64) :
    udecZ v = udecZ (v / 10) ++ [48 + v % 10] := by
  have Hnz : v ≠ 0 := by omega
  have Hdnz : v / 10 ≠ 0 := by
    have h1 : (1 : Int) ≤ v / 10 := by
      rw [Int.le_ediv_iff_mul_le (by decide : (0 : Int) < 10)]
      omega
    omega
  unfold udecZ dec_fuel
  rw [ite_eq_right (by simpa using Hnz), ite_eq_right (by simpa using Hdnz),
    show (24 : Nat) = 23 + 1 from rfl, udigits_aux_S 23 v,
    ite_eq_right (by simpa using Hnz)]
  have Hn : 0 ≤ v / 10 := Int.ediv_nonneg (by omega) (by decide)
  have Hlt : v / 10 < (10 : Int) ^ 23 := by
    rw [Int.ediv_lt_iff_lt_mul (by decide : (0 : Int) < 10)]
    have hm : (10 : Int) ^ 23 * 10 = (10 : Int) ^ 24 := by
      rw [← Int.pow_succ]
    rw [hm]
    have hpow : (2 : Int) ^ 64 < (10 : Int) ^ 24 := by decide
    omega
  rw [udigits_aux_fuel 23 24 (v / 10) Hn Hlt (by decide)]

/-- A rendering never has more digits than its fuel. -/
theorem udigits_aux_len (f : Nat) (v : Int) : (udigits_aux v f).length ≤ f := by
  induction f generalizing v with
  | zero => exact Nat.le_refl 0
  | succ f ih =>
      rw [udigits_aux_S f v]
      by_cases H : v == 0
      · simp [H]
      · have ih' := ih (v / 10)
        simp [H, List.length_append]
        omega

/-- A `2^64` value renders in at most 20 digits. -/
theorem udecZ_len_le (v : Int) (Hv0 : 0 ≤ v) (Hv : v < 2 ^ 64) :
    (udecZ v).length ≤ 20 := by
  have H20 : v < (10 : Int) ^ 20 := by
    have hpow := pow10_20_gt'
    omega
  by_cases Hnz : v = 0
  · subst Hnz
    simp [udecZ]
  · unfold udecZ dec_fuel
    rw [ite_eq_right (by simpa using Hnz),
      udigits_aux_fuel 20 24 v Hv0 H20 (by decide)]
    exact udigits_aux_len 20 v

/-- A rendering is never empty (`"0"` at the very least). -/
theorem udecZ_len_pos (v : Int) : 1 ≤ (udecZ v).length := by
  by_cases Hnz : v = 0
  · subst Hnz
    simp [udecZ]
  · unfold udecZ dec_fuel
    rw [ite_eq_right (by simpa using Hnz),
      show (24 : Nat) = 23 + 1 from rfl, udigits_aux_S 23 v,
      ite_eq_right (by simpa using Hnz)]
    simp [List.length_append]

/-- Every rendered byte value of [udecZ] is an ASCII digit. -/
theorem udigits_aux_digits (f : Nat) (v : Int) (Hv : 0 ≤ v) :
    ∀ d ∈ udigits_aux v f, 48 ≤ d ∧ d ≤ 57 := by
  induction f generalizing v with
  | zero => simp [udigits_aux]
  | succ f ih =>
      rw [udigits_aux_S f v]
      by_cases H : v == 0
      · simp [H]
      · have hH : ¬ ((v == 0) = true) := by simpa using H
        rw [ite_eq_right hH]
        intro d hd
        rw [List.mem_append] at hd
        rcases hd with hd | hd
        · exact ih (v / 10) (Int.ediv_nonneg Hv (by decide)) d hd
        · rw [List.mem_singleton] at hd
          subst hd
          have h1 : 0 ≤ v % 10 := Int.emod_nonneg v (by decide)
          have h2 : v % 10 < 10 := Int.emod_lt_of_pos v (by decide)
          omega

theorem udecZ_digits (v : Int) (Hv : 0 ≤ v) :
    ∀ d ∈ udecZ v, 48 ≤ d ∧ d ≤ 57 := by
  by_cases Hnz : v = 0
  · subst Hnz
    simp [udecZ]
  · unfold udecZ dec_fuel
    rw [ite_eq_right (by simpa using Hnz)]
    exact udigits_aux_digits 24 v Hv

/-- Signed rendering, by sign. -/
theorem sdecZ_nonneg (v : Int) (Hv : 0 ≤ v) : sdecZ v = udecZ v := by
  unfold sdecZ
  rw [ite_eq_right (by omega)]

theorem sdecZ_neg (v : Int) (Hv : v < 0) : sdecZ v = 45 :: udecZ (- v) := by
  unfold sdecZ
  rw [ite_eq_left Hv]

theorem sdecZ_len_pos (v : Int) : 1 ≤ (sdecZ v).length := by
  unfold sdecZ
  by_cases H : v < 0
  · rw [ite_eq_left H]
    simp only [List.length_cons]
    have Hpos := udecZ_len_pos (- v)
    omega
  · rw [ite_eq_right H]
    exact udecZ_len_pos v

/-- All byte values are in 0..255 (so [Z_to_bv 8] is injective on them). -/
theorem sdecZ_range (v : Int) : ∀ d ∈ sdecZ v, 0 ≤ d ∧ d < 256 := by
  unfold sdecZ
  by_cases H : v < 0
  · rw [ite_eq_left H]
    intro d hd
    rw [List.mem_cons] at hd
    rcases hd with hd | hd
    · subst hd
      omega
    · have Hd := udecZ_digits (- v) (by omega) d hd
      omega
  · rw [ite_eq_right H]
    intro d hd
    have Hd := udecZ_digits v (by omega) d hd
    omega

/-! ## Bridge to `Common/NumPrint.udec` -/

theorem udigits_aux_udec_aux (f : Nat) (v : Int) :
    to_bytes (udigits_aux v f) = NumPrint.udec_aux v f := by
  induction f generalizing v with
  | zero => rfl
  | succ f ih =>
      rw [udigits_aux_S f v, NumPrint.udec_aux_S f v]
      by_cases H : v == 0
      · simp [to_bytes, H]
      · have hH : ¬ ((v == 0) = true) := by simpa using H
        rw [ite_eq_right hH, ite_eq_right hH]
        have hsplit :
            to_bytes (udigits_aux (v / 10) f ++ [48 + v % 10]) =
              to_bytes (udigits_aux (v / 10) f) ++
                [BitVec.ofInt 8 (48 + v % 10)] := by
          simp [to_bytes]
        rw [hsplit, ih (v / 10)]

theorem udecZ_udec (v : Int) : to_bytes (udecZ v) = NumPrint.udec v := by
  by_cases Hnz : v = 0
  · subst Hnz
    rfl
  · unfold udecZ NumPrint.udec dec_fuel
    rw [ite_eq_right (by simpa using Hnz), ite_eq_right (by simpa using Hnz)]
    exact udigits_aux_udec_aux 24 v

end LinuxSem.Common.Decimal
