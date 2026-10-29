/-

  * Common.StringsSpec — image-independent pure definitions for musl
    string-routine summaries (`memset`, `memcmp`)

    - `cb c`  : the byte `memset` stores = low byte of the value register `c`;
      `cv c`  : its numeric value; `cb_zero` : `cb (Z_to_bv 64 0) = Z_to_bv 8 0`.
    - `memcmp_res bl br` : what `memcmp`/`bcmp` return in a0 (as a Z; the
      register holds `Z_to_bv 64 (memcmp_res bl br)`): the difference of the
      first mismatching byte pair, 0 if none.  `memcmp_a0_zero_iff` : the
      register is `Z_to_bv 64 0` iff `bl = br`.

   also imports `BvBase`, `RiscvSemantics`,
  `MemImageType` and `Common.PropExec`.  Only `BvBase` is needed here: the
  definitions below are pure (`word`/`byte` and `BitVec.ofInt`), and every
  lemma is arithmetic over `toNat`/`toInt`.  In particular nothing of the
  `triple`-style vocabulary of `PropExec` is used — the single 
  reference to `PropExec` is `u8_range` (the `0 <= bv_unsigned b < 256`
  fact for a byte) inside `memcmp_res_range`.  `PropExec` is not yet green
  in this module, so instead of duplicating `u8_range` the byte bound is
  taken straight from the structure invariant `BitVec.isLt`
  (`b.toNat < 2^8 = 256`).
  `Z` is `Int`, `list byte` is `List byte`, and the
  `Z`-equality test `(bv_unsigned x =? bv_unsigned y)%Z` is `x = y`: two
  bitvectors are equal iff their unsigned readings are (`BitVec.toNat_inj`),
  so the computation is the same and stays decidable/computable.
  `bv_unsigned c mod 256` (`Int` mod) is kept verbatim
  as `cv`, so `cv_range` is `Int.emod_nonneg`/`Int.emod_lt_of_pos`, and the
  two `Z_to_bv` lemmas (`cb_cv`, `cb_lit`) are the single fact that
  `BitVec.ofInt n` only depends on the argument modulo `2^n`
  (`ofInt_emod_congr` below), with `Int.emod_emod_of_dvd` doing the
  truncation `64 -> 8` in `cb_lit`.  (`Z_to_bv` is `BitVec.ofInt` throughout, and
  every `omega` step is plain arithmetic on `Nat`/`Int`.)
-/
import LinuxSem.LinuxProcessSem.BvBase

namespace LinuxSem.Common.StringsSpec

open LinuxSem.Riscv (word byte)

/-! ## Helper: `Z_to_bv n` only sees the argument modulo `2^n` -/

/-- `BitVec.ofInt n` depends only on the residue of
    its argument modulo `2^n`.  (`BitVec.toNat_ofInt` says the `toNat` view
    is exactly that residue, so equal residues give equal words.)

    this has no  counterpart — it is the single
    bitvector fact the two `Z_to_bv` lemmas below need, kept `private` so
    the public surface stays exactly the one. -/
private theorem ofInt_emod_congr {n : Nat} {z w : Int}
    (h : z % (2 ^ n : Nat) = w % (2 ^ n : Nat)) :
    BitVec.ofInt n z = BitVec.ofInt n w := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofInt, BitVec.toNat_ofInt, h]

/- =====================================================================
   ** memset's fill byte
   ===================================================================== -/

/-- The byte `memset` stores for the 64-bit value register `c`: the low byte
    of `c`. -/
def cb (c : word) : byte := BitVec.ofInt 8 (c.toNat : Int)

/-- The numeric value of that byte. -/
def cv (c : word) : Int := (c.toNat : Int) % 256

theorem cv_range (c : word) : 0 ≤ cv c ∧ cv c < 256 := by
  have h1 : 0 ≤ (c.toNat : Int) % 256 := Int.emod_nonneg _ (by decide)
  have h2 : (c.toNat : Int) % 256 < 256 := Int.emod_lt_of_pos _ (by decide)
  exact ⟨h1, h2⟩

theorem cb_cv (c : word) : BitVec.ofInt 8 (cv c) = cb c := by
  refine ofInt_emod_congr ?_
  exact Int.emod_emod (c.toNat : Int) 256

/-- the common case `memset(p, 0, n)` (also holds by conversion) -/
theorem cb_zero : cb (BitVec.ofInt 64 0) = BitVec.ofInt 8 0 := by
  simp [cb]

theorem cb_lit (z : Int) : cb (BitVec.ofInt 64 z) = BitVec.ofInt 8 z := by
  unfold cb
  have hw : ((BitVec.ofInt 64 z).toNat : Int) = z % (2 ^ 64 : Nat) := by
    rw [BitVec.toNat_ofInt]
    exact Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))
  rw [hw]
  refine ofInt_emod_congr ?_
  have hdvd : ((2 ^ 8 : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) :=
    ⟨((2 ^ 56 : Nat) : Int), by decide⟩
  rw [Int.emod_emod_of_dvd z hdvd]

/- =====================================================================
   ** memcmp's result
   ===================================================================== -/

/-- What `memcmp`/`bcmp` return in a0, as an `Int`: the difference of the
    first mismatching byte pair, `0` if there is none. -/
def memcmp_res : List byte → List byte → Int
  | x :: bl', y :: br' =>
      if x = y then memcmp_res bl' br' else (x.toNat : Int) - (y.toNat : Int)
  | _, _ => 0

theorem memcmp_res_range (bl br : List byte) :
    -255 ≤ memcmp_res bl br ∧ memcmp_res bl br ≤ 255 := by
  induction bl generalizing br with
  | nil => cases br <;> simp [memcmp_res]
  | cons x bl ih =>
    cases br with
    | nil => simp [memcmp_res]
    | cons y br =>
      have hx : x.toNat < 256 := x.isLt
      have hy : y.toNat < 256 := y.isLt
      by_cases hxy : x = y
      · subst hxy
        have hstep : memcmp_res (x :: bl) (x :: br) = memcmp_res bl br := by
          simp [memcmp_res]
        rw [hstep]
        exact ih br
      · have hstep : memcmp_res (x :: bl) (y :: br) =
            (x.toNat : Int) - (y.toNat : Int) := by
          simp [memcmp_res, hxy]
        rw [hstep]
        constructor <;> omega

theorem memcmp_res_zero_iff (bl br : List byte) (hlen : br.length = bl.length) :
    (memcmp_res bl br = 0 ↔ bl = br) := by
  induction bl generalizing br with
  | nil =>
    cases br with
    | nil => simp [memcmp_res]
    | cons y br => simp at hlen
  | cons x bl ih =>
    cases br with
    | nil => simp at hlen
    | cons y br =>
      have hlen' : br.length = bl.length := by
        simp only [List.length_cons] at hlen
        omega
      by_cases hxy : x = y
      · subst hxy
        have hstep : memcmp_res (x :: bl) (x :: br) = memcmp_res bl br := by
          simp [memcmp_res]
        rw [hstep, ih br hlen']
        simp
      · have hne : (x.toNat : Int) - (y.toNat : Int) ≠ 0 := by
          intro h
          apply hxy
          apply BitVec.toNat_inj.mp
          have hx : x.toNat < 256 := x.isLt
          have hy : y.toNat < 256 := y.isLt
          omega
        have hstep : memcmp_res (x :: bl) (y :: br) =
            (x.toNat : Int) - (y.toNat : Int) := by
          simp [memcmp_res, hxy]
        rw [hstep]
        simp [hne, hxy]

theorem memcmp_res_refl (bl : List byte) : memcmp_res bl bl = 0 :=
  (memcmp_res_zero_iff bl bl rfl).mpr rfl

/-- The register-level test the callers perform (`beqz a0`/`bnez a0`). -/
theorem memcmp_a0_zero_iff (bl br : List byte) (hlen : br.length = bl.length) :
    (BitVec.ofInt 64 (memcmp_res bl br) = BitVec.ofInt 64 0 ↔ bl = br) := by
  rw [← memcmp_res_zero_iff bl br hlen]
  have hv := memcmp_res_range bl br
  have hge : -(2 : Int) ^ (64 - 1) ≤ memcmp_res bl br := by
    have hpow : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
    omega
  have hlt : memcmp_res bl br < (2 : Int) ^ (64 - 1) := by
    have hpow : (2 : Int) ^ (64 - 1) = 9223372036854775808 := by decide
    omega
  have key : (BitVec.ofInt 64 (memcmp_res bl br)).toInt = memcmp_res bl br :=
    BitVec.toInt_ofInt_eq_self (by decide) hge hlt
  have h0 : (BitVec.ofInt 64 0).toInt = 0 := by decide
  rw [← BitVec.toInt_inj, key, h0]

theorem memcmp_u_nonzero (bl br : List byte) (hlen : br.length = bl.length)
    (hne : bl ≠ br) : (BitVec.ofInt 64 (memcmp_res bl br)).toNat ≠ 0 := by
  intro hu
  apply hne
  apply (memcmp_a0_zero_iff bl br hlen).mp
  exact BitVec.toNat_inj.mp (by rw [hu]; simp)

/-! ## Sanity checks

    The  file has no `vm_compute` goals; these pin the two
    definitions that are actually evaluated at run time (the fill byte and
    the `memcmp` result). -/

example : cb (BitVec.ofInt 64 0) = BitVec.ofInt 8 0 := cb_zero

example : cb (BitVec.ofInt 64 0x1234) = (0x34 : byte) := by decide

example : cv (BitVec.ofInt 64 0x1234) = 0x34 := by decide

example : (memcmp_res [1, 2] [1, 3] : Int) = -1 := by decide

example : (memcmp_res [1, 2] [1, 2] : Int) = 0 := by decide

example : (memcmp_res [255] [0] : Int) = 255 := by decide

example : (memcmp_res [0, 9] [0] : Int) = 0 := by decide

example : cb (BitVec.ofInt 64 (-1)) = (0xFF : byte) := by decide

example : (memcmp_res [5] [7] : Int) = -2 := by decide

-- the wrap-around test the callers do: a negative difference is still `ne 0`
example : BitVec.ofInt 64 (memcmp_res [1, 2] [1, 2]) = 0 := by decide

example : ¬ (BitVec.ofInt 64 (memcmp_res [1, 2] [1, 3]) = 0) := by decide

end LinuxSem.Common.StringsSpec
