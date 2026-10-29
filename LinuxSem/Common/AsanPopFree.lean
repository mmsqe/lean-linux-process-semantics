/-
  * Common.AsanPopFree — the `PopulateFreeArray` free-array fill loop of the
    ASan primary allocator, as a MODEL-FREE `msteps` contract.

  [PopulateFreeArray] free-array fill loop summary (image-parametric Section
  over the 8 instruction words at p..p+28) + the APSX-style routine contract
  `popfree_spec` consumed by the `PX XPopFree` closer.

  The loop (`i` = x10, `e` = x11 = free_array + 4*total_freed, `c` = x12 =
  chunk offset cursor, `s` = x21 = chunk size, `n` = x19 = new_chunks):
<<
    p+0 : srli x14,x12,4        x14 = c >> 4               (compact pointer)
    p+4 : xori x15,x10,-1       x15 = ~i
    p+8 : addi x10,x10,1        i++
    p+12: slli x15,x15,2
    p+16: add  x15,x11,x15      x15 = e - 4*(i_old+1)
    p+20: sw   x14,0(x15)       free_array[total_freed-1-i_old] = c >> 4
    p+24: add  x12,x12,x21      c += s
    p+28: bltu x10,x19,p        while (i < n)
>>
  Contract `popfree_loop_run`: from the head with `i < n` the loop exits at
  `p+32` with x10 = n, x12 = c + (n-i)*s, x14/x15 = last value/address,
  all other registers unchanged, memory = `pf_mem mem e c s i (n-i)`;
  `pf_mem_rdn`/`pf_mem_cell` (cells = 4-byte LE values
  `(c + (k-1-j)*s)/16`, j counted upwards from the lowest address
  `e - 4(i+k)`), `pf_cell_linear` and `pf_mem_frame` describe it.

  APSX-style contract: `popfree_spec SEGS p` with the memory in `wbytes`
  form over `pf_bytes c s k` (lowest address first);
  `popfree_spec_of_code` derives it from the eight `fetch_word` facts;
  read-back lemmas `pf_bytes_length`, `pf_bytes_cell`, `pf_bytes_nth`.
 The
    Lean `section` below is only this tree's grouping device.
 `red_if` (reduce a closed
    `if bv_eqb a b` by `vm_compute`) has no Lean counterpart: this tree's
    step lemmas deliver the `if bv_eqb rd 0` already reduced at the literal
    register numbers (`show bv_eqb (14 : reg) 0 = false from by decide`
    followed by `Bool.false_eq_true, ite_false`).  It deliberately does
    not reuse `SeqExec.getr_resolve`, whose final `getr_nz` step would
    rewrite `getr regs r` (the shape the loop facts are stated about) into
    `reg_get regs r`.
  * glue : `toNat_four_mul` (`Z.to_nat (4j) = 4 * Z.to_nat
    j`), `natSucc_sub_one`, `toNat_succ_int` (`((a+1).toNat : Int) =
    a.toNat + 1`, the `2^64`-as-`Nat` spelling of `PropExec.u_add1`),
    `bv_unsigned_ofInt` (`bv_unsigned (ofInt n z) = z % 2^n`),
    `v_xori_m1` (`v_xori x (-1) = ~~~x`) and `znot_Z_to_bv`
    (`~~~(ofInt 64 i) = ofInt 64 (2^64 - 1 - i)`), plus the `gr` macro.
  * `Z.ltb (i+1) n` (a `Bool`) becomes the propositional `(i + 1) < n` in
    `pf_iter`'s post-state, exactly as elsewhere in this tree; the branch
    case split then closes with `decide_eq_true` / `decide_eq_false`.
  * As `Common/CatExec.lean` records,
    `omega` gives up on an `Int`-valued sum compared against the literal
    `2^64`; every `2^64` bound in this file therefore goes through the
    `Nat` reshaping `CatExec.nat_sum_le_two64` / `CatExec.int_sum_le_of_nat`
    and `Nat`-level length facts, and only the statement's boundary is
    `Int`.  Two further traps met here: `omega` does not know
    `(b :: l).length ≥ 1` (state it with `simp`), and it needs
    `Int.add_mul` before it can see through `(a + b) * c`.
 `lake env lean
  LinuxSem/Common/AsanPopFree.lean` is silent.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.SymExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.LibMaskBits
import LinuxSem.Common.RocqSpelling
import LinuxSem.Common.AxSymExec3
import LinuxSem.Common.AxSymExec3Sound

namespace LinuxSem.Common.AsanPopFree

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StoreOk
open LinuxSem.Common.SymExec
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymExec3Sound (rdn_pointwise)

/-- `Local Instance asanreflect_fx : PropExec.FPState :=
    PropExec.fx0`. -/
local instance asanpopfree_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! ## The eight loop words and their decodes

    The eight instruction words of the loop (identical in the asan and both
    images). -/

/-- `srli x14,x12,4` -/
def PW0 : BitVec 32 := 0x00465713
/-- `xori x15,x10,-1` -/
def PW1 : BitVec 32 := 0xfff54793
/-- `addi x10,x10,1` -/
def PW2 : BitVec 32 := 0x00150513
/-- `slli x15,x15,2` -/
def PW3 : BitVec 32 := 0x00279793
/-- `add x15,x11,x15` -/
def PW4 : BitVec 32 := 0x00f587b3
/-- `sw  x14,0(x15)` -/
def PW5 : BitVec 32 := 0x00e7a023
/-- `add x12,x12,x21` -/
def PW6 : BitVec 32 := 0x01560633
/-- `bltu x10,x19,-28` -/
def PW7 : BitVec 32 := 0xff3562e3

theorem PD0 : decodeAny PW0 = some (Instr.shiftImm .SRL 14 12 4, 4) := by decide
theorem PD1 : decodeAny PW1 = some (Instr.opImm .XOR 15 10 4095, 4) := by decide
theorem PD2 : decodeAny PW2 = some (Instr.opImm .ADD 10 10 1, 4) := by decide
theorem PD3 : decodeAny PW3 = some (Instr.shiftImm .SLL 15 15 2, 4) := by decide
theorem PD4 : decodeAny PW4 = some (Instr.op .ADD 15 11 15, 4) := by decide
theorem PD5 : decodeAny PW5 = some (Instr.store .SZ4 15 14 0, 4) := by decide
theorem PD6 : decodeAny PW6 = some (Instr.op .ADD 12 12 21, 4) := by decide
theorem PD7 : decodeAny PW7 = some (Instr.branch .LTU 10 19 8164, 4) := by decide

/-! ## The memory after `k` more iterations -/

/-- The memory after `k` more iterations from index `i` with value cursor `c`
    (oldest write first): iteration `i` writes the 4 LE bytes of `c/16` at
    `e - 4(i+1)`. -/
def pf_mem (mem : word → Option byte) (e c s i : Int) : Nat → word → Option byte
  | 0 => mem
  | k + 1 =>
    pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
              (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) e (c + s) s (i + 1) k

/-- The same bytes as ONE list, lowest address first: `k` cells, cell `j`
    (byte offset `4j`) = u32 LE of `(c + (k-1-j)*s)/16`. -/
def pf_bytes (c s : Int) : Nat → List byte
  | 0 => []
  | k + 1 => Z_to_le_bytes 4 ((c + (k : Int) * s) / 16) ++ pf_bytes c s k

theorem pf_bytes_length (c s : Int) (k : Nat) : (pf_bytes c s k).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (Z_to_le_bytes 4 ((c + (k : Int) * s) / 16) ++ pf_bytes c s k).length = 4 * (k + 1)
    rw [List.length_append, CatExec.length_Z_to_le_bytes, ih]
    omega

/-- glue: `Z.of_nat (k+1) - 1 = Z.of_nat k`. -/
theorem natSucc_sub_one (k : Nat) : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by
  push_cast
  omega

/-- `Z.to_nat` of `4 * j` for a non-negative `j` (list indices are `Nat`
    in this tree). -/
theorem toNat_four_mul (j : Int) (Hj : 0 ≤ j) : (4 * j).toNat = 4 * j.toNat := by
  rw [Int.toNat_mul (by decide) Hj]
  rfl

/-- Byte `t` of cell `j` (cells counted upwards from the lowest address).
-/
theorem pf_bytes_nth (c s : Int) (k : Nat) :
    ∀ (j : Int) (t : Nat), 0 ≤ j → j < (k : Int) → t < 4 →
      (pf_bytes c s k).getD ((4 * j).toNat + t) (Z_to_bv 8 0)
        = (Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16)).getD t (Z_to_bv 8 0) := by
  induction k with
  | zero =>
    intro j t Hj0 Hjk _
    omega
  | succ k ih =>
    intro j t Hj0 Hjk Ht
    show ((Z_to_le_bytes 4 ((c + (k : Int) * s) / 16) ++ pf_bytes c s k).getD
        ((4 * j).toNat + t) (Z_to_bv 8 0)) = _
    rw [List.getD_eq_getElem?_getD]
    by_cases hj0 : j = 0
    · subst hj0
      rw [Int.mul_zero, Int.toNat_zero, Nat.zero_add]
      have hlen : t < (Z_to_le_bytes 4 ((c + (k : Int) * s) / 16)).length := by
        rw [CatExec.length_Z_to_le_bytes]; exact Ht
      have hk : ((k + 1 : Nat) : Int) - 1 - 0 = (k : Int) := by
        rw [natSucc_sub_one]; omega
      rw [List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD, hk]
    · have hpos : 0 ≤ j := by omega
      have hjtoNat : 1 ≤ j.toNat := by
        have h1 : (1 : Int) ≤ (j.toNat : Int) := by
          rw [Int.toNat_of_nonneg hpos]; omega
        omega
      rw [toNat_four_mul j hpos]
      have hge : (Z_to_le_bytes 4 ((c + (k : Int) * s) / 16)).length ≤ 4 * j.toNat + t := by
        rw [CatExec.length_Z_to_le_bytes]; omega
      have hsub : 4 * j.toNat + t - (Z_to_le_bytes 4 ((c + (k : Int) * s) / 16)).length
          = (4 * (j - 1)).toNat + t := by
        rw [CatExec.length_Z_to_le_bytes, toNat_four_mul (j - 1) (by omega)]
        have h1 : (j - 1).toNat = j.toNat - 1 := by
          rw [Int.toNat_sub'' hpos (by decide)]; rfl
        omega
      have hk : ((k + 1 : Nat) : Int) - 1 = (k : Int) := natSucc_sub_one k
      have harith : ((k : Int) - 1 - (j - 1)) = ((k : Int) - j) := by omega
      rw [List.getElem?_append_right hge, hsub, ← List.getD_eq_getElem?_getD,
        ih (j - 1) t (by omega) (by omega) Ht, hk, harith]


/-- Cell `j` as a 4-byte slice.   `pf_bytes_cell`. -/
theorem pf_bytes_cell (c s : Int) (k : Nat) :
    ∀ (j : Int), 0 ≤ j → j < (k : Int) →
      ((pf_bytes c s k).drop (4 * j).toNat).take 4
        = Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16) := by
  induction k with
  | zero =>
    intro j Hj0 Hjk
    omega
  | succ k ih =>
    intro j Hj0 Hjk
    show ((Z_to_le_bytes 4 ((c + (k : Int) * s) / 16) ++ pf_bytes c s k).drop
        (4 * j).toNat).take 4 = _
    by_cases hj0 : j = 0
    · subst hj0
      rw [Int.mul_zero, Int.toNat_zero, List.drop_zero]
      rw [List.take_append_of_le_length (by rw [CatExec.length_Z_to_le_bytes]; omega)]
      rw [List.take_of_length_le (by rw [CatExec.length_Z_to_le_bytes]; omega)]
      rw [show ((k + 1 : Nat) : Int) - 1 - 0 = (k : Int) by rw [natSucc_sub_one]; omega]
    · have hpos : 0 ≤ j := by omega
      have hjtoNat : 1 ≤ j.toNat := by
        have h1 : (1 : Int) ≤ (j.toNat : Int) := by
          rw [Int.toNat_of_nonneg hpos]; omega
        omega
      rw [toNat_four_mul j hpos]
      rw [List.drop_append,
        List.drop_eq_nil_of_le (by rw [CatExec.length_Z_to_le_bytes]; omega)]
      rw [List.nil_append]
      have hsub : 4 * j.toNat - (Z_to_le_bytes 4 ((c + (k : Int) * s) / 16)).length
          = (4 * (j - 1)).toNat := by
        rw [CatExec.length_Z_to_le_bytes, toNat_four_mul (j - 1) (by omega)]
        have h1 : (j - 1).toNat = j.toNat - 1 := by
          rw [Int.toNat_sub'' hpos (by decide)]; rfl
        omega
      have harith : ((k : Int) - 1 - (j - 1)) = ((k : Int) - j) := by omega
      rw [hsub, ih (j - 1) (by omega) (by omega), natSucc_sub_one k, harith]


/-! ## The routine contract -/

/-- THE CONTRACT consumed by the plan checker's `PX XPopFree` node
    (AsanPlanSoundSums style): from the loop head `p` with `0 <= i < n` the
    loop exits at `p+32`; memory = the old one with `[e-4n, e-4i)`
    overwritten by `pf_bytes c s (n-i)`. -/
def popfree_spec (SEGS : List Segment) (p : Int) : Prop :=
  ∀ (regs : BvMap word) (mem : word → Option byte) (i e c s n : Int),
    getr regs 10 = Z_to_bv 64 i → getr regs 11 = Z_to_bv 64 e →
    getr regs 12 = Z_to_bv 64 c → getr regs 21 = Z_to_bv 64 s →
    getr regs 19 = Z_to_bv 64 n →
    (0 ≤ i ∧ i < n) → (4 * n ≤ e ∧ e < 2 ^ 64) → 0 ≤ c → 0 ≤ s →
    c + (n - i) * s < 2 ^ 64 →
    store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (4 * (n - i)).toNat = true →
    ∃ regs',
      msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 (p + 32))
                    (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (n - i).toNat))
                    (seg_rom SEGS))
      ∧ getr regs' 10 = Z_to_bv 64 n
      ∧ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
      ∧ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16)
      ∧ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
      ∧ (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 15 → getr regs' r = getr regs r)

section PopFreeLoop

variable (segs : List Segment)
-- Address of the loop head (0x52a70 asan).
variable (p : Int)

/-- Register file after one iteration. -/
def iter_regs (regs : BvMap word) (i e c s : Int) : BvMap word :=
  regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
               15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s))

/-- `bv_unsigned (Z_to_bv 64 z) = z` for an in-range `z`. -/
theorem u64_of_Z (z : Int) (Hz : 0 ≤ z ∧ z < 2 ^ 64) : bv_unsigned (Z_to_bv 64 z) = z :=
  StepTac.u_Z2bv z Hz.1 Hz.2

/-- `Ltac gr`: peel `getr` through a `regupd` chain with the
    concrete register numbers (`repeat first [rewrite getr_same by
    reg_neq_tac | rewrite getr_other by reg_neq_tac]`).  Unlike
    `SeqExec.gr` it does NOT finish with `getr_nz`: the loop
    facts are stated about `getr regs r`, so the chain must come to rest
    there. -/
macro "gr" : tactic =>
  `(tactic|
    (repeat (first
      | rw [getr_same _ _ _ (by decide)]
      | rw [getr_other _ _ _ _ (by decide)])))


/-! ## One iteration and the whole loop -/

/-- glue: `v_xori x (-1)` is the bitwise complement (this tree's
    `v_xori` goes through `zlxor` on the `toNat` representatives). -/
theorem v_xori_m1 (x : word) : v_xori x (-1) = ~~~x := by
  have hof : BitVec.ofNat 64 x.toNat = x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  have hone : BitVec.ofNat 64 18446744073709551615 = BitVec.allOnes 64 := by decide
  have hw : bv_wrap 64 (-1) = ((18446744073709551615 : Nat) : Int) := by decide
  unfold v_xori
  rw [hw]
  unfold zlxor
  simp only [Int.toNat_natCast]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_xor, hof, hone, BitVec.not_def, BitVec.xor_comm]

/-- glue: the bitwise complement of `Z_to_bv 64 i` is
    `Z_to_bv 64 (2^64 - 1 - i)`. -/
theorem znot_Z_to_bv (i : Int) (h0 : 0 ≤ i) (h1 : i < 2 ^ 64) :
    ~~~(Z_to_bv 64 i) = Z_to_bv 64 (2 ^ 64 - 1 - i) := by
  have hpos : 0 ≤ 2 ^ 64 - 1 - i := by omega
  have hlt : 2 ^ 64 - 1 - i < ((2 ^ 64 : Nat) : Int) := by omega
  have hi : ((Z_to_bv 64 i).toNat : Int) = i := StepTac.u_Z2bv i h0 h1
  have hR : ((Z_to_bv 64 (2 ^ 64 - 1 - i)).toNat : Int) = 2 ^ 64 - 1 - i :=
    StepTac.u_Z2bv _ hpos hlt
  have hi2 : (i.toNat : Int) = i := Int.toNat_of_nonneg h0
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not]
  omega

/-- glue: `bv_unsigned` of an `ofInt` literal is its residue. -/
theorem bv_unsigned_ofInt (n : Nat) (z : Int) :
    bv_unsigned (Z_to_bv n z) = z % ((2 ^ n : Nat) : Int) := by
  unfold bv_unsigned Z_to_bv
  rw [BitVec.toNat_ofInt,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := Nat.two_pow_pos n; omega))]

/-- One iteration of the loop, from the head `p`: it falls through to `p+32`
    when `i+1 >= n` and back to `p` otherwise. -/
theorem pf_iter (Hp : 28 ≤ p ∧ p + 32 < 2 ^ 64)
    (HF0 : fetch_word segs (Z_to_bv 64 p) = some PW0)
    (HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = some PW1)
    (HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = some PW2)
    (HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = some PW3)
    (HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = some PW4)
    (HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = some PW5)
    (HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = some PW6)
    (HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = some PW7)
    (regs : BvMap word) (mem rom : word → Option byte) (i e c s n : Int)
    (H10 : getr regs 10 = Z_to_bv 64 i) (H11 : getr regs 11 = Z_to_bv 64 e)
    (H12 : getr regs 12 = Z_to_bv 64 c) (H21 : getr regs 21 = Z_to_bv 64 s)
    (H19 : getr regs 19 = Z_to_bv 64 n)
    (Hi : 0 ≤ i) (Hin : i + 1 ≤ n) (Hne : 4 * n ≤ e) (He : e < 2 ^ 64)
    (Hc : 0 ≤ c) (Hs : 0 ≤ s) (Hcs : c + s < 2 ^ 64)
    (Hok : store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true) :
    ∃ regs',
      msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                  (mkst regs' (Z_to_bv 64 (if (i + 1) < n then p else p + 32))
                        (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
                          (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
      ∧ getr regs' 10 = Z_to_bv 64 (i + 1) ∧ getr regs' 11 = Z_to_bv 64 e
      ∧ getr regs' 12 = Z_to_bv 64 (c + s)
      ∧ getr regs' 21 = Z_to_bv 64 s ∧ getr regs' 19 = Z_to_bv 64 n
      ∧ getr regs' 14 = Z_to_bv 64 (c / 16) ∧ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
      ∧ (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 15 → getr regs' r = getr regs r) := by
  have hi64 : i < 2 ^ 64 := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hi164 : i + 1 < 2 ^ 64 := by omega
  have he4 : 4 * (i + 1) ≤ e := by omega
  have hsh4 : ((4 : BitVec 6)).toNat = (4 : Int) := by decide
  have hsh2 : ((2 : BitVec 6)).toNat = (2 : Int) := by decide
  -- the values computed by the iteration
  have V14 : v_srli (Z_to_bv 64 c) 4 = Z_to_bv 64 (c / 16) := by
    rw [LibMaskBits.v_srli_Z c 4 ⟨Hc, by omega⟩ (by omega)]
    rfl
  have V15a : v_xori (Z_to_bv 64 i) ((4095 : BitVec 12)).toInt = Z_to_bv 64 (2 ^ 64 - 1 - i) := by
    rw [show ((4095 : BitVec 12)).toInt = (-1 : Int) from by decide, v_xori_m1]
    exact znot_Z_to_bv i Hi hi64
  have V10 : v_addi (Z_to_bv 64 i) ((1 : BitVec 12)).toInt = Z_to_bv 64 (i + 1) := by
    rw [show ((1 : BitVec 12)).toInt = (1 : Int) from by decide, SymExec.v_addi_lit]
  have V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) ((2 : BitVec 6)).toNat
      = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i) := by
    have hx : (2 ^ 64 - 1 - i) * 4 = 2 ^ 66 - 4 - 4 * i := by omega
    rw [hsh2]
    unfold v_slli zshiftl
    rw [StepTac.u_Z2bv (2 ^ 64 - 1 - i) (by omega) (by omega), ← hx]
    rfl
  have V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i))
      = Z_to_bv 64 (e - 4 * (i + 1)) := by
    have hX : (e % ((2 ^ 64 : Nat) : Int) + (2 ^ 66 - 4 - 4 * i) % ((2 ^ 64 : Nat) : Int))
          % ((2 ^ 64 : Nat) : Int)
        = (e - 4 * (i + 1)) % ((2 ^ 64 : Nat) : Int) := by
      rw [Int.emod_add_emod, Int.add_emod_emod]
      have hx : e + (2 ^ 66 - 4 - 4 * i)
          = (e - 4 * (i + 1)) + 4 * ((2 ^ 64 : Nat) : Int) := by omega
      rw [hx, Int.add_mul_emod_self_right]
    unfold v_add
    simp only [bv_unsigned_ofInt]
    rw [LinuxSem.Common.StepTac.Z_to_bv_mod64, hX, ← LinuxSem.Common.StepTac.Z_to_bv_mod64]
  have Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) ((0 : BitVec 12)).toInt
      = Z_to_bv 64 (e - 4 * (i + 1)) := by
    rw [show ((0 : BitVec 12)).toInt = (0 : Int) from by decide, SymExec.v_addi_lit, Int.add_zero]
  have V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s) :=
    LibMaskBits.v_add_ZZ c s ⟨Hc, by omega⟩ ⟨Hs, by omega⟩
  -- the register file after each of the eight instructions
  let m1 : BvMap word := regupd regs 14 (Z_to_bv 64 (c / 16))
  let m2 : BvMap word := regupd m1 15 (Z_to_bv 64 (2 ^ 64 - 1 - i))
  let m3 : BvMap word := regupd m2 10 (Z_to_bv 64 (i + 1))
  let m4 : BvMap word := regupd m3 15 (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i))
  let m5 : BvMap word := regupd m4 15 (Z_to_bv 64 (e - 4 * (i + 1)))
  let m6 : BvMap word := regupd m5 12 (Z_to_bv 64 (c + s))
  let mem' : word → Option byte :=
    wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))
  have h1 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 p) mem rom)
      = .MachineOk (mkst m1 (Z_to_bv 64 (p + 4)) mem rom) := by
    rw [PropExec.step_srli segs regs (Z_to_bv 64 p) mem rom PW0 14 12 4 HF0 (by decide) PD0]
    simp only [show bv_eqb (14 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m1, hsh4, H12, V14, SymExec.v_addi_lit]
  have h2 : RiscvSemantics.step segs (mkst m1 (Z_to_bv 64 (p + 4)) mem rom)
      = .MachineOk (mkst m2 (Z_to_bv 64 (p + 8)) mem rom) := by
    rw [PropExec.step_xori segs m1 (Z_to_bv 64 (p + 4)) mem rom PW1 15 10 4095 HF1 (by decide) PD1]
    simp only [show bv_eqb (15 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m1, m2]
    gr
    simp only [H10, V15a, SymExec.v_addi_lit]
    rw [show p + 4 + 4 = p + 8 by omega]
  have h3 : RiscvSemantics.step segs (mkst m2 (Z_to_bv 64 (p + 8)) mem rom)
      = .MachineOk (mkst m3 (Z_to_bv 64 (p + 12)) mem rom) := by
    rw [PropExec.step_addi segs m2 (Z_to_bv 64 (p + 8)) mem rom PW2 10 10 1 HF2 (by decide) PD2]
    simp only [show bv_eqb (10 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m2, m3]
    gr
    simp only [H10, V10, SymExec.v_addi_lit]
    rw [show p + 8 + 4 = p + 12 by omega]
  have h4 : RiscvSemantics.step segs (mkst m3 (Z_to_bv 64 (p + 12)) mem rom)
      = .MachineOk (mkst m4 (Z_to_bv 64 (p + 16)) mem rom) := by
    rw [PropExec.step_slli segs m3 (Z_to_bv 64 (p + 12)) mem rom PW3 15 15 2 HF3 (by decide) PD3]
    simp only [show bv_eqb (15 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m3, m4]
    gr
    simp only [V15b, SymExec.v_addi_lit]
    rw [show p + 12 + 4 = p + 16 by omega]
  have h5 : RiscvSemantics.step segs (mkst m4 (Z_to_bv 64 (p + 16)) mem rom)
      = .MachineOk (mkst m5 (Z_to_bv 64 (p + 20)) mem rom) := by
    rw [PropExec.step_add segs m4 (Z_to_bv 64 (p + 16)) mem rom PW4 15 11 15 HF4 (by decide) PD4]
    simp only [show bv_eqb (15 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m4, m5]
    gr
    simp only [H11, V15c, SymExec.v_addi_lit]
    rw [show p + 16 + 4 = p + 20 by omega]
  have h6 : RiscvSemantics.step segs (mkst m5 (Z_to_bv 64 (p + 20)) mem rom)
      = .MachineOk (mkst m5 (Z_to_bv 64 (p + 24)) mem' rom) := by
    have Hok' : store_ok segs mem (v_addi (getr m5 15) ((0 : BitVec 12)).toInt) 4 = true := by
      simp only [m5, m4, m3, m2, m1]
      gr
      rw [Vst]
      exact Hok
    rw [SeqExec.step_sw_val segs m5 (Z_to_bv 64 (p + 20)) mem rom PW5 15 14 0 HF5 (by decide) PD5 Hok']
    simp only [show bv_eqb (15 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m5, m4, m3, m2, m1, mem']
    gr
    simp only [Vst, SymExec.v_addi_lit]
    rw [show p + 20 + 4 = p + 24 by omega]
  have h7 : RiscvSemantics.step segs (mkst m5 (Z_to_bv 64 (p + 24)) mem' rom)
      = .MachineOk (mkst m6 (Z_to_bv 64 (p + 28)) mem' rom) := by
    rw [PropExec.step_add segs m5 (Z_to_bv 64 (p + 24)) mem' rom PW6 12 12 21 HF6 (by decide) PD6]
    simp only [show bv_eqb (12 : reg) 0 = false from by decide, Bool.false_eq_true, ite_false,
      m5, m6]
    gr
    simp only [H12, H21, V12, SymExec.v_addi_lit]
    rw [show p + 24 + 4 = p + 28 by omega]
  have hltu : c_ltu (getr m6 10) (getr m6 19) = decide ((i + 1) < n) := by
    simp only [m6, m5, m4, m3, m2, m1]
    gr
    rw [H19, LibMaskBits.c_ltu_Z (i + 1) n ⟨by omega, hi164⟩ ⟨by omega, hn64⟩]
  have h8 : RiscvSemantics.step segs (mkst m6 (Z_to_bv 64 (p + 28)) mem' rom)
      = .MachineOk (mkst m6 (Z_to_bv 64 (if (i + 1) < n then p else p + 32)) mem' rom) := by
    by_cases hlt : (i + 1) < n
    · have Hc : c_ltu (getr m6 10) (getr m6 19) = true := by
        rw [hltu]; exact decide_eq_true hlt
      rw [PropExec.step_bltu_tk segs m6 (Z_to_bv 64 (p + 28)) mem' rom PW7 10 19 8164
        HF7 (by decide) PD7 Hc, ite_eq_left hlt]
      simp only [SymExec.btgt_lit,
        show ((8164 : BitVec 13)).toInt = (-28 : Int) from by decide,
        show p + 28 + -28 = p by omega]
    · have Hc : c_ltu (getr m6 10) (getr m6 19) = false := by
        rw [hltu]; exact decide_eq_false hlt
      rw [PropExec.step_bltu_ft segs m6 (Z_to_bv 64 (p + 28)) mem' rom PW7 10 19 8164
        HF7 (by decide) PD7 Hc, ite_eq_right hlt]
      simp only [SymExec.v_addi_lit,
        show p + 28 + 4 = p + 32 by omega]
  have hms : msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
      (mkst m6 (Z_to_bv 64 (if (i + 1) < n then p else p + 32)) mem' rom) :=
    msteps.mst_step _ _ _ (by rfl) h1
      (msteps.mst_step _ _ _ (by rfl) h2
        (msteps.mst_step _ _ _ (by rfl) h3
          (msteps.mst_step _ _ _ (by rfl) h4
            (msteps.mst_step _ _ _ (by rfl) h5
              (msteps.mst_step _ _ _ (by rfl) h6
                (msteps.mst_step _ _ _ (by rfl) h7
                  (msteps.mst_step _ _ _ (by rfl) h8 (msteps.mst_refl _))))))))
  refine ⟨m6, hms, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [m6, m5, m4, m3, m2, m1]; gr
  · simp only [m6, m5, m4, m3, m2, m1]; gr; exact H11
  · simp only [m6, m5, m4, m3, m2, m1]; gr
  · simp only [m6, m5, m4, m3, m2, m1]; gr; exact H21
  · simp only [m6, m5, m4, m3, m2, m1]; gr; exact H19
  · simp only [m6, m5, m4, m3, m2, m1]; gr
  · simp only [m6, m5, m4, m3, m2, m1]; gr
  · intro r h10 h12 h14 h15
    simp only [m6, m5, m4, m3, m2, m1]
    rw [getr_other _ _ _ _ h12, getr_other _ _ _ _ h15, getr_other _ _ _ _ h15,
      getr_other _ _ _ _ h10, getr_other _ _ _ _ h15, getr_other _ _ _ _ h14]


/-- `k+1` iterations from the head, running to the exit `p+32` with the
    memory `pf_mem mem e c s i (k+1)`. -/
theorem pf_loop (Hp : 28 ≤ p ∧ p + 32 < 2 ^ 64)
    (HF0 : fetch_word segs (Z_to_bv 64 p) = some PW0)
    (HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = some PW1)
    (HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = some PW2)
    (HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = some PW3)
    (HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = some PW4)
    (HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = some PW5)
    (HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = some PW6)
    (HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = some PW7) :
    ∀ (k : Nat) (regs : BvMap word) (mem rom : word → Option byte) (i e c s n : Int),
      n = i + ((k + 1 : Nat) : Int) →
      getr regs 10 = Z_to_bv 64 i → getr regs 11 = Z_to_bv 64 e →
      getr regs 12 = Z_to_bv 64 c → getr regs 21 = Z_to_bv 64 s →
      getr regs 19 = Z_to_bv 64 n →
      0 ≤ i → 4 * n ≤ e → e < 2 ^ 64 → 0 ≤ c → 0 ≤ s →
      c + ((k + 1 : Nat) : Int) * s < 2 ^ 64 →
      (∀ j, i ≤ j → j < n →
        store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true) →
      ∃ regs',
        msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                    (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (k + 1)) rom)
        ∧ getr regs' 10 = Z_to_bv 64 n ∧ getr regs' 11 = Z_to_bv 64 e
        ∧ getr regs' 12 = Z_to_bv 64 (c + ((k + 1 : Nat) : Int) * s)
        ∧ getr regs' 21 = Z_to_bv 64 s ∧ getr regs' 19 = Z_to_bv 64 n
        ∧ getr regs' 14 = Z_to_bv 64 ((c + (k : Int) * s) / 16)
        ∧ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
        ∧ (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 15 → getr regs' r = getr regs r) := by
  intro k
  induction k with
  | zero =>
    -- last iteration
    intro regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok
    have Hn1 : n = i + 1 := by
      have h : ((1 : Nat) : Int) = (1 : Int) := rfl
      rw [h] at Hn; exact Hn
    have Hin : i + 1 ≤ n := by omega
    have Hcs1 : c + s < 2 ^ 64 := by omega
    obtain ⟨regs', hms, R10, R11, R12, R21, R19, R14, R15, Ro⟩ :=
      pf_iter segs p Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7 regs mem rom i e c s n
        H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs1 (Hok i (by omega) (by omega))
    have hnot : ¬ (i + 1) < n := by omega
    rw [ite_eq_right hnot] at hms
    refine ⟨regs', hms, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [R10, Hn1]
    · exact R11
    · rw [R12]
      congr 1
      rw [show ((0 + 1 : Nat) : Int) = (1 : Int) from rfl, Int.one_mul]
    · exact R21
    · exact R19
    · rw [R14]
      congr 1
      rw [show ((0 : Nat) : Int) = (0 : Int) from rfl, Int.zero_mul, Int.add_zero]
    · rw [R15, Hn1]
    · exact Ro
  | succ k ih =>
    -- one iteration, then the rest
    intro regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok
    have hk1 : ((k + 1 + 1 : Nat) : Int) = ((k + 1 : Nat) : Int) + 1 := by push_cast; omega
    have hk2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; omega
    rw [hk1] at Hn Hcs
    rw [Int.add_mul, Int.one_mul] at Hcs
    have Hi2 : i + 1 < n := by omega
    have Hin : i + 1 ≤ n := by omega
    have hj : 0 ≤ ((k + 1 : Nat) : Int) * s := Int.mul_nonneg (Int.natCast_nonneg _) Hs
    have Hcs1 : c + s < 2 ^ 64 := by omega
    have Hcs' : (c + s) + ((k + 1 : Nat) : Int) * s < 2 ^ 64 := by omega
    obtain ⟨regs1, hms1, R10, R11, R12, R21, R19, R14, R15, Ro⟩ :=
      pf_iter segs p Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7 regs mem rom i e c s n
        H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs1 (Hok i (by omega) (by omega))
    rw [ite_eq_left Hi2] at hms1
    have Hok' : ∀ j, (i + 1) ≤ j → j < n →
        store_ok segs (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
          (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true := by
      intro j hj1 hj2
      exact store_ok_mono segs 4 mem _ _
        (wbytes_grows _ mem _) (Hok j (by omega) hj2)
    obtain ⟨regs2, hms2, S10, S11, S12, S21, S19, S14, S15, So⟩ :=
      ih regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
            (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom (i + 1) e (c + s) s n
        (by omega) R10 R11 R12 R21 R19 (by omega) Hne He (by omega) Hs Hcs' Hok'
    refine ⟨regs2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact msteps_trans segs _ _ _ hms1 hms2
    · exact S10
    · exact S11
    · rw [S12]
      congr 1
      have harith : (c + s) + ((k + 1 : Nat) : Int) * s = c + ((k + 1 + 1 : Nat) : Int) * s := by
        rw [hk1, Int.add_mul, Int.one_mul]; omega
      rw [harith]
    · exact S21
    · exact S19
    · rw [S14]
      congr 1
      have harith : (c + s) + (k : Int) * s = c + ((k + 1 : Nat) : Int) * s := by
        rw [hk2, Int.add_mul, Int.one_mul]; omega
      rw [harith]
    · exact S15
    · intro r A B C D
      exact (So r A B C D).trans (Ro r A B C D)


/-! ## Reading the written cells back -/

/-- glue: `((a + 1).toNat : Int) = (a.toNat : Int) + 1`. -/
theorem toNat_succ_int (a : word) (h : a.toNat + 1 < 2 ^ 64) :
    ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := by
  rw [CatExec.toNat_add_one a h]
  push_cast
  rfl

/-- Pointwise description of `wbytes` (copies of MemSplit's, to keep this
    file's imports light). -/
theorem pf_wbytes_inside (bs : List byte) :
    ∀ (m : word → Option byte) (a x : word),
      (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      ((a.toNat : Int) ≤ (x.toNat : Int) ∧
        (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int)) →
      wbytes m a bs x = some (bs.getD (x.toNat - a.toNat) (Z_to_bv 8 0)) := by
  induction bs with
  | nil =>
    intro m a x _ Hx
    have h : (x.toNat : Int) < (a.toNat : Int) := by
      have h2 := Hx.2
      rw [List.length_nil, Int.ofNat_zero, Int.add_zero] at h2
      exact h2
    omega
  | cons b rest ih =>
    intro m a x Hnw Hx
    have hN : a.toNat + (b :: rest).length ≤ 2 ^ 64 := CatExec.nat_sum_le_two64 Hnw
    by_cases hxa : x = a
    · rw [hxa]
      rw [Nat.sub_self, List.getD_cons_zero]
      cases rest with
      | nil =>
        show (if bv_eqb a a then some b else m a) = some b
        simp [bv_eqb_refl]
      | cons b' rest' =>
        show wbytes (fun y => if bv_eqb y a then some b else m y) (a + 1) (b' :: rest') a
          = some b
        have hposN : a.toNat + 1 < 2 ^ 64 := by
          have h := hN
          rw [List.length_cons] at h
          have hl : 1 ≤ (b' :: rest').length := by simp
          omega
        have ha1n : (a + 1).toNat = a.toNat + 1 := CatExec.toNat_add_one a hposN
        have hbnd : ((a + 1).toNat : Int) + ((b' :: rest').length : Int)
            ≤ ((2 ^ 64 : Nat) : Int) := by
          apply CatExec.int_sum_le_of_nat
          rw [ha1n]
          have h := hN
          rw [List.length_cons] at h
          omega
        have hlt : (a.toNat : Int) < ((a + 1).toNat : Int) := by
          rw [ha1n]
          push_cast
          omega
        rw [wbytes_below (b' :: rest') _ (a + 1) a hbnd hlt]
        simp [bv_eqb_refl]
    · have hne : (x.toNat : Int) ≠ (a.toNat : Int) := by
        intro h
        apply hxa
        apply BitVec.eq_of_toNat_eq
        exact_mod_cast h
      have hgt : (a.toNat : Int) < (x.toNat : Int) := by omega
      have hgtNat : a.toNat + 1 ≤ x.toNat := by omega
      have hposN : a.toNat + 1 < 2 ^ 64 := by
        have := x.isLt
        omega
      have ha1n : (a + 1).toNat = a.toNat + 1 := CatExec.toNat_add_one a hposN
      have hbnd : ((a + 1).toNat : Int) + (rest.length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
        apply CatExec.int_sum_le_of_nat
        rw [ha1n]
        have h := hN
        rw [List.length_cons] at h
        omega
      have hx' : ((a + 1).toNat : Int) ≤ (x.toNat : Int) ∧
          (x.toNat : Int) < ((a + 1).toNat : Int) + (rest.length : Int) := by
        have h1 : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := toNat_succ_int a hposN
        have hlenI : ((b :: rest).length : Int) = (rest.length : Int) + 1 := by
          rw [List.length_cons, Int.natCast_add, Int.natCast_one]
        have h2 := Hx.2
        rw [hlenI] at h2
        rw [h1]
        constructor <;> omega
      have hidx : (x.toNat - (a + 1).toNat) + 1 = x.toNat - a.toNat := by
        rw [ha1n]
        omega
      show wbytes (fun y => if bv_eqb y a then some b else m y) (a + 1) rest x
        = some ((b :: rest).getD (x.toNat - a.toNat) (Z_to_bv 8 0))
      rw [ih _ (a + 1) x hbnd hx', ← hidx, List.getD_cons_succ]

/-- Pointwise description of `wbytes`, outside case. -/
theorem pf_wbytes_outside (bs : List byte) (m : word → Option byte) (a x : word)
    (Hnw : (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hout : (x.toNat : Int) < (a.toNat : Int) ∨
      (a.toNat : Int) + (bs.length : Int) ≤ (x.toNat : Int)) :
    wbytes m a bs x = m x := by
  rcases Hout with h | h
  · exact wbytes_below bs m a x Hnw h
  · exact wbytes_above bs m a x h

/-- Bytes outside `[e - 4(i+k), e - 4i)` are untouched. -/
theorem pf_mem_frame : ∀ (k : Nat) (mem : word → Option byte) (e c s i : Int) (a : word),
    0 ≤ i → 4 * (i + (k : Int)) ≤ e → e < 2 ^ 64 →
    ((a.toNat : Int) < e - 4 * (i + (k : Int)) ∨ e - 4 * i ≤ (a.toNat : Int)) →
    pf_mem mem e c s i k a = mem a := by
  intro k
  induction k with
  | zero =>
    intro mem e c s i a _ _ _ _
    rfl
  | succ k ih =>
    intro mem e c s i a Hi Hk He Ha
    have Hk' : 4 * ((i + 1) + (k : Int)) ≤ e := by
      push_cast at Hk
      omega
    have Hi' : 0 ≤ i + 1 := by omega
    have Ha' : ((a.toNat : Int) < e - 4 * ((i + 1) + (k : Int)) ∨
        e - 4 * (i + 1) ≤ (a.toNat : Int)) := by
      push_cast at Ha
      omega
    show pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
          (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) e (c + s) s (i + 1) k a = mem a
    rw [ih _ e (c + s) s (i + 1) a Hi' Hk' He Ha']
    -- the outer write does not touch `a`
    have ha0 : ((Z_to_bv 64 (e - 4 * (i + 1))).toNat : Int) = e - 4 * (i + 1) := by
      apply StepTac.u_Z2bv
      · omega
      · omega
    have hlen : (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))).length = 4 :=
      CatExec.length_N_to_le_bytes 4 _
    have hbnd : ((Z_to_bv 64 (e - 4 * (i + 1))).toNat : Int)
        + ((word_to_le_bytes 4 (Z_to_bv 64 (c / 16))).length : Int)
        ≤ ((2 ^ 64 : Nat) : Int) := by
      rw [hlen, ha0]
      omega
    have Hout : ((a.toNat : Int) < (Z_to_bv 64 (e - 4 * (i + 1))).toNat ∨
        ((Z_to_bv 64 (e - 4 * (i + 1))).toNat : Int) + 4 ≤ (a.toNat : Int)) := by
      rw [ha0]
      push_cast at Ha
      omega
    exact pf_wbytes_outside _ _ _ _ hbnd Hout

/-- `word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v`. -/
theorem word_to_le_bytes4_Z (v : Int) :
    word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v := by
  have h : ((Z_to_bv 64 v).toNat : Int) = bv_wrap 64 v := by
    unfold bv_wrap Z_to_bv
    rw [BitVec.toNat_ofInt,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := Nat.two_pow_pos 64; omega))]
  unfold word_to_le_bytes
  rw [h]
  exact SeqExec.Z_to_le_bytes_wrap 4 64 v (by decide)


/-- Byte `t` of cell `j` (cells counted upwards from the lowest address
    `e - 4(i+k)`). -/
theorem pf_mem_cell : ∀ (k : Nat) (mem : word → Option byte) (e c s : Int) (i : Int)
    (j : Int) (t : Nat),
    0 ≤ i → 4 * (i + (k : Int)) ≤ e → e < 2 ^ 64 →
    0 ≤ j → j < (k : Int) → t < 4 →
    pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int)))
      = some ((Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16)).getD t (Z_to_bv 8 0)) := by
  intro k
  induction k with
  | zero =>
    intro mem e c s i j t Hi Hk He Hj0 Hjk Ht
    omega
  | succ k ih =>
    intro mem e c s i j t Hi Hk He Hj0 Hjk Ht
    have hk1 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by push_cast; omega
    have htI : ((t : Int)) < 4 := by exact_mod_cast Ht
    -- the write address of THIS iteration and the bounds around it
    have hbase : 0 ≤ e - 4 * (i + ((k + 1 : Nat) : Int)) := by omega
    have hlow : 0 ≤ e - 4 * (i + 1) := by omega
    have hlow64 : e - 4 * (i + 1) < 2 ^ 64 := by omega
    have ha0 : ((Z_to_bv 64 (e - 4 * (i + 1))).toNat : Int) = e - 4 * (i + 1) :=
      StepTac.u_Z2bv _ hlow hlow64
    have hlenI : ((word_to_le_bytes 4 (Z_to_bv 64 (c / 16))).length : Int) = 4 := by
      rw [CatExec.length_N_to_le_bytes]; rfl
    have hbnd : ((Z_to_bv 64 (e - 4 * (i + 1))).toNat : Int)
        + ((word_to_le_bytes 4 (Z_to_bv 64 (c / 16))).length : Int)
        ≤ ((2 ^ 64 : Nat) : Int) := by
      rw [hlenI, ha0]; omega
    have hlenN : (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))).length = 4 :=
      CatExec.length_N_to_le_bytes 4 _
    have Hk' : 4 * ((i + 1) + (k : Int)) ≤ e := by
      have h := Hk
      rw [hk1] at h
      omega
    by_cases hj : j = (k : Int)
    · -- the cell written by THIS iteration, untouched by the later ones
      rw [hj]
      have haddr : e - 4 * (i + ((k + 1 : Nat) : Int)) + 4 * (k : Int) + (t : Int)
          = e - 4 * (i + 1) + (t : Int) := by rw [hk1]; omega
      rw [haddr]
      have hv1 : ((Z_to_bv 64 (e - 4 * (i + 1) + (t : Int))).toNat : Int)
          = e - 4 * (i + 1) + (t : Int) := by
        apply StepTac.u_Z2bv <;> omega
      show pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
              (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) e (c + s) s (i + 1) k
            (Z_to_bv 64 (e - 4 * (i + 1) + (t : Int)))
          = some ((Z_to_le_bytes 4 ((c + (((k + 1 : Nat) : Int) - 1 - (k : Int)) * s) / 16)).getD t
              (Z_to_bv 8 0))
      rw [pf_mem_frame k _ e (c + s) s (i + 1) _ (by omega) Hk' He (by omega)]
      rw [pf_wbytes_inside (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))) mem
        (Z_to_bv 64 (e - 4 * (i + 1))) _ hbnd (by
          constructor
          · rw [ha0, hv1]; omega
          · rw [ha0, hv1, hlenI]; omega)]
      rw [word_to_le_bytes4_Z]
      have hidx : (Z_to_bv 64 (e - 4 * (i + 1) + (t : Int))).toNat
          - (Z_to_bv 64 (e - 4 * (i + 1))).toNat = t := by
        omega
      rw [hidx]
      have hval : (c + (((k + 1 : Nat) : Int) - 1 - (k : Int)) * s) / 16 = c / 16 := by
        have hz : ((k + 1 : Nat) : Int) - 1 - (k : Int) = 0 := by rw [hk1]; omega
        rw [hz, Int.zero_mul, Int.add_zero]
      rw [hval]
    · -- a cell of the inner chain: shift the block by one iteration
      have hjk' : j < (k : Int) := by omega
      have haddr : e - 4 * (i + ((k + 1 : Nat) : Int)) + 4 * j + (t : Int)
          = e - 4 * ((i + 1) + (k : Int)) + 4 * j + (t : Int) := by rw [hk1]; omega
      rw [haddr]
      show pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
              (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) e (c + s) s (i + 1) k
            (Z_to_bv 64 (e - 4 * ((i + 1) + (k : Int)) + 4 * j + (t : Int)))
          = some ((Z_to_le_bytes 4 ((c + (((k + 1 : Nat) : Int) - 1 - j) * s) / 16)).getD t
              (Z_to_bv 8 0))
      rw [ih (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1)))
            (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) e (c + s) s (i + 1) j t
          (by omega) (by omega) He Hj0 hjk' Ht]
      have hval : ((c + s) + ((k : Int) - 1 - j) * s) / 16
          = (c + (((k + 1 : Nat) : Int) - 1 - j) * s) / 16 := by
        have hT : ((k : Int) - 1 - j) + 1 = ((k + 1 : Nat) : Int) - 1 - j := by
          rw [hk1]; omega
        congr 1
        calc (c + s) + ((k : Int) - 1 - j) * s
            = c + (((k : Int) - 1 - j) * s + s) := by omega
          _ = c + (((k : Int) - 1 - j) + 1) * s := by rw [Int.add_mul, Int.one_mul]
          _ = c + (((k + 1 : Nat) : Int) - 1 - j) * s := by rw [hT]
      rw [hval]


/-- The cells read back as a 4-byte arithmetic progression (the `KSeq`
    shape): cell `j` (address `e - 4(i+k) + 4j`) holds
    `(c + (k-1-j)*s) / 16`. -/
theorem pf_mem_rdn (mem : word → Option byte) (e c s i : Int) :
    ∀ (k : Nat) (j : Int),
      0 ≤ i → 4 * (i + (k : Int)) ≤ e → e < 2 ^ 64 → 0 ≤ j → j < (k : Int) →
      rdn segs (pf_mem mem e c s i k) (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j)) 4
        = some (Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16)) := by
  intro k j Hi Hk He Hj Hjk
  have h1 : bv_unsigned (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j))
      = e - 4 * (i + (k : Int)) + 4 * j := by
    apply StepTac.u_Z2bv <;> omega
  refine rdn_pointwise segs (pf_mem mem e c s i k) 4
    (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j))
    (Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16))
    (CatExec.length_Z_to_le_bytes 4 _) ?_ ?_
  · simp only [h1]; omega
  · intro t Ht
    simp only [h1]
    exact pf_mem_cell k mem e c s i j t Hi Hk He Hj Hjk Ht


/-- The cell values form the arithmetic progression the `KSeq` checker
    matches: `cell j = cell(base) + j * (-(s/16))` when `16 ∣ s`. -/
theorem pf_cell_linear (c s k j : Int) (H : (16 : Int) ∣ s) :
    (c + (k - 1 - j) * s) / 16 = (c + (k - 1) * s) / 16 + j * (-(s / 16)) := by
  rcases H with ⟨q, rfl⟩
  have hq : (16 * q) / 16 = q := by
    rw [Int.mul_comm 16 q]
    exact Int.mul_ediv_cancel q (by decide)
  rw [hq]
  have hsplit : (c + (k - 1 - j) * (16 * q))
      = (c + (k - 1) * (16 * q)) + (-(j * q)) * 16 := by
    have h1 : (k - 1 - j) * (16 * q) = (k - 1) * (16 * q) - j * (16 * q) :=
      Int.sub_mul _ _ _
    have h2 : j * (16 * q) = j * q * 16 := by
      rw [Int.mul_assoc j q 16, Int.mul_comm 16 q]
    rw [h1, Int.sub_eq_add_neg, h2, ← Int.neg_mul]
    omega
  rw [hsplit, Int.add_mul_ediv_right _ _ (by decide : (16 : Int) ≠ 0), Int.mul_neg]

/-- The loop from its head with `i < n`: runs to the exit `p + 32`.  The
    memory is `pf_mem mem e c s i (n-i)`. -/
theorem popfree_loop_run (Hp : 28 ≤ p ∧ p + 32 < 2 ^ 64)
    (HF0 : fetch_word segs (Z_to_bv 64 p) = some PW0)
    (HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = some PW1)
    (HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = some PW2)
    (HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = some PW3)
    (HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = some PW4)
    (HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = some PW5)
    (HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = some PW6)
    (HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = some PW7)
    (regs : BvMap word) (mem rom : word → Option byte) (i e c s n : Int)
    (H10 : getr regs 10 = Z_to_bv 64 i) (H11 : getr regs 11 = Z_to_bv 64 e)
    (H12 : getr regs 12 = Z_to_bv 64 c) (H21 : getr regs 21 = Z_to_bv 64 s)
    (H19 : getr regs 19 = Z_to_bv 64 n)
    (Hi : 0 ≤ i) (Hin : i < n) (Hne : 4 * n ≤ e) (He : e < 2 ^ 64)
    (Hc : 0 ≤ c) (Hs : 0 ≤ s) (Hcs : c + (n - i) * s < 2 ^ 64)
    (Hwr : ∀ (d : Int) (m : Nat), 0 ≤ d → d + (m : Int) ≤ 4 * (n - i) →
      store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true) :
    ∃ regs',
      msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                  (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (n - i).toNat) rom)
      ∧ getr regs' 10 = Z_to_bv 64 n ∧ getr regs' 11 = Z_to_bv 64 e
      ∧ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
      ∧ getr regs' 21 = Z_to_bv 64 s ∧ getr regs' 19 = Z_to_bv 64 n
      ∧ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16)
      ∧ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
      ∧ (∀ r : reg, r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 15 → getr regs' r = getr regs r) := by
  have hni : 0 < n - i := by omega
  have hniN : 0 < (n - i).toNat := by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (by omega)]
    exact hni
  obtain ⟨k, hk⟩ : ∃ k, (n - i).toNat = k + 1 := ⟨(n - i).toNat - 1, by omega⟩
  have hkz : ((k + 1 : Nat) : Int) = n - i := by
    have h : (((n - i).toNat : Nat) : Int) = n - i := Int.toNat_of_nonneg (by omega)
    rw [hk] at h
    exact h
  have hk' : ((k : Nat) : Int) = n - i - 1 := by
    have := hkz
    push_cast at this
    omega
  have Hok : ∀ j, i ≤ j → j < n →
      store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true := by
    intro j hj1 hj2
    have hd : e - 4 * (j + 1) = e - 4 * n + 4 * (n - j - 1) := by omega
    rw [hd]
    exact Hwr (4 * (n - j - 1)) 4 (by omega) (by omega)
  obtain ⟨regs', hms, R10, R11, R12, R21, R19, R14, R15, Ro⟩ :=
    pf_loop segs p Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7 k regs mem rom i e c s n
      (by rw [hkz]; omega) H10 H11 H12 H21 H19 Hi Hne He Hc Hs
      (by rw [hkz]; exact Hcs) Hok
  refine ⟨regs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk]; exact hms
  · rw [R10]
  · exact R11
  · rw [R12, hkz]
  · exact R21
  · exact R19
  · rw [R14, hk']
  · rw [R15]
  · exact Ro


/-- `pf_mem` is the byte-level `wbytes` over the SAME block, lowest address
    first. -/
theorem pf_mem_wbytes (mem : word → Option byte) (e c s i : Int) :
    ∀ (k : Nat), 0 ≤ i → 4 * (i + (k : Int)) ≤ e → e < 2 ^ 64 →
      pf_mem mem e c s i k
        = wbytes mem (Z_to_bv 64 (e - 4 * (i + (k : Int)))) (pf_bytes c s k) := by
  intro k Hi Hk He
  have hbase : ((Z_to_bv 64 (e - 4 * (i + (k : Int)))).toNat : Int) = e - 4 * (i + (k : Int)) := by
    apply StepTac.u_Z2bv <;> omega
  have hlenI : ((pf_bytes c s k).length : Int) = 4 * (k : Int) := by
    rw [pf_bytes_length]
    push_cast
    rfl
  have hboundA : ((Z_to_bv 64 (e - 4 * (i + (k : Int)))).toNat : Int)
      + ((pf_bytes c s k).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [hlenI, hbase]
    omega
  funext a
  have ha := a.isLt
  by_cases Hlt : (a.toNat : Int) < e - 4 * (i + (k : Int))
  · -- below the block: neither side touches `a`
    rw [pf_mem_frame k mem e c s i a Hi Hk He (Or.inl Hlt)]
    rw [pf_wbytes_outside (pf_bytes c s k) mem (Z_to_bv 64 (e - 4 * (i + (k : Int)))) a hboundA
      (Or.inl (by rw [hbase]; exact Hlt))]
  · by_cases Hge : (a.toNat : Int) < e - 4 * i
    · -- inside the block: byte `t` of cell `j`
      have hd0 : 0 ≤ (a.toNat : Int) - (e - 4 * (i + (k : Int))) := by omega
      have hdk : (a.toNat : Int) - (e - 4 * (i + (k : Int))) < 4 * (k : Int) := by omega
      generalize hjdef : (((a.toNat : Int) - (e - 4 * (i + (k : Int)))) / 4) = j
      generalize htdef : ((((a.toNat : Int) - (e - 4 * (i + (k : Int)))) % 4).toNat) = t
      have hj0 : 0 ≤ j := by
        rw [← hjdef]
        exact Int.ediv_nonneg hd0 (by decide)
      have hjk : j < (k : Int) := by
        rw [← hjdef]
        rw [Int.ediv_lt_iff_lt_mul (a := (a.toNat : Int) - (e - 4 * (i + (k : Int))))
          (b := (k : Int)) (c := 4) (by decide)]
        omega
      have htval : (t : Int) = ((a.toNat : Int) - (e - 4 * (i + (k : Int)))) % 4 := by
        rw [← htdef]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
      have ht4 : t < 4 := by
        have h1 : ((a.toNat : Int) - (e - 4 * (i + (k : Int)))) % 4 < 4 := by
          have h := Int.emod_lt ((a.toNat : Int) - (e - 4 * (i + (k : Int)))) (by decide : (4 : Int) ≠ 0)
          simpa using h
        have h2 : 0 ≤ ((a.toNat : Int) - (e - 4 * (i + (k : Int)))) % 4 :=
          Int.emod_nonneg _ (by decide)
        omega
      have hd : (a.toNat : Int) - (e - 4 * (i + (k : Int))) = 4 * j + (t : Int) := by
        have h1 := Int.mul_ediv_add_emod ((a.toNat : Int) - (e - 4 * (i + (k : Int)))) 4
        rw [hjdef] at h1
        omega
      have haeq : a = Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int)) := by
        apply BitVec.eq_of_toNat_eq
        have hR : (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int))).toNat
            = ((e - 4 * (i + (k : Int)) + 4 * j + (t : Int))).toNat := by
          rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
        rw [hR]
        omega
      have haddrv : ((Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int))).toNat : Int)
          = e - 4 * (i + (k : Int)) + 4 * j + (t : Int) := by
        apply StepTac.u_Z2bv <;> omega
      rw [haeq, pf_mem_cell k mem e c s i j t Hi Hk He hj0 hjk ht4]
      rw [pf_wbytes_inside (pf_bytes c s k) mem (Z_to_bv 64 (e - 4 * (i + (k : Int))))
        (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int))) hboundA (by
          constructor
          · rw [haddrv, hbase]; omega
          · rw [haddrv, hbase, hlenI]; omega)]
      have hidx : (Z_to_bv 64 (e - 4 * (i + (k : Int)) + 4 * j + (t : Int))).toNat
          - (Z_to_bv 64 (e - 4 * (i + (k : Int)))).toNat = 4 * j.toNat + t := by
        have h1 : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg hj0
        omega
      have hlast : (Z_to_le_bytes 4 ((c + ((k : Int) - 1 - j) * s) / 16)).getD t (Z_to_bv 8 0)
          = (pf_bytes c s k).getD (4 * j.toNat + t) (Z_to_bv 8 0) := by
        rw [← pf_bytes_nth c s k j t hj0 hjk ht4, toNat_four_mul j hj0]
      rw [hidx, hlast]
    · -- above the block: neither side touches `a`
      rw [pf_mem_frame k mem e c s i a Hi Hk He (Or.inr (by omega))]
      rw [pf_wbytes_outside (pf_bytes c s k) mem (Z_to_bv 64 (e - 4 * (i + (k : Int)))) a hboundA
        (Or.inr (by rw [hbase, hlenI]; omega))]


/-! ## The contract `popfree_spec` from the code facts -/

/-- The routine contract, derived from the eight `fetch_word` facts.  The
    memory goes from `pf_mem` to the `wbytes`-over-`pf_bytes` form via
    [`pf_mem_wbytes`]. -/
theorem popfree_spec_of_code (Hp : 28 ≤ p ∧ p + 32 < 2 ^ 64)
    (HF0 : fetch_word segs (Z_to_bv 64 p) = some PW0)
    (HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = some PW1)
    (HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = some PW2)
    (HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = some PW3)
    (HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = some PW4)
    (HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = some PW5)
    (HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = some PW6)
    (HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = some PW7) :
    popfree_spec segs p := by
  intro regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok
  obtain ⟨Hi, Hin'⟩ := Hin
  obtain ⟨Hne, He64⟩ := He
  have hN : (((4 * (n - i)).toNat : Nat) : Int) = 4 * (n - i) :=
    Int.toNat_of_nonneg (by omega)
  have hlo : ((Z_to_bv 64 (e - 4 * n)).toNat : Int) = e - 4 * n :=
    StepTac.u_Z2bv _ (by omega) (by omega)
  have Hwr : ∀ (d : Int) (m : Nat), 0 ≤ d → d + (m : Int) ≤ 4 * (n - i) →
      store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true := by
    intro d m Hd Hdm
    have ha : ((Z_to_bv 64 (e - 4 * n + d)).toNat : Int) = e - 4 * n + d :=
      StepTac.u_Z2bv _ (by omega) (by omega)
    refine store_ok_sub segs mem (Z_to_bv 64 (e - 4 * n)) (Z_to_bv 64 (e - 4 * n + d))
      (4 * (n - i)).toNat m ?_ Hok ?_ ?_
    · rw [hN, hlo]; omega
    · rw [hlo, ha]; omega
    · rw [hlo, ha, hN]; omega
  obtain ⟨regs', hms, R10, R11, R12, R21, R19, R14, R15, Ro⟩ :=
    popfree_loop_run segs p Hp HF0 HF1 HF2 HF3 HF4 HF5 HF6 HF7 regs mem (seg_rom segs)
      i e c s n H10 H11 H12 H21 H19 Hi Hin' Hne He64 Hc Hs Hcs Hwr
  have hni' : (((n - i).toNat : Nat) : Int) = n - i := Int.toNat_of_nonneg (by omega)
  have hmem := pf_mem_wbytes mem e c s i (n - i).toNat Hi
    (by rw [hni']; omega) He64
  rw [show e - 4 * (i + (((n - i).toNat : Nat) : Int)) = e - 4 * n by rw [hni']; omega] at hmem
  rw [hmem] at hms
  exact ⟨regs', hms, R10, R12, R14, R15, Ro⟩

end PopFreeLoop

end LinuxSem.Common.AsanPopFree
