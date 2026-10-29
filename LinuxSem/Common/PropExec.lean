/-
  * Common.PropExec — propositional symbolic-execution engine.

    Image-INDEPENDENT proof infrastructure: a propositional single-step
    engine ([mkst]/[getr]/[regupd], value shapes [v_addi]/[v_mul]/[v_andi],
    conditions [c_lts]/[c_eq], per-instruction [step_*] lemmas) together with
    the layout/read lemmas needed to drive a symbolic argv-byte read.

    Built on the RISC-V ISA semantics: machine values are [word = BitVec 64],
    register indices are [reg = BitVec 5], bytes are [byte = BitVec 8].  The
    decode hypotheses are over [DecodeC.decodeAny] (instruction AST + size),
    the value shapes are [BitVec.ofInt 64] of plain-[Int] expressions over
    [toNat]/[toInt], and there are no branch/jump alignment side conditions —
    the ISA model has no alignment check.

    This file fixes the vocabulary the proofs speak, in Lean core terms:
      * [bv_unsigned x]      ↦ [x.toNat]        (here written [x.toNat])
      * [bv_signed x]        ↦ [x.toInt]
      * [Z_to_bv n z]        ↦ [BitVec.ofInt n z]
      * [bv_wrap n z]        ↦ `z % 2^n`, i.e. [bv_wrap] below
      * [bv_swrap n z]       ↦ [bv_swrap] below
      * [Z.land]/[Z.lor]/[Z.lxor] have NO Lean core counterpart on [Int]
        ([Int.land] does not exist), so this file carries [zland]/[zlor]/
        [zlxor], defined through `Nat.land`/`Nat.lor`/`Nat.lxor` on the
        [toNat] representatives.  The one negative
        mask , `Z.land z (-2)` ([jalr_tgtZ]), is carried as
        [zland_m2], whose two's-complement identity `z land (-2) = z - z
        mod 2` holds for EVERY [Int] [z], so that case is exact, not an
        approximation.
      * [Z.shiftl a k] ↦ [a * 2^k] and [Z.shiftr a k] ↦ [Int.ediv a (2^k)]
        ([zshiftl]/[zshiftr]), the value `a * 2^k` / `a / 2^k` for `k ≥ 0`
        (all this file uses).
      * [Z.quot]/[Z.rem] ↦ [Int.tdiv]/[Int.tmod] (truncating, as in RISC-V),
        [Z.div]/[Z.modulo] ↦ [Int.ediv]/[Int.emod].
      * [Z.testbit] ↦ [Nat.testBit] on the [toNat] representative; the two
        [Z.testbit] helper lemmas are stated at that level.
      * Width hypotheses.  `bv_sign_extend 64`  is only ever used
        with `n ≤ 64`; Lean's [BitVec.signExtend] truncates for wider
        sources, so those lemmas carry the bound explicitly (`hn : n ≤ 64`).
 Files using [mkst] must work inside
        `section ... variable [fx : FPState] ... end` or name an instance.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PlacementSearch

namespace LinuxSem.Common.PropExec

-- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the two linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PlacementSearch

/-! ## The `Int`-level vocabulary Lean core does not provide -/

/-- `bv_wrap`: `z mod 2^n`, the non-negative representative. -/
def bv_wrap (n : Nat) (z : Int) : Int := z % ((2 ^ n : Nat) : Int)

/-- `bv_swrap`: the signed wrap,
    `((z + 2^(n-1)) mod 2^n) - 2^(n-1)`. -/
def bv_swrap (n : Nat) (z : Int) : Int :=
  (z + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) - ((2 ^ (n - 1) : Nat) : Int)

/-- Bitwise and on non-negative arguments (Lean core has no [Int.land];
    `Nat.land` on the `toNat` representatives is what `Z.land` computes
    there).  Every use site below has `a, b ≥ 0`. -/
def zland (a b : Int) : Int := ((a.toNat &&& b.toNat : Nat) : Int)

/-- Bitwise or on non-negative arguments (see [zland]). -/
def zlor (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)

/-- Bitwise xor on non-negative arguments (see [zland]). -/
def zlxor (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

/-- `Z.land z (-2)` — the jalr target's "clear bit 0" mask.  The
    two's-complement identity `z land -2 = z - z mod 2` is exact for every
    [Int], so this is the exact mask, not an approximation. -/
def zland_m2 (z : Int) : Int := z - z % 2

/-- Left shift of `a` by `k ≥ 0`: multiplication by `2^k`. -/
def zshiftl (a : Int) (k : Nat) : Int := a * ((2 ^ k : Nat) : Int)

/-- Right shift of `a` by `k ≥ 0`: floor division by `2^k`.   -/
def zshiftr (a : Int) (k : Nat) : Int := a / ((2 ^ k : Nat) : Int)

/-! ## State constructors and register helpers -/

/-- The FP half of the machine state: the register file and the fcsr.

    The state shape every per-instruction step lemma is stated at PINS the
    four fields no integer instruction touches — no pending syscall, no live
    LR/SC reservation, an empty FP register file and a cleared fcsr, all of
    them exactly what [Run.init_machine_state] starts from.  Pinning rather
    than quantifying is what keeps the step lemmas' statements (and so the
    example proofs) unchanged as the machine state grows: an integer
    instruction PRESERVES these fields, so a lemma of the form
    `step (mkst ...) = MachineOk (mkst ...)` stays true and stays provable by
    computation.

    FP-STATE GENERALIZATION: the FP register file and fcsr are carried by an
    ambient typeclass instance [fx : FPState], so every lemma below is
    polymorphic in the (integer-instruction-preserved) FP state instead of
    pinning it to the initial one.  [fx0] is the FP state at process entry. -/
class FPState where
  /-- The floating-point register file. -/
  fp_regs : BvMap word
  /-- The stored fcsr (fflags + frm). -/
  fp_csr : BitVec 32

/-- The FP state at process entry: an empty FP register file and a cleared
    fcsr. -/
@[reducible] def fx0 : FPState := ⟨bvmap_empty, BitVec.ofInt 32 0⟩

/-- The machine state shape every step lemma below is stated at. -/
def mkst [fx : FPState] (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := none, ms_resv := none, ms_fcsr := fx.fp_csr,
    ms_mem := mem, ms_rom := rom }

section WithFP1

variable [fx : FPState]

/-- The register file is a `BvMap word`, the same representation the ISA core
    ([Sem.core]) uses; [getr] mirrors [Sem.rget] (x0 forced to 0, missing
    keys read as 0 via [reg_get]) and [regupd] is a plain map update.
    Register-file equalities are STRUCTURAL map equalities — no functional
    extensionality involved. -/
def getr (regs : BvMap word) (r : reg) : word :=
  if bv_eqb r 0 then (0 : word) else reg_get regs r

/-- Bind a register (x0 included: the caller decides). -/
def regupd (regs : BvMap word) (r : reg) (v : word) : BvMap word :=
  bvmapSet r v regs

/-! ## Small conversion helpers (all definitional) -/

/-- [bv_eqb r 0] is [is_x0 r]. -/
theorem bv_eqb0_is_x0 (r : reg) : bv_eqb r 0 = is_x0 r := by
  unfold bv_eqb is_x0
  have e1 : (r == (0:reg)) = decide (r = 0) := rfl
  have e2 : (r.toNat == 0) = decide (r.toNat = 0) := rfl
  rw [e1, e2, decide_eq_decide]
  exact ⟨fun h => by subst h; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

/-- x0 is x0. -/
theorem is_x0_0 : is_x0 0 = true := by decide

/-- The wrap at width 64 is a mod. -/
theorem bv_wrap64_mod (z : Int) : bv_wrap 64 z = z % 2 ^ 64 := rfl

/-- The wrap at width 32 is a mod. -/
theorem bv_wrap32_mod (z : Int) : bv_wrap 32 z = z % 2 ^ 32 := rfl

/-- Bitvector equality is reflexive. -/
theorem bv_eqb_refl {n : Nat} (a : BitVec n) : bv_eqb a a = true := by
  simp [bv_eqb]

/-- Bitvector inequality is `false`. -/
theorem bv_eqb_neq {n : Nat} (a b : BitVec n) (h : a ≠ b) : bv_eqb a b = false := by
  simp [bv_eqb, h]

/-- The argument registers of the raw ecall record, as [reg] indices.  These
    collapse the `BitVec.ofInt 5 (10 + k)` index shape (from
    [record_gpr]/`reg_get regs (10 + k)`) to the literal [reg] a0/a1/a2.  Kept
    here (below every Common sim/exec file) so all of them — and the
    FileSim-based examples — reuse a single copy instead of the inline
    `assert (E1k : ...) by (apply bv_eq; reflexivity)` boilerplate. -/
theorem arg_reg_0 : BitVec.ofInt 5 (10 + (0 : Int)) = (10 : reg) := by decide
theorem arg_reg_1 : BitVec.ofInt 5 (10 + (1 : Int)) = (11 : reg) := by decide
theorem arg_reg_2 : BitVec.ofInt 5 (10 + (2 : Int)) = (12 : reg) := by decide

/-- Sign extension to the full word is `ofInt` of the signed reading.
    the width bound is explicit — Lean's [BitVec.signExtend]
    truncates for wider sources, and  only sign-extends `n ≤ 64`. -/
theorem sext_eq_ofInt {n m : Nat} (imm : BitVec n) (hn : n ≤ m) :
    sext m imm = BitVec.ofInt m imm.toInt := by
  unfold sext
  rw [← BitVec.toInt_signExtend_of_le (x := imm) (v := m) hn]
  exact (BitVec.ofInt_toInt).symm

/-- The `toInt` of `ofInt 64` of a signed reading: `ofInt`/`sext` agree. -/
theorem toInt_ofInt_sext {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    (BitVec.ofInt 64 imm.toInt).toInt = imm.toInt := by
  rw [← sext_eq_ofInt imm hn]
  exact BitVec.toInt_signExtend_of_le hn

/-! ## Z-level range/bit helpers for the bridge proofs -/

/-- The balanced mod at width 32 is the 32-bit signed wrap. -/
theorem bmod32_eq_swrap (z : Int) : z.bmod (2 ^ 32) = bv_swrap 32 z := by
  rw [Int.bmod_def]
  unfold bv_swrap
  split <;> omega

/-- The balanced mod at width 16 is the 16-bit signed wrap. -/
theorem bmod16_eq_swrap (z : Int) : z.bmod (2 ^ 16) = bv_swrap 16 z := by
  rw [Int.bmod_def]
  unfold bv_swrap
  split <;> omega

/-- Above a bound that fits, every bit is clear.   -/
theorem Z_testbit_high (n a k : Nat) (ha : a < 2 ^ n) (hk : n ≤ k) :
    Nat.testBit a k = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hk))

/-- The converse: if every bit from `n` up is clear, the value is below
    `2^n`. -/
theorem Z_bounded_by_bits (n a : Nat)
    (hb : ∀ k, n ≤ k → Nat.testBit a k = false) : a < 2 ^ n := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0]; exact Nat.two_pow_pos n
  · have ha0 : a ≠ 0 := Nat.ne_of_gt hpos
    by_cases h : a < 2 ^ n
    · exact h
    · have hbit : Nat.testBit a (Nat.log2 a) = true := Nat.testBit_log2 ha0
      have hk : n ≤ Nat.log2 a := (Nat.le_log2 ha0).mpr (Nat.le_of_not_lt h)
      rw [hb _ hk] at hbit
      exact Bool.noConfusion hbit

/-- A land of a bounded value stays bounded. -/
theorem Z_land_range (a b : Int) (ha : 0 ≤ a ∧ a < 2 ^ 64) (hb : 0 ≤ b) :
    0 ≤ zland a b ∧ zland a b < 2 ^ 64 := by
  unfold zland
  have h1 : a.toNat < 2 ^ 64 := by simpa using ha.2
  have h2 : (a.toNat &&& b.toNat) ≤ a.toNat := Nat.and_le_left
  omega

/-- A lor of two bounded values stays bounded. -/
theorem Z_lor_range (a b : Int) (ha : 0 ≤ a ∧ a < 2 ^ 64) (hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ zlor a b ∧ zlor a b < 2 ^ 64 := by
  unfold zlor
  have h1 : a.toNat < 2 ^ 64 := by simpa using ha.2
  have h2 : b.toNat < 2 ^ 64 := by simpa using hb.2
  have h3 : (a.toNat ||| b.toNat) < 2 ^ 64 := Nat.or_lt_two_pow h1 h2
  omega

/-- An lxor of two bounded values stays bounded. -/
theorem Z_lxor_range (a b : Int) (ha : 0 ≤ a ∧ a < 2 ^ 64) (hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ zlxor a b ∧ zlxor a b < 2 ^ 64 := by
  unfold zlxor
  have h1 : a.toNat < 2 ^ 64 := by simpa using ha.2
  have h2 : b.toNat < 2 ^ 64 := by simpa using hb.2
  have h3 : (a.toNat ^^^ b.toNat) < 2 ^ 64 := Nat.xor_lt_two_pow h1 h2
  omega

/-- A right shift of a bounded value stays bounded. -/
theorem Z_shiftr_range (a k : Int) (ha : 0 ≤ a ∧ a < 2 ^ 64) (hk : 0 ≤ k) :
    0 ≤ zshiftr a k.toNat ∧ zshiftr a k.toNat < 2 ^ 64 := by
  unfold zshiftr
  have hpos : (0 : Int) < ((2 ^ k.toNat : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hnn : 0 ≤ a / ((2 ^ k.toNat : Nat) : Int) := Int.ediv_nonneg ha.1 (by omega)
  have hle : a / ((2 ^ k.toNat : Nat) : Int) ≤ a := Int.ediv_le_self _ ha.1
  omega

/-- [bv_swrap] absorbs an inner [bv_wrap] on either summand. -/
theorem bv_swrap_add_idemp_l (n : Nat) (x y : Int) :
    bv_swrap n (bv_wrap n x + y) = bv_swrap n (x + y) := by
  unfold bv_swrap bv_wrap
  have h1 : x % ((2 ^ n : Nat) : Int) + y + ((2 ^ (n - 1) : Nat) : Int)
      = x % ((2 ^ n : Nat) : Int) + (y + ((2 ^ (n - 1) : Nat) : Int)) := by omega
  have h2 : x + y + ((2 ^ (n - 1) : Nat) : Int)
      = x + (y + ((2 ^ (n - 1) : Nat) : Int)) := by omega
  rw [h1, h2, Int.emod_add_emod]

/-- Right-summand version. -/
theorem bv_swrap_add_idemp_r (n : Nat) (x y : Int) :
    bv_swrap n (x + bv_wrap n y) = bv_swrap n (x + y) := by
  rw [Int.add_comm x, bv_swrap_add_idemp_l, Int.add_comm]

/-- [bv_swrap] only depends on the argument mod `2^n`. -/
theorem bv_swrap_wrap' (n : Nat) (z : Int) : bv_swrap n (bv_wrap n z) = bv_swrap n z := by
  unfold bv_swrap bv_wrap
  rw [Int.emod_add_emod]

end WithFP1

section WithFP1b

variable [fx : FPState]

/-! ## Value shapes (Int normal forms over `toNat`/`toInt`) -/

/-- Signed view of a register value. -/
def zsig (x : word) : Int := x.toInt

def v_addi (x : word) (imm : Int) : word := BitVec.ofInt 64 ((x.toNat : Int) + imm)
def v_add (x y : word) : word := BitVec.ofInt 64 ((x.toNat : Int) + (y.toNat : Int))
def v_sub (x y : word) : word := BitVec.ofInt 64 ((x.toNat : Int) - (y.toNat : Int))
def v_mul (x y : word) : word := BitVec.ofInt 64 ((x.toNat : Int) * (y.toNat : Int))
def v_andi (x : word) (imm : Int) : word := BitVec.ofInt 64 (zland (x.toNat : Int) (bv_wrap 64 imm))
def v_ori (x : word) (imm : Int) : word := BitVec.ofInt 64 (zlor (x.toNat : Int) (bv_wrap 64 imm))
def v_xori (x : word) (imm : Int) : word := BitVec.ofInt 64 (zlxor (x.toNat : Int) (bv_wrap 64 imm))
def v_and (x y : word) : word := BitVec.ofInt 64 (zland (x.toNat : Int) (y.toNat : Int))
def v_or (x y : word) : word := BitVec.ofInt 64 (zlor (x.toNat : Int) (y.toNat : Int))
def v_xor (x y : word) : word := BitVec.ofInt 64 (zlxor (x.toNat : Int) (y.toNat : Int))

def c_eq (x y : word) : Bool := bv_eqb x y
def c_lts (x y : word) : Bool := bv_lts x y
def c_ltu (x y : word) : Bool := bv_ltu x y

def btgt (pc : word) (imm : Int) : word := v_addi pc imm

/-- Comparisons: 0/1 results. -/
def v_slti (x : word) (imm : Int) : word :=
  if x.toInt < imm then BitVec.ofInt 64 1 else BitVec.ofInt 64 0
def v_sltiu (x : word) (imm : Int) : word :=
  if (x.toNat : Int) < bv_wrap 64 imm then BitVec.ofInt 64 1 else BitVec.ofInt 64 0
def v_slt (x y : word) : word := if c_lts x y then BitVec.ofInt 64 1 else BitVec.ofInt 64 0
def v_sltu (x y : word) : word := if c_ltu x y then BitVec.ofInt 64 1 else BitVec.ofInt 64 0

/-- Immediate shifts (the shift amount is the 6-bit shamt, as Int). -/
def v_slli (x : word) (sh : Int) : word := BitVec.ofInt 64 (zshiftl (x.toNat : Int) sh.toNat)
def v_srli (x : word) (sh : Int) : word := BitVec.ofInt 64 (zshiftr (x.toNat : Int) sh.toNat)
def v_srai (x : word) (sh : Int) : word := BitVec.ofInt 64 (zshiftr (zsig x) sh.toNat)

/-- Register shifts (the shift amount is the rs2 value mod 64). -/
def v_sll (x y : word) : word := BitVec.ofInt 64 (zshiftl (x.toNat : Int) (y.toNat % 64))
def v_srl (x y : word) : word := BitVec.ofInt 64 (zshiftr (x.toNat : Int) (y.toNat % 64))
def v_sra (x y : word) : word := BitVec.ofInt 64 (zshiftr (zsig x) (y.toNat % 64))

/-- Upper immediates: [imm] is the ALREADY-SHIFTED signed U-immediate. -/
def v_lui (imm : Int) : word := BitVec.ofInt 64 imm
def v_auipc (pc : word) (imm : Int) : word := BitVec.ofInt 64 (imm + (pc.toNat : Int))

/-- RV64 word ops: compute in 32 bits, sign-extend to 64. -/
def v_addiw (x : word) (imm : Int) : word :=
  BitVec.ofInt 64 (bv_swrap 32 ((x.toNat : Int) + imm))
def v_slliw (x : word) (sh : Int) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftl (x.toNat : Int) sh.toNat))
def v_srliw (x : word) (sh : Int) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftr (bv_wrap 32 (x.toNat : Int)) sh.toNat))
def v_sraiw (x : word) (sh : Int) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftr (bv_swrap 32 (x.toNat : Int)) sh.toNat))
def v_addw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 ((x.toNat : Int) + (y.toNat : Int)))
def v_subw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 ((x.toNat : Int) - (y.toNat : Int)))
def v_sllw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftl (x.toNat : Int) (y.toNat % 32)))
def v_srlw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftr (bv_wrap 32 (x.toNat : Int)) (y.toNat % 32)))
def v_sraw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 (zshiftr (bv_swrap 32 (x.toNat : Int)) (y.toNat % 32)))

/-- High multiplies. -/
def v_mulh (x y : word) : word :=
  BitVec.ofInt 64 (zshiftr (x.toInt * y.toInt) 64)
def v_mulhsu (x y : word) : word :=
  BitVec.ofInt 64 (zshiftr (x.toInt * (y.toNat : Int)) 64)
def v_mulhu (x y : word) : word :=
  BitVec.ofInt 64 (zshiftr ((x.toNat : Int) * (y.toNat : Int)) 64)
def v_mulw (x y : word) : word :=
  BitVec.ofInt 64 (bv_swrap 32 ((x.toNat : Int) * (y.toNat : Int)))

/-- Division family: only the divide-by-zero split remains (signed overflow
    needs no case in the model: the wrap handles min / -1). -/
def v_div (x y : word) : word :=
  if (y.toNat : Int) = 0 then BitVec.ofInt 64 (-1)
  else BitVec.ofInt 64 (Int.tdiv (zsig x) (zsig y))
def v_rem (x y : word) : word :=
  if (y.toNat : Int) = 0 then x
  else BitVec.ofInt 64 (Int.tmod (zsig x) (zsig y))
def v_divw (x y : word) : word :=
  if bv_wrap 32 (y.toNat : Int) = 0 then BitVec.ofInt 64 (-1)
  else BitVec.ofInt 64 (bv_swrap 32 (Int.tdiv (bv_swrap 32 (x.toNat : Int))
                                              (bv_swrap 32 (y.toNat : Int))))
def v_remw (x y : word) : word :=
  if bv_wrap 32 (y.toNat : Int) = 0 then BitVec.ofInt 64 (bv_swrap 32 (x.toNat : Int))
  else BitVec.ofInt 64 (bv_swrap 32 (Int.tmod (bv_swrap 32 (x.toNat : Int))
                                              (bv_swrap 32 (y.toNat : Int))))
def v_divuw (x y : word) : word :=
  if bv_wrap 32 (y.toNat : Int) = 0 then BitVec.ofInt 64 (-1)
  else BitVec.ofInt 64 (bv_swrap 32 (Int.ediv (bv_wrap 32 (x.toNat : Int))
                                              (bv_wrap 32 (y.toNat : Int))))
def v_remuw (x y : word) : word :=
  if bv_wrap 32 (y.toNat : Int) = 0 then BitVec.ofInt 64 (bv_swrap 32 (x.toNat : Int))
  else BitVec.ofInt 64 (bv_swrap 32 (Int.emod (bv_wrap 32 (x.toNat : Int))
                                              (bv_wrap 32 (y.toNat : Int))))

/-- Signed-load register results. -/
def v_lb (b : byte) : word := BitVec.ofInt 64 b.toInt
def v_lh (v : word) : word := BitVec.ofInt 64 (bv_swrap 16 (v.toNat : Int))
def v_lw (v : word) : word := BitVec.ofInt 64 (bv_swrap 32 (v.toNat : Int))

/-- jalr target: `(rs1 + imm)` with bit 0 cleared. -/
def jalr_tgtZ (x : word) (imm : Int) : Int := zland_m2 ((x.toNat : Int) + imm)
def jalr_tgt (x : word) (imm : Int) : word := BitVec.ofInt 64 (jalr_tgtZ x imm)

/-! ## Memory read/write mirrors -/

/-- The read-only image as a byte function: a one-byte [memory_read]. -/
def seg_rom (segs : List Segment) : word → Option byte :=
  fun addr =>
    match memory_read segs addr 1 with
    | some (b :: _) => some b
    | _ => none

/-- Read [n] bytes at [a], preferring the writable overlay [mem] and falling
    back to the static image. -/
def rdn (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match (match mem a with
           | some b => some b
           | none => seg_rom segs a) with
    | some b =>
      match rdn segs mem (a + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- The tree interpreter's overlay read is [rdn]. -/
theorem ov_rdn (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word) :
    ov_read_bytes segs mem a n = rdn segs mem a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [ov_read_bytes, rdn, seg_rom]
    cases h : mem a with
    | some b => simp only [h, ih]; rfl
    | none =>
      cases h2 : memory_read segs a 1 with
      | none => simp only [h, h2]
      | some bs =>
        cases bs with
        | nil => simp only [h, h2]
        | cons b rest => simp only [h, h2]; rw [ih (a + 1)]; rfl

/-- Loaded-value bridges: [interp_eff] hands [le_bytes_to_word bs] to the
    [ELoad] continuation. -/
theorem le_word_1 (b : byte) : le_bytes_to_word [b] = BitVec.ofInt 64 (b.toNat : Int) := by
  simp [le_bytes_to_word, bytes_le_to_Z, bytes_le_to_Nat]

/-- A byte list whose value is already the unsigned reading of [v] loads
    as [v]. -/
theorem le_word_v (bs : List byte) (v : word) (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    le_bytes_to_word bs = v := by
  unfold le_bytes_to_word
  rw [Hv, BitVec.ofInt_natCast]
  simp

/-- Extracting the low byte of a widened byte is the byte. -/
theorem b_extract8_id (b : byte) : bits 0 8 (BitVec.ofInt 64 (b.toNat : Int)) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [bits, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero]
  have h1 : (0 : Int) ≤ (b.toNat : Int) := by omega
  have h2 : (b.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
    have := b.isLt; omega
  rw [Int.emod_eq_of_lt h1 h2, Int.toNat_natCast, Nat.mod_eq_of_lt b.isLt]

/-- Signed-load value bridges ([v_lb]/[v_lh] are defined above). -/
theorem b_lb_val (b : byte) : sext 64 (bits 0 8 (le_bytes_to_word [b])) = v_lb b := by
  rw [le_word_1, b_extract8_id]
  exact sext_eq_ofInt b (by decide : 8 ≤ 64)

/-- The halfword bridge. -/
theorem b_lh_val (v : word) : sext 64 (bits 0 16 v) = v_lh v := by
  have h1 : sext 64 (bits 0 16 v) = BitVec.ofInt 64 (bits 0 16 v).toInt :=
    sext_eq_ofInt (n := 16) (m := 64) (imm := bits 0 16 v) (by decide)
  rw [show (bits 0 16 v).toInt = (v.toNat : Int).bmod (2 ^ 16) from by
        simp only [bits, BitVec.toInt_extractLsb', Nat.shiftRight_zero],
      bmod16_eq_swrap] at h1
  exact h1

/-- The word bridge. -/
theorem b_lw_val (v : word) : sext 64 (bits 0 32 v) = v_lw v := by
  have h1 : sext 64 (bits 0 32 v) = BitVec.ofInt 64 (bits 0 32 v).toInt :=
    sext_eq_ofInt (n := 32) (m := 64) (imm := bits 0 32 v) (by decide)
  rw [show (bits 0 32 v).toInt = (v.toNat : Int).bmod (2 ^ 32) from by
        simp only [bits, BitVec.toInt_extractLsb', Nat.shiftRight_zero],
      bmod32_eq_swrap] at h1
  exact h1

/-- A read of [n] bytes is [n] bytes long. -/
theorem rdn_length (segs : List Segment) (mem : word → Option byte) (n : Nat) (a : word)
    (bs : List byte) (H : rdn segs mem a n = some bs) : bs.length = n := by
  induction n generalizing a bs with
  | zero =>
    simp only [rdn, Option.some.injEq] at H
    subst H; rfl
  | succ n ih =>
    simp only [rdn] at H
    split at H
    · rename_i b _
      split at H
      · rename_i rest hr
        simp only [Option.some.injEq] at H
        subst H
        simp only [List.length_cons, ih (a + 1) rest hr]
      · exact absurd H (by simp)
    · exact absurd H (by simp)

end WithFP1b

section WithFP1c

variable [fx : FPState]

/-! ## Value bridges: the exec-produced bv expressions equal the v_*
    normal forms. -/

/-- `a + sext imm` is `v_addi`. -/
theorem b_addsext (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    a + sext 64 imm = v_addi a imm.toInt := by
  rw [sext_eq_ofInt imm hn]
  unfold v_addi
  bv_omega

/-- The pc increment. -/
theorem b_npc4 (p : word) : p + BitVec.ofInt 64 4 = v_addi p 4 := by
  unfold v_addi
  bv_omega

/-- `alu64 ADD` on a sign-extended immediate. -/
theorem alu_addi (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    alu64 .ADD a (sext 64 imm) = v_addi a imm.toInt :=
  b_addsext a imm hn

/-- The low-64 `toNat` of an `ofInt` is a residue. -/
theorem toNat_ofInt_64 (i : Int) :
    (BitVec.ofInt 64 i).toNat = (i % ((2 ^ 64 : Nat) : Int)).toNat :=
  BitVec.toNat_ofInt i

/-- `2^64` is positive, in the shape the `BitVec` lemmas use. -/
theorem two64_pos_int : (0 : Int) < ((2 ^ 64 : Nat) : Int) := by
  rw [Int.natCast_pow]
  exact Int.pow_pos (by decide)

/-- `2^32` is positive, in the shape the `BitVec` lemmas use. -/
theorem two32_pos_int : (0 : Int) < ((2 ^ 32 : Nat) : Int) := by
  rw [Int.natCast_pow]
  exact Int.pow_pos (by decide)

/-- A 32-bit residue cast back. -/
theorem natCast_emod32_toNat (i : Int) :
    ((i % ((2 ^ 32 : Nat) : Int)).toNat : Int) = i % ((2 ^ 32 : Nat) : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have h := two32_pos_int; omega))

/-- The residue is in range. -/
theorem emod64_bounds (i : Int) :
    0 ≤ i % ((2 ^ 64 : Nat) : Int) ∧ i % ((2 ^ 64 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) :=
  ⟨Int.emod_nonneg _ (by have h := two64_pos_int; omega), Int.emod_lt_of_pos _ two64_pos_int⟩

/-- The residue `toNat` is below `2^64`. -/
theorem emod64_toNat_lt (i : Int) : (i % ((2 ^ 64 : Nat) : Int)).toNat < 2 ^ 64 := by
  have := (emod64_bounds i).2
  omega

/-- The residue `toNat`, cast back, is the residue. -/
theorem natCast_emod64_toNat (i : Int) :
    ((i % ((2 ^ 64 : Nat) : Int)).toNat : Int) = i % ((2 ^ 64 : Nat) : Int) :=
  Int.toNat_of_nonneg (emod64_bounds i).1

/-- `alu64 AND` on a sign-extended immediate. -/
theorem alu_andi (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    alu64 .AND a (sext 64 imm) = v_andi a imm.toInt := by
  rw [sext_eq_ofInt imm hn]
  simp only [v_andi, zland, bv_wrap, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofInt, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (emod64_toNat_lt imm.toInt))]

/-- `alu64 OR` on a sign-extended immediate. -/
theorem alu_ori (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    alu64 .OR a (sext 64 imm) = v_ori a imm.toInt := by
  rw [sext_eq_ofInt imm hn]
  simp only [v_ori, zlor, bv_wrap, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofInt, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by have := a.isLt; simpa using this)
    (emod64_toNat_lt imm.toInt))]

/-- `alu64 XOR` on a sign-extended immediate. -/
theorem alu_xori (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    alu64 .XOR a (sext 64 imm) = v_xori a imm.toInt := by
  rw [sext_eq_ofInt imm hn]
  simp only [v_xori, zlxor, bv_wrap, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofInt, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by have := a.isLt; simpa using this)
    (emod64_toNat_lt imm.toInt))]

/-- `alu64 SLT` on a 12-bit sign-extended immediate. -/
theorem alu_slti (a : word) (imm : BitVec 12) :
    alu64 .SLT a (sext 64 imm) = v_slti a imm.toInt := by
  simp only [v_slti, alu64, alu, bv_lts, sext,
    BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  by_cases h : a.toInt < imm.toInt <;> simp [h]

/-- `alu64 SLTU` on a sign-extended immediate. -/
theorem alu_sltiu (a : word) {n : Nat} (imm : BitVec n) (hn : n ≤ 64) :
    alu64 .SLTU a (sext 64 imm) = v_sltiu a imm.toInt := by
  simp only [alu64, alu, v_sltiu, bv_wrap, bv_ltu, sext_eq_ofInt imm hn, BitVec.toNat_ofInt,
    decide_eq_true_eq]
  have hK0 : 0 ≤ imm.toInt % ((2 ^ 64 : Nat) : Int) :=
    Int.emod_nonneg _ (by have h := two64_pos_int; omega)
  have h : (a.toNat < (imm.toInt % ((2 ^ 64 : Nat) : Int)).toNat)
      ↔ ((a.toNat : Int) < imm.toInt % ((2 ^ 64 : Nat) : Int)) := by omega
  by_cases hq : ((a.toNat : Int) < imm.toInt % ((2 ^ 64 : Nat) : Int))
  · simp [hq, h.mpr hq]
    /- `simp` normalizes both guards to the same proposition and stops
       there; the closing step is `rfl`, which checks the resulting
       `if … = if …` directly. -/
    rfl
  · simp [hq, fun hc => hq (h.mp hc)]
    rfl

/-- `alu64 ADD`. -/
theorem alu_add (a b : word) : alu64 .ADD a b = v_add a b := by
  unfold v_add alu64 alu
  bv_omega

/-- `alu64 SUB`. -/
theorem alu_sub (a b : word) : alu64 .SUB a b = v_sub a b := by
  unfold v_sub alu64 alu
  bv_omega

/-- `alu64 SLT`. -/
theorem alu_slt (a b : word) : alu64 .SLT a b = v_slt a b := rfl

/-- `alu64 SLTU`. -/
theorem alu_sltu (a b : word) : alu64 .SLTU a b = v_sltu a b := rfl

/-- `alu64 AND`. -/
theorem alu_and (a b : word) : alu64 .AND a b = v_and a b := by
  simp only [v_and, zland, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (by have := b.isLt; simpa using this))]

/-- `alu64 OR`. -/
theorem alu_or (a b : word) : alu64 .OR a b = v_or a b := by
  simp only [v_or, zlor, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by have := a.isLt; simpa using this)
    (by have := b.isLt; simpa using this))]

/-- `alu64 XOR`. -/
theorem alu_xor (a b : word) : alu64 .XOR a b = v_xor a b := by
  simp only [v_xor, zlxor, alu64, alu]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Int.toNat_natCast]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by have := a.isLt; simpa using this)
    (by have := b.isLt; simpa using this))]

end WithFP1c

section WithFP1d

variable [fx : FPState]

/-! ## Shift-amount views -/

/-- `zext` preserves the unsigned reading. -/
theorem toNat_zext {n m : Nat} (x : BitVec n) (h : n ≤ m) : (zext m x).toNat = x.toNat := by
  simp only [zext, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- Masking with 63 is a mod 64. -/
theorem and63_toNat (x : word) : (x &&& BitVec.ofInt 64 63).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_and]
  have h63 : (BitVec.ofInt 64 63).toNat = 63 := by decide
  rw [h63, show (63 : Nat) = 2 ^ 6 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- The 6-bit shamt view. -/
theorem shamt6_mask (s : BitVec 6) :
    (zext 64 s &&& BitVec.ofInt 64 63).toNat = s.toNat := by
  rw [and63_toNat, toNat_zext s (by decide), Nat.mod_eq_of_lt s.isLt]

/-- The 64-bit register-amount view. -/
theorem regamt64_mask (b : word) :
    (b &&& BitVec.ofInt 64 63).toNat = (b.toNat % 64 : Nat) := and63_toNat b

/-- `alu64 SLL` on a 6-bit shamt. -/
theorem alu_slli (a : word) (s : BitVec 6) :
    alu64 .SLL a (zext 64 s) = v_slli a s.toNat := by
  simp only [alu64, alu, v_slli, zshiftl, shamt6_mask, Int.toNat_natCast]
  rw [show ((BitVec.toNat a : Int) * ((2 ^ s.toNat : Nat) : Int))
      = ((BitVec.toNat a * 2 ^ s.toNat : Nat) : Int) from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

/-- `alu64 SRL` on a 6-bit shamt. -/
theorem alu_srli (a : word) (s : BitVec 6) :
    alu64 .SRL a (zext 64 s) = v_srli a s.toNat := by
  simp only [alu64, alu, v_srli, zshiftr, shamt6_mask, Int.toNat_natCast]
  rw [show ((BitVec.toNat a : Int) / ((2 ^ s.toNat : Nat) : Int))
      = ((BitVec.toNat a / 2 ^ s.toNat : Nat) : Int) from (Int.natCast_ediv _ _).symm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)).symm

/-- `alu64 SRA` on a 6-bit shamt. -/
theorem alu_srai (a : word) (s : BitVec 6) :
    alu64 .SRA a (zext 64 s) = v_srai a s.toNat := by
  simp only [alu64, alu, v_srai, zshiftr, zsig, shamt6_mask, Int.toNat_natCast]
  rw [show a.sshiftRight s.toNat = BitVec.ofInt 64 (a.toInt >>> s.toNat) from rfl]
  rw [Int.shiftRight_eq_div_pow]

/-- `alu64 SLL`. -/
theorem alu_sll (a b : word) : alu64 .SLL a b = v_sll a b := by
  simp only [alu64, alu, v_sll, zshiftl, regamt64_mask]
  rw [show ((BitVec.toNat a : Int) * ((2 ^ (BitVec.toNat b % 64) : Nat) : Int))
      = ((BitVec.toNat a * 2 ^ (BitVec.toNat b % 64) : Nat) : Int) from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

/-- `alu64 SRL`. -/
theorem alu_srl (a b : word) : alu64 .SRL a b = v_srl a b := by
  simp only [alu64, alu, v_srl, zshiftr, regamt64_mask]
  rw [show ((BitVec.toNat a : Int) / ((2 ^ (BitVec.toNat b % 64) : Nat) : Int))
      = ((BitVec.toNat a / 2 ^ (BitVec.toNat b % 64) : Nat) : Int) from (Int.natCast_ediv _ _).symm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)).symm

/-- `alu64 SRA`. -/
theorem alu_sra (a b : word) : alu64 .SRA a b = v_sra a b := by
  simp only [alu64, alu, v_sra, zshiftr, zsig, regamt64_mask]
  rw [show a.sshiftRight (b.toNat % 64) = BitVec.ofInt 64 (a.toInt >>> (b.toNat % 64)) from rfl]
  rw [Int.shiftRight_eq_div_pow]

end WithFP1d

section WithFP1e

variable [fx : FPState]

/-! ## W-op (32-bit) bridges -/

/-- A 32-bit signed wrap, widened, is the sign extension of the 32-bit
    `ofInt`.  This is the bridge every `.w` value shape goes through. -/
theorem ofInt_swrap32 (z : Int) :
    BitVec.ofInt 64 (bv_swrap 32 z) = sext 64 (BitVec.ofInt 32 z) := by
  rw [sext_eq_ofInt _ (by decide : 32 ≤ 64), BitVec.toInt_ofInt, ← bmod32_eq_swrap]

/-- The 16-bit version. -/
theorem ofInt_swrap16 (z : Int) :
    BitVec.ofInt 64 (bv_swrap 16 z) = sext 64 (BitVec.ofInt 16 z) := by
  rw [sext_eq_ofInt _ (by decide : 16 ≤ 64), BitVec.toInt_ofInt, ← bmod16_eq_swrap]

/-- The unsigned reading of `low32`. -/
theorem low32_toNat (a : word) : (low32 a).toNat = a.toNat % 2 ^ 32 := by
  simp only [low32, bits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- [low32] at the unsigned level. -/
theorem low32_unsigned (a : word) : ((low32 a).toNat : Int) = bv_wrap 32 (a.toNat : Int) := by
  rw [low32_toNat]
  unfold bv_wrap
  simp only [← Int.natCast_emod, Int.toNat_natCast]

/-- [low32] at the signed level. -/
theorem low32_signed (a : word) : (low32 a).toInt = bv_swrap 32 (a.toNat : Int) := by
  simp only [low32, bits, BitVec.toInt_extractLsb', Nat.shiftRight_zero]
  exact bmod32_eq_swrap _

/-- [low32] is `ofInt` of the value. -/
theorem low32_eq_ofInt (a : word) : low32 a = BitVec.ofInt 32 (a.toNat : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [low32_toNat, BitVec.toNat_ofInt]
  simp only [← Int.natCast_emod, Int.toNat_natCast]

/-- The 5-bit shamt view. -/
theorem shamt5_mask (s : BitVec 5) :
    (zext 32 s &&& BitVec.ofInt 32 31).toNat = s.toNat := by
  rw [BitVec.toNat_and]
  have h31 : (BitVec.ofInt 32 31).toNat = 31 := by decide
  rw [h31, toNat_zext s (by decide : 5 ≤ 32),
    show (31 : Nat) = 2 ^ 5 - 1 from by decide, Nat.and_two_pow_sub_one_of_lt_two_pow s.isLt]

/-- The 32-bit register-amount view. -/
theorem regamt32_mask (b : word) :
    ((low32 b &&& BitVec.ofInt 32 31).toNat : Nat) = b.toNat % 32 := by
  rw [BitVec.toNat_and, low32_toNat]
  have h31 : (BitVec.ofInt 32 31).toNat = 31 := by decide
  rw [h31, show (31 : Nat) = 2 ^ 5 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 5 ∣ 2 ^ 32)]

/-- Sign extension of a 32-bit result, at the unsigned level. -/
theorem sext32_unsigned (v : BitVec 32) :
    ((sext 64 v).toNat : Int) = bv_wrap 64 (bv_swrap 32 (v.toNat : Int)) := by
  rw [sext_eq_ofInt v (by decide : 32 ≤ 64), BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_bmod]
  rw [show Int.bmod (v.toNat : Int) (2 ^ 32) = bv_swrap 32 (v.toNat : Int) from bmod32_eq_swrap _]
  unfold bv_wrap
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have h := two64_pos_int; omega))

/-- The generic `.w` bridge: a 32-bit result that is `ofInt 32 K`
    sign-extends to `ofInt 64 (bv_swrap 32 K)`. -/
theorem sext_ofInt32 (x : BitVec 32) (K : Int) (h : x = BitVec.ofInt 32 K) :
    sext 64 x = BitVec.ofInt 64 (bv_swrap 32 K) := by
  rw [h, ofInt_swrap32]

end WithFP1e

section WithFP1f

variable [fx : FPState]

/-- `low32 a * low32 b` is `ofInt 32` of the product. -/
theorem mul32_low32 (a b : word) :
    low32 a * low32 b = BitVec.ofInt 32 ((a.toNat * b.toNat : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, low32_toNat, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  simp only [Nat.mul_mod, Nat.mod_mod]

/-- `alu32 ADD` of two `low32`s. -/
theorem alu32_add_low32 (a b : word) :
    alu32 .ADD (low32 a) (low32 b) = BitVec.ofInt 32 ((a.toNat + b.toNat : Nat) : Int) := by
  simp only [alu32, alu, low32_eq_ofInt]
  bv_omega

/-- `alu32 SUB` of two `low32`s. -/
theorem alu32_sub_low32 (a b : word) :
    alu32 .SUB (low32 a) (low32 b) = BitVec.ofInt 32 ((a.toNat : Int) - (b.toNat : Int)) := by
  simp only [alu32, alu, low32_eq_ofInt]
  bv_omega

/-- `alu32 ADD` of a `low32` and a sign-extended 12-bit immediate. -/
theorem alu32_add_low32_imm (a : word) (imm : BitVec 12) :
    alu32 .ADD (low32 a) (sext 32 imm) = BitVec.ofInt 32 ((a.toNat : Int) + imm.toInt) := by
  simp only [alu32, alu, low32_eq_ofInt, sext_eq_ofInt imm (by decide : 12 ≤ 32)]
  bv_omega

/-- `alu32 SLL` of a `low32` and a 5-bit shamt. -/
theorem alu32_sll_low32 (a : word) (s : BitVec 5) :
    alu32 .SLL (low32 a) (zext 32 s) =
      BitVec.ofInt 32 ((a.toNat * 2 ^ s.toNat : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu32, alu, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, low32_toNat, shamt5_mask,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  simp only [Nat.mul_mod, Nat.mod_mod]

/-- `alu32 SRL` of a `low32` and a 5-bit shamt. -/
theorem alu32_srl_low32 (a : word) (s : BitVec 5) :
    alu32 .SRL (low32 a) (zext 32 s) =
      BitVec.ofInt 32 (bv_wrap 32 (a.toNat : Int) / ((2 ^ s.toNat : Nat) : Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu32, alu, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, low32_toNat,
    shamt5_mask, BitVec.toNat_ofNat, bv_wrap]
  rw [show ((a.toNat : Int) % ((2 ^ 32 : Nat) : Int)) = ((a.toNat % 2 ^ 32 : Nat) : Int) from
        (Int.natCast_emod _ _).symm]
  rw [show (((a.toNat % 2 ^ 32 : Nat) : Int) / ((2 ^ s.toNat : Nat) : Int))
      = (((a.toNat % 2 ^ 32) / 2 ^ s.toNat : Nat) : Int) from (Int.natCast_ediv _ _).symm]
  simp only [Int.toNat_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
    (Nat.mod_lt _ (by decide : 0 < 2 ^ 32)))).symm

/-- `alu32 SRA` of a `low32` and a 5-bit shamt. -/
theorem alu32_sra_low32 (a : word) (s : BitVec 5) :
    alu32 .SRA (low32 a) (zext 32 s) =
      BitVec.ofInt 32 (bv_swrap 32 (a.toNat : Int) / ((2 ^ s.toNat : Nat) : Int)) := by
  simp only [alu32, alu, shamt5_mask]
  rw [show low32 a = BitVec.ofInt 32 (BitVec.toNat a) from low32_eq_ofInt a]
  rw [show (BitVec.ofInt 32 (BitVec.toNat a)).sshiftRight s.toNat
      = BitVec.ofInt 32 ((BitVec.ofInt 32 (BitVec.toNat a)).toInt >>> s.toNat) from rfl]
  rw [BitVec.toInt_ofInt, bmod32_eq_swrap, Int.shiftRight_eq_div_pow]

/-- `alu32 SLL` of two `low32`s. -/
theorem alu32_sll_low32_reg (a b : word) :
    alu32 .SLL (low32 a) (low32 b) =
      BitVec.ofInt 32 ((a.toNat * 2 ^ (b.toNat % 32) : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu32, alu, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, low32_toNat, regamt32_mask,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  simp only [Nat.mul_mod, Nat.mod_mod]

/-- `alu32 SRL` of two `low32`s. -/
theorem alu32_srl_low32_reg (a b : word) :
    alu32 .SRL (low32 a) (low32 b) =
      BitVec.ofInt 32 (bv_wrap 32 (a.toNat : Int) / ((2 ^ (b.toNat % 32) : Nat) : Int)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alu32, alu, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, low32_toNat,
    regamt32_mask, BitVec.toNat_ofNat, bv_wrap]
  rw [show ((a.toNat : Int) % ((2 ^ 32 : Nat) : Int)) = ((a.toNat % 2 ^ 32 : Nat) : Int) from
        (Int.natCast_emod _ _).symm]
  rw [show (((a.toNat % 2 ^ 32 : Nat) : Int) / ((2 ^ (b.toNat % 32) : Nat) : Int))
      = (((a.toNat % 2 ^ 32) / 2 ^ (b.toNat % 32) : Nat) : Int) from (Int.natCast_ediv _ _).symm]
  simp only [Int.toNat_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
    (Nat.mod_lt _ (by decide : 0 < 2 ^ 32)))).symm

/-- `alu32 SRA` of two `low32`s. -/
theorem alu32_sra_low32_reg (a b : word) :
    alu32 .SRA (low32 a) (low32 b) =
      BitVec.ofInt 32 (bv_swrap 32 (a.toNat : Int) / ((2 ^ (b.toNat % 32) : Nat) : Int)) := by
  simp only [alu32, alu, regamt32_mask]
  rw [show low32 a = BitVec.ofInt 32 (BitVec.toNat a) from low32_eq_ofInt a]
  rw [show (BitVec.ofInt 32 (BitVec.toNat a)).sshiftRight (BitVec.toNat b % 32)
      = BitVec.ofInt 32 ((BitVec.ofInt 32 (BitVec.toNat a)).toInt >>> (BitVec.toNat b % 32)) from rfl]
  rw [BitVec.toInt_ofInt, bmod32_eq_swrap, Int.shiftRight_eq_div_pow]

/-! The `.w` value bridges. -/

/-- `addiw`. -/
theorem w_addiw (a : word) (imm : BitVec 12) :
    sext 64 (alu32 .ADD (low32 a) (sext 32 imm)) = v_addiw a imm.toInt := by
  rw [alu32_add_low32_imm]
  unfold v_addiw
  exact (ofInt_swrap32 _).symm

/-- `slliw`. -/
theorem w_slliw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .SLL (low32 a) (zext 32 s)) = v_slliw a s.toNat := by
  rw [alu32_sll_low32]
  unfold v_slliw zshiftl
  exact (ofInt_swrap32 _).symm

/-- `srliw`. -/
theorem w_srliw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .SRL (low32 a) (zext 32 s)) = v_srliw a s.toNat := by
  rw [alu32_srl_low32]
  unfold v_srliw zshiftr bv_wrap
  exact (ofInt_swrap32 _).symm

/-- `sraiw`. -/
theorem w_sraiw (a : word) (s : BitVec 5) :
    sext 64 (alu32 .SRA (low32 a) (zext 32 s)) = v_sraiw a s.toNat := by
  rw [alu32_sra_low32]
  unfold v_sraiw zshiftr
  exact (ofInt_swrap32 _).symm

/-- `addw`. -/
theorem w_addw (a b : word) : sext 64 (alu32 .ADD (low32 a) (low32 b)) = v_addw a b := by
  rw [alu32_add_low32]
  unfold v_addw
  exact (ofInt_swrap32 _).symm

/-- `subw`. -/
theorem w_subw (a b : word) : sext 64 (alu32 .SUB (low32 a) (low32 b)) = v_subw a b := by
  rw [alu32_sub_low32]
  unfold v_subw
  exact (ofInt_swrap32 _).symm

/-- `sllw`. -/
theorem w_sllw (a b : word) : sext 64 (alu32 .SLL (low32 a) (low32 b)) = v_sllw a b := by
  rw [alu32_sll_low32_reg]
  unfold v_sllw zshiftl
  exact (ofInt_swrap32 _).symm

/-- `srlw`. -/
theorem w_srlw (a b : word) : sext 64 (alu32 .SRL (low32 a) (low32 b)) = v_srlw a b := by
  rw [alu32_srl_low32_reg]
  unfold v_srlw zshiftr bv_wrap
  exact (ofInt_swrap32 _).symm

/-- `sraw`. -/
theorem w_sraw (a b : word) : sext 64 (alu32 .SRA (low32 a) (low32 b)) = v_sraw a b := by
  rw [alu32_sra_low32_reg]
  unfold v_sraw zshiftr
  exact (ofInt_swrap32 _).symm

end WithFP1f

section WithFP1g

variable [fx : FPState]

/-! ## M-extension bridges -/

/-- `MUL`. -/
theorem m_mul (a b : word) : mul_div .MUL a b = v_mul a b := by
  have hv : v_mul a b = BitVec.ofInt 64 ((a.toNat * b.toNat : Nat) : Int) := rfl
  rw [hv]
  apply BitVec.eq_of_toNat_eq
  simp only [mul_div, BitVec.toNat_mul, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    Nat.mul_mod, Nat.mod_mod]

/-- `MULH`. -/
theorem m_mulh (a b : word) : mul_div .MULH a b = v_mulh a b := by
  simp only [mul_div, v_mulh, zshiftr, bv_mulhss, Int.shiftRight_eq_div_pow, Int.toNat_natCast]

/-- `MULHSU`. -/
theorem m_mulhsu (a b : word) : mul_div .MULHSU a b = v_mulhsu a b := by
  simp only [mul_div, v_mulhsu, zshiftr, bv_mulhsu, Int.shiftRight_eq_div_pow, Int.toNat_natCast]

/-- `MULHU`. -/
theorem m_mulhu (a b : word) : mul_div .MULHU a b = v_mulhu a b := by
  simp only [mul_div, v_mulhu, zshiftr, bv_mulhuu, Int.shiftRight_eq_div_pow, Int.toNat_natCast]

/-- `DIV`. -/
theorem m_div (a b : word) : mul_div .DIV a b = v_div a b := by
  simp only [mul_div, v_div]
  by_cases h : b.toNat = 0
  · simp [h]
  · have hb : (b.toNat == 0) = false := by simp [h]
    simp only [hb, Bool.false_eq_true, ite_false, ite_eq_right (by omega : ¬ ((b.toNat : Int) = 0)),
      zsig]
    rw [← BitVec.ofInt_toInt (x := a.sdiv b), BitVec.toInt_sdiv]
    simpa only [BitVec.toInt_ofInt] using
      (BitVec.ofInt_toInt (x := BitVec.ofInt 64 ((a.toInt).tdiv (b.toInt))))

/-- `REM`. -/
theorem m_rem (a b : word) : mul_div .REM a b = v_rem a b := by
  simp only [mul_div, v_rem]
  by_cases h : b.toNat = 0
  · simp [h]
  · have hb : (b.toNat == 0) = false := by simp [h]
    simp only [hb, Bool.false_eq_true, ite_false, ite_eq_right (by omega : ¬ ((b.toNat : Int) = 0)),
      zsig]
    rw [← BitVec.ofInt_toInt (x := a.srem b), BitVec.toInt_srem]

/-- `mulw`. -/
theorem w_mulw (a b : word) :
    sext 64 (mul_div .MUL (low32 a) (low32 b)) = v_mulw a b := by
  rw [show mul_div .MUL (low32 a) (low32 b) = low32 a * low32 b from rfl, mul32_low32]
  unfold v_mulw
  exact (ofInt_swrap32 _).symm

/-- A `Nat` residue is zero iff its `Int` image is. -/
theorem emod32_eq_zero_iff (x : Nat) :
    x % 2 ^ 32 = 0 ↔ (x : Int) % ((2 ^ 32 : Nat) : Int) = 0 := by
  constructor
  · intro h
    rw [← Int.natCast_emod, h]
    rfl
  · intro h
    have h2 : (((x % 2 ^ 32 : Nat)) : Int) = 0 := by rw [Int.natCast_emod]; exact h
    exact Int.natCast_eq_zero.mp h2

/-- The `div0` scrutinee of the 32-bit division family. -/
theorem div0_32_iff (b : word) : (low32 b).toNat = 0 ↔ bv_wrap 32 (b.toNat : Int) = 0 := by
  rw [low32_toNat]
  unfold bv_wrap
  exact emod32_eq_zero_iff _

/-- The Bool-shaped `div0` scrutinee of the 32-bit division family . -/
theorem div0_32 (b : word) : ((low32 b).toNat == 0) = (bv_wrap 32 (b.toNat : Int) == 0) := by
  have e1 : ((low32 b).toNat == 0) = decide ((low32 b).toNat = 0) := rfl
  have e2 : (bv_wrap 32 (b.toNat : Int) == 0) = decide (bv_wrap 32 (b.toNat : Int) = 0) := rfl
  rw [e1, e2, decide_eq_decide, div0_32_iff]

/-- `sdiv` at 32 bits is `ofInt 32` of the truncating quotient. -/
theorem sdiv32 (x y : BitVec 32) :
    x.sdiv y = BitVec.ofInt 32 (Int.tdiv x.toInt y.toInt) := by
  rw [← BitVec.ofInt_toInt (x := x.sdiv y), BitVec.toInt_sdiv]
  simpa only [BitVec.toInt_ofInt] using
    (BitVec.ofInt_toInt (x := BitVec.ofInt 32 (x.toInt.tdiv y.toInt)))

/-- `srem` at 32 bits is `ofInt 32` of the truncating remainder. -/
theorem srem32 (x y : BitVec 32) :
    x.srem y = BitVec.ofInt 32 (Int.tmod x.toInt y.toInt) := by
  rw [← BitVec.ofInt_toInt (x := x.srem y), BitVec.toInt_srem]

/-- The `-1` of the divide-by-zero branch, wrapped at 32 bits. -/
theorem bv_swrap32_neg1 : bv_swrap 32 (-1) = -1 := by decide

/-- `udiv` at 32 bits is `ofInt 32` of the unsigned quotient. -/
theorem udiv32 (x y : BitVec 32) :
    x / y = BitVec.ofInt 32 (Int.ediv (x.toNat : Int) (y.toNat : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv,
    show Int.ediv (x.toNat : Int) (y.toNat : Int) = ((x.toNat / y.toNat : Nat) : Int) from
      (Int.natCast_ediv _ _).symm,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)).symm

/-- `umod` at 32 bits is `ofInt 32` of the unsigned remainder. -/
theorem umod32 (x y : BitVec 32) :
    x % y = BitVec.ofInt 32 (Int.emod (x.toNat : Int) (y.toNat : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod,
    show Int.emod (x.toNat : Int) (y.toNat : Int) = ((x.toNat % y.toNat : Nat) : Int) from
      (Int.natCast_emod _ _).symm,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rcases Nat.eq_zero_or_pos y.toNat with h | h
  · rw [h, Nat.mod_zero]
    exact (Nat.mod_eq_of_lt x.isLt).symm
  · exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ h) (Nat.le_of_lt y.isLt))).symm

/-- `divw`. -/
theorem w_divw (a b : word) : sext 64 (mul_div .DIV (low32 a) (low32 b)) = v_divw a b := by
  simp only [mul_div, v_divw]
  rw [div0_32]
  by_cases hh : bv_wrap 32 (b.toNat : Int) = 0
  · rw [ite_eq_left (by rw [hh]; rfl), ite_eq_left hh]
    rw [show BitVec.ofInt 64 (-1) = sext 64 (BitVec.ofInt 32 (-1)) from by
          rw [← ofInt_swrap32, bv_swrap32_neg1]]
  · rw [ite_eq_right (by simp [hh]), ite_eq_right hh, sdiv32, low32_signed, low32_signed]
    exact (ofInt_swrap32 _).symm

/-- `remw`. -/
theorem w_remw (a b : word) : sext 64 (mul_div .REM (low32 a) (low32 b)) = v_remw a b := by
  simp only [mul_div, v_remw]
  rw [div0_32]
  by_cases hh : bv_wrap 32 (b.toNat : Int) = 0
  · rw [ite_eq_left (by rw [hh]; rfl), ite_eq_left hh]
    rw [low32_eq_ofInt, ← ofInt_swrap32]
  · rw [ite_eq_right (by simp [hh]), ite_eq_right hh, srem32, low32_signed, low32_signed]
    exact (ofInt_swrap32 _).symm

/-- `divuw`. -/
theorem w_divuw (a b : word) : sext 64 (mul_div .DIVU (low32 a) (low32 b)) = v_divuw a b := by
  simp only [mul_div, v_divuw]
  rw [div0_32]
  by_cases hh : bv_wrap 32 (b.toNat : Int) = 0
  · rw [ite_eq_left (by rw [hh]; rfl), ite_eq_left hh]
    rw [show BitVec.ofInt 64 (-1) = sext 64 (BitVec.ofInt 32 (-1)) from by
          rw [← ofInt_swrap32, bv_swrap32_neg1]]
  · rw [ite_eq_right (by simp [hh]), ite_eq_right hh,
      show (low32 a).udiv (low32 b) = (low32 a) / (low32 b) from rfl,
      udiv32, low32_unsigned, low32_unsigned]
    exact (ofInt_swrap32 _).symm

/-- `remuw`. -/
theorem w_remuw (a b : word) : sext 64 (mul_div .REMU (low32 a) (low32 b)) = v_remuw a b := by
  simp only [mul_div, v_remuw]
  rw [div0_32]
  by_cases hh : bv_wrap 32 (b.toNat : Int) = 0
  · rw [ite_eq_left (by rw [hh]; rfl), ite_eq_left hh]
    rw [low32_eq_ofInt, ← ofInt_swrap32]
  · rw [ite_eq_right (by simp [hh]), ite_eq_right hh,
      show (low32 a).umod (low32 b) = (low32 a) % (low32 b) from rfl,
      umod32, low32_unsigned, low32_unsigned]
    exact (ofInt_swrap32 _).symm

/-! ## Upper-immediate and jalr bridges -/

/-- `Z.land z (-2)` commutes with the 64-bit wrap. -/
theorem Z_land_m2_wrap (z : Int) : zland_m2 (bv_wrap 64 z) = bv_wrap 64 (zland_m2 z) := by
  unfold zland_m2 bv_wrap
  have h2 : ((2 : Int) ^ 64) % 2 = 0 := by decide
  omega

/-- `lui`. -/
theorem b_lui (imm : BitVec 20) :
    sext 64 (imm ++ (0#12)) = v_lui (zshiftl imm.toInt 12) := by
  rw [sext_eq_ofInt _ (by decide : 32 ≤ 64)]
  unfold v_lui zshiftl
  rw [BitVec.toInt_append]
  simp only [show (20 == 0) = false from by decide, Bool.false_eq_true, ite_false,
    show (0#12 : BitVec 12).toNat = 0 from by decide,
    BitVec.toNat_ofInt, BitVec.toInt_ofInt,
    Int.zero_emod, Int.toNat_zero]
  congr 1
  omega

/-- `auipc`. -/
theorem b_auipc (p : word) (imm : BitVec 20) :
    p + sext 64 (imm ++ (0#12)) = v_auipc p (zshiftl imm.toInt 12) := by
  rw [b_lui]
  unfold v_lui v_auipc zshiftl
  bv_omega

/-- Clearing bit 0 of a value below `2^n` is subtracting its parity. -/
theorem and_two_pow_sub_two (n x : Nat) (hn : 1 ≤ n) (hx : x < 2 ^ n) :
    x &&& (2 ^ n - 2) = x - x % 2 := by
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.pow_succ]; omega
  have hM : 2 ^ n - 2 = 2 * (2 ^ (n - 1) - 1) := by omega
  rw [hM]
  have hdiv : 2 * (2 ^ (n - 1) - 1) / 2 = 2 ^ (n - 1) - 1 := by omega
  have h1 : (x &&& (2 * (2 ^ (n - 1) - 1))) / 2 = x / 2 &&& (2 ^ (n - 1) - 1) := by
    rw [Nat.and_div_two, hdiv]
  have heven : (x &&& (2 * (2 ^ (n - 1) - 1))) % 2 = 0 := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.and_mod_two_pow]
    have h2 : (2 * (2 ^ (n - 1) - 1)) % 2 = 0 := by omega
    rw [h2, Nat.and_zero]
  have hk : 2 * ((x &&& (2 * (2 ^ (n - 1) - 1))) / 2) = x &&& (2 * (2 ^ (n - 1) - 1)) :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)
  rw [← hk, h1]
  have h3 : x / 2 &&& (2 ^ (n - 1) - 1) = x / 2 :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  rw [h3]
  omega

/-- `jalr`'s target: `(rs1 + imm)` with bit 0 cleared. -/
theorem b_jalr (a : word) (imm : BitVec 12) :
    (a + sext 64 imm) &&& ~~~(1 : word) = jalr_tgt a imm.toInt := by
  rw [b_addsext a imm (by decide : 12 ≤ 64)]
  unfold v_addi jalr_tgt jalr_tgtZ zland_m2
  apply BitVec.eq_of_toNat_eq
  have hK : (BitVec.ofInt 64 ((a.toNat : Int) + imm.toInt)).toNat
      = (((a.toNat : Int) + imm.toInt) % ((2 ^ 64 : Nat) : Int)).toNat := BitVec.toNat_ofInt _
  rw [BitVec.toNat_and, hK, BitVec.toNat_not, show ((1 : word)).toNat = 1 from by decide,
    BitVec.toNat_ofInt, show (2 ^ 64 - 1 - 1 : Nat) = 2 ^ 64 - 2 from by omega]
  rw [and_two_pow_sub_two 64 _ (by decide) (emod64_toNat_lt _)]
  omega


end WithFP1g

/-! -/
open Lean Parser Tactic in
macro "step_pipeline" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, interp_eff_accesses, mkAccessReport,
      rset, rget, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet, bvmap_set,
      getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, w0, Bool.false_eq_true, reduceIte,
      ite_true, ite_false])

section WithFP2

variable [fx : FPState]

theorem step_opimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg)
    (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm op rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- A probe for the pipeline: OpImm, generic in the aluop. (see [step_opimm_gen] above.) -/

/- Shift-immediate, generic in the aluop. -/
theorem step_shiftimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh))) (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/- Register-register, generic in the aluop. -/
theorem step_op_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/- OpImm32 (addiw), generic in nothing: the aluop is fixed to ADD by the decoder. -/
theorem step_opimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm))))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/- Shift-immediate-32, generic in the aluop. -/
theorem step_shiftimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm32 op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/- Register-register-32, generic in the aluop. -/
theorem step_op32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : AluOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd
          (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/- M-extension, generic in the m-op. -/
theorem step_mul_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : MulOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/- M-extension at 32 bits, generic in the m-op. -/
theorem step_mul32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : MulOp) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd
          (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi pc 4) mem rom) := by
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/-- Generic branch step lemmas: taken and fall-through. -/
theorem step_branch_tk_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : BranchCond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  simp only [getr, bv_eqb0_is_x0] at Hc
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, hb, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

/-- The fall-through side. -/
theorem step_branch_ft_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (c : BranchCond) (rs1 rs2 : reg)
    (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  simp only [getr, bv_eqb0_is_x0] at Hc
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

/-! ## Per-instruction step lemmas -/

/-- `addi`. -/
theorem step_addi (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .ADD rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_addi (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .ADD rd rs imm Hfetch Hecall Hdecode, alu_addi (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- `andi`. -/
theorem step_andi (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .AND rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_andi (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .AND rd rs imm Hfetch Hecall Hdecode, alu_andi (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- `ori`. -/
theorem step_ori (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .OR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_ori (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .OR rd rs imm Hfetch Hecall Hdecode, alu_ori (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- `xori`. -/
theorem step_xori (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .XOR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_xori (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .XOR rd rs imm Hfetch Hecall Hdecode, alu_xori (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- `sltiu`. -/
theorem step_sltiu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .SLTU rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sltiu (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .SLTU rd rs imm Hfetch Hecall Hdecode, alu_sltiu (getr regs rs) imm (by decide : 12 ≤ 64)]

/-- `slti`. -/
theorem step_slti (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm .SLT rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_slti (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w .SLT rd rs imm Hfetch Hecall Hdecode, alu_slti (getr regs rs) imm]

/-- `slli`. -/
theorem step_slli (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm .SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_slli (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .SLL rd rs sh Hfetch Hecall Hdecode,
    alu_slli (getr regs rs) sh]

/-- `srli`. -/
theorem step_srli (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm .SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_srli (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .SRL rd rs sh Hfetch Hecall Hdecode,
    alu_srli (getr regs rs) sh]

/-- `srai`. -/
theorem step_srai (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm .SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_srai (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w .SRA rd rs sh Hfetch Hecall Hdecode,
    alu_srai (getr regs rs) sh]

/-- `add`. -/
theorem step_add (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_add (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .ADD rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_add (getr regs rs1) (getr regs rs2)]

/-- `sub`. -/
theorem step_sub (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SUB rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_sub (getr regs rs1) (getr regs rs2)]

/-- `slt`. -/
theorem step_slt (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SLT rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SLT rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_slt (getr regs rs1) (getr regs rs2)]

/-- `sltu`. -/
theorem step_sltu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SLTU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SLTU rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_sltu (getr regs rs1) (getr regs rs2)]

/-- `and`. -/
theorem step_and (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .AND rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_and (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .AND rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_and (getr regs rs1) (getr regs rs2)]

/-- `or`. -/
theorem step_or (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .OR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_or (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .OR rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_or (getr regs rs1) (getr regs rs2)]

/-- `xor`. -/
theorem step_xor (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .XOR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .XOR rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_xor (getr regs rs1) (getr regs rs2)]

/-- `sll`. -/
theorem step_sll (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SLL rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_sll (getr regs rs1) (getr regs rs2)]

/-- `srl`. -/
theorem step_srl (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SRL rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_srl (getr regs rs1) (getr regs rs2)]

/-- `sra`. -/
theorem step_sra (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op .SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w .SRA rd rs1 rs2 Hfetch Hecall Hdecode,
    alu_sra (getr regs rs1) (getr regs rs2)]

/-- `addiw`. -/
theorem step_addiw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_addiw (getr regs rs) imm.toInt)) (v_addi pc 4) mem rom) := by
  rw [step_opimm32_gen segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode,
    w_addiw (getr regs rs) imm]

/-- `slliw`. -/
theorem step_slliw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm32 .SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_slliw (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .SLL rd rs sh Hfetch Hecall Hdecode,
    w_slliw (getr regs rs) sh]

/-- `srliw`. -/
theorem step_srliw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm32 .SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_srliw (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .SRL rd rs sh Hfetch Hecall Hdecode,
    w_srliw (getr regs rs) sh]

/-- `sraiw`. -/
theorem step_sraiw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm32 .SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sraiw (getr regs rs) sh.toNat)) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w .SRA rd rs sh Hfetch Hecall Hdecode,
    w_sraiw (getr regs rs) sh]

/-- `addw`. -/
theorem step_addw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 .ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .ADD rd rs1 rs2 Hfetch Hecall Hdecode,
    w_addw (getr regs rs1) (getr regs rs2)]

/-- `subw`. -/
theorem step_subw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 .SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .SUB rd rs1 rs2 Hfetch Hecall Hdecode,
    w_subw (getr regs rs1) (getr regs rs2)]

/-- `sllw`. -/
theorem step_sllw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 .SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .SLL rd rs1 rs2 Hfetch Hecall Hdecode,
    w_sllw (getr regs rs1) (getr regs rs2)]

/-- `srlw`. -/
theorem step_srlw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 .SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .SRL rd rs1 rs2 Hfetch Hecall Hdecode,
    w_srlw (getr regs rs1) (getr regs rs2)]

/-- `sraw`. -/
theorem step_sraw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 .SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w .SRA rd rs1 rs2 Hfetch Hecall Hdecode,
    w_sraw (getr regs rs1) (getr regs rs2)]

/-- `mul`. -/
theorem step_mul (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .MUL rd rs1 rs2 Hfetch Hecall Hdecode,
    m_mul (getr regs rs1) (getr regs rs2)]

/-- `mulh`. -/
theorem step_mulh (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .MULH rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .MULH rd rs1 rs2 Hfetch Hecall Hdecode,
    m_mulh (getr regs rs1) (getr regs rs2)]

/-- `mulhsu`. -/
theorem step_mulhsu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .MULHSU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .MULHSU rd rs1 rs2 Hfetch Hecall Hdecode,
    m_mulhsu (getr regs rs1) (getr regs rs2)]

/-- `mulhu`. -/
theorem step_mulhu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .MULHU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .MULHU rd rs1 rs2 Hfetch Hecall Hdecode,
    m_mulhu (getr regs rs1) (getr regs rs2)]

/-- `div`. -/
theorem step_div (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_div (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .DIV rd rs1 rs2 Hfetch Hecall Hdecode,
    m_div (getr regs rs1) (getr regs rs2)]

/-- `rem`. -/
theorem step_rem (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul .REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w .REM rd rs1 rs2 Hfetch Hecall Hdecode,
    m_rem (getr regs rs1) (getr regs rs2)]

/-- `mulw`. -/
theorem step_mulw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 .MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .MUL rd rs1 rs2 Hfetch Hecall Hdecode,
    w_mulw (getr regs rs1) (getr regs rs2)]

/-- `divw`. -/
theorem step_divw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 .DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .DIV rd rs1 rs2 Hfetch Hecall Hdecode,
    w_divw (getr regs rs1) (getr regs rs2)]

/-- `divuw`. -/
theorem step_divuw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 .DIVU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .DIVU rd rs1 rs2 Hfetch Hecall Hdecode,
    w_divuw (getr regs rs1) (getr regs rs2)]

/-- `remw`. -/
theorem step_remw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 .REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .REM rd rs1 rs2 Hfetch Hecall Hdecode,
    w_remw (getr regs rs1) (getr regs rs2)]

/-- `remuw`. -/
theorem step_remuw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 .REMU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w .REMU rd rs1 rs2 Hfetch Hecall Hdecode,
    w_remuw (getr regs rs1) (getr regs rs2)]

/-- Branches (no alignment side conditions: the ISA model has no check). -/
theorem step_beq_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .EQ rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .EQ rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_beq_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .EQ rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .EQ rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bne_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .NE rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .NE rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bne_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .NE rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .NE rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_blt_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .LT rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .LT rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_blt_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .LT rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .LT rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bge_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .GE rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .GE rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bge_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .GE rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .GE rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bltu_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .LTU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .LTU rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bltu_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .LTU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .LTU rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bgeu_tk (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w .GEU rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

theorem step_bgeu_ft (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch .GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w .GEU rs1 rs2 imm Hfetch Hecall Hdecode
  simpa [c_eq, c_lts, c_ltu, branch_taken] using Hc

/-! ## Upper immediates, jumps, ecall -/

/-- [imm] is the raw 20-bit U-immediate; the value shape takes the shifted
    signed immediate (the "real" constant). -/
theorem step_lui (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.lui rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lui (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) := by
  have hb : sext 64 (imm ++ (0#12)) = v_lui (zshiftl imm.toInt 12) := b_lui imm
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

/-- `auipc`. -/
theorem step_auipc (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.auipc rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_auipc pc (zshiftl imm.toInt 12))) (v_addi pc 4) mem rom) := by
  have hb : pc + sext 64 (imm ++ (0#12)) = v_auipc pc (zshiftl imm.toInt 12) :=
    b_auipc pc imm
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

/-- `jal x0`: a plain jump, no link register written. -/
theorem step_jal_x0 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (imm : BitVec 21)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal 0 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (btgt pc imm.toInt) mem rom) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [is_x0_0, ite_true, Bool.false_eq_true, reduceIte, hb]

/-- General Jalr: rd := pc + 4 (unless rd = x0), jump to the masked target.
    No alignment side condition (the ISA model has no check). -/
theorem step_jalr_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (jalr_tgt (getr regs rs1) imm.toInt) mem rom) := by
  have hb : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide : 12 ≤ 64)
  have hj : (getr regs rs1 + sext 64 imm) &&& ~~~(1 : word)
      = jalr_tgt (getr regs rs1) imm.toInt := b_jalr _ imm
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, bv_eqb0_is_x0, w1, reg_get, w0] at hb hj ⊢
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, w0, w1, Bool.false_eq_true,
    reg_get] at hb hj ⊢
  all_goals rw [hj]
  all_goals simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, Nat.zero_add]

/-- `ecall`: record a7 as the pending syscall number and stop the instruction
    step (pc does NOT advance). -/
theorem step_ecall (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk { (mkst regs pc mem rom) with ms_svc_pending := some (getr regs 17) } := by
  simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, Hfetch,
    decode_exec_accesses, Hecall, drop_access_report, mkAccessReport, ms_reg, getr,
    bv_eqb0_is_x0, is_x0_0, ite_true, ite_false, w0]

/-! ## Value simplification lemmas -/

theorem two64_pos : (0 : Int) < 2 ^ 64 := two64_pos_int

/-- The unsigned reading of [v_addi] when the sum does not wrap. -/
theorem v_addi_nneg (x : word) (imm : Int) (Hi : 0 ≤ imm)
    (Hs : (x.toNat : Int) + imm < ((2 ^ 64 : Nat) : Int)) :
    ((v_addi x imm).toNat : Int) = (x.toNat : Int) + imm := by
  unfold v_addi
  rw [BitVec.toNat_ofInt]
  have h : ((x.toNat : Int) + imm) % ((2 ^ 64 : Nat) : Int) = (x.toNat : Int) + imm :=
    Int.emod_eq_of_lt (by omega) Hs
  rw [h]
  exact Int.toNat_of_nonneg (by omega)

/-- Adding zero is the identity. -/
theorem v_addi_0 (x : word) : v_addi x 0 = x := by
  unfold v_addi
  rw [Int.add_zero, BitVec.ofInt_natCast]
  simp

/-- The unsigned reading of [v_add] when the sum does not wrap. -/
theorem v_add_small (x y : word) (H : (x.toNat : Int) + (y.toNat : Int) < ((2 ^ 64 : Nat) : Int)) :
    ((v_add x y).toNat : Int) = (x.toNat : Int) + (y.toNat : Int) := by
  unfold v_add
  rw [BitVec.toNat_ofInt]
  have h : ((x.toNat : Int) + (y.toNat : Int)) % ((2 ^ 64 : Nat) : Int)
      = (x.toNat : Int) + (y.toNat : Int) := Int.emod_eq_of_lt (by omega) H
  rw [h]
  exact Int.toNat_of_nonneg (by omega)

/-- The unsigned reading of [v_sub] when the difference does not wrap. -/
theorem v_sub_small (x y : word) (H : (y.toNat : Int) ≤ (x.toNat : Int)) :
    ((v_sub x y).toNat : Int) = (x.toNat : Int) - (y.toNat : Int) := by
  unfold v_sub
  rw [BitVec.toNat_ofInt]
  have h : ((x.toNat : Int) - (y.toNat : Int)) % ((2 ^ 64 : Nat) : Int)
      = (x.toNat : Int) - (y.toNat : Int) :=
    Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)
  rw [h]
  exact Int.toNat_of_nonneg (by omega)

/-- The `slli by 3` reading. -/
theorem v_slli_3 (x : word) (H8 : (8 * (x.toNat : Int)) < ((2 ^ 64 : Nat) : Int)) :
    ((v_slli x 3).toNat : Int) = 8 * (x.toNat : Int) := by
  unfold v_slli zshiftl
  rw [show ((3 : Int)).toNat = 3 from by decide, BitVec.toNat_ofInt,
    show ((2 ^ 3 : Nat) : Int) = 8 from by decide,
    show (x.toNat : Int) * 8 = 8 * (x.toNat : Int) from by rw [Int.mul_comm]]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  exact Int.toNat_of_nonneg (by omega)

theorem v_addi_0_1 : v_addi (BitVec.ofInt 64 0) 1 = BitVec.ofInt 64 1 := by decide
theorem v_addi_0_64 : v_addi (BitVec.ofInt 64 0) 64 = BitVec.ofInt 64 64 := by decide

/-- [v_addi] by one on a `nat_to_word`. -/
theorem v_addi_Sj (j : Nat) (H : ((j : Int) + 1) < ((2 ^ 64 : Nat) : Int)) :
    v_addi (nat_to_word j) 1 = nat_to_word (j + 1) := by
  unfold v_addi nat_to_word
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [show ((j : Int) + 1) = ((j + 1 : Nat) : Int) from by omega, BitVec.ofInt_natCast]

/-! ## Register-file helpers -/

/-- Reading the register just written. -/
theorem getr_same (regs : BvMap word) (r : reg) (v : word) (H : r ≠ 0) :
    getr (regupd regs r v) r = v := by
  unfold getr regupd reg_get
  rw [bv_eqb_neq r 0 H, ite_eq_right (by simp), bvmapGet_set_same]
  rfl

/-- Reading an untouched register. -/
theorem getr_other (regs : BvMap word) (r : reg) (v : word) (r' : reg) (H : r' ≠ r) :
    getr (regupd regs r v) r' = getr regs r' := by
  unfold getr regupd
  by_cases h : bv_eqb r' 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    unfold reg_get
    rw [bvmapGet_set_other r r' v regs (fun hh => H hh.symm)]

/-- [getr] on a nonzero register is [reg_get]. -/
theorem getr_nz (regs : BvMap word) (r : reg) (H : r ≠ 0) : getr regs r = reg_get regs r := by
  unfold getr
  rw [bv_eqb_neq r 0 H, ite_eq_right (by simp)]

/-- An unrelated register is untouched by [regupd]. -/
theorem regupd_other (regs : BvMap word) (r : reg) (v : word) (r' : reg) (H : r' ≠ r) :
    reg_get (regupd regs r v) r' = reg_get regs r' := by
  unfold regupd reg_get
  rw [bvmapGet_set_other r r' v regs (fun hh => H hh.symm)]

/-- The written register reads back. -/
theorem regupd_same (regs : BvMap word) (r : reg) (v : word) :
    reg_get (regupd regs r v) r = v := by
  unfold regupd reg_get
  rw [bvmapGet_set_same]
  rfl

/-! ## Comparison simplification lemmas -/

/-- A word below the sign boundary reads as its unsigned value. -/
theorem bv_signed_small (x : word) (Hx : x.toNat < 2 ^ 63) : x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_msb_cond]
  have h : x.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  simp [h]

/-- A word at or above the sign boundary reads as its unsigned value minus
    `2^64`. -/
theorem bv_signed_hi (x : word) (Hx : 2 ^ 63 ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_msb_cond]
  have h : x.msb = true := by
    cases hh : x.msb with
    | false => rw [BitVec.msb_eq_false_iff_two_mul_lt] at hh; omega
    | true => rfl
  simp [h]

/-- Below the sign boundary, signed and unsigned `<` agree. -/
theorem c_lts_small (x y : word) (Hx : x.toNat < 2 ^ 63) (Hy : y.toNat < 2 ^ 63) :
    c_lts x y = bv_ltu x y := by
  unfold c_lts bv_lts bv_ltu
  simp only [bv_signed_small x Hx, bv_signed_small y Hy]
  rw [decide_eq_decide]
  exact Int.ofNat_lt

/-- A negative word is signed-less than zero. -/
theorem c_lts_neg_0 (x : word) (Hx : 2 ^ 63 ≤ x.toNat) :
    c_lts x (0 : word) = true := by
  unfold c_lts bv_lts
  simp only [bv_signed_hi x Hx, show ((0 : word)).toInt = 0 from by decide]
  exact decide_eq_true (by omega)

/-- A non-negative word is not signed-less than zero. -/
theorem c_lts_pos_0 (x : word) (Hx : x.toNat < 2 ^ 63) :
    c_lts x (0 : word) = false := by
  unfold c_lts bv_lts
  simp only [bv_signed_small x Hx, show ((0 : word)).toInt = 0 from by decide]
  exact decide_eq_false (by omega)

/-- Zero is signed-less than a nonempty non-negative word: the mirror of
    [c_lts_pos_0], and the form every retry loop meets after a short
    write/read. -/
theorem c_lts_0_pos (n : word) (H1 : 1 ≤ (n.toNat : Int)) (H2 : n.toNat < 2 ^ 63) :
    c_lts (0 : word) n = true := by
  rw [c_lts_small _ _ (by decide) H2]
  unfold bv_ltu
  rw [show ((0 : word)).toNat = 0 from by decide]
  exact decide_eq_true (by omega)

/-- The `errno_ret` bounds: a Linux error return is negative and above
    `2^63`. -/
theorem errno_ret_range (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    2 ^ 63 ≤ (errno_ret e).toNat ∧ (errno_ret e).toNat < 2 ^ 64 := by
  unfold errno_ret
  rw [BitVec.toNat_ofInt]
  have hem : (-e) % ((2 ^ 64 : Nat) : Int) = ((2 ^ 64 : Nat) : Int) - e := by omega
  rw [hem]
  have h2 : (((2 ^ 64 : Nat) : Int) - e).toNat = (2 ^ 64 - e.toNat) := by omega
  rw [h2]
  constructor <;> omega

/-- The signed reading of an `errno_ret`. -/
theorem errno_ret_signed (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    (errno_ret e).toInt = -e := by
  have hlo := (errno_ret_range e H1 H2).1
  rw [bv_signed_hi _ hlo]
  have h2 : ((errno_ret e).toNat : Int) = ((2 ^ 64 : Nat) : Int) - e := by
    unfold errno_ret
    rw [BitVec.toNat_ofInt]
    have hem : (-e) % ((2 ^ 64 : Nat) : Int) = ((2 ^ 64 : Nat) : Int) - e := by omega
    rw [hem]
    exact Int.toNat_of_nonneg (by omega)
  rw [h2]
  omega

/-- An error return is signed-less than zero. -/
theorem c_lts_errno (e : Int) (H1 : 1 ≤ e) (H2 : e ≤ 4095) :
    c_lts (errno_ret e) (0 : word) = true :=
  c_lts_neg_0 _ (errno_ret_range e H1 H2).1

/-! ## c_eq / c_ltu simplification lemmas -/

/-- [c_eq] is [bv_eqb] definitionally; bound hypotheses are typed away. -/
theorem c_eq_small (x y : word) : c_eq x y = bv_eqb x y := rfl

/-- [c_ltu] is [bv_ltu] definitionally. -/
theorem c_ltu_small (x y : word) : c_ltu x y = bv_ltu x y := rfl

/-- A nonempty word is not equal to zero. -/
theorem c_eq_0_false (x : word) (Hnz : x.toNat ≠ 0) : c_eq x (0 : word) = false := by
  have hx : x ≠ 0 := fun h => Hnz (by rw [h]; rfl)
  unfold c_eq bv_eqb
  cases h : (x == (0 : word)) with
  | false => rfl
  | true => rw [beq_iff_eq] at h; exact absurd h hx

/-- The positive counterpart of [c_eq_0_false]: the put loop's `beqz` on
    full delivery, from an unsigned-level zero fact. -/
theorem c_eq_0_of_u (x : word) (Hx : x.toNat = 0) : c_eq x (0 : word) = true := by
  have hx : x = 0 := BitVec.eq_of_toNat_eq (by simpa using Hx)
  unfold c_eq bv_eqb
  subst hx
  rfl

theorem c_eq_0_true : c_eq (0 : word) (0 : word) = true := by decide

/-- Distinct unsigned readings mean the words differ. -/
theorem c_eq_neq (x y : word) (Hne : x.toNat ≠ y.toNat) : c_eq x y = false := by
  have h : x ≠ y := fun hh => Hne (by rw [hh])
  unfold c_eq bv_eqb
  cases hh : (x == y) with
  | false => rfl
  | true => rw [beq_iff_eq] at hh; exact absurd hh h

/-- Equality is reflexive. -/
theorem c_eq_refl (x : word) : c_eq x x = true := bv_eqb_refl x

/-! ## LE byte decoding -/

/-- A single byte decodes to its unsigned value. -/
theorem bytes_le_single (b : byte) : bytes_le_to_Z [b] = (b.toNat : Int) := by
  simp [bytes_le_to_Z, bytes_le_to_Nat]

/-- The wrap at width 8 is a mod. -/
theorem bv_wrap8_mod (z : Int) : bv_wrap 8 z = z % 2 ^ 8 := rfl

/-- [word_le8] is [word_to_le_bytes 8]; the two are in fact definitionally
    equal. -/
theorem n_to_le_8_spec (v : word) : word_le8 v = word_to_le_bytes 8 v := rfl

/-! ## Stack memory reads -/

/-- Splitting a list at a position below its length. -/
theorem nth_error_skipn_cons {A : Type} (bs : List A) (d : Nat) (Hd : d < bs.length) :
    ∃ b, bs[d]? = some b ∧ bs.drop d = b :: bs.drop (d + 1) := by
  induction bs generalizing d with
  | nil => simp at Hd
  | cons x rest ih =>
    cases d with
    | zero => exact ⟨x, rfl, rfl⟩
    | succ d' =>
      obtain ⟨b, h1, h2⟩ := ih d' (by simpa using Hd)
      exact ⟨b, by simpa using h1, by simpa using h2⟩

/-- Adding one below the wrap bound. -/
theorem u_add1 (a : word) (Ha : (a.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int)) :
    ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := by
  rw [BitVec.toNat_add]
  have hone : ((1 : word)).toNat = 1 := by decide
  rw [hone, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The address walk is a wrapping `BitVec` add, so the read lemmas need the
    (always trivially satisfied in practice) no-overflow bound
    `sp + length bytes < 2^64`. -/
theorem rdn_stack (segs : List Segment) (sp : word) (bytes : List byte) (k : Nat) :
    ∀ addr : word,
      (sp.toNat : Int) ≤ (addr.toNat : Int) →
      (addr.toNat - sp.toNat) + k ≤ bytes.length →
      (sp.toNat : Int) + (bytes.length : Int) < ((2 ^ 64 : Nat) : Int) →
      rdn segs (stack_to_mem sp bytes) addr k =
        some (List.take k (List.drop (addr.toNat - sp.toNat) bytes)) := by
  induction k with
  | zero => intro addr _ _ _; rfl
  | succ k ih =>
    intro addr Hsp Hlen Hnw
    have hone : ((1 : word)).toNat = 1 := by decide
    have hbound : addr.toNat + 1 < 2 ^ 64 := by omega
    have hboundI : (addr.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int) := by omega
    have hplus : ((addr + 1).toNat : Int) = (addr.toNat : Int) + 1 := u_add1 addr hboundI
    have hplusn : (addr + 1).toNat = addr.toNat + 1 := by omega
    have hspn : sp.toNat ≤ addr.toNat := by omega
    have hlen0 : addr.toNat - sp.toNat + (k + 1) ≤ bytes.length := Hlen
    have hsubn : (addr + 1).toNat - sp.toNat = (addr.toNat - sp.toNat) + 1 := by
      rw [hplusn]
      omega
    have hd : addr.toNat - sp.toNat < bytes.length := by omega
    obtain ⟨b, hb, hdrop⟩ := nth_error_skipn_cons bytes (addr.toNat - sp.toNat) hd
    have hoff : ((addr.toNat : Int) - (sp.toNat : Int)) < (bytes.length : Int) := by omega
    have htoNat : (((addr.toNat : Int) - (sp.toNat : Int))).toNat = addr.toNat - sp.toNat := by
      omega
    have hread : (match stack_to_mem sp bytes addr with
                 | some b => some b
                 | none => seg_rom segs addr) = some b := by
      simp only [stack_to_mem, ite_eq_left hspn, htoNat, ite_eq_left hoff, hb]
    simp only [rdn, hread]
    rw [ih (addr + 1) (by omega) (by rw [hsubn]; omega) Hnw, hsubn, hdrop]
    rfl

/-- Two functions agreeing on a run of `k` addresses give the same read. -/
theorem rdn_ext (segs : List Segment) (k : Nat) :
    ∀ (m1 m2 : word → Option byte) (a : word),
      (a.toNat : Int) + (k : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      (∀ x : word, (a.toNat : Int) ≤ (x.toNat : Int) ∧
        (x.toNat : Int) < (a.toNat : Int) + k → m1 x = m2 x) →
      rdn segs m1 a k = rdn segs m2 a k := by
  induction k with
  | zero => intro m1 m2 a _ _; rfl
  | succ k ih =>
    intro m1 m2 a Hnw Hext
    have ha : m1 a = m2 a := Hext a ⟨by omega, by omega⟩
    rw [rdn, rdn, ha]
    cases k with
    | zero =>
      have hz : ∀ m : word → Option byte, rdn segs m (a + 1) 0 = some [] := fun m => rfl
      cases h : m2 a with
      | none => simp only [h, hz]
      | some b => simp only [h, hz]
    | succ k' =>
      have hone : ((1 : word)).toNat = 1 := by decide
      have h1 : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := u_add1 a (by omega)
      have hbnd : ((a + 1).toNat : Int) + ((k' + 1 : Nat) : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := by omega
      have hext' : ∀ x : word, ((a + 1).toNat : Int) ≤ (x.toNat : Int) ∧
          (x.toNat : Int) < ((a + 1).toNat : Int) + ((k' + 1 : Nat) : Int) →
          m1 x = m2 x := by
        intro x Hx
        exact Hext x ⟨by omega, by omega⟩
      cases h : m2 a with
      | none => simp only [h]; rw [ih m1 m2 (a + 1) hbnd hext']
      | some b =>
        simp only [h]
        rw [ih m1 m2 (a + 1) hbnd hext']

/-! ## THE WRAPPER BRIDGE

    This repo's [init_machine_state] sets [ms_mem] to a wrapper that, for stack
    addresses below [sp] (and above [sp - stack_max_size]), returns [Some 0],
    else defers to the raw [stack_to_mem].  Every read the binaries perform is
    at [addr >= sp], where the zero-fill guard is false, so the wrapper agrees
    with [stack_to_mem]. -/

/-- The zero-fill wrapper `init_machine_state` installs over the entry stack. -/
def wrap_mem (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid : word) (hw : word) (rnd : EntryDraw) : word → Option byte :=
  fun addr =>
    match stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) addr with
    | some b => some b
    | none =>
      if decide ((sp.toNat : Int) - stack_max_size ≤ (addr.toNat : Int)) &&
         decide ((addr.toNat : Int) < (sp.toNat : Int))
      then some (BitVec.ofInt 8 0)
      else none

/-- At and above [sp], the wrapper equals the raw [stack_to_mem]: the
    zero-fill branch is gated by `addr < sp`, which is false. -/
theorem wrap_above_sp (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (x : word) (uid hw : word) (rnd : EntryDraw)
    (Hx : (sp.toNat : Int) ≤ (x.toNat : Int)) :
    wrap_mem ph sp argv envp uid hw rnd x
      = stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x := by
  unfold wrap_mem
  split
  · rename_i b heq; rw [heq]
  · rename_i heq
    rw [heq, ite_eq_right]
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega

/-- Reads above [sp] see the same bytes through the wrapper and through the
    raw stack image. -/
theorem rdn_wrap_stack_above (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (a : word) (n : Nat) (uid hw : word)
    (rnd : EntryDraw)
    (Hsp : (sp.toNat : Int) ≤ (a.toNat : Int))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wrap_mem ph sp argv envp uid hw rnd) a n
      = rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) a n := by
  apply rdn_ext
  · exact Hnw
  · intro x Hx
    exact wrap_above_sp ph sp argv envp x uid hw rnd (by omega)

/-- The initial machine state, in [mkst] shape: an a0 of zero, sp in x2, the
    entry stack behind [wrap_mem] and the image behind [seg_rom]. -/
theorem init_mkst (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    init_machine_state segs pc ph sp rnd argv envp uid hw =
      @mkst fx0
        (regupd (regupd (bvmap_empty : BvMap word) 10 (BitVec.ofInt 64 0)) 2 sp)
        (BitVec.ofInt 64 (Int.ofNat pc))
        (wrap_mem ph sp argv envp uid hw rnd) (seg_rom segs) := rfl

/-- Sanity check for [init_mkst]: the entry state's stack pointer reads back
    through the register file (the register keys agree with [reg_get]). -/
theorem init_mkst_sp (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    ms_sp (init_machine_state segs pc ph sp rnd argv envp uid hw) = sp := by
  rw [init_mkst]
  simp only [ms_sp, mkst]
  exact regupd_same (regupd (bvmap_empty : BvMap word) 10 (BitVec.ofInt 64 0)) 2 sp

/-! ## Stack layout decomposition -/

theorem length_n_to_le_8 (v : word) : (word_le8 v).length = 8 := by
  simp [word_le8]

theorem length_flat_map_le8 (l : List word) : (l.flatMap word_le8).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    rw [List.flatMap_cons, List.length_append, length_n_to_le_8, ih]
    simp only [List.length_cons]
    omega

/-- The nat-valued companion of `Run.total_arg_bytes`: the spec states its
    bound in `Int`, but the stack-image length arithmetic below lives in
    `Nat` with `List.length`, so the splitting lemmas use this form and
    [total_arg_bytes_Z] bridges to the spec's bound. -/
def total_arg_bytes_nat (args : List (List byte)) : Nat :=
  args.foldr (fun a acc => a.length + 1 + acc) 0

/-- [total_arg_bytes] is the `Int` image of [total_arg_bytes_nat]. -/
theorem total_arg_bytes_Z (l : List (List byte)) :
    total_arg_bytes l = (total_arg_bytes_nat l : Int) := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [total_arg_bytes, total_arg_bytes_nat, List.foldr_cons] at *
    rw [ih]
    push_cast
    omega

theorem length_flatten_strings (l : List (List byte)) :
    (flatten_strings l).length = total_arg_bytes_nat l := by
  induction l with
  | nil => rfl
  | cons x r ih =>
    simp only [flatten_strings, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_singleton, List.length_nil, total_arg_bytes_nat, List.foldr_cons] at *
    omega

theorem len_word_nat {A : Type} (l : List A) : len_word l = nat_to_word l.length := rfl

theorem word1_nat : (1 : word) = nat_to_word 1 := rfl

theorem word_add_0 (a : word) : a + nat_to_word 0 = a := by
  simp [nat_to_word]

theorem nat_to_word_merge (m k : Nat) : nat_to_word m + nat_to_word k = nat_to_word (m + k) := by
  unfold nat_to_word
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem nat_to_word_add_merge (a : word) (m k : Nat) :
    a + nat_to_word m + nat_to_word k = a + nat_to_word (m + k) := by
  rw [BitVec.add_assoc, nat_to_word_merge]

theorem string_addrs_fst_structure (strs : List (List byte)) (base : word) :
    (string_addrs base strs).1 =
      match strs with
      | [] => []
      | s :: rest => base :: (string_addrs (base + len_word s + 1) rest).1 := by
  cases strs with
  | nil => rfl
  | cons s rest =>
    simp only [string_addrs]

theorem string_addrs_pair (strs : List (List byte)) (base : word) :
    string_addrs base strs
      = ((string_addrs base strs).1, base + nat_to_word (total_arg_bytes_nat strs)) := by
  induction strs generalizing base with
  | nil => simp [string_addrs, nat_to_word, total_arg_bytes_nat]
  | cons s rest ih =>
    simp only [string_addrs, total_arg_bytes_nat, List.foldr_cons]
    rw [ih (base + len_word s + 1)]
    simp only []
    congr 1
    rw [len_word_nat, word1_nat, nat_to_word_add_merge, nat_to_word_add_merge]
    congr 2
    simp only [total_arg_bytes_nat]
    omega

theorem length_string_addrs_fst (strs : List (List byte)) (base : word) :
    (string_addrs base strs).1.length = strs.length := by
  induction strs generalizing base with
  | nil => rfl
  | cons s rest ih =>
    rw [string_addrs_fst_structure]
    simp only [List.length_cons]
    rw [ih]

/-! ## Stack read corollaries -/

/-- The first platform word (argc) sits at [sp]. -/
theorem bsb_argc_prefix (ph : PhdrInfo) (sp : word) (argv envp : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    ∃ tl, build_stack_bytes ph sp argv envp uid hw rnd = word_le8 (len_word argv) ++ tl := by
  unfold build_stack_bytes
  exact ⟨_, rfl⟩

/-- A read at a known offset into a laid-out block. -/
theorem read_at_offset (segs : List Segment) (sp : word) (bytes pre mid post : List byte)
    (k : Nat) (Hb : bytes = pre ++ mid ++ post) (Hk : mid.length = k)
    (Hnw : (sp.toNat : Int) + (bytes.length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word pre.length) k = some mid := by
  have hpre_le : pre.length ≤ bytes.length := by rw [Hb]; simp
  have hu : ((sp + nat_to_word pre.length).toNat : Int) = (sp.toNat : Int) + (pre.length : Int) := by
    unfold nat_to_word
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : sp.toNat + pre.length % 2 ^ 64 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : pre.length < 2 ^ 64)]
    push_cast
    omega
  have hsp : (sp.toNat : Int) ≤ ((sp + nat_to_word pre.length).toNat : Int) := by omega
  have hpreNat : (sp + nat_to_word pre.length).toNat = sp.toNat + pre.length := by omega
  have hpre : (sp + nat_to_word pre.length).toNat - sp.toNat = pre.length := by
    rw [hpreNat]
    omega
  have hlen : ((sp + nat_to_word pre.length).toNat - sp.toNat) + k ≤ bytes.length := by
    rw [hpre, ← Hk, Hb]
    simp
  rw [rdn_stack segs sp bytes k _ hsp hlen Hnw, hpre]
  have hdrop : List.drop pre.length bytes = mid ++ post := by
    rw [Hb, List.append_assoc, List.drop_append, List.drop_length, List.nil_append,
      Nat.sub_self]
    rfl
  rw [hdrop, ← Hk, List.take_left]

/-- A read that stays inside the BLOCK sees the block: the page tail
    [entry_stack_image] adds sits above it. -/
theorem rdn_image_in_block (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (draw : EntryDraw) (a : word) (n : Nat)
    (Hin : (a.toNat : Int) + (n : Int)
      ≤ entry_block_top sp (build_stack_bytes ph sp argv envp uid hw draw))
    (Hnw : (a.toNat : Int) + (n : Int) ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw draw)) a n
      = rdn segs (stack_to_mem sp (build_stack_bytes ph sp argv envp uid hw draw)) a n := by
  apply rdn_ext
  · exact Hnw
  · intro x Hx
    apply stack_to_mem_image_in_block
    have htop : entry_block_top sp (build_stack_bytes ph sp argv envp uid hw draw)
        = (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw draw).length : Int) := rfl
    omega

/-- [read_at_offset] against the mapped image rather than the block. -/
theorem read_at_offset_image (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (draw : EntryDraw)
    (pre mid post : List byte) (k : Nat)
    (Hb : build_stack_bytes ph sp argv envp uid hw draw = pre ++ mid ++ post)
    (Hk : mid.length = k)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp argv envp uid hw draw).length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw draw))
        (sp + nat_to_word pre.length) k = some mid := by
  have htop : entry_block_top sp (build_stack_bytes ph sp argv envp uid hw draw)
      = (sp.toNat : Int) + ((build_stack_bytes ph sp argv envp uid hw draw).length : Int) := rfl
  have hblen : (build_stack_bytes ph sp argv envp uid hw draw).length
      = pre.length + mid.length + post.length := by rw [Hb]; simp; omega
  have hu : ((sp + nat_to_word pre.length).toNat : Int) = (sp.toNat : Int) + (pre.length : Int) := by
    unfold nat_to_word
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : sp.toNat + pre.length % 2 ^ 64 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : pre.length < 2 ^ 64)]
    push_cast
    omega
  have hIn : ((sp + nat_to_word pre.length).toNat : Int) + (k : Int)
      ≤ entry_block_top sp (build_stack_bytes ph sp argv envp uid hw draw) := by
    rw [htop]; omega
  have hB : ((sp + nat_to_word pre.length).toNat : Int) + (k : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    omega
  rw [rdn_image_in_block segs ph sp argv envp uid hw draw _ _ hIn hB]
  exact read_at_offset segs sp _ pre mid post k Hb Hk Hnw

/-- [read_argc]: the stack image's first word is argc. -/
theorem read_argc (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp argv envp uid hw rnd).length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd)) sp 8
      = some (word_le8 (len_word argv)) := by
  obtain ⟨tl, E⟩ := bsb_argc_prefix ph sp argv envp uid hw rnd
  have h8 : (word_le8 (len_word argv)).length = 8 := length_n_to_le_8 _
  have := read_at_offset_image segs ph sp argv envp uid hw rnd [] (word_le8 (len_word argv)) tl 8
    (by rw [E]; rfl) h8 Hnw
  simpa [word_add_0] using this

/-- Bytes are typed: every byte is below 256 by construction, with no need for
    a separate `Forall (fun b => b < 256)` hypothesis. -/
theorem nth_app0_bound (a1 : List byte) (j : Nat) :
    ((a1 ++ [BitVec.ofInt 8 0])[j]?.getD (BitVec.ofInt 8 0)).toNat < 256 :=
  (BitVec.isLt _)

/-- A one-byte read at a known offset inside a laid-out block. -/
theorem read_byte_at (segs : List Segment) (sp : word) (bytes pre s post : List byte)
    (j : Nat) (Hb : bytes = pre ++ s ++ post) (Hj : j < s.length)
    (Hnw : (sp.toNat : Int) + (bytes.length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp bytes) (sp + nat_to_word (pre.length + j)) 1
      = some [(s[j]?).getD (BitVec.ofInt 8 0)] := by
  obtain ⟨b, hb, hdrop⟩ := nth_error_skipn_cons s j Hj
  have hsplit : s = s.take j ++ b :: s.drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop j s]
    rw [hdrop]
  have hlen : (pre ++ s.take j).length = pre.length + j := by
    simp only [List.length_append, List.length_take]
    rw [Nat.min_eq_left (by omega)]
  have hpre2 : (pre ++ s.take j) ++ [b] ++ (s.drop (j + 1) ++ post) = pre ++ s ++ post := by
    have h1 : s.take j ++ (b :: s.drop (j + 1)) = s := hsplit.symm
    calc (pre ++ s.take j) ++ [b] ++ (s.drop (j + 1) ++ post)
        = pre ++ ((s.take j ++ (b :: s.drop (j + 1))) ++ post) := by
          simp only [List.singleton_append, List.append_assoc, List.cons_append,
            List.nil_append]
      _ = pre ++ (s ++ post) := by rw [h1]
      _ = pre ++ s ++ post := by simp only [List.append_assoc]
  have H := read_at_offset segs sp bytes (pre ++ s.take j) [b] (s.drop (j + 1) ++ post) 1
    (by rw [Hb, ← hpre2]) rfl Hnw
  rw [hlen] at H
  rw [H, hb]
  rfl

/-- [read_byte_at] against the mapped image. -/
theorem read_byte_at_image (segs : List Segment) (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (draw : EntryDraw)
    (pre s post : List byte) (j : Nat)
    (Hb : build_stack_bytes ph sp argv envp uid hw draw = pre ++ s ++ post)
    (Hj : j < s.length)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp argv envp uid hw draw).length : Int) < ((2 ^ 64 : Nat) : Int)) :
    rdn segs (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw draw))
        (sp + nat_to_word (pre.length + j)) 1
      = some [(s[j]?).getD (BitVec.ofInt 8 0)] := by
  obtain ⟨b, hb, hdrop⟩ := nth_error_skipn_cons s j Hj
  have hsplit : s = s.take j ++ b :: s.drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop j s]
    rw [hdrop]
  have hlen : (pre ++ s.take j).length = pre.length + j := by
    simp only [List.length_append, List.length_take]
    rw [Nat.min_eq_left (by omega)]
  have hpre2 : (pre ++ s.take j) ++ [b] ++ (s.drop (j + 1) ++ post) = pre ++ s ++ post := by
    have h1 : s.take j ++ (b :: s.drop (j + 1)) = s := hsplit.symm
    calc (pre ++ s.take j) ++ [b] ++ (s.drop (j + 1) ++ post)
        = pre ++ ((s.take j ++ (b :: s.drop (j + 1))) ++ post) := by
          simp only [List.singleton_append, List.append_assoc, List.cons_append,
            List.nil_append]
      _ = pre ++ (s ++ post) := by rw [h1]
      _ = pre ++ s ++ post := by simp only [List.append_assoc]
  have H := read_at_offset_image segs ph sp argv envp uid hw draw
    (pre ++ s.take j) [b] (s.drop (j + 1) ++ post) 1
    (by rw [Hb, ← hpre2]) rfl Hnw
  rw [hlen] at H
  rw [H, hb]
  rfl

/-! ## Loads -/

/-- Zero-extending the low byte of a widened byte is the byte's unsigned
    reading. -/
theorem zext8_le_word (b : byte) :
    zext 64 (bits 0 8 (le_bytes_to_word [b])) = BitVec.ofInt 64 (b.toNat : Int) := by
  rw [le_word_1, b_extract8_id]
  apply BitVec.eq_of_toNat_eq
  unfold zext BitVec.zeroExtend
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega),
    BitVec.toNat_ofInt]
  have hK : (↑(BitVec.toNat b) % ((2 ^ 64 : Nat) : Int)) = (↑(BitVec.toNat b) : Int) :=
    Int.emod_eq_of_lt (by omega) (by have := b.isLt; omega)
  rw [hK, Int.toNat_natCast]

/-- Zero-extending the low `n` bits of a loaded value. -/
theorem zext_bits (v : word) (n : Nat) (hn : n ≤ 64) (Hv : (v.toNat : Int) < ((2 ^ n : Nat) : Int)) :
    zext 64 (bits 0 n v) = v := by
  have hv : v.toNat < 2 ^ n := by omega
  apply BitVec.eq_of_toNat_eq
  unfold zext BitVec.zeroExtend
  rw [BitVec.toNat_setWidth, bits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

open Lean Parser Tactic in
macro "step_load_start2" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [RiscvSemantics.step, RiscvSemantics.step_accesses, mkst, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, load_val, interp_eff_accesses,
      mkAccessReport, rset, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet,
      bvmap_set, Bool.false_eq_true, reduceIte, ite_true, ite_false, width_bytes])

/-- `lbu`: an unsigned byte load. -/
theorem step_lbu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ1 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (BitVec.ofInt 64 (b.toNat : Int))) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = some [b] := by
    rw [hba, ov_rdn]; exact Hread
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]
  simp only [bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, zext8_le_word]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-! ## LE assembly bridges -/

theorem bytes_le_to_Z_nonneg (bs : List byte) : 0 ≤ bytes_le_to_Z bs := Int.natCast_nonneg _

/-- A byte list is bounded by `2^(8 * length)`. -/
theorem bytes_le_to_Nat_bound (bs : List byte) :
    bytes_le_to_Nat bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [bytes_le_to_Nat]
  | cons b rest ih =>
    have h1 : b.toNat < 2 ^ (8 * (rest.length + 1)) := by
      rw [show 8 * (rest.length + 1) = 8 * rest.length + 8 from by omega, Nat.pow_add]
      calc b.toNat < 2 ^ 8 := b.isLt
        _ = 1 * 2 ^ 8 := by rw [Nat.one_mul]
        _ ≤ 2 ^ (8 * rest.length) * 2 ^ 8 :=
          Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
    have h2 : bytes_le_to_Nat rest <<< 8 < 2 ^ (8 * (rest.length + 1)) := by
      rw [Nat.shiftLeft_eq]
      rw [show 8 * (rest.length + 1) = 8 * rest.length + 8 from by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right ih (by decide)
    rw [show bytes_le_to_Nat (b :: rest) = b.toNat ||| (bytes_le_to_Nat rest <<< 8) from rfl]
    exact Nat.or_lt_two_pow h1 h2

/-- The `Int`-valued bound. -/
theorem bytes_le_to_Z_bound (bs : List byte) :
    bytes_le_to_Z bs < ((2 ^ (8 * bs.length) : Nat) : Int) := by
  unfold bytes_le_to_Z
  exact Int.ofNat_lt.mpr (bytes_le_to_Nat_bound bs)

/-- `lb`. -/
theorem step_lb (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ1 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = some [b] := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 8 (le_bytes_to_word [b])) = v_lb b := b_lb_val b
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `lh`. -/
theorem step_lh (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ2 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 2 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 2 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 16 (le_bytes_to_word bs)) = v_lh v := by
    rw [le_word_v bs v Hv, b_lh_val]
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `lw`. -/
theorem step_lw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ4 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 4 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : sext 64 (bits 0 32 (le_bytes_to_word bs)) = v_lw v := by
    rw [le_word_v bs v Hv, b_lw_val]
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `lhu`. -/
theorem step_lhu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ2 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 2 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 2 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : zext 64 (bits 0 16 (le_bytes_to_word bs)) = v := by
    rw [le_word_v bs v Hv]
    have hlen : bs.length = 2 := rdn_length segs mem 2 _ bs Hread
    have hbnd : (bytes_le_to_Z bs) < ((2 ^ 16 : Nat) : Int) := by
      have h := bytes_le_to_Z_bound bs
      rw [hlen] at h
      simpa using h
    refine zext_bits v 16 (by decide) ?_
    rw [← Hv]
    exact hbnd
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `lwu`. -/
theorem step_lwu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ4 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 4 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : zext 64 (bits 0 32 (le_bytes_to_word bs)) = v := by
    rw [le_word_v bs v Hv]
    have hlen : bs.length = 4 := rdn_length segs mem 4 _ bs Hread
    have hbnd : (bytes_le_to_Z bs) < ((2 ^ 32 : Nat) : Int) := by
      have h := bytes_le_to_Z_bound bs
      rw [hlen] at h
      simpa using h
    refine zext_bits v 32 (by decide) ?_
    rw [← Hv]
    exact hbnd
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `ld`: the full word, no extension. -/
theorem step_ld (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load .SZ8 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) 8 = some bs)
    (Hv : bytes_le_to_Z bs = (v.toNat : Int)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 8 = some bs := by
    rw [hba, ov_rdn]; exact Hread
  have hv : bits 0 64 (le_bytes_to_word bs) = v := by
    rw [le_word_v bs v Hv]
    apply BitVec.eq_of_toNat_eq
    simp only [bits, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (by have := v.isLt; omega)
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  simp only [hov, hv, bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4]
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-! ## Proof helper for value shapes that carry if-expressions

    After [step_pipeline] and unfolding [getr], both sides of the goal carry
    syntactically identical boolean scrutinees; destruct them all, then each
    leaf closes by conversion. -/
macro "split_value_ifs" : tactic =>
  `(tactic| (repeat' first | rfl | (split <;> skip)))

/-- Sanity check for [split_value_ifs]: the `if`-carrying shape of a value
    bridge closes after the scrutinee is destructed. -/
example (b : Bool) (x : word) :
    (if b then x else x) = x := by
  split_value_ifs

/-! ## Per-width range views (unfolding `2^n` to literals) -/

theorem u64_range (x : word) : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2 ^ 64 := by
  have := x.isLt; omega

theorem u8_range (b : byte) : 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) < 256 := by
  have := b.isLt; omega

theorem u6_range (s : BitVec 6) : 0 ≤ (s.toNat : Int) ∧ (s.toNat : Int) < 64 := by
  have := s.isLt; omega

theorem u5_range (s : BitVec 5) : 0 ≤ (s.toNat : Int) ∧ (s.toNat : Int) < 32 := by
  have := s.isLt; omega

theorem wrap64_range (z : Int) :
    0 ≤ bv_wrap 64 z ∧ bv_wrap 64 z < ((2 ^ 64 : Nat) : Int) :=
  emod64_bounds z

/-- [bv_swrap] only depends on the argument mod `2^n`. -/
theorem bv_swrap_congr (n : Nat) (x y : Int) (H : bv_wrap n x = bv_wrap n y) :
    bv_swrap n x = bv_swrap n y := by
  simp only [bv_swrap]
  simp only [bv_wrap] at H ⊢
  rw [← Int.emod_add_emod, H, Int.emod_add_emod]

theorem bv_swrap_add_swrap_l (n : Nat) (x y : Int) :
    bv_swrap n (bv_swrap n x + y) = bv_swrap n (x + y) := by
  unfold bv_swrap
  have h : (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int)
      - ((2 ^ (n - 1) : Nat) : Int) + y + ((2 ^ (n - 1) : Nat) : Int)
      = (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) + y := by omega
  rw [h, Int.emod_add_emod]
  congr 2
  omega

theorem bv_swrap_add_swrap_r (n : Nat) (x y : Int) :
    bv_swrap n (x + bv_swrap n y) = bv_swrap n (x + y) := by
  rw [Int.add_comm x, bv_swrap_add_swrap_l, Int.add_comm]

/-- Above the half-modulus the signed wrap subtracts the modulus. -/
theorem bv_swrap_hi (n : Nat) (z : Int) (Hn : n ≠ 0)
    (Hlo : ((2 ^ (n - 1) : Nat) : Int) ≤ z) (Hhi : z < ((2 ^ n : Nat) : Int)) :
    bv_swrap n z = z - ((2 ^ n : Nat) : Int) := by
  unfold bv_swrap
  have hnm : n = (n - 1) + 1 := by omega
  have hmul : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    rw [hnm, Nat.pow_succ]
    push_cast
    rw [Int.mul_comm]
  have hpos : (0 : Int) < ((2 ^ n : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos n)
  have hhalf : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have h1 : (z + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int)
      = z + ((2 ^ (n - 1) : Nat) : Int) - ((2 ^ n : Nat) : Int) := by
    have h2 : z + ((2 ^ (n - 1) : Nat) : Int)
        = ((z + ((2 ^ (n - 1) : Nat) : Int) - ((2 ^ n : Nat) : Int))
           + ((2 ^ n : Nat) : Int)) := by omega
    rw [h2, Int.add_emod_right, Int.emod_eq_of_lt] <;> omega
  rw [h1]
  omega

/-- Record equality for [mkst]. -/
theorem ok_mkst_eq (r1 r2 : BvMap word) (p1 p2 : word) (m1 m2 : word → Option byte)
    (ro : word → Option byte) (Hr : r1 = r2) (Hp : p1 = p2) (Hm : ∀ a, m1 a = m2 a) :
    (machine_result.MachineOk (mkst r1 p1 m1 ro) : machine_result machine_state)
      = .MachineOk (mkst r2 p2 m2 ro) := by
  subst Hr; subst Hp
  have : m1 = m2 := funext Hm
  rw [this]

/-- `bytes_le_to_Nat` over a concatenation. -/
theorem bytes_le_to_Nat_app (xs ys : List byte) :
    bytes_le_to_Nat (xs ++ ys)
      = bytes_le_to_Nat xs ||| (bytes_le_to_Nat ys <<< (8 * xs.length)) := by
  induction xs with
  | nil => simp [bytes_le_to_Nat]
  | cons x rest ih =>
    rw [show (x :: rest) ++ ys = x :: (rest ++ ys) from rfl]
    rw [show bytes_le_to_Nat (x :: (rest ++ ys))
        = x.toNat ||| (bytes_le_to_Nat (rest ++ ys) <<< 8) from rfl]
    rw [ih]
    rw [show bytes_le_to_Nat (x :: rest) = x.toNat ||| (bytes_le_to_Nat rest <<< 8) from rfl]
    rw [List.length_cons, show 8 * (rest.length + 1) = 8 * rest.length + 8 from by omega]
    rw [Nat.shiftLeft_or_distrib]
    rw [← Nat.shiftLeft_add, Nat.or_assoc]

/-- [bytes_le_to_Z] splits the same way. -/
theorem bytes_le_app (xs ys : List byte) :
    bytes_le_to_Z (xs ++ ys)
      = zlor (bytes_le_to_Z xs) (zshiftl (bytes_le_to_Z ys) (8 * xs.length)) := by
  unfold bytes_le_to_Z zlor zshiftl
  rw [bytes_le_to_Nat_app]
  have h1 : (bytes_le_to_Nat ys : Int) * ((2 ^ (8 * xs.length) : Nat) : Int)
      = ((bytes_le_to_Nat ys <<< (8 * xs.length) : Nat) : Int) := by
    rw [Nat.shiftLeft_eq]
    push_cast
    rfl
  have h2 : ((bytes_le_to_Nat xs : Int)).toNat = bytes_le_to_Nat xs := rfl
  rw [h1, h2]
  simp only [Int.toNat_natCast]

/-- [le2] assembles the little-endian two-byte value. -/
theorem le2_spec (b1 b0 : byte) :
    ((le2 b1 b0).toNat : Int) = bytes_le_to_Z [b0, b1] := by
  unfold le2 bytes_le_to_Z
  rw [show b1.append b0 = b1 ++ b0 from rfl, BitVec.toNat_append]
  rw [show bytes_le_to_Nat [b0, b1] = b0.toNat ||| (b1.toNat <<< 8) from by
        simp [bytes_le_to_Nat], Nat.or_comm]

/-- [le4] assembles the little-endian four-byte value. -/
theorem le4_spec (b3 b2 b1 b0 : byte) :
    ((le4 b3 b2 b1 b0).toNat : Int) = bytes_le_to_Z [b0, b1, b2, b3] := by
  have e1 : le4 b3 b2 b1 b0 = (b3 ++ b2) ++ (b1 ++ b0) := rfl
  unfold bytes_le_to_Z
  rw [e1, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
  rw [show bytes_le_to_Nat [b0, b1, b2, b3]
      = bytes_le_to_Nat ([b0, b1] ++ [b2, b3]) from rfl, bytes_le_to_Nat_app,
    show bytes_le_to_Nat [b0, b1] = b0.toNat ||| (b1.toNat <<< 8) from by
      simp [bytes_le_to_Nat],
    show bytes_le_to_Nat [b2, b3] = b2.toNat ||| (b3.toNat <<< 8) from by
      simp [bytes_le_to_Nat]]
  rw [Nat.or_comm (b3.toNat <<< 8) b2.toNat,
    Nat.or_comm (((b2.toNat ||| b3.toNat <<< 8)) <<< (8 + 8)) (b1.toNat <<< 8 ||| b0.toNat),
    Nat.or_comm (b1.toNat <<< 8) b0.toNat]
  rfl

/-- [le8] assembles the little-endian eight-byte value. -/
theorem le8_spec (b7 b6 b5 b4 b3 b2 b1 b0 : byte) :
    ((le8 b7 b6 b5 b4 b3 b2 b1 b0).toNat : Int)
      = bytes_le_to_Z [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have h4 : ∀ (c3 c2 c1 c0 : byte), (le4 c3 c2 c1 c0).toNat = bytes_le_to_Nat [c0, c1, c2, c3] := by
    intro c3 c2 c1 c0
    have h := le4_spec c3 c2 c1 c0
    unfold bytes_le_to_Z at h
    exact Int.natCast_inj.mp h
  have e1 : le8 b7 b6 b5 b4 b3 b2 b1 b0 = (le4 b7 b6 b5 b4) ++ (le4 b3 b2 b1 b0) := rfl
  unfold bytes_le_to_Z
  rw [e1, BitVec.toNat_append, h4, h4]
  rw [show bytes_le_to_Nat [b0, b1, b2, b3, b4, b5, b6, b7]
      = bytes_le_to_Nat ([b0, b1, b2, b3] ++ [b4, b5, b6, b7]) from rfl, bytes_le_to_Nat_app,
    Nat.or_comm]
  rfl

/-! ## The `Z_to_le_bytes` round-trip -/

/-- Splitting a residue at the low eight bits. -/
theorem mod_mul_256 (x m : Nat) (hm : 0 < m) :
    x % (m * 256) = (x / 256 % m) * 256 + x % 256 := by
  have hx : x = 256 * (x / 256) + x % 256 := (Nat.div_add_mod x 256).symm
  have hr : x % 256 < 256 := Nat.mod_lt _ (by decide)
  have hqr : x / 256 % m < m := Nat.mod_lt _ hm
  have hstep : (256 * (x / 256)) % (m * 256) = (x / 256 % m) * 256 := by
    rw [Nat.mul_comm 256 (x / 256), Nat.mul_mod_mul_right]
  have h1 : x % (m * 256) = (256 * (x / 256) + x % 256) % (m * 256) :=
    congrArg (fun t => t % (m * 256)) hx
  rw [h1, Nat.add_mod, hstep, Nat.mod_eq_of_lt (by omega : x % 256 < m * 256),
    Nat.mod_eq_of_lt (by omega : (x / 256 % m) * 256 + x % 256 < m * 256)]

/-- Reassembling `8k` little-endian bytes recovers the residue mod `2^(8k)`. -/
theorem lor_shift_div (x k : Nat) :
    (x % 256) ||| ((x / 256 % 2 ^ (8 * k)) <<< 8) = x % 2 ^ (8 * (k + 1)) := by
  have hr : x % 256 < 2 ^ 8 := by
    have := Nat.mod_lt x (by decide : 0 < 256); omega
  have hor : (x / 256 % 2 ^ (8 * k)) <<< 8 ||| (x % 256)
      = (x / 256 % 2 ^ (8 * k)) <<< 8 + x % 256 :=
    (Nat.shiftLeft_add_eq_or_of_lt hr _).symm
  rw [Nat.or_comm, hor, Nat.add_comm, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ 8 = 256 from by decide]
  rw [show 8 * (k + 1) = 8 * k + 8 from by omega, Nat.pow_add,
    show (2 : Nat) ^ 8 = 256 from by decide,
    Nat.add_comm (x % 256) (x / 256 % 2 ^ (8 * k) * 256),
    ← mod_mul_256 x (2 ^ (8 * k)) (Nat.two_pow_pos _)]

/-- `Z_to_le_bytes` is `bytes_le_to_Nat`'s inverse on non-negative values. -/
theorem bytes_le_to_Nat_Z_to_le (k : Nat) (z : Int) (Hz : 0 ≤ z) :
    bytes_le_to_Nat (Z_to_le_bytes k z) = z.toNat % 2 ^ (8 * k) := by
  induction k generalizing z with
  | zero => simp [Z_to_le_bytes, bytes_le_to_Nat, Nat.mod_one]
  | succ k ih =>
    have hz8 : (0 : Int) ≤ z >>> 8 := by
      rw [Int.shiftRight_eq_div_pow]
      exact Int.ediv_nonneg Hz (by decide)
    have hb : (BitVec.ofInt 8 z).toNat = z.toNat % 256 := by
      rw [BitVec.toNat_ofInt, show ((2 ^ 8 : Nat) : Int) = 256 from by decide]
      omega
    have hq : (z >>> 8).toNat = z.toNat / 256 := by
      rw [Int.shiftRight_eq_div_pow, show ((2 ^ 8 : Nat) : Int) = 256 from by decide]
      omega
    rw [show Z_to_le_bytes (k + 1) z = BitVec.ofInt 8 z :: Z_to_le_bytes k (z >>> 8) from rfl,
      show bytes_le_to_Nat (BitVec.ofInt 8 z :: Z_to_le_bytes k (z >>> 8))
        = (BitVec.ofInt 8 z).toNat
          ||| (bytes_le_to_Nat (Z_to_le_bytes k (z >>> 8)) <<< 8) from rfl,
      ih (z >>> 8) hz8, hb, hq]
    exact lor_shift_div z.toNat k

/-- The `Int`-valued form. -/
theorem bytes_le_Z_to_le (k : Nat) (z : Int) (Hz : 0 ≤ z) :
    bytes_le_to_Z (Z_to_le_bytes k z) = ((z.toNat % 2 ^ (8 * k) : Nat) : Int) := by
  unfold bytes_le_to_Z
  rw [bytes_le_to_Nat_Z_to_le k z Hz]

/-- `word_to_le_bytes` reads back as the word's unsigned value. -/
theorem bytes_le_N (k : Nat) (v : word) :
    bytes_le_to_Z (word_to_le_bytes k v) = ((v.toNat % 2 ^ (8 * k) : Nat) : Int) := by
  unfold word_to_le_bytes
  exact bytes_le_Z_to_le k (v.toNat : Int) (by omega)

/-- `word_le8` reads back as the word's unsigned value. -/
theorem bytes_le_n_to_le_8 (v : word) : bytes_le_to_Z (word_le8 v) = (v.toNat : Int) := by
  have h := bytes_le_N 8 v
  rwa [show 8 * 8 = 64 from rfl, show v.toNat % 2 ^ 64 = v.toNat from
        Nat.mod_eq_of_lt (by have := v.isLt; omega)] at h

/-- The entry stack image never exceeds [Run.entry_stack_span], the closed-form
    upper bound [Run.entry_stack_fits] is stated against.  [Run] cannot prove
    this itself — the layout arithmetic lives here — and without it
    [entry_stack_span] would be an over-approximation nothing checks: add one
    more word to [build_stack_bytes] and this lemma stops holding, which is the
    whole reason the span is a closed form rather than a second copy of the
    layout.  Everything that needs a size for the initial stack image goes
    through this lemma. -/
theorem build_stack_bytes_within_span (ph : PhdrInfo) (sp : word)
    (a e : List (List byte)) (uid hw : word) (rnd : EntryDraw) :
    ((build_stack_bytes ph sp a e uid hw rnd).length : Int) ≤ entry_stack_span a e := by
  unfold entry_stack_span
  simp only [build_stack_bytes, List.length_append, List.length_replicate, length_n_to_le_8,
    length_flat_map_le8, length_string_addrs_fst, length_flatten_strings,
    length_auxv_bytes, length_at_random_bytes, total_arg_bytes_Z, auxv_size]
  omega

/-- The page-granular entry stack never rises above the top of the user address
    space, and needs no premise of its own to say so: [Run.entry_stack_image]
    maps up to the page boundary above the block, and [Run.entry_stack_fits] —
    the conjunct of [Run.valid_entry] that keeps the block under
    [State.sp_window_hi] — already forces that boundary under it too, because
    [sp_window_hi] is page-aligned and rounding up an address below a
    page-aligned bound stays at or below it.

    This is why mapping whole pages needs no change to [Run.valid_sp] or
    [Run.valid_entry].  Without it, mapping whole pages would mean NARROWING
    the entry quantifier to keep the mapping inside the address space —
    excluding placements a kernel really produces, which is the soundness hole
    [Run.valid_entry]'s own note argues against. -/
theorem entry_page_top_within_window (ph : PhdrInfo) (sp : word)
    (argv envp : List (List byte)) (uid hw : word) (draw : EntryDraw)
    (Hfit : entry_stack_fits sp argv envp) :
    entry_page_top sp (build_stack_bytes ph sp argv envp uid hw draw) ≤ sp_window_hi := by
  have Hlen := build_stack_bytes_within_span ph sp argv envp uid hw draw
  unfold entry_stack_fits at Hfit
  unfold entry_page_top
  apply page_round_up_Z_le
  · unfold entry_block_top
    omega
  · decide
