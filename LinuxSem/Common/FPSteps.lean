/-
  * Common.FPSteps — single-step lemmas for the RISC-V F/D instructions
    (and the two fcsr CSR ops) that occur in LIVE code of the reference
    binary (strtod / __floatscan / soft-float helpers / cJSON parse_number).

    Image-INDEPENDENT (parametric in [segs]).

    Conventions.
    * States are [@mkst fx regs pc mem rom] with the FP register file and
      fcsr carried by the typeclass instance [fx : FPState] (PropExec).
      An FP instruction CHANGES the instance; the post state is written
      with an explicit instance [@mkst (mkFP fregs' fcsr') ...].
    * Nobody downstream needs FP VALUES, so every lemma is stated in
      "havoc" form: the new FP register file / the integer result are
      existentially quantified; what IS tracked is the dynamic rounding
      mode field fcsr[7:5] ([frm_zero]), which must be a valid mode for
      the rm=7 (DYN) arithmetic instructions to be modeled at all, and
      which no live instruction changes (arithmetic only ORs flags into
      fcsr[4:0]; [csrsi fflags,_] only touches fcsr[4:0]).
    * [frm_zero f := Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0].
    * All names are prefixed [fp_].

    NOTES.
 This tree's [Nat]
      spelling is also what `Sem.frm_of` itself computes, so the rounding-mode
      lemmas below match the model's own expression by conversion.
 [mkstFP_eq_mkst] records
      that the two are the same record.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Riscv.Fpu

set_option autoImplicit false
-- Same rationale as `PropExec`/`SeqExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.FPSteps

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec

/-! ## The FP-state constructor and the [Nat] shift toolkit -/

/-- The FP-state constructor  writes as `mkFP`.

     defines this in `PropExec`; this tree defines it here,
    this file being its only user. -/
@[reducible] def mkFP (fregs : BvMap word) (fcsr : BitVec 32) : FPState := ⟨fregs, fcsr⟩

/-- The post state of an FP instruction: [mkst] with the FP register file and
    fcsr given explicitly.
 The name `mkstFP` is used because Lean's simplifier cannot unfold
    `@mkst inst …` at a
    NON-ambient [inst] — the equation lemma's instance argument is filled by
    typeclass search, not by matching — so an explicit-argument spelling is
    what makes the post states of the FP step lemmas reduce. -/
def mkstFP (fregs : BvMap word) (fcsr : BitVec 32) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) : machine_state :=
  { ms_regs := regs, ms_fregs := fregs, ms_pc_val := pc, ms_svc_pending := none,
    ms_resv := none, ms_fcsr := fcsr, ms_mem := mem, ms_rom := rom }

/-- [mkstFP] IS  `@mkst (mkFP …)`, definitionally. -/
theorem mkstFP_eq_mkst (fregs : BvMap word) (fcsr : BitVec 32) (regs : BvMap word)
    (pc : word) (mem rom : word → Option byte) :
    mkstFP fregs fcsr regs pc mem rom = @mkst (mkFP fregs fcsr) regs pc mem rom := rfl

/-- `>>>` distributes over `|||` (Lean core has the
    `testBit` laws but not this shift law). -/
theorem shiftRight_or (a b n : Nat) : (a ||| b) >>> n = (a >>> n) ||| (b >>> n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or]

/-- `>>>` distributes over `&&&`. -/
theorem shiftRight_and (a b n : Nat) : (a &&& b) >>> n = (a >>> n) &&& (b >>> n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and]

/- =====================================================================
   The rounding-mode-field invariant
   ===================================================================== -/

/-- `fcsr[7:5] = 0`: the dynamic rounding mode field is RNE.
-/
def frm_zero (f : BitVec 32) : Prop := (f.toNat >>> 5) &&& 7 = 0

/-- The FP state at process entry has `fcsr = 0`, hence `frm_zero`. -/
theorem fp_frm_zero_fx0 : frm_zero fx0.fp_csr := by
  unfold frm_zero
  decide

/-- The encoded exception flags occupy bits 0..4 of the fcsr. -/
theorem fp_fflags_bits_range (fl : fflags) : 0 ≤ fflags_bits fl ∧ fflags_bits fl < 32 := by
  rcases fl with ⟨nv, dz, of_, uf, nx⟩
  unfold fflags_bits
  cases nv <;> cases dz <;> cases of_ <;> cases uf <;> cases nx <;> decide

/-- A `bv 32` is in `[0, 2^32)`. -/
theorem fp_u32_range (f : BitVec 32) : 0 ≤ (f.toNat : Int) ∧ (f.toNat : Int) < 2 ^ 32 := by
  have := f.isLt; omega

/-- : the wrap of an in-range `Z`
    at width 32 reads back as the same `Z`.  Same statement as
    `SeqExec.toNat_ofInt_small`, restated under this file's name because
     cites its own `Z_to_bv_unsigned` + `bv_wrap_small` pair here. -/
theorem fp_u_Z2bv32 (z : Int) (h0 : 0 ≤ z) (h1 : z < ((2 ^ 32 : Nat) : Int)) :
    ((BitVec.ofInt 32 z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-- the [Nat]-valued reading of [fp_u_Z2bv32] — the form the
    `frm_zero` arithmetic below rewrites with. -/
theorem fp_u_Z2bv32_nat (z : Int) (h0 : 0 ≤ z) (h1 : z < ((2 ^ 32 : Nat) : Int)) :
    (BitVec.ofInt 32 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1]

/-- AND-ing a bounded value with anything keeps it bounded ([Z.land] at `Z`,
    stated at this tree's `zland`). -/
theorem fp_Z_land_range_l (n : Nat) (a b : Int) (hn : (0 : Int) ≤ (n : Int))
    (ha : 0 ≤ a ∧ a < ((2 ^ n : Nat) : Int)) :
    0 ≤ zland a b ∧ zland a b < ((2 ^ n : Nat) : Int) := by
  have h1 : a.toNat < 2 ^ n := by
    have := ha.2
    omega
  have h2 : (a.toNat &&& b.toNat) ≤ a.toNat := Nat.and_le_left
  unfold zland
  omega

/-- OR-ing two bounded values keeps them bounded ([Z.lor] at `Z`). -/
theorem fp_Z_lor_range (n : Nat) (a b : Int) (hn : (0 : Int) ≤ (n : Int))
    (ha : 0 ≤ a ∧ a < ((2 ^ n : Nat) : Int)) (hb : 0 ≤ b ∧ b < ((2 ^ n : Nat) : Int)) :
    0 ≤ zlor a b ∧ zlor a b < ((2 ^ n : Nat) : Int) := by
  have h1 : a.toNat < 2 ^ n := by omega
  have h2 : b.toNat < 2 ^ n := by omega
  have h3 : (a.toNat ||| b.toNat) < 2 ^ n := Nat.or_lt_two_pow h1 h2
  unfold zlor
  omega

/-- OR-ing flag bits (< 32) into fcsr keeps fcsr[7:5]. -/
theorem fp_frm_zero_accrue (f : BitVec 32) (b : Int) (Hb : 0 ≤ b ∧ b < 32)
    (Hf : frm_zero f) : frm_zero (BitVec.ofInt 32 (zlor (f.toNat : Int) b)) := by
  have hr := fp_u32_range f
  have hlt : 0 ≤ zlor (f.toNat : Int) b ∧ zlor (f.toNat : Int) b < ((2 ^ 32 : Nat) : Int) :=
    fp_Z_lor_range 32 _ _ (by omega) hr ⟨Hb.1, by have := Hb.2; omega⟩
  have hz : (BitVec.ofInt 32 (zlor (f.toNat : Int) b)).toNat = (zlor (f.toNat : Int) b).toNat :=
    fp_u_Z2bv32_nat _ hlt.1 hlt.2
  unfold frm_zero at Hf ⊢
  rw [hz]
  have hb5 : b.toNat >>> 5 = 0 := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from by decide]
    exact Nat.div_eq_of_lt (by omega)
  show ((zlor (f.toNat : Int) b).toNat >>> 5) &&& 7 = 0
  rw [show (zlor (f.toNat : Int) b).toNat = (f.toNat ||| b.toNat) from rfl]
  rw [shiftRight_or, hb5, Nat.or_zero]
  exact Hf

/-- Writing the fflags slice (fcsr[4:0]) keeps fcsr[7:5]. -/
theorem fp_frm_zero_slice0_5 (f : BitVec 32) (v : word) (Hf : frm_zero f) :
    frm_zero (slice_set f 0 5 v) := by
  have hX : ((f.toNat &&& 4294967264) ||| (v.toNat &&& 31)) < 2 ^ 32 := by
    apply Nat.or_lt_two_pow
    · have := Nat.and_le_left (n := f.toNat) (m := 4294967264); omega
    · have := Nat.and_le_right (n := v.toNat) (m := 31); omega
  have hnat : ((slice_set f 0 5 v).toNat)
      = ((f.toNat &&& 4294967264) ||| (v.toNat &&& 31)) := by
    unfold slice_set
    simp only []
    rw [show ((2 : Nat) ^ Int.toNat 5 - 1) <<< Int.toNat 0 = 31 from by decide]
    rw [show Nat.xor 31 ((2 : Nat) ^ 32 - 1) = 4294967264 from by decide]
    rw [show Int.toNat 0 = 0 from rfl, Nat.shiftLeft_zero]
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hX),
      Int.toNat_natCast]
  unfold frm_zero
  rw [hnat, shiftRight_or]
  have hlow : (v.toNat &&& 31) >>> 5 = 0 := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from by decide]
    exact Nat.div_eq_of_lt (by have := Nat.and_le_right (n := v.toNat) (m := 31); omega)
  rw [hlow, Nat.or_zero, shiftRight_and]
  rw [show (4294967264 : Nat) >>> 5 = 134217727 from by decide]
  have hx : f.toNat >>> 5 < 2 ^ 27 := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 5 = 32 from by decide]
    have := f.isLt
    omega
  rw [show (134217727 : Nat) = 2 ^ 27 - 1 from by decide]
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow hx]
  exact Hf

/-- an in-range static rounding-mode field (0..4) resolves. -/
theorem rmode_of_Z_lt5 (m : Int) (h : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) :
    ∃ md, rmode_of_Z m = some md := by
  rcases h with h | h | h | h | h <;> rw [h] <;>
    first
      | exact ⟨.RNE, by decide⟩
      | exact ⟨.RTZ, by decide⟩
      | exact ⟨.RDN, by decide⟩
      | exact ⟨.RUP, by decide⟩
      | exact ⟨.RMM, by decide⟩

/-- With fcsr[7:5] = 0, every rm field a compiler emits (0..4 static, or
    7 = DYN) resolves to a rounding mode. -/
theorem fp_resolve_rm (rm : BitVec 3) (f : BitVec 32) (Hf : frm_zero f)
    (Hrm : (rm.toNat : Int) ≤ 4 ∨ (rm.toNat : Int) = 7) :
    ∃ md, rmode_of_field (rm.toNat : Int) (((f.toNat >>> 5) &&& 7 : Nat) : Int) = some md := by
  unfold frm_zero at Hf
  rw [Hf]
  unfold rmode_of_field
  by_cases h7 : ((rm.toNat : Int) == 7) = true
  · rw [ite_eq_left h7]
    exact ⟨.RNE, by decide⟩
  · rw [ite_eq_right h7]
    apply rmode_of_Z_lt5
    have hle : rm.toNat ≤ 4 := by
      rcases Hrm with h' | h'
      · omega
      · exfalso
        have : ((rm.toNat : Int) == 7) = true := by rw [h']; decide
        exact h7 this
    omega

/- =====================================================================
   The step pipeline for FP instructions
   ===================================================================== -/

/-! ## The step pipeline for FP instructions

    [PropExec]'s `step_pipeline`, extended with the `Sem`-level FP plumbing
    (`fget`/`fset`/`fread`/`fwrite`, the rounding-mode resolution, flag accrual
    and NaN boxing). -/
open Lean Parser Tactic in
macro "fp_pipeline" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [mkst, mkstFP, RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, interp_eff_accesses, mkAccessReport,
      rset, rget, with_pc, with_regs, with_resv, with_fcsr, with_fregs, reg_get, bvmapSet,
      bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, w0, Bool.false_eq_true,
      reduceIte, ite_true, ite_false, fget, fset, fp_format, fread, fwrite, accrue, resolve_rm,
      frm_of, nan_box, unbox_s, sgnj_val, inval_resv, width_bytes, load_val, store_val,
      low32, w1])

/-- with fcsr[7:5] = 0 the frm slice reads as 0 — 
    inline `unfold slice_get; change (Z.ones 3) with 7%Z; rewrite Hz`. -/
theorem slice_get_zero_of_frm_zero (f : BitVec 32) (h : frm_zero f) : slice_get f 5 3 = 0 := by
  unfold slice_get frm_zero at *
  rw [show ((3 : Int).toNat) = 3 from rfl, show ((5 : Int).toNat) = 5 from rfl,
    show ((2 : Nat) ^ 3 - 1) = 7 from by decide, h]
  rfl

section WithFP

variable [fx : FPState]

/- =====================================================================
   Data movement: fld / flw / fsd / fsw / fmv / fsgnj
   ===================================================================== -/

/-- `fld rd, imm(rs)`. -/
theorem fp_step_fld (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (a : word) (bs : List byte)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fLoad .D rd rs imm, 4))
    (Ha : v_addi (getr regs rs) imm.toInt = a) (Hr : rdn segs mem a 8 = some bs) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (mkstFP (bvmapSet rd (bits 0 64 (le_bytes_to_word bs)) fx.fp_regs)
        fx.fp_csr regs (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 8 = some bs := by
    rw [hba, Ha, ov_rdn]; exact Hr
  fp_pipeline Hf, He, Hd
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr, with_fregs] at hba hov ⊢
  simp only [hba] at hov ⊢
  rw [hov]

/-- `flw rd, imm(rs)`. -/
theorem fp_step_flw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (a : word) (bs : List byte)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fLoad .S rd rs imm, 4))
    (Ha : v_addi (getr regs rs) imm.toInt = a) (Hr : rdn segs mem a 4 = some bs) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (mkstFP (bvmapSet rd (nan_box (bits 0 32 (le_bytes_to_word bs)))
        fx.fp_regs) fx.fp_csr regs (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4 = some bs := by
    rw [hba, Ha, ov_rdn]; exact Hr
  fp_pipeline Hf, He, Hd
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr, with_fregs] at hba hov ⊢
  simp only [hba] at hov ⊢
  rw [hov]

/-- `fsd rs2, imm(rs1)`: an 8-byte store of the (here irrelevant) FP value. -/
theorem fp_step_fsd (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fStore .D rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hok : store_ok segs mem a 8 = true) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (@mkst fx regs (v_addi pc 4)
        (wbytes mem a (word_to_le_bytes 8 (reg_get fx.fp_regs rs2))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  fp_pipeline Hf, He, Hd
  simp only [getr, bv_eqb0_is_x0, reg_get, w0] at hba Ha
  rw [hba, Ha]
  simp only [Hok, ite_eq_left, reduceIte, write_to_mem_wbytes, word_to_le_bytes]

/-- `fsw rs2, imm(rs1)`: a 4-byte store. -/
theorem fp_step_fsw (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fStore .S rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hok : store_ok segs mem a 4 = true) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (@mkst fx regs (v_addi pc 4)
        (wbytes mem a
          (Z_to_le_bytes 4 ((low32 (reg_get fx.fp_regs rs2)).toNat : Int))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  fp_pipeline Hf, He, Hd
  simp only [getr, bv_eqb0_is_x0, reg_get, w0] at hba Ha
  rw [hba, Ha]
  simp only [Hok, ite_eq_left, reduceIte, write_to_mem_wbytes, word_to_le_bytes]

/-- `fmv.x.d rd, fs`: integer register := FP bit pattern. -/
theorem fp_step_fmv_x_d (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fmv .X_F .D rd rs1, 4)) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (@mkst fx (if bv_eqb rd 0 then regs
        else regupd regs rd (reg_get fx.fp_regs rs1)) (v_addi pc 4) mem rom) := by
  fp_pipeline Hf, He, Hd
  by_cases h1 : is_x0 rd <;> simp [h1, bvmapSet, bvmap_set, w0, reg_get]

/-- `fmv.x.w rd, fs`. -/
theorem fp_step_fmv_x_w (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fmv .X_F .S rd rs1, 4)) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (@mkst fx (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (low32 (reg_get fx.fp_regs rs1))))
        (v_addi pc 4) mem rom) := by
  fp_pipeline Hf, He, Hd
  by_cases h1 : is_x0 rd <;> simp [h1, bvmapSet, bvmap_set, w0, reg_get]

/-- `fmv.d.x fd, rs`. -/
theorem fp_step_fmv_d_x (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fmv .F_X .D rd rs1, 4)) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (mkstFP (bvmapSet rd (getr regs rs1) fx.fp_regs) fx.fp_csr
        regs (v_addi pc 4) mem rom) := by
  fp_pipeline Hf, He, Hd

/-- `fmv.w.x fd, rs`. -/
theorem fp_step_fmv_w_x (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fmv .F_X .S rd rs1, 4)) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (mkstFP (bvmapSet rd (nan_box (low32 (getr regs rs1))) fx.fp_regs)
        fx.fp_csr regs (v_addi pc 4) mem rom) := by
  fp_pipeline Hf, He, Hd

/-- `fsgnj` / `fsgnjn` / `fsgnjx` (`fmv.d`, `fneg.d`, `fabs.d` are these). -/
theorem fp_step_fsgnj (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : FsgnOp) (fmt : FFmt)
    (rd rs1 rs2 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fsgnj op fmt rd rs1 rs2, 4)) :
    ∃ fr', RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (mkstFP fr' fx.fp_csr regs (v_addi pc 4) mem rom) := by
  cases fmt with
  | S => exact ⟨?_, by fp_pipeline Hf, He, Hd; rfl⟩
  | D => exact ⟨?_, by fp_pipeline Hf, He, Hd; rfl⟩

/- =====================================================================
   Arithmetic / conversions / compares (havoc-valued)
   ===================================================================== -/

/-- fadd/fsub/fmul/fdiv . s/d : new FP file, flags OR-ed into fcsr[4:0]. -/
theorem fp_step_fari (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : FariOp) (fmt : FFmt)
    (rd rs1 rs2 : reg) (rm : BitVec 3)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fari op fmt rd rs1 rs2 rm, 4))
    (Hz : frm_zero fx.fp_csr) (Hrm : (rm.toNat : Int) ≤ 4 ∨ (rm.toNat : Int) = 7) :
    ∃ fr' cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
        .MachineOk (mkstFP fr' cs' regs (v_addi pc 4) mem rom) := by
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm fx.fp_csr Hz Hrm
  fp_pipeline Hf, He, Hd
  rw [Hmd]
  cases fmt <;> cases op
  all_goals simp only [interp_eff_accesses, drop_access_report, mkAccessReport, reduceIte, ite_eq_left]
  all_goals refine ⟨_, _, ?_, rfl⟩
  all_goals
    exact fp_frm_zero_accrue _ _
      ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz

/-- fcvt with an FP DESTINATION (fcvt.d.w, fcvt.s.w, fcvt.d.l[u], fcvt.s.d,
    fcvt.d.s, ...): new FP file, flags accrue. -/
theorem fp_step_fcvt_to_f (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (dst src : FcvtTy) (rd rs1 : reg)
    (rm : BitVec 3)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fcvt dst src rd rs1 rm, 4))
    (Hdst : dst = .S ∨ dst = .D) (Hz : frm_zero fx.fp_csr)
    (Hrm : (rm.toNat : Int) ≤ 4 ∨ (rm.toNat : Int) = 7) :
    ∃ fr' cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
        .MachineOk (mkstFP fr' cs' regs (v_addi pc 4) mem rom) := by
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm fx.fp_csr Hz Hrm
  fp_pipeline Hf, He, Hd
  rw [Hmd]
  rcases Hdst with h | h <;> rw [h] <;> cases src
  all_goals simp only [interp_eff_accesses, drop_access_report, mkAccessReport, reduceIte,
    ite_eq_left, Bool.false_eq_true]
  all_goals refine ⟨_, _, ?_, rfl⟩
  all_goals
    exact fp_frm_zero_accrue _ _
      ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz

/-- fcvt with an INTEGER destination (fcvt.l.d, fcvt.w.s, fcvt.lu.d, ...):
    integer rd := some word, flags accrue. -/
theorem fp_step_fcvt_to_x (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (dst src : FcvtTy) (rd rs1 : reg)
    (rm : BitVec 3)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fcvt dst src rd rs1 rm, 4))
    (Hdst : dst = .W ∨ dst = .WU ∨ dst = .L ∨ dst = .LU)
    (Hsrc : src = .S ∨ src = .D) (Hz : frm_zero fx.fp_csr)
    (Hrm : (rm.toNat : Int) ≤ 4 ∨ (rm.toNat : Int) = 7) :
    ∃ (v : word) (cs' : BitVec 32), frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
        .MachineOk (mkstFP fx.fp_regs cs'
          (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm fx.fp_csr Hz Hrm
  fp_pipeline Hf, He, Hd
  rw [Hmd]
  rcases Hdst with h | h | h | h <;> rw [h] <;> rcases Hsrc with h' | h' <;> rw [h']
  all_goals simp only [interp_eff_accesses, drop_access_report, mkAccessReport, reduceIte,
    ite_eq_left, Bool.false_eq_true]
  all_goals
    by_cases h1 : is_x0 rd
    · simp only [h1, bv_eqb0_is_x0, ite_true, ite_false, reduceIte, Bool.false_eq_true] at ⊢
      refine ⟨0, _, ?_, rfl⟩
      exact fp_frm_zero_accrue _ _
        ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz
    · simp only [h1, bv_eqb0_is_x0, ite_true, ite_false, reduceIte, Bool.false_eq_true] at ⊢
      refine ⟨_, _, ?_, rfl⟩
      exact fp_frm_zero_accrue _ _
        ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz

/-- feq/flt/fle . s/d : integer rd := 0 or 1, flags accrue. -/
theorem fp_step_fcmp (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (op : FcmpOp) (fmt : FFmt)
    (rd rs1 rs2 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.fcmp op fmt rd rs1 rs2, 4))
    (Hz : frm_zero fx.fp_csr) :
    ∃ (b : Bool) (cs' : BitVec 32), frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
        .MachineOk (mkstFP fx.fp_regs cs'
          (if bv_eqb rd 0 then regs
            else regupd regs rd (if b then BitVec.ofInt 64 1 else BitVec.ofInt 64 0))
          (v_addi pc 4) mem rom) := by
  fp_pipeline Hf, He, Hd
  cases fmt <;> cases op
  all_goals simp only [interp_eff_accesses, drop_access_report, mkAccessReport, reduceIte,
    ite_eq_left, Bool.false_eq_true, w1, w0]
  all_goals
    by_cases h1 : is_x0 rd
    · simp only [h1, bv_eqb0_is_x0, ite_true, ite_false, reduceIte, Bool.false_eq_true] at ⊢
      refine ⟨false, _, ?_, rfl⟩
      exact fp_frm_zero_accrue _ _
        ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz
    · simp only [h1, bv_eqb0_is_x0, ite_true, ite_false, reduceIte, Bool.false_eq_true] at ⊢
      refine ⟨_, _, ?_, rfl⟩
      exact fp_frm_zero_accrue _ _
        ⟨(fp_fflags_bits_range _).1, (fp_fflags_bits_range _).2⟩ Hz

/- =====================================================================
   The two CSR instructions of the binary
   ===================================================================== -/

/-- frrm rd (= csrrs rd, frm, x0): reads fcsr[7:5] = 0, writes nothing. -/
theorem fp_step_frrm (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.csr .RS rd 0 (BitVec.ofInt 12 2), 4))
    (Hz : frm_zero fx.fp_csr) :
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      .MachineOk (@mkst fx (if bv_eqb rd 0 then regs
        else regupd regs rd (BitVec.ofInt 64 0)) (v_addi pc 4) mem rom) := by
  have hz := slice_get_zero_of_frm_zero fx.fp_csr Hz
  have hw : csr_write_illegal false (BitVec.ofInt 12 2) = false := by decide
  have hsl : csr_slice (BitVec.ofInt 12 2) = some (5, 3) := by decide
  have hz64 : (BitVec.ofInt 64 0 : word) = 0 := by decide
  fp_pipeline Hf, He, Hd
  by_cases h1 : is_x0 rd <;>
    simp only [h1, hz, hw, hsl, hz64, is_x0_0, exec_csr, with_fcsr, rset, with_regs, with_pc,
      interp_eff_accesses, drop_access_report, mkAccessReport, ite_true, ite_false, reduceIte,
      Bool.not_true, Bool.false_eq_true, ite_eq_left, bvmapSet, bvmap_set, w0, reg_get, mkst] at ⊢

/-- csrsi fflags, uimm (= csrrsi x0, fflags, uimm): sets flag bits only. -/
theorem fp_step_csrsi_fflags (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (uimm : BitVec 5)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.csrI .RS 0 uimm (BitVec.ofInt 12 1), 4))
    (Hz : frm_zero fx.fp_csr) :
    ∃ cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
        .MachineOk (mkstFP fx.fp_regs cs' regs (v_addi pc 4) mem rom) := by
  have hw : csr_write_illegal false (BitVec.ofInt 12 1) = false := by decide
  have hsl : csr_slice (BitVec.ofInt 12 1) = some (0, 5) := by decide
  by_cases hu : (uimm.toNat == 0) = true
  · refine ⟨fx.fp_csr, Hz, ?_⟩
    fp_pipeline Hf, He, Hd
    simp only [hu, hw, hsl, is_x0_0, exec_csr, with_fcsr, rset, with_regs, with_pc,
      interp_eff_accesses, drop_access_report, mkAccessReport, ite_true, ite_false, reduceIte,
      Bool.not_true, Bool.false_eq_true, ite_eq_left, bvmapSet, bvmap_set, w0, reg_get, mkst] at ⊢
  · have hu' : (uimm.toNat == 0) = false := by
      cases h : uimm.toNat == 0 with
      | false => rfl
      | true => simp_all
    refine ⟨slice_set fx.fp_csr 0 5 (slice_get fx.fp_csr 0 5 ||| zext 64 uimm), ?_, ?_⟩
    · exact fp_frm_zero_slice0_5 _ _ Hz
    · have hw2 : csr_write_illegal true (BitVec.ofInt 12 1) = false := by decide
      fp_pipeline Hf, He, Hd
      simp only [hu', hw2, hsl, is_x0_0, Bool.not_false, exec_csr, with_fcsr, rset, with_regs, with_pc,
        interp_eff_accesses, drop_access_report, mkAccessReport, ite_true, ite_false, reduceIte,
        Bool.not_true, Bool.false_eq_true, ite_eq_left, bvmapSet, bvmap_set, w0, reg_get, mkst] at ⊢

end WithFP

/-! ## Sanity checks

    The decidable definitions above, evaluated (this tree's `vm_compute;
    reflexivity` → `by decide` convention). -/

/-- The entry fcsr is `frm_zero` (fcsr[7:5] = 0). -/
example : frm_zero (BitVec.ofInt 32 0) := by unfold frm_zero; decide

/-- A set frm field is NOT `frm_zero`. -/
example : ¬ frm_zero (BitVec.ofInt 32 32) := by unfold frm_zero; decide

/-- With fcsr[7:5] = 0 the frm slice reads as 0. -/
example : slice_get (BitVec.ofInt 32 0) 5 3 = 0 := by decide

/-- The frm slice of a full fcsr reads back its 3 bits. -/
example : slice_get (BitVec.ofInt 32 224) 5 3 = 7 := by decide

/-- The two CSR addresses this file names: fflags = 1, frm = 2. -/
example : csr_slice (BitVec.ofInt 12 1) = some (0, 5) := by decide

example : csr_slice (BitVec.ofInt 12 2) = some (5, 3) := by decide

/-- The post-state constructor reads back what it was given. -/
example :
    (mkstFP bvmap_empty (BitVec.ofInt 32 0) bvmap_empty 0 (fun _ : word => none)
      (fun _ : word => none)).ms_fcsr = BitVec.ofInt 32 0 := rfl

end LinuxSem.Common.FPSteps
