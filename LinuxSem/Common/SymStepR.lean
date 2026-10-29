/-
  * Common.SymStepR — per-instruction step lemmas over a machine state with an
    ARBITRARY LR/SC reservation ([mkstR]), including the RV64A instructions
    [lr.w/d], [sc.w/d] (success path) and the AMOs.

    Written for the reservation-tracking extension of the reflective symbolic
    executor [AxSymExec3] (soundness in [AxSymExec3Sound]).

    [PropExec.mkst regs pc mem rom] PINS [ms_resv := none]; it is, by
    definition, CONVERTIBLE with [mkstR regs pc mem rom none] (both unfold to
    the same record), so every lemma below specialises to the [mkst]-lemma of
    the same name in [PropExec]/[SeqExec].  Nothing here changes [PropExec].

    Reservation behaviour (transcribed from [Sem.exec], proved by
    computation through [RiscvSemantics.step], never assumed):
      - integer ALU / branches / jumps / fences / loads: reservation unchanged;
      - [Store]: [resv_inval_w rv a] — a store to EXACTLY the reserved
        address kills the reservation ([Sem.inval_resv]);
      - [Lr]: reservation := [some a];
      - [Sc] with reservation [some a] on its own address: store, [rd := 0],
        reservation := [none] (the failing [Sc] is not covered: the
        symbolic executor never needs it);
      - [Amo]: load, store [amo_val], [rd := old], reservation as for a store.
    All three atomics FAULT on a misaligned address ([Sem.amo_aligned]);
    the lemmas take the alignment as a hypothesis.

    The vocabulary mapping is [PropExec]'s : `Z` → [Int], `bv_unsigned x` → `(x.toNat : Int)`,
    `bv_signed x` → `x.toInt`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_extract lo len w` → `bits lo len w`, `Z_to_le_bytes` unchanged,
    `Z.eqb (bv_unsigned r) (bv_unsigned a)` → `r.toNat == a.toNat` (the
    spelling [Sem.inval_resv] itself uses, so the reservation lemmas reduce by
    conversion), `nat` → [Nat], and the section variables are explicit [segs].
    The  `Ltac stepR_pipeline` is the `stepR_pipeline` tactic macro
    below. 0)%Z) with false`,
    stated as a lemma because Lean's [Nat.beq] and [Int] `Z.eqb` differ
    syntactically) and [resv_inval_w_none]/[resv_inval_w_some] .
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec

set_option autoImplicit false
-- Same rationale as `PropExec`/`SeqExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.SymStepR

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec

variable [fx : FPState]

/-! ## The state shape: [mkst] with the reservation exposed -/

/-- The state shape the lemmas below are stated at: [mkst] with the LR/SC
    reservation exposed as a parameter.

    as in [PropExec.mkst], the FP register file and the fcsr come
    from the ambient [FPState] instance rather than being pinned to the
    entry-state values, so the lemmas are polymorphic in the (integer- and
    load/store-preserved) FP state.   pins them to `bvmap_empty`/
    `0`, which is the [fx0] instance. -/
def mkstR (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (rv : Option word) : machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := none, ms_resv := rv, ms_fcsr := fx.fp_csr,
    ms_mem := mem, ms_rom := rom }

/-- With no reservation, [mkstR] IS [mkst] — definitionally. -/
theorem mkstR_None (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    mkstR regs pc mem rom none = mkst regs pc mem rom := rfl

/-- [mkstR] pins the pending-syscall slot, as [mkst] does. -/
theorem mkstR_svc (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (rv : Option word) : (mkstR regs pc mem rom rv).ms_svc_pending = none := rfl

/-- What a store / AMO to address [a] does to the reservation: a store to
    EXACTLY the reserved address kills the reservation, anything else leaves
    it alone ([Sem.inval_resv]).
-/
def resv_inval_w (rv : Option word) (a : word) : Option word :=
  match rv with
  | some r => if r.toNat == a.toNat then none else rv
  | none => none

/-- The [none] branch of [resv_inval_w]. -/
theorem resv_inval_w_none (a : word) : resv_inval_w none a = none := rfl

/-- The reserved-address branch: an exact match clears, anything else keeps. -/
theorem resv_inval_w_some (r a : word) :
    resv_inval_w (some r) a = if r.toNat == a.toNat then none else some r := rfl

/-- The value a load writes back, per width/sign, as a function of the bytes
    read.  It is exactly the value the ISA layer's [Sem.load_val] hands its
    continuation. -/
def load_result (sz : MSize) (sx : Bool) (bs : List byte) : word :=
  match sz with
  | .SZ1 => if sx then sext 64 (bits 0 8 (le_bytes_to_word bs))
            else zext 64 (bits 0 8 (le_bytes_to_word bs))
  | .SZ2 => if sx then sext 64 (bits 0 16 (le_bytes_to_word bs))
            else zext 64 (bits 0 16 (le_bytes_to_word bs))
  | .SZ4 => if sx then sext 64 (bits 0 32 (le_bytes_to_word bs))
            else zext 64 (bits 0 32 (le_bytes_to_word bs))
  | .SZ8 => bits 0 64 (le_bytes_to_word bs)

/-- The sign-extension flag a load of width [sz] actually applies: `SZ8` has
    no extension to apply, so the flag is moot there. -/
def eff_sx (sz : MSize) (sx : Bool) : Bool :=
  match sz with | .SZ8 => false | _ => sx

/-- Size in bytes of a load/store.

    [Nat]-valued, because it is the width argument of [rdn] and
    [store_ok]; the ISA layer's `Riscv.msizeBytes` is the same function at
    [Int] (its `SZ` mirrors [Sem.amo_bytes]'s `Int`). -/
def msize_bytes (sz : MSize) : Nat :=
  match sz with | .SZ1 => 1 | .SZ2 => 2 | .SZ4 => 4 | .SZ8 => 8

/-- Atomic widths as load/store widths. -/
def amo_msize (wd : AWidth) : MSize := match wd with | .W => .SZ4 | .D => .SZ8

/-- Atomic widths in bytes. -/
def amo_nbytes (wd : AWidth) : Nat := match wd with | .W => 4 | .D => 8

/-- The bytes an AMO writes: [amo_val] at the operand width. -/
def amo_store_bytes (op : AmoOp) (wd : AWidth) (bs : List byte) (src : word) :
    List byte :=
  match wd with
  | .W => Z_to_le_bytes 4 ((amo_val op (bits 0 32 (le_bytes_to_word bs)) (low32 src)).toNat : Int)
  | .D => Z_to_le_bytes 8 ((amo_val op (bits 0 64 (le_bytes_to_word bs)) src).toNat : Int)

/-! -/
open Lean Parser Tactic in
macro "stepR_pipeline" hf:simpLemma "," he:simpLemma "," hd:simpLemma : tactic =>
  `(tactic|
    simp only [mkstR, RiscvSemantics.step, RiscvSemantics.step_accesses, ms_pc, $hf, $he, $hd,
      decode_exec_accesses, drop_access_report, exec, interp_eff_accesses, mkAccessReport,
      rset, rget, with_pc, with_regs, with_resv, with_fcsr, reg_get, bvmapSet, bvmap_set,
      mkst, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, w0, Bool.false_eq_true, reduceIte,
      ite_true, ite_false])

/-! ## bridge helpers -/

/--  inline `change (negb (0 =? -/
theorem amo_aligned_of_mod (wd : AWidth) (a : word)
    (h : ((a.toNat : Int) % amo_bytes wd) = 0) : amo_aligned wd a = true := by
  have key : ∀ (k : Nat), (amo_bytes wd : Int) = (k : Int) → a.toNat % k = 0 := by
    intro k hk
    have h1 : ((a.toNat % k : Nat) : Int) = 0 := by
      rw [Int.natCast_emod]
      simpa [hk] using h
    exact Int.natCast_eq_zero.mp h1
  cases wd with
  | W => simp [amo_aligned, amo_bytes, key 4 (by decide)]
  | D => simp [amo_aligned, amo_bytes, key 8 (by decide)]

/-- [inval_resv] leaves the register file alone.   -/
theorem inval_resv_regs (a : word) (c : core) : (inval_resv a c).c_regs = c.c_regs := by
  cases c with
  | mk regs fregs pc fcsr resv =>
    unfold inval_resv
    cases resv with
    | none => rfl
    | some r => by_cases h : r.toNat == a.toNat <;> simp [h, with_resv]

/-- [inval_resv] leaves the FP register file alone. -/
theorem inval_resv_fregs (a : word) (c : core) : (inval_resv a c).c_fregs = c.c_fregs := by
  cases c with
  | mk regs fregs pc fcsr resv =>
    unfold inval_resv
    cases resv with
    | none => rfl
    | some r => by_cases h : r.toNat == a.toNat <;> simp [h, with_resv]

/-- [inval_resv] leaves the pc alone. -/
theorem inval_resv_pc (a : word) (c : core) : (inval_resv a c).c_pc = c.c_pc := by
  cases c with
  | mk regs fregs pc fcsr resv =>
    unfold inval_resv
    cases resv with
    | none => rfl
    | some r => by_cases h : r.toNat == a.toNat <;> simp [h, with_resv]

/-- [inval_resv] leaves the fcsr alone. -/
theorem inval_resv_fcsr (a : word) (c : core) : (inval_resv a c).c_fcsr = c.c_fcsr := by
  cases c with
  | mk regs fregs pc fcsr resv =>
    unfold inval_resv
    cases resv with
    | none => rfl
    | some r => by_cases h : r.toNat == a.toNat <;> simp [h, with_resv]

/-- what [inval_resv] does to the reservation itself — the
    [resv_inval_w] of the pre-state's reservation. -/
theorem inval_resv_resv (a : word) (c : core) :
    (inval_resv a c).c_resv = resv_inval_w c.c_resv a := by
  cases c with
  | mk regs fregs pc fcsr resv =>
    unfold inval_resv resv_inval_w
    cases resv with
    | none => rfl
    | some r => by_cases h : r.toNat == a.toNat <;> simp [h, with_resv]

/- =================================================================
   Integer instructions: the reservation passes through
   ================================================================= -/

/-- `OP-IMM` (`addi`/`slti`/`sltiu`/`xori`/`ori`/`andi`): the ALU result into
    `rd` unless `rd = x0`; an integer instruction, so the reservation passes
    through unchanged. -/
theorem stepR_opimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AluOp)
    (rd rs : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm op rd rs imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `OP-IMM` shift (`slli`/`srli`/`srai`): the 6-bit `shamt` zero-extended to the
    word; reservation unchanged. -/
theorem stepR_shiftimm_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AluOp)
    (rd rs : reg) (sh : BitVec 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `OP` (`add`/`sub`/`slt`/`sltu`/`and`/`or`/`xor`/`sll`/`srl`/`sra`):
    register-register ALU, reservation unchanged. -/
theorem stepR_op_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AluOp)
    (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/-- `ADDIW`: the ALU op is fixed to `ADD` by the decoder; the 32-bit sum is
    sign-extended back to the word.  Reservation unchanged. -/
theorem stepR_opimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (rd rs : reg)
    (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.opImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm))))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `OP-IMM-32` shift (`slliw`/`srliw`/`sraiw`): the 5-bit `shamt` is
    zero-extended to 32 bits before the 32-bit shift.  Reservation unchanged. -/
theorem stepR_shiftimm32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AluOp)
    (rd rs : reg) (sh : BitVec 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.shiftImm32 op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
    simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get]

/-- `OP-32` (`addw`/`subw`/`sllw`/`srlw`/`sraw`): both operands truncated to 32
    bits, the result sign-extended back.  Reservation unchanged. -/
theorem stepR_op32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AluOp)
    (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.op32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd
          (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/-- `M` (`mul`/`mulh`/`mulhsu`/`mulhu`/`div`/`divu`/`rem`/`remu`): the
    reservation passes through. -/
theorem stepR_mul_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : MulOp)
    (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/-- `M` at 32 bits (`mulw`/`divw`/`divuw`/`remw`/`remuw`): operands truncated to
    32 bits before the operation, result sign-extended back. -/
theorem stepR_mul32_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : MulOp)
    (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.mul32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd
          (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1 <;> by_cases h3 : is_x0 rs2 <;>
    simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get]

/-- `lui`: `rd := sign_extend (imm << 12)`, pc advances.  Reservation
    unchanged. -/
theorem stepR_lui (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (rd : reg)
    (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.lui rd imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (v_lui (zshiftl imm.toInt 12)))
        (v_addi pc 4) mem rom rv) := by
  have hb : sext 64 (imm ++ (0#12)) = v_lui (zshiftl imm.toInt 12) := b_lui imm
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

/-- `auipc`: `rd := pc + sign_extend (imm << 12)`, pc advances.  Reservation
    unchanged. -/
theorem stepR_auipc (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (rd : reg)
    (imm : BitVec 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.auipc rd imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (v_auipc pc (zshiftl imm.toInt 12)))
        (v_addi pc 4) mem rom rv) := by
  have hb : pc + sext 64 (imm ++ (0#12)) = v_auipc pc (zshiftl imm.toInt 12) :=
    b_auipc pc imm
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, BitVec.ofNat_eq_ofNat]

/-- `jal` with a live link register: `rd := pc + 4`, jump to `pc + sign_extend
    imm`.  Reservation unchanged. -/
theorem stepR_jal_link (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (rd : reg)
    (imm : BitVec 21)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (btgt pc imm.toInt) mem rom rv) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;> simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get]

/-- `jalr`: `rd := pc + 4` (unless x0), jump to `(rs1 + sign_extend imm) & ~1`
    ([v_jalr]); the ISA model has no alignment side condition.  Reservation
    unchanged. -/
theorem stepR_jalr (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (rd rs1 : reg)
    (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (v_jalr (getr regs rs1) imm.toInt) mem rom rv) := by
  have hb : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide : 12 ≤ 64)
  have hj : (getr regs rs1 + sext 64 imm) &&& ~~~(1 : word)
      = v_jalr (getr regs rs1) imm.toInt := b_jalr _ imm
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, bv_eqb0_is_x0, w1, reg_get, w0] at hb hj ⊢
  by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs1
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, w0, w1, Bool.false_eq_true,
    reg_get] at hb hj ⊢
  all_goals rw [hj]
  all_goals simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, Nat.zero_add]

/-- A taken branch: pc := [btgt], no register written, reservation unchanged.
     -/
theorem stepR_branch_tk_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (c : BranchCond)
    (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR regs (btgt pc imm.toInt) mem rom rv) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  simp only [getr, bv_eqb0_is_x0] at Hc
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, hb, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

/-- The fall-through side of a branch: pc advances by 4, reservation unchanged. -/
theorem stepR_branch_ft_gen (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (c : BranchCond)
    (rs1 rs2 : reg) (imm : BitVec 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  simp only [getr, bv_eqb0_is_x0] at Hc
  stepR_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rs1 <;> by_cases h2 : is_x0 rs2
  all_goals simp only [h1, h2, ite_true, ite_false, reduceIte, BitVec.ofNat_eq_ofNat, reg_get,
    bvmapGet, bvmap_get, w0, Bool.false_eq_true] at Hc
  all_goals simp [h1, h2, Hc, BitVec.ofNat_eq_ofNat, reg_get, bvmapGet, bvmap_get, w0]

/-- `fence`: a single hart, so the model makes it a no-op; reservation unchanged. -/
theorem stepR_fence (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32)
    (a b c : BitVec 4) (d e : reg) (Hfetch : fetch_word segs pc = some w)
    (Hecall : is_ecall w = false) (Hdecode : decodeAny w = some (Instr.fence a b c d e, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode

/-- `fence.i`: likewise a no-op in this model; reservation unchanged. -/
theorem stepR_fencei (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (a b : reg)
    (c : BitVec 12) (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.fenceI a b c, 4)) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  stepR_pipeline Hfetch, Hecall, Hdecode

/- =================================================================
   Loads and stores
   ================================================================= -/

theorem stepR_load (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (sz : MSize)
    (sx : Bool) (rd rs : reg) (imm : BitVec 12) (bs : List byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.load sz sx rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) imm.toInt) (msize_bytes sz) = some bs) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (load_result sz sx bs)) (v_addi pc 4) mem rom rv) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) (msize_bytes sz) = some bs := by
    rw [hba, ov_rdn]; exact Hread
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr] at hba hov ⊢
  simp only [hba] at hov ⊢
  cases sz <;> simp only [msize_bytes] at hov
  all_goals
    simp only [hov, width_bytes, load_val, load_result, interp_eff_accesses, drop_access_report,
      mkAccessReport, mkstR, ite_eq_left, reduceIte] at ⊢
  all_goals
    by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;> by_cases h3 : sx <;>
      simp [h1, h2, h3, bvmapSet, bvmap_set, w0, reg_get, regupd, getr, v_addi, msize_bytes]

/-- Store of any width, value exposed, reservation invalidated on an exact
    address match. -/
theorem stepR_store (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (sz : MSize)
    (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store sz rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) (msize_bytes sz) = true) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes (msize_bytes sz) (getr regs rs2))) rom
        (resv_inval_w rv (v_addi (getr regs rs1) imm.toInt))) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) (msize_bytes sz) = true := by
    rw [hba]; exact Hok
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr] at hba hok ⊢
  simp only [hba] at hok ⊢
  cases sz <;> simp only [msize_bytes] at hok
  all_goals
    simp only [hok, width_bytes, store_val, interp_eff_accesses, drop_access_report,
      mkAccessReport, write_to_mem_wbytes, store_bytes_low8, store_bytes_low16,
      store_bytes_low32, inval_resv_regs, inval_resv_fregs, inval_resv_pc, inval_resv_fcsr,
      inval_resv_resv, resv_inval_w, mkstR, ite_eq_left, reduceIte] at ⊢
  all_goals
    by_cases h1 : is_x0 rs2 <;>
      simp [h1, bvmapSet, bvmap_set, w0, reg_get, regupd, getr, v_addi, msize_bytes]
  all_goals
    cases rv <;> rfl

/- =================================================================
   A extension
   ================================================================= -/

/-- LR: load (like [lw]/[ld]) and reserve the address. -/
theorem stepR_lr (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (wd : AWidth)
    (aq rl : Bool) (rd rs : reg) (bs : List byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.lr wd aq rl rd rs, 4))
    (Hal : ((getr regs rs).toNat : Int) % amo_bytes wd = 0)
    (Hread : rdn segs mem (getr regs rs) (amo_nbytes wd) = some bs) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (load_result (amo_msize wd) true bs))
        (v_addi pc 4) mem rom (some (getr regs rs))) := by
  have hal : amo_aligned wd (getr regs rs) = true := amo_aligned_of_mod wd _ Hal
  have hov : ov_read_bytes segs mem (getr regs rs) (amo_nbytes wd) = some bs := by
    rw [ov_rdn]; exact Hread
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr] at hal hov ⊢
  rw [hal] at ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_eq_left, reduceIte] at ⊢
  cases wd <;> simp only [amo_nbytes] at hov
  all_goals
    simp only [hov, amo_msize, amo_nbytes, amo_bytes, width_bytes, load_val, load_result,
      interp_eff_accesses, drop_access_report, mkAccessReport, mkstR, ite_eq_left, reduceIte] at ⊢
  all_goals
    by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs <;>
      simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, regupd, getr, v_addi, amo_nbytes,
        amo_msize, word_to_le_bytes]

/-- SC, success path: the reservation is on the SC's own address. -/
theorem stepR_sc_ok (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (wd : AWidth) (aq rl : Bool)
    (rd rs1 rs2 : reg) (r : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.sc wd aq rl rd rs1 rs2, 4))
    (Hal : ((getr regs rs1).toNat : Int) % amo_bytes wd = 0)
    (Hr : r = getr regs rs1)
    (Hok : store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true) :
    RiscvSemantics.step segs (mkstR regs pc mem rom (some r)) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (BitVec.ofInt 64 0))
        (v_addi pc 4)
        (wbytes mem (getr regs rs1)
          (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom none) := by
  have hal : amo_aligned wd (getr regs rs1) = true := amo_aligned_of_mod wd _ Hal
  subst Hr
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr] at hal Hok ⊢
  rw [hal] at ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_eq_left, reduceIte, beq_self_eq_true] at ⊢
  cases wd <;> simp only [amo_nbytes] at Hok
  all_goals
    simp only [Hok, amo_msize, amo_nbytes, amo_bytes, width_bytes, store_val,
      store_bytes_low32, interp_eff_accesses, drop_access_report, mkAccessReport,
      write_to_mem_wbytes, mkstR, ite_eq_left, reduceIte] at ⊢
  all_goals
    by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs2 <;>
      simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, regupd, getr, v_addi, amo_nbytes,
        amo_msize, word_to_le_bytes]

/-- AMO: load the old value, store [amo_val op old src], [rd := old]
    (sign-extended for .w); reservation invalidated like a store. -/
theorem stepR_amo (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (rv : Option word) (w : BitVec 32) (op : AmoOp)
    (wd : AWidth) (aq rl : Bool) (rd rs1 rs2 : reg) (bs : List byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.amo op wd aq rl rd rs1 rs2, 4))
    (Hal : ((getr regs rs1).toNat : Int) % amo_bytes wd = 0)
    (Hread : rdn segs mem (getr regs rs1) (amo_nbytes wd) = some bs)
    (Hok : store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true) :
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
      .MachineOk (mkstR (if bv_eqb rd 0 then regs
        else regupd regs rd (load_result (amo_msize wd) true bs))
        (v_addi pc 4)
        (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2)))
        rom (resv_inval_w rv (getr regs rs1))) := by
  have hal : amo_aligned wd (getr regs rs1) = true := amo_aligned_of_mod wd _ Hal
  have hov : ov_read_bytes segs mem (getr regs rs1) (amo_nbytes wd) = some bs := by
    rw [ov_rdn]; exact Hread
  stepR_pipeline Hfetch, Hecall, Hdecode
  simp only [getr, rget, reg_get, bv_eqb0_is_x0, w0, with_pc, with_regs, with_resv,
    with_fcsr] at hal hov Hok ⊢
  rw [hal] at ⊢
  simp only [Bool.not_true, Bool.false_eq_true, ite_eq_left, reduceIte] at ⊢
  cases wd <;> simp only [amo_nbytes] at hov Hok
  all_goals
    simp only [hov, Hok, amo_msize, amo_nbytes, amo_bytes, amo_store_bytes, width_bytes,
      load_val, load_result, interp_eff_accesses, drop_access_report, mkAccessReport,
      write_to_mem_wbytes, inval_resv_regs, inval_resv_fregs, inval_resv_pc,
      inval_resv_fcsr, inval_resv_resv, resv_inval_w, mkstR, ite_eq_left, reduceIte] at ⊢
  all_goals
    cases rv <;>
    by_cases h1 : is_x0 rd <;> by_cases h2 : is_x0 rs2 <;>
      simp [h1, h2, bvmapSet, bvmap_set, w0, reg_get, regupd, getr, v_addi, amo_nbytes,
        amo_msize, word_to_le_bytes, inval_resv_regs, inval_resv_fregs, inval_resv_pc,
        inval_resv_fcsr, inval_resv_resv, resv_inval_w, with_resv]

/-! ## Sanity checks

    The decidable definitions above, evaluated. -/

theorem msize_bytes_vals :
    (msize_bytes .SZ1, msize_bytes .SZ2, msize_bytes .SZ4, msize_bytes .SZ8) =
      (1, 2, 4, 8) := by decide

theorem amo_nbytes_vals : (amo_nbytes .W, amo_nbytes .D) = (4, 8) := by decide

theorem amo_msize_vals : (amo_msize .W, amo_msize .D) = (MSize.SZ4, MSize.SZ8) := by decide

theorem eff_sx_vals :
    (eff_sx .SZ8 true, eff_sx .SZ4 true, eff_sx .SZ8 false) = (false, true, false) := by decide

theorem resv_inval_w_hit : resv_inval_w (some (7 : word)) 7 = none := by decide

theorem resv_inval_w_miss : resv_inval_w (some (7 : word)) 8 = some 7 := by decide

theorem load_result_ld :
    load_result .SZ8 false [1, 2] = bits 0 64 (le_bytes_to_word [1, 2]) := by decide

theorem load_result_lb :
    load_result .SZ1 true [255] = BitVec.ofInt 64 (-1) := by decide

theorem amo_store_bytes_len :
    (amo_store_bytes .ADD .W [0, 0, 0, 0] 0).length = 4 ∧
      (amo_store_bytes .SWAP .D (List.replicate 8 0) 0).length = 8 := by decide

end LinuxSem.Common.SymStepR
