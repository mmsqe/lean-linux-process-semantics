/-
  * Common.SeqExec — additional image-INDEPENDENT symbolic-execution
    infrastructure for compiled (C / Zig) binaries with real stack frames.

  Machine values are `word = BitVec 64`, register indices are `reg = BitVec 5`,
  bytes are `byte = BitVec 8`.  Purely additive over [Common.PropExec] /
  [Common.CatSim] / [Common.CatExec].  The cat-argv-era binaries
  were flat assembly: no calls, no stores, no unsigned branches.
  Compiled binaries need:

  - step lemmas for the calling convention: [Jal] with a live link
    register, [Jalr] (calls and [ret]);
  - a VALUE-precise store-double lemma [step_sd_val] (CatExec's
    [step_sd] leaves the stored bytes existential, which is useless
    when the binary later reloads the slot — e.g. the saved [ra]);
  - read-back theory for [wbytes] ([rdn_wbytes_hit]);
  - a [to_wexit] write constructor that exposes the syscall's actual
    return value ([tw_write_ret]) for binaries that test it, and an
    exit constructor for arbitrary small exit codes ([tw_exit_coden]);
  - generic argv-pointer bounds ([argv_ptr_bounds]) usable by any
    proof.

  Conventions: decode hypotheses are over [DecodeC.decode_any]; there
  are no [align4]/[align4_jalr] side conditions (the ISA model has no
  branch/jump alignment check); "small" value lemmas state
  [bv_unsigned]-level equations with [Z] guards; the stored bytes of
  [Sd]/[Sb] are the exact [word_to_le_bytes] lists by conversion.

  NOTES.

  - `Section WithFP`'s `Context {fx : FPState}` becomes the ambient
    `variable [fx : FPState]` of the same name, exactly as `PropExec`,
    `CatExec` and `MmapSim` do; the section's `fp_regs`/`fp_csr` are
    `fx.fp_regs`/`fx.fp_csr`.
  - `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `bv_signed w` → `w.toInt`,
    `bv_eqb a b` → Riscv.Prelude's `bv_eqb`, `bv_and` → `&&&`,
    `word_to_le_bytes n v` → `LinuxProcessSem.RiscvSemantics.word_to_le_bytes`
    (definitionally `Z_to_le_bytes n (v.toNat : Int)`), `firstn`/`skipn` →
    `List.take`/`List.drop`, `lia`/`nia` → `omega`, `vm_compute; reflexivity`
    → `decide`, `M_DIVU`/`M_REMU` → `MulOp.DIVU`/`MulOp.REMU`,
    `ALU_*` → `AluOp.*`, `Jal`/`Jalr`/`Lui`/`Auipc`/`Store`/`OpImm`/`Op`/
    `ShiftImm`/`Mul` → `Instr.jal`/… (this tree's lowercase constructors).
  - `Reg`/`reg` indices: `getr regs 17` etc.   - Store specifications: `CatExec.step_sd` is the model for the [wbytes]
    existential shape; the VALUE-precise variants below expose the exact
    `word_to_le_bytes` list, and the narrow-width ones ([SZ1]/[SZ2]/[SZ4])
    go through the truncation identities [store_bytes_low16]/
    [store_bytes_low32], because the
    interpreter truncates the stored value BEFORE serialising it.
 None of
    them changes an  statement: every  declaration below has
    the type, modulo the [Z]/[Int] and `nth`/`getD` conventions
    listed above.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.ExitSim

set_option autoImplicit false
-- Same rationale as `PropExec`/`CatExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.SeqExec

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.ExitSim

section WithFP1

variable [fx : FPState]

/- =================================================================
   Value shapes (exact normal forms, like PropExec's)
   ================================================================= -/

/-- The jalr target: (rs1 + imm) with bit 0 cleared.  Definitionally
    equal to [PropExec.jalr_tgt], so [step_jalr] composes with
    [step_jalr_gen]'s conclusion. -/
def v_jalr (x : word) (imm : Int) : word := BitVec.ofInt 64 (jalr_tgtZ x imm)

/- =================================================================
   Per-instruction step lemmas
   ================================================================= -/

/-- Jal with a live link register: rd := pc + 4, jump to [btgt].
    (No [align4] hypothesis: the ISA model has no alignment check.) -/
theorem step_jal_link (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 21)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jal rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (btgt pc imm.toInt) mem rom) := by
  have hb : pc + sext 64 imm = btgt pc imm.toInt := b_addsext pc imm (by decide)
  step_pipeline Hfetch, Hecall, Hdecode
  by_cases h1 : is_x0 rd <;>
    simp [h1, hb, bvmapSet, bvmap_set, w0, reg_get, b_npc4]

/-- Jalr: rd := pc + 4, jump to (rs1 + imm) & ~1.  Restatement of
    [PropExec.step_jalr_gen] with the [v_jalr] value shape. -/
theorem step_jalr (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
        (v_jalr (getr regs rs1) imm.toInt) mem rom) := by
  have := step_jalr_gen segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode
  simpa only [v_jalr, jalr_tgt] using this

end WithFP1

section WithFP2

variable [fx : FPState]

/- =================================================================
   Value-precise store double
   ================================================================= -/

/-- Store double, stored VALUE exposed: mem := wbytes mem (rs1+imm)
    (word_to_le_bytes 8 rs2), so a later reload sees the exact bytes. -/
theorem step_sd_val (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ8 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 8 (getr regs rs2))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 8 = true := by
    rw [hba]; exact Hok
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, word_to_le_bytes, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [step_sd_val] with the store address and value pre-normalized, so the
    chained machine state stays in [sp - k]-literal form. -/
theorem step_sd_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.store .SZ8 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hok : store_ok segs mem a 8 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  rw [step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd]
  · simp only [Ha, Hv]
  · rw [Ha]; exact Hok

/- =================================================================
   [_at] forms of the value-writing step lemmas

   Each is a ~3-line corollary of the corresponding [PropExec.step_*]:
   the writeback value is pre-normalized so an evar step-chain stays flat.
   Without them, every ALU instruction in a long chain embeds
   [v_addi (getr <chain>) imm] in the written value — two references to
   the previous state per step — and normalizing the final state (e.g.
   splitting on accumulated register facts) explodes exponentially once
   the initial sp is symbolic.
   ================================================================= -/

/-- [step_addi] with the writeback value pre-normalized (the [addi]/[li]
    analogue of [step_sd_at]): the chained machine state stays flat. -/
theorem step_addi_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm .ADD rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_addi (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_addi segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_add] at a pre-normalized writeback. -/
theorem step_add_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op .ADD rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_add (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_sub] at a pre-normalized writeback. -/
theorem step_sub_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op .SUB rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_sub (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_lui] at a pre-normalized writeback. -/
theorem step_lui_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.lui rd imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_lui (zshiftl imm.toInt 12) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_lui segs regs pc mem rom w rd imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_auipc] at a pre-normalized writeback. -/
theorem step_auipc_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd : reg) (imm : BitVec 20) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.auipc rd imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_auipc pc (zshiftl imm.toInt 12) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_auipc segs regs pc mem rom w rd imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_addiw] at a pre-normalized writeback. -/
theorem step_addiw_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm32 rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_addiw (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_addiw segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_sltiu] at a pre-normalized writeback. -/
theorem step_sltiu_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm .SLTU rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_sltiu (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_xori] at a pre-normalized writeback. -/
theorem step_xori_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm .XOR rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_xori (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_xori segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_mul] at a pre-normalized writeback. -/
theorem step_mul_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul .MUL rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_mul (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_andi] at a pre-normalized writeback. -/
theorem step_andi_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm .AND rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_andi (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_andi segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_ori] at a pre-normalized writeback. -/
theorem step_ori_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.opImm .OR rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_ori (getr regs rs) imm.toInt = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_ori segs regs pc mem rom w rd rs imm Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_slli] at a pre-normalized writeback. -/
theorem step_slli_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.shiftImm .SLL rd rs sh, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_slli (getr regs rs) (sh.toNat : Int) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_slli segs regs pc mem rom w rd rs sh Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_srli] at a pre-normalized writeback. -/
theorem step_srli_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.shiftImm .SRL rd rs sh, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_srli (getr regs rs) (sh.toNat : Int) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_srli segs regs pc mem rom w rd rs sh Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [step_srai] at a pre-normalized writeback. -/
theorem step_srai_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (sh : BitVec 6)
    (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.shiftImm .SRA rd rs sh, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_srai (getr regs rs) (sh.toNat : Int) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_srai segs regs pc mem rom w rd rs sh Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

end WithFP2

section WithFP3

variable [fx : FPState]

/- =================================================================
   wbytes read-back
   ================================================================= -/

/-- the [n = 0] step of [rdn], definitionally. -/
theorem rdn_zero (segs : List Segment) (mem : word → Option byte) (a : word) :
    rdn segs mem a 0 = some [] := rfl

/-- the [n + 1] step of [rdn] at a byte the overlay
    supplies. -/
theorem rdn_succ (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat)
    (b : byte) (h : mem a = some b) :
    rdn segs mem a (n + 1) = (rdn segs mem (a + 1) n).bind (fun rest => some (b :: rest)) := by
  simp only [rdn, h]
  cases rdn segs mem (a + 1) n with
  | none => rfl
  | some rest => rfl

/-- NEW no-overflow hypothesis (the [wbytes]/[rdn] address walks are
    wrapping [bv] adds, mirroring [wbytes_below]/[rdn_ext]); trivially
    discharged downstream — stack addresses sit far below 2^64. -/
theorem rdn_wbytes_hit (segs : List Segment) (bs : List byte) :
    ∀ (m : word → Option byte) (a : word),
      (a.toNat : Int) + (bs.length : Int) ≤ ((2 ^ 64 : Nat) : Int) →
      rdn segs (wbytes m a bs) a bs.length = some bs := by
  induction bs with
  | nil => intro m a _; rfl
  | cons b rest ih =>
    intro m a Hnw
    have hlen : (b :: rest).length = rest.length + 1 := rfl
    rw [hlen]
    have hstep : wbytes m a (b :: rest)
        = wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) rest := rfl
    rw [hstep]
    cases rest with
    | nil =>
      -- the LAST write of the walk: [m'] reads [b] at [a] outright
      have hread : wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) [] a
          = some b := by
        simp only [wbytes, ite_eq_left (bv_eqb_refl a)]
      have hn : (([] : List byte).length + 1) = 0 + 1 := rfl
      rw [hn, rdn_succ segs _ a 0 b hread, rdn_zero]
      rfl
    | cons b' rest' =>
      -- an earlier write: [wbytes_below] reads [m'] at [a] directly
      have hlen2 : ((b :: b' :: rest').length : Int) = ((b' :: rest').length : Int) + 1 := by
        rw [List.length_cons, Int.natCast_add, Int.natCast_one]
      -- the walk cannot wrap: the store's second byte sits inside the bound
      have ha1 : (a.toNat : Int) + 1 < ((2 ^ 64 : Nat) : Int) := by
        have h := Hnw
        rw [hlen2] at h
        have h0 : (1 : Int) ≤ ((b' :: rest').length : Int) := by
          have hpos : 1 ≤ (b' :: rest').length := by simp
          exact Int.ofNat_le.mpr hpos
        omega
      have h1 : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := u_add1 a ha1
      have hbnd : ((a + 1).toNat : Int) + ((b' :: rest').length : Int)
          ≤ ((2 ^ 64 : Nat) : Int) := by
        have h := Hnw
        rw [hlen2] at h
        rw [h1]
        omega
      have hlt : (a.toNat : Int) < ((a + 1).toNat : Int) := by
        rw [h1]; omega
      have hread : wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1)
            (b' :: rest') a = some b := by
        rw [wbytes_below (b' :: rest') _ (a + 1) a hbnd hlt, ite_eq_left (bv_eqb_refl a)]
      rw [rdn_succ segs _ a (b' :: rest').length b hread, ih _ (a + 1) hbnd]
      rfl

/-- Read a full 8-byte slot back. -/
theorem rdn_wbytes_hit8 (segs : List Segment) (m : word → Option byte) (a v : word)
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8 = some (word_to_le_bytes 8 v) := by
  have H := rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a (by
    rw [length_N_to_le_bytes]; exact Hnw)
  rwa [length_N_to_le_bytes] at H

/-- Hypothesis-free: the [bv] bound is enforced by the type. -/
theorem bytes_le_to_Z_8 (v : word) : bytes_le_to_Z (word_to_le_bytes 8 v) = (v.toNat : Int) := by
  rw [bytes_le_N 8 v, show 8 * 8 = 64 from rfl,
    Nat.mod_eq_of_lt (by have := v.isLt; omega)]

/- =================================================================
   Value simplification
   ================================================================= -/

/-- Definitional: [c_ltu] IS the unsigned [Z.ltb]; no range hypotheses
    are needed, since the [bv] bounds are enforced by the type. -/
theorem c_ltu_ltb (x y : word) : c_ltu x y = decide (x.toNat < y.toNat) := by
  unfold c_ltu bv_ltu
  rfl

theorem v_addiw_small (x : word) (imm : Int)
    (Hlo : 0 ≤ (x.toNat : Int) + imm) (Hhi : (x.toNat : Int) + imm < 2 ^ 31) (_ : 0 ≤ imm) :
    ((v_addiw x imm).toNat : Int) = (x.toNat : Int) + imm := by
  unfold v_addiw
  rw [BitVec.toNat_ofInt]
  have hb : bv_swrap 32 ((x.toNat : Int) + imm) = (x.toNat : Int) + imm := by
    unfold bv_swrap
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.add_sub_cancel]
  rw [hb]
  rw [show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl]
  rw [Int.emod_eq_of_lt (by omega) (by have := u64_range x; omega), Int.toNat_of_nonneg (by omega)]

theorem v_addiw_id (x : word) (Hx : (x.toNat : Int) < 2 ^ 31) : v_addiw x 0 = x := by
  apply BitVec.eq_of_toNat_eq
  have h := v_addiw_small x 0 (by omega) (by omega) (by omega)
  rw [Int.add_zero] at h
  exact Int.ofNat_inj.mp h

/- Every [jalr] in these binaries has a concrete rs1 value and
   immediate at proof time (ra is always a concrete code address), so
   [v_jalr _ _ = <target>] closes by computation (through [decide])
   instance-by-instance; no symbolic lemma is needed. -/

/-- Masking a small exit code with 255 is the identity (word-level;
    used by [tw_exit_coden] against [tw_exit]'s [bv_and _ 255]). -/
theorem land_255_small (c : word) (Hc : (c.toNat : Int) < 256) :
    c &&& BitVec.ofInt 64 255 = c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 255).toNat = 255 from by decide]
  have h : c.toNat &&& 255 = c.toNat := by
    have h1 : (255 : Nat) = 2 ^ 8 - 1 := by decide
    have hc : c.toNat < 256 := by
      have h' : (c.toNat : Int) < ((256 : Nat) : Int) := Hc
      exact Int.ofNat_lt.mp h'
    rw [h1, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]
  rw [h]

end WithFP3


section WithFP4

variable [fx : FPState]

/- =================================================================
   to_wexit constructors
   ================================================================= -/

/-- The raw ecall post-state record (svc field = [some (getr regs 17)], as
    [step_ecall] leaves it).  abbreviation: the statements
    spell the record out five times; naming it here keeps the statements
    readable and changes nothing (it is a `def`, reducible). -/
abbrev ecall_st (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    machine_state :=
  { ms_regs := regs, ms_fregs := fx.fp_regs, ms_pc_val := pc,
    ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fx.fp_csr,
    ms_mem := mem, ms_rom := rom }

/-- A write at the raw ecall post-state, continuing with the ACTUAL
    syscall return value: the environment delivers a nonempty prefix of
    [buf], so a0 holds [len_word (firstn n buf)] for the chosen [n] and
    the continuation is the delivered-length family.  Use instead of
    [tw_write_rec] when the binary tests the return value (write-retry
    loops).  Conventions follow [tw_write_rec]: the a7 test is
    Int-characterized, fd 1 is [Z_to_bv 64 1], the record carries
    [ms_resv := None]. -/
theorem tw_write_ret (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (buf : List byte) (bufs : List (List byte)) (code : word)
    (H17 : ((getr regs 17).toNat : Int) = 64)
    (H10 : reg_get regs 10 = BitVec.ofInt 64 1)
    (Hr : ms_read_bytes (ecall_st regs pc mem rom)
      (reg_get regs 11) (reg_get regs 12) = some buf)
    (Hnb : 1 ≤ buf.length)
    (Hcont : ∀ n, 1 ≤ n → n ≤ buf.length →
       to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n)))
         (v_addi pc 4) mem rom) bufs code) :
    to_wexit segs (ecall_st regs pc mem rom) (buf :: bufs) code := by
  refine to_wexit.tw_write (segs := segs) (ecall_st regs pc mem rom) (getr regs 17)
    buf bufs code rfl H17 ?_ ?_ Hnb ?_
  · simp only [ecall_st, ms_gpr, arg_reg_0]
    exact H10
  · simp only [ecall_st, ms_gpr, arg_reg_1, arg_reg_2]
    exact Hr
  · intro n Hn1 Hn2
    have hstep : advance_past_svc (set_gpr0 (ecall_st regs pc mem rom) (len_word (buf.take n)))
        = mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom :=
      adv_set regs pc _ mem rom _
    rw [hstep]
    exact Hcont n Hn1 Hn2

/-- Exit with an arbitrary small code at the raw ecall post-state. -/
theorem tw_exit_coden (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (c : word)
    (H17 : ((getr regs 17).toNat : Int) = 93)
    (H10 : reg_get regs 10 = c) (Hc : (c.toNat : Int) < 256) :
    to_wexit segs (ecall_st regs pc mem rom) [] c := by
  have Hg : ms_gpr (ecall_st regs pc mem rom) 0 &&& BitVec.ofInt 64 255 = c := by
    have hg0 : ms_gpr (ecall_st regs pc mem rom) 0 = reg_get regs 10 := by
      simp only [ecall_st, ms_gpr]
      congr 1
    rw [hg0, H10]
    exact land_255_small c Hc
  rw [← Hg]
  exact to_wexit.tw_exit (ecall_st regs pc mem rom) (getr regs 17) rfl (Or.inl H17)

end WithFP4

section WithFP5

variable [fx : FPState]

/- =================================================================
   Generic argv-pointer bounds
   ================================================================= -/

/-- Everything the initial stack layout can address fits in
    [sp .. sp + argv_layout_slack), where the slack covers the maximal
    struct prefix, all argv string bytes, and one string's length.
    (A [Z] constant; the bounds are over [bv_unsigned].) -/
def argv_layout_slack : Int := 4300000

/-- Pure-[Z] arithmetic cores for [argv_ptr_bounds].
    PERFORMANCE: they exist so each `omega` below runs in a MINIMAL
    context.  Inside the main proof the [valid_argv]/[valid_envp]
    components sit in scope carrying large [nat] literals (2097152,
    131071, ...); an arithmetic call that sees them is much slower even
    though it needs none of them (the certificate search drags the large
    constants through).  Stated separately, each call is instantaneous.
 Same facts, same
    use sites. -/
theorem argv_struct_arith (a e : Nat) (ha0 : 0 ≤ a) (ha : a ≤ 1024)
    (he0 : 0 ≤ e) (he : e ≤ 256) :
    8 + (a + 1) * 8 + (e + 1) * 8 + 160 ≤ 10424 := by omega

theorem argv_sum_arith (a b : Nat) (ha : a ≤ 10424) (hb : b ≤ 2097152) :
    a + b ≤ 2107576 := by omega

theorem argv_mod_arith (s m : Nat) (hs : 0 ≤ s) (hm : 0 ≤ m) (hm' : m ≤ 2107576)
    (h : s + 4300000 < 2 ^ 64) : 0 ≤ s + m ∧ s + m < 2 ^ 64 := by omega

theorem argv_final_arith (s m l : Nat) (hm : 0 ≤ m) (hl : 0 ≤ l) (hm' : m ≤ 2107576)
    (hl' : l ≤ 131071) (h : s + 4300000 < 2 ^ 64) :
    s ≤ s + m ∧ s + m + l + 1 < 2 ^ 64 := by omega

/-- [bv_unsigned] of [sp + nat_to_word n] below the wrap. -/
theorem toNat_add_nat_to_word (sp : word) (n : Nat) (h : sp.toNat + n < 2 ^ 64) :
    (sp + nat_to_word n).toNat = sp.toNat + n := by
  have hn : n < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, show (nat_to_word n).toNat = n from by
    rw [nat_to_word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]]
  exact Nat.mod_eq_of_lt h

theorem argv_ptr_bounds (sp : word) (av ev : List (List byte)) (k : Nat)
    (Hva : valid_argv av) (Hve : valid_envp ev) (Hk : k < av.length)
    (Hsp : (sp.toNat : Int) + argv_layout_slack < ((2 ^ 64 : Nat) : Int)) :
    ((sp.toNat : Int) ≤ ((cat_argv_ptr sp av ev k).toNat : Int)) ∧
    (((cat_argv_ptr sp av ev k).toNat : Int)
      + ((av[k]?.getD []).length : Int) + 1 < ((2 ^ 64 : Nat) : Int)) := by
  -- the [valid_argv]/[valid_envp] projections, read at `Nat`
  have hav : av.length ≤ 1024 := Int.ofNat_le.mp (valid_argv_len av Hva)
  have hev : ev.length ≤ 256 := Int.ofNat_le.mp (Hve.1)
  have hnth : (av[k]?.getD []).length ≤ 131071 :=
    Int.ofNat_le.mp (valid_argv_str_len av k Hva Hk)
  -- the total argv byte bound, at the prefix [av.take k]
  have htot_av : total_arg_bytes_nat av ≤ 2097152 := by
    have h := Hva.2.1
    rw [total_arg_bytes_Z] at h
    exact Int.ofNat_le.mp h
  have htot : total_arg_bytes_nat (av.take k) ≤ 2097152 :=
    Nat.le_trans (total_arg_bytes_firstn_le k av) htot_av
  -- the struct prefix fits
  have hA : cat_struct_size av ev ≤ 10424 :=
    argv_struct_arith av.length ev.length (Nat.zero_le _) hav (Nat.zero_le _) hev
  -- the layout offset [n] and its bounds
  have hn : cat_struct_size av ev + total_arg_bytes_nat (av.take k) ≤ 2107576 :=
    argv_sum_arith _ _ hA htot
  -- the pointer is [sp + n]
  have Hptr : cat_argv_ptr sp av ev k
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k Hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge]
  -- the no-overflow bound on [sp], at `Nat`
  have HspN : sp.toNat + 4300000 < 2 ^ 64 := by
    have h := Hsp
    unfold argv_layout_slack at h
    rw [← Int.ofNat_lt, Int.natCast_add]
    exact h
  have hmod : sp.toNat + (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) < 2 ^ 64 :=
    (argv_mod_arith _ _ (Nat.zero_le _) (Nat.zero_le _) hn HspN).2
  have Hu := toNat_add_nat_to_word sp _ hmod
  have hfin := argv_final_arith sp.toNat _
    (av[k]?.getD []).length (Nat.zero_le _) (Nat.zero_le _) hn hnth HspN
  constructor
  · rw [Hptr, Hu]
    exact Int.le_add_of_nonneg_right (Int.natCast_nonneg _)
  · rw [Hptr, Hu]
    have h' : ((sp.toNat + (cat_struct_size av ev + total_arg_bytes_nat (av.take k))
        + (av[k]?.getD []).length + 1 : Nat) : Int) < ((2 ^ 64 : Nat) : Int) :=
      Int.ofNat_lt.mpr hfin.2
    simpa only [Int.natCast_add, Int.natCast_one] using h'

end WithFP5

section WithFP6

variable [fx : FPState]

/-- Jalr with rd = x0 (RISC-V [ret] / tail jump) and the target named.
    (No [align4_jalr] hypothesis: the ISA model has no jump alignment check.) -/
theorem step_jalr_x0 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 : reg) (imm : BitVec 12) (tgt : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.jalr 0 rs1 imm, 4))
    (Ht : getr regs rs1 = tgt) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_jalr tgt imm.toInt) mem rom) := by
  rw [step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd, Ht]
  simp only [bv_eqb_refl, ite_true]

/-- Jalr with a live link register and the target named. -/
theorem step_jalr_link (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 : reg) (imm : BitVec 12) (tgt : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.jalr rd rs1 imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Ht : getr regs rs1 = tgt) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt imm.toInt) mem rom) := by
  rw [step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd, Ht, Hrd]
  simp only [Bool.false_eq_true, ite_false]

end WithFP6

/- =================================================================
   Register-lookup resolution tactics
   ================================================================= -/

section WithFPRegs

variable [fx : FPState]

theorem getr_zero (regs : BvMap word) : getr regs 0 = BitVec.ofInt 64 0 := by
  simp only [getr, bv_eqb_refl, ite_true]
  rfl

/-- Discharge a concrete [reg]-literal inequality ([r ≠ r'], both closed
    [bv 5] literals).

    PERFORMANCE: the tactic is [discriminate Hc], not bare
    [discriminate], for the reason quoted below; in this tree the two
    registers are closed `BitVec 5` literals, so `decide` IS the
    hypothesis-naming closer and there is no failing-attempt cost to
    control:
     notes that bare [discriminate] falls back to scanning the
    whole hypothesis context on the FAILING attempt that terminates each
    `rewrite !`/`repeat` — there the two registers are equal and [Hc]
    reduces to [8%Z = 8%Z].  Argument-less [discriminate] then scans the
    context for some other discriminable equation, which in a stepping
    proof means conversion work over the machine state and memory image:
    ~10 s per failing attempt.  Naming the hypothesis makes the failure
    immediate. -/
macro "reg_neq_tac" : tactic => `(tactic| decide)

/-- Resolve [getr <regupd-chain> r] for concrete register numbers. -/
macro "getr_resolve" : tactic =>
  `(tactic|
    (repeat (first
      | rw [getr_same _ _ _ (by decide)]
      | rw [getr_other _ _ _ _ (by decide)]
      | rw [getr_zero]
      | rw [getr_nz _ _ (by decide)])))

/-- Resolve [<regupd-chain> r] applications. -/
macro "regupd_resolve" : tactic =>
  `(tactic|
    (repeat (first
      | rw [regupd_same]
      | rw [regupd_other _ _ _ _ (by decide)])))

-- Smoke tests: the tactics are not otherwise exercised in this file.
example (regs : BvMap word) (v : word) : getr (regupd (regupd regs 8 v) 9 v) 8 = v := by
  getr_resolve

example (regs : BvMap word) (v : word) : getr (regupd regs 8 v) 0 = BitVec.ofInt 64 0 := by
  getr_resolve

example (regs : BvMap word) (v : word) : reg_get (regupd (regupd regs 8 v) 9 v) 8 = v := by
  regupd_resolve

end WithFPRegs

section WithFP7

variable [fx : FPState]

/- =================================================================
   M-extension, word ops, byte store, word load
   (M-extension steps: oob_read_bug_ns.  [step_lw_zero] and
    [v_remu_small] further down have exactly one user, modprint_ns —
    oob_read_bug_ns uses [v_remu] but never [v_remu_small].)
   ================================================================= -/

def v_divu (x y : word) : word := BitVec.ofInt 64 ((x.toNat : Int) / (y.toNat : Int))

def v_remu (x y : word) : word := BitVec.ofInt 64 ((x.toNat : Int) % (y.toNat : Int))

/-- Bridges: [Sem.mul_div M_DIVU]/[M_REMU] agree with the
    [v_divu]/[v_remu] shapes away from the divide-by-zero case. -/
theorem m_divu (a b : word) (Hb : (b.toNat : Int) ≠ 0) : mul_div .DIVU a b = v_divu a b := by
  have hb0 : b.toNat ≠ 0 := by intro h; exact Hb (by rw [h]; rfl)
  have hb : (b.toNat == 0) = false := by simp [hb0]
  simp only [mul_div, hb, Bool.false_eq_true, ite_false, v_divu]
  rw [show a.udiv b = BitVec.ofNat 64 (a.toNat / b.toNat) from BitVec.udiv_def,
    ← Int.natCast_ediv, BitVec.ofInt_natCast]

theorem m_remu (a b : word) (Hb : (b.toNat : Int) ≠ 0) : mul_div .REMU a b = v_remu a b := by
  have hb0 : b.toNat ≠ 0 := by intro h; exact Hb (by rw [h]; rfl)
  have hb : (b.toNat == 0) = false := by simp [hb0]
  simp only [mul_div, hb, Bool.false_eq_true, ite_false, v_remu]
  rw [show a.umod b = BitVec.ofNat 64 (a.toNat % b.toNat) from BitVec.umod_def,
    ← Int.natCast_emod, BitVec.ofInt_natCast]

theorem step_divu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul .DIVU rd rs1 rs2, 4))
    (Hnz : (getr regs rs2).toNat ≠ 0) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  have h : ((getr regs rs2).toNat : Int) ≠ 0 := by
    intro hc; exact Hnz (by rw [← Int.ofNat_inj]; simpa using hc)
  rw [step_mul_gen segs regs pc mem rom w .DIVU rd rs1 rs2 Hf He Hd,
    m_divu (getr regs rs1) (getr regs rs2) h]

theorem step_remu (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul .REMU rd rs1 rs2, 4))
    (Hnz : (getr regs rs2).toNat ≠ 0) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
        (v_addi pc 4) mem rom) := by
  have h : ((getr regs rs2).toNat : Int) ≠ 0 := by
    intro hc; exact Hnz (by rw [← Int.ofNat_inj]; simpa using hc)
  rw [step_mul_gen segs regs pc mem rom w .REMU rd rs1 rs2 Hf He Hd,
    m_remu (getr regs rs1) (getr regs rs2) h]

theorem step_lw_zero (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.load .SZ4 true rd rs imm, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hr : rdn segs mem (v_addi (getr regs rs) imm.toInt) 4
      = some [BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd (BitVec.ofInt 64 0)) (v_addi pc 4) mem rom) := by
  have hba : getr regs rs + sext 64 imm = v_addi (getr regs rs) imm.toInt :=
    b_addsext (getr regs rs) imm (by decide)
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 4
      = some [BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0] := by
    rw [hba, ov_rdn]; exact Hr
  have Hval : sext 64 (bits 0 32 (le_bytes_to_word [BitVec.ofInt 8 0, BitVec.ofInt 8 0,
      BitVec.ofInt 8 0, BitVec.ofInt 8 0])) = BitVec.ofInt 64 0 := by decide
  step_load_start2 Hf, He, Hd
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]
  have hrd0 : is_x0 rd = false := by rw [← bv_eqb0_is_x0]; exact Hrd
  simp only [bvmapSet, bvmap_set, getr, regupd, v_addi, bv_eqb0_is_x0, b_npc4, Hval, hrd0]
  by_cases h2 : is_x0 rs <;> simp [h2, bvmapSet, bvmap_set, w0, reg_get]

end WithFP7

section WithFP8

variable [fx : FPState]

/- =================================================================
   Division-by-shift and byte-truncation identities
   ================================================================= -/

/-- `2^m = 2^8 * 2^(m-8)` for `8 ≤ m`, at `Int` (the exponent split is a
    `Nat` identity, so it is stated once here). -/
theorem two_pow_split (m : Nat) (Hm : 8 ≤ m) :
    ((2 ^ m : Nat) : Int) = ((2 ^ 8 : Nat) : Int) * ((2 ^ (m - 8) : Nat) : Int) := by
  have e : (2 ^ m : Nat) = 2 ^ 8 * 2 ^ (m - 8) := by
    rw [← Nat.pow_add, show 8 + (m - 8) = m from by omega]
  rw [e, Int.natCast_mul]

/-- The div/mod shape of a shift by a whole number of bytes:
    `(z mod 2^m) / 2^8 = (z / 2^8) mod 2^(m-8)`. -/
theorem Zmod_pow2_div8 (z : Int) (m : Nat) (Hm : 8 ≤ m) :
    (z % ((2 ^ m : Nat) : Int)) / ((2 ^ 8 : Nat) : Int)
      = (z / ((2 ^ 8 : Nat) : Int)) % ((2 ^ (m - 8) : Nat) : Int) := by
  have h256 : ((2 ^ 8 : Nat) : Int) = 256 := by decide
  rw [two_pow_split m Hm, h256]
  -- the two residues of [z] at 256
  have hr0 : 0 ≤ z % 256 := Int.emod_nonneg _ (by decide)
  have hr256 : z % 256 < 256 := Int.emod_lt_of_pos _ (by decide)
  have hB0 : (0 : Int) < ((2 ^ (m - 8) : Nat) : Int) :=
    Int.ofNat_lt.mpr (Nat.two_pow_pos _)
  have hB1 : (1 : Int) ≤ ((2 ^ (m - 8) : Nat) : Int) := by omega
  -- [z = 256 * (z/256) + z%256], so the residue at [256 * B] is explicit
  have hzmod : z % (256 * ((2 ^ (m - 8) : Nat) : Int))
      = 256 * ((z / 256) % ((2 ^ (m - 8) : Nat) : Int)) + z % 256 := by
    have e1 : 256 * (z / 256) + z % 256 = z := Int.mul_ediv_add_emod z 256
    calc z % (256 * ((2 ^ (m - 8) : Nat) : Int))
        = (256 * (z / 256) + z % 256) % (256 * ((2 ^ (m - 8) : Nat) : Int)) := by rw [e1]
      _ = ((256 * (z / 256)) % (256 * ((2 ^ (m - 8) : Nat) : Int)) + z % 256)
            % (256 * ((2 ^ (m - 8) : Nat) : Int)) := by
            rw [Int.add_emod, Int.emod_eq_of_lt hr0 (by omega)]
      _ = (256 * ((z / 256) % ((2 ^ (m - 8) : Nat) : Int)) + z % 256)
            % (256 * ((2 ^ (m - 8) : Nat) : Int)) := by
            rw [Int.mul_emod_mul_of_pos (a := (256 : Int)) (z / 256) _ (by decide)]
      _ = 256 * ((z / 256) % ((2 ^ (m - 8) : Nat) : Int)) + z % 256 :=
            Int.emod_eq_of_lt (by omega) (by omega)
  rw [hzmod, Int.add_comm (256 * ((z / 256) % ((2 ^ (m - 8) : Nat) : Int))) (z % 256),
    Int.add_mul_ediv_left (z % 256) ((z / 256) % ((2 ^ (m - 8) : Nat) : Int))
      (by decide : (256 : Int) ≠ 0),
    Int.ediv_eq_zero_of_lt hr0 hr256, Int.zero_add]

/-- An [n]-byte little-endian list only depends on [z] modulo [2^(8n)]. -/
theorem Z_to_le_bytes_wrap (n : Nat) (m : Nat) (z : Int) (Hm : 8 * n ≤ m) :
    Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z := by
  induction n generalizing m z with
  | zero => rw [Z_to_le_bytes, Z_to_le_bytes]
  | succ n ih =>
    rw [Z_to_le_bytes, Z_to_le_bytes, bv_wrap]
    congr 1
    · -- the low byte: [z mod 2^m] and [z] agree modulo [2^8]
      have hdvd : ((2 ^ 8 : Nat) : Int) ∣ ((2 ^ m : Nat) : Int) := by
        refine ⟨((2 ^ (m - 8) : Nat) : Int), ?_⟩
        rw [two_pow_split m (by omega)]
      have he : (z % ((2 ^ m : Nat) : Int)) % ((2 ^ 8 : Nat) : Int)
          = z % ((2 ^ 8 : Nat) : Int) := Int.emod_emod_of_dvd z hdvd
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, he]
    · -- the shift: [(z mod 2^m) >>> 8 = bv_wrap (m-8) (z >>> 8)]
      have hshift : (z % ((2 ^ m : Nat) : Int)) >>> 8
          = bv_wrap (m - 8) (z >>> 8) := by
        rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow,
          Zmod_pow2_div8 z m (by omega), bv_wrap,
          show ((2 ^ 8 : Nat) : Int) = 256 from by decide]
      rw [hshift]
      exact ih (m - 8) _ (by omega)

/-- : the single stored byte of [sb] is the low byte of the word.
    It is the [n = 1] instance of [Z_to_le_bytes_wrap]. -/
theorem store_bytes_low8 (u : word) :
    Z_to_le_bytes 1 ((bits 0 8 u).toNat : Int) = word_to_le_bytes 1 u := by
  unfold word_to_le_bytes
  rw [← Z_to_le_bytes_wrap 1 8 (u.toNat : Int) (by decide)]
  congr 1

/-- The [sh] store value: 2 bytes of the 16-bit truncation are the
    2 bytes of the full word. -/
theorem store_bytes_low16 (u : word) :
    Z_to_le_bytes 2 ((bits 0 16 u).toNat : Int) = word_to_le_bytes 2 u := by
  unfold word_to_le_bytes
  rw [← Z_to_le_bytes_wrap 2 16 (u.toNat : Int) (by decide)]
  congr 1

/-- The [sw] store value: 4 bytes of [low32] are the 4 bytes of the
    full word. -/
theorem store_bytes_low32 (u : word) :
    Z_to_le_bytes 4 ((low32 u).toNat : Int) = word_to_le_bytes 4 u := by
  unfold word_to_le_bytes low32
  rw [← Z_to_le_bytes_wrap 4 32 (u.toNat : Int) (by decide)]
  congr 1

/-- Collapse the singleton [word_to_le_bytes] list to the literal byte;
    handy after [step_sb256]/[step_sb] when the caller wants the byte
    rather than [word_to_le_bytes 1 v].  Hypothesis-free. -/
theorem N_to_le_bytes_1_small (v : word) :
    word_to_le_bytes 1 v = [BitVec.ofInt 8 (v.toNat : Int)] := by
  rw [word_to_le_bytes, Z_to_le_bytes]
  rfl

end WithFP8

section WithFP9

variable [fx : FPState]

/-- Store byte: the stored list is the exact single little-endian byte
    of rs2 ([word_to_le_bytes 1], = [bv_extract 0 8]); no [< 128] /
    [< 256] value hypotheses are needed — the bv model stores the low
    byte directly. -/
theorem step_sb (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 1 (getr regs rs2))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 1 = true := by
    rw [hba]; exact Hok
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, store_bytes_low8, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [Sb] with any stored byte value: identical to [step_sb]; kept so
    call sites keep their name. -/
theorem step_sb256 (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 1 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 1 (getr regs rs2))) rom) :=
  step_sb segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok

/-- Store word, stored VALUE exposed (the [sw] analogue of
    [step_sd_val]). -/
theorem step_sw_val (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ4 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 4 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 4 (getr regs rs2))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 4 = true := by
    rw [hba]; exact Hok
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, store_bytes_low32, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [step_sw_val] with the store address and value pre-normalized. -/
theorem step_sw_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.store .SZ4 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hok : store_ok segs mem a 4 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom) := by
  rw [step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd]
  · simp only [Ha, Hv]
  · rw [Ha]; exact Hok

/-- Store halfword, stored VALUE exposed (the [sh] analogue of
    [step_sd_val]). -/
theorem step_sh_val (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decodeAny w = some (Instr.store .SZ2 rs1 rs2 imm, 4))
    (Hok : store_ok segs mem (v_addi (getr regs rs1) imm.toInt) 2 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs rs1) imm.toInt)
          (word_to_le_bytes 2 (getr regs rs2))) rom) := by
  have hba : getr regs rs1 + sext 64 imm = v_addi (getr regs rs1) imm.toInt :=
    b_addsext (getr regs rs1) imm (by decide)
  have hok : store_ok segs mem (getr regs rs1 + sext 64 imm) 2 = true := by
    rw [hba]; exact Hok
  step_pipeline Hfetch, Hecall, Hdecode
  simp only [store_val, getr, rget, reg_get, bv_eqb0_is_x0, w0, v_addi] at hok hba ⊢
  rw [hba] at hok
  simp only [hba, hok, interp_eff_accesses, drop_access_report, mkAccessReport,
    write_to_mem_wbytes, store_bytes_low16, width_bytes, mkst, inval_resv, ite_true, reduceIte]

/-- [step_sh_val] with the store address and value pre-normalized. -/
theorem step_sh_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (a v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.store .SZ2 rs1 rs2 imm, 4))
    (Ha : v_addi (getr regs rs1) imm.toInt = a) (Hv : getr regs rs2 = v)
    (Hok : store_ok segs mem a 2 = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom) := by
  rw [step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd]
  · simp only [Ha, Hv]
  · rw [Ha]; exact Hok

/- The [sb] [_at] form already exists as [MmapSim.step_sb_at] (with the
   stored BYTE additionally pre-normalized); it is not duplicated here —
   a same-name lemma with a different premise list would shadow it or be
   shadowed depending on import order (the [word_add_0_r] trap). -/

end WithFP9

section WithFP10

variable [fx : FPState]

/- value simplification -/

/-- [bv_unsigned (Z_to_bv n z)] for an in-range [z]. -/
theorem toNat_ofInt_small {n : Nat} {z : Int} (h0 : 0 ≤ z)
    (h1 : z < ((2 ^ n : Nat) : Int)) : ((BitVec.ofInt n z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

theorem v_divu_small (x y : word) (Hy : 0 < (y.toNat : Int)) :
    ((v_divu x y).toNat : Int) = (x.toNat : Int) / (y.toNat : Int) := by
  unfold v_divu
  refine toNat_ofInt_small
    (Int.ediv_nonneg (Int.natCast_nonneg _) (Int.le_of_lt Hy)) ?_
  rw [Int.natCast_pow]
  exact Int.lt_of_le_of_lt (Int.ediv_le_self _ (Int.natCast_nonneg _)) (u64_range x).2

theorem v_remu_small (x y : word) (Hy : 0 < (y.toNat : Int)) :
    ((v_remu x y).toNat : Int) = (x.toNat : Int) % (y.toNat : Int) := by
  unfold v_remu
  refine toNat_ofInt_small (Int.emod_nonneg _ (Int.ne_of_gt Hy)) ?_
  rw [Int.natCast_pow]
  exact Int.lt_of_lt_of_le (Int.emod_lt_of_pos _ Hy) (Int.le_of_lt (u64_range y).2)

theorem v_subw_small (x y : word) (Hle : (y.toNat : Int) ≤ (x.toNat : Int))
    (Hlt : (x.toNat : Int) - (y.toNat : Int) < 2 ^ 31) :
    ((v_subw x y).toNat : Int) = (x.toNat : Int) - (y.toNat : Int) := by
  unfold v_subw
  rw [BitVec.toNat_ofInt]
  have hsw : bv_swrap 32 ((x.toNat : Int) - (y.toNat : Int))
      = (x.toNat : Int) - (y.toNat : Int) := by
    unfold bv_swrap
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.add_sub_cancel]
  rw [hsw]
  have hx := u64_range x
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_of_nonneg (by omega)]

theorem land_d48 (d : Int) (Hd0 : 0 ≤ d) (Hd : d < 16) : zland d 48 = 0 := by
  have hd : d.toNat < 16 := by
    have h : (d.toNat : Int) = d := Int.toNat_of_nonneg Hd0
    omega
  unfold zland
  rw [show ((48 : Int).toNat) = 48 from by decide]
  have h1 : d.toNat &&& 15 = d.toNat := by
    rw [show (15 : Nat) = 2 ^ 4 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hd]
  rw [← h1, Nat.and_assoc, show (15 : Nat) &&& 48 = 0 from by decide, Nat.and_zero,
    Int.ofNat_zero]

theorem lor_small_add (d : Int) (Hd0 : 0 ≤ d) (Hd : d < 16) : zlor d 48 = d + 48 := by
  have hd : d.toNat < 16 := by
    have h : (d.toNat : Int) = d := Int.toNat_of_nonneg Hd0
    omega
  have hd' : (d.toNat : Int) = d := Int.toNat_of_nonneg Hd0
  unfold zlor
  rw [show ((48 : Int).toNat) = 48 from by decide]
  have h : 2 ^ 4 * 3 + d.toNat = 2 ^ 4 * 3 ||| d.toNat :=
    Nat.two_pow_add_eq_or_of_lt (i := 4) (b := d.toNat) (a := 3) (by omega)
  have e48 : (48 : Nat) = 2 ^ 4 * 3 := by decide
  have h' : d.toNat ||| 48 = d.toNat + 48 := by
    rw [Nat.or_comm, e48, ← h]
    omega
  rw [h', Int.natCast_add, hd', show ((48 : Nat) : Int) = 48 from by decide]

theorem v_ori_lor (d : word) (Hd : (d.toNat : Int) < 16) :
    v_ori d 48 = BitVec.ofInt 64 ((d.toNat : Int) + 48) := by
  unfold v_ori
  rw [show bv_wrap 64 48 = 48 from by decide,
    lor_small_add (d.toNat : Int) (Int.natCast_nonneg _) Hd]

end WithFP10

section WithFP11

variable [fx : FPState]

/- =================================================================
   rdn composition/extraction (generic)
   ================================================================= -/

/-- the byte [rdn] reads at [a] (the writable overlay
    first, then the immutable image) — the scrutinee  destructures
    inline as `match mem a with Some b => Some b | None => seg_rom segs a`. -/
def rdn_byte (segs : List Segment) (mem : word → Option byte) (a : word) : Option byte :=
  match mem a with
  | some b => some b
  | none => seg_rom segs a

/-- the [n + 1] step of [rdn] at an arbitrary read byte
    (the general form of [rdn_succ], which fixes the overlay as the source). -/
theorem rdn_succ_byte (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat)
    (b : byte) (h : rdn_byte segs mem a = some b) :
    rdn segs mem a (n + 1) = (rdn segs mem (a + 1) n).bind (fun rest => some (b :: rest)) := by
  cases hmem : mem a with
  | some c =>
    have hc : c = b := by
      have h' := h
      unfold rdn_byte at h'
      rw [hmem] at h'
      exact Option.some.inj h'
    subst hc
    simp only [rdn, hmem]
    cases rdn segs mem (a + 1) n with
    | none => rfl
    | some rest => rfl
  | none =>
    have hseg : seg_rom segs a = some b := by
      have h' := h
      unfold rdn_byte at h'
      rw [hmem] at h'
      exact h'
    simp only [rdn, hmem, hseg]
    cases rdn segs mem (a + 1) n with
    | none => rfl
    | some rest => rfl

/-- a [none] read at [a] makes the [n + 1] read fail. -/
theorem rdn_succ_none (segs : List Segment) (mem : word → Option byte) (a : word) (n : Nat)
    (h : rdn_byte segs mem a = none) : rdn segs mem a (n + 1) = none := by
  cases hmem : mem a with
  | some c =>
    have h' := h
    unfold rdn_byte at h'
    rw [hmem] at h'
    exact absurd h' (by simp)
  | none =>
    have hseg : seg_rom segs a = none := by
      have h' := h
      unfold rdn_byte at h'
      rw [hmem] at h'
      exact h'
    simp only [rdn, hmem, hseg]

/-- [a + nat_to_word (n + 1) = a + 1 + nat_to_word n] (the index step of the
    [rdn] inductions below). -/
theorem add_nat_to_word_succ (a : word) (n : Nat) :
    a + nat_to_word (n + 1) = a + 1 + nat_to_word n := by
  rw [show n + 1 = 1 + n from by omega, ← nat_to_word_add_merge a 1 n, ← word1_nat]

theorem rdn_app (segs : List Segment) (mem : word → Option byte) (n1 : Nat) :
    ∀ (n2 : Nat) (a : word) (bs1 bs2 : List byte),
      rdn segs mem a n1 = some bs1 →
      rdn segs mem (a + nat_to_word n1) n2 = some bs2 →
      rdn segs mem a (n1 + n2) = some (bs1 ++ bs2) := by
  induction n1 with
  | zero =>
    intro n2 a bs1 bs2 H1 H2
    rw [rdn_zero, Option.some.injEq] at H1
    subst H1
    rw [word_add_0] at H2
    simpa using H2
  | succ n1 ih =>
    intro n2 a bs1 bs2 H1 H2
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 from by omega]
    cases hb : rdn_byte segs mem a with
    | none =>
      rw [rdn_succ_none segs mem a n1 hb] at H1
      exact absurd H1 (by simp)
    | some b =>
      rw [rdn_succ_byte segs mem a n1 b hb] at H1
      cases hr : rdn segs mem (a + 1) n1 with
      | none => rw [hr] at H1; simp at H1
      | some rest =>
        rw [hr] at H1
        simp only [Option.bind_some, Option.some.injEq] at H1
        subst H1
        rw [rdn_succ_byte segs mem a (n1 + n2) b hb,
          ih n2 (a + 1) rest bs2 hr (by rw [add_nat_to_word_succ] at H2; exact H2)]
        rfl

theorem rdn_nth (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte) (j : Nat),
      rdn segs mem a n = some bs → j < n →
      rdn segs mem (a + nat_to_word j) 1 = some [bs[j]?.getD (BitVec.ofInt 8 0)] := by
  induction n with
  | zero => intro a bs j _ Hj; omega
  | succ n ih =>
    intro a bs j H Hj
    cases hb : rdn_byte segs mem a with
    | none =>
      rw [rdn_succ_none segs mem a n hb] at H
      exact absurd H (by simp)
    | some b =>
      rw [rdn_succ_byte segs mem a n b hb] at H
      cases hr : rdn segs mem (a + 1) n with
      | none => rw [hr] at H; simp at H
      | some rest =>
        rw [hr] at H
        simp only [Option.bind_some, Option.some.injEq] at H
        subst H
        cases j with
        | zero =>
          rw [word_add_0, rdn_succ_byte segs mem a 0 b hb, rdn_zero]
          rfl
        | succ j' =>
          rw [add_nat_to_word_succ]
          exact ih (a + 1) rest j' hr (by omega)

/-- [addi] with a negative immediate (generic form of the per-example
    [v_addi_m16]/[v_addi_m64] locals; use with [apply] — the immediate
    [-k] is convertible to the literal).  The immediate is a [Z], and
    the conclusion is the [Z_to_bv]-normal form (the equation itself
    holds by conversion — the hypotheses are kept so call sites survive
    and so the RHS really is a non-wrapping difference). -/
theorem v_addi_m (x : word) (k : Int) (_ : k ≤ (x.toNat : Int)) (_ : 0 < k) :
    v_addi x (- k) = BitVec.ofInt 64 ((x.toNat : Int) - k) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem rdn_skipn (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte) (k : Nat),
      rdn segs mem a n = some bs → k ≤ n →
      rdn segs mem (a + nat_to_word k) (n - k) = some (bs.drop k) := by
  induction n with
  | zero =>
    intro a bs k H Hk
    have hk : k = 0 := by omega
    subst hk
    have hbs : bs = [] := by
      have h' := H
      rw [rdn_zero] at h'
      exact (Option.some.inj h').symm
    subst hbs
    rw [word_add_0, rdn_zero]
    rfl
  | succ n ih =>
    intro a bs k H Hk
    cases hb : rdn_byte segs mem a with
    | none =>
      rw [rdn_succ_none segs mem a n hb] at H
      exact absurd H (by simp)
    | some b =>
      rw [rdn_succ_byte segs mem a n b hb] at H
      cases hr : rdn segs mem (a + 1) n with
      | none => rw [hr] at H; simp at H
      | some rest =>
        rw [hr] at H
        simp only [Option.bind_some, Option.some.injEq] at H
        subst H
        cases k with
        | zero =>
          rw [word_add_0, show n + 1 - 0 = n + 1 from by omega,
            rdn_succ_byte segs mem a n b hb, hr]
          rfl
        | succ k' =>
          rw [add_nat_to_word_succ,
            show n + 1 - (k' + 1) = n - k' from by omega,
            ih (a + 1) rest k' hr (by omega)]
          rfl

theorem rdn_firstn (segs : List Segment) (mem : word → Option byte) (n : Nat) :
    ∀ (a : word) (bs : List byte) (k : Nat),
      rdn segs mem a n = some bs → k ≤ n →
      rdn segs mem a k = some (bs.take k) := by
  induction n with
  | zero =>
    intro a bs k H Hk
    have hk : k = 0 := by omega
    subst hk
    rw [rdn_zero, Option.some.injEq] at H
    subst H
    rw [rdn_zero]
    rfl
  | succ n ih =>
    intro a bs k H Hk
    cases hb : rdn_byte segs mem a with
    | none =>
      rw [rdn_succ_none segs mem a n hb] at H
      exact absurd H (by simp)
    | some b =>
      rw [rdn_succ_byte segs mem a n b hb] at H
      cases hr : rdn segs mem (a + 1) n with
      | none => rw [hr] at H; simp at H
      | some rest =>
        rw [hr] at H
        simp only [Option.bind_some, Option.some.injEq] at H
        subst H
        cases k with
        | zero => rw [rdn_zero]; rfl
        | succ k' =>
          rw [rdn_succ_byte segs mem a k' b hb, List.take_succ_cons,
            ih (a + 1) rest k' hr (by omega)]
          rfl

end WithFP11

/- =================================================================
   Sanity checks

    carries none for this file; these pin the few computable
   definitions the module introduces (the conventions of this tree's
   "definition of done").
   ================================================================= -/

section Sanity

/-- Sanity check for [v_divu]: unsigned division, truncated to 64 bits. -/
example : v_divu (BitVec.ofInt 64 100) (BitVec.ofInt 64 7) = BitVec.ofInt 64 14 := by decide

/-- Sanity check for [v_remu]: unsigned remainder. -/
example : v_remu (BitVec.ofInt 64 100) (BitVec.ofInt 64 7) = BitVec.ofInt 64 2 := by decide

/-- Sanity check for [v_jalr]: bit 0 of the target is cleared. -/
example : v_jalr (BitVec.ofInt 64 0x1001) 0 = BitVec.ofInt 64 0x1000 := by decide

/-- Sanity check for [v_jalr] with an immediate. -/
example : v_jalr (BitVec.ofInt 64 0x1000) 8 = BitVec.ofInt 64 0x1008 := by decide

/-- Sanity check for [argv_layout_slack]. -/
example : argv_layout_slack = 4300000 := by decide

/-- Sanity check for [N_to_le_bytes_1_small] at a concrete word: only the
    low byte survives. -/
example : word_to_le_bytes 1 (BitVec.ofInt 64 0x1234) = [BitVec.ofInt 8 0x34] := by decide

/-- Sanity check for [v_addi_m] at a concrete base and immediate. -/
example : v_addi (BitVec.ofInt 64 100) (- (16 : Int)) = BitVec.ofInt 64 84 := by decide

/-- Sanity check for [v_addiw_id]: the sign-extended word op is the identity
    on an in-range value. -/
example : v_addiw (BitVec.ofInt 64 41) 0 = BitVec.ofInt 64 41 := by decide

end Sanity
