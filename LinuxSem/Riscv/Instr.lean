/-
  * Instr: the RV64GC base instruction AST.

  Design rules:
  - Immediates are kept at their *encoded* width with the sign bit
    included (I/S: 12 bits, B: 13, U: 20, J: 21); interpretation
    (sign-extension, shifting) is deferred to the semantics.
  - Compressed instructions have their own AST in `DecodeC` and are
    expanded into this AST, so the execution semantics is written once.
-/
import LinuxSem.Riscv.Prelude

namespace LinuxSem.Riscv

/-- Integer register-register ops (OP / OP-32 major opcodes). -/
inductive AluOp : Type
  | ADD | SUB | SLL | SLT | SLTU
  | XOR | SRL | SRA | OR | AND
  deriving DecidableEq, Repr

/-- M extension ops. -/
inductive MulOp : Type
  | MUL | MULH | MULHSU | MULHU
  | DIV | DIVU | REM | REMU
  deriving DecidableEq, Repr

inductive BranchCond : Type
  | EQ | NE | LT | GE | LTU | GEU
  deriving DecidableEq, Repr

/-- Memory access sizes, in bytes. -/
inductive MSize : Type
  | SZ1 | SZ2 | SZ4 | SZ8
  deriving DecidableEq, Repr

/-- A extension. -/
inductive AmoOp : Type
  | SWAP | ADD | XOR | AND | OR
  | MIN | MAX | MINU | MAXU
  deriving DecidableEq, Repr

/-- `.w` / `.d` -/
inductive AWidth : Type
  | W | D
  deriving DecidableEq, Repr

/-- Zicsr. -/
inductive CsrOp : Type
  | RW | RS | RC
  deriving DecidableEq, Repr

/-- F/D formats. -/
inductive FFmt : Type
  | S | D
  deriving DecidableEq, Repr

inductive FariOp : Type
  | ADD | SUB | MUL | DIV
  deriving DecidableEq, Repr

inductive FmaOp : Type
  | MADD | MSUB | NMSUB | NMADD
  deriving DecidableEq, Repr

inductive FsgnOp : Type
  | SGNJ | SGNJN | SGNJX
  deriving DecidableEq, Repr

inductive FminmaxOp : Type
  | MIN | MAX
  deriving DecidableEq, Repr

inductive FcmpOp : Type
  | EQ | LT | LE
  deriving DecidableEq, Repr

/-- Operand kind of an `Fcvt`: integer (32/64, signed/unsigned) or FP
    format.  Decoding only produces the architecturally valid pairs. -/
inductive FcvtTy : Type
  | W | WU | L | LU   /- integer targets/sources -/
  | S | D             /- FP formats -/
  deriving DecidableEq, Repr

/-- `fmv.x.w` / `fmv.w.x` / `fmv.x.d` / `fmv.d.x`: direction of the raw move. -/
inductive FmvDir : Type
  | X_F | F_X
  deriving DecidableEq, Repr

inductive Instr : Type
/- RV32I / RV64I -/
  | lui (rd : reg) (imm : BitVec 20)
  | auipc (rd : reg) (imm : BitVec 20)
  | jal (rd : reg) (imm : BitVec 21)        -- bit 0 of imm is always 0
  | jalr (rd rs1 : reg) (imm : BitVec 12)
  | branch (c : BranchCond) (rs1 rs2 : reg) (imm : BitVec 13)  -- bit 0 always 0
  | load (sz : MSize) (signed : Bool) (rd rs1 : reg) (imm : BitVec 12)
  | store (sz : MSize) (rs1 rs2 : reg) (imm : BitVec 12)  -- mem[rs1+imm] <- rs2
  | opImm (op : AluOp) (rd rs1 : reg) (imm : BitVec 12)
      -- addi/slti/sltiu/xori/ori/andi; never SUB/shift
  | shiftImm (op : AluOp) (rd rs1 : reg) (shamt : BitVec 6)   -- slli/srli/srai
  | op (op : AluOp) (rd rs1 rs2 : reg)
  | opImm32 (rd rs1 : reg) (imm : BitVec 12)                  -- addiw
  | shiftImm32 (op : AluOp) (rd rs1 : reg) (shamt : BitVec 5) -- slliw/srliw/sraiw
  | op32 (op : AluOp) (rd rs1 rs2 : reg)  -- addw/subw/sllw/srlw/sraw
  | fence (fm : BitVec 4) (pred succ : BitVec 4) (rd rs1 : reg)
  | fenceI (rd rs1 : reg) (imm : BitVec 12)
  | ecall
  | ebreak
/- M -/
  | mul (op : MulOp) (rd rs1 rs2 : reg)
  | mul32 (op : MulOp) (rd rs1 rs2 : reg)  -- mulw/divw/divuw/remw/remuw
/- A -/
  | lr (w : AWidth) (aq rl : Bool) (rd rs1 : reg)
  | sc (w : AWidth) (aq rl : Bool) (rd rs1 rs2 : reg)
  | amo (op : AmoOp) (w : AWidth) (aq rl : Bool) (rd rs1 rs2 : reg)
/- Zicsr -/
  | csr (op : CsrOp) (rd rs1 : reg) (csr : BitVec 12)
  | csrI (op : CsrOp) (rd : reg) (uimm : BitVec 5) (csr : BitVec 12)
/- F/D loads/stores (rd/rs2 name FP registers) -/
  | fLoad (fmt : FFmt) (rd rs1 : reg) (imm : BitVec 12)
  | fStore (fmt : FFmt) (rs1 rs2 : reg) (imm : BitVec 12)
/- F/D computation -/
  | fma (op : FmaOp) (fmt : FFmt) (rd rs1 rs2 rs3 : reg) (rm : BitVec 3)
  | fari (op : FariOp) (fmt : FFmt) (rd rs1 rs2 : reg) (rm : BitVec 3)
  | fsqrt (fmt : FFmt) (rd rs1 : reg) (rm : BitVec 3)
  | fsgnj (op : FsgnOp) (fmt : FFmt) (rd rs1 rs2 : reg)
  | fminmax (op : FminmaxOp) (fmt : FFmt) (rd rs1 rs2 : reg)
  | fcmp (op : FcmpOp) (fmt : FFmt) (rd rs1 rs2 : reg)
  | fcvt (dst src : FcvtTy) (rd rs1 : reg) (rm : BitVec 3)
  | fmv (dir : FmvDir) (fmt : FFmt) (rd rs1 : reg)
  | fclass (fmt : FFmt) (rd rs1 : reg)
  deriving DecidableEq, Repr

/-- Size in bytes of a modeled memory access. -/
def msizeBytes : MSize → Int
  | .SZ1 => 1 | .SZ2 => 2 | .SZ4 => 4 | .SZ8 => 8

end LinuxSem.Riscv
