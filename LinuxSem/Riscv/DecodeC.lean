/-
  * DecodeC: the RV64C compressed (16-bit) decoder.

  Compressed instructions get their own AST [CInstr] (one constructor per
  instruction, fields at encoded width) and are expanded into the base
  `Instr` AST by `expandC`, so the execution semantics is written once.
  Immediate fields of `CInstr` are stored *scaled* (as byte offsets /
  actual values, sign bit included) since the RVC scaling is a pure
  encoding artifact.

  Policy notes for a comparison with objdump (all confirmed against
  binutils objdump on rv64):
  - HINT encodings decode, matching binutils: c.addi with imm=0
    (c.nop prints as "c.addi zero,0" under -M no-aliases), c.li /
    c.lui / c.mv / c.add with rd=0, c.slli with rd=0.
  - Shifts with shamt=0 decode here as shamt-0 CSlli/CSrli/CSrai,
    but binutils prints them with the RV128 mnemonics c.slli64 /
    c.srli64 / c.srai64 — a comparison must special-case them.
  - The all-zero halfword 0x0000 returns none here, but binutils
    prints it as "c.unimp" — a comparison must special-case it.
  - Reserved encodings return none, matching binutils: c.addi4spn
    nzuimm=0, c.addiw rd=0, c.lui nzimm=0, c.lwsp/c.ldsp rd=0,
    c.jr rs1=0, the bit12=1 subw-group funct2 2/3.
    EXCEPTION: c.addi16sp nzimm=0 is reserved by the spec but
    binutils 2.40 accepts it, so we decode it (see below).
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode

namespace LinuxSem.Riscv

/-- Map a 3-bit compressed register field to x8..x15. -/
def creg (r : BitVec 3) : reg := (1 : BitVec 2).append r

inductive CInstr : Type
/- Quadrant 0 -/
  | cAddi4spn (rd' : BitVec 3) (nzuimm : BitVec 10)   -- addi rd', x2, nzuimm
  | cFld (rd' rs1' : BitVec 3) (uimm : BitVec 8)
  | cLw (rd' rs1' : BitVec 3) (uimm : BitVec 7)
  | cLd (rd' rs1' : BitVec 3) (uimm : BitVec 8)
  | cFsd (rs1' rs2' : BitVec 3) (uimm : BitVec 8)
  | cSw (rs1' rs2' : BitVec 3) (uimm : BitVec 7)
  | cSd (rs1' rs2' : BitVec 3) (uimm : BitVec 8)
/- Quadrant 1 -/
  | cAddi (rd : reg) (imm : BitVec 6)                 -- c.nop = CAddi x0 0
  | cAddiw (rd : reg) (imm : BitVec 6)
  | cLi (rd : reg) (imm : BitVec 6)
  | cAddi16sp (imm : BitVec 10)                       -- addi x2, x2, imm (×16)
  | cLui (rd : reg) (imm : BitVec 6)
  | cSrli (rd' : BitVec 3) (shamt : BitVec 6)
  | cSrai (rd' : BitVec 3) (shamt : BitVec 6)
  | cAndi (rd' : BitVec 3) (imm : BitVec 6)
  | cSub (rd' rs2' : BitVec 3) | cXor (rd' rs2' : BitVec 3)
  | cOr (rd' rs2' : BitVec 3) | cAnd (rd' rs2' : BitVec 3)
  | cSubw (rd' rs2' : BitVec 3) | cAddw (rd' rs2' : BitVec 3)
  | cJ (imm : BitVec 12)
  | cBeqz (rs1' : BitVec 3) (imm : BitVec 9)
  | cBnez (rs1' : BitVec 3) (imm : BitVec 9)
/- Quadrant 2 -/
  | cSlli (rd : reg) (shamt : BitVec 6)
  | cFldsp (rd : reg) (uimm : BitVec 9)
  | cLwsp (rd : reg) (uimm : BitVec 8)
  | cLdsp (rd : reg) (uimm : BitVec 9)
  | cJr (rs1 : reg)
  | cMv (rd rs2 : reg)
  | cEbreak
  | cJalr (rs1 : reg)
  | cAdd (rd rs2 : reg)
  | cFsdsp (rs2 : reg) (uimm : BitVec 9)
  | cSwsp (rs2 : reg) (uimm : BitVec 8)
  | cSdsp (rs2 : reg) (uimm : BitVec 9)
  deriving DecidableEq, Repr

/-- Decode a 16-bit compressed instruction halfword. -/
def decode16 (h : BitVec 16) : Option CInstr :=
  let f3 := (bits 13 3 h).toNat
  let r1c : BitVec 3 := bits 7 3 h   -- rs1'/rd'
  let r2c : BitVec 3 := bits 2 3 h   -- rs2'/rd'
  let rd : reg := bits 7 5 h         -- full-width rd/rs1
  let rs2 : reg := bits 2 5 h        -- full-width rs2
  -- Common immediates
  let imm6 : BitVec 6 := (bits 12 1 h).append (bits 2 5 h)
  let uimmD : BitVec 8 :=   -- c.fld/c.ld/c.fsd/c.sd: ×8
    (bits 5 2 h).append ((bits 10 3 h).append (0 : BitVec 3))
  let uimmW : BitVec 7 :=   -- c.lw/c.sw: ×4
    (bits 5 1 h).append
      ((bits 10 3 h).append ((bits 6 1 h).append (0 : BitVec 2)))
  match (bits 0 2 h).toNat, f3 with
  -- ---- Quadrant 0 ----
  | 0, 0 =>
      -- c.addi4spn; nzuimm = 0 is reserved (covers the all-zero
      -- halfword 0x0000, which must be illegal)
      let nzuimm : BitVec 10 :=
        (bits 7 4 h).append
          ((bits 11 2 h).append
            ((bits 5 1 h).append
              ((bits 6 1 h).append (0 : BitVec 2))))
      if nzuimm.toNat = 0 then none else some (.cAddi4spn r2c nzuimm)
  | 0, 1 => some (.cFld r2c r1c uimmD)
  | 0, 2 => some (.cLw r2c r1c uimmW)
  | 0, 3 => some (.cLd r2c r1c uimmD)   -- RV64: c.ld, not c.flw
  | 0, 5 => some (.cFsd r1c r2c uimmD)
  | 0, 6 => some (.cSw r1c r2c uimmW)
  | 0, 7 => some (.cSd r1c r2c uimmD)
  -- ---- Quadrant 1 ----
  | 1, 0 => some (.cAddi rd imm6)        -- incl. c.nop and hints
  | 1, 1 =>
      -- RV64: c.addiw (RV32's c.jal); rd = 0 reserved
      if rd.toNat = 0 then none else some (.cAddiw rd imm6)
  | 1, 2 => some (.cLi rd imm6)          -- rd = 0 is a hint; decode it
  | 1, 3 =>
      if rd.toNat = 2 then
        -- c.addi16sp: nzimm[9|8:7|6|5|4] at h[12|4:3|5|2|6], ×16.
        -- nzimm = 0 is reserved by the ISA spec, but binutils 2.40
        -- ACCEPTS it (0x6101 prints "c.addi16sp sp,0"), so we decode
        -- it too, to match objdump.
        let imm : BitVec 10 :=
          (bits 12 1 h).append
            ((bits 3 2 h).append
              ((bits 5 1 h).append
                ((bits 2 1 h).append
                  ((bits 6 1 h).append (0 : BitVec 4)))))
        some (.cAddi16sp imm)
      else
        -- c.lui; imm = 0 reserved.  rd = 0 is a hint — we decode it
        -- (POLICY: check binutils' printing of the rd=0 hint form).
        if imm6.toNat = 0 then none else some (.cLui rd imm6)
  | 1, 4 =>
      match (bits 10 2 h).toNat with
      | 0 => some (.cSrli r1c imm6)  -- shamt = 0 is a hint; decode it
      | 1 => some (.cSrai r1c imm6)
      | 2 => some (.cAndi r1c imm6)
      | _ =>
          -- 3: register-register group
          match bit 12 h, (bits 5 2 h).toNat with
          | false, 0 => some (.cSub r1c r2c)
          | false, 1 => some (.cXor r1c r2c)
          | false, 2 => some (.cOr r1c r2c)
          | false, _ => some (.cAnd r1c r2c)
          | true, 0 => some (.cSubw r1c r2c)
          | true, 1 => some (.cAddw r1c r2c)
          | true, _ => none  -- reserved
  | 1, 5 =>
      -- c.j: imm[11|4|9:8|10|6|7|3:1|5] at h[12|11|10:9|8|7|6|5:3|2]
      some (.cJ ((bits 12 1 h).append
        ((bits 8 1 h).append
          ((bits 9 2 h).append
            ((bits 6 1 h).append
              ((bits 7 1 h).append
                ((bits 2 1 h).append
                  ((bits 11 1 h).append
                    ((bits 3 3 h).append (0 : BitVec 1))))))))))
  | 1, 6 | 1, 7 =>
      -- c.beqz/c.bnez: imm[8|4:3|7:6|2:1|5] at h[12|11:10|6:5|4:3|2]
      let imm : BitVec 9 :=
        (bits 12 1 h).append
          ((bits 5 2 h).append
            ((bits 2 1 h).append
              ((bits 10 2 h).append
                ((bits 3 2 h).append (0 : BitVec 1)))))
      if f3 = 6 then some (.cBeqz r1c imm) else some (.cBnez r1c imm)
  -- ---- Quadrant 2 ----
  | 2, 0 => some (.cSlli rd imm6)        -- rd = 0 / shamt = 0: hints
  | 2, 1 =>
      -- c.fldsp: uimm[5|4:3|8:6] at h[12|6:5|4:2], ×8
      some (.cFldsp rd ((bits 2 3 h).append
        ((bits 12 1 h).append ((bits 5 2 h).append (0 : BitVec 3)))))
  | 2, 2 =>
      -- c.lwsp: uimm[5|4:2|7:6] at h[12|6:4|3:2], ×4; rd = 0 reserved
      if rd.toNat = 0 then none
      else some (.cLwsp rd ((bits 2 2 h).append
        ((bits 12 1 h).append ((bits 4 3 h).append (0 : BitVec 2)))))
  | 2, 3 =>
      -- c.ldsp; rd = 0 reserved
      if rd.toNat = 0 then none
      else some (.cLdsp rd ((bits 2 3 h).append
        ((bits 12 1 h).append ((bits 5 2 h).append (0 : BitVec 3)))))
  | 2, 4 =>
      if bit 12 h then
        if rs2.toNat = 0 then
          if rd.toNat = 0 then some .cEbreak else some (.cJalr rd)
        else some (.cAdd rd rs2)   -- rd = 0 hint; decode
      else
        if rs2.toNat = 0 then
          -- c.jr; rs1 = 0 reserved
          if rd.toNat = 0 then none else some (.cJr rd)
        else some (.cMv rd rs2)   -- rd = 0 hint; decode
  | 2, 5 =>
      -- c.fsdsp: uimm[5:3|8:6] at h[12:10|9:7], ×8
      some (.cFsdsp rs2 ((bits 7 3 h).append
        ((bits 10 3 h).append (0 : BitVec 3))))
  | 2, 6 =>
      -- c.swsp: uimm[5:2|7:6] at h[12:9|8:7], ×4
      some (.cSwsp rs2 ((bits 7 2 h).append
        ((bits 9 4 h).append (0 : BitVec 2))))
  | 2, 7 =>
      -- c.sdsp
      some (.cSdsp rs2 ((bits 7 3 h).append
        ((bits 10 3 h).append (0 : BitVec 3))))
  -- Quadrant 3 = low bits 11: a 32-bit instruction, not compressed.
  | _, _ => none

/-! ## Expansion into the base AST (total). -/

def x0 : reg := 0
def x1 : reg := 1
def x2 : reg := 2

def expandC : CInstr → Instr
  | .cAddi4spn rd' nzuimm => .opImm .ADD (creg rd') x2 (zext 12 nzuimm)
  | .cFld rd' rs1' uimm => .fLoad .D (creg rd') (creg rs1') (zext 12 uimm)
  | .cLw rd' rs1' uimm => .load .SZ4 true (creg rd') (creg rs1') (zext 12 uimm)
  | .cLd rd' rs1' uimm => .load .SZ8 true (creg rd') (creg rs1') (zext 12 uimm)
  | .cFsd rs1' rs2' uimm => .fStore .D (creg rs1') (creg rs2') (zext 12 uimm)
  | .cSw rs1' rs2' uimm => .store .SZ4 (creg rs1') (creg rs2') (zext 12 uimm)
  | .cSd rs1' rs2' uimm => .store .SZ8 (creg rs1') (creg rs2') (zext 12 uimm)
  | .cAddi rd imm => .opImm .ADD rd rd (sext 12 imm)
  | .cAddiw rd imm => .opImm32 rd rd (sext 12 imm)
  | .cLi rd imm => .opImm .ADD rd x0 (sext 12 imm)
  | .cAddi16sp imm => .opImm .ADD x2 x2 (sext 12 imm)  -- imm is ×16 already
  | .cLui rd imm => .lui rd (sext 20 imm)   -- 6-bit nzimm sexts into U-imm
  | .cSrli rd' sh => .shiftImm .SRL (creg rd') (creg rd') sh
  | .cSrai rd' sh => .shiftImm .SRA (creg rd') (creg rd') sh
  | .cAndi rd' imm => .opImm .AND (creg rd') (creg rd') (sext 12 imm)
  | .cSub rd' rs2' => .op .SUB (creg rd') (creg rd') (creg rs2')
  | .cXor rd' rs2' => .op .XOR (creg rd') (creg rd') (creg rs2')
  | .cOr rd' rs2' => .op .OR (creg rd') (creg rd') (creg rs2')
  | .cAnd rd' rs2' => .op .AND (creg rd') (creg rd') (creg rs2')
  | .cSubw rd' rs2' => .op32 .SUB (creg rd') (creg rd') (creg rs2')
  | .cAddw rd' rs2' => .op32 .ADD (creg rd') (creg rd') (creg rs2')
  | .cJ imm => .jal x0 (sext 21 imm)
  | .cBeqz rs1' imm => .branch .EQ (creg rs1') x0 (sext 13 imm)
  | .cBnez rs1' imm => .branch .NE (creg rs1') x0 (sext 13 imm)
  | .cSlli rd sh => .shiftImm .SLL rd rd sh
  | .cFldsp rd uimm => .fLoad .D rd x2 (zext 12 uimm)
  | .cLwsp rd uimm => .load .SZ4 true rd x2 (zext 12 uimm)
  | .cLdsp rd uimm => .load .SZ8 true rd x2 (zext 12 uimm)
  | .cJr rs1 => .jalr x0 rs1 0
  | .cMv rd rs2 => .op .ADD rd x0 rs2
  | .cEbreak => .ebreak
  | .cJalr rs1 => .jalr x1 rs1 0
  | .cAdd rd rs2 => .op .ADD rd rd rs2
  | .cFsdsp rs2 uimm => .fStore .D x2 rs2 (zext 12 uimm)
  | .cSwsp rs2 uimm => .store .SZ4 x2 rs2 (zext 12 uimm)
  | .cSdsp rs2 uimm => .store .SZ8 x2 rs2 (zext 12 uimm)

/-- Driver convenience: decode either width from a 32-bit fetch.
    Returns the instruction and its length in bytes (2 or 4). -/
def decodeAny (w : BitVec 32) : Option (Instr × Int) :=
  if (bits 0 2 w).toNat = 3 then
    match decode w with
    | some i => some (i, 4)
    | none => none
  else
    match decode16 (bits 0 16 w) with
    | some c => some (expandC c, 2)
    | none => none

/-! ## Architecturally defined-illegal encodings

`decodeAny` returning `none` covers two different kinds of word: bit
patterns this decoder does not model (reserved or unallocated encoding
space, which a future extension may claim), and the one pattern the
unprivileged ISA DEFINES to be an illegal instruction in every
implementation, under every extension: an instruction whose bits [15:0]
are all zeros ("Encodings with bits [15:0] all zeros are defined as
illegal instructions" -- RISC-V unprivileged spec, Expanded
Instruction-Length Encoding).  Fetching such a parcel raises an
illegal-instruction trap on real hardware; under Linux the process takes
SIGILL.

`isDefinedIllegal` recognizes exactly that pattern, and is deliberately
conservative about everything else: reserved opcode space, prefixes
announcing encodings longer than 32 bits (including the all-ones parcel
-- the spec makes all-ones illegal only across all ILEN bits, which a
32-bit window cannot see), and HINT-adjacent code points are all NOT
defined-illegal.  Only the upper halfword of `w` is ignored: an all-zero
low parcel is a complete 16-bit illegal instruction on its own, whatever
follows it. -/
def isDefinedIllegal (w : BitVec 32) : Bool :=
  (bits 0 16 w).toNat = 0

end LinuxSem.Riscv
