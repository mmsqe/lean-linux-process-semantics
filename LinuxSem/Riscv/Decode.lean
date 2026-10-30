/-
  * Decode: the 32-bit RV64IMAFD_Zicsr_Zifencei decoder.

  `decode w = none` means "not a valid 32-bit instruction".  What counts
  as valid is the RISC-V specification (RV64GC) and QEMU user mode, the
  references this tree names for instructions.  binutils objdump is
  narrower in places; those cases are flagged inline as policy notes for
  a comparison with objdump.

  Immediates are kept at their encoded width, sign bit included
  (see Instr.lean); no sign extension happens here.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr

namespace LinuxSem.Riscv

/-! ## Instruction fields -/

/-- Register fields. -/
def f_rd (w : BitVec 32) : reg := bits 7 5 w
def f_rs1 (w : BitVec 32) : reg := bits 15 5 w
def f_rs2 (w : BitVec 32) : reg := bits 20 5 w
def f_rs3 (w : BitVec 32) : reg := bits 27 5 w

/-- Immediates, reassembled at encoded width. -/
def immI (w : BitVec 32) : BitVec 12 := bits 20 12 w

def immS (w : BitVec 32) : BitVec 12 :=
  (bits 25 7 w).append (bits 7 5 w)

def immB (w : BitVec 32) : BitVec 13 :=
  (bits 31 1 w).append
    ((bits 7 1 w).append
      ((bits 25 6 w).append
        ((bits 8 4 w).append (0 : BitVec 1))))

def immU (w : BitVec 32) : BitVec 20 := bits 12 20 w

def immJ (w : BitVec 32) : BitVec 21 :=
  (bits 31 1 w).append
    ((bits 12 8 w).append
      ((bits 20 1 w).append
        ((bits 21 10 w).append (0 : BitVec 1))))

/-! ## The decoder -/

/-- Decode a 32-bit instruction word. -/
def decode (w : BitVec 32) : Option Instr :=
  let opc := (bits 0 7 w).toNat
  let rd := f_rd w
  let f3 := (bits 12 3 w).toNat
  let rs1 := f_rs1 w
  let rs2 := f_rs2 w
  let f7 := (bits 25 7 w).toNat
  let rm : BitVec 3 := bits 12 3 w
  match opc with
  -- Words whose low two bits are not 11 fall through to `none` below,
  -- as do the 48-bit-and-up prefixes (bits[4:2] = 111).
  | 0x37 => some (.lui rd (immU w))
  | 0x17 => some (.auipc rd (immU w))
  | 0x6F => some (.jal rd (immJ w))
  | 0x67 => if f3 = 0 then some (.jalr rd rs1 (immI w)) else none
  | 0x63 =>
      -- BRANCH
      let br (c : BranchCond) := some (.branch c rs1 rs2 (immB w))
      match f3 with
      | 0 => br .EQ  | 1 => br .NE
      | 4 => br .LT  | 5 => br .GE
      | 6 => br .LTU | 7 => br .GEU
      | _ => none
  | 0x03 =>
      -- LOAD; funct3 = 7 (an "ldu") does not exist
      let ld (sz : MSize) (sg : Bool) := some (.load sz sg rd rs1 (immI w))
      match f3 with
      | 0 => ld .SZ1 true  | 1 => ld .SZ2 true
      | 2 => ld .SZ4 true  | 3 => ld .SZ8 true
      | 4 => ld .SZ1 false | 5 => ld .SZ2 false | 6 => ld .SZ4 false
      | _ => none
  | 0x23 =>
      -- STORE
      let st (sz : MSize) := some (.store sz rs1 rs2 (immS w))
      match f3 with
      | 0 => st .SZ1 | 1 => st .SZ2 | 2 => st .SZ4 | 3 => st .SZ8
      | _ => none
  | 0x13 =>
      -- OP-IMM; RV64 shifts have 6-bit shamt (bit 25 may be set)
      let oi (op : AluOp) := some (.opImm op rd rs1 (immI w))
      let sh : BitVec 6 := bits 20 6 w
      match f3 with
      | 0 => oi .ADD | 2 => oi .SLT | 3 => oi .SLTU
      | 4 => oi .XOR | 6 => oi .OR  | 7 => oi .AND
      | 1 =>
          -- slli: bits[31:26] must be 000000
          if (bits 26 6 w).toNat = 0 then some (.shiftImm .SLL rd rs1 sh) else none
      | 5 =>
          match (bits 26 6 w).toNat with
          | 0x00 => some (.shiftImm .SRL rd rs1 sh)
          | 0x10 => some (.shiftImm .SRA rd rs1 sh)
          | _ => none
      | _ => none
  | 0x1B =>
      -- OP-IMM-32; 5-bit shamt, bit 25 must be 0 (checked via funct7)
      let sh5 : BitVec 5 := bits 20 5 w
      match f3 with
      | 0 => some (.opImm32 rd rs1 (immI w))
      | 1 => if f7 = 0 then some (.shiftImm32 .SLL rd rs1 sh5) else none
      | 5 =>
          match f7 with
          | 0x00 => some (.shiftImm32 .SRL rd rs1 sh5)
          | 0x20 => some (.shiftImm32 .SRA rd rs1 sh5)
          | _ => none
      | _ => none
  | 0x33 =>
      -- OP: funct7 checked exactly (0x00 / 0x20 / 0x01 = M)
      let op (o : AluOp) := some (.op o rd rs1 rs2)
      let ml (o : MulOp) := some (.mul o rd rs1 rs2)
      match f7, f3 with
      | 0x00, 0 => op .ADD | 0x20, 0 => op .SUB
      | 0x00, 1 => op .SLL
      | 0x00, 2 => op .SLT | 0x00, 3 => op .SLTU
      | 0x00, 4 => op .XOR
      | 0x00, 5 => op .SRL | 0x20, 5 => op .SRA
      | 0x00, 6 => op .OR  | 0x00, 7 => op .AND
      | 0x01, 0 => ml .MUL    | 0x01, 1 => ml .MULH
      | 0x01, 2 => ml .MULHSU | 0x01, 3 => ml .MULHU
      | 0x01, 4 => ml .DIV    | 0x01, 5 => ml .DIVU
      | 0x01, 6 => ml .REM    | 0x01, 7 => ml .REMU
      | _, _ => none
  | 0x3B =>
      -- OP-32; the M subset here is only mulw/divw/divuw/remw/remuw
      let op (o : AluOp) := some (.op32 o rd rs1 rs2)
      let ml (o : MulOp) := some (.mul32 o rd rs1 rs2)
      match f7, f3 with
      | 0x00, 0 => op .ADD | 0x20, 0 => op .SUB
      | 0x00, 1 => op .SLL
      | 0x00, 5 => op .SRL | 0x20, 5 => op .SRA
      | 0x01, 0 => ml .MUL
      | 0x01, 4 => ml .DIV   | 0x01, 5 => ml .DIVU
      | 0x01, 6 => ml .REM   | 0x01, 7 => ml .REMU
      | _, _ => none
  | 0x0F =>
      -- MISC-MEM.  The unprivileged spec reserves fence's rd and
      -- rs1 fields and says base implementations SHALL IGNORE
      -- them, and that reserved fm and predecessor/successor
      -- settings are to be treated as a fence with fm = 0000
      -- (src/unpriv/rv32.adoc, norm:fence_unused_flds_rsv);
      -- Zifencei says the same of fence.i's funct12, rs1 and rd
      -- (src/unpriv/zifencei.adoc, norm:fence-i_rsv).  QEMU user
      -- mode decodes both that way (target/riscv/insn32.decode:
      -- "fence  ---- pred:4 succ:4 ----- 000 ----- 0001111" and
      -- "fence_i  ---- ---- ---- ----- 001 ----- 0001111").  The
      -- fields are kept raw; `Sem.exec` runs every fence as a
      -- no-op (one hart), which is what "treat as fm = 0000"
      -- gives here.
      -- POLICY: binutils 2.4x objdump is narrower — it wants
      -- rd = rs1 = 0 and either fm = 0 (any pred/succ, 0 printing
      -- as "unknown") or the exact fm=8, pred=succ=rw word
      -- (fence.tso), and it takes fence.i only as 0x0000100f.  A
      -- comparison with objdump must special-case the words it
      -- rejects.
      match f3 with
      | 0 => some (.fence (bits 28 4 w) (bits 24 4 w) (bits 20 4 w) rd rs1)
      | 1 => some (.fenceI rd rs1 (immI w))
      | _ => none  -- funct3 = 2 (Zicbom/Zicboz) is out of scope
  | 0x73 =>
      -- SYSTEM
      match f3 with
      | 0 =>
          -- Only ecall/ebreak; privileged instructions are out of scope
          -- and return none.  POLICY (confirmed): binutils objdump for
          -- plain rv64 DOES print mret/wfi/sfence.vma etc. — a
          -- comparison with objdump must expect them, or this
          -- decoder must be extended.
          match w.toNat with
          | 0x00000073 => some .ecall
          | 0x00100073 => some .ebreak
          | _ => none
      | 1 => some (.csr .RW rd rs1 (bits 20 12 w))
      | 2 => some (.csr .RS rd rs1 (bits 20 12 w))
      | 3 => some (.csr .RC rd rs1 (bits 20 12 w))
      | 5 => some (.csrI .RW rd rs1 (bits 20 12 w))
      | 6 => some (.csrI .RS rd rs1 (bits 20 12 w))
      | 7 => some (.csrI .RC rd rs1 (bits 20 12 w))
      | _ => none  -- funct3 = 4
  | 0x2F =>
      -- AMO
      let aq := bit 26 w
      let rl := bit 25 w
      let go (aw : AWidth) :=
        let am (o : AmoOp) := some (.amo o aw aq rl rd rs1 rs2)
        match (bits 27 5 w).toNat with
        | 0x00 => am .ADD
        | 0x01 => am .SWAP
        | 0x02 =>
            -- lr: rs2 must be 0 (binutils rejects rs2 <> 0)
            if rs2.toNat = 0 then some (.lr aw aq rl rd rs1) else none
        | 0x03 => some (.sc aw aq rl rd rs1 rs2)
        | 0x04 => am .XOR
        | 0x08 => am .OR
        | 0x0C => am .AND
        | 0x10 => am .MIN
        | 0x14 => am .MAX
        | 0x18 => am .MINU
        | 0x1C => am .MAXU
        | _ => none
      match f3 with
      | 2 => go .W
      | 3 => go .D
      | _ => none
  | 0x07 =>
      -- LOAD-FP: flw/fld only
      match f3 with
      | 2 => some (.fLoad .S rd rs1 (immI w))
      | 3 => some (.fLoad .D rd rs1 (immI w))
      | _ => none
  | 0x27 =>
      -- STORE-FP
      match f3 with
      | 2 => some (.fStore .S rs1 rs2 (immS w))
      | 3 => some (.fStore .D rs1 rs2 (immS w))
      | _ => none
  | 0x43 | 0x47 | 0x4B | 0x4F =>
      -- FMA group; fmt = bits[26:25]
      let mo := match opc with
                | 0x43 => FmaOp.MADD  | 0x47 => FmaOp.MSUB
                | 0x4B => FmaOp.NMSUB | _    => FmaOp.NMADD
      -- POLICY: rm kept raw; the reserved rm values 5/6 still decode here —
      -- check binutils' policy and align in the differ.
      match (bits 25 2 w).toNat with
      | 0 => some (.fma mo .S rd rs1 rs2 (f_rs3 w) rm)
      | 1 => some (.fma mo .D rd rs1 rs2 (f_rs3 w) rm)
      | _ => none  -- fmt 10/11 illegal (no Q/H)
  | 0x53 =>
      -- OP-FP: funct7 dispatch.  rm kept raw for arith/sqrt/cvt
      -- (POLICY: reserved rm values 5/6 accepted — differ to align).
      let cvtInt :=  -- integer FcvtTy selected by the rs2 field
        match rs2.toNat with
        | 0 => some FcvtTy.W | 1 => some FcvtTy.WU
        | 2 => some FcvtTy.L | 3 => some FcvtTy.LU
        | _ => none
      match f7 with
      | 0x00 => some (.fari .ADD .S rd rs1 rs2 rm)
      | 0x01 => some (.fari .ADD .D rd rs1 rs2 rm)
      | 0x04 => some (.fari .SUB .S rd rs1 rs2 rm)
      | 0x05 => some (.fari .SUB .D rd rs1 rs2 rm)
      | 0x08 => some (.fari .MUL .S rd rs1 rs2 rm)
      | 0x09 => some (.fari .MUL .D rd rs1 rs2 rm)
      | 0x0C => some (.fari .DIV .S rd rs1 rs2 rm)
      | 0x0D => some (.fari .DIV .D rd rs1 rs2 rm)
      | 0x2C => if rs2.toNat = 0 then some (.fsqrt .S rd rs1 rm) else none
      | 0x2D => if rs2.toNat = 0 then some (.fsqrt .D rd rs1 rm) else none
      | 0x10 | 0x11 =>
          let fmt := if f7 = 0x10 then FFmt.S else FFmt.D
          match f3 with
          | 0 => some (.fsgnj .SGNJ fmt rd rs1 rs2)
          | 1 => some (.fsgnj .SGNJN fmt rd rs1 rs2)
          | 2 => some (.fsgnj .SGNJX fmt rd rs1 rs2)
          | _ => none
      | 0x14 | 0x15 =>
          let fmt := if f7 = 0x14 then FFmt.S else FFmt.D
          match f3 with
          | 0 => some (.fminmax .MIN fmt rd rs1 rs2)
          | 1 => some (.fminmax .MAX fmt rd rs1 rs2)
          | _ => none
      | 0x50 | 0x51 =>
          -- fcmp: feq/flt/fle = funct3 2/1/0
          let fmt := if f7 = 0x50 then FFmt.S else FFmt.D
          match f3 with
          | 2 => some (.fcmp .EQ fmt rd rs1 rs2)
          | 1 => some (.fcmp .LT fmt rd rs1 rs2)
          | 0 => some (.fcmp .LE fmt rd rs1 rs2)
          | _ => none
      | 0x60 =>
          -- fcvt.{w,wu,l,lu}.s
          match cvtInt with
          | some dst => some (.fcvt dst .S rd rs1 rm) | none => none
      | 0x61 =>
          -- fcvt.{w,wu,l,lu}.d
          match cvtInt with
          | some dst => some (.fcvt dst .D rd rs1 rm) | none => none
      | 0x68 =>
          -- fcvt.s.{w,wu,l,lu}
          match cvtInt with
          | some src => some (.fcvt .S src rd rs1 rm) | none => none
      | 0x69 =>
          -- fcvt.d.{w,wu,l,lu}.  fcvt.d.w/fcvt.d.wu are exact, but
          -- the spec still decodes rm as usual: "Some instructions,
          -- including widening conversions, have the rm field but
          -- are nevertheless mathematically unaffected by the
          -- rounding mode; software should set their rm field to
          -- RNE (000) but implementations must treat the rm field
          -- as usual (in particular, with regard to decoding legal
          -- vs. reserved encodings)" (src/unpriv/f-st-ext.adoc,
          -- norm:roundingmode_unaffected_rm_decode).  QEMU decodes
          -- all four with a free rm (insn32.decode @r2_rm).  The
          -- reserved modes 5/6 are rejected by `Sem.exec`, not
          -- here.
          -- POLICY: binutils objdump is narrower — it rejects
          -- rm <> 0 on fcvt.d.w/fcvt.d.wu (0xd205c553 is invalid
          -- to objdump); a comparison must special-case it.
          match cvtInt with
          | some src => some (.fcvt .D src rd rs1 rm)
          | none => none
      | 0x20 =>
          -- fcvt.s.d (rs2 = 1); rs2 = 0 would be fcvt.s.s: illegal
          if rs2.toNat = 1 then some (.fcvt .S .D rd rs1 rm) else none
      | 0x21 =>
          -- fcvt.d.s (rs2 = 0); rs2 = 1 would be fcvt.d.d: illegal.
          -- The conversion is exact, and rm is decoded as usual for
          -- a widening conversion (same spec rule as 0x69 above);
          -- QEMU: @r2_rm.
          -- POLICY: binutils objdump rejects rm <> 0 here
          -- (0x4205c553 invalid) — special-case it in a
          -- comparison.
          if rs2.toNat = 0 then some (.fcvt .D .S rd rs1 rm) else none
      | 0x70 =>
          -- fmv.x.w (f3 = 0) / fclass.s (f3 = 1); rs2 must be 0
          if rs2.toNat = 0 then
            match f3 with
            | 0 => some (.fmv .X_F .S rd rs1)
            | 1 => some (.fclass .S rd rs1)
            | _ => none
          else none
      | 0x71 =>
          -- fmv.x.d / fclass.d
          if rs2.toNat = 0 then
            match f3 with
            | 0 => some (.fmv .X_F .D rd rs1)
            | 1 => some (.fclass .D rd rs1)
            | _ => none
          else none
      | 0x78 =>
          -- fmv.w.x
          if rs2.toNat = 0 && f3 = 0 then some (.fmv .F_X .S rd rs1) else none
      | 0x79 =>
          -- fmv.d.x
          if rs2.toNat = 0 && f3 = 0 then some (.fmv .F_X .D rd rs1) else none
      | _ => none
  | _ => none

end LinuxSem.Riscv
