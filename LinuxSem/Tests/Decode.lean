/-
  * Decoder conformance tests.

  These are the decoder's own sanity checks, transcribed as ordinary
  Lean theorems checked by `decide`, so they run on every build.
-/
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC

namespace LinuxSem.Riscv.Tests

open LinuxSem.Riscv

/-! ### Decode.v checks -/

example : decode 0x00000013 = some (.opImm .ADD 0 0 0) := by decide

example : decode 0x00c58533 = some (.op .ADD 10 11 12) := by decide

example : decode 0xfe0796e3 = some (.branch .NE 15 0 (BitVec.ofInt 13 (-20))) := by decide

example : decode 0x00153513 = some (.opImm .SLTU 10 10 1) := by decide

example : decode 0x02b4d53b = some (.mul32 .DIVU 10 9 11) := by decide

example : decode 0x140536af = some (.lr .D true false 13 10) := by decide

example : decode 0x00000073 = some .ecall := by decide
example : decode 0x00100073 = some .ebreak := by decide
example : decode 0x00200073 = none := by decide

example : decode 0x0ff0000f = some (.fence 0 15 15 0 0) := by decide
example : decode 0x8330000f = some (.fence 8 3 3 0 0) := by decide
example : decode 0x0000100f = some (.fenceI 0 0 0) := by decide

-- The fields the spec tells an implementation to ignore: fence, fence.i
-- and the exact fcvt forms decode whatever those fields hold.  binutils
-- objdump rejects all seven words below; QEMU executes them.
example : decode 0x0ff0008f = some (.fence 0 15 15 1 0) := by decide
example : decode 0x0ff0080f = some (.fence 0 15 15 16 0) := by decide
example : decode 0x8120000f = some (.fence 8 1 2 0 0) := by decide
example : decode 0x0010100f = some (.fenceI 0 0 1) := by decide
example : decode 0x00a0100f = some (.fenceI 0 0 10) := by decide

example : decode 0x341022f3 = some (.csr .RS 5 0 0x341) := by decide

example : decode 0x00c58553 = some (.fari .ADD .S 10 11 12 0) := by decide

-- fcvt.s.s / fcvt.d.d are illegal
example : decode 0x40058553 = none := by decide
example : decode 0x42158553 = none := by decide

-- ...but a widening conversion decodes with a free rm (spec: "implementations
-- must treat the rm field as usual"); binutils rejects both words below
example : decode 0xd2001053 = some (.fcvt .D .W 0 0 1) := by decide
example : decode 0x4201f553 = some (.fcvt .D .S 10 3 7) := by decide

-- Low 2 bits <> 11: never a valid 32-bit instruction
example : decode 0x00000001 = none := by decide
example : decode 0x0000852a = none := by decide

/-! ### DecodeC.v checks -/

example : decode16 0x0000 = none := by decide
example : decode16 0x4108 = some (.cLw 2 2 0) := by decide
example : expandC (.cLw 2 2 0) = .load .SZ4 true 10 10 0 := by decide
example : decode16 0x0001 = some (.cAddi 0 0) := by decide
example : decode16 0x852a = some (.cMv 10 10) := by decide
example : decode16 0x8082 = some (.cJr 1) := by decide
example : expandC (.cJr 1) = .jalr 0 1 0 := by decide
example : decode16 0x9002 = some .cEbreak := by decide
example : decode16 0x1141 = some (.cAddi 2 (BitVec.ofInt 6 (-16))) := by decide
example : decode16 0xe022 = some (.cSdsp 8 0) := by decide
example : decode16 0x6505 = some (.cLui 10 1) := by decide
example : expandC (.cLui 10 1) = .lui 10 1 := by decide
example : decode16 0x7139 = some (.cAddi16sp (BitVec.ofInt 10 (-64))) := by decide

-- c.addi16sp with nzimm = 0 is reserved (QEMU traps it)
example : decode16 0x6101 = none := by decide
-- ...but a nonzero nzimm still decodes, with bit 12 clear or set
example : decode16 0x6141 = some (.cAddi16sp (BitVec.ofInt 10 16)) := by decide
example : decode16 0x7101 = some (.cAddi16sp (BitVec.ofInt 10 (-512))) := by decide

-- Low bits 11: not a compressed instruction
example : decode16 0x0013 = none := by decide

-- decodeAny picks the right width
example : decodeAny 0x00000013 = some (.opImm .ADD 0 0 0, 4) := by decide
example : decodeAny 0x00008082 = some (.jalr 0 1 0, 2) := by decide

-- Defined-illegal: exactly the all-zero low parcel, upper bits ignored
example : isDefinedIllegal 0x00000000 = true := by decide
example : isDefinedIllegal 0xffff0000 = true := by decide
-- ...and nothing decodeAny accepts, nor merely-reserved space
example : isDefinedIllegal 0x00000013 = false := by decide
example : isDefinedIllegal 0x00000001 = false := by decide
example : isDefinedIllegal 0xffffffff = false := by decide
-- A defined-illegal word is (a fortiori) undecodable
example : decodeAny 0x00000000 = none := by decide
example : decodeAny 0xffff0000 = none := by decide


/-! ### Additional immediate-field checks (store and I-type) -/

-- sd a0, 8(sp): imm[11:5]=0, rs2=10, rs1=2, funct3=3, imm[4:0]=8
example : decode 0x00A13423 = some (.store .SZ8 2 10 8) := by decide

-- addi a0, a0, -1
example : decode 0xfff50513 = some (.opImm .ADD 10 10 (BitVec.ofInt 12 (-1))) := by decide

-- jal ra, +8
example : decode 0x008000ef = some (.jal 1 8) := by decide

-- c.sdsp a0, 8(sp)
example : decode16 0xE42A = some (.cSdsp 10 8) := by decide
example : expandC (.cSdsp 10 8) = .store .SZ8 2 10 8 := by decide

-- c.addi4spn a0, sp, 8
example : decode16 0x0028 = some (.cAddi4spn 2 8) := by decide
example : expandC (.cAddi4spn 2 8) = .opImm .ADD 10 2 8 := by decide


-- lui a0, 0x12345
example : decode 0x12345537 = some (.lui 10 0x12345) := by decide

-- lw a0, 4(a1)
example : decode 0x0045A503 = some (.load .SZ4 true 10 11 4) := by decide

-- addiw a0, a0, -1
example : decode 0xfff5051b = some (.opImm32 10 10 (BitVec.ofInt 12 (-1))) := by decide

-- auipc a0, 0x1
example : decode 0x00001517 = some (.auipc 10 1) := by decide

end LinuxSem.Riscv.Tests
