/-
  * LinuxProcessSem.Checks.RiscvSegmentChunks — segment chunks invisible

  `elf-snapshot` divides a large logical ELF segment into bounded
  primitive strings.  These checks pin the load and fetch behavior at
  the join: the join is not a mapping or permission boundary.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n` and `Z_to_bv n z` is `BitVec.ofInt n z`; a segment's bytes
  are stored as a `String`.  The bytes a check compares against are
  spelled `BitVec.ofInt 8 n` (`Z_to_bv 8 n`), and every
  `Example name : ...` check is a `theorem` with the same name here.

  (closed computations).  The convention is `by decide`.
  Every goal in this file is an equality of `Option` values over
  decidable carriers (`Byte`/`BitVec 8` and `BitVec 32`), so that closes
  all of them.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics

set_option autoImplicit false

namespace LinuxSem.Checks.RiscvSegmentChunks

open LinuxSem.Riscv (word byte)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- One logical segment whose five bytes are split across TWO chunks, so
    that the byte at offset 2 (the first byte of the second chunk) has to
    be found by walking past the first one. -/
def chunked_segment : Segment where
  seg_base := 0x100
  seg_size := 5
  seg_perms := "r-x"
  seg_bytes := ["1122", "334455"]

def chunked_segments : List Segment := [chunked_segment]

/-- The last byte of chunk 0. -/
theorem chunk_join_byte_before :
    segment_byte_at chunked_segment.seg_bytes 1
      = some (BitVec.ofInt 8 0x22) := by decide

/-- The first byte of chunk 1 — the join itself. -/
theorem chunk_join_byte_after :
    segment_byte_at chunked_segment.seg_bytes 2
      = some (BitVec.ofInt 8 0x33) := by decide

/-- A four-byte data read that straddles the join. -/
theorem data_read_crosses_chunk_join :
    memory_read chunked_segments (BitVec.ofInt 64 0x101) 4
      = some [BitVec.ofInt 8 0x22, BitVec.ofInt 8 0x33,
              BitVec.ofInt 8 0x44, BitVec.ofInt 8 0x55] := by decide

/-- A four-byte instruction fetch that straddles the join. -/
theorem instruction_fetch_crosses_chunk_join :
    fetch_word chunked_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x44332211) := by decide

end LinuxSem.Checks.RiscvSegmentChunks
