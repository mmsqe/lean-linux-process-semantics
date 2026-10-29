/-
  * LinuxProcessSem.Checks.RiscvAlignment — instruction-fetch alignment

  Regression checks for the IALIGN=32 gate in [fetch_word].  The
  misaligned addresses below are deliberately mapped, executable, and
  backed by enough bytes: they would all be readable through
  [code_read], so only the PC-alignment rule can make the fetch and
  step fail.

  [fetch_word] gates on [addr mod 2], not [addr mod 4]: with compressed
  instructions modeled, [pc ≡ 2 (mod 4)] is a legal (halfword-aligned)
  fetch address, so only the odd residues below are actually rejected.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n` and `Z_to_bv n z` is `BitVec.ofInt n z`; a segment's bytes
  are stored as a `String`.  Every `Example name : ...` check
  is a `theorem` with the same name here.

  (closed computations).  The convention is `by decide`,
  which closes every goal whose type has a `DecidableEq` instance
  (`Option`/`List`/`BitVec`).  The goals stated as an equality of
  `machine_result machine_state` values have none — `machine_state` has
  function-typed fields (`ms_mem`, `ms_rom`), so neither it nor
  `machine_result machine_state` is decidable — and there the same
  computation is done by the kernel and the goal is closed by `rfl`,
  exactly what `reflexivity` after such a computation establishes.  The constructors of `machine_result` are spelled
  `.MachineFault` / `.MachineOk` in statements for the namespace reason
  recorded in `Checks/RiscvCompressedFetch`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics

set_option autoImplicit false

namespace LinuxSem.Checks.RiscvAlignment

open LinuxSem.Riscv (word byte bvmap_empty)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- Two aligned instructions: ECALL at [0x100], then ADDI x0,x0,0 at
    [0x104].  Eight bytes also make every four-byte read starting at
    [0x101], [0x102], or [0x103] stay within the executable segment. -/
def alignment_segment : Segment where
  seg_base := 0x100
  seg_size := 8
  seg_perms := "r-x"
  seg_bytes := ["7300000013000000"]

def alignment_segments : List Segment := [alignment_segment]

def alignment_state (pc : word) : machine_state where
  ms_regs := bvmap_empty
  ms_fregs := bvmap_empty
  ms_pc_val := pc
  ms_svc_pending := none
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun _ => none
  ms_rom := fun _ => none

/-- Each misaligned range is otherwise a successful instruction-memory
    read.  These checks keep the tests from passing because of a fixture
    boundary or permission mistake instead of the alignment gate. -/
theorem code_read_misaligned_mod_1_is_mapped :
    code_read alignment_segments (BitVec.ofInt 64 0x101) 4
      = some [BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0,
              BitVec.ofInt 8 0x13] := by decide

theorem code_read_misaligned_mod_2_is_mapped :
    code_read alignment_segments (BitVec.ofInt 64 0x102) 4
      = some [BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0x13,
              BitVec.ofInt 8 0] := by decide

theorem code_read_misaligned_mod_3_is_mapped :
    code_read alignment_segments (BitVec.ofInt 64 0x103) 4
      = some [BitVec.ofInt 8 0, BitVec.ofInt 8 0x13, BitVec.ofInt 8 0,
              BitVec.ofInt 8 0] := by decide

/-- Aligned fetches remain unchanged at both instruction boundaries. -/
theorem fetch_aligned_ecall :
    fetch_word alignment_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x73) := by decide

theorem fetch_aligned_addi :
    fetch_word alignment_segments (BitVec.ofInt 64 0x104)
      = some (BitVec.ofInt 32 0x13) := by decide

/-- Odd addresses fault even though the underlying four-byte range is
    executable and mapped; [pc ≡ 2 (mod 4)] is halfword-aligned and
    therefore a legal (compressed-instruction) fetch address, so it
    reads the four-byte word straddling the two instructions instead
    of faulting. -/
theorem fetch_misaligned_mod_1 :
    fetch_word alignment_segments (BitVec.ofInt 64 0x101) = none := by decide

theorem fetch_halfword_aligned_mod_2 :
    fetch_word alignment_segments (BitVec.ofInt 64 0x102)
      = some (BitVec.ofInt 32 0x130000) := by decide

theorem fetch_misaligned_mod_3 :
    fetch_word alignment_segments (BitVec.ofInt 64 0x103) = none := by decide

/-- Pin the externally visible machine-step behavior, not just the helper:
    a valid aligned instruction steps, while each misaligned initial PC is
    [MachineFault]. -/
theorem step_aligned_succeeds :
    (match step alignment_segments
            (alignment_state (BitVec.ofInt 64 0x100)) with
     | .MachineOk _ => True
     | _ => False) := by
  -- The goal is a `match` on a value with no `DecidableEq`
  -- (see the file header), so there is no `Decidable` instance for `by
  -- decide` to use; `show` performs the same computation definitionally.
  show True
  trivial

theorem step_misaligned_mod_1 :
    step alignment_segments (alignment_state (BitVec.ofInt 64 0x101))
      = .MachineFault := by rfl

/-- The word fetched at this halfword-aligned PC is [0x130000], whose
    LOW parcel is the all-zero halfword the ISA defines illegal
    ([DecodeC.isDefinedIllegal]), so the step faults through the
    defined-illegal path rather than the alignment gate: real hardware
    traps on this parcel too (SIGILL), so it is a [MachineFault] like
    the misaligned fetches around it — not [MachineUnmodeled].  (See
    [Checks.RiscvDefinedIllegal] for the classification checks proper.) -/
theorem step_halfword_aligned_mod_2 :
    step alignment_segments (alignment_state (BitVec.ofInt 64 0x102))
      = .MachineFault := by rfl

theorem step_misaligned_mod_3 :
    step alignment_segments (alignment_state (BitVec.ofInt 64 0x103))
      = .MachineFault := by rfl

end LinuxSem.Checks.RiscvAlignment
