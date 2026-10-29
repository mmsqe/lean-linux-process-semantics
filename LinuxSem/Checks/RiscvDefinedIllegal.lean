/-
  * LinuxProcessSem.Checks.RiscvDefinedIllegal — defined-illegal encodings fault

  Classification checks for [DecodeC.is_defined_illegal]: a word
  [decode_any] rejects is normally [MachineUnmodeled] (the MODEL gave
  up — it may be a decoder hole), but the all-zero 16-bit parcel is
  defined illegal by the ISA in every implementation, so real hardware
  traps and the process takes SIGILL — a failure the real process also
  suffers, hence [MachineFault] (see the [machine_result] taxonomy in
  [RiscvSemantics]).

  The fixtures pin both sides of the split on the same shape: the same
  segment layout holding all-zero bytes (defined illegal → fault)
  versus all-ones bytes (merely unallocated/reserved space →
  unmodeled).

  The second half of the file is the same split one layer up, where
  the word DECODES.  [is_defined_illegal] is consulted only when
  [decode_any] fails, so it cannot see an architecturally illegal
  instruction that decodes fine — the standing example being GNU as's
  [unimp] (0xc0001073 = csrrw x0, cycle, x0), which is what a
  -fsanitize-trap binary executes when a check fires.  That decision
  belongs to [Sem.exec], which answers [Sem.EDefinedIllegal] and gets
  the same [MachineFault]; the contrast fixtures are the CSR
  instructions on the SAME read-only address that do not write, which
  stay this model's own decline.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n`, `Z_to_bv n z` is `BitVec.ofInt n z`, and the instruction
  words are passed as a `String`.  Every `Example name : ...` check
  is a `theorem` with the same name here.

  (the `Sem` module).  `Riscv.Sem` is taken WITHOUT
  opening its namespace, so that `Sem.step` does not shadow
  `RiscvSemantics.step`; Lean has
  no un-imported module, so the file names
  `LinuxSem.Riscv.Sem` and opens only the one predicate it
  needs, `csr_read_only`, from `LinuxSem.Riscv`.  The
  `step` below is `RiscvSemantics.step`.  This is a naming-only choice.

  (closed computations).  The convention is `by decide`,
  which closes every goal whose type has a `DecidableEq` instance.
  A goal stated as an equality of `machine_result machine_state` values
  has none — `machine_state` has function-typed fields, so neither it
  nor `machine_result machine_state` is decidable — and there the same
  computation is done by the kernel and the goal is closed by `rfl`,
  which is what `reflexivity` after such a computation establishes.  The constructors of `machine_result` are spelled
  `.MachineFault` / `.MachineUnmodeled` in statements for the same
  namespace reason as in `Checks/RiscvCompressedFetch`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
-- NOT opened below: `Sem.step`
-- would shadow [RiscvSemantics.step], which is the function every check
-- below is about.
import LinuxSem.Riscv.Sem

/- `st0` keeps its `segs` parameter even though the
   state does not read it; Lean's `linter.unusedVariables` warns on that,
   so it is switched off for the file rather than renaming the argument
   away from the signature. -/
set_option linter.unusedVariables false

namespace LinuxSem.Checks.RiscvDefinedIllegal

open LinuxSem.Riscv
  (word reg byte decodeAny isDefinedIllegal csr_read_only bvmap_empty)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

def st0 (segs : List Segment) (pc : word) : machine_state where
  ms_regs := bvmap_empty
  ms_fregs := bvmap_empty
  ms_pc_val := pc
  ms_svc_pending := none
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun _ => none
  ms_rom := fun _ => none

/-- A 4-byte executable segment of zeroed memory — the shape a wild jump
    into a zero-filled page lands on, which is exactly why the ISA
    defines the all-zero parcel illegal. -/
def zero_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["00000000"]

def zero_segments : List Segment := [zero_segment]

/-- The fetch itself succeeds — the bytes are mapped and executable —
    so the classification below is [decode_exec]'s, not the fetch
    layer's. -/
theorem zero_fetch_ok :
    fetch_word zero_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0) := by decide

theorem zero_word_undecodable :
    decodeAny (BitVec.ofInt 32 0) = none := by decide

theorem zero_word_defined_illegal :
    isDefinedIllegal (BitVec.ofInt 32 0) = true := by decide

/-- THE CHECK: stepping onto the all-zero word is a fault the real
    process suffers too (SIGILL), not the model giving up. -/
theorem zero_step_fault :
    step zero_segments (st0 zero_segments (BitVec.ofInt 64 0x100))
      = .MachineFault := by rfl

/-- A 2-byte segment holding only the zero parcel: the all-zero halfword
    is a complete 16-bit illegal instruction on its own, so it faults
    even when no further bytes are mapped (the length-correct
    [fetch_tail] path). -/
def zero2_segment : Segment where
  seg_base := 0x100
  seg_size := 2
  seg_perms := "r-x"
  seg_bytes := ["0000"]

def zero2_segments : List Segment := [zero2_segment]

theorem zero2_step_fault :
    step zero2_segments (st0 zero2_segments (BitVec.ofInt 64 0x100))
      = .MachineFault := by rfl

/-- An all-zero LOW parcel under a nonzero upper halfword is still the
    defined-illegal instruction — the parcel is 16 bits long, and the
    following bytes are simply the next (never-reached) parcel. -/
def zerolow_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["00001300"]

def zerolow_segments : List Segment := [zerolow_segment]

theorem zerolow_step_fault :
    step zerolow_segments (st0 zerolow_segments (BitVec.ofInt 64 0x100))
      = .MachineFault := by rfl

/-- CONTRAST: the all-ones word is also undecodable, but the ISA does
    NOT define it illegal from a 32-bit window (all-ones is illegal only
    across all ILEN bits, and the low bits announce a longer encoding a
    future extension could give meaning to) — so it stays the model's
    own limit. -/
def ones_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["ffffffff"]

def ones_segments : List Segment := [ones_segment]

theorem ones_word_not_defined_illegal :
    isDefinedIllegal (BitVec.ofInt 32 0xffffffff) = false := by decide

theorem ones_step_unmodeled :
    step ones_segments (st0 ones_segments (BitVec.ofInt 64 0x100))
      = .MachineUnmodeled := by rfl

/- * Defined-illegal instructions that DECODE

    csr[11:10] = 11 marks a read-only CSR address, and writing one raises
    an illegal-instruction exception in every conforming implementation
    at every privilege level (RISC-V unprivileged spec, CSR Address
    Mapping Conventions; the argument is on [Sem.csr_write_illegal]).
    The address alone settles it, so the rule reaches addresses this
    model does not implement — which is the whole point, since the
    instruction the toolchain picked for "always illegal" names one. -/

/- The predicate reads the two top bits and nothing else, so the cases
   that matter are the boundary and the addresses a reader would expect
   it to claim and it does not. -/
theorem csr_ro_cycle :
    csr_read_only (BitVec.ofInt 12 0xc00) = true := by decide

theorem csr_ro_top :
    csr_read_only (BitVec.ofInt 12 0xfff) = true := by decide

theorem csr_ro_fcsr :
    csr_read_only (BitVec.ofInt 12 0x003) = false := by decide

/-- 0xbff is the last read/WRITE address; 0xc00 the first read-only one. -/
theorem csr_ro_just_below :
    csr_read_only (BitVec.ofInt 12 0xbff) = false := by decide

/-- mstatus is read/write.  Writing it from user mode is illegal too, but
    for a reason about the HART rather than about the instruction, so
    this predicate does not claim it — see [Sem.csr_read_only]. -/
theorem csr_ro_mstatus :
    csr_read_only (BitVec.ofInt 12 0x300) = false := by decide

/-- [unimp] is a well-formed Zicsr instruction: the decoder accepts it,
    and [is_defined_illegal] — which only ever sees words the decoder
    REJECTED — says nothing about it.  These two are why the fault has to
    be issued by [exec]. -/
theorem unimp_decodes :
    (match decodeAny (BitVec.ofInt 32 0xc0001073) with
     | some _ => true
     | none => false) = true := by decide

theorem unimp_not_flagged_by_decode_hook :
    isDefinedIllegal (BitVec.ofInt 32 0xc0001073) = false := by decide

/-- A 4-byte executable segment holding one instruction word, given in
    memory (little-endian) byte order. -/
def word_segment (hex : String) : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := [hex]

def word_segments (hex : String) : List Segment :=
  [word_segment hex]

def step_word (hex : String) : machine_result machine_state :=
  step (word_segments hex) (st0 (word_segments hex) (BitVec.ofInt 64 0x100))

/-- THE CHECK, in the shape the sanitizer emits it: `unimp`, the word a
    -fsanitize-trap check executes when it fires, is the process dying of
    SIGILL — not the model giving up. -/
theorem unimp_step_fault : step_word "731000c0" = .MachineFault := by rfl

/-- The rule is about the write side, not about that one encoding.
    `csrs cycle, x1` (0xc000a073) writes because rs1 /= x0... -/
theorem csrs_readonly_step_fault : step_word "73a000c0" = .MachineFault := by rfl

/-- ...and `csrwi cycle, 1` (0xc000d073) writes because csrrwi always
    does, whatever the immediate. -/
theorem csrwi_readonly_step_fault : step_word "73d000c0" = .MachineFault := by rfl

/-- CONTRAST 1: `rdcycle x1` (0xc00020f3 = csrrs x1, cycle, x0) reads the
    SAME read-only address and rs1 = x0, so it does not write and the
    architecture does not define it illegal.  This model has no [cycle]
    counter, so it declines — and the decline must stay a decline.  A
    rule keyed on the address instead of on the write would fault here,
    claiming a death for an instruction a real process survives. -/
theorem rdcycle_step_unmodeled : step_word "f32000c0" = .MachineUnmodeled := by rfl

/-- CONTRAST 2: the immediate form, `csrrsi x1, cycle, 0` (0xc00060f3).
    uimm = 0 suppresses the write for csrrsi/csrrci exactly as rs1 = x0
    does for csrrs/csrrc, so this is a legal read too. -/
theorem csrrsi_zero_step_unmodeled :
    step_word "f36000c0" = .MachineUnmodeled := by rfl

/-- CONTRAST 3: a write to a read/WRITE address the model does implement
    still retires.  `fscsr x1, x2` (0x003110f3 = csrrw x1, fcsr, x2)
    would be the casualty of a gate that fired on the write alone. -/
theorem fscsr_step_retires :
    (match step_word "f3103100" with
     | .MachineOk _ => true
     | _ => false) = true := by decide

end LinuxSem.Checks.RiscvDefinedIllegal
