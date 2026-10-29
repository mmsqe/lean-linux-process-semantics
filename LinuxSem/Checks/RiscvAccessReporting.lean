/-
  * LinuxProcessSem.Checks.RiscvAccessReporting — exact data reports

  Instruction access reporting is an observation of the authoritative
  interpreter, not a second instruction semantics.  These executable
  checks pin the report emitted for each instruction family that can
  touch data memory: every integer width, both floating-point widths,
  LR/SC, and AMOs.  The cross-page checks use deliberately misaligned
  eight-byte operations; each report retains the one architectural
  range rather than rounding or splitting it.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n` and `Z_to_bv n z` is `BitVec.ofInt n z`; a segment's bytes
  are stored as a `String`.  `bv_unsigned a` is `a.toNat`, so the
  window test is stated here as a `Prop` disjunction of conjunctions
  decided by `if` (the same test, the same numbers).  `memory_access` is
  the pair abbreviation (`word × Nat`), and the report's ranges are the
  structure field `report.accessed_ranges`.  Every `Example name : ...`
  check is a `theorem` with the same name here.

  (closed computations / `repeat split`).  The convention is
  `by decide`, which closes every goal whose type has a
  `DecidableEq` instance; a conjunction of such equalities has a
  `Decidable` instance too, so a `repeat split` needs no separate step.  `machine_result` itself is never compared here — the
  report is projected out of the `MachineOk` arm inside
  [reported_ranges], so every statement in the file is decidable.
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

set_option autoImplicit false

/- (reduction depth).  These checks are compiled evaluations:
   the VM runs them with no depth bound, while `by decide`
   (and `rfl`) reduce in the kernel.  The
   [0x148]-byte instruction segment plus the effect-tree interpreter
   [step_accesses] walk deeper nesting than the default
   `maxRecDepth` allows.  The bound is raised rather than any check
   weakened: every statement below is still a closed computation.
   Elaboration cost is a few seconds for the file. -/
set_option maxRecDepth 100000

namespace LinuxSem.Checks.RiscvAccessReporting

open LinuxSem.Riscv (word byte bvmap_empty bvmapSet)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- Nineteen 32-bit instructions, all using x11 as the address register and,
    where needed, x12/f12 as the source:

      0x100  lb       x10, 0(x11)       03850500
      0x104  lh       x10, 0(x11)       03950500
      0x108  lw       x10, 0(x11)       03a50500
      0x10c  ld       x10, 0(x11)       03b50500
      0x110  sb       x12, 0(x11)       2380c500
      0x114  sh       x12, 0(x11)       2390c500
      0x118  sw       x12, 0(x11)       23a0c500
      0x11c  sd       x12, 0(x11)       23b0c500
      0x120  flw      f10, 0(x11)       07a50500
      0x124  fld      f10, 0(x11)       07b50500
      0x128  fsw      f12, 0(x11)       27a0c500
      0x12c  fsd      f12, 0(x11)       27b0c500
      0x130  lr.w     x10, (x11)        2fa50510
      0x134  lr.d     x10, (x11)        2fb50510
      0x138  sc.w     x10, x12, (x11)   2fa5c518
      0x13c  sc.d     x10, x12, (x11)   2fb5c518
      0x140  amoadd.w x10, x12, (x11)   2fa5c500
      0x144  amoadd.d x10, x12, (x11)   2fb5c500
      0x148  addi     x0, x0, 0         13000000 -/
def access_code_segment : Segment where
  seg_base := 0x100
  seg_size := 76
  seg_perms := "r-x"
  seg_bytes :=
    ["038505000395050003a5050003b505002380c5002390c50023a0c50023b0c50007a5050007b5050027a0c50027b0c5002fa505102fb505102fa5c5182fb5c5182fa5c5002fb5c50013000000"]

def access_segments : List Segment := [access_code_segment]

/-- Two writable windows.  The first holds aligned ordinary accesses.  The
    second straddles [0x1000], allowing successful eight-byte operations to
    exercise cross-page ranges without changing instruction semantics. -/
def access_data (a : word) : Option byte :=
  let z : Int := (a.toNat : Int)
  if (0x200 ≤ z ∧ z < 0x220) ∨ (0xffc ≤ z ∧ z < 0x1004) then
    some (BitVec.ofInt 8 0x5a)
  else none

def access_state (pc : Int) (addr : Int) (resv : Option word) :
    machine_state where
  ms_regs :=
    bvmapSet (BitVec.ofInt 5 11) (BitVec.ofInt 64 addr)
      (bvmapSet (BitVec.ofInt 5 12) (BitVec.ofInt 64 0x1122334455667788)
        bvmap_empty)
  ms_fregs :=
    bvmapSet (BitVec.ofInt 5 12) (BitVec.ofInt 64 0x8877665544332211)
      bvmap_empty
  ms_pc_val := BitVec.ofInt 64 pc
  ms_svc_pending := none
  ms_resv := resv
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := access_data
  ms_rom := fun _ => none

def reported_ranges (st : machine_state) :
    Option (List memory_access) :=
  match step_accesses access_segments st with
  | .MachineOk report => some report.accessed_ranges
  | .MachineFault => none
  | .MachineUnmodeled => none

def access_at (addr : Int) (bytes : Nat) : List memory_access :=
  [(BitVec.ofInt 64 addr, bytes)]

def access_pair (addr : Int) (bytes : Nat) : List memory_access :=
  access_at addr bytes ++ access_at addr bytes

theorem integer_load_reports :
    reported_ranges (access_state 0x100 0x200 none)
        = some (access_at 0x200 1) ∧
      reported_ranges (access_state 0x104 0x200 none)
        = some (access_at 0x200 2) ∧
      reported_ranges (access_state 0x108 0x200 none)
        = some (access_at 0x200 4) ∧
      reported_ranges (access_state 0x10c 0x200 none)
        = some (access_at 0x200 8) := by decide

theorem integer_store_reports :
    reported_ranges (access_state 0x110 0x200 none)
        = some (access_at 0x200 1) ∧
      reported_ranges (access_state 0x114 0x200 none)
        = some (access_at 0x200 2) ∧
      reported_ranges (access_state 0x118 0x200 none)
        = some (access_at 0x200 4) ∧
      reported_ranges (access_state 0x11c 0x200 none)
        = some (access_at 0x200 8) := by decide

theorem floating_load_reports :
    reported_ranges (access_state 0x120 0x200 none)
        = some (access_at 0x200 4) ∧
      reported_ranges (access_state 0x124 0x200 none)
        = some (access_at 0x200 8) := by decide

theorem floating_store_reports :
    reported_ranges (access_state 0x128 0x200 none)
        = some (access_at 0x200 4) ∧
      reported_ranges (access_state 0x12c 0x200 none)
        = some (access_at 0x200 8) := by decide

theorem load_reserved_reports :
    reported_ranges (access_state 0x130 0x200 none)
        = some (access_at 0x200 4) ∧
      reported_ranges (access_state 0x134 0x200 none)
        = some (access_at 0x200 8) := by decide

theorem store_conditional_reports :
    reported_ranges
        (access_state 0x138 0x200 (some (BitVec.ofInt 64 0x200)))
      = some (access_at 0x200 4) ∧
      reported_ranges
        (access_state 0x13c 0x200 (some (BitVec.ofInt 64 0x200)))
      = some (access_at 0x200 8) := by decide

theorem failed_store_conditionals_report_no_access :
    reported_ranges (access_state 0x138 0x200 none) = some [] ∧
      reported_ranges (access_state 0x13c 0x200 none) = some [] := by decide

theorem atomic_read_modify_write_reports :
    reported_ranges (access_state 0x140 0x200 none)
        = some (access_pair 0x200 4) ∧
      reported_ranges (access_state 0x144 0x200 none)
        = some (access_pair 0x200 8) := by decide

theorem cross_page_reports :
    reported_ranges (access_state 0x10c 0xffc none)
        = some (access_at 0xffc 8) ∧
      reported_ranges (access_state 0x11c 0xffc none)
        = some (access_at 0xffc 8) := by decide

/-- Instruction fetches are deliberately absent: callers account only for
    successful DATA effects, while code remains governed by segment execute
    permissions. -/
theorem register_only_instruction_reports_no_access :
    reported_ranges (access_state 0x148 0x200 none) = some [] := by decide

end LinuxSem.Checks.RiscvAccessReporting
