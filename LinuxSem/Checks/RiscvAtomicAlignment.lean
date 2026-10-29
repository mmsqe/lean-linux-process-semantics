/-
  * LinuxProcessSem.Checks.RiscvAtomicAlignment — misaligned atomics fault

  Regression checks for the A-extension alignment gate in [Sem.exec]:
  lr/sc/amo at an address that is not naturally aligned to the operand
  width (4 for .w, 8 for .d) is [Sem.EFault], which [interp_eff] turns
  into [MachineFault] — the SIGBUS the real process takes.  Plain
  loads and stores are deliberately NOT gated (the model permits
  misaligned ones, as the emulated hart and Linux on real hardware
  do), so these checks pin the split.

  Anti-vacuity: every misaligned case below differs from a green
  aligned twin ONLY in the low bits of the address register, and the
  data window is readable and writable at both addresses — so only
  the alignment gate can make the misaligned one fault.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n` and `Z_to_bv n z` is `BitVec.ofInt n z`; a segment's bytes
  are stored as a `String`.  `bv_unsigned a` is `a.toNat`, and the
  window test is stated here as a `Prop` conjunction decided by `if`
  (the same test, the same numbers).  The register map's keys are
  `reg`s (`BitVec 5`), so `bvmap_set (Z_to_bv 5 11)` is `bvmapSet
  (BitVec.ofInt 5 11)` verbatim.  Every `Example name : ...` check
  is a `theorem` with the same name here.

  (closed computations / `exact I`).  The convention is
  `by decide`, which closes every goal whose type has a `DecidableEq`
  instance (`Option`/`List`/`BitVec`).  A goal stated as an equality of
  `machine_result machine_state` values has none — `machine_state` has
  function-typed fields (`ms_mem`, `ms_rom`) — so there the same
  computation is done by the kernel and the goal is closed by `rfl`,
  exactly what `reflexivity` after such a computation establishes.
  An `exact I` on a `match ... => True` goal needs the goal first
  brought to `True` by `show`, which performs the same computation
  definitionally; there is no `Decidable` instance for
  `by decide` to use there.  The constructors of `machine_result` are
  spelled `.MachineFault` in statements for the namespace reason
  recorded in `Checks/RiscvCompressedFetch`.
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

namespace LinuxSem.Checks.RiscvAtomicAlignment

open LinuxSem.Riscv (word reg byte bvmap_empty bvmapSet)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- Six atomics, one per instruction word, all using x11 as the address
    and x12 as the source, rd = x10:

      0x100  lr.w     x10, (x11)        2fa50510
      0x104  lr.d     x10, (x11)        2fb50510
      0x108  sc.w     x10, x12, (x11)   2fa5c518
      0x10c  sc.d     x10, x12, (x11)   2fb5c518
      0x110  amoadd.w x10, x12, (x11)   2fa5c500
      0x114  amoadd.d x10, x12, (x11)   2fb5c500 -/
def atomic_code_segment : Segment where
  seg_base := 0x100
  seg_size := 24
  seg_perms := "r-x"
  seg_bytes := ["2fa505102fb505102fa5c5182fb5c5182fa5c5002fb5c500"]

def atomic_segments : List Segment := [atomic_code_segment]

/-- A 32-byte writable data window at [0x200], present in the overlay:
    [ov_read_bytes] answers loads from it and [store_ok] accepts stores
    into it, so an atomic aimed anywhere inside is otherwise fully
    executable. -/
def atomic_data (a : word) : Option byte :=
  if (0x200 : Int) ≤ (a.toNat : Int) ∧ (a.toNat : Int) < 0x220 then
    some (BitVec.ofInt 8 0x5a)
  else none

def atomic_state (pc : word) (addr : Int) (resv : Option word) :
    machine_state where
  ms_regs :=
    bvmapSet (BitVec.ofInt 5 11) (BitVec.ofInt 64 addr)
      (bvmapSet (BitVec.ofInt 5 12) (BitVec.ofInt 64 0x1122334455667788)
        bvmap_empty)
  ms_fregs := bvmap_empty
  ms_pc_val := pc
  ms_svc_pending := none
  ms_resv := resv
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := atomic_data
  ms_rom := fun _ => none

def pc_lr_w : word := BitVec.ofInt 64 0x100
def pc_lr_d : word := BitVec.ofInt 64 0x104
def pc_sc_w : word := BitVec.ofInt 64 0x108
def pc_sc_d : word := BitVec.ofInt 64 0x10c
def pc_amo_w : word := BitVec.ofInt 64 0x110
def pc_amo_d : word := BitVec.ofInt 64 0x114

def steps_ok (st : machine_state) : Prop :=
  match step atomic_segments st with
  | .MachineOk _ => True
  | _ => False

/-! *** lr: the aligned twin retires, every misaligned residue faults. -/

theorem lr_w_aligned : steps_ok (atomic_state pc_lr_w 0x204 none) := by
  show True
  trivial

theorem lr_w_mod_2 :
    step atomic_segments (atomic_state pc_lr_w 0x206 none)
      = .MachineFault := by rfl

theorem lr_w_mod_1 :
    step atomic_segments (atomic_state pc_lr_w 0x205 none)
      = .MachineFault := by rfl

theorem lr_d_aligned : steps_ok (atomic_state pc_lr_d 0x200 none) := by
  show True
  trivial

/-- 4 mod 8: aligned for lr.w (green above), misaligned for lr.d. -/
theorem lr_d_mod_4 :
    step atomic_segments (atomic_state pc_lr_d 0x204 none)
      = .MachineFault := by rfl

/-! *** amo: same split, and the aligned twin's store retires. -/

theorem amo_w_aligned : steps_ok (atomic_state pc_amo_w 0x204 none) := by
  show True
  trivial

theorem amo_w_mod_2 :
    step atomic_segments (atomic_state pc_amo_w 0x206 none)
      = .MachineFault := by rfl

theorem amo_d_aligned : steps_ok (atomic_state pc_amo_d 0x200 none) := by
  show True
  trivial

theorem amo_d_mod_4 :
    step atomic_segments (atomic_state pc_amo_d 0x204 none)
      = .MachineFault := by rfl

/-! *** sc: the alignment check runs BEFORE the reservation check.

    A misaligned sc faults even with NO live reservation — without the
    gate (or with it placed after the reservation test) this case would
    retire cleanly with rd = 1, never touching memory.  With a live
    matching reservation the aligned twin stores and retires. -/

theorem sc_w_aligned_success :
    steps_ok (atomic_state pc_sc_w 0x204 (some (BitVec.ofInt 64 0x204))) := by
  show True
  trivial

theorem sc_w_aligned_fail_retires :
    steps_ok (atomic_state pc_sc_w 0x204 none) := by
  show True
  trivial

theorem sc_w_mod_2_no_resv :
    step atomic_segments (atomic_state pc_sc_w 0x206 none)
      = .MachineFault := by rfl

theorem sc_w_mod_2_live_resv :
    step atomic_segments
      (atomic_state pc_sc_w 0x206 (some (BitVec.ofInt 64 0x206)))
      = .MachineFault := by rfl

theorem sc_d_aligned_success :
    steps_ok (atomic_state pc_sc_d 0x200 (some (BitVec.ofInt 64 0x200))) := by
  show True
  trivial

/-- 4 mod 8 with a matching reservation: only the width's own alignment
    can be what faults here. -/
theorem sc_d_mod_4_live_resv :
    step atomic_segments
      (atomic_state pc_sc_d 0x204 (some (BitVec.ofInt 64 0x204)))
      = .MachineFault := by rfl

end LinuxSem.Checks.RiscvAtomicAlignment
