/-
  * Common.AgentNodes — the pending-`ecall` state in `mkst`/`getr` vocabulary.

    Binary-agnostic (parametric in `segs`, the ecall `pc` and its fetch
    fact).  This is the small kit `RefNodes` (and every walk reaching a
    syscall) is written in:

      - `epend regs pc mem rom x8` : the machine state sitting ON the ecall
        with `ms_svc_pending = Some x8`, i.e. `RiscvSemantics.step` of
        `mkst regs pc mem rom` at an `ecall` (`step_ecall_epend`);
      - `ms_gpr_epend0..5`, `ms_read_byte_epend`, `ms_writable_byte_epend` :
        the syscall-argument / memory views of that state;
      - `adv_set_epend`, `adv_eff_ret_epend` : the post-syscall state of a
        return-only effect is `mkst (regupd regs 10 r) (v_addi pc 4) mem rom`;
      - `rz_sys` : enter the node (the `ecall` instruction step itself);
      - `rz_write_chan` : write(fd -> channel) with SHORT WRITES (the
        continuation is quantified over the delivered length);
      - `rz_exit_lit` : exit/exit_group with a literal status below 256.

      The nodes use the fault-free `realizes`, with the
      `m_vm_lazy model = []` side condition threaded through.  The
      per-syscall nodes for openat, mmap and read are in `RefNodes`.
      `rz_write_chan` quantifies its continuation over the delivered prefix
      length (`ShapeAlg.rz_write_ch`).

    NOTES.

    * Values are `Int`; `bvmap 5 word` is `BvMap word` (the association-list
      register file), `bv_unsigned w` is `(w.toNat : Int)`, `Z_to_bv 64 z` is
      `BitVec.ofInt 64 z`, `bv_and` is `&&&`, `Z.of_nat n` is `(n : Int)`,
      `nth 0 l` peeling is `List.take`, and `len_word` is `BvBase.len_word`.

    * The FP half of the state is the ambient `FPState` instance, as in
      `PropExec`; [epend] pins it to [fx0] — the entry state the rest of
      `Common`'s step lemmas use (see `PropExec`'s notes).  No statement
      below mentions the FP state.

    * `arg_reg_0..2` are `PropExec`'s; `arg_reg_3..5` are declared here.

    * [ms_writable_byte] carries the loaded segments as an EXPLICIT first
      argument (like `wview`).

    * The `rz_write_chan` proof drives `ShapeAlg.rz_write_ch` with
      `buf := bs`; `fd_lookup`/`FdChannel` are `StateFd`/`State`'s, and the
      `fd32` truncation is `Sys.Syscall.fd32_id`.

    Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StreamExec
import LinuxSem.Common.MmapSim
import LinuxSem.Common.AllocSim
import LinuxSem.Common.FileSim
import LinuxSem.Common.ShapeAlg
import LinuxSem.Common.Nodes
import LinuxSem.Common.StoreOk
import LinuxSem.Common.AgentLib

namespace LinuxSem.Common.AgentNodes

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.AgentLib
open LinuxSem.Common.ExitSim
open LinuxSem.Common.FileSim
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uaccess

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-- The `FPState` instance this file's states run under (the entry state, as
    everywhere else in `Common`). -/
local instance agentnodes_fx : FPState := fx0

/-! =========================================================================
    The pending-ecall state
    ========================================================================= -/

/-- The machine state sitting ON the `ecall` with `ms_svc_pending = some x8`. -/
def epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : machine_state :=
  { ms_regs := regs,
    ms_fregs := (inferInstance : FPState).fp_regs,
    ms_pc_val := pc,
    ms_svc_pending := some x8, ms_resv := none,
    ms_fcsr := (inferInstance : FPState).fp_csr,
    ms_mem := mem, ms_rom := rom }

/-- The `ecall` instruction step lands in [epend]. -/
theorem step_ecall_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom)
      = .MachineOk (epend regs pc mem rom (getr regs 17)) := by
  rw [step_ecall segs regs pc mem rom w HF HE]
  rfl

theorem epend_svc (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_svc_pending = some x8 := rfl

/-- The syscall-argument views of the pending state are the `getr` reads of
    `a0`/`a1`/`a2`. -/
theorem ms_gpr_epend0 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((0 : Nat) : Int))) = getr regs 10
  rw [show BitVec.ofInt 5 (10 + ((0 : Nat) : Int)) = (10 : reg) from arg_reg_0]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (10 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend1 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((1 : Nat) : Int))) = getr regs 11
  rw [show BitVec.ofInt 5 (10 + ((1 : Nat) : Int)) = (11 : reg) from arg_reg_1]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (11 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend2 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((2 : Nat) : Int))) = getr regs 12
  rw [show BitVec.ofInt 5 (10 + ((2 : Nat) : Int)) = (12 : reg) from arg_reg_2]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (12 : reg) 0 (by decide),
    ite_eq_right (by simp)]

/-- The a3/a4/a5 register indices, as `BitVec.ofInt 5` of `10 + n`. -/
theorem arg_reg_3 : BitVec.ofInt 5 (10 + ((3 : Nat) : Int)) = (13 : reg) := by decide
theorem arg_reg_4 : BitVec.ofInt 5 (10 + ((4 : Nat) : Int)) = (14 : reg) := by decide
theorem arg_reg_5 : BitVec.ofInt 5 (10 + ((5 : Nat) : Int)) = (15 : reg) := by decide

theorem ms_gpr_epend3 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((3 : Nat) : Int))) = getr regs 13
  rw [show BitVec.ofInt 5 (10 + ((3 : Nat) : Int)) = (13 : reg) from arg_reg_3]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (13 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend4 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((4 : Nat) : Int))) = getr regs 14
  rw [show BitVec.ofInt 5 (10 + ((4 : Nat) : Int)) = (14 : reg) from arg_reg_4]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (14 : reg) 0 (by decide),
    ite_eq_right (by simp)]

theorem ms_gpr_epend5 (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15 := by
  show reg_get regs (BitVec.ofInt 5 (10 + ((5 : Nat) : Int))) = getr regs 15
  rw [show BitVec.ofInt 5 (10 + ((5 : Nat) : Int)) = (15 : reg) from arg_reg_5]
  unfold getr
  rw [LinuxSem.Common.PropExec.bv_eqb_neq (15 : reg) 0 (by decide),
    ite_eq_right (by simp)]

/-- The read view of the pending state is the merged read view of `mem`. -/
theorem ms_read_byte_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (x8 : word) :
    ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem :=
  rfl

/-- The kernel's writable view of the pending state is [wview] of `mem`. -/
theorem ms_writable_byte_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (x8 : word) :
    ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem :=
  rfl

theorem ms_mem_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_mem = mem := rfl

theorem ms_rom_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 : word) : (epend regs pc mem rom x8).ms_rom = rom := rfl

/-- The post-syscall state of a return-only effect is the plain
    return-value update. -/
theorem adv_set_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 v : word) :
    advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
      = mkst (regupd regs 10 v) (v_addi pc 4) mem rom :=
  CatExec.adv_set regs pc (some x8) mem rom v

theorem adv_eff_ret_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 r : word) :
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  FileSim.adv_eff_ret regs pc x8 mem rom r

theorem adv_eff_ret_copyins_epend (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (x8 r : word) (reads : List (word × Nat)) :
    advance_past_svc
        (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom := by
  rw [CatSim.apply_effect_copyins_no_write]
  exact adv_set_epend regs pc mem rom x8 r

/-- Enter the syscall node: the `ecall` instruction step itself. -/
theorem rz_sys (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hc : realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T) :
    realizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  ShapeAlg.rz_step segs (mkst regs pc mem rom) model
    (epend regs pc mem rom (getr regs 17)) T
    Hh Hlazy rfl (step_ecall_epend segs regs pc mem rom w HF HE) Hc

/-! =========================================================================
    write(fd, buf, n) to a channel fd: SHORT WRITES
    ========================================================================= -/

/-- The environment delivers any NONEMPTY PREFIX of the `n` readable bytes
    `bs`; the continuation must hold for every delivered length `k`
    (a0 := k).  Shape: `t_write_ch ch bs T`.  `n = 0` is NOT covered
    (zero-count writes face `access_ok_zero`). -/
theorem rz_write_chan (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (fd ch : word) (n : Nat)
    (bs : List byte) (T : TSet)
    (Hh : m_halted model = none)
    (Hlazy : m_vm_lazy model = [])
    (Hno : ((getr regs 17).toNat : Int) = 64)
    (Hfd : getr regs 10 = fd) (Hfd32 : (fd.toNat : Int) < (2 : Int) ^ 32)
    (Hlk : fd_lookup (m_fds model) fd = some (FdEntry.FdChannel ch))
    (Hch : w_is0 ch = false)
    (Hcnt : getr regs 12 = BitVec.ofInt 64 (n : Int))
    (Hn1 : 1 ≤ n) (Hmax : (n : Int) ≤ rw_bytes_max)
    (Hn64 : (n : Int) < ((2 ^ 64 : Nat) : Int))
    (Hrd : rdn segs mem (getr regs 11) n = some bs)
    (Hc : ∀ k, 1 ≤ k → k ≤ n →
      realizes segs (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 (k : Int)))
        (v_addi pc 4) mem (seg_rom segs)) model) T) :
    realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
      (t_write_ch ch bs T) := by
  have hlen : bs.length = n := rdn_length segs mem n (getr regs 11) bs Hrd
  have hrom : (epend regs pc mem (seg_rom segs) (getr regs 17)).ms_rom
      = seg_rom segs := rfl
  refine ShapeAlg.rz_write_ch segs (epend regs pc mem (seg_rom segs) (getr regs 17))
    model fd ch (getr regs 17) bs T Hh Hlazy ?_ ?_ rfl Hno ?_ ?_ ?_ ?_ ?_
  · exact ⟨Hlk, Hch⟩
  · exact Sys.Syscall.fd32_id fd (by omega)
  · rw [ms_gpr_epend0]
    exact Hfd
  · rw [ms_gpr_epend1, ms_gpr_epend2, Hcnt,
      ms_read_bytes_rdn segs (epend regs pc mem (seg_rom segs) (getr regs 17)) _ _ hrom,
      word_to_nat_ofInt_lit n Hn64]
    exact Hrd
  · unfold buf_modeled
    rw [hlen]
    exact Hmax
  · rw [hlen]
    exact Hn1
  · intro k hk1 hk2
    have hlenword : len_word (bs.take k) = BitVec.ofInt 64 (k : Int) := by
      unfold len_word
      rw [List.length_take, Nat.min_eq_left hk2]
      exact (BitVec.ofInt_natCast 64 k).symm
    rw [hlenword, adv_set_epend]
    exact Hc k hk1 (by omega)

/-! =========================================================================
    exit_group(code) / exit(code) with a literal status
    ========================================================================= -/

/-- `andi code, 255` on a status below 256 is the status. -/
theorem bv_and_255_small (code : Int) (Hc : 0 ≤ code ∧ code < 256) :
    BitVec.ofInt 64 code &&& BitVec.ofInt 64 255 = BitVec.ofInt 64 code := by
  have hcode : (BitVec.ofInt 64 code).toNat = code.toNat := by
    rw [BitVec.toNat_ofInt]
    have h : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := Int.natCast_pow 2 64
    rw [h, Int.emod_eq_of_lt Hc.1 (by rw [← h]; omega)]
  have h255 : (BitVec.ofInt 64 255).toNat = 255 := by decide
  have hsmall : code.toNat < 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hcode, h255, show (255 : Nat) = 2 ^ 8 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsmall]

theorem rz_exit_lit (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (code : Int)
    (Hh : m_halted model = none) (Hx8 : is_exit_no (getr regs 17))
    (Ha0 : getr regs 10 = BitVec.ofInt 64 code)
    (Hc : 0 ≤ code ∧ code < 256) :
    realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
      (t_exit (BitVec.ofInt 64 code) (m_fs model)) := by
  have h := ShapeAlg.rz_exit segs (epend regs pc mem rom (getr regs 17)) model
    (getr regs 17) Hh rfl Hx8
  rw [ms_gpr_epend0, Ha0, bv_and_255_small code Hc] at h
  exact h
