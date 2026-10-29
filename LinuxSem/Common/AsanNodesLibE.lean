/-
  * Common.AsanNodesLibE — generic node library for the spec: lazy-tolerant
    (no `m_vm_lazy = []` premise) syscall nodes for set_tid_address / brk /
    munmap / exit, the ecall entry step, srealizes wrappers, and cs_ok
    helpers shared by the `AsanNodesMm*` files.
 Every mmap / munmap / mprotect / brk
  effect is such (`State.syscall_effect_accesses` = eff_copyins ++ write
  accesses = []), and then the post-syscall materialisation is the identity
  WHATEVER the lazy ledger holds (`materialize_model_accesses_nil`).  This is
  what lets the ASan proof run on a model whose lazy ledger is non-empty for
  the whole run (the runtime's `MAP_NORESERVE` reservations).
  The Section `Noacc` over `segs : list Segment` is threaded explicitly here
  (Lean has no section variables at use sites, the tree's convention), so
  every declaration of that section takes `segs` as its leading parameter.
  `-halted` lemmas: [m_halted] is untouched by every ledger-only model
  transformer; each is `rfl` or one `if`-split.
  All 45  declarations are
  stated and proved, the MAP_FIXED-wholly-inside-one-live-mapping pair
  (`mmap_fixedin_check` :643 and `srz_mmap_fixedin_lazy` :725, section `6b`)
  included.  Nothing is missing; there is no proof hole, no extra postulate
  and no `unsafe`.
 This tree
  binds `n` as an explicit parameter with the equation hypothesis
  `Hn : n = Z_to_bv 64 (page_round_up_Z len)`, the same encoding the
  AsanNodesMmLib node lemmas use for their `nZ`/`n`; a caller passes `rfl`.
-/

import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.ExecutableSpecs
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
import LinuxSem.Common.SpinAlg
import LinuxSem.Common.Nodes
import LinuxSem.Common.StoreOk
import LinuxSem.Common.AgentLib
import LinuxSem.Common.AgentNodes
import LinuxSem.Common.RefNodes
import LinuxSem.Common.AsanAcct
import LinuxSem.Common.AsanAcctShape
import LinuxSem.Common.AsanPlacement
import LinuxSem.Common.BackingAlgebra
import LinuxSem.Common.AsanCeil
import LinuxSem.Common.RocqSpelling
import LinuxSem.Common.AxSymExec3
import LinuxSem.Common.AxSymExec3Sound
import LinuxSem.Common.AxSymRun3
import LinuxSem.Common.AsanPlanCore
import LinuxSem.Common.AsanPlan
import LinuxSem.Common.AsanPlanSound
import LinuxSem.Common.SharedFacts

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.AsanNodesLibE

open LinuxSem.Common.SharedFacts (materialize_model_accesses_nil)

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Common.PropExec
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamExec
open LinuxSem.Common.MmapSim
open LinuxSem.Common.AllocSim
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.SpinAlg
open LinuxSem.Common.Nodes
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AgentNodes
open LinuxSem.Common.RefNodes
open LinuxSem.Common.AsanCeil
open LinuxSem.Common.AxSymExec3
open LinuxSem.Common.RocqSpelling
open LinuxSem.Common.AxSymRun3
open LinuxSem.Common.AsanPlanCore
open LinuxSem.Common.AsanPlan
open LinuxSem.Common.AsanPlanSound
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork

/-- The FP state at process entry , so that the `PropExec`-based lemmas elaborate. -/
local instance asannodeslibe_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   1. Checker-based node constructors WITHOUT the lazy premise
   ========================================================================= -/

/-- A successful checker run whose effect touches no user memory yields an
    `sstep` — the post-syscall materialisation is the identity whatever the
    lazy ledger holds. -/
theorem sstep_of_check_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hc : check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs)
    (Hh' : m_halted m' = none) (Hacc : syscall_effect_accesses eff = []) :
    sstep segs (mkCfg ms model) evs
      (.SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')) := by
  refine sstep.syscall ms model x8 eff m' m' evs Hh Hsvc ?_ Hh' ?_
  · exact (check_syscall_ok_iff _ _ _ _ _).mp Hc
  · rw [Hacc]; exact materialize_model_accesses_nil m'

/-- The `node_ok` constructor from a checker family: one silent resolution
    per index, exhaustive, never unmodeled. -/
theorem node_chk_ev_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (I : Type) (effs : I → SyscallEffect) (ms' : I → Model)
    (evs : I → List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : ∀ i, check_syscall (sys_input segs ms x8) (effs i) model = .CheckOk (ms' i) (evs i))
    (Hinv : ∀ eff m' ev, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
      ∃ i, eff = effs i ∧ m' = ms' i ∧ ev = evs i)
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh' : ∀ i, m_halted (ms' i) = none)
    (Hacc : ∀ i, syscall_effect_accesses (effs i) = []) :
    node_ok segs (mkCfg ms model) I evs
      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) := by
  constructor
  · intro i
    exact sstep_of_check_noacc segs ms model x8 (effs i) (ms' i) (evs i) Hh Hsvc
      (Hok i) (Hh' i) (Hacc i)
  · intro e st hss
    rcases sstep_svc_inv segs ms model x8 e st Hsvc hss with
      ⟨eff, model', ev, hc, h1 | h2 | h3⟩ | ⟨eff, hc, -, -⟩
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨m'', -, he, hmat, hst⟩ := h1
      rw [Hacc i, materialize_model_accesses_nil] at hmat
      obtain rfl : ms' i = m'' := by injection hmat
      exact ⟨i, he, hst⟩
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨-, -, hmat, -⟩ := h2
      rw [Hacc i, materialize_model_accesses_nil] at hmat
      exact absurd hmat (by simp)
    · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' ev hc
      obtain ⟨code, hh2, -, -⟩ := h3
      rw [Hh' i] at hh2
      exact absurd hh2 (by simp)
    · exact absurd hc (Hnu eff)

/-- `node_chk_ev_noacc` with no events. -/
theorem node_chk_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (I : Type) (effs : I → SyscallEffect) (ms' : I → Model)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hok : ∀ i, check_syscall (sys_input segs ms x8) (effs i) model = .CheckOk (ms' i) [])
    (Hinv : ∀ eff m' evs, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs →
      ∃ i, eff = effs i ∧ m' = ms' i ∧ evs = [])
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh' : ∀ i, m_halted (ms' i) = none)
    (Hacc : ∀ i, syscall_effect_accesses (effs i) = []) :
    node_ok segs (mkCfg ms model) I (fun _ => [])
      (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) :=
  node_chk_ev_noacc segs ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hinv Hnu Hh' Hacc

/-- The deterministic special case: the checker admits exactly one effect. -/
theorem node_det_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff0 : SyscallEffect) (m0 : Model) (evs0 : List event)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff m' evs, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs ↔
      (eff = eff0 ∧ m' = m0 ∧ evs = evs0))
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh0 : m_halted m0 = none) (Hacc : syscall_effect_accesses eff0 = []) :
    node_ok segs (mkCfg ms model) Unit (fun _ => evs0)
      (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0) := by
  refine node_chk_ev_noacc segs ms model x8 Unit (fun _ => eff0) (fun _ => m0)
    (fun _ => evs0) Hh Hsvc ?_ ?_ Hnu ?_ ?_
  · intro _
    exact (Hchk eff0 m0 evs0).mpr ⟨rfl, rfl, rfl⟩
  · intro eff m' ev hc
    obtain ⟨rfl, rfl, rfl⟩ := (Hchk eff m' ev).mp hc
    exact ⟨(), rfl, rfl, rfl⟩
  · intro _; exact Hh0
  · intro _; exact Hacc

/-- silent `realizes` wrapper for `node_det_noacc`. -/
theorem rz_det_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff0 : SyscallEffect) (m0 : Model) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff m' evs, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs ↔
      (eff = eff0 ∧ m' = m0 ∧ evs = []))
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh0 : m_halted m0 = none) (Hacc : syscall_effect_accesses eff0 = [])
    (Hc : realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T) :
    realizes segs (mkCfg ms model) T :=
  rz_silent1 segs _ _ T
    (node_det_noacc segs ms model x8 eff0 m0 [] Hh Hsvc Hchk Hnu Hh0 Hacc) Hc

/-- srealizes twin of `rz_det_noacc`. -/
theorem srz_det_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (eff0 : SyscallEffect) (m0 : Model) (T : TSet)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hchk : ∀ eff m' evs, check_syscall (sys_input segs ms x8) eff model = .CheckOk m' evs ↔
      (eff = eff0 ∧ m' = m0 ∧ evs = []))
    (Hnu : ∀ eff, check_syscall (sys_input segs ms x8) eff model ≠ .CheckUnmodeled)
    (Hh0 : m_halted m0 = none) (Hacc : syscall_effect_accesses eff0 = [])
    (Hc : srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T) :
    srealizes segs (mkCfg ms model) T :=
  srz_silent1 segs _ _ T
    (node_det_noacc segs ms model x8 eff0 m0 [] Hh Hsvc Hchk Hnu Hh0 Hacc) Hc

/-- srealizes twin of `Nodes.rz_cases`: a silent node whose resolutions each
    continue as their own shape realizes the union. -/
theorem srz_cases (segs : List Segment) (c : config) (I : Type) (nx : I → config)
    (T : I → TSet) (i0 : I)
    (Hnode : node_ok segs c I (fun _ => []) nx)
    (Hc : ∀ i, srealizes segs (nx i) (T i)) :
    srealizes segs c (t_alt T) := by
  refine srz_conseq segs c (t_alt (fun i => t_emit [] (T i))) (t_alt T) ?_ ?_
  · exact .srz_node c I (fun _ => []) nx T i0 Hnode Hc
  · intro tr
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr).mpr hi⟩

/- =========================================================================
   2. Model-transformer frame facts
   ========================================================================= -/

theorem with_vm_backing_halted (l : List (word × word)) (p : List word) (m : Model) :
    m_halted (with_vm_backing l p m) = m_halted m := by
  simp [with_vm_backing, m_halted]

theorem vm_add_lazy_halted (a n : word) (m : Model) :
    m_halted (vm_add_lazy a n m) = m_halted m := by
  simp [vm_add_lazy, with_vm_backing, m_halted]

theorem with_mmap_backing_halted (flags a n : word) (m : Model) :
    m_halted (with_mmap_backing flags a n m) = m_halted m := by
  unfold with_mmap_backing
  by_cases h : mmap_noreserve_b flags
  · rw [ite_eq_left h]; exact vm_add_lazy_halted a n m
  · rw [ite_eq_right h]

theorem with_mmap_replacement_halted (flags a n : word) (m : Model) :
    m_halted (with_mmap_replacement flags a n m) = m_halted m := by
  unfold with_mmap_replacement
  rw [with_mmap_backing_halted, vm_forget_range_halted]

theorem with_mmap_destroyed_halted (a n : word) (h : VmMaps) (m : Model) :
    m_halted (with_mmap_destroyed a n h m) = m_halted m := by
  unfold with_mmap_destroyed
  rw [vm_forget_range_halted, with_vmmaps_halted]

theorem forget_vm_ranges_halted (ranges : List (word × word)) (m : Model) :
    m_halted (forget_vm_ranges ranges m) = m_halted m := by
  induction ranges generalizing m with
  | nil => simp [forget_vm_ranges]
  | cons p rest ih =>
    obtain ⟨a, n⟩ := p
    simp only [forget_vm_ranges]
    rw [ih, vm_forget_range_halted]

theorem brk_model_halted (req r : word) (m : Model) :
    m_halted (brk_model req r m) = m_halted m := by
  unfold brk_model with_brk_next
  rw [forget_vm_ranges_halted, with_vmmaps_halted]

/- =========================================================================
   3. Entering a syscall node without the lazy premise
   ========================================================================= -/

/-- `ms_pc` reads the pending-`ecall` state back. -/
theorem ms_pc_mkst (regs : BvMap word) (pc : word) (mem rom : word → Option byte) :
    ms_pc (mkst regs pc mem rom) = pc := rfl

/-- The `ecall` instruction reports no memory access. -/
theorem stepacc_ecall_epend (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true) :
    step_accesses segs (mkst regs pc mem rom) =
      .MachineOk (mkAccessReport (epend regs pc mem rom (getr regs 17)) []) := by
  unfold step_accesses
  rw [ms_pc_mkst]
  rw [HF]
  simp only [decode_exec_accesses, HE, ite_eq_left]
  rfl

/-- The `ecall` entry step, silently, for `realizes`. -/
theorem rz_sys_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (HF : fetch_word segs pc = some w)
    (HE : is_ecall w = true)
    (Hc : realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T) :
    realizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  rz_silent1 segs _ _ T
    (node_instr_noacc segs (mkst regs pc mem rom) model
      (epend regs pc mem rom (getr regs 17)) Hh rfl
      (stepacc_ecall_epend segs regs pc mem rom w HF HE)) Hc

/-- Common register bookkeeping for the mmap nodes: `a1 = len` as an `Int`,
    non-zero and not the zero word. -/
theorem epend_len (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (len : Int)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len ∧ len < 2 ^ 64) :
    ((ms_gpr (epend regs pc mem rom (getr regs 17)) 1).toNat : Int) = len ∧
      ms_gpr (epend regs pc mem rom (getr regs 17)) 1 ≠ BitVec.ofInt 64 0 := by
  constructor
  · rw [ms_gpr_epend1, H11]; exact u64_lit len ⟨by omega, Hlen.2⟩
  · rw [ms_gpr_epend1, H11]
    intro hc
    have h := congrArg (fun (x : word) => (x.toNat : Int)) hc
    rw [u64_lit len ⟨by omega, Hlen.2⟩] at h
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0] at h
    omega

/-- The `ecall` entry step, silently, for `srealizes`. -/
theorem srz_sys_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (T : TSet)
    (Hh : m_halted model = none) (HF : fetch_word segs pc = some w)
    (HE : is_ecall w = true)
    (Hc : srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) T :=
  srz_silent1 segs _ _ T
    (node_instr_noacc segs (mkst regs pc mem rom) model
      (epend regs pc mem rom (getr regs 17)) Hh rfl
      (stepacc_ecall_epend segs regs pc mem rom w HF HE)) Hc

/- =========================================================================
   4. munmap of one tracked entry (srealizes)
   ========================================================================= -/

/-  inline collapse of the munmap checker at its
   single admissible effect, packaged as a standalone iff so the `match` on
   the effect is eliminated ONCE (inside this lemma) rather than at each of
   the two `srz_det_noacc` obligations. -/
theorem check_munmap_collapse (a n : word) (model : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) :
    ((match eff with
      | ⟨r, [], [], us, [], []⟩ =>
          if (w_is0 r && listNN_eqb us [(a, n)]) = true then
            check_result.CheckOk (munmap_model a n model) [] else check_result.CheckReject
      | _ => check_result.CheckReject) = check_result.CheckOk m' evs) ↔
      (eff = ⟨BitVec.ofInt 64 0, [], [], [(a, n)], [], []⟩ ∧
        m' = munmap_model a n model ∧ evs = []) := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w0, ws⟩ <;> rcases zs with _ | ⟨z0, zs⟩ <;>
    rcases cs with _ | ⟨c0, cs⟩ <;> rcases ci with _ | ⟨i0, ci⟩ <;> dsimp only
  · have hcond : (w_is0 (BitVec.ofInt 64 0) && listNN_eqb [(a, n)] [(a, n)]) = true := by
      rw [show w_is0 (BitVec.ofInt 64 0) = true from by
            unfold w_is0; exact PropExec.bv_eqb_refl _,
          show listNN_eqb [(a, n)] [(a, n)] = true from (listNN_eqb_eq _ _).mpr rfl]
      rfl
    by_cases hc : (w_is0 r && listNN_eqb us [(a, n)]) = true
    · rw [ite_eq_left hc]
      constructor
      · intro h
        rw [Bool.and_eq_true] at hc
        obtain ⟨hw, hl⟩ := hc
        have hr : r = BitVec.ofInt 64 0 := by
          unfold w_is0 at hw; exact (bv_eqb_eq r _).mp hw
        have hu : us = [(a, n)] := (listNN_eqb_eq us [(a, n)]).mp hl
        subst hr hu
        cases h
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨-, rfl, rfl⟩; rfl
    · rw [ite_eq_right hc]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨h1, -, -⟩
        have hr : r = BitVec.ofInt 64 0 := by
          have := congrArg (fun e : SyscallEffect => e.eff_ret) h1; simpa using this
        have hu : us = [(a, n)] := by
          have := congrArg (fun e : SyscallEffect => e.eff_unmaps) h1; simpa using this
        subst hr hu
        exact absurd hcond hc
  all_goals simp

/-- munmap of one tracked entry, `srealizes`, WITHOUT the lazy premise: the
    unique checker success is the effect that returns 0 and unmaps
    `[a, a + page_round_up_Z len)`, whose successor model and memory are
    `munmap_model a n model` / `unfill a n mem`.

    The exact Sv48 bound of `munmap_args_ok` (`Hnw`) is what rules out the
    silent-`CheckUnmodeled` branch. -/
theorem srz_munmap_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (a : word) (len : Int)
    (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 215)
    (H10 : getr regs 10 = a) (Hal : ((a.toNat : Int)) % page_size = 0)
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hnw : ((a.toNat : Int)) + page_round_up_Z len ≤ TASK_SIZE)
    (Hhas : map_has ((m_vmmaps model).vm_maps) a (BitVec.ofInt 64 (page_round_up_Z len)) = true)
    (Hc : srealizes segs (mkCfg (mkst (regupd regs 10 (BitVec.ofInt 64 0)) (v_addi pc 4)
                             (unfill a (BitVec.ofInt 64 (page_round_up_Z len)) mem) rom)
                       (munmap_model a (BitVec.ofInt 64 (page_round_up_Z len)) model)) K) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) K := by
  have Hlen' : len < 2 ^ 64 := by
    have h1 : len ≤ page_round_up_Z len := (page_round_up_Z_bounds len (by omega)).1
    have h2 : ((a.toNat : Int)) < 2 ^ 64 := by have := a.isLt; omega
    have h3 : TASK_SIZE < 2 ^ 64 := by unfold TASK_SIZE; decide
    omega
  refine srz_sys_lazy segs regs pc mem rom model w K Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 215 := by
    rw [H17]; exact u64_lit 215 ⟨by decide, by decide⟩
  have Hu1 : ((ms_gpr ms 1).toNat : Int) = len := by
    dsimp only [ms]
    rw [ms_gpr_epend1, H11]; exact u64_lit len ⟨by omega, Hlen'⟩
  have Hpr : page_round_up (ms_gpr ms 1) = BitVec.ofInt 64 (page_round_up_Z len) := by
    unfold page_round_up; rw [Hu1]
  have H0 : ms_gpr ms 0 = a := by
    dsimp only [ms]
    rw [ms_gpr_epend0, H10]
  have Hargs : munmap_args_ok ms model := by
    unfold munmap_args_ok
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [H0]; exact Hal
    · intro hz
      have h := congrArg (fun (x : word) => (x.toNat : Int)) hz
      rw [Hu1] at h
      have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
      rw [h0] at h
      omega
    · rw [H0, Hu1]; exact Hnw
    · rw [H0, Hpr]; exact Hhas
  have hmod := fun eff => munmap_check_modeled ms model eff Hargs
  simp only [H0, Hpr] at hmod
  have Hchkfun : ∀ eff, check_syscall (sys_input segs ms (getr regs 17)) eff model =
      (match eff with
       | ⟨r, [], [], us, [], []⟩ =>
           if (w_is0 r && listNN_eqb us [(a, BitVec.ofInt 64 (page_round_up_Z len))]) = true then
             check_result.CheckOk (munmap_model a (BitVec.ofInt 64 (page_round_up_Z len)) model) []
           else check_result.CheckReject
       | _ => check_result.CheckReject) := by
    intro eff
    rw [munmap_check segs ms (getr regs 17) model eff Hno, H0]
    exact hmod eff
  refine srz_det_noacc segs ms model (getr regs 17)
    ⟨BitVec.ofInt 64 0, [], [], [(a, BitVec.ofInt 64 (page_round_up_Z len))], [], []⟩
    (munmap_model a (BitVec.ofInt 64 (page_round_up_Z len)) model) K
    Hh rfl ?_ ?_ ?_ rfl ?_
  · intro eff m' evs
    rw [Hchkfun eff]
    exact check_munmap_collapse a (BitVec.ofInt 64 (page_round_up_Z len)) model eff m' evs
  · intro eff hck
    rw [Hchkfun eff] at hck
    obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
    rcases ws with _ | ⟨w0, ws⟩ <;> rcases zs with _ | ⟨z0, zs⟩ <;>
      rcases cs with _ | ⟨c0, cs⟩ <;> rcases ci with _ | ⟨i0, ci⟩ <;> try dsimp only
    all_goals
      (by_cases h : (w_is0 r = true ∧
          listNN_eqb us [(a, BitVec.ofInt 64 (page_round_up_Z len))] = true)
       · simp [ite_eq_left h] at hck
       · simp [ite_eq_right h] at hck)
  · rw [munmap_model_halted]; exact Hh
  · dsimp only [ms]
    rw [adv_unmaps1_epend]
    exact Hc

/- =========================================================================
   5. brk: query / two-outcome grow / blocked grow
   ========================================================================= -/

/-- `RefNodes.node_brk` minus the lazy premise, through the checker. -/
theorem node_brk_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 214) :
    node_ok segs (mkCfg ms model)
      { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
      (fun _ => [])
      (fun i => mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU i.1 []
            (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
            (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) i.1 model)) := by
  refine node_chk_noacc segs ms model x8
    { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
    (fun i => SyscallEffect.mkEffectU i.1 []
      (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
      (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])
    (fun i => AllocSim.brk_model (ms_gpr ms 0) i.1 model) Hh Hsvc ?_ ?_ ?_ ?_ ?_
  · intro i
    exact (check_syscall_ok_iff _ _ _ _ _).mpr (AllocSim.brk_ok_intro segs ms x8 model i.1 Hno i.2)
  · intro eff m' evs hc
    obtain ⟨heff, hevs, hok, hmod⟩ :=
      (AllocSim.brk_ok_iff segs ms x8 model eff m' evs Hno).mp
        ((check_syscall_ok_iff _ _ _ _ _).mp hc)
    exact ⟨⟨eff.eff_ret, hok⟩, heff, hmod, hevs⟩
  · intro eff hc
    exact AllocSim.brk_no_unmodeled segs ms x8 model Hno
      (check_syscall_sound_unmodeled _ eff _ hc)
  · intro i
    show m_halted (AllocSim.brk_model (ms_gpr ms 0) i.1 model) = none
    rw [brk_model_halted]; exact Hh
  · intro i; rfl

/-- brk QUERY (`a0 = 0`): the single resolution keeps the break, so the
    successor is `mkst (regupd regs 10 (vm_brk model)) (pc+4) mem rom` at the
    same model. -/
theorem srz_brk_query_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (K : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 214)
    (H10 : getr regs 10 = BitVec.ofInt 64 0)
    (Hc : srealizes segs (mkCfg (mkst (regupd regs 10 (m_vmmaps model).vm_brk) (v_addi pc 4) mem rom) model) K) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) K := by
  refine srz_sys_lazy segs regs pc mem rom model w K Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 214 := by
    rw [H17]; exact u64_lit 214 ⟨by decide, by decide⟩
  have H0 : ms_gpr ms 0 = BitVec.ofInt 64 0 := by
    dsimp only [ms]; rw [ms_gpr_epend0, H10]
  have Hcases : ∀ r, AllocSim.brk_resolution_ok model (ms_gpr ms 0) r ↔
      r = (m_vmmaps model).vm_brk := by
    intro r
    rw [H0]
    show AllocSim.mmap_brk_r_ok model (BitVec.ofInt 64 0) r = true ↔
      r = (m_vmmaps model).vm_brk
    rw [AllocSim.mmap_brk_r_ok_eq]
    have hw : w_is0 (BitVec.ofInt 64 0) = true := by
      unfold w_is0; exact PropExec.bv_eqb_refl _
    have hc : (w_is0 (BitVec.ofInt 64 0) ||
        decide (((BitVec.ofInt 64 0).toNat : Int) < ((min_brk (m_vmmaps model)).toNat : Int))) = true := by
      rw [hw]; rfl
    rw [ite_eq_left hc, beq_iff_eq]
  have Hq : AllocSim.brk_resolution_ok model (ms_gpr ms 0) (m_vmmaps model).vm_brk :=
    (Hcases _).mpr rfl
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun _ : { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r } => K)) K
    ?_ ?_
  · refine srz_cases segs (mkCfg ms model)
      { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
      (fun i => mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU i.1 []
            (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
            (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) i.1 model))
      (fun _ => K) ⟨_, Hq⟩ ?_ ?_
    · exact node_brk_lazy segs ms model (getr regs 17) Hh rfl Hno
    · intro i
      obtain ⟨r, hr⟩ := i
      have Er : r = (m_vmmaps model).vm_brk := (Hcases r).mp hr
      subst Er
      show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU (m_vmmaps model).vm_brk []
            (brk_zeros (ms_gpr ms 0) (m_vmmaps model).vm_brk (m_vmmaps model).vm_brk)
            (brk_unmaps (m_vmmaps model).vm_brk (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) (m_vmmaps model).vm_brk model)) K
      rw [H0, AllocSim.brk_zeros_query, AllocSim.brk_unmaps_keep]
      rw [AllocSim.brk_model_query _ model rfl, vmmaps_eta, with_vmmaps_eta]
      dsimp only [ms]
      rw [adv_ret_epend]
      exact Hc
  · intro tr
    constructor
    · rintro ⟨i, hT⟩; exact hT
    · intro hT; exact ⟨⟨_, Hq⟩, hT⟩

/-- brk GROW with both outcomes: the checker's resolutions are `b` (the
    break is unchanged, a provably blocked grow) and `req` (the grant, when
    `brk_grow_ok` admits it), so the node realizes `t_alt2 KA KB`.

    `b` is the current break `(m_vmmaps model).vm_brk` and `req` the request
    `b + d`: the caller has already established that the grow is admitted and
    that `d` is a nonzero whole number of pages. -/
theorem srz_brk_grow_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (d : Int)
    (KA KB : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 214)
    (Hbal : (((m_vmmaps model).vm_brk).toNat : Int) % page_size = 0)
    (Hdal : d % page_size = 0) (Hd : 0 < d)
    (Hb0 : 0 < (((m_vmmaps model).vm_brk).toNat : Int))
    (Hnw : (((m_vmmaps model).vm_brk).toNat : Int) + d < 2 ^ 64)
    (Hs : (((m_vmmaps model).vm_start_brk).toNat : Int) ≤
      (((m_vmmaps model).vm_brk).toNat : Int) + d)
    (H10 : getr regs 10 = BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d))
    (Hadm : brk_grow_ok model
      (BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d))
      (BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d)) = true)
    (HA : srealizes segs (mkCfg (mkst (regupd regs 10 (m_vmmaps model).vm_brk)
            (v_addi pc 4) mem rom) model) KA)
    (HB : srealizes segs (mkCfg (mkst (regupd regs 10
              (BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d))) (v_addi pc 4)
            (zfill (m_vmmaps model).vm_brk (BitVec.ofInt 64 d) mem) rom)
          (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps model).vm_reserved
            (((m_vmmaps model).vm_brk, BitVec.ofInt 64 d) :: (m_vmmaps model).vm_maps)
            (m_vmmaps model).vm_noaccess (m_vmmaps model).vm_start_brk
            (BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d))
            (m_vmmaps model).vm_limit (m_vmmaps model).vm_mmap_base
            (m_vmmaps model).vm_init_sp) model)) KB) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt2 KA KB) := by
  let b : word := (m_vmmaps model).vm_brk
  let req : word := BitVec.ofInt 64 ((b.toNat : Int) + d)
  have hbdef : b = (m_vmmaps model).vm_brk := rfl
  have hb2 : ((b.toNat : Int)) = (((m_vmmaps model).vm_brk).toNat : Int) := rfl
  have hreqdef : req = BitVec.ofInt 64 ((b.toNat : Int) + d) := rfl
  have Hureq : (req.toNat : Int) = (b.toNat : Int) + d :=
    u64_lit ((b.toNat : Int) + d) ⟨by omega, Hnw⟩
  have Hbr : (b.toNat : Int) < 2 ^ 64 := by have := b.isLt; omega
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt2 KA KB) Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 214 := by
    rw [H17]; exact u64_lit 214 ⟨by decide, by decide⟩
  have H0 : ms_gpr ms 0 = req := by
    dsimp only [ms]
    rw [ms_gpr_epend0, H10]
  have Hpos : 0 < (req.toNat : Int) := by rw [Hureq]; omega
  have Hs' : (((m_vmmaps model).vm_start_brk).toNat : Int) ≤ (req.toNat : Int) := by
    rw [Hureq]; exact Hs
  have Hb' : (((m_vmmaps model).vm_brk).toNat : Int) ≤ (req.toNat : Int) := by
    rw [Hureq]; omega
  have Hcases : ∀ r, AllocSim.brk_resolution_ok model (ms_gpr ms 0) r ↔
      (r = b ∨ (r = req ∧ brk_grow_ok model req req = true)) := by
    intro r
    rw [H0]
    exact RefNodes.brk_r_ok_grow_cases model req r Hpos Hs' Hb'
  have Hkeep : AllocSim.brk_resolution_ok model (ms_gpr ms 0) b :=
    (Hcases b).mpr (Or.inl rfl)
  have Hgrow : AllocSim.brk_resolution_ok model (ms_gpr ms 0) req :=
    (Hcases req).mpr (Or.inr ⟨rfl, Hadm⟩)
  have Hneq : req ≠ b := by
    intro E
    have h := congrArg (fun (x : word) => (x.toNat : Int)) E
    rw [Hureq] at h
    omega
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun i : { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r } =>
      if bv_eqb i.1 b then KA else KB)) (t_alt2 KA KB) ?_ ?_
  · refine srz_cases segs (mkCfg ms model)
      { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
      (fun i => mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU i.1 []
            (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
            (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) i.1 model))
      (fun i => if bv_eqb i.1 b then KA else KB) ⟨b, Hkeep⟩ ?_ ?_
    · exact node_brk_lazy segs ms model (getr regs 17) Hh rfl Hno
    · intro i
      obtain ⟨r, hr⟩ := i
      rcases (Hcases r).mp hr with rfl | ⟨rfl, hg⟩
      · rw [PropExec.bv_eqb_refl]
        show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
            (SyscallEffect.mkEffectU b []
              (brk_zeros (ms_gpr ms 0) b b) (brk_unmaps b b) [] [])))
          (AllocSim.brk_model (ms_gpr ms 0) b model)) KA
        rw [H0, AllocSim.brk_zeros_keep, AllocSim.brk_unmaps_keep,
          RefNodes.brk_model_keep]
        dsimp only [ms]
        rw [adv_ret_epend]
        exact HA
      · rw [PropExec.bv_eqb_neq req b Hneq]
        have Hlt : (b.toNat : Int) < (req.toNat : Int) := by rw [Hureq]; omega
        have Hreq0 : req ≠ BitVec.ofInt 64 0 := by
          intro E
          have h := congrArg (fun (x : word) => (x.toNat : Int)) E
          rw [Hureq] at h
          have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
          rw [h0] at h
          omega
        have h1 : page_round_up_Z (b.toNat : Int) = (b.toNat : Int) :=
          AllocSim.page_round_up_Z_aligned _ (by omega) Hbal
        have h2 : page_round_up_Z (req.toNat : Int) = (b.toNat : Int) + d := by
          rw [Hureq]
          exact AllocSim.page_round_up_Z_aligned _ (by omega) (by
            rw [show ((b.toNat : Int) + d) % page_size = 0 by
              rw [Int.add_emod, Hbal, Hdal]; simp])
        have Hzeros : brk_zeros (ms_gpr ms 0) req b = [(b, BitVec.ofInt 64 d)] := by
          rw [H0, AllocSim.brk_zeros_grow req req b Hreq0 Hb0 Hlt]
          unfold brk_page_range
          rw [h1, h2]
          rw [ite_eq_left (show (b.toNat : Int) < (b.toNat : Int) + d from by omega)]
          rw [show BitVec.ofInt 64 (b.toNat : Int) = b from RefNodes.Z_to_bv_u_eq' b _ rfl]
          rw [show ((b.toNat : Int) + d - (b.toNat : Int)) = d by omega]
        have Hunmaps : brk_unmaps req b = [] :=
          AllocSim.brk_unmaps_grow req b (by rw [Hureq]; omega)
        have Hmod : AllocSim.brk_model (ms_gpr ms 0) req model =
            with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps model).vm_reserved
              (((m_vmmaps model).vm_brk, BitVec.ofInt 64 d) :: (m_vmmaps model).vm_maps)
              (m_vmmaps model).vm_noaccess (m_vmmaps model).vm_start_brk
              (BitVec.ofInt 64 ((((m_vmmaps model).vm_brk).toNat : Int) + d))
              (m_vmmaps model).vm_limit (m_vmmaps model).vm_mmap_base
              (m_vmmaps model).vm_init_sp) model := by
          rw [H0]
          exact RefNodes.brk_model_grow_eq model d Hd Hb0 Hnw Hbal Hdal
        rw [Hzeros, Hunmaps, Hmod]
        dsimp only [ms]
        rw [adv_zeros1_epend]
        exact HB
  · intro tr
    constructor
    · rintro ⟨i, hT⟩
      show KA tr ∨ KB tr
      by_cases h : bv_eqb i.1 b = true
      · exact Or.inl (by rw [ite_eq_left h] at hT; exact hT)
      · exact Or.inr (by rw [ite_eq_right h] at hT; exact hT)
    · rintro (hT | hT)
      · refine ⟨⟨b, Hkeep⟩, ?_⟩
        show (if bv_eqb b b = true then KA else KB) tr
        rw [PropExec.bv_eqb_refl]
        simpa using hT
      · refine ⟨⟨req, Hgrow⟩, ?_⟩
        show (if bv_eqb req b = true then KA else KB) tr
        rw [PropExec.bv_eqb_neq req b Hneq]
        simpa using hT

/-- brk GROW that is provably blocked (`brk_grow_ok model req req = false`):
    the only resolution is the unchanged break, so the node is silent. -/
theorem srz_brk_grow_blocked_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (req : word) (KA : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 214)
    (H10 : getr regs 10 = req)
    (Hpos : 0 < (req.toNat : Int))
    (Hs : (((m_vmmaps model).vm_start_brk).toNat : Int) ≤ (req.toNat : Int))
    (Hb : (((m_vmmaps model).vm_brk).toNat : Int) ≤ (req.toNat : Int))
    (Hblk : brk_grow_ok model req req = false)
    (HA : srealizes segs (mkCfg (mkst (regupd regs 10 (m_vmmaps model).vm_brk)
            (v_addi pc 4) mem rom) model) KA) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) KA := by
  let b : word := (m_vmmaps model).vm_brk
  refine srz_sys_lazy segs regs pc mem rom model w KA Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 214 := by
    rw [H17]; exact u64_lit 214 ⟨by decide, by decide⟩
  have H0 : ms_gpr ms 0 = req := by
    dsimp only [ms]; rw [ms_gpr_epend0, H10]
  have Hcases : ∀ r, AllocSim.brk_resolution_ok model (ms_gpr ms 0) r ↔ r = b := by
    intro r
    rw [H0]
    have h := RefNodes.brk_r_ok_grow_cases model req r Hpos Hs Hb
    constructor
    · intro hr
      rcases h.mp hr with h1 | ⟨h1, h2⟩
      · exact h1
      · rw [Hblk] at h2
        exact absurd h2 (by simp)
    · intro h1; exact h.mpr (Or.inl h1)
  have Hkeep : AllocSim.brk_resolution_ok model (ms_gpr ms 0) b := (Hcases b).mpr rfl
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun _ : { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r } => KA)) KA
    ?_ ?_
  · refine srz_cases segs (mkCfg ms model)
      { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
      (fun i => mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU i.1 []
            (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
            (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) i.1 model))
      (fun _ => KA) ⟨b, Hkeep⟩ ?_ ?_
    · exact node_brk_lazy segs ms model (getr regs 17) Hh rfl Hno
    · intro i
      obtain ⟨r, hr⟩ := i
      have Er : r = b := (Hcases r).mp hr
      subst Er
      show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU b []
            (brk_zeros (ms_gpr ms 0) b b) (brk_unmaps b b) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) b model)) KA
      rw [H0, AllocSim.brk_zeros_keep, AllocSim.brk_unmaps_keep, RefNodes.brk_model_keep]
      dsimp only [ms]
      rw [adv_ret_epend]
      exact HA
  · intro tr
    constructor
    · rintro ⟨i, hT⟩; exact hT
    · intro hT; exact ⟨⟨b, Hkeep⟩, hT⟩

/- =========================================================================
   6. set_tid_address, exit
   ========================================================================= -/

/-- The first `set_tid_address`: the resolution is any tid in the envelope,
    the successor records it (`with_tid`) and returns it in `a0`; the effect
    touches no memory, so no lazy premise is needed. -/
theorem node_set_tid_lazy (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 96) (Htid : m_tid model = none) :
    node_ok segs (mkCfg ms model) tid_I (fun _ => [])
      (fun i => mkCfg (advance_past_svc (apply_effect ms
        (SyscallEffect.mkEffectU i.1 [] [] [] [] []))) (with_tid i.1 model)) := by
  have Hchk : ∀ eff : SyscallEffect,
      check_syscall (sys_input segs ms x8) eff model
        = (match eff with
           | ⟨ret, [], [], [], [], []⟩ =>
               if decide (0 < (ret.toNat : Int)) &&
                  decide ((ret.toNat : Int)
                    < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE)
               then .CheckOk (with_tid ret model) [] else .CheckReject
           | _ => .CheckReject) := by
    intro eff
    rw [check_syscall_96 segs ms x8 eff model Hno]
    unfold LinuxSem.Checks.Sys.Kernel.Fork.check_set_tid_address
    rw [Htid]
    rfl
  refine node_chk_noacc segs ms model x8 tid_I
    (fun i => SyscallEffect.mkEffectU i.1 [] [] [] [] [])
    (fun i => with_tid i.1 model) Hh Hsvc ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [Hchk]
    have hA : decide (0 < (i.1.toNat : Int)) = true := by simpa using i.2.1
    have hB : decide ((i.1.toNat : Int)
        < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE) = true := by
      simpa using i.2.2
    simp only [hA, hB, Bool.and_true, ite_true]
  · rintro ⟨ret, ws, zs, us, cs, ci⟩ m' ev hc
    rw [Hchk] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases ws with _ | ⟨w, ws'⟩
    · rcases zs with _ | ⟨z, zs'⟩
      · rcases us with _ | ⟨u, us'⟩
        · rcases cs with _ | ⟨c, cs'⟩
          · rcases ci with _ | ⟨x, ci'⟩
            · by_cases hcond : (0 < (ret.toNat : Int))
                  ∧ ((ret.toNat : Int)
                      < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE)
              · simp only [ite_eq_left hcond] at hc
                obtain ⟨rfl, rfl⟩ := hc
                exact ⟨⟨ret, hcond.1, hcond.2⟩, rfl, rfl, rfl⟩
              · simp only [ite_eq_right hcond] at hc
                simp at hc
            · simp at hc
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  · rintro ⟨ret, ws, zs, us, cs, ci⟩ hc
    rw [Hchk] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases ws with _ | ⟨w, ws'⟩
    · rcases zs with _ | ⟨z, zs'⟩
      · rcases us with _ | ⟨u, us'⟩
        · rcases cs with _ | ⟨c, cs'⟩
          · rcases ci with _ | ⟨x, ci'⟩
            · by_cases hcond : (0 < (ret.toNat : Int))
                  ∧ ((ret.toNat : Int)
                      < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE)
              · simp only [ite_eq_left hcond] at hc
                simp at hc
              · simp only [ite_eq_right hcond] at hc
                simp at hc
            · simp at hc
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  · intro i
    show m_halted (with_tid i.1 model) = none
    rw [with_tid_halted]; exact Hh
  · intro i; rfl

theorem srz_set_tid_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (K : TSet) (w : BitVec 32)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 96)
    (Htid : m_tid model = none)
    (Hk : ∀ tid : word, (0 < (tid.toNat : Int) ∧
        (tid.toNat : Int) < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE) →
      srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom)
        (with_tid tid model)) K) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) K := by
  refine srz_sys_lazy segs regs pc mem rom model w K Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 96 := by
    rw [H17]; exact u64_lit 96 ⟨by decide, by decide⟩
  refine srz_conseq segs (mkCfg ms model)
    (t_alt (fun _ : tid_I => K)) K ?_ ?_
  · refine srz_cases segs (mkCfg ms model) tid_I
      (fun i => mkCfg (advance_past_svc (apply_effect ms
        (SyscallEffect.mkEffectU i.1 [] [] [] [] []))) (with_tid i.1 model))
      (fun _ => K) ⟨BitVec.ofInt 64 1, RefNodes.one_tid_ok⟩ ?_ ?_
    · exact node_set_tid_lazy segs ms model (getr regs 17) Hh rfl Hno Htid
    · intro i
      show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
        (SyscallEffect.mkEffectU i.1 [] [] [] [] []))) (with_tid i.1 model)) K
      rw [CatSim.apply_effect_no_write]
      dsimp only [ms]
      rw [AgentNodes.adv_set_epend]
      exact Hk i.1 ⟨i.2.1, i.2.2⟩
  · intro tr
    constructor
    · rintro ⟨i, hT⟩; exact hT
    · intro hT; exact ⟨⟨BitVec.ofInt 64 1, RefNodes.one_tid_ok⟩, hT⟩

theorem srz_exit_at_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (code : word)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 94 ∨ getr regs 17 = BitVec.ofInt 64 93)
    (H10 : getr regs 10 = code) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model)
      (t_exit (code &&& BitVec.ofInt 64 255) (m_fs model)) := by
  refine srz_sys_lazy segs regs pc mem rom model w _ Hh HF HE ?_
  have hx8 : is_exit_no (getr regs 17) := by
    rcases H17 with h | h
    · right; rw [h]; rfl
    · left; rw [h]; rfl
  rw [← H10, ← ms_gpr_epend0]
  exact srz_exit segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) Hh rfl hx8

/- =========================================================================
   7. Small generic facts
   ========================================================================= -/

/-  `bv_and_255` concludes `Z_to_bv 64 (Z.land c0 255)`.
   Lean core has no `Int.land`, so this tree concludes `c0 % 256`, which IS
   `Z.land c0 255` for `0 <= c0` (the lemma's hypothesis).  The `255` operand
   is unchanged, so every use site is unaffected. -/

/-- `is_ecall_at` read back: the pc window and the fetched `ecall`. -/
theorem is_ecall_at_sound (SEGS : List Segment) (cs : acs)
    (H : is_ecall_at SEGS cs = true) :
    0 ≤ pc cs ∧ pc cs + 4 < two64 ∧
      ∃ w, fetch_word SEGS (BitVec.ofInt 64 (pc cs)) = some w ∧ is_ecall w = true := by
  unfold is_ecall_at at H
  rw [Bool.and_eq_true, Bool.and_eq_true] at H
  obtain ⟨⟨h0, h4⟩, hf⟩ := H
  rw [decide_eq_true_eq] at h0 h4
  cases hw : fetch_word SEGS (BitVec.ofInt 64 (pc cs)) with
  | none => simp [hw] at hf
  | some w => exact ⟨h0, h4, w, rfl, by simpa [hw] using hf⟩

theorem Some_inj {T : Type} (a b : T) (h : some a = some b) : a = b :=
  Option.some.inj h

theorem v_addi_pc (p : Int) (H0 : 0 ≤ p) (H4 : p + 4 < two64) :
    v_addi (BitVec.ofInt 64 p) 4 = BitVec.ofInt 64 (p + 4) := by
  have h4' : p < 2 ^ 64 := by unfold two64 at H4; omega
  exact AgentLib.v_addi_lit p 4 ⟨H0, h4'⟩

theorem bv_and_255 (c0 : Int) (Hc : 0 ≤ c0 ∧ c0 < two64) :
    (BitVec.ofInt 64 c0 &&& BitVec.ofInt 64 255) = BitVec.ofInt 64 (c0 % 256) := by
  have htop : c0 < ((2 ^ 64 : Nat) : Int) := by
    have h : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := Int.natCast_pow 2 64
    rw [h]; unfold two64 at Hc; exact Hc.2
  have hc0 : (BitVec.ofInt 64 c0).toNat = c0.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt Hc.1 htop]
  have h255 : (BitVec.ofInt 64 255).toNat = 255 := by decide
  have hres : (BitVec.ofInt 64 (c0 % 256)).toNat = c0.toNat % 256 := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt]
    · rw [Int.toNat_emod Hc.1 (by decide)]
      rfl
    · exact Int.emod_nonneg _ (by decide)
    · have := Int.emod_lt_of_pos c0 (by decide : (0 : Int) < 256); omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, hc0, h255, hres]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
    show (2 : Nat) ^ 8 = 256 from by decide]

/- =========================================================================
   6b. MAP_FIXED wholly inside one live mapping: THREE resolutions
       (both prot spellings and both flag spellings, no lazy premise,
       srealizes)
   ========================================================================= -/

/-- At core flags `50` (private + anonymous + fixed) none of the other mmap
    shapes match, and only the `PROT_NONE` / rw `MAP_FIXED` gates do. -/
theorem mmap_gates_core50 (flags prot : word) (Hc : mmap_flags_core flags = 50) :
    mmap_modeled_b prot flags (BitVec.ofInt 64 0) = false ∧
    mmap_noaccess_b prot flags (BitVec.ofInt 64 0) = false ∧
    mmap_fixed_noaccess_b (BitVec.ofInt 64 0) flags (BitVec.ofInt 64 0) = true ∧
    mmap_fixed_noaccess_b (BitVec.ofInt 64 3) flags (BitVec.ofInt 64 0) = false ∧
    mmap_fixed_rw_b (BitVec.ofInt 64 3) flags (BitVec.ofInt 64 0) = true := by
  unfold mmap_modeled_b mmap_noaccess_b mmap_fixed_noaccess_b mmap_fixed_rw_b
  rw [Hc]
  have h34 : ((50 : Int) == (LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_PRIVATE +
      LinuxSem.LinuxProcessSem.Sys.Uapi.MAP_ANONYMOUS)) = false := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [h34]
  · simp [h34]
  · decide
  · decide
  · decide

theorem srz_alt3 (segs : List Segment) (c : config) (nx : three → config) (A B C : TSet)
    (Hnode : node_ok segs c three (fun _ => []) nx)
    (HA : srealizes segs (nx three.T1) A) (HB : srealizes segs (nx three.T2) B)
    (HC : srealizes segs (nx three.T3) C) :
    srealizes segs c (t_alt3 A B C) := by
  refine srz_conseq segs c
    (t_alt (fun i => match i with
      | three.T1 => A
      | three.T2 => B
      | three.T3 => C)) (t_alt3 A B C) ?_ ?_
  · refine srz_cases segs c three nx (fun i => match i with
      | three.T1 => A
      | three.T2 => B
      | three.T3 => C) three.T1 Hnode ?_
    intro i
    cases i with
    | T1 => exact HA
    | T2 => exact HB
    | T3 => exact HC
  · intro tr
    unfold t_alt3 t_alt2 t_alt
    constructor
    · rintro ⟨i, h⟩
      cases i with
      | T1 => exact Or.inl h
      | T2 => exact Or.inr (Or.inl h)
      | T3 => exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact ⟨three.T1, h⟩
      · exact ⟨three.T2, h⟩
      · exact ⟨three.T3, h⟩

def fixedin_ok_vmmaps (prot : Int) (addr n : word) (h : VmMaps) : VmMaps :=
  if prot = 0 then
    VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps
      ((addr, n) :: maps_subtract h.vm_noaccess (addr.toNat : Int)
        ((addr.toNat : Int) + (n.toNat : Int)))
      h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp
  else mmap_fixed_rw_next h addr n

def fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  VmMaps.mkVmMapsFull h.vm_reserved
    (maps_subtract h.vm_maps (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
    (maps_subtract h.vm_noaccess (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
    h.vm_start_brk h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp

def fixedin_ok_model (prot : Int) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n
    (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m)

def fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m

def fixedin_ok_eff (prot : Int) (addr n : word) : SyscallEffect :=
  if prot = 0 then SyscallEffect.mkEffectU addr [] [] [(addr, n)] [] []
  else SyscallEffect.mkEffectU addr [] [(addr, n)] [] [] []

theorem with_mmap_replacement_halted' (flags a n : word) (m : Model) :
    m_halted (with_mmap_replacement flags a n m) = m_halted m :=
  with_mmap_replacement_halted flags a n m

theorem with_mmap_destroyed_halted' (a n : word) (h : VmMaps) (m : Model) :
    m_halted (with_mmap_destroyed a n h m) = m_halted m :=
  with_mmap_destroyed_halted a n h m

/-- The checker collapse on the contained `MAP_FIXED` branch.

    A request wholly inside one live mapping, at core flags `50`, with `prot`
    either `PROT_NONE` (0) or `PROT_READ|PROT_WRITE` (3): each `prot` opens
    exactly one of `check_mmap`'s two contained arms (`G3` for `PROT_NONE`,
    `G4`/`G5` for rw, out of [mmap_gates_core50]), the guards above those arms
    are all discharged by the hypotheses (`two_pow_64` and `alloc_top` bounds
    from the ceiling, page alignment, positivity, the `region_free` /
    `map_contains` pair that keeps the request inside one live mapping), and
    the effect match then has exactly three successes: the errno with the range
    preserved, the errno with the range destroyed, and the replacement.

    The two post-states are the named ones: [fixedin_destroyed_model] is
    `with_mmap_destroyed` over `mmap_fixed_destroyed_next`, [fixedin_ok_model]
    is `with_mmap_replacement` over [fixedin_ok_vmmaps] (`mmap_fixed_rw_next`
    for rw, the `PROT_NONE` push onto `vm_noaccess` otherwise) — the same terms
    the checker writes inline, so each arm of the collapse closes by `rfl`.
-/
theorem mmap_fixedin_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (prot : Int) (flags addr : word) (len : Int)
    (Hno : (x8.toNat : Int) = 222)
    (Hprot : prot = 0 ∨ prot = 3)
    (Hcore : mmap_flags_core flags = 50)
    (H0 : ms_gpr ms 0 = addr) (Hal : (addr.toNat : Int) % page_size = 0)
    (Hpos : 0 < (addr.toNat : Int))
    (H1 : ms_gpr ms 1 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 prot) (H3 : ms_gpr ms 3 = flags)
    (H4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1)) (H5 : ms_gpr ms 5 = BitVec.ofInt 64 0)
    (Hce : (addr.toNat : Int) + page_round_up_Z len ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (n : word) (Hn : n = BitVec.ofInt 64 (page_round_up_Z len))
    (Hrf : region_free (m_vmmaps model).vm_reserved addr n = true)
    (Hmc : map_contains (m_vmmaps model).vm_maps addr n = true)
    (Hbud : prot = 3 → mmap_fixed_rw_budget_ok flags model addr n = true) :
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
        | ⟨r, [], zs, us, [], []⟩ =>
            if errno_ret_in mmap_errnos r then
              (match zs, us with
               | [], [] => check_result.CheckOk model []
               | [], _ =>
                   if listNN_eqb us [(addr, n)] then
                     check_result.CheckOk (fixedin_destroyed_model addr n model) []
                   else check_result.CheckReject
               | _, _ => check_result.CheckReject)
            else if prot = 0 then
              (match zs with
               | [] =>
                   if bv_eqb r addr && listNN_eqb us [(addr, n)] then
                     check_result.CheckOk (fixedin_ok_model prot flags addr n model) []
                   else check_result.CheckReject
               | _ => check_result.CheckReject)
            else
              (match us with
               | [] =>
                   if bv_eqb r addr && listNN_eqb zs [(addr, n)] then
                     check_result.CheckOk (fixedin_ok_model prot flags addr n model) []
                   else check_result.CheckReject
               | _ => check_result.CheckReject)
        | _ => check_result.CheckReject) := by
  have Hlen' : len < 2 ^ 64 := by
    have h1 : len ≤ page_round_up_Z len := AsanCeil.page_round_up_Z_ge_all len
    have h2 : ((addr.toNat : Int)) < 2 ^ 64 := by have := addr.isLt; omega
    have h3 : alloc_ceiling < 2 ^ 64 := by unfold alloc_ceiling; decide
    omega
  have hgr1 : ((BitVec.ofInt 64 len).toNat : Int) = len := u64_lit len ⟨by omega, Hlen'⟩
  have hne : BitVec.ofInt 64 len ≠ BitVec.ofInt 64 0 := by
    intro h
    have h2 := congrArg (fun (x : word) => (x.toNat : Int)) h
    rw [hgr1] at h2
    have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by simp
    rw [h0] at h2
    omega
  have hlen0 : w_is0 (BitVec.ofInt 64 len) = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ hne
  have hanon : mmap_anon_b flags = true :=
    AsanCeil.mmap_anon_b_of_core flags 50 Hcore (by decide)
  have htop : ¬ (two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z len) := by
    have h3 : alloc_ceiling < two_pow_64 := by unfold alloc_ceiling two_pow_64; decide
    omega
  have hle : (addr.toNat : Int) + page_round_up_Z len ≤ alloc_top (m_vmmaps model) :=
    AsanCeil.alloc_top_ge_of_ceiling _ _ Hisp Hce
  have hal : ((addr.toNat : Int) % page_size == 0) = true := beq_iff_eq.mpr Hal
  subst Hn
  rcases Hprot with rfl | rfl
  · obtain ⟨Gm, Gn, Gfn, -, -⟩ := mmap_gates_core50 flags (BitVec.ofInt 64 0) Hcore
    rw [RefNodes.mmap_check segs ms x8 model eff Hno]
    unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
    simp only [H2, H3, H5, H0, H1, hgr1, htop, hle, hal, Hpos, hlen0, hanon, Gm, Gn, Gfn,
      Hrf, Hmc, AsanCeil.mmap_off_aligned_b_0, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, not_true_eq_false,
      not_false_eq_true, Bool.and_true, Bool.and_false, Bool.or_false, Bool.or_true,
      decide_true, decide_false]
    dsimp only [fixedin_ok_model, fixedin_ok_vmmaps, fixedin_destroyed_model,
      fixedin_destroyed_vmmaps, mmap_fixed_destroyed_next]
    obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
    rcases ws with _ | ⟨w, ws⟩ <;> rcases zs with _ | ⟨z, zs⟩ <;>
      rcases us with _ | ⟨u, us⟩ <;> rcases cs with _ | ⟨c, cs⟩ <;>
      rcases ci with _ | ⟨i, ci⟩ <;> dsimp only
    all_goals (try rfl)
    all_goals simp only [ite_self]
  · obtain ⟨Gm, Gn, -, Gfn, Gfr⟩ := mmap_gates_core50 flags (BitVec.ofInt 64 3) Hcore
    have hbud3 : mmap_fixed_rw_budget_ok flags model addr
        (BitVec.ofInt 64 (page_round_up_Z len)) = true := Hbud rfl
    rw [RefNodes.mmap_check segs ms x8 model eff Hno]
    unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
    simp only [H2, H3, H5, H0, H1, hgr1, htop, hle, hal, Hpos, hlen0, hanon, Gm, Gn, Gfn,
      Gfr, hbud3, Hrf, Hmc, AsanCeil.mmap_off_aligned_b_0, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, not_true_eq_false,
      not_false_eq_true, Bool.and_true, Bool.and_false, Bool.or_false, Bool.or_true,
      decide_true, decide_false]
    dsimp only [fixedin_ok_model, fixedin_ok_vmmaps, fixedin_destroyed_model,
      fixedin_destroyed_vmmaps, mmap_fixed_destroyed_next]
    obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
    rcases ws with _ | ⟨w, ws⟩ <;> rcases zs with _ | ⟨z, zs⟩ <;>
      rcases us with _ | ⟨u, us⟩ <;> rcases cs with _ | ⟨c, cs⟩ <;>
      rcases ci with _ | ⟨i, ci⟩ <;> dsimp only
    all_goals (try rfl)
    all_goals simp only [ite_self]

/-- The contained `MAP_FIXED` node: three resolutions, all
    silent.

    - `KA`: `-ENOMEM` with everything preserved;
    - `KB`: success, `a0 := addr`; `PROT_NONE` erases the bytes, rw zero-fills them;
    - `KC`: `-ENOMEM` with the range DESTROYED (gone from both ledgers, bytes erased).

    The node is [node_chk_noacc] over the three effects of the collapse in
    [mmap_fixedin_check]: each carries no writes, no copies and no copy-ins,
    so `syscall_effect_accesses` is `[]` and the post-syscall materialisation
    is the identity whatever the lazy ledger holds.  The caller supplies the
    three continuations and [srz_alt3] turns them into `t_alt3 KA KB KC`; the
    three `-halted` obligations are the two primed lemmas plus `Hh`, and the
    continuations are [adv_ret_epend] for `KA`, [adv_unmaps1_epend] (PROT_NONE)
    or [adv_zeros1_epend] (rw) for `KB`, and [adv_unmaps1_epend] for `KC`. -/
theorem srz_mmap_fixedin_lazy (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (prot : Int)
    (flags addr : word) (len : Int) (KA KB KC : TSet)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none)
    (H17 : getr regs 17 = BitVec.ofInt 64 222)
    (Hprot : prot = 0 ∨ prot = 3) (Hcore : mmap_flags_core flags = 50)
    (H10 : getr regs 10 = addr) (Hal : (addr.toNat : Int) % page_size = 0)
    (Hpos : 0 < (addr.toNat : Int))
    (H11 : getr regs 11 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hce : (addr.toNat : Int) + page_round_up_Z len ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps model))
    (H12 : getr regs 12 = BitVec.ofInt 64 prot) (H13 : getr regs 13 = flags)
    (H14 : getr regs 14 = BitVec.ofInt 64 (-1)) (H15 : getr regs 15 = BitVec.ofInt 64 0)
    (n : word) (Hn : n = BitVec.ofInt 64 (page_round_up_Z len))
    (Hrf : region_free (m_vmmaps model).vm_reserved addr n = true)
    (Hmc : map_contains (m_vmmaps model).vm_maps addr n = true)
    (Hbud : prot = 3 → mmap_fixed_rw_budget_ok flags model addr n = true)
    (HA : srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM))
            (v_addi pc 4) mem rom) model) KA)
    (HB : srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
            (if prot = 0 then unfill addr n mem else zfill addr n mem) rom)
          (fixedin_ok_model prot flags addr n model)) KB)
    (HC : srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4)
            (unfill addr n mem) rom) (fixedin_destroyed_model addr n model)) KC) :
    srealizes segs (mkCfg (mkst regs pc mem rom) model) (t_alt3 KA KB KC) := by
  refine srz_sys_lazy segs regs pc mem rom model w (t_alt3 KA KB KC) Hh HF HE ?_
  let ms : machine_state := epend regs pc mem rom (getr regs 17)
  have Hno : ((getr regs 17).toNat : Int) = 222 := by
    rw [H17]; exact u64_lit 222 ⟨by decide, by decide⟩
  have Hlen' : len < 2 ^ 64 := by
    have h1 : len ≤ page_round_up_Z len := (page_round_up_Z_bounds len (by omega)).1
    have h2 : ((addr.toNat : Int)) < 2 ^ 64 := by have := addr.isLt; omega
    have h3 : alloc_ceiling < 2 ^ 64 := by unfold alloc_ceiling; decide
    omega
  have h0 : ms_gpr ms 0 = addr := by dsimp only [ms]; rw [ms_gpr_epend0, H10]
  have h1 : ms_gpr ms 1 = BitVec.ofInt 64 len := by
    dsimp only [ms]; rw [ms_gpr_epend1, H11]
  have h2 : ms_gpr ms 2 = BitVec.ofInt 64 prot := by
    dsimp only [ms]; rw [ms_gpr_epend2, H12]
  have h3 : ms_gpr ms 3 = flags := by dsimp only [ms]; rw [ms_gpr_epend3, H13]
  have h4 : ms_gpr ms 4 = BitVec.ofInt 64 (-1) := by
    dsimp only [ms]; rw [ms_gpr_epend4, H14]
  have h5 : ms_gpr ms 5 = BitVec.ofInt 64 0 := by
    dsimp only [ms]; rw [ms_gpr_epend5, H15]
  have Hchk := fun eff => mmap_fixedin_check segs ms (getr regs 17) model eff prot flags addr
    len Hno Hprot Hcore h0 Hal Hpos h1 Hlen h2 h3 h4 h5 Hce Hisp n Hn Hrf Hmc Hbud
  have hmem : ENOMEM ∈ mmap_errnos := by simp [mmap_errnos]
  have herrT : errno_ret_in mmap_errnos (errno_ret ENOMEM) = true :=
    errno_ret_in_intro mmap_errnos ENOMEM hmem
  have Haddr_ne : errno_ret_in mmap_errnos addr = false := by
    refine errno_ret_in_below mmap_errnos addr (by decide) ?_
    have h3 : alloc_ceiling < two_pow_64 - 4096 := by
      unfold alloc_ceiling two_pow_64; decide
    have h1 : len ≤ page_round_up_Z len := (page_round_up_Z_bounds len (by omega)).1
    omega
  let effs : three → SyscallEffect := fun i => match i with
    | three.T1 => SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] []
    | three.T2 => fixedin_ok_eff prot addr n
    | three.T3 => SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] []
  let ms' : three → Model := fun i => match i with
    | three.T1 => model
    | three.T2 => fixedin_ok_model prot flags addr n model
    | three.T3 => fixedin_destroyed_model addr n model
  refine srz_alt3 segs (mkCfg ms model)
    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB KC ?_ ?_ ?_ ?_
  · refine node_chk_noacc segs ms model (getr regs 17) three effs ms' Hh rfl ?_ ?_ ?_ ?_ ?_
    · intro i
      cases i with
      | T1 =>
        show check_syscall (sys_input segs ms (getr regs 17))
            (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] []) model
          = check_result.CheckOk model []
        rw [Hchk (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] [])]
        dsimp only
        rw [ite_eq_left herrT]
      | T2 =>
        show check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
          = check_result.CheckOk (fixedin_ok_model prot flags addr n model) []
        dsimp only [fixedin_ok_eff]
        by_cases hp : prot = 0
        · rw [ite_eq_left hp]
          rw [Hchk (SyscallEffect.mkEffectU addr [] [] [(addr, n)] [] [])]
          dsimp only
          rw [ite_eq_right (by rw [Haddr_ne]; simp)]
          rw [ite_eq_left hp]
          have hb : (bv_eqb addr addr && listNN_eqb [(addr, n)] [(addr, n)]) = true := by
            rw [PropExec.bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl
          rw [ite_eq_left hb]
        · rw [ite_eq_right hp]
          rw [Hchk (SyscallEffect.mkEffectU addr [] [(addr, n)] [] [] [])]
          dsimp only
          rw [ite_eq_right (by rw [Haddr_ne]; simp)]
          rw [ite_eq_right hp]
          have hb : (bv_eqb addr addr && listNN_eqb [(addr, n)] [(addr, n)]) = true := by
            rw [PropExec.bv_eqb_refl, (listNN_eqb_eq _ _).mpr rfl]; rfl
          rw [ite_eq_left hb]
      | T3 =>
        show check_syscall (sys_input segs ms (getr regs 17))
            (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] []) model
          = check_result.CheckOk (fixedin_destroyed_model addr n model) []
        rw [Hchk (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [])]
        dsimp only
        rw [ite_eq_left herrT]
        have hl : listNN_eqb [(addr, n)] [(addr, n)] = true := (listNN_eqb_eq _ _).mpr rfl
        rw [ite_eq_left hl]
    · rintro ⟨r, ws, zs, us, cs, ci⟩ m' evs hc
      rw [Hchk ⟨r, ws, zs, us, cs, ci⟩] at hc
      rcases ws with _ | ⟨w0, ws⟩
      · rcases cs with _ | ⟨c0, cs⟩
        · rcases ci with _ | ⟨i0, ci⟩
          · rcases zs with _ | ⟨z0, zs⟩
            · rcases us with _ | ⟨u0, us⟩
              · -- (a) the only admissible effect here is the plain errno
                dsimp only at hc
                by_cases herr : errno_ret_in mmap_errnos r = true
                · rw [ite_eq_left herr] at hc
                  have hr : r = errno_ret ENOMEM := by
                    obtain ⟨e, he, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                    have he' : e = ENOMEM := by simpa [mmap_errnos] using he
                    rw [he']
                  subst hr
                  cases hc
                  exact ⟨three.T1, rfl, rfl, rfl⟩
                · rw [ite_eq_right herr] at hc
                  by_cases hp : prot = 0
                  · rw [ite_eq_left hp] at hc
                    by_cases hb : (bv_eqb r addr && listNN_eqb ([] : List (word × word))
                        [(addr, n)]) = true
                    · exfalso
                      rw [Bool.and_eq_true] at hb
                      have hl : ([] : List (word × word)) = [(addr, n)] :=
                        (listNN_eqb_eq _ _).mp hb.2
                      simp at hl
                    · rw [ite_eq_right hb] at hc
                      cases hc
                  · rw [ite_eq_right hp] at hc
                    by_cases hb : (bv_eqb r addr && listNN_eqb ([] : List (word × word))
                        [(addr, n)]) = true
                    · exfalso
                      rw [Bool.and_eq_true] at hb
                      have hl : ([] : List (word × word)) = [(addr, n)] :=
                        (listNN_eqb_eq _ _).mp hb.2
                      simp at hl
                    · rw [ite_eq_right hb] at hc
                      cases hc
              · -- (b) errno with the range destroyed, or the PROT_NONE success
                dsimp only at hc
                by_cases herr : errno_ret_in mmap_errnos r = true
                · rw [ite_eq_left herr] at hc
                  have hr : r = errno_ret ENOMEM := by
                    obtain ⟨e, he, rfl⟩ := (errno_ret_in_true mmap_errnos r).mp herr
                    have he' : e = ENOMEM := by simpa [mmap_errnos] using he
                    rw [he']
                  subst hr
                  by_cases hl : listNN_eqb (u0 :: us) [(addr, n)] = true
                  · rw [ite_eq_left hl] at hc
                    have hul : (u0 :: us) = [(addr, n)] := (listNN_eqb_eq _ _).mp hl
                    rw [hul]
                    cases hc
                    exact ⟨three.T3, rfl, rfl, rfl⟩
                  · rw [ite_eq_right hl] at hc
                    cases hc
                · rw [ite_eq_right herr] at hc
                  by_cases hp : prot = 0
                  · rw [ite_eq_left hp] at hc
                    by_cases hb : (bv_eqb r addr && listNN_eqb (u0 :: us) [(addr, n)]) = true
                    · rw [ite_eq_left hb] at hc
                      rw [Bool.and_eq_true] at hb
                      obtain ⟨hb1, hb2⟩ := hb
                      have hr : r = addr := (Fs.bv_eqb_eq r addr).mp hb1
                      have hu : (u0 :: us) = [(addr, n)] := (listNN_eqb_eq _ _).mp hb2
                      subst hr
                      rw [hu]
                      cases hc
                      refine ⟨three.T2, ?_, rfl, rfl⟩
                      dsimp only [effs, fixedin_ok_eff]
                      rw [ite_eq_left hp]
                    · rw [ite_eq_right hb] at hc
                      cases hc
                  · rw [ite_eq_right hp] at hc
                    cases hc
            · rcases us with _ | ⟨u0, us⟩
              · -- (c) the rw success
                dsimp only at hc
                by_cases herr : errno_ret_in mmap_errnos r = true
                · rw [ite_eq_left herr] at hc
                  cases hc
                · rw [ite_eq_right herr] at hc
                  by_cases hp : prot = 0
                  · rw [ite_eq_left hp] at hc
                    cases hc
                  · rw [ite_eq_right hp] at hc
                    by_cases hb : (bv_eqb r addr && listNN_eqb (z0 :: zs) [(addr, n)]) = true
                    · rw [ite_eq_left hb] at hc
                      rw [Bool.and_eq_true] at hb
                      obtain ⟨hb1, hb2⟩ := hb
                      have hr : r = addr := (Fs.bv_eqb_eq r addr).mp hb1
                      have hz : (z0 :: zs) = [(addr, n)] := (listNN_eqb_eq _ _).mp hb2
                      subst hr
                      rw [hz]
                      cases hc
                      refine ⟨three.T2, ?_, rfl, rfl⟩
                      dsimp only [effs, fixedin_ok_eff]
                      rw [ite_eq_right hp]
                    · rw [ite_eq_right hb] at hc
                      cases hc
              · -- (d) both lists non-empty: every arm rejects
                dsimp only at hc
                by_cases herr : errno_ret_in mmap_errnos r = true
                · rw [ite_eq_left herr] at hc
                  cases hc
                · rw [ite_eq_right herr] at hc
                  by_cases hp : prot = 0
                  · rw [ite_eq_left hp] at hc
                    cases hc
                  · rw [ite_eq_right hp] at hc
                    cases hc
          · rcases zs with _ | ⟨z0, zs⟩ <;> rcases us with _ | ⟨u0, us⟩ <;>
              (try dsimp only at hc) <;> cases hc
        · rcases zs with _ | ⟨z0, zs⟩ <;> rcases us with _ | ⟨u0, us⟩ <;>
            (try dsimp only at hc) <;> cases hc
      · dsimp only at hc
        cases hc
    · rintro ⟨r, ws, zs, us, cs, ci⟩ hc
      rw [Hchk ⟨r, ws, zs, us, cs, ci⟩] at hc
      rcases ws with _ | ⟨w0, ws⟩ <;> rcases zs with _ | ⟨z0, zs⟩ <;>
        rcases us with _ | ⟨u0, us⟩ <;> rcases cs with _ | ⟨c0, cs⟩ <;>
        rcases ci with _ | ⟨i0, ci⟩ <;> (try dsimp only at hc)
      all_goals (repeat' (split at hc))
      all_goals (exact absurd hc (by simp))
    · intro i
      cases i with
      | T1 => exact Hh
      | T2 =>
        show m_halted (fixedin_ok_model prot flags addr n model) = none
        unfold fixedin_ok_model
        rw [with_mmap_replacement_halted, with_vmmaps_halted]
        exact Hh
      | T3 =>
        show m_halted (fixedin_destroyed_model addr n model) = none
        unfold fixedin_destroyed_model
        rw [with_mmap_destroyed_halted]
        exact Hh
    · intro i
      cases i with
      | T1 => rfl
      | T2 =>
        show syscall_effect_accesses (fixedin_ok_eff prot addr n) = []
        dsimp only [fixedin_ok_eff]
        by_cases hp : prot = 0
        · rw [ite_eq_left hp]; rfl
        · rw [ite_eq_right hp]; rfl
      | T3 => rfl
  · show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [] [] []))) (ms' three.T1)) KA
    dsimp only [ms']
    dsimp only [ms]
    rw [adv_ret_epend]
    exact HA
  · show srealizes segs (mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n)))
        (ms' three.T2)) KB
    dsimp only [ms']
    dsimp only [fixedin_ok_eff]
    by_cases hp : prot = 0
    · rw [ite_eq_left hp] at HB ⊢
      dsimp only [ms]
      rw [adv_unmaps1_epend]
      exact HB
    · rw [ite_eq_right hp] at HB ⊢
      dsimp only [ms]
      rw [adv_zeros1_epend]
      exact HB
  · show srealizes segs (mkCfg (advance_past_svc (apply_effect ms
        (SyscallEffect.mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [])))
        (ms' three.T3)) KC
    dsimp only [ms']
    dsimp only [ms]
    rw [adv_unmaps1_epend]
    exact HC

/- =========================================================================
   8. cs_ok helpers shared by the node packages
   ========================================================================= -/

/-- The REFUSED child of any memory syscall: registers `a0 := -ENOMEM`,
    `pc + 4`, model and memory unchanged.  `refuse` only rewrites the
    symbolic register file and the pc, so every `cs_ok` field but `co_regs`
    is carried over verbatim. -/
theorem pc_refuse (cs : acs) : pc (refuse cs) = pc cs + 4 := rfl

theorem nxt_refuse (cs : acs) : nxt (refuse cs) = nxt cs := rfl

theorem cs_ok_refuse (segs : List Segment) (A : atable) (LIMIT : Int)
    (SINV : env → (word → Option byte) → Prop) (argH : env → word → Bool) (FS0 : Fs.Fs)
    (E : env) (cs : acs) (R : BvMap word) (FULL : word → Option byte) (model : Model)
    (HC : cs_ok segs A LIMIT SINV argH FS0 E cs R FULL model) :
    cs_ok segs A LIMIT SINV argH FS0 E (refuse cs)
      (regupd R 10 (BitVec.ofInt 64 ENOMEM_RET)) FULL model := by
  obtain ⟨c_regs, c_log, c_know, c_halt, c_fds, c_fs, c_tid, c_res, c_limit, c_maps,
    c_holes, c_seps, c_wf, c_bounds, c_lazyb, c_nasub, c_none, c_kinds, c_totsz,
    c_split, c_brk, c_sbrk, c_eager, c_abytes, c_minv, c_zero, c_sinv⟩ := HC
  refine
    { co_regs := ?_
      co_log := ?_
      co_know := ?_
      co_halt := c_halt
      co_fds := c_fds
      co_fs := c_fs
      co_tid := c_tid
      co_res := c_res
      co_limit := c_limit
      co_maps := c_maps
      co_holes := c_holes
      co_seps := c_seps
      co_wf := c_wf
      co_bounds := c_bounds
      co_lazyb := c_lazyb
      co_nasub := c_nasub
      co_none := c_none
      co_kinds := c_kinds
      co_totsz := c_totsz
      co_split := c_split
      co_brk := c_brk
      co_sbrk := c_sbrk
      co_eager := c_eager
      co_abytes := c_abytes
      co_minv := c_minv
      co_zero := c_zero
      co_sinv := c_sinv }
  · exact AsanPlanSound.regs_ok_set_n E cs.a_ss.s_regs R 10 (.ELit ENOMEM_RET)
      (BitVec.ofInt 64 ENOMEM_RET) c_regs (by decide) rfl
  · rfl
  · exact c_know


