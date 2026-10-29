/-
  * Common.RefNodes — [realizes] syscall nodes for the syscalls the driver +
    musl issue, in continuation-passing style.

    Image-INDEPENDENT (Section over [segs]); the state on the ecall is
    [mkst regs pc mem (seg_rom segs)] and every lemma has the shape

      fetch_word segs pc = Some w -> is_ecall w = true ->
      m_halted model = None -> m_vm_lazy model = [] ->
      getr regs 17 = Z_to_bv 64 <nr> -> <argument / model facts> ->
      <one [realizes] hypothesis per outcome, at
         mkst (regupd regs 10 <ret>) (v_addi pc 4) <mem'> (seg_rom segs), <model'>> ->
      realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) <shape>.

    Nodes and checker equations: brk ([node_brk]), mmap ([mmap_check];
    PROT_NONE anonymous: [mmap_noaccess_check]; contained MAP_FIXED
    PROT_NONE: [fixed_noaccess_model]), mprotect ([mprotect_check]),
    munmap ([munmap_check]), set_tid_address ([node_set_tid]),
    exit/exit_group ([rz_exit_at]).  [writev] is LibWritev.rz_writev*.

    Every node is derived from the verified checker
    ([ExecutableSpecs.check_syscall]) through [Nodes.sstep_svc_inv] /
    [Nodes.node_chk].

    After the Section (image- and [segs]-independent, Z_scope):
    - LEDGER ALGEBRA for discharging the nodes' model-side hypotheses on
      concrete ledgers ([region_free_*], [map_has_*], [map_contains_*],
      [map_remove_*], [maps_subtract_*], [iv_subtract_*], [live_bytes_*]);
    - pigeonhole lemmas for an mmap grant address ([pick_candidate],
      [region_free_of_noconflict]);
    - [brk_grow_ok_aligned_intro] / [brk_grow_admissible_init].

    Notes:
    - every node takes [m_vm_lazy model = []] next to
      [m_halted model = None];
    - brk: [brk_r_ok]/[brk_grow_ok] take the MODEL (budget =
      [vm_backing_used]); post-model is [AllocSim.brk_model req r model]
      (= [Mmap.with_brk_next]), for which [brk_model_grow_eq] gives the
      explicit ledger on the aligned-grow path;
    - mmap PROT_NONE: the grant predicate has NO budget conjunct
      ([grant_ok_na]); mprotect rw over PROT_NONE: success additionally
      needs [mprotect_budget_ok]; MAP_FIXED PROT_NONE / munmap successors
      go through [vm_forget_range] ([fixed_noaccess_model] etc. below are
      stated with it).

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  * `Z` → `Int`, `N`/`nat` → `Nat`, `bv_and` → `&&&`,
    `Z_to_bv 64 n` → `BitVec.ofInt 64 n`, `bv_unsigned w` → `(w.toNat : Int)`,
    `None`/`Some` → `none`/`some`, `<>` → `≠`, `~` → `¬`.
 The 
    `End WithSegs` boundary is marked by a comment.
 Both statements are kept pointwise.
  * `Z.ltb_irrefl` is `decide (x < x) = false` here; `Z.leb_le`/`Z.ltb_lt`
    are `decide_eq_true_eq`; `Z.eqb_eq` is `beq_iff_eq`.
  * `List.Forall` statements ([iv_subtract_sizes], [maps_subtract_sizes],
    [map_remove_sizes], [pick_candidate]) are spelled pointwise as
    `∀ p ∈ l, ...`, the tree's convention; `List.NoDup` is `List.Nodup`.
  * Two  `let`-abbreviations are inlined, each flagged at its
    declaration: the `let h := m_vmmaps m in let b := vm_brk h in` prefix of
    [brk_r_ok_grow_cases] and [brk_grow_ok_aligned_intro], and the
    `let n := Z_to_bv 64 (page_round_up_Z len)` of [mprotect_check] (there it
    is kept, since it also appears in the conclusion).

  * `lemma` is not a declaration keyword in this Lake setup, so every 
    `Lemma` is a Lean `theorem`.
  Everything is proved here; there is no proof hole, no extra postulate and
  no `unsafe`, and no declaration is deferred.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
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
import LinuxSem.Common.SharedFacts
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
import LinuxSem.Common.AgentNodes
import LinuxSem.Common.SpecConsts
import LinuxSem.Common.AsanCeil

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.RefNodes

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
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.SharedFacts
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StreamExec
open LinuxSem.Common.MmapSim
open LinuxSem.Common.FileSim
open LinuxSem.Common.ShapeAlg
open LinuxSem.Common.Nodes
open LinuxSem.Common.AgentLib
open LinuxSem.Common.AgentNodes
open LinuxSem.Common.AsanCeil
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap

/-- The `FPState` instance every state in this file runs under: the entry
    state, as everywhere else in `Common`. -/
local instance refnodes_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   Shape helpers
   ========================================================================= -/

/-- Three-way silent choice, right-nested. -/
def t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C)

theorem t_alt2_idem (A : TSet) : t_eq (t_alt2 A A) A := by
  intro tr
  unfold t_alt2
  exact ⟨fun h => h.elim id id, fun h => Or.inl h⟩

theorem t_alt3_idem (A : TSet) : t_eq (t_alt3 A A A) A := by
  intro tr
  unfold t_alt3 t_alt2
  exact ⟨fun h => h.elim id (fun h' => h'.elim id id),
    fun h => Or.inl h⟩

/- =========================================================================
   Model plumbing
   ========================================================================= -/

theorem with_fds_halted' (fds : List (word × FdEntry)) (m : Model) :
    m_halted (with_fds fds m) = m_halted m := rfl

theorem with_fds_lazy (fds : List (word × FdEntry)) (m : Model) :
    m_vm_lazy (with_fds fds m) = m_vm_lazy m := rfl

theorem with_tid_halted (t : word) (m : Model) :
    m_halted (with_tid t m) = m_halted m := rfl

theorem with_tid_lazy (t : word) (m : Model) :
    m_vm_lazy (with_tid t m) = m_vm_lazy m := rfl

theorem with_vmmaps_lazy' (h : VmMaps) (m : Model) :
    m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := rfl

theorem with_vmmaps_eta (m : Model) : with_vmmaps (m_vmmaps m) m = m := by
  obtain ⟨fd, vm, io, fs, proc, lim, time⟩ := m
  obtain ⟨maps, lazy, mat⟩ := vm
  rfl

theorem vmmaps_eta (h : VmMaps) :
    VmMaps.mkVmMapsFull h.vm_reserved h.vm_maps h.vm_noaccess h.vm_start_brk
      h.vm_brk h.vm_limit h.vm_mmap_base h.vm_init_sp = h := by
  obtain ⟨res, maps, na, sb, b, lim, mb, sp⟩ := h
  rfl

/-- `Z_to_bv 64` of a word's unsigned value is the word. -/
theorem Z_to_bv_u_eq' (a : word) (z : Int) (H : z = (a.toNat : Int)) :
    BitVec.ofInt 64 z = a := by
  subst H
  refine BitVec.eq_of_toNat_eq ?_
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt]
  · simp
  · exact Int.natCast_nonneg _
  · have := a.isLt
    omega

/-- [vm_forget_range] on a model without lazy mappings or materialized
    pages is the identity (our binaries never create MAP_NORESERVE
    mappings, so both ledgers stay empty for the whole run). -/
theorem vm_forget_range_id (lo hi : Int) (m : Model)
    (Hl : m_vm_lazy m = []) (Hm : m_vm_materialized m = []) :
    vm_forget_range lo hi m = m := by
  obtain ⟨fd, vm, io, fs, proc, lim, time⟩ := m
  obtain ⟨maps, lazy, mat⟩ := vm
  simp only [m_vm_lazy, m_vm_materialized] at Hl Hm
  subst Hl
  subst Hm
  rfl

theorem vm_forget_range_lazy_nil (lo hi : Int) (m : Model)
    (Hl : m_vm_lazy m = []) : m_vm_lazy (vm_forget_range lo hi m) = [] := by
  rw [vm_forget_range]
  show maps_subtract (m_vm_lazy m) lo hi = []
  rw [Hl]
  rfl

theorem vm_forget_range_halted (lo hi : Int) (m : Model) :
    m_halted (vm_forget_range lo hi m) = m_halted m := rfl

/- =========================================================================
   Section WithSegs — every declaration below takes `segs` explicitly
   ========================================================================= -/

/-- The [check_syscall] equation for mmap ([MmapSim] reasons through
    [syscall_spec_mmap] instead). -/
theorem mmap_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (Hno : (x8.toNat : Int) = 222) :
    check_syscall (sys_input segs ms x8) eff model
      = LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
          (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3)
          (ms_gpr ms 4) (ms_gpr ms 5) eff model := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_mmap := by
    rw [in_sysno_sys_input, Hno]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, hlook,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_mmap,
    in_arg0_sys_input, StreamSim.in_arg1_sys_input, StreamSim.in_arg2_sys_input,
    in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input]

/-- The [check_syscall] equation for munmap. -/
theorem munmap_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (Hno : (x8.toNat : Int) = 215) :
    check_syscall (sys_input segs ms x8) eff model
      = LinuxSem.Checks.Sys.Mm.Mmap.check_munmap
          (ms_gpr ms 0) (ms_gpr ms 1) eff model := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_munmap := by
    rw [in_sysno_sys_input, Hno]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, hlook,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_munmap,
    in_arg0_sys_input, StreamSim.in_arg1_sys_input]

/- =========================================================================
   Generic: three-way silent nodes
   ========================================================================= -/

inductive three where
  | T1
  | T2
  | T3
  deriving DecidableEq, Repr

theorem rz_alt3 (segs : List Segment) (c : config) (nx : three → config)
    (A B C : TSet)
    (Hnode : node_ok segs c three (fun _ => []) nx)
    (HA : realizes segs (nx three.T1) A) (HB : realizes segs (nx three.T2) B)
    (HC : realizes segs (nx three.T3) C) :
    realizes segs c (t_alt3 A B C) := by
  refine realizes.rz_conseq c (t_alt (fun i => match i with
      | three.T1 => A | three.T2 => B | three.T3 => C)) (t_alt3 A B C) ?_ ?_
  · exact rz_cases segs c three nx _ three.T1 Hnode (by rintro (_ | _ | _) <;> assumption)
  · intro tr
    unfold t_alt3 t_alt2 t_alt
    refine ⟨?_, ?_⟩
    · rintro ⟨i, h⟩
      cases i with
      | T1 => exact Or.inl h
      | T2 => exact Or.inr (Or.inl h)
      | T3 => exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact ⟨three.T1, h⟩
      · exact ⟨three.T2, h⟩
      · exact ⟨three.T3, h⟩

/-- A node whose admissible transitions are exactly those described by a
    predicate on (events, successor): the [node_ok] interface from an
    "iff" characterization of [sstep]. -/
theorem node_of_iff (segs : List Segment) (c : config) (I : Type)
    (evs : I → List event) (nx : I → config)
    (H1 : ∀ i, sstep segs c (evs i) (.SNext (nx i)))
    (H2 : ∀ (e : List event) (st : step_to), sstep segs c e st →
      ∃ i, e = evs i ∧ st = .SNext (nx i)) :
    node_ok segs c I evs nx := ⟨H1, H2⟩

/- =========================================================================
   Post-state normal forms for the effect shapes used below
   ========================================================================= -/

theorem adv_ret_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 r : word) :
    advance_past_svc (apply_effect (epend regs pc mem rom x8)
        (SyscallEffect.mkEffectU r [] [] [] [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) mem rom :=
  adv_eff_ret_epend regs pc mem rom x8 r

theorem zeros_cover_one (a n x : word) :
    zeros_cover [(a, n)] x
      = (decide ((a.toNat : Int) ≤ (x.toNat : Int)) &&
         decide ((x.toNat : Int) < (a.toNat : Int) + (n.toNat : Int))) := by
  simp [zeros_cover]

/-- The single-range case of [apply_unmaps] is [unfill]. -/
theorem apply_unmaps_one (mem : word → Option byte) (a n : word) :
    apply_unmaps mem [(a, n)] = unfill a n mem := by
  funext x
  simp only [apply_unmaps, unfill, zeros_cover_one]

theorem adv_zeros1_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 r a n : word) :
    advance_past_svc (apply_effect (epend regs pc mem rom x8)
        (SyscallEffect.mkEffectU r [] [(a, n)] [] [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom := by
  have Hm : apply_zeros mem [(a, n)] = zfill a n mem := by
    rw [AllocSim.apply_zeros_one]
    rfl
  simp only [advance_past_svc, apply_effect, apply_writes, apply_copies, apply_unmaps,
    set_reg_10, ms_pc, b_npc4, mkst, epend, Hm]

theorem adv_unmaps1_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 r a n : word) :
    advance_past_svc (apply_effect (epend regs pc mem rom x8)
        (SyscallEffect.mkEffectU r [] [] [(a, n)] [] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom := by
  have Hm : apply_unmaps mem [(a, n)] = unfill a n mem := apply_unmaps_one mem a n
  simp only [advance_past_svc, apply_effect, apply_writes, apply_copies,
    AllocSim.apply_zeros_nil, set_reg_10, ms_pc, b_npc4, mkst, epend, Hm]

/-- `MmapSim.wbytes` and `CatExec.wbytes` are the same byte-write walk. -/
theorem wbytes_mmap_eq_cat (m : word → Option byte) (a : word) (bs : List byte) :
    MmapSim.wbytes m a bs = CatExec.wbytes m a bs := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b rest ih =>
    show MmapSim.wbytes _ _ rest = CatExec.wbytes _ _ rest
    exact ih _ _

/--  concludes `wbytes mem buf data`; the byte-write walk
    the effect layer actually applies is `RiscvSemantics.write_to_mem`, and
    the statement below uses `MmapSim.wbytes`, this tree's copy of 
    `wbytes` (the two are linked by [wbytes_mmap_eq_cat] and
    [CatExec.write_to_mem_wbytes]). -/
theorem adv_write1_epend (regs : BvMap word) (pc : word) (mem rom : word → Option byte)
    (x8 r buf : word) (data : List byte) :
    advance_past_svc (apply_effect (epend regs pc mem rom x8)
        (mkEffect r [(buf, data)] []))
      = mkst (regupd regs 10 r) (v_addi pc 4) (MmapSim.wbytes mem buf data) rom := by
  have Hm : write_to_mem mem buf data = MmapSim.wbytes mem buf data := by
    rw [wbytes_mmap_eq_cat]
    exact CatExec.write_to_mem_wbytes data mem buf
  simp only [advance_past_svc, apply_effect, apply_writes, apply_copies, apply_unmaps,
    AllocSim.apply_zeros_nil, set_reg_10, ms_pc, b_npc4, mkst, epend, Hm]

/- =========================================================================
   munmap(a, len) of exactly one recorded mapping
   ========================================================================= -/

theorem munmap_model_simple (a n : word) (m : Model)
    (Hl : m_vm_lazy m = []) (Hm : m_vm_materialized m = []) :
    munmap_model a n m
      = with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
          (map_remove (m_vmmaps m).vm_maps a)
          (maps_subtract (m_vmmaps m).vm_noaccess
            (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))
          (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
          (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m := by
  rw [munmap_model, LinuxSem.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_destroyed]
  exact vm_forget_range_id _ _ _ (by rw [with_vmmaps_lazy']; exact Hl) Hm

/- =========================================================================
   brk
   ========================================================================= -/

/-- The brk node in terms of the resolved break [r]: every admissible
    transition is [r] with [Mmap.brk_r_ok model req r = true]
    ([AllocSim.brk_resolution_ok]), to the [AllocSim.brk_model] successor
    with the [brk_zeros]/[brk_unmaps] effect. -/
theorem node_brk (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 214) :
    node_ok segs (mkCfg ms model)
      { r : word // AllocSim.brk_resolution_ok model (ms_gpr ms 0) r }
      (fun _ => [])
      (fun i => mkCfg (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU i.1 []
            (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
            (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])))
        (AllocSim.brk_model (ms_gpr ms 0) i.1 model)) := by
  constructor
  · intro i
    have hspec := AllocSim.brk_ok_intro segs ms x8 model i.1 Hno i.2
    obtain ⟨-, hh', -, -, hlazy'⟩ :=
      AllocSim.brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno hspec
    exact sstep.syscall ms model x8
      (SyscallEffect.mkEffectU i.1 []
        (brk_zeros (ms_gpr ms 0) i.1 (m_vmmaps model).vm_brk)
        (brk_unmaps i.1 (m_vmmaps model).vm_brk) [] [])
      (AllocSim.brk_model (ms_gpr ms 0) i.1 model)
      (AllocSim.brk_model (ms_gpr ms 0) i.1 model) []
      Hh Hsvc hspec hh' (by rw [materialize_model_accesses_no_lazy _ _ (by rw [hlazy']; exact Hlazy)])
  · intro e st hss
    obtain ⟨eff, model', hspec, rfl, rfl⟩ :=
      AllocSim.sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno hss
    obtain ⟨heff, -, hok, rfl⟩ := (AllocSim.brk_ok_iff segs ms x8 model eff model' [] Hno).mp hspec
    refine ⟨⟨eff.eff_ret, hok⟩, rfl, ?_⟩
    show step_to.SNext (mkCfg (advance_past_svc (apply_effect ms eff))
          (AllocSim.brk_model (ms_gpr ms 0) eff.eff_ret model))
        = step_to.SNext (mkCfg (advance_past_svc (apply_effect ms
            (SyscallEffect.mkEffectU eff.eff_ret []
              (brk_zeros (ms_gpr ms 0) eff.eff_ret (m_vmmaps model).vm_brk)
              (brk_unmaps eff.eff_ret (m_vmmaps model).vm_brk) [] [])))
          (AllocSim.brk_model (ms_gpr ms 0) eff.eff_ret model))
    rw [heff]

/-- Unfolding [brk_r_ok] on a request at or above both the heap base and the
    current break (the GROW path): the resolutions are exactly "keep the
    break" and — if [brk_grow_ok] admits it — "move to req". -/
theorem brk_r_ok_grow_cases (m : Model) (req r : word)
    (Hpos : 0 < (req.toNat : Int))
    (Hs : ((m_vmmaps m).vm_start_brk.toNat : Int) ≤ (req.toNat : Int))
    (Hb : ((m_vmmaps m).vm_brk.toNat : Int) ≤ (req.toNat : Int)) :
    AllocSim.brk_resolution_ok m req r ↔
      (r = (m_vmmaps m).vm_brk ∨
        (r = req ∧ brk_grow_ok m req req = true)) := by
  have hne : req ≠ BitVec.ofInt 64 0 := by
    intro hh
    rw [hh] at Hpos
    simp at Hpos
  have E0 : w_is0 req = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ hne
  have Hmin : ((min_brk (m_vmmaps m)).toNat : Int) ≤ (req.toNat : Int) := Hs
  have E1 : decide ((req.toNat : Int) < ((min_brk (m_vmmaps m)).toNat : Int)) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  have E2 : decide ((req.toNat : Int) < ((m_vmmaps m).vm_brk.toNat : Int)) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  unfold AllocSim.brk_resolution_ok
  rw [AllocSim.mmap_brk_r_ok_eq]
  simp only [E0, Bool.false_or, Bool.false_eq_true, ite_false, E1, E2]
  rw [Bool.and_eq_true, Bool.or_eq_true]
  simp only [bv_eqb, beq_iff_eq]
  constructor
  · rintro ⟨h | h, hg⟩
    · subst h; exact Or.inr ⟨rfl, hg⟩
    · exact Or.inl h
  · rintro (h | ⟨h, hg⟩)
    · subst h
      refine ⟨Or.inr rfl, ?_⟩
      have hlt : decide (((m_vmmaps m).vm_brk.toNat : Int) <
          ((m_vmmaps m).vm_brk.toNat : Int)) = false := by simp
      simp only [brk_grow_ok, hlt, Bool.and_false, Bool.false_eq_true, ite_false]
    · subst h
      exact ⟨Or.inl rfl, hg⟩

/-- The model after keeping the break is unchanged. -/
theorem brk_model_keep (m : Model) (req : word) :
    AllocSim.brk_model req (m_vmmaps m).vm_brk m = m := by
  have hb : brk_unmaps (m_vmmaps m).vm_brk (m_vmmaps m).vm_brk = [] :=
    AllocSim.brk_unmaps_keep _
  have hlt : decide (((m_vmmaps m).vm_brk.toNat : Int) <
      ((m_vmmaps m).vm_brk.toNat : Int)) = false := by simp
  have hgr : brk_grants req (m_vmmaps m).vm_brk (m_vmmaps m).vm_brk = [] :=
    AllocSim.brk_grants_keep req _
  simp only [AllocSim.brk_model, with_brk_next, forget_vm_ranges, hb, List.nil_append,
    brk_model_next, brk_maps_next, maps_subtract_ranges, List.foldl_nil, hlt,
    Bool.and_false, hgr, Bool.false_eq_true, ite_false]
  exact with_vmmaps_eta m

/-- `Z_to_bv 64 (u + d) - Z_to_bv 64 u` is `Z_to_bv 64 d` (bitvector
    arithmetic is modulo `2^64`, so no range hypothesis is needed). -/
theorem ofInt_add_sub_ofInt (u d : Int) :
    BitVec.ofInt 64 (u + d) - BitVec.ofInt 64 u = BitVec.ofInt 64 d := by
  rw [BitVec.ofInt_add, BitVec.add_comm (BitVec.ofInt 64 u), BitVec.add_sub_cancel]

/-- `Z_to_bv 64 (a + d) - a` is `Z_to_bv 64 d` for a [word] `a`. -/
theorem word_sub_ofInt (a : word) (d : Int) :
    BitVec.ofInt 64 ((a.toNat : Int) + d) - a = BitVec.ofInt 64 d := by
  have key := ofInt_add_sub_ofInt ((a.toNat : Int)) d
  rwa [show BitVec.ofInt 64 ((a.toNat : Int)) = a from Z_to_bv_u_eq' a _ rfl] at key

/-- The model after an aligned grow [b -> b + d] (b > 0 page aligned, d > 0). -/
theorem brk_model_grow_eq (m : Model) (d : Int)
    (Hd : 0 < d) (Hb0 : 0 < ((m_vmmaps m).vm_brk.toNat : Int))
    (Hnw : ((m_vmmaps m).vm_brk.toNat : Int) + d < 2 ^ 64)
    (Hbal : ((m_vmmaps m).vm_brk.toNat : Int) % page_size = 0)
    (Hdal : d % page_size = 0) :
    AllocSim.brk_model (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d))
        (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d)) m
      = with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
          (((m_vmmaps m).vm_brk, BitVec.ofInt 64 d) :: (m_vmmaps m).vm_maps)
          (m_vmmaps m).vm_noaccess (m_vmmaps m).vm_start_brk
          (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d))
          (m_vmmaps m).vm_limit (m_vmmaps m).vm_mmap_base
          (m_vmmaps m).vm_init_sp) m := by
  have Hureq : ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) + d :=
    AgentLib.u64_lit _ ⟨by omega, by omega⟩
  have Hlt : ((m_vmmaps m).vm_brk.toNat : Int)
      < ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int) := by
    rw [Hureq]; omega
  have Hreq0 : (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word)
      ≠ BitVec.ofInt 64 0 := by
    intro E
    have h1 : ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
        = ((BitVec.ofInt 64 0 : word).toNat : Int) := by rw [E]
    rw [Hureq] at h1
    simp at h1
    omega
  have hbu : ((m_vmmaps m).vm_brk.toNat : Int)
      ≤ ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int) := by
    rw [Hureq]; omega
  have hunm : brk_unmaps (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d))
      (m_vmmaps m).vm_brk = [] :=
    AllocSim.brk_unmaps_grow _ _ hbu
  have hgr : brk_grants (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d))
      (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d)) (m_vmmaps m).vm_brk
      = [((m_vmmaps m).vm_brk,
          BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) - (m_vmmaps m).vm_brk)] :=
    AllocSim.brk_grants_grow _ _ _ Hreq0 Hb0 Hlt
  have hnotlt : decide (((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      < ((m_vmmaps m).vm_brk.toNat : Int)) = false := by
    simp only [decide_eq_false_iff_not]; omega
  simp only [AllocSim.brk_model, with_brk_next, forget_vm_ranges, hunm, List.nil_append,
    brk_model_next, brk_maps_next, maps_subtract_ranges, List.foldl_nil, hnotlt,
    Bool.and_false, Bool.false_eq_true, ite_false, hgr]
  rw [show BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) - (m_vmmaps m).vm_brk
      = BitVec.ofInt 64 d from word_sub_ofInt _ d]
  rfl

/- =========================================================================
   mmap(0, len, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)
   ========================================================================= -/

/-- The model after a fresh PROT_NONE grant: recorded in both ledgers. -/
def noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
    ((a, n) :: (m_vmmaps m).vm_maps)
    ((a, n) :: (m_vmmaps m).vm_noaccess)
    (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
    (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m

/-- May the kernel place an INACCESSIBLE reservation at [a, a+n)?  Like
    [MmapSim.grant_ok] WITHOUT the budget conjunct: a PROT_NONE mapping
    consumes no backed memory ([Mmap.mmap_spec], noaccess branch). -/
def grant_ok_na (hint : word) (m : Model) (a : word) (n : Int) : Bool :=
  decide ((a.toNat : Int) % page_size = 0) && decide (0 < (a.toNat : Int))
  && decide ((a.toNat : Int) + n ≤ alloc_ceiling)
  && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
       (BitVec.ofInt 64 n)
  && hint_placement_ok_b hint (m_vmmaps m) (a.toNat : Int) n

/-- The checker's grant condition for a PROT_NONE NULL-hint grant — exactly
    what [check_mmap] tests (run-dependent ceiling, no placement gate). -/
def grant_ok_na_pin (m : Model) (a : word) (n : Int) : Bool :=
  decide ((a.toNat : Int) % page_size = 0) && decide (0 < (a.toNat : Int))
  && decide ((a.toNat : Int) + n ≤ alloc_top (m_vmmaps m))
  && region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a
       (BitVec.ofInt 64 n)

theorem grant_ok_na_of_pin (PL : placement_policy) (hint : word) (m : Model)
    (a : word) (n : Int) (Hn : 0 < n) (Hnal : n % page_size = 0)
    (H : grant_ok_na_pin m a n = true) : grant_ok_na hint m a n = true := by
  unfold grant_ok_na_pin at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨⟨⟨Hal, Hpos⟩, Htop⟩, Hrf⟩ := H
  have HtopP : (a.toNat : Int) + n ≤ alloc_top (m_vmmaps m) := by simpa using Htop
  obtain ⟨Hce, Hpl⟩ := PL (m_vmmaps m) a n Hn Hnal
    (by simpa using Hal) (by simpa using Hpos) HtopP Hrf
  have Hce' : decide ((a.toNat : Int) + n ≤ alloc_ceiling) = true := by
    simpa using Hce
  have Hpl' : hint_placement_ok_b hint (m_vmmaps m) (a.toNat : Int) n = true := by
    unfold hint_placement_ok_b
    cases hw : w_is0 hint with
    | false => rfl
    | true => exact Hpl
  simp only [grant_ok_na, Hal, Hpos, Hrf, Hce', Hpl', Bool.and_true]

theorem grant_ok_na_pin_of_grant_ok (hint : word) (m : Model) (a : word) (n : Int)
    (H : grant_ok hint m a n = true) : grant_ok_na_pin m a n = true := by
  unfold grant_ok at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := H
  unfold grant_ok_na_pin
  simp only [h1, h2, h3, h4, Bool.and_true]

/-- [grant_ok_na] implies [grant_ok_na_pin] once the ledger's stack pointer
    is admissible. -/
theorem grant_ok_na_pin_of_gate (hint : word) (m : Model) (a : word) (n : Int)
    (Hisp : init_sp_ok (m_vmmaps m)) (H : grant_ok_na hint m a n = true) :
    grant_ok_na_pin m a n = true := by
  unfold grant_ok_na at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨⟨⟨⟨Hal, Hpos⟩, Hce⟩, Hrf⟩, -⟩ := H
  have HceP : (a.toNat : Int) + n ≤ alloc_ceiling := by simpa using Hce
  have Htop : (a.toNat : Int) + n ≤ alloc_top (m_vmmaps m) :=
    alloc_top_ge_of_ceiling _ _ Hisp HceP
  have Htop' : decide ((a.toNat : Int) + n ≤ alloc_top (m_vmmaps m)) = true := by
    simpa using Htop
  unfold grant_ok_na_pin
  simp only [Hal, Hpos, Hrf, Htop', Bool.and_true]

theorem grant_na_pin_not_errno (m : Model) (a : word) (n : Int)
    (Hn : 0 ≤ n) (Hg : grant_ok_na_pin m a n = true) :
    errno_ret_in mmap_errnos a = false := by
  unfold grant_ok_na_pin at Hg
  simp only [Bool.and_eq_true] at Hg
  have Htop : (a.toNat : Int) + n ≤ alloc_top (m_vmmaps m) := by simpa using Hg.1.2
  refine errno_ret_in_below _ _ (by decide) ?_
  have hroom := alloc_top_room (m_vmmaps m)
  have hs : stack_max_size = 8388608 := LinuxSem.LinuxProcessSem.stack_max_size_val
  unfold two_pow_64 at *
  omega

/-- The argument shape of the PROT_NONE anonymous grant: [len <> 0],
    [prot = PROT_NONE], [flags = MAP_PRIVATE|MAP_ANONYMOUS],
    [fd = -1], [off = 0]. -/
def mmap_noaccess_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ BitVec.ofInt 64 0 ∧ ms_gpr ms 2 = BitVec.ofInt 64 0
  ∧ ms_gpr ms 3 = BitVec.ofInt 64 34 ∧ ms_gpr ms 4 = BitVec.ofInt 64 (-1)
  ∧ ms_gpr ms 5 = BitVec.ofInt 64 0

theorem mmap_noaccess_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (Hno : (x8.toNat : Int) = 222)
    (Hargs : mmap_noaccess_args_ok ms) :
    check_syscall (sys_input segs ms x8) eff model
      = (let n := page_round_up_Z ((ms_gpr ms 1).toNat : Int)
         match eff with
         | ⟨r, [], [], us, [], []⟩ =>
             if errno_ret_in mmap_errnos r then
               (match us with | [] => .CheckOk model [] | _ => .CheckReject)
             else if grant_ok_na_pin model r n && listNN_eqb us [(r, BitVec.ofInt 64 n)]
               then .CheckOk (noaccess_model r (BitVec.ofInt 64 n) model) []
               else .CheckReject
         | _ => .CheckReject) := by
  obtain ⟨H1, H2, H3, H4, H5⟩ := Hargs
  rw [mmap_check segs ms x8 model eff Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mmap.check_mmap
  have E1 : w_is0 (ms_gpr ms 1) = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ H1
  rw [H2, H3, H5, E1]
  have eoff : mmap_off_aligned_b (BitVec.ofInt 64 0) = true := by decide
  have eanon : mmap_anon_b (BitVec.ofInt 64 34) = true := by decide
  have emod : mmap_modeled_b (BitVec.ofInt 64 0) (BitVec.ofInt 64 34)
      (BitVec.ofInt 64 0) = false := by decide
  have ena : mmap_noaccess_b (BitVec.ofInt 64 0) (BitVec.ofInt 64 34)
      (BitVec.ofInt 64 0) = true := by decide
  have enr : mmap_noreserve_b (BitVec.ofInt 64 34) = false := by decide
  simp only [eoff, eanon, emod, ena, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ite_false, ite_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws'⟩
  · rcases zs with _ | ⟨z, zs'⟩
    · rcases cs with _ | ⟨c, cs'⟩
      · rcases ci with _ | ⟨x, ci'⟩
        · rcases us with _ | ⟨u, us'⟩
          · rcases h : errno_ret_in mmap_errnos r with _ | _
            · rfl
            /- `h` selects the errno arm, and `ite_true` reduces the `if`
               it leaves behind: neither the rewrite of the guard nor the
               `ite` reduction happens on its own here. -/
            · simp only [h, grant_ok_na_pin, noaccess_model,
                LinuxSem.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing, enr,
                Bool.false_eq_true, ite_false, ite_true]
          · rcases h : errno_ret_in mmap_errnos r with _ | _ <;> rfl
        · rcases us with _ | ⟨u, us'⟩ <;> rfl
      · rcases us with _ | ⟨u, us'⟩ <;> rfl
    · rfl
  · rfl

theorem grant_na_not_errno (hint : word) (model : Model) (a : word) (n : Int)
    (Hn : 0 ≤ n) (Hg : grant_ok_na hint model a n = true) :
    errno_ret_in mmap_errnos a = false := by
  unfold grant_ok_na at Hg
  simp only [Bool.and_eq_true] at Hg
  have Hce : (a.toNat : Int) + n ≤ alloc_ceiling := by simpa using Hg.1.1.2
  refine errno_ret_in_below _ _ (by decide) ?_
  have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
  unfold two_pow_64 at *
  omega


/- =========================================================================
   mprotect(addr, len, PROT_READ|PROT_WRITE) over PROT_NONE pages
   ========================================================================= -/

/-- The model after enabling [addr, addr+n): the range leaves [vm_noaccess]
    (= [Mprotect.mprotect_model_next]). -/
def mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
    (maps_subtract (m_vmmaps m).vm_noaccess
      (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
    (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
    (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m

theorem mprotect_model_next_eq (m : Model) (addr n : word) :
    LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_model_next m addr n
      = mprotect_model addr n m := rfl

theorem check_syscall_226 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 226) :
    check_syscall (sys_input segs ms x8) eff m
      = LinuxSem.Checks.Sys.Mm.Mprotect.check_mprotect
          (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_mprotect := by
    rw [in_sysno_sys_input, Hno]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, hlook,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_mprotect,
    in_arg0_sys_input, StreamSim.in_arg1_sys_input, StreamSim.in_arg2_sys_input]

theorem mprotect_check (segs : List Segment) (ms : machine_state) (x8 : word)
    (model : Model) (eff : SyscallEffect) (addr : word) (len : Int)
    (Hno : (x8.toNat : Int) = 226)
    (H0 : ms_gpr ms 0 = addr) (Hal : (addr.toNat : Int) % page_size = 0)
    (H1 : ms_gpr ms 1 = BitVec.ofInt 64 len) (Hlen : 0 < len)
    (Hnw : (addr.toNat : Int) + page_round_up_Z len < two_pow_64)
    (H2 : ms_gpr ms 2 = BitVec.ofInt 64 3) :
    let n := BitVec.ofInt 64 (page_round_up_Z len)
    map_contains (m_vmmaps model).vm_noaccess addr n = true →
    map_contains (m_vmmaps model).vm_maps addr n = true →
    check_syscall (sys_input segs ms x8) eff model
      = (match eff with
        | ⟨r, [], zs, [], [], []⟩ =>
            if errno_ret_in mprotect_errnos r then
              (match zs with | [] => .CheckOk model [] | _ => .CheckReject)
            else if LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok
                  model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
              then .CheckOk (mprotect_model addr n model) []
              else .CheckReject
        | _ => .CheckReject) := by
  dsimp only
  intro Hna Hma
  rw [check_syscall_226 segs ms x8 eff model Hno]
  unfold LinuxSem.Checks.Sys.Mm.Mprotect.check_mprotect
  rw [H0, H2, H1]
  have Hlen0 : 0 ≤ len := by omega
  have Hlenlt : len < 2 ^ 64 := by
    have hb := (AllocSim.page_round_up_Z_bounds len Hlen0).1
    have ha := (u64_range addr).1
    unfold two_pow_64 at Hnw
    omega
  have Hul : ((BitVec.ofInt 64 len).toNat : Int) = len :=
    AgentLib.u64_lit len ⟨Hlen0, Hlenlt⟩
  rw [Hul]
  have egrow : LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_grows_conflict_b
      (BitVec.ofInt 64 3) = false := by decide
  have emod : LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_modeled_b
      (BitVec.ofInt 64 3) = true := by decide
  have hal : ((addr.toNat : Int) % page_size == 0) = true := by rw [Hal]; rfl
  have hne : (BitVec.ofInt 64 len : word) ≠ BitVec.ofInt 64 0 := by
    intro h
    have h2 : (BitVec.ofInt 64 len).toNat = 0 := by rw [h]; rfl
    rw [AgentLib.toNat_ofInt_lit len ⟨Hlen0, Hlenlt⟩] at h2
    omega
  have elen : w_is0 (BitVec.ofInt 64 len) = false := by
    unfold w_is0
    exact PropExec.bv_eqb_neq _ _ hne
  have hnw : ¬ (two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z len) := by omega
  simp only [egrow, hal, elen, emod, hnw, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_false, ite_true, Hna, Hma, Bool.and_true]
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  rcases ws with _ | ⟨w, ws'⟩
  · rcases us with _ | ⟨u, us'⟩
    · rcases cs with _ | ⟨c, cs'⟩
      · rcases ci with _ | ⟨x, ci'⟩
        · rcases zs with _ | ⟨z, zs'⟩
          · rcases h : errno_ret_in mprotect_errnos r with _ | _
            · rfl
            · simp only [mprotect_model_next_eq]
          · rcases h : errno_ret_in mprotect_errnos r with _ | _ <;> rfl
        · rcases zs with _ | ⟨z, zs'⟩ <;> rfl
      · rcases zs with _ | ⟨z, zs'⟩ <;> rfl
    · rcases zs with _ | ⟨z, zs'⟩ <;> rfl
  · rcases zs with _ | ⟨z, zs'⟩ <;> rfl

theorem ENOMEM_in_mprotect_errnos : ENOMEM ∈ mprotect_errnos := by
  simp [mprotect_errnos]


/- =========================================================================
   mmap(addr, len, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0)
   over a range inside one tracked mapping (musl's brk guard page)
   ========================================================================= -/

/-- Success: the range becomes inaccessible (PROT_NONE ledger + unmapped
    overlay); ownership ([vm_maps]) is unchanged; the lazy/materialized
    ledgers are cleared over the range ([vm_forget_range], identity on our
    models: [fixed_noaccess_model_simple]). -/
def fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int))
    (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
      ((addr, n) :: maps_subtract (m_vmmaps m).vm_noaccess
        (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
      (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
      (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m)

/-- Destructive failure: the range is gone from both ledgers. -/
def fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int))
    (with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
      (maps_subtract (m_vmmaps m).vm_maps
        (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
      (maps_subtract (m_vmmaps m).vm_noaccess
        (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
      (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
      (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m)

theorem fixed_noaccess_model_simple (addr n : word) (m : Model)
    (Hl : m_vm_lazy m = []) (Hm : m_vm_materialized m = []) :
    fixed_noaccess_model addr n m
      = with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
          ((addr, n) :: maps_subtract (m_vmmaps m).vm_noaccess
            (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
          (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
          (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m := by
  rw [fixed_noaccess_model]
  exact vm_forget_range_id _ _ _ (by rw [with_vmmaps_lazy']; exact Hl) Hm

theorem fixed_destroyed_model_simple (addr n : word) (m : Model)
    (Hl : m_vm_lazy m = []) (Hm : m_vm_materialized m = []) :
    fixed_destroyed_model addr n m
      = with_vmmaps (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved
          (maps_subtract (m_vmmaps m).vm_maps
            (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
          (maps_subtract (m_vmmaps m).vm_noaccess
            (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)))
          (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
          (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m := by
  rw [fixed_destroyed_model]
  exact vm_forget_range_id _ _ _ (by rw [with_vmmaps_lazy']; exact Hl) Hm

/-- The argument shape of the contained MAP_FIXED PROT_NONE overwrite. -/
def mmap_fixed_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 ≠ BitVec.ofInt 64 0 ∧ ms_gpr ms 2 = BitVec.ofInt 64 0
  ∧ ms_gpr ms 3 = BitVec.ofInt 64 50 ∧ ms_gpr ms 4 = BitVec.ofInt 64 (-1)
  ∧ ms_gpr ms 5 = BitVec.ofInt 64 0

/- =========================================================================
   set_tid_address(p): the FIRST call picks any tid in (0, 2^22)
   ========================================================================= -/

theorem check_syscall_96 (segs : List Segment) (ms : machine_state) (x8 : word)
    (eff : SyscallEffect) (m : Model) (Hno : (x8.toNat : Int) = 96) :
    check_syscall (sys_input segs ms x8) eff m
      = LinuxSem.Checks.Sys.Kernel.Fork.check_set_tid_address eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca
      LinuxSem.Checks.Sys.Dispatch.checked_table
      ((sys_input segs ms x8).in_sysno.toNat : Int)
      = some LinuxSem.Checks.Sys.Dispatch.arm_set_tid_address := by
    rw [in_sysno_sys_input, Hno]
    arm_dispatch
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, hlook,
    LinuxSem.Checks.Sys.Dispatch.ca_check_arm_set_tid_address]

/-- The resolutions of a first [set_tid_address]: any tid in the envelope. -/
def tid_I : Type := { t : word // 0 < (t.toNat : Int) ∧ (t.toNat : Int) < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE }

theorem one_tid_ok : 0 < ((BitVec.ofInt 64 1 : word).toNat : Int)
    ∧ ((BitVec.ofInt 64 1 : word).toNat : Int) < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE := by
  have h1 : ((BitVec.ofInt 64 1 : word).toNat : Int) = 1 := by
    rw [AgentLib.u64_lit 1 ⟨by omega, by decide⟩]
  unfold LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE
  omega

/-- The first [set_tid_address] node: the resolution is any tid in the
    envelope, the successor records it ([with_tid]) and returns it in a0. -/
theorem node_set_tid (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : (x8.toNat : Int) = 96)
    (Htid : m_tid model = none) :
    node_ok segs (mkCfg ms model) tid_I (fun _ => [])
      (fun i => mkCfg (advance_past_svc (set_gpr0 ms i.1)) (with_tid i.1 model)) := by
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
  have Enx : ∀ i : tid_I,
      mkCfg (advance_past_svc (set_gpr0 ms i.1)) (with_tid i.1 model)
        = mkCfg (advance_past_svc (apply_effect ms
            (SyscallEffect.mkEffectU i.1 [] [] [] [] []))) (with_tid i.1 model) := by
    intro i
    have he : apply_effect ms (SyscallEffect.mkEffectU i.1 [] [] [] [] [])
        = set_gpr0 ms i.1 := CatSim.apply_effect_no_write ms i.1
    rw [he]
  have hP : LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE
      = 2 ^ 22 := rfl
  constructor
  · intro i
    show sstep segs (mkCfg ms model) []
      (.SNext (mkCfg (advance_past_svc (set_gpr0 ms i.1)) (with_tid i.1 model)))
    rw [Enx i]
    have hA : decide (0 < (i.1.toNat : Int)) = true := by simpa using i.2.1
    have hB : decide ((i.1.toNat : Int)
        < LinuxSem.LinuxProcessSem.Sys.Kernel.Fork.PID_MAX_ENVELOPE) = true := by
      simpa using i.2.2
    have hc : check_syscall (sys_input segs ms x8)
        (SyscallEffect.mkEffectU i.1 [] [] [] [] []) model
        = .CheckOk (with_tid i.1 model) [] := by
      rw [Hchk]
      simp only [hA, hB, Bool.and_true, ite_true]
    exact sstep_of_check segs ms model x8 _ (with_tid i.1 model) [] Hh Hsvc hc
      (by rw [with_tid_halted]; exact Hh)
      (by rw [with_tid_lazy]; exact Hlazy)
  · intro e st hss
    have Hinv : ∀ (eff : SyscallEffect) (m' : Model) (ev : List event),
        check_syscall (sys_input segs ms x8) eff model = .CheckOk m' ev →
        ∃ i : tid_I, eff = SyscallEffect.mkEffectU i.1 [] [] [] [] []
          ∧ m' = with_tid i.1 model ∧ ev = [] := by
      rintro ⟨ret, ws, zs, us, cs, ci⟩ m' ev hc
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
    obtain ⟨eff, model', evs, hc, hcases⟩ | ⟨eff, hc, hne, hserr⟩ :=
      sstep_svc_inv segs ms model x8 e st Hsvc hss
    · rcases hcases with ⟨model'', hh', he, hmat, hst⟩
        | ⟨hh', he, hmat, hst⟩ | ⟨code, hh', he, hst⟩
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' evs hc
        rw [materialize_model_accesses_no_lazy _ _
          (by rw [with_tid_lazy]; exact Hlazy)] at hmat
        obtain rfl := Option.some.inj hmat
        exact ⟨i, he, by rw [hst]; simp only []; rw [← Enx i]⟩
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' evs hc
        rw [materialize_model_accesses_no_lazy _ _
          (by rw [with_tid_lazy]; exact Hlazy)] at hmat
        simp at hmat
      · obtain ⟨i, rfl, rfl, rfl⟩ := Hinv eff model' evs hc
        rw [with_tid_halted, Hh] at hh'
        simp at hh'
    · exfalso
      rw [Hchk] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
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

/- =========================================================================
   exit / exit_group
   ========================================================================= -/

/-- At an ecall pc with a7 = 94 (exit_group) or 93 (exit) and a0 = code, the
    configuration realizes [t_exit (code & 255)]. -/
theorem rz_exit_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (code : word)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (H17 : getr regs 17 = BitVec.ofInt 64 94 ∨ getr regs 17 = BitVec.ofInt 64 93)
    (H10 : getr regs 10 = code) :
    realizes segs (mkCfg (mkst regs pc mem rom) model)
      (t_exit (code &&& BitVec.ofInt 64 255) (m_fs model)) := by
  have hx8 : is_exit_no (getr regs 17) := by
    rcases H17 with h | h
    · right; rw [h]; rfl
    · left; rw [h]; rfl
  refine rz_sys segs regs pc mem rom model w _ Hh Hlazy HF HE ?_
  have h := ShapeAlg.rz_exit segs (epend regs pc mem rom (getr regs 17)) model
    (getr regs 17) Hh rfl hx8
  rw [ms_gpr_epend0, H10] at h
  exact h

/-- ... with a literal status below 256. -/
theorem rz_exit_at_lit (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (model : Model) (w : BitVec 32) (code : Int)
    (HF : fetch_word segs pc = some w) (HE : is_ecall w = true)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (H17 : getr regs 17 = BitVec.ofInt 64 94 ∨ getr regs 17 = BitVec.ofInt 64 93)
    (H10 : getr regs 10 = BitVec.ofInt 64 code) (Hc : 0 ≤ code ∧ code < 256) :
    realizes segs (mkCfg (mkst regs pc mem rom) model)
      (t_exit (BitVec.ofInt 64 code) (m_fs model)) := by
  rw [← AgentNodes.bv_and_255_small code Hc]
  exact rz_exit_at segs regs pc mem rom model w (BitVec.ofInt 64 code) HF HE Hh Hlazy H17 H10

/- =========================================================================
   Discharging the budget side conditions
   ========================================================================= -/

/-- On a model with no lazy mappings and no materialized sparse pages (every
    model our binaries reach) the backed-memory meter is the VmMaps-level
    [vm_backed_bytes]; with no PROT_NONE ranges it is just [vm_live_bytes]. -/
theorem vm_backing_used_simple (m : Model) (Hl : m_vm_lazy m = [])
    (Hm : m_vm_materialized m = []) :
    vm_backing_used m = vm_backed_bytes (m_vmmaps m) := by
  unfold vm_backing_used vm_backed_bytes
  rw [Hl, Hm]
  simp [maps_subtract_all]

theorem vm_backed_bytes_no_noaccess (h : VmMaps) (H : h.vm_noaccess = []) :
    vm_backed_bytes h = vm_live_bytes h := by
  unfold vm_backed_bytes vm_backed_maps vm_live_bytes
  rw [H]
  simp [maps_subtract_all]


/-- Admissibility of an aligned grow [b -> b + d]: below the ceiling,
    disjoint from the image and every mapping, within budget.

     opens with `let h := m_vmmaps m in let b := vm_brk h
    in`; the two abbreviations are inlined here so the statement's hypotheses
    read as the same predicates at `(m_vmmaps m).vm_brk`. -/
theorem brk_grow_ok_aligned_intro (m : Model) (d : Int)
    (Hbal : ((m_vmmaps m).vm_brk.toNat : Int) % page_size = 0)
    (Hdal : d % page_size = 0) (Hd : 0 < d)
    (Hb0 : 0 < ((m_vmmaps m).vm_brk.toNat : Int))
    (Hce : ((m_vmmaps m).vm_brk.toNat : Int) + d ≤ alloc_ceiling)
    (Hisp : init_sp_ok (m_vmmaps m))
    (Hrf : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
        (m_vmmaps m).vm_brk (BitVec.ofInt 64 (d + page_size)) = true)
    (Hlive : vm_backing_used m + d ≤ (m_vmmaps m).vm_limit) :
    brk_grow_ok m (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d))
      (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d)) = true := by
  have hcv : alloc_ceiling = 0x7fff7f800000 := alloc_ceiling_val
  have hdw : 0 ≤ d := by omega
  have hdwlt : d < 2 ^ 64 := by omega
  have Hureq : ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) + d := AgentLib.u64_lit _ ⟨by omega, by omega⟩
  have hb0 : decide (0 < ((m_vmmaps m).vm_brk.toNat : Int)) = true := by simpa using Hb0
  have hlt : decide (((m_vmmaps m).vm_brk.toNat : Int)
      < ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)) = true := by
    simp only [decide_eq_true_eq]
    rw [Hureq]; omega
  have hlo : page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) :=
    AllocSim.page_round_up_Z_aligned _ (by omega) Hbal
  have hhi0 : page_round_up_Z
      ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      = ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int) :=
    AllocSim.page_round_up_Z_aligned _
      (by rw [Hureq]; omega)
      (by rw [Hureq, Int.add_emod, Hbal, Hdal]; simp)
  have hhi : page_round_up_Z
      ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      = ((m_vmmaps m).vm_brk.toNat : Int) + d := by
    rw [hhi0, Hureq]
  have hltlo : page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)
      < page_round_up_Z
          ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int) := by
    rw [hlo, hhi]; omega
  have hle : decide (page_round_up_Z
        ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
      ≤ alloc_top (m_vmmaps m)) = true := by
    simp only [decide_eq_true_eq]
    rw [hhi]
    exact Int.le_trans Hce (alloc_ceiling_le_alloc_top _ Hisp)
  have hrf' : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      (BitVec.ofInt 64 (page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int)))
      (BitVec.ofInt 64 (page_round_up_Z
          ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d) : word).toNat : Int)
        + page_size - page_round_up_Z ((m_vmmaps m).vm_brk.toNat : Int))) = true := by
    rw [hlo, hhi]
    rw [show ((m_vmmaps m).vm_brk.toNat : Int) + d + page_size
        - ((m_vmmaps m).vm_brk.toNat : Int) = d + page_size from by omega]
    rw [show BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat : Int) = (m_vmmaps m).vm_brk
      from Z_to_bv_u_eq' _ _ rfl]
    exact Hrf
  have hbud : brk_budget_ok m (BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d)) = true := by
    unfold brk_budget_ok
    simp only [decide_eq_true_eq]
    have hs : ((BitVec.ofInt 64 ((m_vmmaps m).vm_brk.toNat + d)
        - (m_vmmaps m).vm_brk).toNat : Int) = d := by
      rw [word_sub_ofInt (m_vmmaps m).vm_brk d]
      exact AgentLib.u64_lit d ⟨hdw, hdwlt⟩
    rw [hs]
    exact Hlive
  unfold brk_grow_ok
  simp only []
  rw [hb0, hlt]
  rw [show (true && true) = true from rfl, ite_eq_left rfl, ite_eq_left hltlo, hle, hrf', hbud]
  rfl

/-- In the initial model (no mappings yet; break = the ASLR base [brk0] at or
    above the image top) the first aligned grow of [d <= limit] bytes that
    stays below the ceiling is admissible. -/
theorem brk_grow_admissible_init (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (model : Model) (d : Int)
    (Hsp : sp_window_lo ≤ (sp.toNat : Int))
    (Htop : reserved_top reserved ≤ (brk0.toNat : Int))
    (Hbal : (brk0.toNat : Int) % page_size = 0) (Hdal : d % page_size = 0) (Hd : 0 < d)
    (Hb0 : 0 < (brk0.toNat : Int))
    (Hce : (brk0.toNat : Int) + d ≤ alloc_ceiling)
    (Hlim : d ≤ lim)
    (Hvm : m_vmmaps model = VmMaps.mkVmMapsFull reserved [] [] brk0 brk0 lim mbase sp)
    (Hlz : m_vm_lazy model = []) (Hmt : m_vm_materialized model = []) :
    brk_grow_ok model (BitVec.ofInt 64 ((brk0.toNat : Int) + d))
      (BitVec.ofInt 64 ((brk0.toNat : Int) + d)) = true := by
  have hb : (m_vmmaps model).vm_brk = brk0 := by rw [Hvm]
  have hl : (m_vmmaps model).vm_limit = lim := by rw [Hvm]
  have hres : (m_vmmaps model).vm_reserved = reserved := by rw [Hvm]
  have hmaps : (m_vmmaps model).vm_maps = [] := by rw [Hvm]
  have hbal' : ((m_vmmaps model).vm_brk.toNat : Int) % page_size = 0 := by
    rw [hb]; exact Hbal
  have hb0' : 0 < ((m_vmmaps model).vm_brk.toNat : Int) := by
    rw [hb]; exact Hb0
  have hce' : ((m_vmmaps model).vm_brk.toNat : Int) + d ≤ alloc_ceiling := by
    rw [hb]; exact Hce
  have hisp' : init_sp_ok (m_vmmaps model) := by
    rw [Hvm]; exact Hsp
  have hrf' : region_free ((m_vmmaps model).vm_reserved ++ (m_vmmaps model).vm_maps)
      (m_vmmaps model).vm_brk (BitVec.ofInt 64 (d + page_size)) = true := by
    rw [hres, hmaps, hb]
    simpa using AllocSim.region_free_above_top reserved brk0
      (BitVec.ofInt 64 (d + page_size)) Htop
  have hlive' : vm_backing_used model + d ≤ (m_vmmaps model).vm_limit := by
    rw [vm_backing_used_simple model Hlz Hmt]
    have hz : vm_backed_bytes (m_vmmaps model) = 0 := by
      rw [Hvm]
      simp [vm_backed_bytes, vm_backed_maps, vm_live_bytes, maps_subtract_all,
        LinuxSem.LinuxProcessSem.live_bytes]
    rw [hz, hl]
    omega
  simpa only [hb] using
    brk_grow_ok_aligned_intro model d hbal' Hdal Hd hb0' hce' hisp' hrf' hlive'

/- =========================================================================
   End of the [WithSegs] section: the remaining material is [segs]-independent
   ========================================================================= -/


/- =========================================================================
   Ledger algebra: evaluating the model's interval bookkeeping
   ========================================================================= -/

theorem u64_roundtrip (x : word) : BitVec.ofInt 64 (x.toNat : Int) = x :=
  Z_to_bv_u_eq' x _ rfl

/-- [region_free] -/
theorem region_free_app (l1 l2 : List (word × word)) (lo n : word) :
    region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n) := by
  induction l1 with
  | nil => rfl
  | cons hd l1 ih =>
    obtain ⟨b, s⟩ := hd
    simp only [List.cons_append, region_free, ih]
    rw [Bool.and_assoc]

/-- NOTE: shadows [State.region_free_In]/[State.region_free_intro] (which
    speak [iv_overlap]); these are the Z-inequality forms the walks use. -/
theorem region_free_In (l : List (word × word)) (lo n b s : word)
    (Hrf : region_free l lo n = true) (Hin : (b, s) ∈ l) :
    (lo.toNat : Int) + (n.toNat : Int) ≤ (b.toNat : Int) ∨
      (b.toNat : Int) + (s.toNat : Int) ≤ (lo.toNat : Int) := by
  induction l with
  | nil => simp at Hin
  | cons hd r ih =>
    obtain ⟨b', s'⟩ := hd
    obtain ⟨Hd, Hrf'⟩ := MmapSim.region_free_cons b' s' r lo n Hrf
    rcases List.mem_cons.mp Hin with h | h
    · injection h with h1 h2
      rw [h1, h2]
      exact Hd
    · exact ih Hrf' h

theorem region_free_intro (l : List (word × word)) (lo n : word)
    (H : ∀ b s, (b, s) ∈ l →
      (lo.toNat : Int) + (n.toNat : Int) ≤ (b.toNat : Int) ∨
        (b.toNat : Int) + (s.toNat : Int) ≤ (lo.toNat : Int)) :
    region_free l lo n = true := by
  induction l with
  | nil => rfl
  | cons hd r ih =>
    obtain ⟨b, s⟩ := hd
    simp only [region_free]
    rw [ih (fun b' s' hin => H b' s' (by simp [hin]))]
    have hov : iv_overlap lo n b s = false := by
      unfold iv_overlap
      rcases H b s (by simp) with h | h
      · have h2 : decide ((b.toNat : Int) < (lo.toNat : Int) + (n.toNat : Int)) = false := by
          simp only [decide_eq_false_iff_not]; omega
        rw [h2, Bool.and_false]
      · have h1 : decide ((lo.toNat : Int) < (b.toNat : Int) + (s.toNat : Int)) = false := by
          simp only [decide_eq_false_iff_not]; omega
        rw [h1, Bool.false_and]
    rw [hov]
    rfl

/-- [map_has] / [map_contains] -/
theorem map_has_head (a n : word) (l : List (word × word)) :
    map_has ((a, n) :: l) a n = true := by
  simp [map_has]

theorem map_has_cons (p : word × word) (a n : word) (l : List (word × word))
    (H : map_has l a n = true) : map_has (p :: l) a n = true := by
  unfold map_has at *
  simp only [List.any_cons, H, Bool.or_true]

theorem map_contains_head (a sz lo n : word) (l : List (word × word))
    (H1 : (a.toNat : Int) ≤ (lo.toNat : Int))
    (H2 : (lo.toNat : Int) + (n.toNat : Int) ≤ (a.toNat : Int) + (sz.toNat : Int)) :
    map_contains ((a, sz) :: l) lo n = true := by
  have h1 : decide ((a.toNat : Int) ≤ (lo.toNat : Int)) = true := by simpa using H1
  have h2 : decide ((lo.toNat : Int) + (n.toNat : Int)
      ≤ (a.toNat : Int) + (sz.toNat : Int)) = true := by simpa using H2
  unfold map_contains
  simp only [List.any_cons, h1, h2, Bool.and_self, Bool.true_or]

theorem map_contains_cons (p : word × word) (lo n : word) (l : List (word × word))
    (H : map_contains l lo n = true) : map_contains (p :: l) lo n = true := by
  unfold map_contains at *
  simp only [List.any_cons, H, Bool.or_true]

/-- [map_remove] (munmap's effect on [vm_maps]) -/
theorem map_remove_nil (a : word) : map_remove [] a = [] := rfl

theorem map_remove_head (a n : word) (l : List (word × word)) :
    map_remove ((a, n) :: l) a = map_remove l a := by
  simp [map_remove]

theorem map_remove_skip (b s a : word) (l : List (word × word)) (H : b ≠ a) :
    map_remove ((b, s) :: l) a = (b, s) :: map_remove l a := by
  have h : (b == a) = false := beq_eq_false_iff_ne.mpr H
  simp [map_remove, h]

theorem map_remove_notin (l : List (word × word)) (a : word)
    (H : ∀ b s, (b, s) ∈ l → b ≠ a) : map_remove l a = l := by
  induction l with
  | nil => rfl
  | cons hd r ih =>
    obtain ⟨b, s⟩ := hd
    rw [map_remove_skip b s a r (H b s (by simp))]
    rw [ih (fun b' s' hin => H b' s' (by simp [hin]))]

/-- Disjoint nonempty intervals have different bases. -/
theorem disjoint_base_ne (lo n b s : word)
    (Hn : 0 < (n.toNat : Int)) (Hs : 0 < (s.toNat : Int))
    (Hd : (lo.toNat : Int) + (n.toNat : Int) ≤ (b.toNat : Int) ∨
      (b.toNat : Int) + (s.toNat : Int) ≤ (lo.toNat : Int)) :
    b ≠ lo := by
  intro h
  subst h
  omega

/-- [live_bytes] -/
theorem live_bytes_cons (a n : word) (l : List (word × word)) :
    LinuxSem.LinuxProcessSem.live_bytes ((a, n) :: l)
      = (n.toNat : Int) + LinuxSem.LinuxProcessSem.live_bytes l := rfl

/- [live_bytes_app] — the append law for the ledger sum — is stated once, in
   the spec layer: [LinuxSem.LinuxProcessSem.Sys.Mm.Mremap.live_bytes_app],
   in scope here through the [open ... Sys.Mm.Mremap] above.  It is not
   restated in this file. -/

theorem live_bytes_nonneg (l : List (word × word)) :
    0 ≤ LinuxSem.LinuxProcessSem.live_bytes l := by
  induction l with
  | nil => simp [LinuxSem.LinuxProcessSem.live_bytes]
  | cons hd l ih =>
    obtain ⟨a, n⟩ := hd
    simp only [LinuxSem.LinuxProcessSem.live_bytes]
    have := (u64_range n).1
    omega

theorem live_bytes_map_remove_le (l : List (word × word)) (a : word) :
    LinuxSem.LinuxProcessSem.live_bytes (map_remove l a)
      ≤ LinuxSem.LinuxProcessSem.live_bytes l := by
  induction l with
  | nil => simp [map_remove, LinuxSem.LinuxProcessSem.live_bytes]
  | cons hd l ih =>
    obtain ⟨b, s⟩ := hd
    by_cases h : b = a
    · subst h
      rw [map_remove_head]
      simp only [LinuxSem.LinuxProcessSem.live_bytes]
      have hs := (u64_range s).1
      omega
    · rw [map_remove_skip b s a l h]
      simp only [LinuxSem.LinuxProcessSem.live_bytes]
      have hs := (u64_range s).1
      omega

/-- [iv_subtract] / [maps_subtract] (munmap / mprotect / MAP_FIXED effects
    on [vm_noaccess], brk shrink).  NOTE: the interval endpoints [lo]/[hi]
    are [Int] in the current [State.iv_subtract]. -/
theorem maps_subtract_nil (lo hi : Int) : maps_subtract [] lo hi = [] := rfl

theorem maps_subtract_cons (a sz : word) (lo hi : Int) (l : List (word × word)) :
    maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi :=
  rfl

/-- Subtracting a range that covers the interval removes it. -/
theorem iv_subtract_covered (a sz : word) (lo hi : Int)
    (H1 : lo ≤ (a.toNat : Int)) (H2 : (a.toNat : Int) + (sz.toNat : Int) ≤ hi) :
    iv_subtract a sz lo hi = [] := by
  unfold iv_subtract
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rfl

/-- ... in particular the interval itself. -/
theorem iv_subtract_self (a sz : word) :
    iv_subtract a sz (a.toNat : Int) ((a.toNat : Int) + (sz.toNat : Int)) = [] :=
  iv_subtract_covered a sz _ _ (by omega) (by omega)

/-- Subtracting a disjoint range keeps a nonempty interval whole. -/
theorem iv_subtract_disjoint (a sz : word) (lo hi : Int)
    (Hsz : 0 < (sz.toNat : Int)) (Hlh : lo ≤ hi)
    (Hd : hi ≤ (a.toNat : Int) ∨ (a.toNat : Int) + (sz.toNat : Int) ≤ lo) :
    iv_subtract a sz lo hi = [(a, sz)] := by
  unfold iv_subtract
  dsimp only
  rcases Hd with hd | hd
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only [List.nil_append]
    rw [Int.max_eq_left (by omega), u64_roundtrip,
      show (a.toNat : Int) + (sz.toNat : Int) - (a.toNat : Int) = (sz.toNat : Int) from by omega,
      u64_roundtrip]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    simp only [List.append_nil]
    rw [Int.min_eq_left (by omega), u64_roundtrip]

/-- Subtracting a suffix [lo, hi) with [a < lo <= a+sz <= hi] keeps the
    prefix [a, lo). -/
theorem iv_subtract_suffix (a sz : word) (lo hi : Int)
    (H1 : (a.toNat : Int) < lo) (H2 : lo ≤ (a.toNat : Int) + (sz.toNat : Int))
    (H3 : (a.toNat : Int) + (sz.toNat : Int) ≤ hi) :
    iv_subtract a sz lo hi = [(a, BitVec.ofInt 64 (lo - (a.toNat : Int)))] := by
  unfold iv_subtract
  dsimp only
  rw [ite_eq_left H1, ite_eq_right (by omega)]
  simp only [List.append_nil]
  rw [Int.min_eq_right (by omega)]

/-- Subtracting a prefix [lo, hi) with [lo <= a < hi < a+sz] keeps the
    suffix [hi, a+sz). -/
theorem iv_subtract_prefix (a sz : word) (lo hi : Int)
    (H1 : lo ≤ (a.toNat : Int)) (H2 : (a.toNat : Int) ≤ hi)
    (H3 : hi < (a.toNat : Int) + (sz.toNat : Int)) :
    iv_subtract a sz lo hi
      = [(BitVec.ofInt 64 hi, BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - hi))] := by
  unfold iv_subtract
  dsimp only
  rw [ite_eq_right (by omega), ite_eq_left H3]
  simp only [List.nil_append]
  rw [Int.max_eq_right (by omega)]

/-- Size bounds survive subtraction (for [grant_exists]'s hypothesis). -/
theorem iv_subtract_sizes (a sz : word) (lo hi N : Int)
    (Hlo : 0 ≤ lo) (Hhi : hi < 2 ^ 64) (Hs : (sz.toNat : Int) ≤ N) :
    ∀ p ∈ iv_subtract a sz lo hi, (p.2.toNat : Int) ≤ N := by
  have ha := u64_range a
  have hsz := u64_range sz
  intro p hp
  unfold iv_subtract at hp
  dsimp only at hp
  rcases List.mem_append.mp hp with h | h
  · by_cases hc : (a.toNat : Int) < lo
    · rw [ite_eq_left hc] at h
      simp only [List.mem_singleton] at h
      subst h
      simp only [Prod.snd]
      rw [AgentLib.u64_lit _ ⟨by omega, by omega⟩]
      omega
    · rw [ite_eq_right hc] at h
      simp at h
  · by_cases hc : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left hc] at h
      simp only [List.mem_singleton] at h
      subst h
      simp only [Prod.snd]
      rw [AgentLib.u64_lit _ ⟨by omega, by omega⟩]
      omega
    · rw [ite_eq_right hc] at h
      simp at h

theorem maps_subtract_sizes (l : List (word × word)) (lo hi N : Int)
    (Hlo : 0 ≤ lo) (Hhi : hi < 2 ^ 64)
    (H : ∀ p ∈ l, (p.2.toNat : Int) ≤ N) :
    ∀ p ∈ maps_subtract l lo hi, (p.2.toNat : Int) ≤ N := by
  induction l with
  | nil => intro p hp; simp [maps_subtract] at hp
  | cons hd l ih =>
    obtain ⟨a, sz⟩ := hd
    intro p hp
    simp only [maps_subtract] at hp
    rcases List.mem_append.mp hp with h | h
    · exact iv_subtract_sizes a sz lo hi N Hlo Hhi (H (a, sz) (by simp)) p h
    · exact ih (fun q hq => H q (by simp [hq])) p h

theorem map_remove_sizes (l : List (word × word)) (a : word) (N : Int)
    (H : ∀ p ∈ l, (p.2.toNat : Int) ≤ N) :
    ∀ p ∈ map_remove l a, (p.2.toNat : Int) ≤ N := by
  intro p hp
  unfold map_remove at hp
  exact H p (List.mem_filter.mp hp).1

theorem maps_subtract_length (l : List (word × word)) (lo hi : Int) :
    (maps_subtract l lo hi).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [maps_subtract]
  | cons hd l ih =>
    obtain ⟨a, sz⟩ := hd
    simp only [maps_subtract, List.length_append, List.length_cons]
    have h2 : (iv_subtract a sz lo hi).length ≤ 2 := by
      unfold iv_subtract
      dsimp only
      split <;> split <;> simp
    omega

theorem map_remove_length (l : List (word × word)) (a : word) :
    (map_remove l a).length ≤ l.length := by
  induction l with
  | nil => simp [map_remove]
  | cons hd l ih =>
    obtain ⟨b, s⟩ := hd
    by_cases h : b = a
    · subst h
      rw [map_remove_head]
      simp only [List.length_cons]
      omega
    · rw [map_remove_skip b s a l h]
      simp only [List.length_cons]
      omega

/-- [live_bytes] only shrinks under subtraction. -/
theorem live_bytes_iv_subtract_le (a sz : word) (lo hi : Int) (Hlh : lo ≤ hi) :
    LinuxSem.LinuxProcessSem.live_bytes (iv_subtract a sz lo hi)
      ≤ (sz.toNat : Int) := by
  have ha := u64_range a
  have hsz := u64_range sz
  unfold iv_subtract
  dsimp only
  split <;> split
  · simp only [List.singleton_append, List.append_nil,
      LinuxSem.LinuxProcessSem.live_bytes]
    rw [AgentLib.u64_lit _ ⟨by omega, by omega⟩,
      AgentLib.u64_lit _ ⟨by omega, by omega⟩]
    have hm := Int.min_le_right (a := (sz.toNat : Int)) (b := lo - (a.toNat : Int))
    have hM := Int.le_max_right (a := (a.toNat : Int)) (b := hi)
    omega
  · simp only [List.singleton_append, List.nil_append,
      LinuxSem.LinuxProcessSem.live_bytes]
    rw [AgentLib.u64_lit _ ⟨by omega, by omega⟩]
    have hm := Int.min_le_left (a := (sz.toNat : Int)) (b := lo - (a.toNat : Int))
    omega
  · simp only [List.nil_append, List.append_nil,
      LinuxSem.LinuxProcessSem.live_bytes]
    rw [AgentLib.u64_lit _ ⟨by omega, by omega⟩]
    have hM := Int.le_max_left (a := (a.toNat : Int)) (b := hi)
    omega
  · simp only [List.nil_append,
      LinuxSem.LinuxProcessSem.live_bytes]
    omega

theorem live_bytes_maps_subtract_le (l : List (word × word)) (lo hi : Int)
    (Hlh : lo ≤ hi) :
    LinuxSem.LinuxProcessSem.live_bytes (maps_subtract l lo hi)
      ≤ LinuxSem.LinuxProcessSem.live_bytes l := by
  induction l with
  | nil => simp [maps_subtract, LinuxSem.LinuxProcessSem.live_bytes]
  | cons hd l ih =>
    obtain ⟨a, sz⟩ := hd
    simp only [maps_subtract, LinuxSem.LinuxProcessSem.live_bytes]
    rw [live_bytes_app]
    have h1 := live_bytes_iv_subtract_le a sz lo hi Hlh
    have h2 := ih
    omega

theorem maps_subtract_all_nil (maps : List (word × word)) : maps_subtract_all maps [] = maps := rfl

theorem maps_subtract_all_cons (maps : List (word × word)) (a n : word)
    (cuts : List (word × word)) :
    maps_subtract_all maps ((a, n) :: cuts)
      = maps_subtract_all (maps_subtract maps (a.toNat : Int)
          ((a.toNat : Int) + (n.toNat : Int))) cuts := rfl

theorem live_bytes_maps_subtract_all_le (cuts maps : List (word × word)) :
    LinuxSem.LinuxProcessSem.live_bytes (maps_subtract_all maps cuts)
      ≤ LinuxSem.LinuxProcessSem.live_bytes maps := by
  induction cuts generalizing maps with
  | nil => simp [maps_subtract_all]
  | cons hd cuts ih =>
    obtain ⟨a, n⟩ := hd
    rw [maps_subtract_all_cons]
    refine Int.le_trans (ih _) ?_
    apply live_bytes_maps_subtract_le
    have := (u64_range n).1
    omega

/-- The BACKED view never exceeds the logical live total ... -/
theorem vm_backed_bytes_le_live (h : VmMaps) :
    vm_backed_bytes h ≤ vm_live_bytes h := by
  unfold vm_backed_bytes vm_backed_maps vm_live_bytes
  apply live_bytes_maps_subtract_all_le

/-- ... so on our models (no lazy mappings, no materialized sparse pages) the
    budget meter is bounded by [vm_live_bytes]: every budget hypothesis
    [vm_live_bytes h + n <= vm_limit h] discharges the spec's
    [vm_backing_used m + n <= vm_limit h]. -/
theorem vm_backing_used_le_live (m : Model) (Hl : m_vm_lazy m = [])
    (Hm : m_vm_materialized m = []) :
    vm_backing_used m ≤ vm_live_bytes (m_vmmaps m) := by
  rw [vm_backing_used_simple m Hl Hm]
  exact vm_backed_bytes_le_live _

theorem grant_budget_intro (m : Model) (n : Int) (Hl : m_vm_lazy m = [])
    (Hm : m_vm_materialized m = [])
    (H : vm_live_bytes (m_vmmaps m) + n ≤ (m_vmmaps m).vm_limit) :
    vm_backing_used m + n ≤ (m_vmmaps m).vm_limit :=
  Int.le_trans (Int.add_le_add_right (vm_backing_used_le_live m Hl Hm) n) H

/-- The budget test of an rw [mprotect] over a PROT_NONE range, discharged
    from the LOGICAL ledger: exposing bytes never charges more than the live
    byte total. -/
theorem mprotect_budget_ok_intro (m : Model) (addr n : word)
    (Hl : m_vm_lazy m = []) (Hm : m_vm_materialized m = [])
    (Hlive : vm_live_bytes (m_vmmaps m) ≤ (m_vmmaps m).vm_limit) :
    LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok m addr n
      = true := by
  unfold LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect.mprotect_budget_ok
  rw [mprotect_model_next_eq]
  unfold vm_backing_within_limit
  simp only [decide_eq_true_eq]
  refine Int.le_trans (vm_backing_used_le_live (mprotect_model addr n m) ?_ ?_) ?_
  · rw [mprotect_model, with_vmmaps_lazy']; exact Hl
  · exact Hm
  · simpa [mprotect_model, vm_live_bytes] using Hlive

/-- [file_read] delivers at most [count] and at most the remaining bytes
    (for [rz_read_file]'s length side conditions). -/
theorem file_read_length_eq (data : List byte) (off count : word) :
    (file_read data off count).length
      = Nat.min (word_to_nat count) (data.length - word_to_nat off) :=
  length_file_read data off count

theorem file_read_length_le (data : List byte) (off count : word) :
    (file_read data off count).length ≤ word_to_nat count
      ∧ (file_read data off count).length ≤ data.length - word_to_nat off := by
  rw [file_read_length_eq]
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩


/- =========================================================================
   Pigeonhole lemmas for an admissible mmap address
   ========================================================================= -/

/-- Candidate grant addresses for a size bound [N]:
    [cand N j = bottomup_floor + j*2N] (at or above [Mmap.bottomup_floor],
    so [Mmap.placement_ok]'s first disjunct holds for every candidate,
    whatever the hint and the mmap base).  An interval of size at most [N]
    meets at most one candidate window [cand N j, cand N j + n) (n <= N), so
    among [length l + 1] candidates one is free of all [length l] recorded
    intervals. -/
def cand (N : Int) (j : Nat) : Int := bottomup_floor + (j : Int) * (2 * N)

def zconflict (a n : Int) (p : word × word) : Prop :=
  a < (p.1.toNat : Int) + (p.2.toNat : Int) ∧ (p.1.toNat : Int) < a + n

def zconflictb (a n : Int) (p : word × word) : Bool :=
  decide (a < (p.1.toNat : Int) + (p.2.toNat : Int)) &&
    decide ((p.1.toNat : Int) < a + n)

theorem zconflictb_spec (a n : Int) (p : word × word) :
    zconflictb a n p = true ↔ zconflict a n p := by
  unfold zconflictb zconflict
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem cand_spacing (N : Int) (j k : Nat) (HN : 0 ≤ N) (H : j < k) :
    cand N j + 2 * N ≤ cand N k := by
  have hjk : (j : Int) + 1 ≤ (k : Int) := by
    have := Int.ofNat_lt.mpr H
    omega
  have h1 : ((j : Int) + 1) * (2 * N) ≤ (k : Int) * (2 * N) :=
    Int.mul_le_mul_of_nonneg_right hjk (by omega)
  rw [Int.add_mul, Int.one_mul] at h1
  unfold cand
  rw [bottomup_floor_val]
  omega

/-- At most one candidate conflicts with a given interval of size <= N. -/
theorem conflict_unique (N n : Int) (p : word × word) (j k : Nat)
    (Hn : 0 ≤ n ∧ n ≤ N) (Hs : (p.2.toNat : Int) ≤ N)
    (H1 : zconflict (cand N j) n p) (H2 : zconflict (cand N k) n p) : j = k := by
  obtain ⟨A1, A2⟩ := H1
  obtain ⟨B1, B2⟩ := H2
  have HN : 0 ≤ N := by omega
  rcases Nat.lt_trichotomy j k with Hlt | Heq | Hgt
  · have hcs := cand_spacing N j k HN Hlt
    omega
  · exact Heq
  · have hcs := cand_spacing N k j HN Hgt
    omega

/-- a filtered list of a [Nodup] list is [Nodup] . -/
theorem nodup_filter (p : Nat → Bool) {js : List Nat} (H : js.Nodup) :
    (js.filter p).Nodup := by
  induction js with
  | nil => simp
  | cons j js ih =>
    rw [List.nodup_cons] at H
    obtain ⟨Hnotin, Hnd⟩ := H
    simp only [List.filter]
    split
    · rw [List.nodup_cons]
      exact ⟨fun h => Hnotin (List.mem_filter.mp h).1, ih Hnd⟩
    · exact ih Hnd

/-- Removing the (at most one) element satisfying [P] costs at most one. -/
theorem filter_keep_all_but_one (P : Nat → Bool) (js : List Nat)
    (Hnd : js.Nodup)
    (Huniq : ∀ j k, j ∈ js → k ∈ js → P j = true → P k = true → j = k) :
    js.length ≤ (js.filter (fun j => !(P j))).length + 1 := by
  induction js with
  | nil => exact Nat.zero_le _
  | cons j js ih =>
    rw [List.nodup_cons] at Hnd
    obtain ⟨Hnotin, Hnd'⟩ := Hnd
    have ih' := ih Hnd' (fun a b ha hb => Huniq a b (by simp [ha]) (by simp [hb]))
    by_cases Pj : P j = true
    · have Hall : ∀ k, k ∈ js → P k = false := by
        intro k hk
        cases Pk : P k with
        | false => rfl
        | true =>
          have hjk : j = k := Huniq j k (by simp) (by simp [hk]) Pj Pk
          subst hjk
          exact absurd hk Hnotin
      have Hid : js.filter (fun j0 => !(P j0)) = js := by
        apply List.filter_eq_self.mpr
        intro a ha
        rw [Hall a ha]
        rfl
      simp only [List.length_cons, List.filter, Pj, Bool.not_true, Bool.false_eq_true,
        ite_false]
      rw [Hid]
      simp
    · have Pj' : P j = false := by simpa using Pj
      simp only [List.length_cons, List.filter, Pj', Bool.not_false, ite_true]
      omega

/-- the surviving-candidate list of [pick_candidate], 
    `set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js)`. -/
def candFree (N n : Int) (p : word × word) (js : List Nat) : List Nat :=
  js.filter (fun j => !(zconflictb (cand N j) n p))

theorem pick_candidate (N n : Int) (l : List (word × word)) :
    ∀ js : List Nat, 0 ≤ n ∧ n ≤ N →
      (∀ p ∈ l, (p.2.toNat : Int) ≤ N) → js.Nodup → l.length < js.length →
      ∃ j, j ∈ js ∧ ∀ p ∈ l, ¬ zconflict (cand N j) n p := by
  induction l with
  | nil =>
    intro js Hn Hsz Hnd Hlen
    cases js with
    | nil => simp at Hlen
    | cons j js => exact ⟨j, by simp, by intro p hp; simp at hp⟩
  | cons hd l ih =>
    obtain ⟨p0, s0⟩ := hd
    intro js Hn Hsz Hnd Hlen
    have Hsz' : ∀ q ∈ l, (q.2.toNat : Int) ≤ N := fun q hq => Hsz q (by simp [hq])
    have Hp : (s0.toNat : Int) ≤ N := Hsz (p0, s0) (by simp)
    have Hnd' : (candFree N n (p0, s0) js).Nodup := nodup_filter _ Hnd
    have Hlen' : js.length ≤ (candFree N n (p0, s0) js).length + 1 := by
      apply filter_keep_all_but_one
      · exact Hnd
      · intro j k _ _ Pj Pk
        exact conflict_unique N n (p0, s0) j k Hn Hp
          (zconflictb_spec _ _ _ |>.mp Pj) (zconflictb_spec _ _ _ |>.mp Pk)
    have Hlen'' : l.length < (candFree N n (p0, s0) js).length := by
      simp only [List.length_cons] at Hlen
      omega
    obtain ⟨j, Hj, Hfree⟩ := ih (candFree N n (p0, s0) js) Hn Hsz' Hnd' Hlen''
    have hmem : j ∈ js := (List.mem_filter.mp Hj).1
    have hnconf : (!(zconflictb (cand N j) n (p0, s0))) = true := (List.mem_filter.mp Hj).2
    refine ⟨j, hmem, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro Hc
      have hc : zconflictb (cand N j) n (p0, s0) = true := zconflictb_spec _ _ _ |>.mpr Hc
      rw [hc] at hnconf
      simp at hnconf
    · exact Hfree q hq'

theorem region_free_of_noconflict (l : List (word × word)) (a n : Int)
    (Ha : 0 ≤ a) (Hn : 0 ≤ n) (Hnw : a + n < 2 ^ 64)
    (Hno : ∀ p ∈ l, ¬ zconflict a n p) :
    region_free l (BitVec.ofInt 64 a) (BitVec.ofInt 64 n) = true := by
  induction l with
  | nil => rfl
  | cons hd l ih =>
    obtain ⟨b, s⟩ := hd
    have hnw' : a + n < 2 ^ 64 := Hnw
    simp only [region_free]
    rw [ih (fun p hp => Hno p (by simp [hp]))]
    have ha' : ((BitVec.ofInt 64 a).toNat : Int) = a :=
      AgentLib.u64_lit a ⟨Ha, by omega⟩
    have hn' : ((BitVec.ofInt 64 n).toNat : Int) = n :=
      AgentLib.u64_lit n ⟨Hn, by omega⟩
    have hov : iv_overlap (BitVec.ofInt 64 a) (BitVec.ofInt 64 n) b s = false := by
      unfold iv_overlap
      rw [ha', hn']
      have hc := Hno (b, s) (by simp)
      unfold zconflict at hc
      simp only [Prod.fst, Prod.snd] at hc
      by_cases h1 : a < (b.toNat : Int) + (s.toNat : Int)
      · have h2 : ¬ ((b.toNat : Int) < a + n) := fun h2 => hc ⟨h1, h2⟩
        rw [decide_eq_false_iff_not.mpr h2, Bool.and_false]
      · rw [decide_eq_false_iff_not.mpr h1, Bool.false_and]
    rw [hov]
    rfl



/-- An access-free instruction is a silent deterministic node on ANY model
    (in particular with a non-empty lazy ledger: nothing is charged). -/
theorem node_instr_noacc (segs : List Segment) (ms : machine_state) (model : Model)
    (ms' : machine_state)
    (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : step_accesses segs ms = .MachineOk (mkAccessReport ms' [])) :
    node_ok segs (mkCfg ms model) Unit (fun _ => []) (fun _ => mkCfg ms' model) := by
  have Hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
    unfold mi_account_step
    rw [Hstep]
    dsimp only [mkAccessReport]
    rw [materialize_model_accesses_nil]
  constructor
  · intro _
    exact sstep.instr ms model ms' model Hh Hsvc Hacc
  · intro e st hss
    cases hss with
    | instr ms0 model0 ms1 model1 hh hsvc hstep =>
      rw [Hacc] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      exact ⟨(), rfl, rfl⟩
    | instr_fault ms0 model0 hh hsvc hstep =>
      rw [Hacc] at hstep; cases hstep
    | instr_unmodeled ms0 model0 hh hsvc hstep =>
      rw [Hacc] at hstep; cases hstep
    | syscall ms0 model0 x8 eff m' m'' evs hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc; cases hsvc
    | syscall_materialization_fault ms0 model0 x8 eff m' evs hh hsvc hspec hh' hmat =>
      rw [Hsvc] at hsvc; cases hsvc
    | exit ms0 model0 x8 eff m' evs code hh hsvc hspec hh' hk =>
      rw [Hsvc] at hsvc; cases hsvc
    | killed ms0 model0 x8 eff m' evs sig hh hsvc hspec hk =>
      rw [Hsvc] at hsvc; cases hsvc
    | syscall_unmodeled ms0 model0 x8 hh hsvc hspec =>
      rw [Hsvc] at hsvc; cases hsvc



end LinuxSem.Common.RefNodes
