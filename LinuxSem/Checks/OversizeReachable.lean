/-
  * LinuxSem.Checks.OversizeReachable — the finer budget premise, on runs

  Not part of the trusted specification.  As `Checks.BudgetPremise` does for
  the released premise, this shows both directions on runs:

  - the finer premise HOLDS of the `Checks.BudgetPremise.mm_image` run, which
    the released premise excludes, and the finer statement is refuted on it
    (`mm_within_budget_only`, `mm_errors`, `mm_refutes_budgets_only`);
  - it EXCLUDES a run whose second one-page `mmap` at a one-page budget is
    refused for budget and not for oversize
    (`cm_run_budget_only_refused`, `cm_not_within_budget_only`).

  The first is the finer premise's bite: the same run that
  `Checks.BudgetPremise.mm_not_within_budget` rules OUT of the released
  statements is back IN scope under the finer one, so a source that dies
  there refutes the `_budgets_only` form while satisfying its premise.
  The second is the direction the other way: a cumulative refusal is still
  excluded, so the finer premise is not vacuous.
-/
import LinuxSem.Checks.BudgetPremise
import LinuxSem.Checks.Examples
import LinuxSem.Common.MmapSim
import LinuxSem.EquivalenceDefinition.Equivalence

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.Checks
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.BudgetPremise
open LinuxSem.Checks.Omni
open LinuxSem.Checks.Examples

namespace LinuxSem.Checks.OversizeReachable

/-- The `Common.PropExec` floating-point register file the `Common` lemmas
    that reflect on the decoder are parameterized by; `fx0` is the
    arbitrary one the worked-example modules use. -/
local instance oversizereachable_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   The oversize refusal: in scope of the finer premise
   ========================================================================= -/

/-- The request pending at `BudgetPremise.mm_s 6`. -/
def mm_i : SyscallInput := sys_input mm_segments (mm_s 6) (BitVec.ofInt 64 222)

/-- The same input written out, so a lemma stated about `mm_i` can be used
    where the `sys_input` spelling is in the way and conversely. -/
theorem mm_i_eq : mm_i = sys_input mm_segments (mm_s 6) (BitVec.ofInt 64 222) := rfl

theorem mm_i_budget_refused : alloc_budget_refused_b mm_i mm_model = true := by decide

/-- ...and it is an OVERSIZE refusal: the two-page request alone exceeds
    the one-page budget, so the finer premise does not count it. -/
theorem mm_i_classifies_oversize :
    alloc_refuse_reason mm_i mm_model = some .RefuseOversize := by decide

/-- The -ENOMEM refusal the kernel gives it. -/
def mm_eff : SyscallEffect := mkEffect (errno_ret ENOMEM) [] []

/-- The state after the ecall returns that refusal. -/
def mm_ms7 : machine_state := advance_past_svc (apply_effect (mm_s 6) mm_eff)

theorem mm_arg0 : ms_gpr (mm_s 6) 0 = BitVec.ofInt 64 0 := by decide
theorem mm_arg1 : ms_gpr (mm_s 6) 1 = BitVec.ofInt 64 8192 := by decide
theorem mm_arg2 : ms_gpr (mm_s 6) 2 = BitVec.ofInt 64 3 := by decide
theorem mm_arg3 : ms_gpr (mm_s 6) 3 = BitVec.ofInt 64 34 := by decide
theorem mm_arg4 : ms_gpr (mm_s 6) 4 = BitVec.ofInt 64 (-1) := by decide
theorem mm_arg5 : ms_gpr (mm_s 6) 5 = BitVec.ofInt 64 0 := by decide

theorem mm_sysno : (mm_i.in_sysno.toNat : Int) = 222 := by decide

/-- The ecall never leaves the modeled surface: at these arguments the
    mmap checker's answer is not `CheckUnmodeled`, and the checker and the
    spec agree on declination (`check_mmap_complete_unmodeled`). -/
theorem mm_ecall_no_unmodeled : ¬ Specs.syscall_spec mm_i mm_model .unmodeled := by
  intro h
  have hno : (((BitVec.ofInt 64 222)).toNat : Int) = 222 := by decide
  have h2 : Sys.Mm.Mmap.mmap_spec (ms_gpr (mm_s 6) 0) (ms_gpr (mm_s 6) 1)
      (ms_gpr (mm_s 6) 2) (ms_gpr (mm_s 6) 3) (ms_gpr (mm_s 6) 4) (ms_gpr (mm_s 6) 5)
      (sys_input mm_segments (mm_s 6) (BitVec.ofInt 64 222)) mm_model .unmodeled := by
    rw [← LinuxSem.Common.MmapSim.syscall_spec_mmap mm_segments (mm_s 6)
      (BitVec.ofInt 64 222) mm_model .unmodeled hno]
    exact h
  have hcu := LinuxSem.Checks.Sys.Mm.Mmap.check_mmap_complete_unmodeled _ _ _ _ _ _ mm_model
    (sys_input mm_segments (mm_s 6) (BitVec.ofInt 64 222))
    (mkEffect (BitVec.ofInt 64 0) [] []) h2
  rw [mm_arg0, mm_arg1, mm_arg2, mm_arg3, mm_arg4, mm_arg5] at hcu
  have hval : check_mmap (BitVec.ofInt 64 0) (BitVec.ofInt 64 8192) (BitVec.ofInt 64 3)
      (BitVec.ofInt 64 34) (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 0)
      (mkEffect (BitVec.ofInt 64 0) [] []) mm_model = .CheckReject := by
    rfl
  rw [hval] at hcu
  exact nomatch hcu

/-- Every outcome the kernel admits at the ecall is the -ENOMEM refusal,
    with the model unchanged.  The request is a hint-placed anonymous
    mapping of two pages on a one-page budget: the grant arm's `choose`
    guard carries `mmap_noreserve_backed_ok`, which fails here, so the
    `alt` collapses onto its errno arm. -/
theorem mm_ecall_only (o : Outcome SyscallEffect Model event) :
    Specs.syscall_spec mm_i mm_model o → o = .ok mm_eff mm_model [] := by
  intro h
  have hno : (((BitVec.ofInt 64 222)).toNat : Int) = 222 := by decide
  have h2 : Sys.Mm.Mmap.mmap_spec (ms_gpr (mm_s 6) 0) (ms_gpr (mm_s 6) 1)
      (ms_gpr (mm_s 6) 2) (ms_gpr (mm_s 6) 3) (ms_gpr (mm_s 6) 4) (ms_gpr (mm_s 6) 5)
      (sys_input mm_segments (mm_s 6) (BitVec.ofInt 64 222)) mm_model o := by
    rw [← LinuxSem.Common.MmapSim.syscall_spec_mmap mm_segments (mm_s 6)
      (BitVec.ofInt 64 222) mm_model o hno]
    exact h
  rw [mm_arg0, mm_arg1, mm_arg2, mm_arg3, mm_arg4, mm_arg5] at h2
  have hna : Sys.Mm.Mmap.mmap_noreserve_backed_ok (BitVec.ofInt 64 34) mm_model
      (page_round_up_Z ((BitVec.ofInt 64 8192).toNat : Int)) = false := by decide
  cases o with
  | unmodeled => exact absurd h mm_ecall_no_unmodeled
  | ok eff m' evs =>
    simp only [Sys.Mm.Mmap.mmap_spec] at h2
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left (by decide), alt] at h2
    rcases h2 with h2 | h2
    · -- the errno arm: one of the injectable errnos, model unchanged
      obtain ⟨e, m1, evs1, evs2, hch, hk, heq⟩ := h2
      obtain ⟨e0, hmem, ho⟩ := hch
      cases ho
      cases hk
      cases heq
      have he : e = ENOMEM := by
        simp only [Sys.Mm.Mmap.mmap_errnos, List.mem_cons, List.not_mem_nil,
          or_false] at hmem
        exact hmem
      subst he
      rfl
    · -- the grant arm: its placement guard carries the budget conjunct
      exfalso
      obtain ⟨u, m1, evs1, evs2, hmod, hk, heq⟩ := h2
      cases hmod
      obtain ⟨a, m2, fe1, fe2, hch, hkk, heq2⟩ := hk
      obtain ⟨a0, hguard, ho⟩ := hch
      obtain ⟨-, -, -, -, hbud⟩ := hguard
      exact absurd hbud (by decide)

/-- The -ENOMEM refusal IS admitted, so the ecall completes. -/
theorem mm_ecall_admits :
    Specs.syscall_spec mm_i mm_model (.ok mm_eff mm_model []) := by
  have hno : (((BitVec.ofInt 64 222)).toNat : Int) = 222 := by decide
  rw [mm_i_eq, LinuxSem.Common.MmapSim.syscall_spec_mmap mm_segments (mm_s 6)
    (BitVec.ofInt 64 222) mm_model _ hno]
  rw [mm_arg0, mm_arg1, mm_arg2, mm_arg3, mm_arg4, mm_arg5]
  simp only [Sys.Mm.Mmap.mmap_spec]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide), alt]
  left
  exact ⟨ENOMEM, mm_model, [], [], ⟨ENOMEM, by decide, rfl⟩, rfl, rfl⟩

theorem mm_ms7_svc : mm_ms7.ms_svc_pending = none := by decide

/-- After the refusal the program runs off the end of its 24-byte
    segment: the next fetch faults. -/
theorem mm_ms7_faults : RiscvSemantics.step mm_segments mm_ms7 = .MachineFault := rfl

/-- The fetch after the refusal faults, and the accounting says so too. -/
theorem mm_ms7_accesses : RiscvSemantics.step_accesses mm_segments mm_ms7 = .MachineFault :=
  rfl

theorem mm_ms7_accesses_fault (report : access_report machine_state) :
    RiscvSemantics.step_accesses mm_segments mm_ms7 ≠ .MachineOk report := by
  rw [mm_ms7_accesses]
  intro h
  exact nomatch h

/-- "Never budget-only refused from here", closed under `star`. -/
def mm_never_bor (c : config) : Prop :=
  ∀ tr c', star mm_segments c tr c' → ¬ budget_only_refused_at mm_segments c'

theorem mm_never_bor_intro (c : config)
    (Hn : ¬ budget_only_refused_at mm_segments c)
    (Hs : ∀ evs c2, sstep mm_segments c evs (.SNext c2) → mm_never_bor c2) :
    mm_never_bor c := by
  intro tr c' hstar
  cases hstar with
  | refl => exact Hn
  | step _ _ _ _ _ hss hrest => exact Hs _ _ hss _ _ hrest

theorem mm_never_bor_c7 : mm_never_bor ⟨mm_ms7, mm_model⟩ := by
  apply mm_never_bor_intro
  · rintro ⟨-, h | h⟩
    · obtain ⟨-, report, hacc, -⟩ := h
      change RiscvSemantics.step_accesses mm_segments mm_ms7 = .MachineOk report at hacc
      exact mm_ms7_accesses_fault report hacc
    · obtain ⟨x8, hx8, -⟩ := h
      rw [mm_ms7_svc] at hx8
      exact nomatch hx8
  · intro evs c2 hss
    obtain ⟨-, hfault⟩ := LinuxSem.Checks.Omni.sstep_fault_only mm_segments mm_ms7 mm_model
      (by decide) mm_ms7_svc mm_ms7_faults evs (.SNext c2) hss
    exact absurd hfault (by simp)

theorem mm_never_bor_c6 : mm_never_bor ⟨mm_s 6, mm_model⟩ := by
  apply mm_never_bor_intro
  · rintro ⟨-, h | h⟩
    · obtain ⟨hnone, -⟩ := h
      rw [mm_svc6] at hnone
      exact nomatch hnone
    · obtain ⟨x8, hx8, h | h⟩ := h
      · rw [mm_svc6] at hx8
        obtain rfl := Option.some.inj hx8
        rw [← mm_i_eq, mm_i_classifies_oversize] at h
        exact absurd h (by simp)
      · obtain ⟨eff, m', evs, hspec, hhalt, hmat⟩ := h
        rw [mm_svc6] at hx8
        obtain rfl := Option.some.inj hx8
        have hone := mm_ecall_only (.ok eff m' evs) hspec
        cases hone
        rw [materialize_model_accesses_no_lazy mm_model _ (by decide)] at hmat
        exact nomatch hmat
  · intro evs c2 hss
    cases hss with
    | instr ms model ms' model' hh hsvc hstep =>
      rw [mm_svc6] at hsvc; exact absurd hsvc (by simp)
    | syscall ms model x8 eff model' model'' evs hh hsvc hspec hh' hmat =>
      rw [mm_svc6] at hsvc
      obtain rfl := Option.some.inj hsvc
      have hone := mm_ecall_only (.ok eff model' evs) hspec
      cases hone
      rw [materialize_model_accesses_no_lazy mm_model _ (by decide)] at hmat
      obtain rfl := Option.some.inj hmat
      exact mm_never_bor_c7
    | exit ms model x8 eff model' evs code hh hsvc hspec hh' hk =>
      rw [mm_svc6] at hsvc
      obtain rfl := Option.some.inj hsvc
      have hone := mm_ecall_only (.ok eff model' evs) hspec
      cases hone
      rw [show m_halted mm_model = none from by decide] at hh'
      exact absurd hh' (by simp)
    | killed ms model x8 eff model' evs sig hh hsvc hspec hk =>
      rw [mm_svc6] at hsvc
      obtain rfl := Option.some.inj hsvc
      have hone := mm_ecall_only (.ok eff model' evs) hspec
      cases hone
      rw [show m_killed mm_model = none from by decide] at hk
      exact absurd hk (by simp)

theorem mm_never_bor_k_aux : ∀ d k, 6 - k = d → k ≤ 6 →
    mm_never_bor ⟨mm_s k, mm_model⟩ := by
  intro d
  induction d with
  | zero =>
    intro k hd hk
    have hk6 : k = 6 := by omega
    subst hk6
    exact mm_never_bor_c6
  | succ d ih =>
    intro k hd hk
    have hlt : k < 6 := by omega
    apply mm_never_bor_intro
    · intro hb
      exact budget_refused_at_no_lazy_instr mm_segments (mm_s k) mm_model (by decide)
        (mm_svc_none k hlt) (budget_only_refused_at_implies _ _ hb)
    · intro evs c2 hss
      obtain ⟨-, hc2⟩ := LinuxSem.Checks.Omni.sstep_instr_only mm_segments (mm_s k) mm_model
        (mm_s (k + 1)) (by decide) (mm_svc_none k hlt) (mm_step k hlt mm_ms0.ms_mem)
        evs (.SNext c2) hss
      obtain rfl := step_to.SNext.inj hc2
      exact ih (k + 1) (by omega) (by omega)

/-- Whatever the program counter is at, the budget-only mark is not
    reached from `⟨mm_s k, mm_model⟩` for `k ≤ 6`. -/
theorem mm_never_bor_k (k : Nat) (Hk : k ≤ 6) : mm_never_bor ⟨mm_s k, mm_model⟩ :=
  mm_never_bor_k_aux (6 - k) k rfl Hk

/-- The finer premise HOLDS of the mm run: from the start no configuration
    on any `star` path is refused for budget only.  The ecall's refusal is
    an OVERSIZE one (`mm_i_classifies_oversize`), and everything else on
    the path is either an instruction step (no budget clause fires: the
    lazy ledger is empty) or the final fetch fault. -/
theorem mm_within_budget_only :
    source_within_budget_only mm_budget mm_image demo_entry
      LinuxSem.Checks.Omni.demo_proc_input := by
  intro hc
  unfold run_budget_only_refused at hc
  simp only [mm_image, demo_entry, LinuxSem.EquivalenceDefinition.Equivalence.mkImage] at hc
  rw [mm_config] at hc
  obtain ⟨tr, c, hstar, hb⟩ := hc
  exact mm_never_bor_k 0 (by omega) tr c hstar hb

/- ... which the released premise does not
   (`Checks.BudgetPremise.mm_not_within_budget`). -/

/-- The mm run errors: the refusal, then a fetch fault. -/
theorem mm_errors : (run mm_image mm_budget demo_entry
    LinuxSem.Checks.Omni.demo_proc_input).bh_errors := by
  show reaches_error mm_segments
    (init_config mm_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw mm_budget
      LinuxSem.Checks.Omni.demo_proc_input)
  rw [mm_config]
  refine ⟨[], ⟨mm_ms7, mm_model⟩, [], ?_, ?_⟩
  · refine star_trans mm_segments mm_c [] ⟨mm_s 6, mm_model⟩ mm_star []
      ⟨mm_ms7, mm_model⟩
      (star.step ⟨mm_s 6, mm_model⟩ [] ⟨mm_ms7, mm_model⟩ [] ⟨mm_ms7, mm_model⟩ ?_
        (star.refl _))
    exact sstep.syscall (mm_s 6) mm_model (BitVec.ofInt 64 222) mm_eff mm_model mm_model
      [] (by decide) mm_svc6 mm_ecall_admits (by decide)
      (materialize_model_accesses_no_lazy mm_model _ (by decide))
  · exact sstep.instr_fault _ _ rfl mm_ms7_svc (by no_lazy; rw [mm_ms7_faults])

/-- The demo entry is valid for the mm image at every valid input.  The
    same argument as `Checks.BudgetPremise.demo_entry_valid_ebreak`: the
    image's segments do not enter it. -/
theorem demo_entry_valid_mm (inp : ProcInput) (Hvalid : valid_input inp) :
    valid_entry mm_image demo_entry inp := by
  rw [valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvalid)]
  obtain ⟨Hargv, Henvp, -⟩ := Hvalid
  obtain ⟨-, Hspan⟩ := entry_stack_span_bound _ _ Hargv Henvp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold valid_sp demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold sp_window_lo sp_window_hi
    exact ⟨by omega, by omega, by decide⟩
  · unfold valid_brk mm_image mm_segments
    decide
  · unfold valid_mmap_base demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold mmap_base_min mmap_base_max sp_window_hi page_size
    exact ⟨by omega, by omega, by decide⟩
  · unfold entry_stack_fits demo_entry
    rw [bv_unsigned_Z_to_bv_u64 _ ⟨by decide, by decide⟩]
    unfold entry_stack_span_max sp_window_hi at *
    omega

/-- `strong_universal_error_free_T_budgets_only_refuted_by_source_error`,
    fired: the finer statement is false of the mm run paired with the
    exit-0 image, at its one-page budget and every target budget.  The
    released statement at the same budgets says nothing about this input
    (`Checks.BudgetPremise.mm_not_within_budget`). -/
theorem mm_refutes_budgets_only (lim_target : Int) :
    ¬ strong_universal_error_free_T_budgets_only mm_budget lim_target
        mm_image exit0_image := by
  apply strong_universal_error_free_T_budgets_only_refuted_by_source_error
    mm_budget lim_target mm_image exit0_image demo_entry demo_entry
    LinuxSem.Checks.Omni.demo_proc_input
  · apply demo_entry_valid_mm
    exact demo_input_valid
  · apply demo_entry_valid_exit0
    exact demo_input_valid
  · exact demo_input_valid
  · exact mm_within_budget_only
  · exact mm_errors

/-- The exit-0 image satisfies the finer premise at every budget. -/
theorem exit0_source_within_budget_only (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : source_within_budget_only lim exit0_image en inp := by
  intro hc
  exact exit0_never_budget_refused lim en inp (run_budget_only_refused_implies _ _ _ _ hc)

/- =========================================================================
   A cumulative refusal: excluded by the finer premise
   ========================================================================= -/

/-- Seven instructions at 0x100: two
    `mmap(addr, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)`
    calls.  The first passes `addr = 0`.  The second passes the address
    the first returned, which stays in `a0`; without MAP_FIXED it is only
    a hint, and the hint-placed branch does not read it.  At a one-page
    budget the first may be granted, and the second is then refused with
    a charge equal to the budget. -/
def cm_segment : Segment where
  seg_base := 0x100
  seg_size := 28
  seg_perms := "r-x"
  seg_bytes := ["9308e00db715000013063000930620021307f0ff7300000073000000"]

def cm_segments : List Segment := [cm_segment]

def cm_image : Image :=
  LinuxSem.EquivalenceDefinition.Equivalence.mkImage cm_segments 0x100 demo_phdrs

def cm_budget : Int := page_size

def cm_ms0 : machine_state :=
  init_machine_state cm_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
    demo_draw
    LinuxSem.Checks.Omni.demo_proc_input.in_argv
    LinuxSem.Checks.Omni.demo_proc_input.in_envp
    LinuxSem.Checks.Omni.demo_proc_input.in_uid
    LinuxSem.Checks.Omni.demo_proc_input.in_hwcap

def cm_msk (k : Nat) : machine_state :=
  match run_steps k cm_segments cm_ms0 with
  | some ms => ms
  | none => cm_ms0

def cm_s (k : Nat) : machine_state := with_mem (cm_msk k) cm_ms0.ms_mem

def cm_model : Model :=
  init_model (segments_reserved cm_segments) (BitVec.ofInt 64 0x1000)
    (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000) cm_budget
    LinuxSem.Checks.Omni.demo_proc_input

def cm_c : config := ⟨cm_s 0, cm_model⟩

theorem cm_config :
    init_config cm_segments 0x100 demo_phdrs (BitVec.ofInt 64 0x7fff80000000)
      (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 mmap_base_max) demo_draw cm_budget
      LinuxSem.Checks.Omni.demo_proc_input = cm_c := by
  simp only [cm_c, cm_s, cm_msk, run_steps, cm_budget]
  rw [← with_mem_eta cm_ms0]
  rfl

theorem cm_step : ∀ k, k < 6 → ∀ mem,
    RiscvSemantics.step cm_segments (with_mem (cm_msk k) mem)
      = .MachineOk (with_mem (cm_msk (k + 1)) mem) := by
  intro k Hk mem
  rcases k with _ | _ | _ | _ | _ | _ | k <;> first | istep | omega

theorem cm_instr_sstep (k : Nat) (Hk : k < 6) :
    sstep cm_segments ⟨cm_s k, cm_model⟩ [] (.SNext ⟨cm_s (k + 1), cm_model⟩) := by
  have hstep : mi_account_step cm_segments (cm_s k) cm_model
      = .MachineOk (cm_s (k + 1), cm_model) := by
    no_lazy
    simp only [cm_s]
    rw [cm_step k Hk cm_ms0.ms_mem]
  have hsvc : (cm_s k).ms_svc_pending = none := by
    rcases k with _ | _ | _ | _ | _ | _ | k <;> first | decide | omega
  exact sstep.instr _ _ _ _ rfl hsvc hstep

theorem cm_star6 : star cm_segments cm_c [] ⟨cm_s 6, cm_model⟩ := by
  unfold cm_c
  exact star.step _ _ _ _ _ (cm_instr_sstep 0 (by omega))
    (star.step _ _ _ _ _ (cm_instr_sstep 1 (by omega))
      (star.step _ _ _ _ _ (cm_instr_sstep 2 (by omega))
        (star.step _ _ _ _ _ (cm_instr_sstep 3 (by omega))
          (star.step _ _ _ _ _ (cm_instr_sstep 4 (by omega))
            (star.step _ _ _ _ _ (cm_instr_sstep 5 (by omega)) (star.refl _))))))

/-- The first request, before any grant: within budget, so not refused. -/
def cm_i1 : SyscallInput := sys_input cm_segments (cm_s 6) (BitVec.ofInt 64 222)

theorem cm_ecall1_not_refused : alloc_refuse_reason cm_i1 cm_model = none := by decide

/-- THE ADDRESS THE MODEL CHOOSES.  The hint-placed branch admits any
    positive, page-aligned, free address whose mapping ends at or below
    `State.alloc_top`, when its budget gate passes; this effect names
    one, and `cm_sc1` is the acceptor's statement that it is admissible. -/
def cm_addr : word := BitVec.ofInt 64 0x10000000

def cm_eff1 : SyscallEffect := mkEffect cm_addr [] [(cm_addr, BitVec.ofInt 64 4096)]

def cm_model1 : Model :=
  match check_syscall cm_i1 cm_eff1 cm_model with
  | .CheckOk m _ => m
  | _ => cm_model

theorem cm_sc1 : check_syscall cm_i1 cm_eff1 cm_model = .CheckOk cm_model1 [] := rfl

theorem cm_sc1_spec : Specs.syscall_spec cm_i1 cm_model (.ok cm_eff1 cm_model1 []) := by
  apply (check_syscall_ok_iff cm_i1 cm_eff1 cm_model cm_model1 []).mp
  exact cm_sc1

/-- The state the first call leaves: `a0` holds the address, the page is
    zeroed, and the pc is at the second `ecall`. -/
def cm_t0 : machine_state := advance_past_svc (apply_effect (cm_s 6) cm_eff1)

def cm_tk (k : Nat) : machine_state :=
  match run_steps k cm_segments cm_t0 with
  | some ms => ms
  | none => cm_t0

def cm_t (k : Nat) : machine_state := with_mem (cm_tk k) cm_t0.ms_mem

theorem cm_t0_eq : cm_t 0 = cm_t0 := by
  simp only [cm_t, cm_tk, run_steps]
  exact (with_mem_eta cm_t0).symm

theorem cm_syscall1_sstep :
    sstep cm_segments ⟨cm_s 6, cm_model⟩ [] (.SNext ⟨cm_t 0, cm_model1⟩) := by
  rw [cm_t0_eq]
  unfold cm_t0
  have hsvc : (cm_s 6).ms_svc_pending = some (BitVec.ofInt 64 222) := by decide
  exact sstep.syscall (cm_s 6) cm_model (BitVec.ofInt 64 222) cm_eff1 cm_model1
    cm_model1 [] rfl hsvc cm_sc1_spec rfl
    (materialize_model_accesses_no_lazy cm_model1 _ rfl)

theorem cm_step2 : ∀ mem,
    RiscvSemantics.step cm_segments (with_mem (cm_tk 0) mem)
      = .MachineOk (with_mem (cm_tk 1) mem) := by
  intro mem
  istep

theorem cm_instr2_sstep :
    sstep cm_segments ⟨cm_t 0, cm_model1⟩ [] (.SNext ⟨cm_t 1, cm_model1⟩) := by
  have hstep : mi_account_step cm_segments (cm_t 0) cm_model1
      = .MachineOk (cm_t 1, cm_model1) := by
    no_lazy
    simp only [cm_t]
    rw [cm_step2]
  have hsvc : (cm_t 0).ms_svc_pending = none := by decide
  exact sstep.instr _ _ _ _ rfl hsvc hstep

theorem cm_svc_t1 : (cm_t 1).ms_svc_pending = some (BitVec.ofInt 64 222) := by decide

/-- The second request: budget-refused, with a charge of one page, equal
    to the budget and not above it, so the classifier gives
    `.RefuseBudget`. -/
def cm_i2 : SyscallInput := sys_input cm_segments (cm_t 1) (BitVec.ofInt 64 222)

theorem cm_ecall2_charge :
    alloc_req_charge_bytes cm_i2 cm_model1 = cm_budget
    ∧ (m_vmmaps cm_model1).vm_limit = cm_budget := by
  refine ⟨?_, ?_⟩ <;> decide

theorem cm_ecall2_classifies_budget :
    alloc_refuse_reason cm_i2 cm_model1 = some .RefuseBudget := by decide

theorem cm_ecall2_is_budget_only_refused :
    budget_only_refused_at cm_segments ⟨cm_t 1, cm_model1⟩ := by
  refine ⟨rfl, Or.inr ⟨BitVec.ofInt 64 222, cm_svc_t1, Or.inl ?_⟩⟩
  exact cm_ecall2_classifies_budget

theorem cm_run_budget_only_refused :
    run_budget_only_refused cm_image cm_budget demo_entry
      LinuxSem.Checks.Omni.demo_proc_input := by
  unfold run_budget_only_refused
  simp only [cm_image, demo_entry, LinuxSem.EquivalenceDefinition.Equivalence.mkImage]
  rw [cm_config]
  refine ⟨[], ⟨cm_t 1, cm_model1⟩, ?_, cm_ecall2_is_budget_only_refused⟩
  refine star_trans cm_segments cm_c [] ⟨cm_s 6, cm_model⟩ cm_star6 []
    ⟨cm_t 1, cm_model1⟩ ?_
  refine star_trans cm_segments ⟨cm_s 6, cm_model⟩ [] ⟨cm_t 0, cm_model1⟩
    (star.step _ _ _ _ _ cm_syscall1_sstep (star.refl _)) []
    ⟨cm_t 1, cm_model1⟩ (star.step _ _ _ _ _ cm_instr2_sstep (star.refl _))

/-- ... so the finer premise excludes this run, and with it the released
    premise (`Equivalence.source_within_budget_only_of_source_within_budget`). -/
theorem cm_not_within_budget_only :
    ¬ source_within_budget_only cm_budget cm_image demo_entry
        LinuxSem.Checks.Omni.demo_proc_input := by
  intro H
  exact H cm_run_budget_only_refused

theorem cm_not_within_budget :
    ¬ source_within_budget cm_budget cm_image demo_entry
        LinuxSem.Checks.Omni.demo_proc_input := by
  intro H
  exact cm_not_within_budget_only
    (source_within_budget_only_of_source_within_budget cm_budget cm_image demo_entry
      LinuxSem.Checks.Omni.demo_proc_input H)

end LinuxSem.Checks.OversizeReachable
