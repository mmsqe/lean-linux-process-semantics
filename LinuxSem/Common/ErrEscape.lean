/-
  * Common.ErrEscape — the SOURCE-ERROR ESCAPE glue.

  TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.ExitSim),
  NOT part of the trusted specification.

  Following the PropExec conventions: the decode hypotheses go through
  `DecodeC.decodeAny` with `Instr.load` ASTs and encoded-width `BitVec 12`
  immediates; the faulting address is
  `v_addi (getr regs rs) imm.toInt` (the `step_lbu`/`step_ld`
  address shape), read via `ov_rdn`.  The instruction SIZE returned by
  `decodeAny` is quantified (`isz : Int`, where the healthy load lemmas pin `4`) —
  a faulting load never advances the pc, so the same lemma covers a
  compressed `C.LD` encoding.

  `Equivalence.equiv` contains an escape hatch only if EVERY execution
  of the SOURCE binary reaches the explicit error transition.  This
  file packages that proof for the most common all-error shape: a
  deterministic straight line of ordinary instructions ending in an
  illegal one (e.g. a load from an unmapped address):

  - `step_lbu_fault` / `step_ld_fault`: a byte/double load whose
    address is unreadable (writable overlay AND ROM both miss) is an
    illegal instruction (`MachineFault`);
  - `msteps_illegal_all_traces_error`: an `msteps` run
    (Common.CatSim) into a non-syscall state whose next step is
    `MachineFault` proves `Run.all_traces_error`;
  - `err_escape_equiv`: at the `Equivalence` level, such a source run
    discharges `equiv (run source ...) target` for ANY `target`
    behavior — the target need not be analyzed at all.

  The omni reading (`msteps_illegal_exec`) says the same in ONE
  judgment: every execution of the path ends by erroring FROM the
  faulting configuration.  `OmniRun.exec` with that postcondition
  carries both what the escape needs (`Run.all_traces_error`, via
  `OmniRun.all_traces_error_iff`) and what keeps the escape honest
  (`Equivalence.modeled`, via `OmniRun.coexec_covered` and the fact
  that a `MachineFault` is not the model giving up), so the two
  sections below are corollaries of it, and `err_escape_omni_strong_equiv`
  is the packaged escape in the shape of
  `OmniEquivalence.omni_strong_equiv`.

  NOTES.

  - `Section WithFP1`'s `Context {fx : FPState}` is this tree's AMBIENT
    typeclass instance (`variable [fx : FPState]`), exactly as in
    `Common.PropExec`: `mkst` reads the FP register file and fcsr out of it,
    so only the two faulting-load lemmas (the only ones that mention `mkst`)
    pick it up.
  - `Variable segs : list Segment` is an EXPLICIT LEADING PARAMETER on every
    declaration that mentions it — the convention `ExitSim.lean`,
    `CatSim.lean`, `Run.lean` and `OmniRun.lean` follow for their sections.
  - `mkCfg ms model` is the `config` record constructor `⟨ms, model⟩`;
    `mkEntry sp brk0 mb rnd` is the `ExecEntry` record constructor
    `⟨sp, brk0, mb, rnd⟩`.
  - `RiscvSemantics.step segs ms` stays explicit in `segs` (this tree keeps
    `mi_loaded_segments` a leading parameter rather than a section variable).
 No  declaration is weakened by it.
  - `all_traces_error_iff`/`covered`/`errors`/`never_errors`/`exits_with` are
    `OmniRun`'s; `Equivalence.modeled` is `OmniEquivalence.modeled_iff.mpr`.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.OmniRun
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.CatSim
import LinuxSem.Common.PropExec

set_option autoImplicit false

namespace LinuxSem.Common.ErrEscape

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.PropExec

/- =========================================================================
   Faulting loads

   `Section WithFP1`'s `Context {fx : FPState}` — the ambient FP state the
   `mkst` states below are built with — is spelled `variable [fx : FPState]`
   in the section these two lemmas live in, as in `Common.PropExec`.
   ========================================================================= -/

section FaultLoads

variable [fx : FPState]

/-- A byte load from an unreadable address is an illegal instruction. -/
theorem step_lbu_fault (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (isz : Int) :
    fetch_word segs pc = some w →
    is_ecall w = false →
    decodeAny w = some (Instr.load .SZ1 true rd rs imm, isz) →
    rdn segs mem (v_addi (getr regs rs) imm.toInt) 1 = none →
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineFault := by
  intro Hfetch Hecall Hdecode Hread
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 1 = none := by
    rw [b_addsext (getr regs rs) imm (by decide), ov_rdn]
    exact Hread
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]

/-- A double load from an unreadable address is an illegal instruction. -/
theorem step_ld_fault (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (isz : Int) :
    fetch_word segs pc = some w →
    is_ecall w = false →
    decodeAny w = some (Instr.load .SZ8 true rd rs imm, isz) →
    rdn segs mem (v_addi (getr regs rs) imm.toInt) 8 = none →
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineFault := by
  intro Hfetch Hecall Hdecode Hread
  have hov : ov_read_bytes segs mem (getr regs rs + sext 64 imm) 8 = none := by
    rw [b_addsext (getr regs rs) imm (by decide), ov_rdn]
    exact Hread
  step_load_start2 Hfetch, Hecall, Hdecode
  simp only [rget, getr, bv_eqb0_is_x0, w0] at hov ⊢
  rw [hov]

end FaultLoads

/-!  Lean's `cases` has to name every arm, so the fact
    is stated once here and used there. -/

/-- From an accounted `MachineFault` on a non-syscall state, the ONLY `sstep`
    is the error transition, and it emits nothing. -/
theorem sstep_fault_inv (segs : List Segment) (ms : machine_state) (model : Model)
    (evs : List event) (st : step_to) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    Run.sstep segs ⟨ms, model⟩ evs st →
    (evs = [] ∧ st = .SError) := by
  intro Hlazy Hsvc Hfault Hss
  have Hacc : mi_account_step segs ms model = .MachineFault := by
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hfault]
  cases Hss with
  | instr ms0 model0 ms0' model0' hh hsvc hacc =>
    exfalso
    rw [Hacc] at hacc
    exact nomatch hacc
  | instr_fault ms0 model0 hh hsvc hacc => exact ⟨rfl, rfl⟩
  | instr_unmodeled ms0 model0 hh hsvc hacc =>
    exfalso
    rw [Hacc] at hacc
    exact nomatch hacc
  | syscall ms0 model0 x8 eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_materialization_fault ms0 model0 x8 eff model1 evs0 hh hsvc hspec hh' hmat =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | exit ms0 model0 x8 eff model1 evs0 code hh hsvc hspec hh' hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | killed ms0 model0 x8 eff model1 evs0 sig hh hsvc hspec hk =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)
  | syscall_unmodeled ms0 model0 x8 hh hsvc hspec =>
    exact absurd (hsvc.symm.trans Hsvc) (by simp)

/- =========================================================================
   msteps into an illegal step reaches the error transition
   ========================================================================= -/

/-- An `msteps` run is a silent `star` (the model is untouched). -/
theorem msteps_star_nil (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    Run.star segs ⟨ms, model⟩ [] ⟨ms', model⟩ := by
  intro Hh Hlazy H
  induction H with
  | mst_refl ms0 => exact Run.star.refl ⟨ms0, model⟩
  | mst_step ms0 ms1 ms2 hsvc hstep htail ih =>
    have hss : Run.sstep segs ⟨ms0, model⟩ [] (.SNext ⟨ms1, model⟩) :=
      Run.sstep.instr ms0 model ms1 model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms0 model Hlazy, hstep])
    simpa using Run.star.step ⟨ms0, model⟩ [] ⟨ms1, model⟩ [] ⟨ms2, model⟩ hss ih

/-- Straight line of instructions, then an illegal one: error reached. -/
theorem msteps_illegal_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    reaches_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hm Hsvc Hill
  refine ⟨[], ⟨ms', model⟩, [], msteps_star_nil segs ms ms' model Hh Hlazy Hm, ?_⟩
  exact Run.sstep.instr_fault ms' model Hh Hsvc
    (by rw [mi_account_step_no_lazy segs ms' model Hlazy, Hill])

/- =========================================================================
   The omni reading: one judgment for the whole escape
   ========================================================================= -/

/-- The faulting state: its only transition is the error one, taken
    from itself. -/
theorem illegal_exec (segs : List Segment) (ms : machine_state) (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    OmniRun.exec segs ⟨ms, model⟩
      (fun tr o => tr = [] ∧ o = .OError ⟨ms, model⟩) := by
  intro Hh Hlazy Hsvc Hill
  have hacc : mi_account_step segs ms model = .MachineFault := by
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hill]
  have herr : ∀ evs, Run.sstep segs ⟨ms, model⟩ evs .SError →
      (evs = [] ∧ (outcome.OError ⟨ms, model⟩) = (outcome.OError ⟨ms, model⟩)) := by
    intro evs hss
    obtain ⟨hevs, -⟩ := sstep_fault_inv segs ms model evs .SError Hlazy Hsvc Hill hss
    exact ⟨hevs, rfl⟩
  have hnext : ∀ evs c', Run.sstep segs ⟨ms, model⟩ evs (.SNext c') →
      OmniRun.exec segs c' (fun tr o => (evs ++ tr = [] ∧ o = .OError ⟨ms, model⟩)) := by
    intro evs c' hss
    obtain ⟨-, hst⟩ := sstep_fault_inv segs ms model evs (.SNext c') Hlazy Hsvc Hill hss
    exact nomatch hst
  exact OmniRun.exec.step ⟨ms, model⟩ _ Hh
    ⟨[], .SError, Run.sstep.instr_fault ms model Hh Hsvc hacc⟩ herr hnext

/-- One ordinary instruction in front of any omni judgment: the
    transition is unique and silent, so the postcondition is unchanged. -/
theorem instr_exec (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (Q : post) :
    m_halted model = none →
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    OmniRun.exec segs ⟨ms', model⟩ Q →
    OmniRun.exec segs ⟨ms, model⟩ Q := by
  intro Hh Hlazy Hsvc Hstep Hex
  refine OmniRun.exec_step_only segs ⟨ms, model⟩ Q [] ⟨ms', model⟩ ?_ ?_ ?_
  · exact Run.sstep.instr ms model ms' model Hh Hsvc
      (by rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep])
  · intro evs st hss
    exact sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep hss
  · simpa using Hex

theorem msteps_exec (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (Q : post) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    OmniRun.exec segs ⟨ms', model⟩ Q →
    OmniRun.exec segs ⟨ms, model⟩ Q := by
  intro Hh Hlazy Hm Hex
  revert Hex
  induction Hm with
  | mst_refl ms0 => intro Hex; exact Hex
  | mst_step ms0 ms1 ms2 hsvc hstep htail ih =>
    intro Hex
    exact instr_exec segs ms0 ms1 model Q Hh Hlazy hsvc hstep (ih Hex)

/-- THE judgment: a deterministic instruction path ending in an illegal
    instruction errors, on every execution, from that instruction's
    configuration. -/
theorem msteps_illegal_exec (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.exec segs ⟨ms, model⟩
      (fun tr o => tr = [] ∧ o = .OError ⟨ms', model⟩) := by
  intro Hh Hlazy Hm Hsvc Hill
  exact msteps_exec segs ms ms' model _ Hh Hlazy Hm
    (illegal_exec segs ms' model Hh Hlazy Hsvc Hill)

/-- The faulting configuration is covered: the fault is a
    `MachineFault`, not the model giving up. -/
theorem fault_covered_at (segs : List Segment) (ms : machine_state) (model : Model) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    ¬ unmodeled_at segs ⟨ms, model⟩ := by
  intro Hlazy Hsvc Hfault
  rintro ⟨-, hun | hun⟩
  · obtain ⟨-, hacc⟩ := hun
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hfault] at hacc
    exact nomatch hacc
  · obtain ⟨x8, hsvcx, -⟩ := hun
    exact absurd hsvcx (by rw [Hsvc]; simp)

/-- What the one judgment yields: the escape ... -/
theorem msteps_illegal_errors (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.exec segs ⟨ms, model⟩ errors := by
  intro Hh Hlazy Hm Hsvc Hill
  refine OmniRun.exec_conseq segs ⟨ms, model⟩ _ errors
    (msteps_illegal_exec segs ms ms' model Hh Hlazy Hm Hsvc Hill) ?_
  intro tr o h
  rw [h.2]
  exact True.intro

/-- ... and coverage, without a separate walk of the path. -/
theorem msteps_illegal_covered (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.coexec segs ⟨ms, model⟩ (covered segs) := by
  intro Hh Hlazy Hm Hsvc Hill
  refine OmniRun.exec_coexec segs _ _ ?_
  refine OmniRun.exec_conseq segs ⟨ms, model⟩ _ (covered segs)
    (msteps_illegal_exec segs ms ms' model Hh Hlazy Hm Hsvc Hill) ?_
  intro tr o h
  rw [h.2]
  exact fault_covered_at segs ms' model Hlazy Hsvc Hill

/-- Bites: the judgment NAMES the outcome, so the other readings of the
    same path are refuted — it does not exit with any code, and it is not
    error-free. -/
theorem msteps_illegal_no_exit (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    ∀ code, ¬ OmniRun.exec segs ⟨ms, model⟩ (exits_with code) := by
  intro Hh Hlazy Hm Hsvc Hill code Hex
  obtain ⟨tr, o, hm, heq⟩ :=
    OmniRun.exec_realizes segs _ _
      (msteps_illegal_exec segs ms ms' model Hh Hlazy Hm Hsvc Hill)
  obtain rfl := heq.2
  exact OmniRun.exec_sound segs _ _ Hex tr _ hm

theorem msteps_illegal_not_never_errors (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    ¬ OmniRun.coexec segs ⟨ms, model⟩ never_errors := by
  intro Hh Hlazy Hm Hsvc Hill Hco
  obtain ⟨tr, o, hm, heq⟩ :=
    OmniRun.exec_realizes segs _ _
      (msteps_illegal_exec segs ms ms' model Hh Hlazy Hm Hsvc Hill)
  obtain rfl := heq.2
  exact (OmniRun.coexec_sound segs _ tr _ hm never_errors Hco) True.intro

/- =========================================================================
   Universal error for deterministic instruction paths
   ========================================================================= -/

/-- An illegal ordinary-instruction state has exactly the error step and
    therefore all of its executions error. -/
theorem illegal_all_traces_error (segs : List Segment) (ms : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    all_traces_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hsvc Hill
  have hacc : mi_account_step segs ms model = .MachineFault := by
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hill]
  refine all_traces_error.intro ⟨ms, model⟩ ⟨[], .SError, ?_⟩ ?_
  · exact Run.sstep.instr_fault ms model Hh Hsvc hacc
  · intro evs c' hss
    obtain ⟨-, hst⟩ := sstep_fault_inv segs ms model evs (.SNext c') Hlazy Hsvc Hill hss
    exact nomatch hst

/-- Prepending the unique ordinary instruction transition preserves the
    universal error property. -/
theorem instr_all_traces_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    all_traces_error segs ⟨ms', model⟩ →
    all_traces_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hsvc Hstep Hall
  refine all_traces_error.intro ⟨ms, model⟩ ⟨[], .SNext ⟨ms', model⟩, ?_⟩ ?_
  · exact Run.sstep.instr ms model ms' model Hh Hsvc
      (by rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep])
  · intro evs c' hss
    obtain ⟨-, hto⟩ :=
      sstep_instr_inv segs ms model ms' evs (.SNext c') Hlazy Hsvc Hstep hss
    cases hto
    exact Hall

/-- Prepend any deterministic sequence of ordinary instructions to an
    all-error configuration. -/
theorem msteps_all_traces_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    all_traces_error segs ⟨ms', model⟩ →
    all_traces_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hm Hall
  revert Hall
  induction Hm with
  | mst_refl ms0 => intro Hall; exact Hall
  | mst_step ms0 ms1 ms2 hsvc hstep htail ih =>
    intro Hall
    exact instr_all_traces_error segs ms0 ms1 model Hh Hlazy hsvc hstep (ih Hall)

/-- A deterministic instruction path ending in an illegal instruction
    has no alternative non-error trace. -/
theorem msteps_illegal_all_traces_error (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_halted model = none →
    m_vm_lazy model = [] →
    msteps segs ms ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    all_traces_error segs ⟨ms, model⟩ := by
  intro Hh Hlazy Hm Hfinal_svc Hillegal
  exact (all_traces_error_iff segs ⟨ms, model⟩).mpr
    (msteps_illegal_errors segs ms ms' model Hh Hlazy Hm Hfinal_svc Hillegal)

/- =========================================================================
   Coverage: the deterministic fault path is MODELED
   ========================================================================= -/

/-! The escape paths are exactly the paths where the source is EXPECTED
    to error, so they are the paths where `Equivalence.modeled` cannot be
    obtained from a `¬ reaches_error` proof (there is no such proof —
    the source really does error).  They have to be closed directly, and
    the content of doing so is the whole point of the split: the fault at
    the end of the path is a `MachineFault` — a load from an unmapped
    address, which a real process suffers as SIGSEGV — and every state
    before it is an ordinary `MachineOk` instruction.  Nowhere on the
    path does the MODEL give up, so the run is fully covered even though
    it dies. -/

/-- A configuration with no `SNext` successor is only `star`-reachable
    from itself. -/
theorem star_stuck_refl (segs : List Segment) (c : config) (tr : List event)
    (c' : config) :
    (∀ evs c2, ¬ Run.sstep segs c evs (.SNext c2)) →
    Run.star segs c tr c' → c' = c := by
  intro Hno Hstar
  cases Hstar with
  | refl => rfl
  | step _ evs c2 _ _ hss _ => exact absurd hss (Hno evs c2)

/-- The faulting state itself is covered: its only transition is the
    error one, and that error is a genuine fault. -/
theorem fault_no_unmodeled (segs : List Segment) (ms : machine_state) (model : Model) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    ¬ reaches_unmodeled segs ⟨ms, model⟩ := by
  intro Hlazy Hsvc Hfault
  have Hno : ∀ evs c2, ¬ Run.sstep segs ⟨ms, model⟩ evs (.SNext c2) := by
    intro evs c2 hss
    obtain ⟨-, hst⟩ := sstep_fault_inv segs ms model evs (.SNext c2) Hlazy Hsvc Hfault hss
    exact nomatch hst
  rintro ⟨tr, c, Hstar, Hun⟩
  have hc : c = ⟨ms, model⟩ := star_stuck_refl segs ⟨ms, model⟩ tr c Hno Hstar
  rw [hc] at Hun
  obtain ⟨-, hun | hun⟩ := Hun
  · obtain ⟨-, hacc'⟩ := hun
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hfault] at hacc'
    exact nomatch hacc'
  · obtain ⟨x8, hsvcx, -⟩ := hun
    exact absurd hsvcx (by rw [Hsvc]; simp)

/-- One ordinary instruction in front of a covered configuration. -/
theorem instr_no_unmodeled (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineOk ms' →
    ¬ reaches_unmodeled segs ⟨ms', model⟩ →
    ¬ reaches_unmodeled segs ⟨ms, model⟩ := by
  intro Hlazy Hsvc Hstep Hnext
  rintro ⟨tr, c, Hstar, Hun⟩
  cases Hstar with
  | refl =>
    obtain ⟨-, hun | hun⟩ := Hun
    · obtain ⟨-, hacc⟩ := hun
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep] at hacc
      exact nomatch hacc
    · obtain ⟨x8, hsvcx, -⟩ := hun
      exact absurd hsvcx (by rw [Hsvc]; simp)
  | step _ evs c2 tr0 _ hss hstar =>
    obtain ⟨-, hc2⟩ :=
      sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy Hsvc Hstep hss
    cases hc2
    exact Hnext ⟨tr0, c, hstar, Hun⟩

/-- A deterministic instruction path ending in a genuine fault never
    reaches a configuration the model does not cover. -/
theorem msteps_fault_no_unmodeled (segs : List Segment) (ms ms' : machine_state)
    (model : Model) :
    msteps segs ms ms' →
    m_vm_lazy model = [] →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    ¬ reaches_unmodeled segs ⟨ms, model⟩ := by
  intro Hm Hlazy Hsvc Hfault
  cases hh : m_halted model with
  | some code =>
    -- a halted model takes no transition, and a halted configuration is
    -- not one the model declined
    rintro ⟨tr, c, Hstar, Hun⟩
    cases Hstar with
    | refl =>
      obtain ⟨h1, -⟩ := Hun
      rw [hh] at h1
      exact nomatch h1
    | step _ evs c2 _ _ hss _ =>
      have hrun := sstep_from_running segs ⟨ms, model⟩ evs (.SNext c2) hss
      rw [hh] at hrun
      exact nomatch hrun
  | none =>
    exact OmniRun.coexec_covered segs _
      (msteps_illegal_covered segs ms ms' model hh Hlazy Hm Hsvc Hfault)

/- =========================================================================
   Equivalence-level escape
   ========================================================================= -/

/-- The omni escape, per run: the source's judgment at any budget ... -/
theorem err_escape_omni_run (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    omni_run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp errors := by
  intro Hm Hsvc Hill
  show OmniRun.exec segs (init_config segs pc ph sp brk0 mb rnd lim inp) errors
  exact msteps_illegal_errors segs _ ms'
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl Hm Hsvc Hill

/-- ... its coverage ... -/
theorem err_escape_omni_covered (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp (covered segs) := by
  intro Hm Hsvc Hill
  show OmniRun.coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) (covered segs)
  exact msteps_illegal_covered segs _ ms'
    (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl Hm Hsvc Hill

/-- ... `OmniEquivalence.omni_equiv` against ANY target run ... -/
theorem err_escape_omni_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (T : Image) (limT : Int) (et : ExecEntry) (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    omni_equiv (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ T limT et inp := by
  intro Hm Hsvc Hill
  exact Or.inl (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill)

/-- ... and the packaged `OmniEquivalence.omni_strong_equiv`: a source
    that deterministically faults, against any target image and entry. -/
theorem err_escape_omni_strong_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (inp : ProcInput)
    (T : Image) (et : ExecEntry) (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    omni_strong_equiv (mkImage segs pc ph) T ⟨sp, brk0, mb, rnd⟩ et inp := by
  intro Hm Hsvc Hill
  refine ⟨?_, ?_⟩
  · exact err_escape_omni_covered segs pc ph sp brk0 mb rnd source_alloc_limit inp ms'
      Hm Hsvc Hill
  · exact err_escape_omni_equiv segs pc ph sp brk0 mb rnd source_alloc_limit inp T
      target_alloc_limit et ms' Hm Hsvc Hill

/-- If the SOURCE deterministically runs into a faulting instruction,
    `Equivalence.equiv` holds against ANY target behavior (the escape in
    `Equivalence.equiv`): the target is freed entirely.  From the omni
    judgment through `OmniRun.bh_all_errors_iff`. -/
theorem err_escape_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (target : behavior) (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    equiv (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) target := by
  intro Hm Hsvc Hill
  refine Or.inl ?_
  exact (bh_all_errors_iff (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp).mpr
    (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill)

/-- …and the same run is MODELED: it dies, but at a `MachineFault`, with
    nothing but ordinary instructions before it.  This is what stops the
    escape from being a way to launder an unmodeled source through the
    theorem.  From the same omni judgment, through
    `OmniEquivalence.modeled_iff`. -/
theorem err_escape_modeled (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    modeled (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp) := by
  intro Hm Hsvc Hill
  refine (modeled_iff (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp).mpr ?_
  exact err_escape_omni_covered segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill

/-- The packaged escape: both clauses of `Equivalence.strong_equiv` for a
    source that deterministically faults, against ANY target. -/
theorem err_escape_strong_equiv (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (target : behavior) (ms' : machine_state) :
    msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    modeled (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp)
    ∧ equiv (run (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp)
         target := by
  intro Hm Hsvc Hill
  refine ⟨?_, ?_⟩
  · exact err_escape_modeled segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill
  · exact err_escape_equiv segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill

end LinuxSem.Common.ErrEscape
