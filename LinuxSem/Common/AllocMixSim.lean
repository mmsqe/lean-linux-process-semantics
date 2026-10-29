/-
  * Common.AllocMixSim — brk outcome sets with trace-silent erroring branches.

    TRUST BOUNDARY: shared proof library, not the trusted specification.
    Image-INDEPENDENT.

    Outcomes are `(List (List byte) × word)` pairs, matching
    `AllocSim.to_outcomes`; the brk syscall number is Int-characterized
    (a pending `x8` with `(x8.toNat : Int) = 214`) exactly as in
    `AllocSim`.

    `AllocSim.to_outcomes` characterizes a brk-branching run whose every
    resolution terminates in a (write buffers, exit code) outcome.  A
    MAY-erroring source — one where some brk resolutions run into the
    explicit error transition while others exit cleanly — does not fit:
    under the universal source-error rule (`Equivalence.equiv` via
    `bh_all_errors`) such a source does NOT free the target, so its
    trace set must still be characterized exactly.

    This file provides `to_outcomes_mix`: the same shape as
    `to_outcomes`, plus an ERROR LEAF (`tom_fault`) for a branch that runs
    a deterministic instruction line into an illegal instruction.  Such
    a branch contributes NO outcome and NO events — every `star` run
    inside it is silent — so the trace set of the whole tree is still
    exactly the prefixes of the outcome traces of the surviving outcome
    set `U` (which must be nonempty, `alloc_mix_obs_iff`).

    The equivalence-level glue `alloc_mix_strong_equiv` pairs a
    may-erroring source (`to_outcomes_mix` with set `U`) with a
    never-erroring target (`to_outcomes` with the SAME set `U`): trace
    sets coincide, and `¬ bh_errors` is required of the TARGET only —
    exactly the obligation `Equivalence.equiv` leaves when the source
    escape is unavailable.

    NOTES.
 `to_outcomes_mix`
      takes `segs` first, so the `AllocSim` lemmas it recurses through
      (`to_outcomes`, `to_outcomes_star_only`, `to_outcomes_star_admits`,
      `to_outcomes_no_error`) are usable without casts.
    - `ms_svc_pending ms` is the projection `ms.ms_svc_pending`; `msteps` is
      `Common.CatSim.msteps`; the `sstep` constructors are `Run.sstep.instr`,
      `Run.sstep.syscall`, ….
    - `Equivalence.modeled` unfolds to `¬ Run.reaches_unmodeled` and the
      right disjunct of `Equivalence.equiv` to trace equality plus
      `¬ reaches_error`; the run-level packaging lemmas
      (`alloc_mix_obs_iff`, `alloc_no_error_run`, `covered_iff`,
      `bh_errors_iff`, `trace_equiv_iff_omni`) are consumed at that level,
      as in `AllocSim.alloc_strong_equiv`.
    - The ambient `FPState` instance (`PropExec.fx0`) is declared locally,
      as `AllocSim2`/`ShapeAlg` do, so that the `AllocSim` lemmas (whose
      proofs go through `PropExec.mkst`) apply.
    - Proof-level only: in `cases` over `star` the first and last
      configurations are fixed by the indices (the run starts at
      `⟨ms, model⟩` and ends at the goal's `c`), so Lean substitutes them
      instead of binding the pattern names; the `step` branches therefore
      refer to the goal's `c` rather than to a `c3`. -/
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
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.Common.SimInv
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.AllocSim
import LinuxSem.Common.ErrEscape

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.AllocMixSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.AllocSim
open LinuxSem.Common.ErrEscape
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

/-- The FP state at process entry, so that the `AllocSim` lemmas (whose
    proofs go through `PropExec.mkst`) elaborate.  Same local instance
    `AllocSim2.lean` and `ShapeAlg.lean` declare. -/
local instance allocmixsim_fx : LinuxSem.Common.PropExec.FPState :=
  LinuxSem.Common.PropExec.fx0

/- =========================================================================
   `to_outcomes_mix`: `to_outcomes` plus trace-silent erroring branches.
   ========================================================================= -/

section WithSegs

/-  `Section WithSegs` variable: the loaded image segments.
   Lean auto-includes it (in the same leading position) in every
   declaration below that mentions it. -/
variable (segs : List Segment)

/-- `to_outcomes` with erroring branches: from `ms` under `model`, the
    non-error resolutions produce EXACTLY the outcome set `U`, and every
    other resolution runs a deterministic silent instruction line into
    the explicit error transition. -/
inductive to_outcomes_mix (segs : List Segment) :
    machine_state → Model → ((List (List byte) × word) → Prop) → Prop where
  | tom_out (ms : machine_state) (model : Model)
      (U : (List (List byte) × word) → Prop)
      (hout : to_outcomes segs ms model U) :
      to_outcomes_mix segs ms model U
  | tom_fault (ms ms' : machine_state) (model : Model)
      (U : (List (List byte) × word) → Prop)
      (hm : msteps segs ms ms')
      (hsvc : ms'.ms_svc_pending = none)
      (hill : RiscvSemantics.step segs ms' = .MachineFault)
      (hU : ∀ o, ¬ U o) :
      to_outcomes_mix segs ms model U
  | tom_step (ms ms' : machine_state) (model : Model)
      (U : (List (List byte) × word) → Prop)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hto : to_outcomes_mix segs ms' model U) :
      to_outcomes_mix segs ms model U
  | tom_brk (ms : machine_state) (model : Model) (x8 : word)
      (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hno : (x8.toNat : Int) = 214)
      (hcont : ∀ (eff : SyscallEffect) (model' : Model) (evs : List event),
         syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
         to_outcomes_mix segs (advance_past_svc (apply_effect ms eff)) model'
           (T eff model'))
      (hU : ∀ o, U o ↔
         (∃ (eff : SyscallEffect) (model' : Model) (evs : List event),
            syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)
            ∧ T eff model' o)) :
      to_outcomes_mix segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tom_msteps (ms ms' : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (H : msteps segs ms ms') (Ht : to_outcomes_mix segs ms' model U) :
    to_outcomes_mix segs ms model U := by
  induction H with
  | mst_refl ms => exact Ht
  | mst_step ms ms' ms'' hsvc hstep hsteps ih =>
    exact to_outcomes_mix.tom_step ms ms' model U hsvc hstep (ih Ht)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tom_equiv (ms : machine_state) (model : Model)
    (U V : (List (List byte) × word) → Prop)
    (Hto : to_outcomes_mix segs ms model U)
    (HV : ∀ o, V o ↔ U o) :
    to_outcomes_mix segs ms model V := by
  revert HV
  induction Hto with
  | tom_out ms model U hout =>
    intro HV
    exact to_outcomes_mix.tom_out ms model V (tou_equiv segs ms model U V hout HV)
  | tom_fault ms ms' model U hm hsvc hill hU =>
    intro HV
    refine to_outcomes_mix.tom_fault ms ms' model V hm hsvc hill ?_
    intro o Ho
    exact hU o ((HV o).mp Ho)
  | tom_step ms ms' model U hsvc hstep hto ih =>
    intro HV
    exact to_outcomes_mix.tom_step ms ms' model V hsvc hstep (ih HV)
  | tom_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro HV
    refine to_outcomes_mix.tom_brk ms model x8 T V hsvc hno ?_ ?_
    · intro eff model' evs hspec
      exact hcont eff model' evs hspec
    · intro o
      exact (HV o).trans (hU o)

/-- `tom_brk` specialized to a continuation family indexed by the
    resolved break value `r` (the mix analogue of `AllocSim.tou_brk_r`). -/
theorem tom_brk_r (ms : machine_state) (model : Model) (x8 : word)
    (T' : word → (List (List byte) × word) → Prop)
    (U : (List (List byte) × word) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : (x8.toNat : Int) = 214)
    (Hcont : ∀ r, brk_resolution_ok model (ms_gpr ms 0) r →
      to_outcomes_mix segs
        (advance_past_svc (apply_effect ms
          (SyscallEffect.mkEffectU r []
                          (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
                          (brk_unmaps r (m_vmmaps model).vm_brk) [] [])))
        (brk_model (ms_gpr ms 0) r model)
        (T' r))
    (HU : ∀ o, U o ↔
      (∃ r, brk_resolution_ok model (ms_gpr ms 0) r ∧ T' r o)) :
    to_outcomes_mix segs ms model U := by
  refine to_outcomes_mix.tom_brk ms model x8 (fun eff _ => T' eff.eff_ret) U
    Hsvc Hno ?_ ?_
  · intro eff model' evs hspec
    obtain ⟨heff, -, hok, hmodel⟩ :=
      (brk_ok_iff segs ms x8 model eff model' evs Hno).mp hspec
    subst hmodel
    rw [heff]
    exact Hcont eff.eff_ret hok
  · intro o
    rw [HU o]
    constructor
    · rintro ⟨r, hok, ht⟩
      exact ⟨SyscallEffect.mkEffectU r []
          (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
          (brk_unmaps r (m_vmmaps model).vm_brk) [] [],
        brk_model (ms_gpr ms 0) r model, [],
        brk_ok_intro segs ms x8 model r Hno hok, ht⟩
    · rintro ⟨eff, model', evs, hspec, ht⟩
      obtain ⟨-, -, hok, -⟩ :=
        (brk_ok_iff segs ms x8 model eff model' evs Hno).mp hspec
      exact ⟨eff.eff_ret, hok, ht⟩

/-- From a non-syscall state whose step is illegal, no `SNext`
    transition exists. -/
theorem illegal_no_snext (ms : machine_state) (model : Model) (evs : List event)
    (c' : config) :
    m_vm_lazy model = [] →
    ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault →
    ¬ sstep segs ⟨ms, model⟩ evs (.SNext c') := by
  intro Hlazy Hsvc Hill Hss
  obtain ⟨-, hst⟩ :=
    sstep_fault_inv segs ms model evs (.SNext c') Hlazy Hsvc Hill Hss
  exact nomatch hst

/-- Every `star` run inside a deterministic line into an illegal
    instruction is silent. -/
theorem err_chain_star_silent (ms ms' : machine_state) (model : Model)
    (Hm : msteps segs ms ms') (Hlazy : m_vm_lazy model = []) :
    ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c → tr = [] := by
  induction Hm with
  | mst_refl ms0 =>
    intro Hsvc' Hill tr c Hstar
    cases Hstar with
    | refl => rfl
    | step c1 evs c2 tr2 c3 Hss Hstar2 =>
      exact absurd Hss (illegal_no_snext segs ms0 model evs c2 Hlazy Hsvc' Hill)
  | mst_step ms0 ms1 ms2 Hsvc Hstep Hm' ih =>
    intro Hsvc' Hill tr c Hstar
    cases Hstar with
    | refl => rfl
    | step c1 evs c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨hevs, hc2⟩ :=
        sstep_instr_inv segs ms0 model ms1 evs (.SNext c2) Hlazy Hsvc Hstep Hss
      subst hevs
      cases hc2
      exact ih Hsvc' Hill tr2 c Hstar2

/-- Trace characterization, "only" direction: every `star` trace is
    either empty or a prefix of an outcome trace of the surviving set. -/
theorem tom_star_only (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes_mix segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      tr = [] ∨ ∃ o, U o ∧ is_prefix tr (outcome_trace (m_fs model) o) := by
  revert Hh Hlazy
  induction Hto with
  | tom_out ms model U hout =>
    intro Hh Hlazy tr c Hstar
    exact Or.inr (to_outcomes_star_only segs ms model U hout Hh Hlazy tr c Hstar)
  | tom_fault ms ms' model U hm hsvc hill hU =>
    intro Hh Hlazy tr c Hstar
    exact Or.inl (err_chain_star_silent segs ms ms' model hm Hlazy hsvc hill tr c Hstar)
  | tom_step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | refl => exact Or.inl rfl
    | step c1 evs c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨hevs, hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy hsvc hstep Hss
      subst hevs
      cases hc2
      exact ih Hh Hlazy tr2 c Hstar2
  | tom_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | refl => exact Or.inl rfl
    | step c1 evs c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨eff, model', hspec, hevs, hc2⟩ :=
        sstep_brk_inv segs ms model x8 evs (.SNext c2) Hh Hlazy hsvc hno Hss
      subst hevs
      cases hc2
      obtain ⟨-, hh', hfs, -, hlazy'⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno hspec
      rcases ih eff model' [] hspec hh' (hlazy'.trans Hlazy) tr2 c Hstar2 with
        hnil | ⟨o, Ho, Hp⟩
      · exact Or.inl hnil
      · refine Or.inr ⟨o, ?_, ?_⟩
        · exact (hU o).mpr ⟨eff, model', [], hspec, Ho⟩
        · rw [← hfs]
          exact Hp

/-- Trace characterization, "admits" direction: every outcome in the
    surviving set is realized by a full run. -/
theorem tom_star_admits (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes_mix segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ∀ o, U o →
      ∃ c, star segs ⟨ms, model⟩ (outcome_trace (m_fs model) o) c := by
  revert Hh Hlazy
  induction Hto with
  | tom_out ms model U hout =>
    intro Hh Hlazy o Ho
    exact to_outcomes_star_admits segs ms model U hout Hh Hlazy o Ho
  | tom_fault ms ms' model U hm hsvc hill hU =>
    intro Hh Hlazy o Ho
    exact absurd Ho (hU o)
  | tom_step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := ih Hh Hlazy o Ho
    refine ⟨c, ?_⟩
    exact star.step ⟨ms, model⟩ [] ⟨ms', model⟩
      (outcome_trace (m_fs model) o) c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep]))
      Hstar
  | tom_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, hspec, ht⟩ := (hU o).mp Ho
    obtain ⟨hevs, hh', hfs, -, hlazy'⟩ :=
      brk_step_shape segs ms x8 model eff model' evs Hh Hlazy hno hspec
    subst hevs
    obtain ⟨c, Hstar⟩ :=
      ih eff model' [] hspec hh' (hlazy'.trans Hlazy) o ht
    refine ⟨c, ?_⟩
    rw [← hfs]
    exact star.step ⟨ms, model⟩ [] ⟨advance_past_svc (apply_effect ms eff), model'⟩
      (outcome_trace (m_fs model') o) c
      (sstep.syscall ms model x8 eff model' model' [] Hh hsvc hspec hh'
        (by rw [materialize_model_accesses_no_lazy model' _ (hlazy'.trans Hlazy)]))
      Hstar

/-- Coverage: a may-erroring brk tree is nonetheless fully MODELED.
    Each shape contributes its own reason — the surviving subtree never
    errors at all, the erroring subtree ends in a genuine
    `MachineFault`, ordinary instructions are `MachineOk`, and brk is
    receptive (`AllocSim.brk_no_unmodeled`), so no reachable configuration is
    one the model declined to interpret. -/
theorem tom_no_unmodeled (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes_mix segs ms model U)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) :
    ¬ reaches_unmodeled segs ⟨ms, model⟩ := by
  revert Hh Hlazy
  induction Hto with
  | tom_out ms model U hout =>
    intro Hh Hlazy
    exact no_error_no_unmodeled segs _
      (to_outcomes_no_error segs ms model U hout Hh Hlazy)
  | tom_fault ms ms' model U hm hsvc hill hU =>
    intro Hh Hlazy
    exact msteps_fault_no_unmodeled segs ms ms' model hm Hlazy hsvc hill
  | tom_step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy
    exact instr_no_unmodeled segs ms ms' model Hlazy hsvc hstep (ih Hh Hlazy)
  | tom_brk ms model x8 T U hsvc hno hcont hU ih =>
    intro Hh Hlazy
    rintro ⟨tr, c, Hstar, Hun⟩
    cases Hstar with
    | refl =>
      obtain ⟨-, hun⟩ := Hun
      rcases hun with ⟨hsvc', -⟩ | ⟨x8', hsvc', herr⟩
      · rw [hsvc] at hsvc'
        exact nomatch hsvc'
      · rw [hsvc] at hsvc'
        cases hsvc'
        exact brk_no_unmodeled segs ms x8 model hno herr
    | step c1 evs c2 tr2 c3 Hss Hstar2 =>
      obtain ⟨eff, model', hspec, -, hc2⟩ :=
        sstep_brk_inv segs ms model x8 evs (.SNext c2) Hh Hlazy hsvc hno Hss
      cases hc2
      obtain ⟨-, hh', -, -, hlazy'⟩ :=
        brk_step_shape segs ms x8 model eff model' [] Hh Hlazy hno hspec
      exact ih eff model' [] hspec hh' (hlazy'.trans Hlazy) ⟨tr2, c, Hstar2, Hun⟩

end WithSegs

/- =========================================================================
   Run-level packaging and the equivalence glue.
   ========================================================================= -/

/-- The trace set of a may-erroring brk tree with a NONEMPTY surviving
    outcome set `U` is exactly the prefixes of `U`'s outcome traces (an
    erroring branch contributes only the empty trace, which is a prefix
    of every outcome trace). -/
theorem alloc_mix_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (List (List byte) × word) → Prop)
    (Hto : to_outcomes_mix segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U)
    (Hne : ∃ o, U o) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
      ↔ ∃ o, U o ∧ is_prefix tr (outcome_trace (in_fs inp) o) := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none :=
    rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] :=
    rfl
  have Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp :=
    rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    rcases tom_star_only segs _ _ U Hto Hh Hlazy tr' c Hstar with
      hnil | ⟨o, Ho, Hp'⟩
    · subst hnil
      obtain ⟨o, Ho⟩ := Hne
      refine ⟨o, Ho, ?_⟩
      cases tr with
      | nil => exact is_prefix_nil _
      | cons e es => exact absurd Hp (by simp [is_prefix])
    · refine ⟨o, Ho, ?_⟩
      rw [Hfs] at Hp'
      exact is_prefix_trans Hp Hp'
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := tom_star_admits segs _ _ U Hto Hh Hlazy o Ho
    rw [Hfs] at Hstar
    exact ⟨outcome_trace (in_fs inp) o, c, Hstar, Hp⟩

/-- The `Equivalence`-level glue: a MAY-erroring source brk tree whose
    surviving outcome set is the (nonempty) `U`, against a
    never-erroring target realizing the SAME `U`.  The source escape is
    unavailable (some source resolution avoids error), so this
    discharges the non-escape disjunct of `equiv`: exact trace-set
    equality plus target no-error. -/
theorem alloc_mix_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes_mix source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U)
    (Hne : ∃ o, U o) :
    modeled (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
    ∧ equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
            (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  constructor
  · unfold modeled
    exact tom_no_unmodeled source_segs _ _ U Hsource rfl rfl
  · right
    constructor
    · intro tr
      exact (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
               Hsource Hne tr).trans
        (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U
          Htarget tr).symm
    · exact alloc_no_error_run target_segs apc aph asp abrk amb arnd alim
        inp U Htarget

/-- The omni equivalence for a may-faulting brk mix against a
    never-faulting target with the same outcome set, at the two role
    budgets: the source is COVERED (its faults are modeled crashes,
    `tom_no_unmodeled`) though not error-free, and the trace sets agree.
    Proved from the ingredients rather than through `strong_equiv_iff`
    so that the `covered_iff` route — the point of the omni reading of a
    crashing source — is visible. -/
theorem alloc_mix_omni_strong_equiv
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw)
    (U : (List (List byte) × word) → Prop) (inp : ProcInput)
    (Hsource : to_outcomes_mix source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp
        source_alloc_limit inp) U)
    (Htarget : to_outcomes target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp
        inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp
        target_alloc_limit inp) U)
    (Hne : ∃ o, U o) :
    omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
      ⟨rsp, rbrk, rmb, rrnd⟩ ⟨asp, abrk, amb, arnd⟩ inp := by
  constructor
  · show coexec source_segs
      (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp)
      (covered source_segs)
    exact (covered_iff source_segs _).mp
      (tom_no_unmodeled source_segs _ _ U Hsource rfl rfl)
  · right
    constructor
    · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) source_alloc_limit
        ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      intro tr
      exact (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd
               source_alloc_limit inp U Hsource Hne tr).trans
        (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit
          inp U Htarget tr).symm
    · refine (bh_errors_iff (mkImage target_segs apc aph) target_alloc_limit
        ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
      exact alloc_no_error_run target_segs apc aph asp abrk amb arnd
        target_alloc_limit inp U Htarget

/-! ## Sanity checks

    `AllocMixSim` carries no `vm_compute` goals — `to_outcomes_mix` is an
    inductive, not a decision procedure — so per the encoding conventions
    these pin the two decidable pieces the file rests on: the `tom_out`
    embedding of an error-free tree, and the prefix relation the trace
    characterization is stated with.  They are checks, not 
    lemmas. -/

section Sanity

/-- An error-free brk tree is a may-erroring one. -/
example (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (List (List byte) × word) → Prop)
    (h : to_outcomes segs ms model U) : to_outcomes_mix segs ms model U :=
  to_outcomes_mix.tom_out ms model U h

/-- A shorter trace is a prefix of a longer one sharing its head. -/
example : is_prefix ([1, 2] : List Nat) [1, 2, 3] := by simp [is_prefix]

/-- ... and a longer one is not a prefix of a shorter one. -/
example : ¬ is_prefix ([1, 2, 3] : List Nat) [1, 2] := by simp [is_prefix]

end Sanity

end LinuxSem.Common.AllocMixSim
