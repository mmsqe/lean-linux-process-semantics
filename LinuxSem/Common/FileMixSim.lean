/-
  * Common.FileMixSim — file outcome sets with trace-silent erroring branches.

  TRUST BOUNDARY: shared proof library, not the trusted specification.
  Image-INDEPENDENT.

  Sibling of `FileSim`.  Outcomes are `(word × Fs.Fs)` pairs; errnos are
  `Int` (`Te : Int → _`); fds are `word`s and the injected fd is
  `alloc_fd (m_fds model)`; the injectable errno set is `openat_errnos`
  (membership predicate `e ∈ openat_errnos`).  The raw-ecall records carry
  the `ms_resv := none` field and a `BvMap word` register file
  (`reg_get regs 10/11/12` are a0/a1/a2, `getr regs 17` is a7); the
  syscall number is Int-characterized (`((getr regs 17).toNat : Int) = 56`).

  `FileSim.to_fout` characterizes a file-syscall-branching run whose
  every resolution terminates in an (exit code, final fs) outcome.  A
  MAY-erroring source — one where some syscall resolutions run into
  the explicit error transition while others exit cleanly — does not
  fit: under the universal source-error rule (`Equivalence.equiv` via
  `bh_all_errors`) such a source does NOT free the target, so its
  trace set must still be characterized exactly.

  An over-PATH_MAX path is a real -ENAMETOOLONG (see
  `Open.openat_spec`), so it gives an ordinary `FileSim.to_fout` tree,
  not this shape.  This file covers the general shape — a source that
  may error on SOME resolutions and exit cleanly on others — which any
  unmodeled syscall reached on only some resolutions produces.  No
  example instantiates it.

  This file provides `to_fout_mix`: the same shape as `to_fout`, plus
  an ERROR LEAF (`tfm_unmodeled`) for a branch that runs a deterministic
  silent instruction line into a syscall whose relational spec is
  `Unmodeled`.  Such a branch contributes NO outcome and NO events — every
  `star` run inside it is silent — so the trace set of the whole tree
  is still exactly the prefixes of the outcome traces of the
  surviving outcome set `U` (which must be nonempty,
  `fout_mix_obs_iff`).

  The equivalence-level glue `file_mix_equiv_only` pairs a
  may-erroring source (`to_fout_mix` with set `U`) with a
  never-erroring target (`to_fout` with the SAME set `U`): trace sets
  coincide, and `¬ bh_errors` is required of the TARGET only —
  exactly the obligation `Equivalence.equiv` leaves when the source
  escape is unavailable.

  NOTE (`Equivalence.modeled`).  Unlike every other combinator in
  `Common/`, this one does NOT supply the source-coverage clause, and
  cannot: `tfm_unmodeled`'s error leaf is a syscall whose spec is `Unmodeled`,
  which is precisely `Run.unmodeled_at`.  A source that needs
  `tfm_unmodeled` is a source this model failed to follow, so its caller has
  no way to discharge `Equivalence.strong_equiv`'s first conjunct.
  That is why the lemma is named `file_mix_equiv_only` and NOT
  `..._strong_equiv`: every `*_strong_equiv*` lemma in `Common/`
  closes BOTH conjuncts, and this one closes only `equiv`, so sharing
  the name would invite a proof author to reach for it and land on an
  unclosable goal.  It has no callers (`openat_spec` answers an
  over-PATH_MAX pathname with an ordinary -ENAMETOOLONG); it is kept
  because the containment it proves is real and the fix for any
  future instance belongs in the SPEC, not in a weaker theorem.
  `AllocMixSim.to_outcomes_mix`, whose error leaf is a genuine
  `MachineFault` rather than a spec `Unmodeled`, DOES supply the clause —
  see `AllocMixSim.tom_no_unmodeled` for the contrast.

  Ergonomic nodes mirror FileSim's: `tfm_open_rd_rec` /
  `tfm_open_wr_rec` (openat branching with `to_fout_mix`
  continuations).  The error leaf is the generic `tfm_unmodeled`: a silent
  line into a syscall whose spec is `Unmodeled`.

  NOTES.
  - `Section WithSegs`'s `Variable segs : list Segment` becomes an
    EXPLICIT LEADING PARAMETER on every declaration that mentions it, as
    `ExitSim`/`WallSim`/`FileSim` do for their sections; `End WithSegs`
    therefore adds nothing, and the run-level lemmas that sit AFTER it
     (`fout_mix_obs_iff`, `file_mix_equiv_only`,
    `file_mix_omni_equiv_only`, `file_mix_unmodeled_leaf_not_covered`)
    still take `segs` first because they are inside `WithFP1` and mention
    it.
  - `Z` → `Int`; `Z_to_bv n z` → `BitVec.ofInt n z`; `bv_unsigned w` →
    `(w.toNat : Int)`; `two_pow_64` stays `two_pow_64`; `Te : Z -> _` is
    `Te : Int → _`.
  - `mkCfg ms model` is `⟨ms, model⟩`; `mkEntry sp brk0 mb rnd` is
    `⟨sp, brk0, mb, rnd⟩`; `SNext`/`SError` are `.SNext`/`.SError`;
    `syscall_spec … Unmodeled` / `… (Ok eff model' evs)` are
    `.unmodeled` / `.ok eff model' evs`; `destruct` on an `Outcome` or a
    `machine_result` is `cases`/`obtain`.
  - `tfm_unmodeled`'s `forall o, ~ U o` is `∀ o, ¬ U o`.
 `FileSim.erec` is that
    literal as a `def`, so a caller whose state is the literal record
    matches by computation; this tree's `FileSim.tfo_open_rd_rec` /
    `tfo_open_wr_rec` use the same spelling, and the proofs below mirror
    theirs (`erec_gpr_0/1/2`, `erec_read_byte`, `adv_eff_ret_copyins`).
 The
    `syscall_spec`-`Unmodeled`-has-no-`Ok`-resolution fact is the same one
    `FileSim.spec_err_all_traces_error` proves inline.
  - `fout_mix_obs_iff`'s empty-trace case: `is_prefix [] l` is `True` and
    `is_prefix (_ :: _) []` is `False` by `is_prefix`'s own equations, so
    `destruct tr` becomes `cases tr` and the impossible branch is
    `False.elim`.
-/
import LinuxSem.Common.FileSim

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LinuxSem.Common.FileMixSim

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.OmniRun
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Open
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence
open LinuxSem.Common.SimInv
open LinuxSem.Common.ExitSim
open LinuxSem.Common.CatSim
open LinuxSem.Common.WallSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.ErrEscape
open LinuxSem.Common.FileSim

variable [fx : FPState]

/- `Section WithSegs`'s `Variable segs : list Segment` is an explicit
   leading parameter from here on. -/

/-- `to_fout` with erroring branches: from `ms` under `model`, the
    non-error resolutions produce EXACTLY the outcome set `U`, and every
    other resolution runs a deterministic silent instruction line into a
    syscall whose spec is `Unmodeled` (the explicit error transition). -/
inductive to_fout_mix (segs : List Segment) : machine_state → Model →
    ((word × Fs.Fs) → Prop) → Prop where
  | out (ms : machine_state) (model : Model) (U : (word × Fs.Fs) → Prop)
      (hout : to_fout segs ms model U) :
      to_fout_mix segs ms model U
  | unmodeled (ms ms' : machine_state) (model : Model) (x8 : word)
      (U : (word × Fs.Fs) → Prop)
      (hm : msteps segs ms ms')
      (hsvc : ms'.ms_svc_pending = some x8)
      (herr : Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled)
      (hU : ∀ o, ¬ U o) :
      to_fout_mix segs ms model U
  | step (ms ms' : machine_state) (model : Model) (U : (word × Fs.Fs) → Prop)
      (hsvc : ms.ms_svc_pending = none)
      (hstep : RiscvSemantics.step segs ms = .MachineOk ms')
      (hto : to_fout_mix segs ms' model U) :
      to_fout_mix segs ms model U
  | sys (ms : machine_state) (model : Model) (x8 : word)
      (T : SyscallEffect → Model → (word × Fs.Fs) → Prop)
      (U : (word × Fs.Fs) → Prop)
      (hsvc : ms.ms_svc_pending = some x8)
      (hne : ¬ Specs.syscall_spec (sys_input segs ms x8) model .unmodeled)
      (hrec : ∃ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs))
      (hshape : ∀ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
        evs = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = [])
      (hcont : ∀ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs) →
        to_fout_mix segs (advance_past_svc (apply_effect ms eff)) model' (T eff model'))
      (hU : ∀ o, U o ↔ (∃ eff model' evs,
        Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' evs)
          ∧ T eff model' o)) :
      to_fout_mix segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tfm_msteps (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (H : msteps segs ms ms')
    (Ht : to_fout_mix segs ms' model U) : to_fout_mix segs ms model U := by
  induction H with
  | mst_refl ms => exact Ht
  | mst_step ms ms' ms'' hsvc hstep hm ih =>
    exact to_fout_mix.step ms ms' model U hsvc hstep (ih Ht)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tfm_equiv (segs : List Segment) (ms : machine_state) (model : Model)
    (U V : (word × Fs.Fs) → Prop) (Hto : to_fout_mix segs ms model U)
    (HV : ∀ o, V o ↔ U o) : to_fout_mix segs ms model V := by
  revert V
  induction Hto with
  | out ms model U hout =>
    intro V HV
    exact to_fout_mix.out ms model V (tfo_equiv segs ms model U V hout HV)
  | unmodeled ms ms' model x8 U hm hsvc herr hU =>
    intro V HV
    refine to_fout_mix.unmodeled ms ms' model x8 V hm hsvc herr ?_
    intro o Ho
    exact hU o ((HV o).mp Ho)
  | step ms ms' model U hsvc hstep hto ih =>
    intro V HV
    exact to_fout_mix.step ms ms' model V hsvc hstep (ih V HV)
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro V HV
    exact to_fout_mix.sys ms model x8 T V hsvc hne hrec hshape hcont
      (fun o => (HV o).trans (hU o))

/- ===================================================================== -/
/- The error leaf is silent                                            -/
/- ===================================================================== -/

/-- A syscall configuration whose relational spec is `Unmodeled` has no
    `SNext` successor (completeness of the executable checker).
 This tree states the same content once as the local
    "every step is the error transition" fact `H` (the regime where every
    `sstep` constructor is a pattern, so the four `.SNext` arms can be
    refuted and the four `.SError` arms are `rfl`), then specialises it —
    the same device `Common.ErrEscape`'s `sstep_fault_inv` uses for its
    inline `inversion …; congruence`. -/
theorem spec_err_no_snext (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (evs : List event) (c' : config)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Herr : Specs.syscall_spec (sys_input segs ms x8) model .unmodeled) :
    ¬ sstep segs ⟨ms, model⟩ evs (.SNext c') := by
  have Hno_ok : ∀ (eff : SyscallEffect) (model' : Model) (events : List event),
      ¬ Specs.syscall_spec (sys_input segs ms x8) model (.ok eff model' events) := by
    intro eff model' events Hok
    have h1 := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model eff Herr
    have h2 := Checks.ExecutableSpecs.check_syscall_complete_ok
      (sys_input segs ms x8) eff model model' events Hok
    rw [h1] at h2
    exact check_result.noConfusion h2
  have H : ∀ (evs' : List event) (st : step_to),
      sstep segs ⟨ms, model⟩ evs' st → st = .SError := by
    intro evs' st Hss
    cases Hss with
    | instr ms0 model0 ms0' model0' hh hsvc hacc =>
      exact absurd (Hsvc.symm.trans hsvc) (by simp)
    | instr_fault ms0 model0 hh hsvc hacc => rfl
    | instr_unmodeled ms0 model0 hh hsvc hacc => rfl
    | syscall ms0 model0 x8' eff model1 model2 evs0 hh hsvc hspec hh' hmat =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model1 _ hspec
    | syscall_materialization_fault ms0 model0 x8' eff model1 evs0 hh hsvc hspec hh' hmat =>
      rfl
    | exit ms0 model0 x8' eff model1 evs0 code hh hsvc hspec hh' hk =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model1 _ hspec
    | killed ms0 model0 x8' eff model1 evs0 sig hh hsvc hspec hk =>
      exfalso
      have hx8 : x8' = x8 := (Option.some.inj (by rw [Hsvc] at hsvc; exact hsvc)).symm
      rw [hx8] at hspec
      exact Hno_ok eff model1 _ hspec
    | syscall_unmodeled ms0 model0 x8' hh hsvc hspec => rfl
  intro Hss
  have hse := H evs (.SNext c') Hss
  cases hse

/-- Every `star` run inside a deterministic line into a spec-`Unmodeled`
    syscall is silent. -/
theorem spec_err_chain_star_silent (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (x8 : word) (Hm : msteps segs ms ms') :
    m_vm_lazy model = [] →
    ms'.ms_svc_pending = some x8 →
    Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c → tr = [] := by
  induction Hm with
  | mst_refl ms0 =>
    intro Hlazy Hsvc Herr tr c Hstar
    cases Hstar with
    | refl => rfl
    | step c1 evs c2 tr0 c3 hss hstar =>
      exact absurd hss (spec_err_no_snext segs ms0 model x8 evs c2 Hsvc Herr)
  | mst_step ms0 ms1 ms2 hsvc hstep hm ih =>
    intro Hlazy Hsvc Herr tr c Hstar
    cases Hstar with
    | refl => rfl
    | step c1 evs c2 tr0 c3 hss hstar =>
      obtain ⟨hevs, hc2⟩ :=
        sstep_instr_inv segs ms0 model ms1 evs (.SNext c2) Hlazy hsvc hstep hss
      rw [hevs]
      have hc2' : c2 = ⟨ms1, model⟩ := (step_to.SNext.injEq _ _).mp hc2
      rw [hc2'] at hstar
      simp only [List.nil_append]
      exact ih Hlazy Hsvc Herr tr0 c hstar

/-- The `tfm_unmodeled` leaf is NOT covered: it is `Run.unmodeled_at`
    reached by a silent line, so `OmniRun.covered` is refuted — the
    contrast with `ErrEscape.msteps_illegal_covered`. -/
theorem msteps_spec_err_not_covered (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hm : msteps segs ms ms') (Hsvc : ms'.ms_svc_pending = some x8)
    (Herr : Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled) :
    ¬ OmniRun.coexec segs ⟨ms, model⟩ (covered segs) := by
  intro Hco
  refine coexec_covered segs ⟨ms, model⟩ Hco ⟨[], ⟨ms', model⟩, ?_, ?_⟩
  · exact msteps_star_nil segs ms ms' model Hh Hlazy Hm
  · unfold unmodeled_at
    exact ⟨Hh, Or.inr ⟨x8, Hsvc, Herr⟩⟩

theorem msteps_spec_err_may_uncovered (segs : List Segment) (ms ms' : machine_state)
    (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hm : msteps segs ms ms') (Hsvc : ms'.ms_svc_pending = some x8)
    (Herr : Specs.syscall_spec (sys_input segs ms' x8) model .unmodeled) :
    ∃ tr o, OmniRun.mexec segs ⟨ms, model⟩ tr o ∧ uncovered segs tr o := by
  have Hun : unmodeled_at segs ⟨ms', model⟩ := ⟨Hh, Or.inr ⟨x8, Hsvc, Herr⟩⟩
  obtain ⟨evs, Hss⟩ := unmodeled_at_sstep_error segs ⟨ms', model⟩ Hun
  refine ⟨[] ++ evs, .OError ⟨ms', model⟩, ?_, ?_⟩
  · exact star_mexec segs ⟨ms, model⟩ [] ⟨ms', model⟩ evs (.OError ⟨ms', model⟩)
      (msteps_star_nil segs ms ms' model Hh Hlazy Hm)
      (mexec.error ⟨ms', model⟩ evs Hss)
  · simpa [uncovered] using Hun

/- ===================================================================== -/
/- Trace characterization                                            -/
/- ===================================================================== -/

/-- "Only" direction: every `star` trace is either empty or a prefix of
    an outcome trace of the surviving set. -/
theorem tfm_star_only (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout_mix segs ms model U) :
    m_halted model = none → m_vm_lazy model = [] →
    ∀ (tr : List event) (c : config), star segs ⟨ms, model⟩ tr c →
      tr = [] ∨ ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  induction Hto with
  | out ms model U hout =>
    intro Hh Hlazy tr c Hstar
    exact Or.inr (to_fout_star_only segs ms model U hout Hh Hlazy tr c Hstar)
  | unmodeled ms ms' model x8 U hm hsvc herr hU =>
    intro Hh Hlazy tr c Hstar
    exact Or.inl (spec_err_chain_star_silent segs ms ms' model x8 hm Hlazy hsvc herr tr c Hstar)
  | step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | refl => exact Or.inl rfl
    | step c1 evs c2 tr0 c3 hss hstar =>
      obtain ⟨hevs, hc2⟩ :=
        sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy hsvc hstep hss
      rw [hevs]
      have hc2' : c2 = ⟨ms', model⟩ := (step_to.SNext.injEq _ _).mp hc2
      rw [hc2'] at hstar
      simp only [List.nil_append]
      exact ih Hh Hlazy tr0 c hstar
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | refl => exact Or.inl rfl
    | step c1 evs c2 tr0 c3 hss hstar =>
      obtain ⟨eff, model', hspec, hevs, hc2⟩ :=
        sstep_fsys_inv segs ms model x8 evs (.SNext c2) Hh Hlazy hsvc hne hshape hss
      rw [hevs]
      have hc2' : c2 = ⟨advance_past_svc (apply_effect ms eff), model'⟩ :=
        (step_to.SNext.injEq _ _).mp hc2
      rw [hc2'] at hstar
      obtain ⟨-, hh', hlazy'⟩ := hshape eff model' [] hspec
      simp only [List.nil_append]
      rcases ih eff model' [] hspec hh' hlazy' tr0 c hstar with rfl | ⟨o, Ho, Hp⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨o, (hU o).mpr ⟨eff, model', [], hspec, Ho⟩, Hp⟩

/-- "Admits" direction: every outcome in the surviving set is realized
    by a full run. -/
theorem tfm_star_admits (segs : List Segment) (ms : machine_state) (model : Model)
    (U : (word × Fs.Fs) → Prop) (Hto : to_fout_mix segs ms model U) :
    m_halted model = none → m_vm_lazy model = [] →
    ∀ o, U o → ∃ c, star segs ⟨ms, model⟩ (fout_trace o) c := by
  induction Hto with
  | out ms model U hout =>
    intro Hh Hlazy o Ho
    exact to_fout_star_admits segs ms model U hout Hh Hlazy o Ho
  | unmodeled ms ms' model x8 U hm hsvc herr hU =>
    intro Hh Hlazy o Ho
    exact absurd Ho (hU o)
  | step ms ms' model U hsvc hstep hto ih =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := ih Hh Hlazy o Ho
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨ms', model⟩ (fout_trace o) c
      (sstep.instr ms model ms' model Hh hsvc
        (by rw [mi_account_step_no_lazy segs ms model Hlazy, hstep])) Hstar⟩
  | sys ms model x8 T U hsvc hne hrec hshape hcont hU ih =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, hspec, Ht⟩ := (hU o).mp Ho
    obtain ⟨hevs, hh', hlazy'⟩ := hshape eff model' evs hspec
    rw [hevs] at hspec
    obtain ⟨c, Hstar⟩ := ih eff model' [] hspec hh' hlazy' o Ht
    exact ⟨c, star.step ⟨ms, model⟩ [] ⟨advance_past_svc (apply_effect ms eff), model'⟩
      (fout_trace o) c
      (sstep.syscall ms model x8 eff model' model' [] Hh hsvc hspec hh'
        (by rw [materialize_model_accesses_no_lazy model' _ hlazy'])) Hstar⟩

/- ===================================================================== -/
/- Ergonomic nodes                                                   -/
/- ===================================================================== -/

/-- Core open node over an abstract success-model builder `mk`, with
    `to_fout_mix` continuations (mirror of `FileSim.tfo_open_core`). -/
theorem tfm_open_core (segs : List Segment) (ms : machine_state) (model : Model)
    (mk : word → Model) (x8 : word) (reads : List (word × Nat))
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Hchk : ∀ eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk)
    (Hmk : ∀ fd, m_halted (mk fd) = none ∧ m_vm_lazy (mk fd) = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout_mix segs (advance_past_svc (apply_effect ms
         (with_copyins reads (mkEffect (errno_ret e) [] [])))) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout_mix segs (advance_past_svc (apply_effect ms
         (with_copyins reads (mkEffect fd [] [])))) (mk fd) (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout_mix segs ms model U := by
  refine to_fout_mix.sys ms model x8
    (fun eff _ => if addr_is_error_b (eff.eff_ret)
       then Te (two_pow_64 - ((eff.eff_ret).toNat : Int)) else Ts (eff.eff_ret))
    U Hsvc ?_ ?_ ?_ ?_ ?_
  · -- no Unmodeled
    intro Hspec
    have hc := Checks.ExecutableSpecs.check_syscall_complete_unmodeled
      (sys_input segs ms x8) model (mkEffect (BitVec.ofInt 64 0) [] []) Hspec
    rw [Hchk] at hc
    exact check_open_result_copyins_never_unmodeled reads _ model mk hc
  · -- receptive: ENOMEM
    refine ⟨with_copyins reads (mkEffect (errno_ret ENOMEM) [] []), model, [], ?_⟩
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk, check_open_result_copyins_ok_iff]
    exact Or.inl ⟨ENOMEM, ENOMEM_in_Sys.Fs.Open.openat_errnos, rfl, rfl, rfl⟩
  · -- shape
    intro eff model' evs Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_open_result_copyins_ok_iff] at Hs
    rcases Hs with ⟨e, -, rfl, rfl, rfl⟩ | ⟨fd, -, -, rfl, rfl, rfl⟩
    · exact ⟨rfl, Hh, Hlazy⟩
    · exact ⟨rfl, (Hmk fd).1, (Hmk fd).2⟩
  · -- continuations
    intro eff model' evs Hs
    rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
      check_open_result_copyins_ok_iff] at Hs
    rcases Hs with ⟨e, hmem, rfl, rfl, -⟩ | ⟨fd, hlk, heq, rfl, rfl, -⟩
    · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
      rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
        errno_ret_recover e h1 h2]
      simp only [ite_true]
      exact Herr e hmem
    · have hne : addr_is_error_b fd = false := by
        rw [heq]
        exact alloc_fd_not_error_b _
      rw [with_copyins_eff_ret_fd, hne]
      simp only [Bool.false_eq_true, ite_false]
      exact Hok fd hlk heq
  · -- outcome set
    intro o
    rw [HU o]
    constructor
    · rintro (⟨e, hmem, hT⟩ | ⟨fd, hlk, heq, hT⟩)
      · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
        refine ⟨with_copyins reads (mkEffect (errno_ret e) [] []), model, [], ?_, ?_⟩
        · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
            check_open_result_copyins_ok_iff]
          exact Or.inl ⟨e, hmem, rfl, rfl, rfl⟩
        · rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
            errno_ret_recover e h1 h2]
          simp only [ite_true]
          exact hT
      · have hne : addr_is_error_b fd = false := by
          rw [heq]
          exact alloc_fd_not_error_b _
        refine ⟨with_copyins reads (mkEffect fd [] []), mk fd, [], ?_, ?_⟩
        · rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
            check_open_result_copyins_ok_iff]
          exact Or.inr ⟨fd, hlk, heq, rfl, rfl, rfl⟩
        · rw [with_copyins_eff_ret_fd, hne]
          simp only [Bool.false_eq_true, ite_false]
          exact hT
    · rintro ⟨eff, model', evs, hspec, hT⟩
      rw [← Checks.ExecutableSpecs.check_syscall_ok_iff, Hchk,
        check_open_result_copyins_ok_iff] at hspec
      rcases hspec with ⟨e, hmem, rfl, rfl, -⟩ | ⟨fd, hlk, heq, rfl, rfl, -⟩
      · obtain ⟨h1, h2⟩ := openat_errno_range e hmem
        left
        refine ⟨e, hmem, ?_⟩
        rw [with_copyins_eff_ret_errno, errno_ret_error_b e h1 h2,
          errno_ret_recover e h1 h2] at hT
        simpa only [ite_true] using hT
      · have hne : addr_is_error_b fd = false := by
          rw [heq]
          exact alloc_fd_not_error_b _
        right
        refine ⟨fd, hlk, heq, ?_⟩
        /- Rewritten in the step of its own (see `FileSim.open_ok`'s mirror
           arm): folded into one `simpa`, `hne` has to fire inside the
           `ite`'s `Decidable` argument, which this toolchain does not do. -/
        rw [with_copyins_eff_ret_fd, hne] at hT
        simpa only [Bool.false_eq_true, ite_false] using hT

/-- O_RDONLY openat of a present file, at the raw ecall record: errno
    branch or any free fd, with `to_fout_mix` continuations. -/
theorem tfm_open_rd_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path) (d : List byte)
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 0)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hfs : fs_lookup (m_fs model) p = some d)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout_mix segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem
         (seg_rom segs)) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout_mix segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
         (with_fds (fd_insert (m_fds model) fd (FdEntry.FdFile p (BitVec.ofInt 64 0)))
            model)
         (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout_mix segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 0 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = (0 : Int) := by
    rw [Hg2]
    decide
  refine tfm_open_core segs (erec regs pc mem (seg_rom segs)) model
    (fun fd => with_fds (fd_insert (m_fds model) fd
      (FdEntry.FdFile p (BitVec.ofInt 64 0))) model)
    (getr regs 17) (open_copyins (erec regs pc mem (seg_rom segs))) Te Ts U rfl Hh Hlazy
    ?_ ?_ ?_ ?_ HU
  · intro eff
    exact openat_rd_check segs (erec regs pc mem (seg_rom segs)) (getr regs 17) model p d
      H17 Hg0 Hpath' Hpe Hfl Hdot Hfs eff
  · intro fd
    exact ⟨by rw [with_fds_halted]; exact Hh, Hlazy⟩
  · intro e hmem
    simp only [erec, adv_eff_ret_copyins]
    exact Herr e hmem
  · intro fd hlk hlt
    simp only [erec, adv_eff_ret_copyins]
    exact Hok fd hlk hlt

/-- O_WRONLY|O_CREAT|O_TRUNC openat at the raw ecall record, with
    `to_fout_mix` continuations.  Like `FileSim.tfo_open_wr_rec` it is
    the create lane only — a plain name nothing lives under; the
    implied-directory lane (a deterministic -EISDIR) has no mix-flavoured
    node because no proof on this route reaches one. -/
theorem tfm_open_wr_rec (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem : word → Option byte) (model : Model) (p : Fs.path)
    (Te : Int → (word × Fs.Fs) → Prop) (Ts : word → (word × Fs.Fs) → Prop)
    (U : (word × Fs.Fs) → Prop)
    (H17 : ((getr regs 17).toNat : Int) = 56)
    (H10 : reg_get regs 10 = Sys.Uapi.AT_FDCWD)
    (H12 : reg_get regs 12 = BitVec.ofInt 64 577)
    (Hpath : read_cstr (mrb segs mem) (reg_get regs 11) = .CstrOk p)
    (Hpe : path_eqb p [] = false)
    (Hdot : Sys.Fs.Open.openat_plain_name p = true)
    (Hun : Sys.Fs.Open.fs_under (m_fs model) p = false)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = [])
    (Herr : ∀ e, e ∈ Sys.Fs.Open.openat_errnos →
       to_fout_mix segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem
         (seg_rom segs)) model (Te e))
    (Hok : ∀ fd, fd_lookup (m_fds model) fd = none → fd = alloc_fd (m_fds model) →
       to_fout_mix segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
         (with_fds (fd_insert (m_fds model) fd (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
            (with_fs (fs_set (m_fs model) p []) model)) (Ts fd))
    (HU : ∀ o, U o ↔
       ((∃ e, e ∈ Sys.Fs.Open.openat_errnos ∧ Te e o) ∨
        (∃ fd, fd_lookup (m_fds model) fd = none ∧ fd = alloc_fd (m_fds model)
           ∧ Ts fd o))) :
    to_fout_mix segs (erec regs pc mem (seg_rom segs)) model U := by
  have Hg0 : ms_gpr (erec regs pc mem (seg_rom segs)) 0 = Sys.Uapi.AT_FDCWD := by
    rw [erec_gpr_0]; exact H10
  have Hg1 : ms_gpr (erec regs pc mem (seg_rom segs)) 1 = reg_get regs 11 := erec_gpr_1 ..
  have Hg2 : ms_gpr (erec regs pc mem (seg_rom segs)) 2 = BitVec.ofInt 64 577 := by
    rw [erec_gpr_2]; exact H12
  have Hpath' : read_cstr (ms_read_byte (erec regs pc mem (seg_rom segs)))
      (ms_gpr (erec regs pc mem (seg_rom segs)) 1) = .CstrOk p := by
    rw [erec_read_byte, Hg1]
    exact Hpath
  have Hfl : Sys.Fs.File.z_ldiff ((ms_gpr (erec regs pc mem (seg_rom segs)) 2).toNat : Int)
      Sys.Fs.Open.open_ignored_flags = Sys.Fs.Open.wr_create_flags := by
    rw [Hg2]
    decide
  refine tfm_open_core segs (erec regs pc mem (seg_rom segs)) model
    (fun fd => with_fds (fd_insert (m_fds model) fd
      (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
      (with_fs (fs_set (m_fs model) p []) model))
    (getr regs 17) (open_copyins (erec regs pc mem (seg_rom segs))) Te Ts U rfl Hh Hlazy
    ?_ ?_ ?_ ?_ HU
  · intro eff
    exact openat_wr_check segs (erec regs pc mem (seg_rom segs)) (getr regs 17) model p
      H17 Hg0 Hpath' Hpe Hfl Hdot Hun eff
  · intro fd
    exact ⟨by rw [with_fds_halted, with_fs_halted]; exact Hh, Hlazy⟩
  · intro e hmem
    simp only [erec, adv_eff_ret_copyins]
    exact Herr e hmem
  · intro fd hlk hlt
    simp only [erec, adv_eff_ret_copyins]
    exact Hok fd hlk hlt

/- There is no PATHNAME-shaped error leaf: on a flag word the
    model interprets, every pathname `openat_spec` can be handed gets an
    answer — the string, a real -ENAMETOOLONG, or a real -EFAULT — so an
    `Unmodeled` leaf for a path that does not resolve would be false.
    The generic `tfm_unmodeled` leaf covers a branch that runs silently
    into ANY syscall whose spec is `Unmodeled` — an unmodeled dirfd, an
    unmodeled open-flag combination (which `openat_spec` declines
    BEFORE it fetches the path), an unmodeled syscall number.  Such a
    branch survives no outcome. -/

/- ===================================================================== -/
/- Run-level packaging and the equivalence glue.                       -/
/- ===================================================================== -/

/-- The trace set of a may-erroring file tree with a NONEMPTY surviving
    outcome set `U` is exactly the prefixes of `U`'s outcome traces (an
    erroring branch contributes only the empty trace, which is a prefix
    of every outcome trace). -/
theorem fout_mix_obs_iff (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (U : (word × Fs.Fs) → Prop)
    (Hto : to_fout_mix segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U)
    (Hne : ∃ o, U o) :
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  intro tr
  have Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = none := rfl
  have Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = [] := rfl
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    rcases tfm_star_only segs _ _ U Hto Hh Hlazy tr' c Hstar with rfl | ⟨o, Ho, Hp'⟩
    · obtain ⟨o, Ho⟩ := Hne
      refine ⟨o, Ho, ?_⟩
      cases tr with
      | nil => exact True.intro
      | cons _ _ => exact False.elim Hp
    · exact ⟨o, Ho, is_prefix_trans Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := tfm_star_admits segs _ _ U Hto Hh Hlazy o Ho
    exact ⟨fout_trace o, c, Hstar, Hp⟩

/-- The `Equivalence`-level glue: a MAY-erroring source file tree whose
    surviving outcome set is the (nonempty) `U`, against a
    never-erroring target realizing the SAME `U`.  The source escape is
    unavailable (some source resolution avoids error), so this
    discharges the non-escape disjunct of `equiv`: exact trace-set
    equality plus target no-error.

    `equiv` ONLY — see the `Equivalence.modeled` note in the header for
    why this combinator cannot close `strong_equiv` and why it
    nonetheless stays. -/
theorem file_mix_equiv_only
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (U : (word × Fs.Fs) → Prop) (inp : ProcInput)
    (Hsource : to_fout_mix source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U)
    (Hne : ∃ o, U o) :
    equiv (run (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩ inp)
          (run (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp) := by
  refine Or.inr ⟨?_, ?_⟩
  · intro tr
    exact (fout_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
        Hsource Hne tr).trans
      (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
  · exact fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

/-- The omni equivalence — the `equiv` conjunct ONLY, as for
    `file_mix_equiv_only`, and named the same way: the source's unmodeled
    leaf is a configuration `Run.unmodeled_at`, so `covered` is refuted
    there (`msteps_spec_err_not_covered`, `file_mix_unmodeled_leaf_not_covered`)
    rather than merely unproved. -/
theorem file_mix_omni_equiv_only
    (source_segs : List Segment) (rpc : Nat) (rph : PhdrInfo)
    (rsp rbrk rmb : word) (rrnd : EntryDraw) (rlim : Int)
    (target_segs : List Segment) (apc : Nat) (aph : PhdrInfo)
    (asp abrk amb : word) (arnd : EntryDraw) (alim : Int)
    (U : (word × Fs.Fs) → Prop) (inp : ProcInput)
    (Hsource : to_fout_mix source_segs
      (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U)
    (Htarget : to_fout target_segs
      (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid
        inp.in_hwcap)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) U)
    (Hne : ∃ o, U o) :
    omni_equiv (mkImage source_segs rpc rph) rlim ⟨rsp, rbrk, rmb, rrnd⟩
               (mkImage target_segs apc aph) alim ⟨asp, abrk, amb, arnd⟩ inp := by
  refine Or.inr ⟨?_, ?_⟩
  · refine (trace_equiv_iff_omni (mkImage source_segs rpc rph) rlim
      ⟨rsp, rbrk, rmb, rrnd⟩ (mkImage target_segs apc aph) alim
      ⟨asp, abrk, amb, arnd⟩ inp).mp ?_
    intro tr
    exact (fout_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U
        Hsource Hne tr).trans
      (fout_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
  · exact (bh_errors_iff (mkImage target_segs apc aph) alim
      ⟨asp, abrk, amb, arnd⟩ inp).mp
      (fout_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget)

/-- At run level: a source whose init line reaches a spec-`Unmodeled`
    syscall is not `covered`, whatever its outcome set -- so no
    `to_fout_mix` combinator can supply `omni_strong_equiv`'s first
    conjunct for it. -/
theorem file_mix_unmodeled_leaf_not_covered (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int) (inp : ProcInput)
    (ms' : machine_state) (x8 : word)
    (Hm : msteps segs
      (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      ms')
    (Hsvc : ms'.ms_svc_pending = some x8)
    (Herr : Specs.syscall_spec (sys_input segs ms' x8)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) .unmodeled) :
    ¬ omni_corun (mkImage segs pc ph) lim ⟨sp, brk0, mb, rnd⟩ inp (covered segs) := by
  show ¬ OmniRun.coexec segs (init_config segs pc ph sp brk0 mb rnd lim inp) (covered segs)
  exact msteps_spec_err_not_covered segs _ ms'
    (init_model (segments_reserved segs) brk0 mb sp lim inp) x8 rfl rfl Hm Hsvc Herr

end LinuxSem.Common.FileMixSim
