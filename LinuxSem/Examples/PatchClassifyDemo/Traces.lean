/-
  * Examples.PatchClassifyDemo.Traces — the COMPLETE trace set of each
    demo program, at every valid entry and on every input

  DEMO FILE (not part of the trusted specification).  `Images` defines
  the demo's six images and `Verdicts` proves that each of them
  terminates with a known exit status wherever it is launched.  This
  file proves the sharper fact the three behavioral obligations
  actually need: what the trace set IS, exactly, rather than what it
  contains.

  ** Why the verdicts are not enough

  `MustExit.must_exit_with` is a claim about how every execution ENDS.
  `MustExit.must_exit_with_realizes` turns it into an existence
  statement — SOME observable trace ends in `State.ExitEv` carrying the
  code — and that is a lower bound on the trace set.  Every obligation
  below needs an UPPER bound as well:

  - `Equivalence.strong_universal_T` needs `Equivalence.trace_equiv`,
    set EQUALITY of the two finite-prefix sets.  Two lower bounds do
    not make an equality: knowing that each of two programs emits its
    exit event says nothing about whether one of them also emits
    something the other does not.
  - Refuting `Classifier.agree` means showing a trace of one program is
    NOT a trace of the other, which is a claim about what the second
    one does not do.  The verdicts' four error/modeled facts close
    every other route: they make `Classifier.agree`'s second, third and
    fourth conjuncts HOLD of the pair (`O1`, `P1`) — both sides fail
    all three antecedents — so the refutation has nowhere to go but the
    trace conjunct.
  - `Classifier.good_input` is `Equivalence.strong_equiv_error_free`,
    which is error-freedom of both sides plus
    `Equivalence.trace_equiv`.  Both originals here ARE error-free, so
    again only the trace conjunct can fail.

  ** The statement, and why it has the shape it has

  `O1_traces` below: the trace set of one of these runs is exactly

      [{ []; [ExitEv code (in_fs inp)] }]

  — an iff, not an inclusion either way.  Three things about the shape
  are worth reading off it.

  The set is CLOSED UNDER PREFIX and contains the empty trace, because
  `Run.obs_trace` is defined that way (`Run.obs_trace_nil`,
  `Run.obs_trace_prefix_closed`); the empty trace is therefore in the
  set of every run whatever, and a characterization that omitted it
  would be false.

  The exit event's payload is `State.in_fs inp` and not a variable:
  `Run.sstep_exit` emits `State.m_fs` of the POST-model, the exit spec
  changes the model only through `State.with_halted`
  (`State.m_fs_with_halted` carries the file system across it), and the
  initial model's file system is the input's
  (`State.m_fs_init_model`).  These programs issue no other syscall, so
  the file system a waiting parent would see is the one the process was
  launched with.  Naming it is what makes the two sides of a
  `Equivalence.trace_equiv` between two such runs literally the same
  set rather than two sets that would have to be related.

  Nothing else is emitted.  The run is four transitions: three
  `Run.sstep_instr`s, which emit `[]` by construction — the two
  `addi`s and the `ecall` INSTRUCTION, which only records the pending
  syscall number and does not advance the pc — and then the one
  `Run.sstep_exit`.  That transition's own event list is forced empty
  by `exit_dispatch_forced`, since the exit spec has no `Monad.choose`
  in it and its outcome triple is therefore unique.

  ** What the premise excludes, which is most programs

  The hypothesis is `Checks.Examples.exits_c` reaching `true` with the
  stack pointer, the writable memory and the read-only backing left as
  VARIABLES — the same premise `Verdicts.must_exit_everywhere_of_exits_c`
  takes, and the same class of programs.  Said the other way round:
  this characterization covers exactly the programs that IGNORE their
  input.  A program that READ its standard input would leave the
  reduction stuck on a variable, so the premise could not be discharged
  for it at all, and its trace set would not be a fixed two-element set
  in the first place — `State.in_fs inp` is the only way the input
  reaches the conclusion here.

  That is the demo's honest limit, and it is where the follow-up the
  demo's README names begins: an input-reading refinement needs a
  SIMULATION argument relating the program's reads to the stream,
  rather than a computation with the input abstracted away.

  ** How it is proved here: the run is four forced transitions

  One engine is `exits_c_star_trace`, an induction on the fuel of
  `exits_c` run in parallel with an inversion of the `Run.star`, exactly
  as `exits_c_must_exit_at` runs the same induction against
  `MustExit.must_exit_at`.  It reaches an upper bound on the accumulated
  trace of any `Run.star`, which is the half `MustExit` cannot give.

  ** Which engine this file uses, and why BOTH are here

  `exits_c_star_trace` is proved at the end of this file, on top of
  `exits_c`, which is one module down in `Verdicts`/`ExitsC`.  It is the
  general engine: it holds at every image that `exits_c` accepts, which
  is what `exits_c_trace_characterization` needs.

  The bound below is a SECOND proof of the same thing for the demo's six
  images, from the run's SHAPE, and it needs no computation — only the
  two facts the program's structure forces:

  - `sstep_instr_unique`: at a configuration whose `ms_svc_pending` is
    `none`, the only `Run.sstep` is the instruction one.  It emits `[]`
    and leaves the model FIXED (`Run.mi_account_step_no_lazy`), which
    is what keeps `m_fs model` in the conclusion alive across the step.
    This is the inversion `Verdicts.must_exit_at_instr` writes twice.
  - `exit_step_forced`: at an `ecall` carrying the exit number the only
    surviving successor is the exit transition — an ordinary syscall
    would have to run on from a halted model, the unmodeled arm is
    forbidden by the exit spec, and the kill arm by the exit spec's
    `m_killed = none`.  That transition emits exactly
    `[ExitEv (ms_gpr ms 0 &&& 255) (m_fs model)]` and halts.

  `star_trace_four` then walks the `Run.star` four cases deep — three
  instruction steps, then the exit step — and `star_from_halted` ends
  it at the halted configuration.  `O1_run_upper`/`O2_run_upper`
  instantiate that engine at each program's own three step lemmas
  (`Verdicts.O1_step_*` and `Verdicts.exit0_step_*`), which is the only
  place the encodings enter; that is why the bound holds at EVERY entry
  and on EVERY input.

  The lower half is then FREE:
  `MustExit.must_exit_with_realizes` already produces a `Run.star`
  whose trace ends in the exit event, and the upper bound identifies
  that trace with the singleton.  So no execution is ever built by
  hand here either.
-/
import LinuxSem.Examples.PatchClassifyDemo.Verdicts
import LinuxSem.Examples.PatchClassifyDemo.ExitsC

/- `autoImplicit` is off for this file: a bare structure-field name would
   otherwise silently become an implicitly bound variable, which in a
   STATEMENT is a weakened claim rather than a compile error. -/
set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Bridge.Exit
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Classifier

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Traces

open Images
open Verdicts

/- =========================================================================
   Two shapes of list equation, once
   ========================================================================= -/

/-- A singleton `State.ExitEv` trace determines its code.  Stated as a
    lemma rather than inlined at each use because it is where the
    refutations below actually bite: an `Classifier.agree` that survived
    would have to make `Classifier.verdict_accept` and
    `Classifier.verdict_reject` the same word, which
    `Classifier.verdict_accept_neq_reject` forbids. -/
theorem exit_singleton_code (c1 c2 : word) (fs1 fs2 : Fs.Fs)
    (h : [event.ExitEv c1 fs1] = [event.ExitEv c2 fs2]) : c1 = c2 := by
  have h' : event.ExitEv c1 fs1 = event.ExitEv c2 fs2 := by simpa using h
  injection h' with hc _

/-- `Run.is_prefix` of a singleton leaves only the two traces the
    characterization names.  `Run.obs_trace` is prefix-closed, so this
    is the step from "the maximal trace is the singleton" to "the trace
    SET is the two-element set". -/
theorem is_prefix_singleton {A : Type} (x : A) (l : List A)
    (h : is_prefix l [x]) : l = [] ∨ l = [x] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons y tl =>
      cases tl with
      | nil =>
          simp only [is_prefix] at h
          exact Or.inr (by rw [h.1])
      | cons z t =>
          simp only [is_prefix] at h
          exact absurd h.2 (by simp)

/- =========================================================================
   One step out of a configuration whose pending syscall is `exit`
   ========================================================================= -/

theorem sstep_instr_unique (segs : List Segment) (ms ms1 : machine_state)
    (model : Model) (evs : List event) (c' : config)
    (hsvc : ms.ms_svc_pending = none)
    (hstep : mi_account_step segs ms model = .MachineOk (ms1, model))
    (hss : sstep segs ⟨ms, model⟩ evs (.SNext c')) :
    evs = [] ∧ c' = ⟨ms1, model⟩ := by
  cases hss with
  | instr ms0 model0 ms1' model1' hh0 hsvc0 hstep' =>
      rw [hstep] at hstep'
      obtain ⟨rfl, rfl⟩ := machine_result.MachineOk.inj hstep'
      exact ⟨rfl, rfl⟩
  | _ => simp_all

theorem exit_step_forced (segs : List Segment) (ms : machine_state) (model : Model)
    (x8p : word) (evs : List event) (c' : config)
    (_hh : m_halted model = none)
    (hsvc : ms.ms_svc_pending = some x8p)
    (hno : exit_number (sys_input segs ms x8p).in_sysno)
    (hss : sstep segs ⟨ms, model⟩ evs (.SNext c')) :
    evs = [event.ExitEv (ms_gpr ms 0 &&& BitVec.ofInt 64 255) (m_fs model)]
      ∧ m_halted c'.cfg_model ≠ none := by
  have hhalt : ∀ (eff : SyscallEffect) (m' : Model) (es : List event),
      syscall_spec (sys_input segs ms x8p) model (.ok eff m' es) →
      m_halted m' = some (ms_gpr ms 0 &&& BitVec.ofInt 64 255) := by
    intro eff m' es hs
    rw [exit_outcome_halts _ model m' eff es hno hs, sys_input_arg0]
  have hnk : ∀ (eff : SyscallEffect) (m' : Model) (es : List event),
      syscall_spec (sys_input segs ms x8p) model (.ok eff m' es) → m_killed m' = none := by
    intro eff m' es hs; exact exit_outcome_not_killed _ model m' eff es hno hs
  have hnu : ¬ syscall_spec (sys_input segs ms x8p) model .unmodeled :=
    exit_spec_not_unmodeled _ _ hno
  cases hss
  case instr => simp_all
  case syscall => grind
  case killed => grind
  case exit =>
    rename_i x8_1 eff_1 model'_1 evs_1 code_1 hh'_1 hk_1 hh_2 hsvc_1 hspec_1
    have hx : x8_1 = x8p := Option.some.inj (hh_2.symm.trans hsvc)
    subst x8_1
    have hevs : evs_1 = [] :=
      exit_outcome_evs (sys_input segs ms x8p) model model'_1 eff_1 evs_1 hno hspec_1
    have hmodel : model'_1 = with_halted
        (in_arg (sys_input segs ms x8p) 0 &&& BitVec.ofInt 64 255) model :=
      exit_outcome_model _ model model'_1 eff_1 evs_1 hno hspec_1
    have hcode : code_1 = in_arg (sys_input segs ms x8p) 0 &&& BitVec.ofInt 64 255 :=
      Option.some.inj (hh'_1.symm.trans (exit_outcome_halts _ model model'_1 eff_1 evs_1 hno hspec_1))
    refine ⟨?_, ?_⟩
    · rw [hevs, List.nil_append, hcode, hmodel, m_fs_with_halted, sys_input_arg0]
    · rw [hmodel, m_halted_with_halted]
      exact Option.some_ne_none _

/-- THE ENGINE.  A run of the demo's four-transition program emits `[]` or
    exactly the one exit event: three instruction steps, each of which is
    the unique successor of its configuration and emits nothing, then the
    exit step, which halts. -/
theorem star_trace_four (segs : List Segment) (code : word)
    (st ms1 ms2 ms3 : machine_state) (model : Model) (x8 : word)
    (hsvc0 : st.ms_svc_pending = none)
    (e1 : mi_account_step segs st model = .MachineOk (ms1, model))
    (hsvc1 : ms1.ms_svc_pending = none)
    (e2 : mi_account_step segs ms1 model = .MachineOk (ms2, model))
    (hsvc2 : ms2.ms_svc_pending = none)
    (e3 : mi_account_step segs ms2 model = .MachineOk (ms3, model))
    (hsvc3 : ms3.ms_svc_pending = some x8)
    (hh : m_halted model = none)
    (hno : exit_number (sys_input segs ms3 x8).in_sysno)
    (hcode : ms_gpr ms3 0 &&& BitVec.ofInt 64 255 = code) :
    ∀ (tr : List event) (c' : config),
      star segs ⟨st, model⟩ tr c' → tr = [] ∨ tr = [event.ExitEv code (m_fs model)] := by
  intro tr c' hstar
  cases hstar with
  | refl => exact Or.inl rfl
  | step c1 evs c2 tr1 c3 hss htail =>
    obtain ⟨rfl, hc2⟩ := sstep_instr_unique segs st ms1 model evs c2 hsvc0 e1 hss
    subst c2
    cases htail with
    | refl => exact Or.inl (by simp)
    | step c1' evs' c2' tr2 c3' hss' htail' =>
      obtain ⟨rfl, hc2'⟩ := sstep_instr_unique segs ms1 ms2 model evs' c2' hsvc1 e2 hss'
      subst c2'
      cases htail' with
      | refl => exact Or.inl (by simp)
      | step c1'' evs'' c2'' tr3 c3'' hss'' htail'' =>
        obtain ⟨rfl, hc2''⟩ := sstep_instr_unique segs ms2 ms3 model evs'' c2'' hsvc2 e3 hss''
        subst c2''
        cases htail'' with
        | refl => exact Or.inl (by simp)
        | step c1''' evs''' c2''' tr4 c4 hss''' htail''' =>
          obtain ⟨hevs, hhalt⟩ := exit_step_forced segs ms3 model x8 evs''' c2''' hh hsvc3 hno hss'''
          obtain ⟨rfl, -⟩ := star_from_halted segs _ tr4 _ htail''' hhalt
          refine Or.inr ?_
          simp only [List.nil_append, List.append_nil, hevs, hcode]

theorem O1_run_upper (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (tr : List event) (c' : config)
    (h : star O1m.loaded_segments
      (init_config O1m.loaded_segments O1m.init_pc O1m.phdrs en.en_sp en.en_brk
        en.en_mmap_base en.en_draw lim inp) tr c') :
    tr = [] ∨ tr = [event.ExitEv verdict_reject (in_fs inp)] := by
  obtain ⟨mem, rom, hshape⟩ := init_machine_state_abstracts O1m.loaded_segments
    O1m.init_pc O1m.phdrs en.en_sp en.en_draw inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  obtain ⟨ms1, h1, hpc1, hsvc1, ha7⟩ := O1_step_a7 (demo_init_state O1m.init_pc en.en_sp mem rom) rfl
  obtain ⟨ms2, h2, hpc2, hsvc2, ha0, ha7'⟩ := O1_step_a0 ms1 hpc1
  obtain ⟨ms3, h3, hsvc3, ha0'⟩ := O1_step_ecall ms2 hpc2
  have hh : m_halted (init_model (segments_reserved O1m.loaded_segments)
      en.en_brk en.en_mmap_base en.en_sp lim inp) = none := m_halted_init_model _ _ _ _ _ _
  have hlazy : m_vm_lazy (init_model (segments_reserved O1m.loaded_segments)
      en.en_brk en.en_mmap_base en.en_sp lim inp) = [] := init_model_no_lazy _ _ _ _ _ _
  have e1 : mi_account_step O1m.loaded_segments (demo_init_state O1m.init_pc en.en_sp mem rom)
      (init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms1, init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h1]
  have e2 : mi_account_step O1m.loaded_segments ms1
      (init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms2, init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h2]
  have e3 : mi_account_step O1m.loaded_segments ms2
      (init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms3, init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h3]
  have hx8 : ms_reg ms2 17 = BitVec.ofInt 64 93 := by rw [ha7', ha7]
  have hno : exit_number (sys_input O1m.loaded_segments ms3 (ms_reg ms2 17)).in_sysno := by
    show ((ms_reg ms2 17).toNat : Int) = 93 ∨ ((ms_reg ms2 17).toNat : Int) = 94
    rw [hx8]; left; rfl
  have hcode : ms_gpr ms3 0 &&& BitVec.ofInt 64 255 = verdict_reject := by
    rw [ha0', ha0]; rfl
  have hcfg : init_config O1m.loaded_segments O1m.init_pc O1m.phdrs en.en_sp en.en_brk
      en.en_mmap_base en.en_draw lim inp
      = ⟨demo_init_state O1m.init_pc en.en_sp mem rom,
         init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp⟩ := by
    simp only [init_config, hshape]
  rw [hcfg] at h
  have hup := star_trace_four O1m.loaded_segments verdict_reject
    (demo_init_state O1m.init_pc en.en_sp mem rom) ms1 ms2 ms3
    (init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
    (ms_reg ms2 17) rfl e1 hsvc1 e2 hsvc2 e3 hsvc3 hh hno hcode tr c' h
  rwa [m_fs_init_model (segments_reserved O1m.loaded_segments) en.en_brk en.en_mmap_base en.en_sp lim inp] at hup


/-- THE CHARACTERIZATION, for the exit-1 family: the trace set of the run is
    exactly the two-element set.  Forward by the engine; backward the empty
    trace is `obs_trace_nil` and the singleton is the execution
    `must_exit_with_realizes` already produces, identified with the
    singleton by the upper bound. -/
theorem O1_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run O1_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_reject (in_fs inp)]) := by
  constructor
  · rintro ⟨tr, c, hstar, hpre⟩
    have hup := O1_run_upper lim en inp tr c hstar
    rcases hup with hnil | hone
    · rw [hnil] at hpre
      cases t with
      | nil => exact Or.inl rfl
      | cons e es => simp [is_prefix] at hpre
    · rw [hone] at hpre
      rcases is_prefix_singleton _ _ hpre with h | h
      · exact Or.inl h
      · exact Or.inr h
  · rintro (rfl | rfl)
    · exact obs_trace_nil _ _
    · obtain ⟨tr0, fs, htr⟩ := O1_realizes_exit_one lim en inp
      obtain ⟨tr', c, hstar, hpre⟩ := htr
      have hup := O1_run_upper lim en inp tr' c hstar
      rcases hup with hnil | hone
      · rw [hnil] at hpre
        cases tr0 with
        | nil => simp [is_prefix] at hpre
        | cons x xs => simp [is_prefix] at hpre
      · rw [hone] at hstar
        exact ⟨_, c, hstar, is_prefix_refl _⟩
theorem O2_run_upper (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (tr : List event) (c' : config)
    (h : star exit0_image_segments
      (init_config exit0_image_segments O2m.init_pc O2m.phdrs en.en_sp en.en_brk
        en.en_mmap_base en.en_draw lim inp) tr c') :
    tr = [] ∨ tr = [event.ExitEv verdict_accept (in_fs inp)] := by
  obtain ⟨mem, rom, hshape⟩ := init_machine_state_abstracts exit0_image_segments
    O2m.init_pc O2m.phdrs en.en_sp en.en_draw inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  obtain ⟨ms1, h1, hpc1, hsvc1, ha7⟩ := exit0_step_a7 (demo_init_state O2m.init_pc en.en_sp mem rom) rfl
  obtain ⟨ms2, h2, hpc2, hsvc2, ha0, ha7'⟩ := exit0_step_a0 ms1 hpc1
  obtain ⟨ms3, h3, hsvc3, ha0'⟩ := exit0_step_ecall ms2 hpc2
  have hh : m_halted (init_model (segments_reserved exit0_image_segments)
      en.en_brk en.en_mmap_base en.en_sp lim inp) = none := m_halted_init_model _ _ _ _ _ _
  have hlazy : m_vm_lazy (init_model (segments_reserved exit0_image_segments)
      en.en_brk en.en_mmap_base en.en_sp lim inp) = [] := init_model_no_lazy _ _ _ _ _ _
  have e1 : mi_account_step exit0_image_segments (demo_init_state O2m.init_pc en.en_sp mem rom)
      (init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms1, init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h1]
  have e2 : mi_account_step exit0_image_segments ms1
      (init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms2, init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h2]
  have e3 : mi_account_step exit0_image_segments ms2
      (init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
      = .MachineOk (ms3, init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp) := by
    rw [mi_account_step_no_lazy _ _ _ hlazy, h3]
  have hx8 : ms_reg ms2 17 = BitVec.ofInt 64 93 := by rw [ha7', ha7]
  have hno : exit_number (sys_input exit0_image_segments ms3 (ms_reg ms2 17)).in_sysno := by
    show ((ms_reg ms2 17).toNat : Int) = 93 ∨ ((ms_reg ms2 17).toNat : Int) = 94
    rw [hx8]; left; rfl
  have hcode : ms_gpr ms3 0 &&& BitVec.ofInt 64 255 = verdict_accept := by
    rw [ha0', ha0]; rfl
  have hcfg : init_config exit0_image_segments O2m.init_pc O2m.phdrs en.en_sp en.en_brk
      en.en_mmap_base en.en_draw lim inp
      = ⟨demo_init_state O2m.init_pc en.en_sp mem rom,
         init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp⟩ := by
    simp only [init_config, hshape]
  rw [hcfg] at h
  have hup := star_trace_four exit0_image_segments verdict_accept
    (demo_init_state O2m.init_pc en.en_sp mem rom) ms1 ms2 ms3
    (init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp)
    (ms_reg ms2 17) rfl e1 hsvc1 e2 hsvc2 e3 hsvc3 hh hno hcode tr c' h
  rwa [m_fs_init_model (segments_reserved exit0_image_segments) en.en_brk en.en_mmap_base en.en_sp lim inp] at hup


/-- THE CHARACTERIZATION, for the exit-0 family: the trace set of the run is
    exactly the two-element set.  Forward by the engine; backward the empty
    trace is `obs_trace_nil` and the singleton is the execution
    `must_exit_with_realizes` already produces, identified with the
    singleton by the upper bound. -/
theorem O2_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run O2_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_accept (in_fs inp)]) := by
  constructor
  · rintro ⟨tr, c, hstar, hpre⟩
    have hup := O2_run_upper lim en inp tr c hstar
    rcases hup with hnil | hone
    · rw [hnil] at hpre
      cases t with
      | nil => exact Or.inl rfl
      | cons e es => simp [is_prefix] at hpre
    · rw [hone] at hpre
      rcases is_prefix_singleton _ _ hpre with h | h
      · exact Or.inl h
      · exact Or.inr h
  · rintro (rfl | rfl)
    · exact obs_trace_nil _ _
    · obtain ⟨tr0, fs, htr⟩ := must_exit_with_realizes verdict_accept O2_image lim en inp (O2_must_exit_zero lim en inp)
      obtain ⟨tr', c, hstar, hpre⟩ := htr
      have hup := O2_run_upper lim en inp tr' c hstar
      rcases hup with hnil | hone
      · rw [hnil] at hpre
        cases tr0 with
        | nil => simp [is_prefix] at hpre
        | cons x xs => simp [is_prefix] at hpre
      · rw [hone] at hstar
        exact ⟨_, c, hstar, is_prefix_refl _⟩


/- =========================================================================
   The other four images
   ========================================================================= -/

/-! `P1m`/`P2m` are the same `MemImage` as `O2m` and `C1m`/`C2m` the same as
    `O1m` (the demo's six names are six obligations over two programs), so
    these four are transports — each stated of its own image, as
    `PatchClassifySpec` ascribes them. -/

theorem P1_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run P1_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_accept (in_fs inp)]) :=
  O2_traces lim en inp t

theorem P2_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run P2_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_accept (in_fs inp)]) :=
  O2_traces lim en inp t

theorem C1_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run C1_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_reject (in_fs inp)]) :=
  O1_traces lim en inp t

theorem C2_traces (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event) :
    bh_traces (run C2_image lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv verdict_reject (in_fs inp)]) :=
  O1_traces lim en inp t

/-- The one-line consequence every refutation below runs through: a
    program that exits 0 never emits the exit-1 event.  Without a
    statement of this shape the characterization would be a description
    with nothing depending on it — and it is exactly the fact
    `MustExit.must_exit_with_realizes` cannot supply, since an existence
    statement about one program says nothing about a second. -/
theorem no_exit_one_trace_of_exit_zero (X : Image)
    (HX : ∀ (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event),
      bh_traces (run X lim en inp) t
        ↔ (t = [] ∨ t = [event.ExitEv verdict_accept (in_fs inp)]))
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_traces (run X lim en inp) [event.ExitEv verdict_reject (in_fs inp)] := by
  intro ht
  have h := (HX lim en inp _).mp ht
  rcases h with he | he
  · exact absurd he (by simp)
  · exact verdict_accept_neq_reject
      (exit_singleton_code _ _ _ _ he).symm

/-- ... and its mirror, so that no refutation depends on which of the
    two codes the defective image happens to report. -/
theorem no_exit_zero_trace_of_exit_one (X : Image)
    (HX : ∀ (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event),
      bh_traces (run X lim en inp) t
        ↔ (t = [] ∨ t = [event.ExitEv verdict_reject (in_fs inp)]))
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_traces (run X lim en inp) [event.ExitEv verdict_accept (in_fs inp)] := by
  intro ht
  have h := (HX lim en inp _).mp ht
  rcases h with he | he
  · exact absurd he (by simp)
  · exact verdict_accept_neq_reject (exit_singleton_code _ _ _ _ he)

/- =========================================================================
   The characterization bites
   ========================================================================= -/


/-! The positive half: the exit event really is emitted, so the
    characterization is not the trace set of a program that says
    nothing.  `Verdicts.O1_realizes_exit_one` makes the same point from
    `MustExit.must_exit_with_realizes`; this one pins the trace exactly,
    payload included. -/
theorem O1_emits_exactly_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    bh_traces (run O1_image lim en inp) [event.ExitEv verdict_reject (in_fs inp)] :=
  (O1_traces lim en inp _).mpr (Or.inr rfl)

theorem P1_emits_exactly_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    bh_traces (run P1_image lim en inp) [event.ExitEv verdict_accept (in_fs inp)] :=
  (P1_traces lim en inp _).mpr (Or.inr rfl)

/-- And the exclusion, on the demo's own images: the defect's exit-1 trace
    is not a trace of its patch.  This is the single fact the
    `Classifier.agree` refutation is built from. -/
theorem P1_never_emits_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_traces (run P1_image lim en inp) [event.ExitEv verdict_reject (in_fs inp)] :=
  no_exit_one_trace_of_exit_zero P1_image P1_traces lim en inp

theorem O2_never_emits_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_traces (run O2_image lim en inp) [event.ExitEv verdict_reject (in_fs inp)] :=
  no_exit_one_trace_of_exit_zero O2_image O2_traces lim en inp

theorem O1_never_emits_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ bh_traces (run O1_image lim en inp) [event.ExitEv verdict_accept (in_fs inp)] :=
  no_exit_zero_trace_of_exit_one O1_image O1_traces lim en inp

/-! =========================================================================
   The `exits_c` engine, and the characterization built on it
   ========================================================================= -/

/-- ** The upper bound on a run whose machine starts `exits_c`-true.**

  The `exits_c` twin of [O1_run_upper]: at every fuel level either a
  syscall is already pending — and then the exit transition is the ONLY
  successor, which emits the one event — or it is not, and the
  instruction transition is the only successor, emits nothing and leaves
  the model fixed, so the induction goes through.

    The two inversions it consumes are the ones this file already has:
    [sstep_instr_unique] and [exit_step_forced].  Nothing is computed —
    `exits_c` is a hypothesis at every level, which is why the bound holds
    at EVERY entry and on EVERY input. -/
theorem exits_c_star_trace (segs : List Segment) (code : word) :
    ∀ (fuel : Nat) (ms : machine_state) (model : Model) (tr : List event) (c' : config),
      m_halted model = none → m_vm_lazy model = [] →
      exits_c segs code fuel ms = true →
      star segs ⟨ms, model⟩ tr c' →
      tr = [] ∨ tr = [event.ExitEv code (m_fs model)] := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms model tr c' _ _ h _
      simp only [exits_c] at h
      exact absurd h (by simp)
  | succ n ih =>
      intro ms model tr c' hh hlazy h hstar
      cases hp : ms.ms_svc_pending with
      | some x8 =>
          have h' : ((decide ((x8.toNat : Int) = 93) || decide ((x8.toNat : Int) = 94))
              && ((ms_gpr ms 0 &&& BitVec.ofInt 64 255) == code)) = true := by
            simpa only [exits_c, hp] using h
          rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
            decide_eq_true_eq, beq_iff_eq] at h'
          obtain ⟨hno, hcode⟩ := h'
          cases hstar with
          | refl => exact Or.inl rfl
          | step c1 evs c2 tr1 c3 hss htail =>
              obtain ⟨hevs, hhalt⟩ :=
                exit_step_forced segs ms model x8 evs c2 hh hp hno hss
              obtain ⟨rfl, -⟩ := star_from_halted segs c2 tr1 c' htail hhalt
              refine Or.inr ?_
              rw [hevs, hcode, List.append_nil]
      | none =>
          cases hstep : RiscvSemantics.step segs ms with
          | MachineOk ms' =>
              have hrec : exits_c segs code n ms' = true := by
                simp only [exits_c, hp, hstep] at h
                exact h
              have hacc : mi_account_step segs ms model = .MachineOk (ms', model) := by
                rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
              cases hstar with
              | refl => exact Or.inl rfl
              | step c1 evs c2 tr1 c3 hss htail =>
                  obtain ⟨rfl, hc2⟩ :=
                    sstep_instr_unique segs ms ms' model evs c2 hp hacc hss
                  subst hc2
                  exact ih ms' model tr1 c' hh hlazy hrec htail
          | MachineFault =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)
          | MachineUnmodeled =>
              simp only [exits_c, hp, hstep] at h
              exact absurd h (by simp)

/-- The upper bound at a RUN's own initial configuration: the trace of
    every execution of the image is `[]` or the one exit event.  Stated
    apart from [exits_c_star_trace] because it is where the three
    abstraction facts are spent (`init_machine_state_abstracts` for the
    machine, `m_halted_init_model` / `init_model_no_lazy` for the model,
    `m_fs_init_model` for the payload), and both directions of the
    characterization use it. -/
theorem run_upper_of_exits_c (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (code : word) (fuel : Nat)
    (H : ∀ sp mem rom, exits_c segs code fuel (demo_init_state pc sp mem rom) = true)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) (tr : List event) (c' : config)
    (h : star segs
      (init_config segs pc ph en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c') :
    tr = [] ∨ tr = [event.ExitEv code (in_fs inp)] := by
  obtain ⟨mem, rom, hshape⟩ := init_machine_state_abstracts segs pc ph en.en_sp en.en_draw
    inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap
  have hcfg : init_config segs pc ph en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp
      = ⟨demo_init_state pc en.en_sp mem rom,
         init_model (segments_reserved segs) en.en_brk en.en_mmap_base en.en_sp lim inp⟩ := by
    simp only [init_config, hshape]
  rw [hcfg] at h
  have hup := exits_c_star_trace segs code fuel (demo_init_state pc en.en_sp mem rom)
    (init_model (segments_reserved segs) en.en_brk en.en_mmap_base en.en_sp lim inp) tr c'
    (m_halted_init_model _ _ _ _ _ _) (init_model_no_lazy _ _ _ _ _ _) (H _ mem rom) h
  rwa [m_fs_init_model (segments_reserved segs) en.en_brk en.en_mmap_base en.en_sp lim inp] at hup

/-- ** The characterization for an `exits_c`-verified image.**

  Given that `exits_c` accepts the image at EVERY stack pointer, memory
  and backing — the premise the demo's six verdicts discharge — the
  trace set of a run is exactly `{[], [ExitEv code (in_fs inp)]}`.

    FORWARD is the upper bound above plus `Run.is_prefix` on a singleton.
    BACKWARD is `must_exit_with_realizes`: `exits_c` is sound for
    `MustExit` (`ExitsC.must_exit_everywhere_of_exits_c`), so an execution
    reaching the exit event EXISTS, and the upper bound identifies its
    trace with the singleton — the same two-step `O1_traces`/`O2_traces`
    take at their own images, at an arbitrary one. -/
theorem exits_c_trace_characterization (segs : List Segment) (pc : Nat) (ph : PhdrInfo)
    (code : word) (fuel : Nat)
    (H : ∀ sp mem rom, exits_c segs code fuel (demo_init_state pc sp mem rom) = true) :
    ∀ (lim : Int) (en : ExecEntry) (inp : ProcInput) (t : List event),
      bh_traces (run (mkImage segs pc ph) lim en inp) t
      ↔ (t = [] ∨ t = [event.ExitEv code (in_fs inp)]) := by
  intro lim en inp t
  constructor
  · rintro ⟨tr, c, hstar, hpre⟩
    have hup := run_upper_of_exits_c segs pc ph code fuel H lim en inp tr c hstar
    rcases hup with hnil | hone
    · rw [hnil] at hpre
      cases t with
      | nil => exact Or.inl rfl
      | cons e es => simp [is_prefix] at hpre
    · rw [hone] at hpre
      rcases is_prefix_singleton _ _ hpre with h | h
      · exact Or.inl h
      · exact Or.inr h
  · rintro (rfl | rfl)
    · exact obs_trace_nil _ _
    · obtain ⟨tr0, fs, htr⟩ :=
        must_exit_with_realizes code (mkImage segs pc ph) lim en inp
          (must_exit_everywhere_of_exits_c segs pc ph code fuel H lim en inp)
      obtain ⟨tr', c, hstar, hpre⟩ := htr
      have hup := run_upper_of_exits_c segs pc ph code fuel H lim en inp tr' c hstar
      rcases hup with hnil | hone
      · rw [hnil] at hpre
        cases tr0 with
        | nil => simp [is_prefix] at hpre
        | cons x xs => simp [is_prefix] at hpre
      · rw [hone] at hstar
        exact ⟨_, c, hstar, is_prefix_refl _⟩

end Traces

end LinuxSem.Examples.PatchClassifyDemo
