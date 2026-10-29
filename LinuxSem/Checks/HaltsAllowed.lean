/-
  * LinuxSem.Checks.HaltsAllowed — the allowed-exit statement, fired

  Not part of the trusted specification: this file is QA on the
  definitions, in the sense [Checks/Examples] describes.  It exists
  so that [EquivalenceDefinition.HaltsAllowed]'s statement family is
  not a family of claims nobody has met or refused.

  WHY IT IS HERE AND NOT UNDER [Checks/Cases/].  The [Cases/] tree is
  the per-arm certificate tree and [Checks.Examples] imports all of it,
  so a [Cases/] file cannot import [Checks.Examples] — the dependency
  runs the other way.  The fixtures this file needs are exactly
  [Checks.Examples]'s images and [Checks.AbortWitness]'s killed run, so
  it sits beside [Checks.AbortWitness] and [Checks.SpuriousCfg], which
  hold the other statement-level witnesses for the same reason.

  ** What is pinned, and why each one

  THE POSITIVE HALF is what separates a demanding statement from an
  empty one.  [halts_allowed_T] is a [forall] over entries and inputs
  with four things to rule out at once, and nothing here would have
  noticed if no image met it.  [exit0_halts_allowed_zero] is a
  concrete image that does, at every valid entry and on every valid
  input rather than at one fixture pair — which matters, because the
  quantifier is the statement and a witness at one entry would leave
  the statement's own shape untested.

  THE NEGATIVE HALVES are the two routes out.  The error route fires
  at statement level: the undecodable image leaves the modeled surface
  on its first fetch, at a VALID entry and on a VALID input, so
  [halts_allowed_T] is refused for it at every allowed set.

  THE SIGNAL ROUTE IS FIRED ONE LEVEL DOWN, AND THAT IS A FACT ABOUT
  THE INPUT CLASS RATHER THAN A GAP HERE.  [Run.valid_input] pins
  [State.in_abort_terminal] to [false], and with the declaration off
  [Kernel.Signal.tkill_spec] declines every call, so no run this
  statement quantifies over can reach a [State.KillEv] at all
  ([Run.sstep_off_no_kill]).  The kill conjunct of
  [MustExit.must_exit_in_at] is therefore a GUARD over this input
  class, not a live refutation of [halts_allowed_T]: it is what keeps
  the predicate honest if the statement is ever issued over an input
  class that admits the declaration.  So the refutation is fired where
  it can be — against [MustExit.must_exit_in] on
  [Checks.AbortWitness]'s killed run — and
  [abrt_input_not_valid_input] pins the reason it stops there, so a
  reader does not take the missing statement-level refutation for an
  oversight.  Without that pin this file would look like it had simply
  failed to state one.

  Spelling.

  `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `bv_and` is `&&&`, `In` is
  [List.Mem], `[a; b]` is `[a, b]`, and `mkCfg ms m` is the [config]
  constructor `⟨ms, m⟩` ([config] is a plain structure here).  `proj2`
  of an [↔] is `.mpr`.  The four sealed surfaces at the end are [def]s
  of the corresponding Lean structures — this tree's rendering of a
  sealed surface, as [Checks/Omni.lean]'s `Exit0Checked` is — and
  [Exit0Image] / [MayFailCfg] are reused from there so that the image a
  reader sees sealed here is the image sealed there.

  `cbn` becomes `simp only [ … ]` with commas, and the three
  closed-computation steps are `decide`: two are closed
  computations on a concrete status list, and the third
  ([exit1_must_exit_reject]) is closed because the entry and the input
  it runs at are concrete.  That is the difference from
  [Checks.GatedSize]'s two verdicts, which quantify over every entry and
  so cannot be reduced at all: a free variable in the state blocks kernel
  reduction of the walk.
-/
import LinuxSem.Checks.Examples
import LinuxSem.Checks.Omni
import LinuxSem.Checks.SpuriousCfg
import LinuxSem.Checks.AbortWitness
import LinuxSem.Checks.GatedSize
import LinuxSem.EquivalenceDefinition.HaltsAllowed

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Run.behavior
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.Checks
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Examples
open LinuxSem.Checks.SpuriousCfg
open LinuxSem.Checks.AbortWitness
open LinuxSem.Checks.GatedSize
open LinuxSem.Checks.Omni (Exit0Image MayFailCfg)
open LinuxSem.Checks.Cases.Kernel.Signal (abort_tid)
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude (check_result)
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.HaltsAllowed

namespace LinuxSem.Checks.HaltsAllowed

/- =========================================================================
   The exit-0 image, at every valid entry and on every valid input
   ========================================================================= -/

/-- The unfiltered twin of [Checks.BudgetPremise.exit0_must_exit_at_cfg]:
    the image exits 0 from EVERY [execve] placement, on EVERY input and
    at EVERY budget.  [Checks.Omni.exit0_exits_c] is what makes that a
    computation over the segment image alone — the program makes no
    memory access beyond its own fetches, so the stack the entry
    describes is never looked at. -/
theorem exit0_must_exit_at_anywhere (sp brk0 mbase : word) (rnd : EntryDraw)
    (lim : Int) (inp : ProcInput) :
    must_exit_at exit0_segments verdict_accept
      (init_config exit0_segments 0x100 demo_phdrs sp brk0 mbase rnd lim inp) := by
  refine exits_c_must_exit_at exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  exact LinuxSem.Checks.Omni.exit0_exits_c sp rnd inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap

/-- UNIVERSALLY QUANTIFIED (admission reason 1), and over the whole
    quantifier the statement carries: every valid entry, every valid
    input, every resolution of the nondeterminism.  The validity
    hypotheses are not used — the image exits from every placement, not
    only the valid ones — and they are still the right premises to
    discharge, because a witness that needed a narrower entry would not
    be a witness for this statement. -/
theorem exit0_halts_allowed_zero :
    halts_allowed_T [verdict_accept] exit0_image := by
  intro en inp _ _
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_in exit0_segments [verdict_accept] verdict_accept _
    (exit0_must_exit_at_anywhere sp brk0 mbase rnd source_alloc_limit inp)
    (by simp)

/-- ... and therefore at the widest set too, through
    [HaltsAllowed.halts_allowed_T_mono].  This is the monotonicity
    lemma FIRED rather than stated: the singleton claim above is carried
    to [AnyExit] by nothing but the subset side condition. -/
theorem exit0_halts_allowed_any_exit :
    halts_allowed_T AnyExit.codes exit0_image := by
  refine halts_allowed_T_mono [verdict_accept] AnyExit.codes exit0_image ?_
    exit0_halts_allowed_zero
  intro code Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  subst Hin
  exact status_allowed_In AnyExit.codes verdict_accept (by decide)

/-- The configured reading, under the configuration the classifier layer
    pins its verdicts to.  [Checks.SpuriousCfg.exits_c_must_exit_at_cfg]
    supplies the filtered walk; nothing else changes. -/
theorem exit0_halts_allowed_forced_only :
    halts_allowed_T_scfg forced_only_cfg [verdict_accept] exit0_image := by
  intro en inp _ _
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  refine (must_exit_in_at_cfg_singleton forced_only_cfg exit0_segments verdict_accept _).mpr ?_
  refine exits_c_must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  exact LinuxSem.Checks.Omni.exit0_exits_c sp rnd inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap

/-- The budget reading, at the shipped source budget.  The premise is
    taken and discarded: this image allocates nothing, so no execution
    of it can be budget-refused, and the statement holds whether or not
    the premise is met. -/
theorem exit0_halts_allowed_budgets :
    halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
      [verdict_accept] exit0_image := by
  intro en inp _ _ _
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  refine (must_exit_in_at_cfg_singleton forced_only_cfg exit0_segments verdict_accept _).mpr ?_
  refine exits_c_must_exit_at_cfg forced_only_cfg exit0_segments verdict_accept 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  exact LinuxSem.Checks.Omni.exit0_exits_c sp rnd inp.in_argv inp.in_envp
    inp.in_uid inp.in_hwcap

/-- The constant-pinned bridge fired on this image: the configured
    statement hands over the budget one with the premise dropped. -/
theorem exit0_budgets_from_scfg :
    halts_allowed_T_scfg_budgets forced_only_cfg source_alloc_limit
      [verdict_accept] exit0_image :=
  halts_allowed_T_scfg_budgets_of_scfg forced_only_cfg _ _
    exit0_halts_allowed_forced_only

/-- The singleton bridge fired in the other direction: the set form at a
    one-element set really is the single-code form, on a concrete run. -/
theorem exit0_singleton_is_must_exit_with (inp : ProcInput) :
    must_exit_in [verdict_accept] exit0_image source_alloc_limit demo_entry inp
    ↔ must_exit_with verdict_accept exit0_image source_alloc_limit demo_entry inp :=
  must_exit_in_singleton verdict_accept exit0_image source_alloc_limit demo_entry inp

/- =========================================================================
   [AnyExit] really covers every status the model can record
   ========================================================================= -/

/-- The pin by computation, on the shape
    [Sys.Kernel.Exit.exit_spec] writes: a status whose low byte is [255]
    and whose high bytes are not zero lands in [AnyExit] under the mask.
    The general claim is
    [HaltsAllowed.any_exit_covers_masked_status]; this is the instance
    that says the general claim's computed reading agrees
    with it on a case a reader can check by eye. -/
theorem truncated_status_in_any_exit :
    (BitVec.ofInt 64 0x1ff &&& BitVec.ofInt 64 255) ∈ AnyExit.codes :=
  status_allowed_In AnyExit.codes _ (by decide)

/-- The two verdict words a classifier uses are in it, which is what
    makes [AnyExit] a set a classifier task could also be stated under. -/
theorem verdicts_in_any_exit :
    verdict_accept ∈ AnyExit.codes ∧ verdict_reject ∈ AnyExit.codes :=
  ⟨status_allowed_In AnyExit.codes _ (by decide),
   status_allowed_In AnyExit.codes _ (by decide)⟩

/-- ... and a word that is NOT a byte is not in it, which is what says
    the set is a real bound rather than everything.  Without this the
    coverage lemma above would be compatible with [AnyExit] holding
    every word. -/
theorem non_byte_not_in_any_exit :
    status_allowed AnyExit.codes (BitVec.ofInt 64 256) = false := by
  decide

/- =========================================================================
   The error route: the undecodable image is refused
   ========================================================================= -/

/-- UNIVERSALLY QUANTIFIED (reason 1) as the negation of one, and at
    EVERY allowed set: the image leaves the modeled surface on its first
    fetch, and [halts_allowed_T] forbids an error anywhere in the tree,
    so no set of statuses can rescue it.  The entry is
    [Checks.Examples.demo_entry] and the input the valid one, so the
    refutation really reaches inside the statement's quantifier. -/
theorem undecodable_image_refutes_halts_allowed (S : List word) :
    ¬ halts_allowed_T S undecodable_image :=
  halts_allowed_T_refuted_by_error S undecodable_image demo_entry demo_proc_input
    (demo_entry_valid_undecodable _ demo_input_valid) demo_input_valid
    (run_unmodeled_errors _ _ _ _
      run_of_undecodable_image_is_unmodeled_at_demo_entry)

/-- The same image is refused under the configured reading too: the
    fetch that leaves the surface is an instruction step, and the filter
    touches no instruction step. -/
theorem undecodable_image_refutes_halts_allowed_forced_only (S : List word) :
    ¬ halts_allowed_T_scfg forced_only_cfg S undecodable_image := by
  intro H
  exact must_exit_in_scfg_refuted_by_error forced_only_cfg S undecodable_image
    source_alloc_limit demo_entry demo_proc_input
    (run_scfg_unmodeled_errors forced_only_cfg undecodable_image source_alloc_limit
      demo_entry demo_proc_input
      (undecodable_unmodeled_scfg_at_demo_entry forced_only_cfg))
    (H demo_entry demo_proc_input (demo_entry_valid_undecodable _ demo_input_valid)
      demo_input_valid)

/- =========================================================================
   The signal route, and where it stops
   ========================================================================= -/

/-- The killed run of [Checks.AbortWitness], in the shape
    [MustExit.must_exit_in_refuted_by_kill] takes. -/
theorem abrt_run_reaches_killed (lim : Int) :
    run_reaches_killed abrt_image lim demo_entry abrt_input := by
  refine ⟨abrt_trace lim, ⟨abrt_t 3, abrt_killed_model lim⟩, BitVec.ofInt 64 6, ?_, ?_⟩
  · show star abrt_segments
      (init_config abrt_segments 0x100 demo_phdrs demo_entry.en_sp demo_entry.en_brk
        demo_entry.en_mmap_base demo_entry.en_draw lim abrt_input)
      (abrt_trace lim) ⟨abrt_t 3, abrt_killed_model lim⟩
    simp only [demo_entry]
    rw [abrt_config]
    exact abrt_star lim
  · exact (killed_is_halted _ _).2

/-- THE SIGNAL REFUTATION, FIRED.  A run that dies by a signal satisfies
    [MustExit.must_exit_in] at NO allowed set — not even one containing
    the signal number, which is the point: the halted case's
    [State.m_killed] conjunct refuses a killed leaf whatever
    [State.m_halted] holds, and [State.with_killed] sets both fields to
    the signal.  So "halts with an allowed status" really does mean
    [exit_group] and not "stops running". -/
theorem abrt_refutes_must_exit_in (S : List word) (lim : Int) :
    ¬ must_exit_in S abrt_image lim demo_entry abrt_input :=
  must_exit_in_refuted_by_kill S abrt_image lim demo_entry abrt_input
    (abrt_run_reaches_killed lim)

/-- ... and here is where it stops, pinned rather than left to a reader.
    [Run.valid_input] pins the abort declaration OFF, and this input
    declares it on, so the run above is not one [halts_allowed_T]
    quantifies over.  That is why the theorem above is about
    [MustExit.must_exit_in] and not about [halts_allowed_T]: the
    statement-level signal refutation is unavailable over this input
    class because the input class has no killed runs in it, not because
    the refutation was not written. -/
theorem abrt_input_not_valid_input : ¬ valid_input abrt_input := by
  intro Hv
  -- Through [Run.valid_input_abort_terminal], the accessor, rather than
  -- by position: [Run.valid_input] grows a conjunct whenever the input
  -- class learns to say something new, and a positional pattern then
  -- names a different clause rather than failing — the witness goes on
  -- compiling and stops being about the abort declaration.  What this
  -- proof depends on is that [Run.valid_input] pins
  -- [State.in_abort_terminal] to [false] SOMEWHERE, which is the fact
  -- the prose above claims.
  have Hoff := valid_input_abort_terminal abrt_input Hv
  rw [abrt_input_declares_abort] at Hoff
  exact absurd Hoff (by simp)

/-- The control, and it is what says the refutation above is about the
    DEATH rather than about the image: the same program on the
    undeclared input is refused too, but by the ERROR route — with the
    declaration clear [Kernel.Signal.tkill_spec] declines, the run
    leaves the modeled surface, and there is no [State.KillEv] to refute
    it by.  The two stances therefore differ on this image for
    [halts_allowed_T] exactly as [Checks.AbortWitness] shows they differ
    for the error-free family. -/
theorem abrt_declined_undeclared_is_unmodeled :
    check_syscall (sys_input abrt_segments (abrt_t 3) (BitVec.ofInt 64 130))
      (mkEffect (BitVec.ofInt 64 0) [] [])
      (with_tid abort_tid
         (init_model (segments_reserved abrt_segments) (BitVec.ofInt 64 0x1000)
            (BitVec.ofInt 64 mmap_base_max) (BitVec.ofInt 64 0x7fff80000000)
            source_alloc_limit abrt_input_undeclared))
    = .CheckUnmodeled :=
  abrt_tkill_declined_undeclared

/- =========================================================================
   The set form is not the single-code form in disguise
   ========================================================================= -/

/-- The statement this whole family exists for, at the level of the
    predicate: [MustExit.must_exit_in] over a two-element set is WEAKER
    than the disjunction of the two single-code claims, because a run
    may exit 0 on one resolution and 1 on another.  Stated here as the
    implication that DOES hold, in both directions of the disjunction,
    so that a reader can see the converse is not offered. -/
theorem must_exit_in_pair_from_either (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput)
    (H : must_exit_with verdict_accept img lim en inp
       ∨ must_exit_with verdict_reject img lim en inp) :
    must_exit_in [verdict_accept, verdict_reject] img lim en inp := by
  rcases H with H | H
  · exact must_exit_with_in _ verdict_accept img lim en inp H (by simp)
  · exact must_exit_with_in _ verdict_reject img lim en inp H (by simp)

/-- The monotonicity lemma fired at the predicate level: a two-element
    allowance is implied by either singleton. -/
theorem must_exit_in_mono_fired (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput)
    (H : must_exit_in [verdict_accept] img lim en inp) :
    must_exit_in [verdict_accept, verdict_reject] img lim en inp := by
  refine must_exit_in_mono [verdict_accept] [verdict_accept, verdict_reject]
    img lim en inp ?_ H
  intro code Hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin ⊢
  exact Or.inl Hin

/- =========================================================================
   The wrong-status route, fired on an image that really exits elsewhere
   ========================================================================= -/

/-- [Checks.GatedSize.exit1_image] is the exit-zero image with one
    immediate changed, so the two are interchangeable everywhere
    [Run.valid_entry] is concerned and the only difference between them
    is the status.  That is what makes it the right refutation: what
    fails is the STATUS and nothing else about the program.

    This is the one evaluation in the file that stays a
    computation, because the entry and the input are the concrete
    [demo_entry] and [demo_proc_input]: the initial state is closed, so
    the kernel can reduce the three-instruction walk (a free variable in
    the state is what blocks that). -/
theorem exit1_must_exit_reject (lim : Int) :
    must_exit_with verdict_reject exit1_image lim demo_entry demo_proc_input := by
  refine exits_c_must_exit_at exit1_segments verdict_reject 8 _ _
    (m_halted_init_model _ _ _ _ _ _) rfl ?_
  decide

/-- THE WRONG-STATUS REFUTATION, FIRED.  A program that halts cleanly,
    errors nowhere, is never killed and terminates on every execution
    still fails [halts_allowed_T] when the status it halts with is
    outside the allowed set.  Without this the statement would be
    indistinguishable, on every image in the tree, from "terminates
    cleanly" with the set along for the ride — every other refutation
    here fires on a program that fails for some OTHER reason.

    The [Run.star] comes from [MustExit.must_exit_at_realizes], which is
    the file's own non-vacuity guard used as a tool: the guard says the
    predicate really produces an exit, and that exit is what the
    refutation needs a witness of. -/
theorem exit1_refutes_halts_allowed_zero :
    ¬ halts_allowed_T [verdict_accept] exit1_image := by
  have Hme := exit1_must_exit_reject source_alloc_limit
  have Hnone : m_halted (init_config exit1_segments 0x100 demo_phdrs demo_entry.en_sp
      demo_entry.en_brk demo_entry.en_mmap_base demo_entry.en_draw
      source_alloc_limit demo_proc_input).cfg_model = none :=
    m_halted_init_model _ _ _ _ _ _
  obtain ⟨tr, fs, c', Hstar, Hh⟩ :=
    must_exit_at_realizes exit1_segments verdict_reject _ Hme Hnone
  refine halts_allowed_T_refuted_by_wrong_status [verdict_accept] exit1_image
    demo_entry demo_proc_input (tr ++ [event.ExitEv verdict_reject fs]) c'
    verdict_reject (demo_entry_valid_exit1 _ demo_input_valid) demo_input_valid
    Hstar Hh ?_
  intro Hin
  have Hall := In_status_allowed [verdict_accept] verdict_reject Hin
  exact absurd Hall (by decide)

/-- ... and the same image PASSES at a set that admits its status, which
    is what says the refutation above is about the set and not about the
    program. -/
theorem exit1_halts_allowed_at_reject :
    must_exit_in [verdict_reject] exit1_image source_alloc_limit demo_entry
      demo_proc_input :=
  (must_exit_in_singleton verdict_reject exit1_image source_alloc_limit demo_entry
    demo_proc_input).mpr (exit1_must_exit_reject _)

/- =========================================================================
   The sealed surfaces are inhabitable
   ========================================================================= -/

/- A module type nothing ascribes against is a module type nobody has
   shown can be met, and the three surfaces this file's statements are
   issued through need that shown.  Each is sealed here over the
   halting fixture at [HaltsAllowed.AnyExit], reusing the
   [MemImageType.MemImage] and [Equivalence.SPURIOUS_CFG] instances
   [Checks.Omni] already packages for the equivalence surfaces, so the
   image a reader sees sealed here is the image sealed there.

   [Equivalence.ShippedBudgets] is the budget pair for the third.  Its
   [headroom] obligation is about the PAIR and this statement has one
   image, so nothing here consumes it; the surface takes the whole
   module anyway, which is what keeps a one-image statement pinned to
   the same constant as the two-image statement beside it. -/

theorem Exit0HaltsAllowedChecked : SPEC_HALTS_ALLOWED AnyExit Exit0Image where
  halts_allowed := exit0_halts_allowed_any_exit

theorem Exit0HaltsAllowedScfgChecked :
    SPEC_HALTS_ALLOWED_SCFG MayFailCfg AnyExit Exit0Image where
  halts_allowed := (halts_allowed_T_scfg_may_fail AnyExit.codes exit0_image).mpr
    exit0_halts_allowed_any_exit

theorem Exit0HaltsAllowedBudgetsChecked :
    SPEC_HALTS_ALLOWED_SCFG_BUDGETS MayFailCfg ShippedBudgets AnyExit Exit0Image where
  halts_allowed := halts_allowed_T_scfg_budgets_of_scfg MayFailCfg.cfg AnyExit.codes
    exit0_image
    ((halts_allowed_T_scfg_may_fail AnyExit.codes exit0_image).mpr
      exit0_halts_allowed_any_exit)

end LinuxSem.Checks.HaltsAllowed
