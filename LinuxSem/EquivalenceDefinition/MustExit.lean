/-
  * EquivalenceDefinition.MustExit — every maximal execution exits with one code


  TRUST BOUNDARY: this file is part of the trusted specification.
  Proof files never edit it.  A top-level check that ascribes against a
  module type mentioning [must_exit_with] depends on the definitions
  here remaining fixed, exactly as the baseline check depends on
  [Equivalence].

  [Equivalence] states obligations about the RELATION between two
  binaries — the baseline shape and its error-free strengthening.
  This file states an obligation about ONE
  binary: on this input, whatever the nondeterminism resolves to, the
  process terminates, and the status a waiting parent reads is [code].
  That is the shape a decision procedure needs — a classifier binary
  answers by exiting 0 or 1, and "answers" has to mean every execution
  answers, the same way, in finite time.

  ** Why an inductive, and why three premises

  The definition is [must_exit_at] below: an accessibility predicate
  over the [Run.SNext] transitions, following [Run.all_traces_error]'s
  shape.  Three properties are wanted and each buys one premise.

  - TERMINATION.  Being INDUCTIVE is what supplies it: a configuration
    with an infinite [Run.SNext] execution cannot construct the proof
    merely because an exiting alternative stays available at every
    finite prefix.  This is the same argument [Run.all_traces_error]'s
    header makes, and it is the reason the predicate is not defined as
    "every maximal trace contains an [State.ExitEv]", which a
    coinductive reading would satisfy vacuously.
  - NO STUCK EXECUTION.  The progress premise ([exists evs st, sstep
    …]) stops a configuration with no successor at all from passing
    because the [forall]-over-successors premise is vacuous there.
    Without it, a wedged run would count as "exits with 0".
  - NO ERRORING EXECUTION.  Premise [forall evs, ~ sstep … SError] is
    the one thing this predicate needs that [Run.all_traces_error] does
    not have, and it is not optional.  [Run.SError] is a step_to
    CONSTRUCTOR, not a configuration, so quantifying over [SNext]
    successors says nothing about it: a configuration that can either
    step on to an exit or take the error transition would satisfy an
    [SNext]-only definition.  A classifier that faults on some
    resolution has not decided anything, so error branches are refuted
    explicitly.

  The two cases are made syntactically exclusive by giving the step
  case the premise [m_halted (cfg_model c) = None].  That premise is
  DERIVABLE from progress — every [Run.sstep] constructor requires
  [m_halted model = None], which [sstep_not_halted] below records — so
  it does not change which configurations satisfy the predicate; it is
  there so that case analysis on one proof against another
  ([must_exit_at_exclusive]) does not have to re-derive it.  The
  consequence worth stating: a configuration halted with a DIFFERENT
  code satisfies neither case, so [must_exit_at] pins the code rather
  than merely asserting termination ([must_exit_at_wrong_code]).

  ** The exit code is compared DIRECTLY, not masked here

  Design decision, and the evidence for it.  [Sys.Kernel.Exit.exit_spec]
  is

      set_halted (bv_and code (Z_to_bv 64 255)) ;; ret_only (Z_to_bv 64 0)

  — the MASK IS APPLIED BY THE SPEC, before the status reaches the
  model.  [Sys.Kernel.Exit.exit_spec] is the only spec arm that writes
  [State.m_halted] at all, and [Sys.SyscallTable.spec_table] routes
  both exit (93) and exit_group (94) to it, so every value
  [State.m_halted] can ever hold is already [bv_and a0 255].  The
  routing half of that is machine-checked, by
  [LinuxProcessSem.Bridge.Exit.exit_dispatch_denotes], which reduces
  [Specs.syscall_spec] at 93 and 94 to [Sys.Kernel.Exit.exit_spec]'s
  normal form out of the literal table, so the routing is not left on
  inspection here.  The "only arm" half is checked nowhere, and it is the
  half a reader should re-check when a syscall lands.
  Note
  that [State.with_halted], the setter underneath [Monad.set_halted],
  is ALSO applied directly about a dozen times elsewhere — in the
  executable checker ([Checks.Sys.Kernel.Exit]), its witness
  ([Checks.Witness.Kernel.Exit]), the simulation layers
  ([Common.ExitSim], [Common.ShapeAlg], [Common.MmapSim],
  [Common.FileSim], [Common.CatSim], [Common.WallSim]) and the QA file
  [Checks.Examples].  Every such site
  passes a value already
  masked with 255, so
  the conclusion survives, but "[Monad.set_halted] is the only writer"
  would not be true and is not what this rests on.

  [Run.sstep_exit] copies that stored word
  verbatim into the [State.ExitEv] it emits.

  Therefore [must_exit_with] compares the stored word with plain
  equality and applies NO mask of its own.  Masking again would be
  idempotent and harmless, but it would also be a second, independent
  statement of the ABI that could drift from the spec's; comparing
  directly keeps [Sys.Kernel.Exit.exit_spec] the single place the low
  byte is defined.

  What a caller must supply, in consequence: [must_exit_with] means
  what Linux observes exactly when [code] is itself a masked byte.
  That the low byte is what a waiting parent reads is the kernel's
  own encoding: [SYSCALL_DEFINE1(exit, int, error_code)] calls
  [do_exit((error_code & 0xff) << 8)] and
  [SYSCALL_DEFINE1(exit_group, ...)] calls
  [do_group_exit((error_code & 0xff) << 8)], and the wait side reads
  that field back with [infop->status = status >> 8] — so the seven
  high bytes of the argument are discarded before any status exists
  and cannot be recovered (kernel/exit.c, Linux v6.18.46, commit
  1f99e9ab748f).  [Z_to_bv 64 0] and [Z_to_bv 64 1] — the two verdicts
  a classifier uses — are already in that range, so
  [must_exit_with (Z_to_bv 64 0)] is precisely "exit(0) as a waiting
  parent sees it".  A [code] outside
  [0 .. 255] names a status no run of this model can reach, which is
  sound but useless; it is not rejected here because the config-level
  predicate is about arbitrary configurations, and a config's
  [State.m_halted] field is not itself constrained to the byte range.

  Write those words PLAIN, with no [bv_and … 255] wrapper.  Re-masking
  is the identity on a value already in [0 .. 255], so a wrapped form
  would be propositionally correct — but it is not SYNTACTICALLY equal
  to the plain form, and equality on [code] is what the lemmas here
  conclude and consume.  [must_exit_at_exclusive] and
  [must_exit_with_exclusive] hand back a bare [code1 = code2]; under a
  mixed convention, turning that into the fact one wanted takes a
  conversion step at every use site instead of none.  One convention,
  the plain one.

  ** Non-vacuity

  [must_exit_with_realizes] is this file's guard, the analogue of
  [Run.all_traces_error_reaches_error]: whatever satisfies the
  predicate really does emit an [State.ExitEv] carrying [code] on some
  execution, so the predicate cannot be satisfied by saying nothing.
  Refutability is [must_exit_at_refuted_by_error] and
  [must_exit_at_wrong_code] at the definition level.  The run-level
  witnesses are example-side: [Checks.Examples.exit0_image_must_exit_zero]
  is a concrete image this predicate HOLDS of, and
  [Checks.Examples.undecodable_image_refutes_must_exit] one it fails
  for at every code.  [Checks.Examples] is **not ported** (see
  the notes), so neither exists under that name here — but the
  positive side is not left empty on that account: the demo under
  [Examples/PatchClassifyDemo] (a consumer of this file, not a dependency)
  carries [O1_must_exit_at], which establishes the predicate at the demo's
  O1 image for any entry state with the pc at the image's first
  instruction, no pending syscall and a lazy-free model, and the six demo
  verdicts are built on facts of that shape.  So an image meeting these
  premises does exist in the tree.  The premises below are still easy to
  write and hard to meet all at once, and nothing in THIS file would
  notice if no image met them.

  NOTES (this file):
  - `run`, `run_scfg`, `must_exit_with`, … read the record fields
    directly rather than matching on the record; the projections reduce on
    concrete records, so `cases img` followed by
    `simp only [must_exit_with]` recovers `init_config`.
  - `Z` is `Int`, `word` is `BitVec 64`, `list` is `List`, `In x l` is
    `x ∈ l`, `Z_to_bv 64 n` is `BitVec.ofInt 64 n`.
  - An inductive's constructors live in its namespace, so
    `must_exit_at_halted` / `must_exit_at_running` are
    `MustExit.must_exit_at.halted` / `.running` (likewise for
    `must_exit_in_at`, `must_exit_at_cfg`, `must_exit_in_at_cfg`).  The
    case labels (`(* sstep_exit *)`, …) become the constructor names in
    the `cases` blocks.
  - `bh_traces`/`bh_errors`/`bh_unmodeled` are structure projections of
    `Run.behavior`; `open behavior` (as `Run.lean` itself does) brings the
    unqualified names into scope.
  - There are no closed sanity goals for this file — every declaration
    here is a `Prop`-valued predicate or a lemma about one — so there are
    no `by decide` checks.
-/
import LinuxSem.LinuxProcessSem.Run

open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.MustExit

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open behavior

/- =========================================================================
   Three facts about [Run.sstep] that the lemmas below rely on
   ========================================================================= -/

/-- Nothing steps out of a halted configuration: every [Run.sstep]
    constructor carries [m_halted model = None] as a premise.  This is
    what makes the progress premise of [must_exit_at]'s step case
    unsatisfiable at a halted configuration, hence what makes the two
    cases exclusive. -/
theorem sstep_not_halted (segs : List Segment) (c : config) (evs : List event)
    (st : step_to) (hss : sstep segs c evs st) : m_halted c.cfg_model = none := by
  cases hss <;> assumption

/-- A run cannot leave a halted configuration, so a [Run.star] out of one
    is the empty one. -/
theorem star_from_halted (segs : List Segment) (c : config) (tr : List event)
    (c' : config) (hstar : star segs c tr c')
    (hh : m_halted c.cfg_model ≠ none) : tr = [] ∧ c' = c := by
  cases hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step =>
    rename_i evs c2 tr1 hss _
    exact absurd (sstep_not_halted segs c evs (.SNext c2) hss) hh

/-- The step that HALTS a configuration is the exit step, and it emits
    the [State.ExitEv] carrying the stored code.  Every other successor
    transition leaves [State.m_halted] alone:

    - [Run.sstep_instr] changes the model only through
      [Run.mi_account_step], whose frame lemma keeps [State.m_proc]
      fixed, and [State.m_halted] is a projection of it;
    - [Run.sstep_syscall] has [m_halted model' = None] as an explicit
      premise and then materializes, which
      [State.materialize_model_accesses_frame] also shows keeps
      [State.m_proc] fixed;
    - the remaining constructors go to [Run.SError].

    So [Run.sstep_exit] is the only way into a halted configuration, and
    the exit event is emitted BY that transition rather than at the
    halted configuration — exits are interior transitions here, not
    terminal ones.  [must_exit_at_realizes] needs exactly this to turn
    "reaches a halted configuration" into "emits an [State.ExitEv]". -/
theorem sstep_next_halts_by_exit (segs : List Segment) (c : config) (evs : List event)
    (c' : config) (hss : sstep segs c evs (.SNext c')) :
    m_halted c'.cfg_model = none
    ∨ (∃ evs0 code,
        evs = evs0 ++ [event.ExitEv code (m_fs c'.cfg_model)]
        ∧ m_halted c'.cfg_model = some code
        ∧ m_killed c'.cfg_model = none)
    ∨ (∃ evs0 sig,
        evs = evs0 ++ [event.KillEv sig (m_fs c'.cfg_model)]
        ∧ m_killed c'.cfg_model = some sig) := by
  cases hss with
  | instr ms model ms' model' hh hsvc hstep =>
    left
    obtain ⟨-, -, -, -, -, hproc, -⟩ :=
      mi_account_step_model_frame segs ms model ms' model' hstep
    have hframe : m_halted model' = m_halted model := by
      unfold m_halted
      rw [hproc]
    rw [hframe]
    exact hh
  | syscall ms model x8 eff model' model'' evs1 hh hsvc hspec hh' hmat =>
    left
    obtain ⟨-, -, -, -, -, hproc, -⟩ :=
      materialize_model_accesses_frame model' (syscall_effect_accesses eff) model'' hmat
    have hframe : m_halted model'' = m_halted model' := by
      unfold m_halted
      rw [hproc]
    rw [hframe]
    exact hh'
  | exit ms model x8 eff model' evs1 code hh hsvc hspec hh' hk =>
    exact Or.inr (Or.inl ⟨evs1, code, rfl, hh', hk⟩)
  | killed ms model x8 eff model' evs1 sig hh hsvc hspec hk =>
    exact Or.inr (Or.inr ⟨evs1, sig, rfl, hk⟩)

/- =========================================================================
   The predicate
   ========================================================================= -/

/-- Every maximal execution from [c] halts, after finitely many steps,
    with [State.m_halted] equal to [Some code].  See this file's header
    for what each premise buys; in one line: inductive for termination,
    progress against stuck configurations, [SError]-refutation against
    faulting ones, and the [forall]-over-successors premise so that one
    exiting resolution cannot hide a sibling that does something else. -/
inductive must_exit_at (segs : List Segment) (code : word) : config → Prop where
  | halted (c : config)
      (hh : m_halted c.cfg_model = some code)
      (hk : m_killed c.cfg_model = none) :
      must_exit_at segs code c
  | running (c : config)
      (hnone : m_halted c.cfg_model = none)
      (hprog : ∃ evs st, sstep segs c evs st)
      (hnoerr : ∀ evs, ¬ sstep segs c evs .SError)
      (hnext : ∀ evs c', sstep segs c evs (.SNext c') → must_exit_at segs code c') :
      must_exit_at segs code c

/-- The run-level statement: every execution of [img] from the [execve]
    choices [en] on inputs [inp], under the memory budget [lim], exits
    with [code].

    Written as a MATCH on the image and the [execve] entry for the same
    reason [Run.run] is (Run.v, [Run.run]'s header): a proof unfolding it
    with [cbn [must_exit_with …]] gets the underlying [Run.init_config]
    application back as soon as those two arguments are concrete records,
    instead of having to name the projections in every such [cbn].  The
    [State.ProcInput] is passed whole and read by projections, which
    reduce, so the same works for a variable [inp].  [Run.ExecEntry] has
    four fields — the stack pointer, the program break, the mmap base and
    the AT_RANDOM draw, all chosen non-deterministically — and all four
    are consumed here exactly as [Run.run] consumes them, so that
    [must_exit_with code img lim en inp] and [Run.run img lim en inp]
    always speak about the SAME configuration.

    NOTE.  Lean's structure projections reduce on concrete records, so
    this reads the fields directly; `cases img` then recovers
    [init_config]. -/
def must_exit_with (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_at img.img_segments code
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/- =========================================================================
   What the predicate rules out: errors, and hence unmodeled behavior
   ========================================================================= -/

/-- No execution reaches the explicit error transition.  The
    [SError]-refutation premise holds at every configuration the
    induction passes through, and [Run.reaches_error] names a [Run.star]
    to a configuration that then errors — so the [Run.star] is walked by
    the induction and its endpoint is one of those configurations.  At a
    halted endpoint there is no [Run.star] to walk and no [Run.sstep] to
    take at all. -/
theorem must_exit_at_no_error (segs : List Segment) (code : word) :
    ∀ (c : config), must_exit_at segs code c → ¬ reaches_error segs c := by
  intro c hme
  induction hme with
  | halted c hh hk =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; simp
    obtain ⟨-, heq⟩ := star_from_halted segs c tr c2 hstar hne
    subst heq
    have hnone := sstep_not_halted segs c2 evs .SError hsserr
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    cases hstar with
    | refl => exact hnoerr evs hsserr
    | step =>
      rename_i evs0 c1 tr1 hss hstar1
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

/-- The run-level image.  This is the clause that makes [must_exit_with]
    usable as a classifier verdict without a separate error-freedom
    conjunct: a binary that decides by exiting cannot also be allowed to
    fault. -/
theorem must_exit_with_no_error (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_with code img lim en inp) :
    ¬ bh_errors (run img lim en inp) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_no_error segs code _ hme

/-- ... and therefore no execution runs off the edge of the model
    either, by [Run.no_error_no_unmodeled]: being uncovered is a special
    case of erroring ([Run.reaches_unmodeled_reaches_error]).  So a
    [must_exit_with] obligation subsumes [Equivalence.modeled] for the
    run it speaks about, exactly as [Equivalence.error_free] does. -/
theorem must_exit_with_modeled (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_with code img lim en inp) :
    ¬ bh_unmodeled (run img lim en inp) := by
  have hnoerr := must_exit_with_no_error code img lim en inp hme
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact no_error_no_unmodeled segs _ hnoerr

/- =========================================================================
   The code is unique
   ========================================================================= -/

/-- One configuration cannot must-exit with two different codes.  This is
    what lets a classifier's two verdicts be read as a decision: from
    [must_exit_with verdict_accept] one may conclude
    [~ must_exit_with verdict_reject], so
    "exits 0" and "exits 1" are genuinely opposite answers rather than
    two claims that could both hold.

    The induction walks one proof and inverts the other at each step.
    Both base cases give [Some c1 = Some c2] directly; a base against a
    step contradicts on [State.m_halted]; step against step follows a
    successor supplied by the progress premise, which exists and is an
    [Run.SNext] because the [SError] branch is refuted. -/
theorem must_exit_at_exclusive (segs : List Segment) (code1 code2 : word) (c : config)
    (h1 : must_exit_at segs code1 c) (h2 : must_exit_at segs code2 c) :
    code1 = code2 := by
  revert code2
  induction h1 with
  | halted c hh hk =>
    intro code2 h2
    cases h2
    · rename_i hh' hk'
      rw [hh] at hh'
      exact Option.some.inj hh'
    · rename_i hnone hprog hnoerr hnext
      rw [hh] at hnone
      exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro code2 h2
    cases h2
    · rename_i hh' hk'
      rw [hh'] at hnone
      exact absurd hnone (by simp)
    · rename_i hnone2 hprog2 hnoerr2 hnext2
      obtain ⟨evs, st, hss⟩ := hprog
      cases st with
      | SNext c' => exact ih evs c' hss code2 (hnext2 evs c' hss)
      | SError => exact absurd hss (hnoerr evs)

theorem must_exit_with_exclusive (code1 code2 : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (h1 : must_exit_with code1 img lim en inp)
    (h2 : must_exit_with code2 img lim en inp) :
    code1 = code2 := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_exclusive segs code1 code2 _ h1 h2

/- =========================================================================
   Non-vacuity: the predicate really produces an exit event
   ========================================================================= -/

/-- From a non-halted configuration satisfying the predicate there is an
    actual [Run.star] whose accumulated trace ENDS in
    [ExitEv code fs].

    The proof follows one successor at a time, chosen by the progress
    premise (and an [Run.SNext] one, because [SError] is refuted).  At
    each step either the successor is still running — recurse, and
    prepend this step's events, which is where the trace grows on the
    left — or the successor is halted, and then
    [sstep_next_halts_by_exit] says the transition just taken was
    [Run.sstep_exit] and its event list already ends in the
    [State.ExitEv].  The code carried by that event is [code] because the
    successor satisfies the predicate and is halted, so it satisfies it
    by the base case.

    The [m_halted (cfg_model c) = None] hypothesis is what the
    statement needs to be about an exit EVENT rather than an exit STATE:
    a configuration handed to us already halted satisfies the predicate
    without any transition having emitted anything.  Run-level, that
    hypothesis is discharged by computation on [Run.init_config]. -/
theorem must_exit_at_realizes (segs : List Segment) (code : word) :
    ∀ (c : config), must_exit_at segs code c → m_halted c.cfg_model = none →
      ∃ tr fs c',
        star segs c (tr ++ [event.ExitEv code fs]) c'
        ∧ m_halted c'.cfg_model = some code := by
  intro c hme
  induction hme with
  | halted c hh hk =>
    intro hrun
    rw [hh] at hrun
    exact absurd hrun (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro hrun
    obtain ⟨evs, st, hss⟩ := hprog
    cases st
    · rename_i c1
      have hme1 := hnext evs c1 hss
      cases hm : m_halted c1.cfg_model with
      | some k =>
        -- The successor is halted and satisfies the predicate, so by the
        -- base case it is NOT killed -- which is what rules the kill
        -- transition out and leaves [Run.sstep_exit] as the only way in.
        have hboth : k = code ∧ m_killed c1.cfg_model = none := by
          cases hme1 with
          | halted =>
            rename_i hh' hk'
            rw [hm] at hh'
            exact ⟨Option.some.inj hh', hk'⟩
          | running =>
            rename_i hnone' _ _ _
            rw [hm] at hnone'
            exact absurd hnone' (by simp)
        obtain ⟨hk_eq, hnk⟩ := hboth
        rw [hk_eq] at hm
        obtain hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨evs0, sig, hevs, hsig⟩ :=
          sstep_next_halts_by_exit segs c evs c1 hss
        · rw [hm] at hnone1
          exact absurd hnone1 (by simp)
        · have hcc : code0 = code := by
            rw [hm] at hcode0
            exact (Option.some.inj hcode0).symm
          rw [hcc] at hevs
          exact ⟨evs0, m_fs c1.cfg_model, c1, by rw [← hevs]; exact star_one segs c evs c1 hss, hm⟩
        · rw [hnk] at hsig
          exact absurd hsig (by simp)
      | none =>
        obtain ⟨tr, fs, c', hstar, hh'⟩ := ih evs c1 hss hm
        refine ⟨evs ++ tr, fs, c', ?_, hh'⟩
        rw [List.append_assoc]
        exact star.step c evs c1 (tr ++ [event.ExitEv code fs]) c' hss hstar
    · exact absurd hss (hnoerr evs)

/-- The guard, at run level: a run that must exit with [code] has an
    observable trace ending in [ExitEv code fs].  This is the analogue of
    [Run.all_traces_error_reaches_error] — a universal predicate whose
    guard nobody can trip is a guard that guards nothing.  In particular
    [must_exit_with] cannot be satisfied by a run that produces no
    events, which is what a purely "never errors, never gets stuck"
    reading would have allowed. -/
theorem must_exit_with_realizes (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_with code img lim en inp) :
    ∃ tr fs, bh_traces (run img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  have hnone : m_halted (init_config segs pc ph sp brk0 mbase rnd lim inp).cfg_model = none :=
    rfl
  obtain ⟨tr, fs, c', hstar, _⟩ := must_exit_at_realizes segs code _ hme hnone
  exact ⟨tr, fs, tr ++ [event.ExitEv code fs], c', hstar, is_prefix_refl _⟩

/- =========================================================================
   The predicate bites: it can be established, and it can be refuted
   ========================================================================= -/

/-- POSITIVE, one step.  A configuration whose every successor is already
    halted with [code] must exit with [code].  It is the introduction
    rule for the [ecall] that runs [Sys.Kernel.Exit.exit_spec], where
    the exit transition is the last one and [Run.sstep_exit]'s target
    carries [Some code].  Nothing uses it yet:
    [Checks.Examples.exits_c_must_exit_at], the one worked example, goes
    through [must_exit_at_running] and [must_exit_at_halted] directly.
    (That example's home is
    `Examples.PatchClassifyDemo.ExitsC.exits_c_must_exit_at`, which is
    what this file's readers should look at, and it also goes through the
    two rules directly.)
    It is kept as the shape a caller reaching the exit in one step would
    want, and should be deleted if nothing claims it.
    ([must_exit_at_halted] is the other introduction rule, and is the
    constructor itself.) -/
theorem must_exit_at_exit_now (segs : List Segment) (code : word) (c : config)
    (hnone : m_halted c.cfg_model = none)
    (hprog : ∃ evs st, sstep segs c evs st)
    (hnoerr : ∀ evs, ¬ sstep segs c evs .SError)
    (hhalt : ∀ evs c', sstep segs c evs (.SNext c') →
      m_halted c'.cfg_model = some code ∧ m_killed c'.cfg_model = none) :
    must_exit_at segs code c :=
  must_exit_at.running c hnone hprog hnoerr
    (fun evs c' hss =>
      let h := hhalt evs c' hss
      must_exit_at.halted c' h.1 h.2)

/-- NEGATIVE, the error route.  A running configuration that can take the
    error transition refutes the predicate for EVERY code — the base case
    is out because the configuration is not halted, and the step case is
    out by its [SError]-refutation premise.  This is the definition-level
    form of [Checks.Examples.undecodable_image_refutes_must_exit], which
    runs it on a concrete image: one whose first fetch is unmodeled
    errors immediately, so it refutes [must_exit_with] at any code. -/
theorem must_exit_at_refuted_by_error (segs : List Segment) (code : word) (c : config)
    (evs : List event) (hnone : m_halted c.cfg_model = none)
    (hsserr : sstep segs c evs .SError) : ¬ must_exit_at segs code c := by
  intro hme
  cases hme with
  | halted =>
    rename_i hh hk
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running =>
    rename_i _ _ hnoerr _
    exact hnoerr evs hsserr

/-- NEGATIVE, the wrong-code route.  A configuration halted with one code
    refutes the predicate at every other code.  Without this the
    predicate could have been "terminates without erroring", with the
    code argument along for the ride; it is what makes [must_exit_with
    verdict_accept] and [must_exit_with verdict_reject] different statements. -/
theorem must_exit_at_wrong_code (segs : List Segment) (code code' : word) (c : config)
    (hh : m_halted c.cfg_model = some code) (hne : code ≠ code') :
    ¬ must_exit_at segs code' c := by
  intro hme
  cases hme with
  | halted =>
    rename_i hh' hk'
    rw [hh] at hh'
    exact hne (Option.some.inj hh')
  | running =>
    rename_i hnone _ _ _
    rw [hh] at hnone
    exact absurd hnone (by simp)

/-- The run-level refutation, packaged for the example side: any run that
    can error refutes [must_exit_with] at every code.  This is the
    contrapositive of [must_exit_with_no_error], and it is the shape the
    [Checks.Examples] witnesses use (their run really is unmodeled):
    those establish [bh_unmodeled] of a
    run, which [Equivalence.run_unmodeled_errors] turns into [bh_errors]. -/
theorem must_exit_with_refuted_by_error (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (herr : bh_errors (run img lim en inp)) :
    ¬ must_exit_with code img lim en inp :=
  fun hme => must_exit_with_no_error code img lim en inp hme herr

/- =========================================================================
   The verdict predicate under a spurious-failure configuration:
   [must_exit_at_cfg], [must_exit_with_scfg]
   =========================================================================

   [Run.run_scfg cfg] walks [Run.sstep_cfg cfg], the step relation with
   every avoidable refusal of a forced-only family removed.  The verdict
   predicate follows: [must_exit_at_cfg cfg] is [must_exit_at] over that
   relation, premise for premise, and [must_exit_with_scfg cfg] is its
   run-level form.  At [Run.may_fail_cfg] it is [must_exit_with] itself
   ([must_exit_with_scfg_may_fail]).

   This is the predicate the classifier layer pins its verdicts to, at
   [Run.forced_only_cfg] ([Classifier.decides_fo]), and the reason is
   this: a classifier that reads its input cannot decide anything
   under a reading where the open may be refused without cause, since
   the refused run reaches neither verdict.  Under forced-only the
   refusal is gone wherever the open could have succeeded, and what
   remains of the obligation is what a decision procedure should be
   asked — every execution the environment can FORCE ends in the right
   verdict.

   What the pin costs, stated once: the progress premise of
   [must_exit_at_cfg_running] is over the FILTERED relation, and
   filtering can only make it harder to meet.  It cannot make it
   impossible where the filter's question is answered — [Run.sstep_cfg_progress]
   — and that is what [must_exit_at_cfg_mono] below turns into the
   statement that a verdict under may-fail is a verdict under every
   configuration: the pin is a WEAKENING of the obligation, never a
   different one.  The premise it carries, [run_decided], is the KNOWN
   GAP of [Run.v]'s spurious-failure section, at the run. -/

inductive must_exit_at_cfg (cfg : SpuriousCfg) (segs : List Segment) (code : word)
    : config → Prop where
  | halted (c : config)
      (hh : m_halted c.cfg_model = some code)
      (hk : m_killed c.cfg_model = none) :
      must_exit_at_cfg cfg segs code c
  | running (c : config)
      (hnone : m_halted c.cfg_model = none)
      (hprog : ∃ evs st, sstep_cfg segs cfg c evs st)
      (hnoerr : ∀ evs, ¬ sstep_cfg segs cfg c evs .SError)
      (hnext : ∀ evs c', sstep_cfg segs cfg c evs (.SNext c') →
        must_exit_at_cfg cfg segs code c') :
      must_exit_at_cfg cfg segs code c

/-- The three facts about [Run.sstep] the lemmas above rely on, carried
    to the filtered relation through [Run.sstep_cfg_sub]. -/
theorem sstep_cfg_not_halted (segs : List Segment) (cfg : SpuriousCfg) (c : config)
    (evs : List event) (st : step_to) (hss : sstep_cfg segs cfg c evs st) :
    m_halted c.cfg_model = none :=
  sstep_not_halted segs c evs st (sstep_cfg_sub segs cfg c evs st hss)

theorem star_cfg_from_halted (segs : List Segment) (cfg : SpuriousCfg) (c : config)
    (tr : List event) (c' : config) (hstar : star_cfg segs cfg c tr c')
    (hh : m_halted c.cfg_model ≠ none) : tr = [] ∧ c' = c := by
  cases hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step =>
    rename_i evs c2 tr1 hss _
    exact absurd (sstep_cfg_not_halted segs cfg c evs (.SNext c2) hss) hh

theorem sstep_cfg_next_halts_by_exit (segs : List Segment) (cfg : SpuriousCfg)
    (c : config) (evs : List event) (c' : config)
    (hss : sstep_cfg segs cfg c evs (.SNext c')) :
    m_halted c'.cfg_model = none
    ∨ (∃ evs0 code,
        evs = evs0 ++ [event.ExitEv code (m_fs c'.cfg_model)]
        ∧ m_halted c'.cfg_model = some code
        ∧ m_killed c'.cfg_model = none)
    ∨ (∃ evs0 sig,
        evs = evs0 ++ [event.KillEv sig (m_fs c'.cfg_model)]
        ∧ m_killed c'.cfg_model = some sig) :=
  sstep_next_halts_by_exit segs c evs c' (sstep_cfg_sub segs cfg c evs (.SNext c') hss)

/- -------------------------------------------------------------------------
   The same five facts, for the filtered predicate
   ------------------------------------------------------------------------- -/

theorem must_exit_at_cfg_no_error (cfg : SpuriousCfg) (segs : List Segment) (code : word) :
    ∀ (c : config), must_exit_at_cfg cfg segs code c → ¬ reaches_error_cfg segs cfg c := by
  intro c hme
  induction hme with
  | halted c hh hk =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; simp
    obtain ⟨-, heq⟩ := star_cfg_from_halted segs cfg c tr c2 hstar hne
    subst heq
    have hnone := sstep_cfg_not_halted segs cfg c2 evs .SError hsserr
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    cases hstar with
    | refl => exact hnoerr evs hsserr
    | step =>
      rename_i evs0 c1 tr1 hss hstar1
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_at_cfg_exclusive (cfg : SpuriousCfg) (segs : List Segment)
    (code1 code2 : word) (c : config)
    (h1 : must_exit_at_cfg cfg segs code1 c) (h2 : must_exit_at_cfg cfg segs code2 c) :
    code1 = code2 := by
  revert code2
  induction h1 with
  | halted c hh hk =>
    intro code2 h2
    cases h2
    · rename_i hh' hk'
      rw [hh] at hh'
      exact Option.some.inj hh'
    · rename_i hnone hprog hnoerr hnext
      rw [hh] at hnone
      exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro code2 h2
    cases h2
    · rename_i hh' hk'
      rw [hh'] at hnone
      exact absurd hnone (by simp)
    · rename_i hnone2 hprog2 hnoerr2 hnext2
      obtain ⟨evs, st, hss⟩ := hprog
      cases st with
      | SNext c' => exact ih evs c' hss code2 (hnext2 evs c' hss)
      | SError => exact absurd hss (hnoerr evs)

theorem must_exit_at_cfg_realizes (cfg : SpuriousCfg) (segs : List Segment) (code : word) :
    ∀ (c : config), must_exit_at_cfg cfg segs code c → m_halted c.cfg_model = none →
      ∃ tr fs c',
        star_cfg segs cfg c (tr ++ [event.ExitEv code fs]) c'
        ∧ m_halted c'.cfg_model = some code := by
  intro c hme
  induction hme with
  | halted c hh hk =>
    intro hrun
    rw [hh] at hrun
    exact absurd hrun (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro hrun
    obtain ⟨evs, st, hss⟩ := hprog
    cases st
    · rename_i c1
      have hme1 := hnext evs c1 hss
      cases hm : m_halted c1.cfg_model with
      | some k =>
        have hboth : k = code ∧ m_killed c1.cfg_model = none := by
          cases hme1 with
          | halted =>
            rename_i hh' hk'
            rw [hm] at hh'
            exact ⟨Option.some.inj hh', hk'⟩
          | running =>
            rename_i hnone' _ _ _
            rw [hm] at hnone'
            exact absurd hnone' (by simp)
        obtain ⟨hk_eq, hnk⟩ := hboth
        rw [hk_eq] at hm
        obtain hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨evs0, sig, hevs, hsig⟩ :=
          sstep_cfg_next_halts_by_exit segs cfg c evs c1 hss
        · rw [hm] at hnone1
          exact absurd hnone1 (by simp)
        · have hcc : code0 = code := by
            rw [hm] at hcode0
            exact (Option.some.inj hcode0).symm
          rw [hcc] at hevs
          refine ⟨evs0, m_fs c1.cfg_model, c1, ?_, hm⟩
          rw [← hevs]
          simpa using star_cfg.step c evs c1 [] c1 hss (star_cfg.refl c1)
        · rw [hnk] at hsig
          exact absurd hsig (by simp)
      | none =>
        obtain ⟨tr, fs, c', hstar, hh'⟩ := ih evs c1 hss hm
        refine ⟨evs ++ tr, fs, c', ?_, hh'⟩
        rw [List.append_assoc]
        exact star_cfg.step c evs c1 (tr ++ [event.ExitEv code fs]) c' hss hstar
    · exact absurd hss (hnoerr evs)

theorem must_exit_at_cfg_refuted_by_error (cfg : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) (evs : List event)
    (hnone : m_halted c.cfg_model = none) (hsserr : sstep_cfg segs cfg c evs .SError) :
    ¬ must_exit_at_cfg cfg segs code c := by
  intro hme
  cases hme with
  | halted =>
    rename_i hh hk
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running =>
    rename_i _ _ hnoerr _
    exact hnoerr evs hsserr

theorem must_exit_at_cfg_wrong_code (cfg : SpuriousCfg) (segs : List Segment)
    (code code' : word) (c : config)
    (hh : m_halted c.cfg_model = some code) (hne : code ≠ code') :
    ¬ must_exit_at_cfg cfg segs code' c := by
  intro hme
  cases hme with
  | halted =>
    rename_i hh' hk'
    rw [hh] at hh'
    exact hne (Option.some.inj hh')
  | running =>
    rename_i hnone _ _ _
    rw [hh] at hnone
    exact absurd hnone (by simp)

/- -------------------------------------------------------------------------
   Meaning at [may_fail_cfg], and monotonicity in the configuration
   ------------------------------------------------------------------------- -/

theorem must_exit_at_cfg_may_fail (segs : List Segment) (code : word) (c : config) :
    must_exit_at_cfg may_fail_cfg segs code c ↔ must_exit_at segs code c := by
  constructor
  · intro h
    induction h with
    | halted c hh hk => exact must_exit_at.halted c hh hk
    | running c hnone hprog hnoerr hnext ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      refine must_exit_at.running c hnone ⟨evs, st, ?_⟩ ?_ ?_
      · exact (sstep_cfg_may_fail segs c evs st).mpr hss
      · intro evs' herr
        exact hnoerr evs' ((sstep_cfg_may_fail segs c evs' .SError).mp herr)
      · intro evs' c' hss'
        exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (.SNext c')).mp hss')
  · intro h
    induction h with
    | halted c hh hk => exact must_exit_at_cfg.halted c hh hk
    | running c hnone hprog hnoerr hnext ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      refine must_exit_at_cfg.running c hnone ⟨evs, st, ?_⟩ ?_ ?_
      · exact (sstep_cfg_may_fail segs c evs st).mp hss
      · intro evs' herr
        exact hnoerr evs' ((sstep_cfg_may_fail segs c evs' .SError).mpr herr)
      · intro evs' c' hss'
        exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (.SNext c')).mpr hss')

/-- The filter's question is answered at every configuration reachable
    from [c] — over the UNFILTERED star, which reaches everything any
    filtered star does.  See [Run.refusal_decided]. -/
def decided_from (cfg : SpuriousCfg) (segs : List Segment) (c : config) : Prop :=
  ∀ tr c' x8,
    star segs c tr c' →
    c'.cfg_ms.ms_svc_pending = some x8 →
    refusal_decided cfg (sys_input segs c'.cfg_ms x8) c'.cfg_model

theorem decided_from_step (cfg cfg' : SpuriousCfg) (segs : List Segment) (c : config)
    (evs : List event) (c' : config) (hdec : decided_from cfg segs c)
    (hss : sstep_cfg segs cfg' c evs (.SNext c')) : decided_from cfg segs c' := by
  intro tr c'' x8 hstar hsvc
  refine hdec (evs ++ tr) c'' x8 ?_ hsvc
  exact star.step c evs c' tr c'' (sstep_cfg_sub segs cfg' c evs (.SNext c') hss) hstar

/-- A verdict under a configuration is a verdict under every SMALLER
    one, wherever the filter's question is answered along the way.
    Progress is [Run.sstep_cfg_progress]; the error premise and the
    successor premise go through [Run.sstep_cfg_mono], since every step
    of the smaller configuration is a step of the larger. -/
theorem must_exit_at_cfg_mono (cfg1 cfg2 : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) (hle : cfg_le cfg1 cfg2)
    (hdec : decided_from cfg1 segs c) (h : must_exit_at_cfg cfg2 segs code c) :
    must_exit_at_cfg cfg1 segs code c := by
  induction h with
  | halted c hh hk =>
    exact must_exit_at_cfg.halted c hh hk
  | running c hnone hprog hnoerr hnext ih =>
    obtain ⟨evs, st, hss⟩ := hprog
    refine must_exit_at_cfg.running c hnone ?_ ?_ ?_
    · obtain ⟨ms, model⟩ := c
      exact sstep_cfg_progress segs cfg1 ms model evs st
        (fun x8 hsvc => hdec [] ⟨ms, model⟩ x8 (star.refl _) hsvc)
        (sstep_cfg_sub segs cfg2 ⟨ms, model⟩ evs st hss)
    · intro evs' herr
      exact hnoerr evs' (sstep_cfg_mono segs cfg1 cfg2 c evs' .SError hle herr)
    · intro evs' c' hss'
      exact ih evs' c' (sstep_cfg_mono segs cfg1 cfg2 c evs' (.SNext c') hle hss')
        (decided_from_step cfg1 cfg1 segs c evs' c' hdec hss')

/-- In particular a verdict under may-fail is a verdict under any
    configuration at all: the pin is a weakening. -/
theorem must_exit_at_cfg_of_must_exit_at (cfg : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) (hdec : decided_from cfg segs c)
    (h : must_exit_at segs code c) : must_exit_at_cfg cfg segs code c := by
  refine must_exit_at_cfg_mono cfg may_fail_cfg segs code c
    (may_fail_cfg_greatest cfg) hdec ?_
  exact (must_exit_at_cfg_may_fail segs code c).mpr h

/- -------------------------------------------------------------------------
   The run-level statement
   ------------------------------------------------------------------------- -/

/-- [must_exit_with] under a configuration: the same [match] on the
    image and the entry, the same initial configuration
    [Run.run_scfg cfg] starts from, so that
    [must_exit_with_scfg cfg code img lim en inp] and
    [Run.run_scfg cfg img lim en inp] always speak about the SAME run. -/
def must_exit_with_scfg (cfg : SpuriousCfg) (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_at_cfg cfg img.img_segments code
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- The one-switch form, as a thin instance: [true] IS
    [must_exit_with] by an [if] on the literal, so every lemma above
    applies at [true] unchanged; [false] is the record form at
    [Run.alloc_only_cfg false]. -/
def must_exit_with_cfg (alloc_may_fail : Bool) (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  if alloc_may_fail then must_exit_with code img lim en inp
  else must_exit_with_scfg (alloc_only_cfg false) code img lim en inp

theorem must_exit_with_cfg_true (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg true code img lim en inp = must_exit_with code img lim en inp :=
  rfl

theorem must_exit_with_cfg_false (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_cfg false code img lim en inp
      = must_exit_with_scfg (alloc_only_cfg false) code img lim en inp :=
  rfl

theorem must_exit_with_scfg_may_fail (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_with_scfg may_fail_cfg code img lim en inp ↔ must_exit_with code img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_cfg_may_fail segs code _

theorem must_exit_with_scfg_no_error (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_with_scfg cfg code img lim en inp) :
    ¬ bh_errors (run_scfg cfg img lim en inp) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_cfg_no_error cfg segs code _ hme

theorem must_exit_with_scfg_modeled (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_with_scfg cfg code img lim en inp) :
    ¬ bh_unmodeled (run_scfg cfg img lim en inp) :=
  fun hun =>
    must_exit_with_scfg_no_error cfg code img lim en inp hme
      (run_scfg_unmodeled_errors cfg img lim en inp hun)

theorem must_exit_with_scfg_exclusive (cfg : SpuriousCfg) (code1 code2 : word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (h1 : must_exit_with_scfg cfg code1 img lim en inp)
    (h2 : must_exit_with_scfg cfg code2 img lim en inp) :
    code1 = code2 := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_cfg_exclusive cfg segs code1 code2 _ h1 h2

/-- The guard, at run level and for the filtered run: a run that must
    exit with [code] under [cfg] has a trace ending in [ExitEv code fs]
    — a trace of the filtered run, and therefore of the unfiltered one
    ([must_exit_with_scfg_realizes_run]).  The second form is what
    [Classifier.accepts_fo_realizes] states: the classifier's verdict is
    an event the real program emits, not one a filter invented. -/
theorem must_exit_with_scfg_realizes (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_with_scfg cfg code img lim en inp) :
    ∃ tr fs, bh_traces (run_scfg cfg img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  have hnone : m_halted (init_config segs pc ph sp brk0 mbase rnd lim inp).cfg_model = none :=
    rfl
  obtain ⟨tr, fs, c', hstar, _⟩ := must_exit_at_cfg_realizes cfg segs code _ hme hnone
  exact ⟨tr, fs, tr ++ [event.ExitEv code fs], c', hstar, is_prefix_refl _⟩

theorem must_exit_with_scfg_realizes_run (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_with_scfg cfg code img lim en inp) :
    ∃ tr fs, bh_traces (run img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨tr, fs, htr⟩ := must_exit_with_scfg_realizes cfg code img lim en inp hme
  exact ⟨tr, fs, run_scfg_sub_traces cfg img lim en inp _ htr⟩

theorem must_exit_with_scfg_refuted_by_error (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (herr : bh_errors (run_scfg cfg img lim en inp)) :
    ¬ must_exit_with_scfg cfg code img lim en inp :=
  fun hme => must_exit_with_scfg_no_error cfg code img lim en inp hme herr

/-- The filter's question is answered on every configuration THIS run
    reaches. -/
def run_decided (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  decided_from cfg img.img_segments
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem must_exit_with_scfg_mono (cfg1 cfg2 : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) (hle : cfg_le cfg1 cfg2)
    (hdec : run_decided cfg1 img lim en inp)
    (h : must_exit_with_scfg cfg2 code img lim en inp) :
    must_exit_with_scfg cfg1 code img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_cfg_mono cfg1 cfg2 segs code _ hle hdec h

theorem must_exit_with_scfg_of_must_exit_with (cfg : SpuriousCfg) (code : word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hdec : run_decided cfg img lim en inp)
    (h : must_exit_with code img lim en inp) :
    must_exit_with_scfg cfg code img lim en inp := by
  refine must_exit_with_scfg_mono cfg may_fail_cfg code img lim en inp
    (may_fail_cfg_greatest cfg) hdec ?_
  exact (must_exit_with_scfg_may_fail code img lim en inp).mpr h

/- =========================================================================
   The SET form: halting with a status in an ALLOWED SET
   =========================================================================

   [must_exit_at] fixes ONE code, and that is the right shape for a
   classifier, whose whole point is that the code carries an answer.  It
   is the wrong shape for the other thing a caller wants to know about a
   single binary: that it TERMINATES CLEANLY, with a status the task
   declares acceptable, whatever the nondeterminism resolves to.  A
   program that exits 0 on one resolution and 1 on another satisfies
   [must_exit_at] at NEITHER code — [must_exit_at_exclusive] says so —
   and yet it halted through [exit_group] both times.

   So the set form replaces the equality at the halted leaf with a
   MEMBERSHIP.  Everything else is premise for premise the same
   predicate, which is what makes the two comparable: inductive for
   termination, progress against stuck configurations,
   [SError]-refutation against faulting ones, the [forall]-over-successors
   premise so no resolution is hidden, and [State.m_killed] clear at the
   leaf so a signal death is not an exit.

   WHAT DOES NOT CARRY OVER is uniqueness.  [must_exit_at_exclusive]
   has no analogue here and must not be written: two allowed sets can
   both contain the code a run exits with, and that is the point.  What
   replaces it is [must_exit_in_at_mono] — a bigger set is a weaker
   claim — and [must_exit_in_at_wrong_code], which is the refutation:
   halting OUTSIDE the set is what fails.

   The set is a [list word] rather than a [word -> Prop] so that a
   concrete instance is a closed term a `decide` can settle, which
   is what the example side needs; [In] over that list is the
   membership.  A caller wanting an infinite or abstract set would want
   the predicate version, and this file does not offer one because
   nothing asks for it — an allowed-exit set is a handful of statuses a
   task writes down.

   The codes are compared the way [must_exit_at] compares them: PLAIN,
   with no [bv_and … 255] wrapper of this file's own.  The header above
   says why at length; in one line, [Sys.Kernel.Exit.exit_spec] applies
   the mask before the status reaches the model, so a set whose members
   are written as bare bytes is a set of statuses a waiting parent can
   really read. -/

inductive must_exit_in_at (segs : List Segment) (S : List word) : config → Prop where
  | halted (c : config) (code : word)
      (hh : m_halted c.cfg_model = some code)
      (hin : code ∈ S)
      (hk : m_killed c.cfg_model = none) :
      must_exit_in_at segs S c
  | running (c : config)
      (hnone : m_halted c.cfg_model = none)
      (hprog : ∃ evs st, sstep segs c evs st)
      (hnoerr : ∀ evs, ¬ sstep segs c evs .SError)
      (hnext : ∀ evs c', sstep segs c evs (.SNext c') → must_exit_in_at segs S c') :
      must_exit_in_at segs S c

/-- The run-level statement, the same [match] on the image and the entry
    [must_exit_with] uses and for the same reason: so that
    [must_exit_in S img lim en inp] and [Run.run img lim en inp] always
    speak about the SAME configuration. -/
def must_exit_in (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_in_at img.img_segments S
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

/-- What a halted configuration satisfying the predicate must look like.
    Stated once because three proofs below take the base case apart, and
    doing it by [inversion] at each of them is where a mistake about the
    kill conjunct would hide. -/
theorem must_exit_in_at_halted_inv (segs : List Segment) (S : List word) (c : config)
    (code : word) (hme : must_exit_in_at segs S c)
    (hh : m_halted c.cfg_model = some code) :
    code ∈ S ∧ m_killed c.cfg_model = none := by
  cases hme with
  | halted =>
    rename_i code0 hin0 hh0 hk0
    have heq : code = code0 := by
      rw [hh] at hh0
      exact Option.some.inj hh0
    rw [heq]
    exact ⟨hin0, hk0⟩
  | running =>
    rename_i hnone _ _ _
    rw [hh] at hnone
    exact absurd hnone (by simp)

/- -------------------------------------------------------------------------
   What the set form rules out: errors, and hence unmodeled behavior
   ------------------------------------------------------------------------- -/

theorem must_exit_in_at_no_error (segs : List Segment) (S : List word) :
    ∀ (c : config), must_exit_in_at segs S c → ¬ reaches_error segs c := by
  intro c hme
  induction hme with
  | halted c code hh hin hk =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; simp
    obtain ⟨-, heq⟩ := star_from_halted segs c tr c2 hstar hne
    subst heq
    have hnone := sstep_not_halted segs c2 evs .SError hsserr
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    cases hstar with
    | refl => exact hnoerr evs hsserr
    | step =>
      rename_i evs0 c1 tr1 hss hstar1
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_in_no_error (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_in S img lim en inp) :
    ¬ bh_errors (run img lim en inp) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_no_error segs S _ hme

theorem must_exit_in_modeled (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_in S img lim en inp) :
    ¬ bh_unmodeled (run img lim en inp) := by
  have hnoerr := must_exit_in_no_error S img lim en inp hme
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact no_error_no_unmodeled segs _ hnoerr

/- -------------------------------------------------------------------------
   The single-code form is the singleton set, and a code in the set
   ------------------------------------------------------------------------- -/

/-- A run that must exit with one code must exit with a status in any
    set containing it.  This is the direction a task takes: a binary
    proved to exit 0 satisfies "exits with something allowed" for every
    allowed set that admits 0. -/
theorem must_exit_at_in (segs : List Segment) (S : List word) (code : word) (c : config)
    (hme : must_exit_at segs code c) (hin : code ∈ S) : must_exit_in_at segs S c := by
  induction hme with
  | halted c hh hk => exact must_exit_in_at.halted c code hh hin hk
  | running c hnone hprog hnoerr hnext ih =>
    exact must_exit_in_at.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)

theorem must_exit_with_in (S : List word) (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_with code img lim en inp)
    (hin : code ∈ S) : must_exit_in S img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_in segs S code _ hme hin

/-- ... and at a ONE-ELEMENT set the two are the same statement.  This is
    the lemma that says the set form is a generalisation rather than a
    different predicate: everything [must_exit_at] concludes is available
    at a singleton, uniqueness included. -/
theorem must_exit_in_at_singleton (segs : List Segment) (code : word) (c : config) :
    must_exit_in_at segs [code] c ↔ must_exit_at segs code c := by
  constructor
  · intro h
    induction h with
    | halted c code0 hh hin hk =>
      rw [List.mem_singleton] at hin
      rw [hin] at hh
      exact must_exit_at.halted c hh hk
    | running c hnone hprog hnoerr hnext ih =>
      exact must_exit_at.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)
  · intro h
    exact must_exit_at_in segs [code] code c h (by simp)

theorem must_exit_in_singleton (code : word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_in [code] img lim en inp ↔ must_exit_with code img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_singleton segs code _

/- -------------------------------------------------------------------------
   Monotone in the set: a wider allowance is a weaker claim
   ------------------------------------------------------------------------- -/

/-- The direction that is sound, and only that one.  Widening the allowed
    set weakens the obligation; NARROWING it does not follow, and a task
    that wants the narrower statement has to prove it. -/
theorem must_exit_in_at_mono (segs : List Segment) (S1 S2 : List word) (c : config)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2) (h : must_exit_in_at segs S1 c) :
    must_exit_in_at segs S2 c := by
  induction h with
  | halted c code hh hin hk =>
    exact must_exit_in_at.halted c code hh (hsub code hin) hk
  | running c hnone hprog hnoerr hnext ih =>
    exact must_exit_in_at.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)

theorem must_exit_in_mono (S1 S2 : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2) (h : must_exit_in S1 img lim en inp) :
    must_exit_in S2 img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_mono segs S1 S2 _ hsub h

/- -------------------------------------------------------------------------
   The set form bites: it can be refuted three ways
   ------------------------------------------------------------------------- -/

/-- NEGATIVE, the error route, as for the single-code form: a running
    configuration that can take the error transition refutes the
    predicate for EVERY allowed set. -/
theorem must_exit_in_at_refuted_by_error (segs : List Segment) (S : List word)
    (c : config) (evs : List event) (hnone : m_halted c.cfg_model = none)
    (hsserr : sstep segs c evs .SError) : ¬ must_exit_in_at segs S c := by
  intro hme
  cases hme with
  | halted =>
    rename_i code hin hh hk
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running =>
    rename_i _ _ hnoerr _
    exact hnoerr evs hsserr

theorem must_exit_in_refuted_by_error (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (herr : bh_errors (run img lim en inp)) :
    ¬ must_exit_in S img lim en inp :=
  fun hme => must_exit_in_no_error S img lim en inp hme herr

/-- NEGATIVE, the wrong-status route.  A configuration halted with a code
    the set does not contain refutes it.  This is what keeps the
    predicate from degenerating into "terminates without erroring" with
    the set along for the ride. -/
theorem must_exit_in_at_wrong_code (segs : List Segment) (S : List word) (code : word)
    (c : config) (hh : m_halted c.cfg_model = some code) (hnin : code ∉ S) :
    ¬ must_exit_in_at segs S c := by
  intro hme
  obtain ⟨hin, -⟩ := must_exit_in_at_halted_inv segs S c code hme hh
  exact hnin hin

/-- NEGATIVE, the SIGNAL route, and this one has no single-code analogue
    in this file because [must_exit_at]'s callers never needed it stated:
    a configuration whose [State.m_killed] is set refutes the predicate
    at every set, whatever [State.m_halted] holds.

    The base case is out by its own [State.m_killed] conjunct.  What
    rules the step case out is [State.m_killed_of_m_halted_none], the
    representation invariant that a model with no halt status has no kill
    status either — [State.with_killed] sets both — so a running
    configuration cannot be a killed one.  A death by signal is
    therefore not an allowed exit for ANY allowed set, which is the
    whole reason the statement this feeds is worth stating separately
    from error-freedom: a process that aborts errors nowhere. -/
theorem must_exit_in_at_refuted_by_kill (segs : List Segment) (S : List word) (c : config)
    (sig : word) (hk : m_killed c.cfg_model = some sig) :
    ¬ must_exit_in_at segs S c := by
  intro hme
  cases hme with
  | halted =>
    rename_i code hh hin hk0
    rw [hk] at hk0
    exact absurd hk0 (by simp)
  | running =>
    rename_i hnone _ _ _
    exact absurd (m_killed_of_m_halted_none c.cfg_model hnone) (by rw [hk]; simp)

/-- The predicate survives a [Run.star]: every configuration the run
    reaches satisfies it again.  A halted configuration takes no step at
    all ([sstep_not_halted]), so the walk can only be in the step case,
    where the [forall]-over-successors premise hands the next one over. -/
theorem must_exit_in_at_star (segs : List Segment) (S : List word) :
    ∀ (c : config) (tr : List event) (c' : config),
      must_exit_in_at segs S c → star segs c tr c' → must_exit_in_at segs S c' := by
  intro c tr c' hme hstar
  revert hme
  induction hstar with
  | refl =>
    intro hme
    exact hme
  | step c0 evs c1 tr1 c2 hss hstar1 ih =>
    intro hme
    refine ih ?_
    cases hme with
    | halted =>
      rename_i code hin hh hk
      exfalso
      have hn := sstep_not_halted segs c0 evs (.SNext c1) hss
      rw [hh] at hn
      exact absurd hn (by simp)
    | running =>
      rename_i hnone hprog hnoerr hnext
      exact hnext evs c1 hss

/-- ... and therefore a run that can REACH a killed configuration refutes
    it.  This is the form the example side uses: a witness image supplies
    a [Run.star] to the configuration its [tkill] produced. -/
theorem must_exit_in_at_refuted_by_reachable_kill (segs : List Segment) (S : List word)
    (c : config) (tr : List event) (c' : config) (sig : word)
    (hstar : star segs c tr c') (hk : m_killed c'.cfg_model = some sig) :
    ¬ must_exit_in_at segs S c :=
  fun hme => must_exit_in_at_refuted_by_kill segs S c' sig hk
    (must_exit_in_at_star segs S c tr c' hme hstar)

/-- "This run can die by a signal", at run level: some execution of it
    reaches a configuration whose [State.m_killed] is set.  Written as a
    [match] for the reason [run_decided] is, so that it and
    [must_exit_in] always speak about the same initial configuration.

    This is DELIBERATELY not [Equivalence.dies_by_signal], which is a
    statement about the trace SET: getting from a [State.KillEv] in a
    trace back to the configuration that emitted it would need to know
    that no other transition can emit one, and nothing in this file
    establishes that.  The reachability form is what a witness image
    actually hands over — a [Run.star] it built — so it is what the
    refutation takes. -/
def run_reaches_killed (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  ∃ tr c' sig,
    star img.img_segments
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c'
    ∧ m_killed c'.cfg_model = some sig

theorem must_exit_in_refuted_by_kill (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hk : run_reaches_killed img lim en inp) :
    ¬ must_exit_in S img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  obtain ⟨tr, c', sig, hstar, hkill⟩ := hk
  exact must_exit_in_at_refuted_by_reachable_kill segs S _ tr c' sig hstar hkill

/- -------------------------------------------------------------------------
   Non-vacuity: the set form really produces an exit event, carrying a
   status the set allows
   ------------------------------------------------------------------------- -/

/-- The guard, and it is STRONGER than "some exit event happens": the
    code the emitted [State.ExitEv] carries is itself in [S].  Without
    the [In] conjunct the statement would be satisfied by a run that
    exits with anything at all, which is the reading the whole predicate
    exists to rule out. -/
theorem must_exit_in_at_realizes (segs : List Segment) (S : List word) :
    ∀ (c : config), must_exit_in_at segs S c → m_halted c.cfg_model = none →
      ∃ tr code fs c',
        code ∈ S
        ∧ star segs c (tr ++ [event.ExitEv code fs]) c'
        ∧ m_halted c'.cfg_model = some code := by
  intro c hme
  induction hme with
  | halted c code hh hin hk =>
    intro hrun
    rw [hh] at hrun
    exact absurd hrun (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro hrun
    obtain ⟨evs, st, hss⟩ := hprog
    cases st
    · rename_i c1
      have hme1 := hnext evs c1 hss
      cases hm : m_halted c1.cfg_model with
      | some k =>
        obtain ⟨hin1, hnk⟩ := must_exit_in_at_halted_inv segs S c1 k hme1 hm
        obtain hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨evs0, sig, hevs, hsig⟩ :=
          sstep_next_halts_by_exit segs c evs c1 hss
        · rw [hm] at hnone1
          exact absurd hnone1 (by simp)
        · have hcc : code0 = k := by
            rw [hm] at hcode0
            exact (Option.some.inj hcode0).symm
          rw [hcc] at hevs
          refine ⟨evs0, k, m_fs c1.cfg_model, c1, hin1, ?_, hm⟩
          rw [← hevs]
          exact star_one segs c evs c1 hss
        · rw [hnk] at hsig
          exact absurd hsig (by simp)
      | none =>
        obtain ⟨tr, code, fs, c', hin', hstar, hh'⟩ := ih evs c1 hss hm
        refine ⟨evs ++ tr, code, fs, c', hin', ?_, hh'⟩
        rw [List.append_assoc]
        exact star.step c evs c1 (tr ++ [event.ExitEv code fs]) c' hss hstar
    · exact absurd hss (hnoerr evs)

theorem must_exit_in_realizes (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) (hme : must_exit_in S img lim en inp) :
    ∃ tr code fs, code ∈ S ∧ bh_traces (run img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  have hnone : m_halted (init_config segs pc ph sp brk0 mbase rnd lim inp).cfg_model = none :=
    rfl
  obtain ⟨tr, code, fs, c', hin, hstar, _⟩ :=
    must_exit_in_at_realizes segs S _ hme hnone
  exact ⟨tr, code, fs, hin, tr ++ [event.ExitEv code fs], c', hstar, is_prefix_refl _⟩

/- =========================================================================
   The set form under a spurious-failure configuration
   =========================================================================

   The same relation to [must_exit_in_at] that [must_exit_at_cfg] has to
   [must_exit_at]: the predicate over [Run.sstep_cfg cfg], premise for
   premise.  It is what a task pinned to [Run.forced_only_cfg] states,
   for the reason that section's header gives — a binary that reads its
   input decides nothing under a reading where the open may be refused
   without cause — and the pin is a WEAKENING, which is
   [must_exit_in_at_cfg_mono]. -/

inductive must_exit_in_at_cfg (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) : config → Prop where
  | halted (c : config) (code : word)
      (hh : m_halted c.cfg_model = some code)
      (hin : code ∈ S)
      (hk : m_killed c.cfg_model = none) :
      must_exit_in_at_cfg cfg segs S c
  | running (c : config)
      (hnone : m_halted c.cfg_model = none)
      (hprog : ∃ evs st, sstep_cfg segs cfg c evs st)
      (hnoerr : ∀ evs, ¬ sstep_cfg segs cfg c evs .SError)
      (hnext : ∀ evs c', sstep_cfg segs cfg c evs (.SNext c') →
        must_exit_in_at_cfg cfg segs S c') :
      must_exit_in_at_cfg cfg segs S c

def must_exit_in_scfg (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  must_exit_in_at_cfg cfg img.img_segments S
    (init_config img.img_segments img.img_init_pc img.img_phdrs
      en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp)

theorem must_exit_in_at_cfg_halted_inv (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) (code : word)
    (hme : must_exit_in_at_cfg cfg segs S c)
    (hh : m_halted c.cfg_model = some code) :
    code ∈ S ∧ m_killed c.cfg_model = none := by
  cases hme with
  | halted =>
    rename_i code0 hin0 hh0 hk0
    have heq : code = code0 := by
      rw [hh] at hh0
      exact Option.some.inj hh0
    rw [heq]
    exact ⟨hin0, hk0⟩
  | running =>
    rename_i hnone _ _ _
    rw [hh] at hnone
    exact absurd hnone (by simp)

theorem must_exit_in_at_cfg_no_error (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) :
    ∀ (c : config), must_exit_in_at_cfg cfg segs S c → ¬ reaches_error_cfg segs cfg c := by
  intro c hme
  induction hme with
  | halted c code hh hin hk =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    have hne : m_halted c.cfg_model ≠ none := by rw [hh]; simp
    obtain ⟨-, heq⟩ := star_cfg_from_halted segs cfg c tr c2 hstar hne
    subst heq
    have hnone := sstep_cfg_not_halted segs cfg c2 evs .SError hsserr
    rw [hh] at hnone
    exact absurd hnone (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro herr
    obtain ⟨tr, c2, evs, hstar, hsserr⟩ := herr
    cases hstar with
    | refl => exact hnoerr evs hsserr
    | step =>
      rename_i evs0 c1 tr1 hss hstar1
      exact ih evs0 c1 hss ⟨tr1, c2, evs, hstar1, hsserr⟩

theorem must_exit_in_scfg_no_error (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_in_scfg cfg S img lim en inp) :
    ¬ bh_errors (run_scfg cfg img lim en inp) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_cfg_no_error cfg segs S _ hme

theorem must_exit_in_scfg_modeled (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_in_scfg cfg S img lim en inp) :
    ¬ bh_unmodeled (run_scfg cfg img lim en inp) :=
  fun hun =>
    must_exit_in_scfg_no_error cfg S img lim en inp hme
      (run_scfg_unmodeled_errors cfg img lim en inp hun)

theorem must_exit_in_scfg_refuted_by_error (cfg : SpuriousCfg) (S : List word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (herr : bh_errors (run_scfg cfg img lim en inp)) :
    ¬ must_exit_in_scfg cfg S img lim en inp :=
  fun hme => must_exit_in_scfg_no_error cfg S img lim en inp hme herr

theorem must_exit_in_at_cfg_refuted_by_kill (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) (sig : word)
    (hk : m_killed c.cfg_model = some sig) :
    ¬ must_exit_in_at_cfg cfg segs S c := by
  intro hme
  cases hme with
  | halted =>
    rename_i code hin hh hk0
    rw [hk] at hk0
    exact absurd hk0 (by simp)
  | running =>
    rename_i hnone _ _ _
    exact absurd (m_killed_of_m_halted_none c.cfg_model hnone) (by rw [hk]; simp)

theorem must_exit_in_at_cfg_star (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) :
    ∀ (c : config) (tr : List event) (c' : config),
      must_exit_in_at_cfg cfg segs S c → star_cfg segs cfg c tr c' →
      must_exit_in_at_cfg cfg segs S c' := by
  intro c tr c' hme hstar
  revert hme
  induction hstar with
  | refl =>
    intro hme
    exact hme
  | step c0 evs c1 tr1 c2 hss hstar1 ih =>
    intro hme
    refine ih ?_
    cases hme with
    | halted =>
      rename_i code hin hh hk
      exfalso
      have hn := sstep_cfg_not_halted segs cfg c0 evs (.SNext c1) hss
      rw [hh] at hn
      exact absurd hn (by simp)
    | running =>
      rename_i hnone hprog hnoerr hnext
      exact hnext evs c1 hss

theorem must_exit_in_at_cfg_refuted_by_reachable_kill (cfg : SpuriousCfg)
    (segs : List Segment) (S : List word) (c : config) (tr : List event)
    (c' : config) (sig : word) (hstar : star_cfg segs cfg c tr c')
    (hk : m_killed c'.cfg_model = some sig) :
    ¬ must_exit_in_at_cfg cfg segs S c :=
  fun hme => must_exit_in_at_cfg_refuted_by_kill cfg segs S c' sig hk
    (must_exit_in_at_cfg_star cfg segs S c tr c' hme hstar)

/-- The configured twin, over [Run.star_cfg]. -/
def run_reaches_killed_cfg (cfg : SpuriousCfg) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  ∃ tr c' sig,
    star_cfg img.img_segments cfg
      (init_config img.img_segments img.img_init_pc img.img_phdrs
        en.en_sp en.en_brk en.en_mmap_base en.en_draw lim inp) tr c'
    ∧ m_killed c'.cfg_model = some sig

theorem must_exit_in_scfg_refuted_by_kill (cfg : SpuriousCfg) (S : List word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hk : run_reaches_killed_cfg cfg img lim en inp) :
    ¬ must_exit_in_scfg cfg S img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  obtain ⟨tr, c', sig, hstar, hkill⟩ := hk
  exact must_exit_in_at_cfg_refuted_by_reachable_kill cfg segs S _ tr c' sig hstar hkill

theorem must_exit_in_at_cfg_wrong_code (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) (code : word) (c : config)
    (hh : m_halted c.cfg_model = some code) (hnin : code ∉ S) :
    ¬ must_exit_in_at_cfg cfg segs S c := by
  intro hme
  obtain ⟨hin, -⟩ := must_exit_in_at_cfg_halted_inv cfg segs S c code hme hh
  exact hnin hin

theorem must_exit_in_at_cfg_mono_set (cfg : SpuriousCfg) (segs : List Segment)
    (S1 S2 : List word) (c : config)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2)
    (h : must_exit_in_at_cfg cfg segs S1 c) :
    must_exit_in_at_cfg cfg segs S2 c := by
  induction h with
  | halted c code hh hin hk =>
    exact must_exit_in_at_cfg.halted c code hh (hsub code hin) hk
  | running c hnone hprog hnoerr hnext ih =>
    exact must_exit_in_at_cfg.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)

theorem must_exit_in_scfg_mono_set (cfg : SpuriousCfg) (S1 S2 : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hsub : ∀ code, code ∈ S1 → code ∈ S2)
    (h : must_exit_in_scfg cfg S1 img lim en inp) :
    must_exit_in_scfg cfg S2 img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_cfg_mono_set cfg segs S1 S2 _ hsub h

/-- Non-vacuity under the configuration, and then the same guard carried
    to the UNFILTERED run: the exit the filtered reading realizes is an
    event the real program emits, not one the filter invented. -/
theorem must_exit_in_at_cfg_realizes (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) :
    ∀ (c : config), must_exit_in_at_cfg cfg segs S c → m_halted c.cfg_model = none →
      ∃ tr code fs c',
        code ∈ S
        ∧ star_cfg segs cfg c (tr ++ [event.ExitEv code fs]) c'
        ∧ m_halted c'.cfg_model = some code := by
  intro c hme
  induction hme with
  | halted c code hh hin hk =>
    intro hrun
    rw [hh] at hrun
    exact absurd hrun (by simp)
  | running c hnone hprog hnoerr hnext ih =>
    intro hrun
    obtain ⟨evs, st, hss⟩ := hprog
    cases st
    · rename_i c1
      have hme1 := hnext evs c1 hss
      cases hm : m_halted c1.cfg_model with
      | some k =>
        obtain ⟨hin1, hnk⟩ := must_exit_in_at_cfg_halted_inv cfg segs S c1 k hme1 hm
        obtain hnone1 | ⟨evs0, code0, hevs, hcode0, _⟩ | ⟨evs0, sig, hevs, hsig⟩ :=
          sstep_cfg_next_halts_by_exit segs cfg c evs c1 hss
        · rw [hm] at hnone1
          exact absurd hnone1 (by simp)
        · have hcc : code0 = k := by
            rw [hm] at hcode0
            exact (Option.some.inj hcode0).symm
          rw [hcc] at hevs
          refine ⟨evs0, k, m_fs c1.cfg_model, c1, hin1, ?_, hm⟩
          rw [← hevs]
          simpa using star_cfg.step c evs c1 [] c1 hss (star_cfg.refl c1)
        · rw [hnk] at hsig
          exact absurd hsig (by simp)
      | none =>
        obtain ⟨tr, code, fs, c', hin', hstar, hh'⟩ := ih evs c1 hss hm
        refine ⟨evs ++ tr, code, fs, c', hin', ?_, hh'⟩
        rw [List.append_assoc]
        exact star_cfg.step c evs c1 (tr ++ [event.ExitEv code fs]) c' hss hstar
    · exact absurd hss (hnoerr evs)

theorem must_exit_in_scfg_realizes (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_in_scfg cfg S img lim en inp) :
    ∃ tr code fs,
      code ∈ S ∧ bh_traces (run_scfg cfg img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  have hnone : m_halted (init_config segs pc ph sp brk0 mbase rnd lim inp).cfg_model = none :=
    rfl
  obtain ⟨tr, code, fs, c', hin, hstar, _⟩ :=
    must_exit_in_at_cfg_realizes cfg segs S _ hme hnone
  exact ⟨tr, code, fs, hin, tr ++ [event.ExitEv code fs], c', hstar, is_prefix_refl _⟩

theorem must_exit_in_scfg_realizes_run (cfg : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_in_scfg cfg S img lim en inp) :
    ∃ tr code fs,
      code ∈ S ∧ bh_traces (run img lim en inp) (tr ++ [event.ExitEv code fs]) := by
  obtain ⟨tr, code, fs, hin, htr⟩ := must_exit_in_scfg_realizes cfg S img lim en inp hme
  exact ⟨tr, code, fs, hin, run_scfg_sub_traces cfg img lim en inp _ htr⟩

/- -------------------------------------------------------------------------
   Meaning at [may_fail_cfg], the singleton bridge, and monotonicity in
   the configuration
   ------------------------------------------------------------------------- -/

theorem must_exit_in_at_cfg_may_fail (segs : List Segment) (S : List word) (c : config) :
    must_exit_in_at_cfg may_fail_cfg segs S c ↔ must_exit_in_at segs S c := by
  constructor
  · intro h
    induction h with
    | halted c code hh hin hk => exact must_exit_in_at.halted c code hh hin hk
    | running c hnone hprog hnoerr hnext ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      refine must_exit_in_at.running c hnone ⟨evs, st, ?_⟩ ?_ ?_
      · exact (sstep_cfg_may_fail segs c evs st).mpr hss
      · intro evs' herr
        exact hnoerr evs' ((sstep_cfg_may_fail segs c evs' .SError).mp herr)
      · intro evs' c' hss'
        exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (.SNext c')).mp hss')
  · intro h
    induction h with
    | halted c code hh hin hk => exact must_exit_in_at_cfg.halted c code hh hin hk
    | running c hnone hprog hnoerr hnext ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      refine must_exit_in_at_cfg.running c hnone ⟨evs, st, ?_⟩ ?_ ?_
      · exact (sstep_cfg_may_fail segs c evs st).mp hss
      · intro evs' herr
        exact hnoerr evs' ((sstep_cfg_may_fail segs c evs' .SError).mpr herr)
      · intro evs' c' hss'
        exact ih evs' c' ((sstep_cfg_may_fail segs c evs' (.SNext c')).mpr hss')

theorem must_exit_in_scfg_may_fail (S : List word) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg may_fail_cfg S img lim en inp ↔ must_exit_in S img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_cfg_may_fail segs S _

/-- The configured singleton is the configured single-code form, the
    [_scfg] twin of [must_exit_in_at_singleton]. -/
theorem must_exit_in_at_cfg_singleton (cfg : SpuriousCfg) (segs : List Segment)
    (code : word) (c : config) :
    must_exit_in_at_cfg cfg segs [code] c ↔ must_exit_at_cfg cfg segs code c := by
  constructor
  · intro h
    induction h with
    | halted c code0 hh hin hk =>
      rw [List.mem_singleton] at hin
      rw [hin] at hh
      exact must_exit_at_cfg.halted c hh hk
    | running c hnone hprog hnoerr hnext ih =>
      exact must_exit_at_cfg.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)
  · intro h
    induction h with
    | halted c hh hk =>
      exact must_exit_in_at_cfg.halted c code hh (by simp) hk
    | running c hnone hprog hnoerr hnext ih =>
      exact must_exit_in_at_cfg.running c hnone hprog hnoerr (fun evs c' hss => ih evs c' hss)

theorem must_exit_in_scfg_singleton (cfg : SpuriousCfg) (code : word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    must_exit_in_scfg cfg [code] img lim en inp
      ↔ must_exit_with_scfg cfg code img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_cfg_singleton cfg segs code _

/-- A verdict under a configuration is a verdict under every SMALLER one,
    wherever the filter's question is answered along the way — the set
    form of [must_exit_at_cfg_mono], with [decided_from] the same
    premise. -/
theorem must_exit_in_at_cfg_mono (cfg1 cfg2 : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) (hle : cfg_le cfg1 cfg2)
    (hdec : decided_from cfg1 segs c) (h : must_exit_in_at_cfg cfg2 segs S c) :
    must_exit_in_at_cfg cfg1 segs S c := by
  induction h with
  | halted c code hh hin hk =>
    exact must_exit_in_at_cfg.halted c code hh hin hk
  | running c hnone hprog hnoerr hnext ih =>
    obtain ⟨evs, st, hss⟩ := hprog
    refine must_exit_in_at_cfg.running c hnone ?_ ?_ ?_
    · obtain ⟨ms, model⟩ := c
      exact sstep_cfg_progress segs cfg1 ms model evs st
        (fun x8 hsvc => hdec [] ⟨ms, model⟩ x8 (star.refl _) hsvc)
        (sstep_cfg_sub segs cfg2 ⟨ms, model⟩ evs st hss)
    · intro evs' herr
      exact hnoerr evs' (sstep_cfg_mono segs cfg1 cfg2 c evs' .SError hle herr)
    · intro evs' c' hss'
      exact ih evs' c' (sstep_cfg_mono segs cfg1 cfg2 c evs' (.SNext c') hle hss')
        (decided_from_step cfg1 cfg1 segs c evs' c' hdec hss')

theorem must_exit_in_at_cfg_of_must_exit_in_at (cfg : SpuriousCfg) (segs : List Segment)
    (S : List word) (c : config) (hdec : decided_from cfg segs c)
    (h : must_exit_in_at segs S c) :
    must_exit_in_at_cfg cfg segs S c := by
  refine must_exit_in_at_cfg_mono cfg may_fail_cfg segs S c
    (may_fail_cfg_greatest cfg) hdec ?_
  exact (must_exit_in_at_cfg_may_fail segs S c).mpr h

theorem must_exit_in_scfg_mono (cfg1 cfg2 : SpuriousCfg) (S : List word) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) (hle : cfg_le cfg1 cfg2)
    (hdec : run_decided cfg1 img lim en inp)
    (h : must_exit_in_scfg cfg2 S img lim en inp) :
    must_exit_in_scfg cfg1 S img lim en inp := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_in_at_cfg_mono cfg1 cfg2 segs S _ hle hdec h

theorem must_exit_in_scfg_of_must_exit_in (cfg : SpuriousCfg) (S : List word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hdec : run_decided cfg img lim en inp) (h : must_exit_in S img lim en inp) :
    must_exit_in_scfg cfg S img lim en inp := by
  refine must_exit_in_scfg_mono cfg may_fail_cfg S img lim en inp
    (may_fail_cfg_greatest cfg) hdec ?_
  exact (must_exit_in_scfg_may_fail S img lim en inp).mpr h

/-- The configured bridge from the single-code form: a binary proved to
    exit with one code under [cfg] satisfies the set form there for every
    set containing it. -/
theorem must_exit_with_scfg_in (cfg : SpuriousCfg) (S : List word) (code : word)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (hme : must_exit_with_scfg cfg code img lim en inp) (hin : code ∈ S) :
    must_exit_in_scfg cfg S img lim en inp := by
  refine must_exit_in_scfg_mono_set cfg [code] S img lim en inp ?_ ?_
  · intro code0 hin0
    rw [List.mem_singleton] at hin0
    rw [hin0]
    exact hin
  · exact (must_exit_in_scfg_singleton cfg code img lim en inp).mpr hme

end LinuxSem.EquivalenceDefinition.MustExit
