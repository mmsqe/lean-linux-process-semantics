/-
  * LinuxProcessSem.OmniRun — omni-big-step judgments over `Run.sstep`

  ADDITIVE, and a candidate for the trusted prefix: this file changes
  nothing in `Run` and redefines no existing name.  It adds three
  judgments over the one-step relation `Run.sstep` and proves each of
  `Run.run`'s observables equivalent to one of them, so a consumer may
  state an obligation in either form and move between the two through a
  proved `iff` (`bh_all_errors_iff`, `bh_errors_iff`, `bh_unmodeled_iff`
  and `bh_traces_iff` at the end of this file;
  `EquivalenceDefinition.OmniEquivalence` restates the theorem families
  the same way).

  ** The three judgments

  A maximal execution from a configuration `c` is a chain of `Run.sstep`
  transitions that either reaches a halted configuration, takes the error
  transition `Run.step_to.SError`, or never ends.  The first two are the
  finite `outcome`s a postcondition sees, together with the accumulated
  event trace:

  - `exec c Q` (inductive): EVERY maximal execution from `c` is finite,
    and its trace and outcome satisfy `Q`.  This is
    `Run.all_traces_error` and `MustExit.must_exit_at` generalised to an
    arbitrary postcondition; it delivers termination, the absence of
    errors and the shape of the trace in ONE induction.
  - `coexec c Q` (coinductive, the same constructors minus the progress
    premise): every maximal execution that ENDS satisfies `Q`; one that
    runs forever is unconstrained.  This is the safety reading, and it is
    what `Run.reaches_error` and `Run.reaches_unmodeled` turn into once
    negated (`bh_errors_iff`, `bh_unmodeled_iff`).
  - `cosafe c P` (coinductive): every finite PREFIX of every execution
    satisfies `P`.  This is what `Run.obs_trace` is, and it is the
    judgment trace equivalence lives in (`obs_equiv_iff_cosafe`).

  ** Why the pair `exec`/`coexec` alone cannot carry trace equivalence

  `exec` and `coexec` constrain only the executions that END: a diverging execution
  reaches no halted configuration and takes no error transition, so it contributes
  nothing to either judgment. Consequently "write a byte to stdout, then run forever"
  and "run forever" satisfy exactly the same `coexec` postconditions (both satisfy
  every one) and the same `exec` postconditions (neither satisfies any), although
  `Checks.Examples.write_then_diverge_vs_diverge` pins that `Equivalence.equiv`
  distinguishes them: the byte is observable as it happens. So this tree contains no
  such separating pair: the strictness claim is pinned result, not a checked claim
  here. Trace equivalence is agreement on all prefix-closed `cosafe` postconditions
  (`obs_equiv_iff_cosafe`); the other two judgments carry the exit-code, error and
  coverage facts.

  ** Outcomes carry the configuration

  `OHalt c'` is the halted configuration, whose exit code is
  `State.m_halted`; `OError c'` is the configuration FROM WHICH the error
  transition was taken.  Carrying `c'` is what lets a postcondition tell
  a modeled crash from the model giving up: `Run.unmodeled_at` is a
  predicate on that configuration, so `Equivalence.modeled` becomes the
  postcondition `covered` on the same judgment that
  `Equivalence.error_free` (`never_errors`) and `Run.all_traces_error`
  (`errors`) use.

  ** Stuck configurations read as silent

  `coexec` carries NO progress premise: a non-halted configuration with no transition
  at all satisfies `coexec c Q` for every `Q`, exactly as a diverging one does
  (`stuck_coexec_any`). `exec` KEEPS the progress premise, as `MustExit.must_exit_at`
  does, so `MustExit.must_exit_with` still fails on a run that gets stuck
  (`stuck_no_exec`). The progress-carrying variant of the coinductive judgment is
  kept as `coexec_progress`, with `coexec_progress_implies` showing it is the
  stronger of the two and `stuck_not_coexec_progress` showing where they differ, so
  that reversing this choice is a local change. `Checks.Omni.coexec_progress_iff` (in
  `Checks/Omni.v`, 1,330 lines) proves that on this tree the two coincide, because no
  non-halted configuration is stuck (`Checks.Omni.sstep_receptive`).
  **`Checks/Omni.lean` HAS LANDED** and proves the identification —
  `LinuxSem.Checks.Omni.coexec_progress_iff` — so the two judgments ARE
  identified in this tree, and the relation below is one direction of that iff. (That
  file still defers 103 of its 125 declarations, almost all stated over the unported
  `Checks/Examples.v` and `Checks/SpuriousCfg.v` fixtures; `coexec_progress_iff` is
  not one of them.) The earlier text said they were related in one direction by
  `coexec_progress_implies`, and the coincidence of the two on this tree remains a
  hypothesis, not a discharged claim.

  ** May-facts

  `Run.reaches_error` and `Run.reaches_unmodeled` are existential.  Their
  omni form is `omni_may`: SOME maximal execution, as the relation
  `mexec`, satisfies the postcondition.  `exec_realizes` and `exec_sound`
  relate the two sides: an `exec` judgment is realised by at least one
  maximal execution, and every maximal execution satisfies it.  The same
  relation is what turns an exact `exec` postcondition into the whole
  trace set (`exec_obs_iff`) — the "admits" half that an omni judgment
  does not deliver by itself.


  - COINDUCTION.  Lean 4 has no coinductive types, so the three
    coinductive judgments (`coexec`, `coexec_progress`, `cosafe`) are
    stated as their finite-unrolling limit: the conjunction, over every
    `Run.star` prefix, of the premises the coinductive constructors
    impose.  For `coexec` that is "every maximal execution that ENDS
    satisfies `Q`" (the halt clause at each reachable configuration, plus
    the error clause at each reachable configuration), for
    `coexec_progress` the same conjoined with "every reachable non-halted
    configuration can take a step", and for `cosafe` literally the
    reading, "every finite prefix of every execution satisfies `P`".
    Each is the greatest fixed point of the corresponding constructor
    functional — the judgments only have universal branching, so the
    limit of the finite unrollings is the gfp — hence extensionally the
  same predicate as coinductive type.  What changes is that the
    intro rules (`coexec_halt`, `coexec_step`, `coexec_progress_halt`,
    `coexec_progress_step`, `cosafe_intro`) are THEOREMS rather than
    constructors, and that a consumer who wants to DESTRUCT one uses
    `coexec_elim` (or `And.left` for `coexec_progress`, or the definition
    itself for `cosafe`) instead of `destruct`.  Every `cofix` proof
    becomes an ordinary proof here; no statement changes.
  - `outcome` keeps constructor names `OHalt`/`OError`; the
    inductive constructors of `mexec` and `exec` are `mexec.halt`,
    `mexec.error`, `mexec.next`, `exec.halt`, `exec.step`, following `all_traces_error.intro`
  in `Run.lean`.  `exec_cases` is this tree's eliminator for `exec`
    (`coexec_elim` plays the same role for the coinductive judgment, and
    the private `star_cases` is the same device for `Run.star`: `cases` on
    an indexed inductive reverts the hypotheses that mention its indices,
    which mid-proof is exactly what one wants to keep).
  - `Z` is `Int`, `bv 64` is `BitVec 64` (`word`), `list` is `List`,
  ``simp` beta` is beta reduction, `<>` is `≠`, `/\` is `∧`.
-/
import LinuxSem.LinuxProcessSem.Run

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.OmniRun

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType

/- =========================================================================
   Postconditions over the accumulated trace
   ========================================================================= -/

/-- How a maximal finite execution ends: halted, or erroring FROM the
    carried configuration. -/
inductive outcome where
  /-- The halted configuration.  Its exit code is `State.m_halted`. -/
  | OHalt (c : config)
  /-- The configuration FROM WHICH the error transition was taken. -/
  | OError (c : config)

/-- A postcondition: the accumulated trace and the outcome. -/
def post : Type := List event → outcome → Prop

/-- Is the outcome an error?  A `def` rather than a `match` at every use
    site, so that `errors` and `never_errors` below are literally
    complementary. -/
def is_error : outcome → Prop
  | .OHalt _ => False
  | .OError _ => True

/-- The postconditions the existing statement families use. -/
def errors : post := fun _ o => is_error o

/-- The postconditions the existing statement families use. -/
def never_errors : post := fun _ o => ¬ is_error o

/-- `Equivalence.modeled`'s postcondition: an error is allowed, but not
    one taken from a configuration the model declines to interpret. -/
def covered (segs : List Segment) : post :=
  fun _ o => match o with
             | .OHalt _ => True
             | .OError c => ¬ unmodeled_at segs c

/-- Its existential dual, for `Run.reaches_unmodeled`. -/
def uncovered (segs : List Segment) : post :=
  fun _ o => match o with
             | .OHalt _ => False
             | .OError c => unmodeled_at segs c

/-- `MustExit.must_exit_at`'s postcondition.  A DEATH BY SIGNAL IS NOT AN
    EXIT, and the second conjunct is what says so: a process killed by
    SIGABRT carries the signal number in `State.m_halted` -- that field is
    the "process is over" marker, and `State.m_killed` is what says which
    of the two ways it got there -- so without the conjunct this
    postcondition would read an abort as a verdict of 6.  The same
    conjunct sits on `MustExit.must_exit_at_halted` for the same reason. -/
def exits_with (code : word) : post :=
  fun _ o => match o with
             | .OHalt c => m_halted c.cfg_model = some code ∧
                           m_killed c.cfg_model = none
             | .OError _ => False

theorem never_errors_covered (segs : List Segment) (tr : List event) (o : outcome)
    (H : never_errors tr o) : covered segs tr o := by
  cases o with
  | OHalt c => exact True.intro
  | OError c => exact fun _ => H True.intro

theorem exits_with_never_errors (code : word) (tr : List event) (o : outcome)
    (H : exits_with code tr o) : never_errors tr o := by
  cases o with
  | OHalt c => exact fun h => h
  | OError c => exact fun _ => H

/-- Every `Run.sstep` leaves a non-halted configuration (every constructor
    carries `m_halted model = none`); the same fact as
    `MustExit.sstep_not_halted`, restated here because this file sits
    below `MustExit`. -/
theorem sstep_from_running (segs : List Segment) (c : config) (evs : List event)
    (st : step_to) (H : sstep segs c evs st) : m_halted c.cfg_model = none := by
  cases H <;> assumption

/-- The two shapes a `Run.star` can have, with the events and the
    intermediate configuration of a step exposed.  The port needs it for
    the same reason it needs `exec_cases`: `cases` on an indexed inductive
    reverts the hypotheses that mention its indices, which in the middle of
    a proof is exactly what a consumer wants to keep. -/
private theorem star_cases (segs : List Segment) (c : config) (tr : List event)
    (c' : config) (H : star segs c tr c') :
    (tr = [] ∧ c' = c) ∨
    (∃ evs tr0 c2, tr = evs ++ tr0 ∧ sstep segs c evs (.SNext c2) ∧
      star segs c2 tr0 c') := by
  cases H with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | step c1 evs c2 tr0 c3 h1 h2 => exact Or.inr ⟨evs, tr0, c2, rfl, h1, h2⟩

/- =========================================================================
   Maximal executions — the "may" side
   ========================================================================= -/

/-- One maximal finite execution: its trace and how it ended. -/
inductive mexec (segs : List Segment) : config → List event → outcome → Prop where
  /-- The execution is over: the configuration is halted, and nothing more
      happens. -/
  | halt (c : config) (hh : m_halted c.cfg_model ≠ none) :
      mexec segs c [] (.OHalt c)
  /-- The execution ends in the explicit error transition. -/
  | error (c : config) (evs : List event) (hss : sstep segs c evs .SError) :
      mexec segs c evs (.OError c)
  /-- The execution takes a successor step and goes on. -/
  | next (c : config) (evs : List event) (c' : config) (tr : List event) (o : outcome)
      (hss : sstep segs c evs (.SNext c')) (hm : mexec segs c' tr o) :
      mexec segs c (evs ++ tr) o

theorem star_mexec (segs : List Segment) (c : config) (tr : List event) (c' : config)
    (tr' : List event) (o : outcome) (Hstar : star segs c tr c')
    (Hm : mexec segs c' tr' o) : mexec segs c (tr ++ tr') o := by
  revert tr' o
  induction Hstar with
  | refl => intro tr' o hm; exact hm
  | step c1 evs c2 tr0 c3 hss hstar ih =>
    intro tr' o hm
    rw [List.append_assoc]
    exact mexec.next c1 evs c2 (tr0 ++ tr') o hss (ih tr' o hm)

theorem mexec_halt_star (segs : List Segment) (c : config) (tr : List event) (o : outcome)
    (Hm : mexec segs c tr o) :
    ∀ c', o = .OHalt c' → star segs c tr c' ∧ m_halted c'.cfg_model ≠ none := by
  induction Hm with
  | halt c hh =>
    intro c' heq
    cases heq
    exact ⟨star.refl c, hh⟩
  | error c evs hss =>
    intro c' heq
    cases heq
  | next c evs c' tr0 o hss hm ih =>
    intro c'' heq
    obtain ⟨hstar, hh⟩ := ih c'' heq
    exact ⟨star.step c evs c' tr0 c'' hss hstar, hh⟩

theorem mexec_error_star (segs : List Segment) (c : config) (tr : List event) (o : outcome)
    (Hm : mexec segs c tr o) :
    ∀ c', o = .OError c' →
      ∃ tr1 evs, tr = tr1 ++ evs ∧ star segs c tr1 c' ∧ sstep segs c' evs .SError := by
  induction Hm with
  | halt c hh =>
    intro c' heq
    cases heq
  | error c evs hss =>
    intro c' heq
    cases heq
    exact ⟨[], evs, rfl, star.refl c, hss⟩
  | next c evs c' tr0 o hss hm ih =>
    intro c'' heq
    obtain ⟨tr1, evs', heqtr, hstar, hss'⟩ := ih c'' heq
    exact ⟨evs ++ tr1, evs', by rw [heqtr, List.append_assoc],
           star.step c evs c' tr1 c'' hss hstar, hss'⟩

/-- `Run.reaches_error` is "some maximal execution errors". -/
theorem reaches_error_iff_may (segs : List Segment) (c : config) :
    reaches_error segs c ↔ ∃ tr o, mexec segs c tr o ∧ errors tr o := by
  constructor
  · intro ⟨tr, c2, evs, hstar, hss⟩
    exact ⟨tr ++ evs, .OError c2,
           star_mexec segs c tr c2 evs (.OError c2) hstar (mexec.error c2 evs hss),
           True.intro⟩
  · intro ⟨tr, o, hm, herr⟩
    cases o with
    | OHalt c' => exact herr.elim
    | OError c' =>
      obtain ⟨tr1, evs, -, hstar, hss⟩ := mexec_error_star segs c tr (.OError c') hm c' rfl
      exact ⟨tr1, c', evs, hstar, hss⟩

/-- `Run.reaches_unmodeled` is "some maximal execution errors from an
    uncovered configuration". -/
theorem reaches_unmodeled_iff_may (segs : List Segment) (c : config) :
    reaches_unmodeled segs c ↔ ∃ tr o, mexec segs c tr o ∧ uncovered segs tr o := by
  constructor
  · intro ⟨tr, c', hstar, hun⟩
    obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error segs c' hun
    exact ⟨tr ++ evs, .OError c', star_mexec segs c tr c' evs (.OError c') hstar
             (mexec.error c' evs hss), hun⟩
  · intro ⟨tr, o, hm, hun⟩
    cases o with
    | OHalt c' => exact hun.elim
    | OError c' =>
      obtain ⟨tr1, evs, -, hstar, -⟩ := mexec_error_star segs c tr (.OError c') hm c' rfl
      exact ⟨tr1, c', hstar, hun⟩

/- =========================================================================
   Terminating omni-exec (inductive)
   ========================================================================= -/

inductive exec (segs : List Segment) : config → post → Prop where
  /-- A halted configuration satisfies every postcondition that accepts the
      empty trace and the halted outcome. -/
  | halt (c : config) (Q : post) (hh : m_halted c.cfg_model ≠ none) (hQ : Q [] (.OHalt c)) :
      exec segs c Q
  /-- A non-halted configuration satisfies `Q` when it can step (the
      progress premise), every error transition satisfies `Q`, and every
      successor satisfies the shifted `Q`. -/
  | step (c : config) (Q : post) (hh : m_halted c.cfg_model = none)
      (hprog : ∃ evs st, sstep segs c evs st)
      (herr : ∀ evs, sstep segs c evs .SError → Q evs (.OError c))
      (hnext : ∀ evs c', sstep segs c evs (.SNext c') →
        exec segs c' (fun tr o => Q (evs ++ tr) o)) :
      exec segs c Q

/-- The two shapes an `exec` judgment can have, as an eliminator: this tree
    needs it because `cases` on `exec` would revert the hypotheses that
    mention the configuration, which in the middle of a proof is exactly
    what a consumer wants to keep. -/
theorem exec_cases (segs : List Segment) (c : config) (Q : post) (H : exec segs c Q) :
    (m_halted c.cfg_model ≠ none ∧ Q [] (.OHalt c)) ∨
    (m_halted c.cfg_model = none ∧ (∃ evs st, sstep segs c evs st) ∧
      (∀ evs, sstep segs c evs .SError → Q evs (.OError c)) ∧
      (∀ evs c', sstep segs c evs (.SNext c') →
        exec segs c' (fun tr o => Q (evs ++ tr) o))) := by
  cases H with
  | halt c Q hh hQ => exact Or.inl ⟨hh, hQ⟩
  | step c Q hh hprog herr hnext => exact Or.inr ⟨hh, hprog, herr, hnext⟩

/-- Consequence: the postcondition may be weakened. -/
theorem exec_conseq (segs : List Segment) (c : config) (Q Q' : post)
    (H : exec segs c Q) (Himp : ∀ tr o, Q tr o → Q' tr o) : exec segs c Q' := by
  revert Himp Q'
  induction H with
  | halt c Q hh hQ =>
    intro Q' Himp
    exact exec.halt c Q' hh (Himp [] (.OHalt c) hQ)
  | step c Q hh hprog herr hnext ih =>
    intro Q' Himp
    refine exec.step c Q' hh hprog (fun evs hss => Himp evs (.OError c) (herr evs hss)) ?_
    intro evs c' hss
    exact ih evs c' hss (fun t o => Q' (evs ++ t) o) (fun tr o h => Himp (evs ++ tr) o h)

/-- Halted configuration: the base case, as a lemma. -/
theorem exec_halted (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model ≠ none) (hQ : Q [] (.OHalt c)) : exec segs c Q :=
  exec.halt c Q hh hQ

/-- A configuration with exactly one transition: the shape a deterministic
    instruction step produces. -/
theorem exec_step_only (segs : List Segment) (c : config) (Q : post) (evs1 : List event)
    (c1 : config) (Hss : sstep segs c evs1 (.SNext c1))
    (Honly : ∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = .SNext c1)
    (Hex : exec segs c1 (fun tr o => Q (evs1 ++ tr) o)) : exec segs c Q := by
  refine exec.step c Q (sstep_from_running segs c evs1 (.SNext c1) Hss)
    ⟨evs1, .SNext c1, Hss⟩ ?_ ?_
  · intro evs hss
    obtain ⟨-, heq⟩ := Honly evs .SError hss
    cases heq
  · intro evs c' hss
    obtain ⟨heqevs, heqst⟩ := Honly evs (.SNext c') hss
    subst heqevs
    cases heqst
    exact Hex

/-- Step closure: an omni judgment survives any `Run.star` prefix, with the
    events already emitted prepended in the postcondition. -/
theorem exec_star (segs : List Segment) (c : config) (Q : post) (tr : List event)
    (c' : config) (Hex : exec segs c Q) (Hstar : star segs c tr c') :
    exec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  revert Hex Q
  induction Hstar with
  | refl =>
    intro Q Hex
    exact Hex
  | step c1 evs c2 tr0 c3 hss hstar ih =>
    intro Q Hex
    rcases exec_cases segs c1 Q Hex with ⟨hh, -⟩ | ⟨-, -, -, hnext⟩
    · exact absurd (sstep_from_running segs c1 evs (.SNext c2) hss) hh
    · refine exec_conseq segs c3 _ _ (ih _ (hnext evs c2 hss)) ?_
      intro t o h
      simpa [List.append_assoc] using h

/-- Soundness: every maximal execution of an `exec` judgment satisfies its
    postcondition ... -/
theorem exec_sound (segs : List Segment) (c : config) (Q : post) (Hex : exec segs c Q) :
    ∀ tr o, mexec segs c tr o → Q tr o := by
  intro tr o hm
  revert Hex Q
  induction hm with
  | halt c hh =>
    intro Q Hex
    rcases exec_cases segs c Q Hex with ⟨-, hQ⟩ | ⟨hh', -, -, -⟩
    · exact hQ
    · exact absurd hh' hh
  | error c evs hss =>
    intro Q Hex
    rcases exec_cases segs c Q Hex with ⟨hh', -⟩ | ⟨-, -, herr, -⟩
    · exact absurd (sstep_from_running segs c evs .SError hss) hh'
    · exact herr evs hss
  | next c evs c' tr0 o hss hm ih =>
    intro Q Hex
    rcases exec_cases segs c Q Hex with ⟨hh', -⟩ | ⟨-, -, -, hnext⟩
    · exact absurd (sstep_from_running segs c evs (.SNext c') hss) hh'
    · exact ih (fun t o => Q (evs ++ t) o) (hnext evs c' hss)

/-- ... and at least one maximal execution exists: the progress premise is
    what keeps `exec` from holding vacuously. -/
theorem exec_realizes (segs : List Segment) (c : config) (Q : post) (Hex : exec segs c Q) :
    ∃ tr o, mexec segs c tr o ∧ Q tr o := by
  induction Hex with
  | halt c Q hh hQ => exact ⟨[], .OHalt c, mexec.halt c hh, hQ⟩
  | step c Q hh hprog herr hnext ih =>
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SNext c' =>
      obtain ⟨tr, o, hm, hq⟩ := ih evs c' hss
      exact ⟨evs ++ tr, o, mexec.next c evs c' tr o hss hm, hq⟩
    | SError =>
      exact ⟨evs, .OError c, mexec.error c evs hss, herr evs hss⟩

/-- A stuck non-halted configuration satisfies no `exec`, whatever the
    postcondition: this is the reading `MustExit.must_exit_at` shares. -/
theorem stuck_no_exec (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none) (Hstuck : ∀ evs st, ¬ sstep segs c evs st) :
    ∀ Q, ¬ exec segs c Q := by
  intro Q Hex
  rcases exec_cases segs c Q Hex with ⟨hh, -⟩ | ⟨-, hprog, -, -⟩
  · exact hh Hh
  · obtain ⟨evs, st, hss⟩ := hprog
    exact Hstuck evs st hss

/-- The omni reading of `Run.all_traces_error`.  The right-to-left direction
    is stated over an arbitrary postcondition entailing an error, because
    `induction` on an `exec` whose postcondition is a concrete lambda
    abstracts it away. -/
theorem exec_errors_all_traces_error (segs : List Segment) (c : config) (Q : post)
    (H : exec segs c Q) (Himp : ∀ tr o, Q tr o → is_error o) :
    all_traces_error segs c := by
  revert Himp
  induction H with
  | halt c Q hh hQ =>
    intro Himp
    exact (Himp [] (.OHalt c) hQ).elim
  | step c Q hh hprog herr hnext ih =>
    intro Himp
    exact all_traces_error.intro c hprog
      (fun evs c' hss => ih evs c' hss (fun tr o hq => Himp (evs ++ tr) o hq))

theorem all_traces_error_iff (segs : List Segment) (c : config) :
    all_traces_error segs c ↔ exec segs c errors := by
  constructor
  · intro H
    induction H with
    | intro c hprog hnext ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      exact exec.step c errors (sstep_from_running segs c evs st hss) ⟨evs, st, hss⟩
        (fun evs' hss' => True.intro) (fun evs' c' hss' => ih evs' c' hss')
  · intro H
    exact exec_errors_all_traces_error segs c errors H (fun _ _ h => h)

/-- No maximal execution errors: the `OError` outcome is refuted. -/
theorem exec_no_error (segs : List Segment) (c : config) (Hex : exec segs c never_errors) :
    ¬ reaches_error segs c := by
  intro ⟨tr, c2, evs, hstar, hss⟩
  exact exec_sound segs c never_errors Hex _ _
    (star_mexec segs c tr c2 evs (.OError c2) hstar (mexec.error c2 evs hss)) True.intro

/-- An exact trace postcondition characterises the whole trace set: the
    "only" half is `exec_sound` along the prefix (`exec_star`), the
    "admits" half is the realised execution (`exec_realizes`). -/
theorem exec_obs_iff (segs : List Segment) (c : config) (full : List event)
    (Hex : exec segs c (fun tr o => tr = full ∧ ¬ is_error o)) :
    ∀ tr, obs_trace segs c tr ↔ is_prefix tr full := by
  intro tr
  constructor
  · intro ⟨tr', c', hstar, hp⟩
    have hex' : exec segs c' (fun t o => (tr' ++ t) = full ∧ ¬ is_error o) :=
      exec_star segs c (fun t o => t = full ∧ ¬ is_error o) tr' c' Hex hstar
    obtain ⟨tr'', o, -, hq⟩ := exec_realizes segs c' _ hex'
    cases o with
    | OHalt c'' =>
      obtain ⟨heq, -⟩ := hq
      rw [← heq]
      exact is_prefix_trans hp (is_prefix_app tr' tr'')
    | OError c'' => exact absurd True.intro hq.2
  · intro hp
    obtain ⟨tr', o, hm, hq⟩ := exec_realizes segs c _ Hex
    cases o with
    | OHalt c' =>
      obtain ⟨heq, -⟩ := hq
      obtain ⟨hstar, -⟩ := mexec_halt_star segs c tr' (.OHalt c') hm c' rfl
      exact ⟨tr', c', hstar, by rw [heq]; exact hp⟩
    | OError c' => exact absurd True.intro hq.2

/- =========================================================================
   Possibly-diverging omni-exec (coinductive) — no progress premise
   ========================================================================= -/

/-- `coinductive type coexec`, as its finite-unrolling limit: every
    maximal execution that ENDS satisfies `Q`, and a diverging or stuck one
    is unconstrained.  See the notes on coinduction; `coexec_halt`
    and `coexec_step` are the two intro rules. -/
def coexec (segs : List Segment) (c : config) (Q : post) : Prop :=
  ∀ (tr : List event) (c' : config), star segs c tr c' →
    (m_halted c'.cfg_model ≠ none → Q tr (.OHalt c')) ∧
    (∀ evs, sstep segs c' evs .SError → Q (tr ++ evs) (.OError c'))

/-- `coexec`'s halt constructor, as an intro rule. -/
theorem coexec_halt (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model ≠ none) (hQ : Q [] (.OHalt c)) : coexec segs c Q := by
  intro tr c' hstar
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, -, hss, -⟩
  · refine ⟨?_, ?_⟩
    · intro _
      rw [h1, h2]
      exact hQ
    · intro evs hss
      rw [h2] at hss
      exact absurd (sstep_from_running segs c evs .SError hss) hh
  · exact absurd (sstep_from_running segs c evs (.SNext c2) hss) hh

/-- `coexec`'s step constructor, as an intro rule. -/
theorem coexec_step (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model = none)
    (herr : ∀ evs, sstep segs c evs .SError → Q evs (.OError c))
    (hnext : ∀ evs c', sstep segs c evs (.SNext c') →
      coexec segs c' (fun tr o => Q (evs ++ tr) o)) :
    coexec segs c Q := by
  intro tr c' hstar
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, rfl, hss, hstar'⟩
  · refine ⟨?_, ?_⟩
    · intro hh'
      rw [h2] at hh'
      exact absurd hh hh'
    · intro evs hss
      rw [h2] at hss
      rw [h1, h2]
      exact herr evs hss
  · obtain ⟨g1, g2⟩ := hnext evs c2 hss tr0 c' hstar'
    exact ⟨g1, fun evs' hss' => by simpa [List.append_assoc] using g2 evs' hss'⟩

/-- The two halves of `coexec`, stated as an eliminator: this tree's
    `coexec` is not an inductive type, so a consumer that destructs one
    uses this instead of `cases`. -/
theorem coexec_elim (segs : List Segment) (c : config) (Q : post) (H : coexec segs c Q) :
    (m_halted c.cfg_model ≠ none ∧ Q [] (.OHalt c)) ∨
    (m_halted c.cfg_model = none ∧
      (∀ evs, sstep segs c evs .SError → Q evs (.OError c)) ∧
      (∀ evs c', sstep segs c evs (.SNext c') →
        coexec segs c' (fun tr o => Q (evs ++ tr) o))) := by
  obtain ⟨h1, h2⟩ := H [] c (star.refl c)
  by_cases hne : m_halted c.cfg_model = none
  · refine Or.inr ⟨hne, h2, ?_⟩
    intro evs c' hss tr c'' hstar
    obtain ⟨g1, g2⟩ := H (evs ++ tr) c'' (star.step c evs c' tr c'' hss hstar)
    exact ⟨g1, fun evs' hss' => by simpa [List.append_assoc] using g2 evs' hss'⟩
  · exact Or.inl ⟨hne, h1 hne⟩

theorem exec_coexec (segs : List Segment) (c : config) (Q : post) (H : exec segs c Q) :
    coexec segs c Q := by
  induction H with
  | halt c Q hh hQ => exact coexec_halt segs c Q hh hQ
  | step c Q hh hprog herr hnext ih =>
    exact coexec_step segs c Q hh herr (fun evs c' hss => ih evs c' hss)

theorem coexec_conseq (segs : List Segment) (c : config) (Q Q' : post)
    (H : coexec segs c Q) (Himp : ∀ tr o, Q tr o → Q' tr o) : coexec segs c Q' := by
  intro tr c' hstar
  obtain ⟨h1, h2⟩ := H tr c' hstar
  exact ⟨fun hh => Himp _ _ (h1 hh), fun evs hss => Himp _ _ (h2 evs hss)⟩

/-- The single-transition rule, as for `exec_step_only`. -/
theorem coexec_step_only (segs : List Segment) (c : config) (Q : post) (evs1 : List event)
    (c1 : config) (Hss : sstep segs c evs1 (.SNext c1))
    (Honly : ∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = .SNext c1)
    (Hco : coexec segs c1 (fun tr o => Q (evs1 ++ tr) o)) : coexec segs c Q := by
  intro tr c' hstar
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, rfl, hss, hstar'⟩
  · refine ⟨?_, ?_⟩
    · intro hh'
      rw [h2] at hh'
      exact absurd (sstep_from_running segs c evs1 (.SNext c1) Hss) hh'
    · intro evs hss
      rw [h2] at hss
      obtain ⟨-, heq⟩ := Honly evs .SError hss
      cases heq
  · obtain ⟨heqevs, heqst⟩ := Honly evs (.SNext c2) hss
    subst heqevs
    cases heqst
    obtain ⟨g1, g2⟩ := Hco tr0 c' hstar'
    exact ⟨g1, fun evs' hss' => by simpa [List.append_assoc] using g2 evs' hss'⟩

theorem coexec_star (segs : List Segment) (c : config) (Q : post) (tr : List event)
    (c' : config) (Hco : coexec segs c Q) (Hstar : star segs c tr c') :
    coexec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  intro tr0 c'' hstar0
  have hstar : star segs c (tr ++ tr0) c'' := star_trans segs c tr c' Hstar tr0 c'' hstar0
  obtain ⟨h1, h2⟩ := Hco (tr ++ tr0) c'' hstar
  exact ⟨h1, fun evs hss => by simpa [List.append_assoc] using h2 evs hss⟩

/-- Soundness: every maximal execution that ends satisfies the
    postcondition.  There is no realisation lemma: without a progress
    premise, nothing forces an execution to exist. -/
theorem coexec_sound (segs : List Segment) (c : config) (tr : List event) (o : outcome)
    (Hm : mexec segs c tr o) : ∀ Q, coexec segs c Q → Q tr o := by
  induction Hm with
  | halt c hh =>
    intro Q Hco
    exact (Hco [] c (star.refl c)).1 hh
  | error c evs hss =>
    intro Q Hco
    exact (Hco [] c (star.refl c)).2 evs hss
  | next c evs c' tr0 o hss hm ih =>
    intro Q Hco
    have hco' : coexec segs c' (fun t o => Q (evs ++ t) o) := by
      intro tr1 c'' hstar
      obtain ⟨g1, g2⟩ := Hco (evs ++ tr1) c'' (star.step c evs c' tr1 c'' hss hstar)
      exact ⟨g1, fun evs' hss' => by simpa [List.append_assoc] using g2 evs' hss'⟩
    exact ih _ hco'

/-- The silent reading of a stuck configuration, both ways: it satisfies
    every `coexec` ... -/
theorem stuck_coexec_any (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none) (Hstuck : ∀ evs st, ¬ sstep segs c evs st) :
    ∀ Q, coexec segs c Q :=
  fun Q => coexec_step segs c Q Hh
    (fun evs hss => absurd hss (Hstuck evs .SError))
    (fun evs c' hss => absurd hss (Hstuck evs (.SNext c')))

/-- Safety direction: `Equivalence.error_free` from the judgment ... -/
theorem coexec_no_error (segs : List Segment) (c : config) (Hco : coexec segs c never_errors) :
    ¬ reaches_error segs c := by
  intro ⟨tr, c2, evs, hstar, hss⟩
  exact coexec_sound segs c (tr ++ evs) (.OError c2)
    (star_mexec segs c tr c2 evs (.OError c2) hstar (mexec.error c2 evs hss))
    never_errors Hco True.intro

/-- ... and the converse, unconditional because a stuck configuration is
    silent on both sides. -/
theorem no_error_coexec (segs : List Segment) (c : config) (Hno : ¬ reaches_error segs c) :
    coexec segs c never_errors := by
  intro tr c' hstar
  exact ⟨fun _ => fun h => h,
         fun evs hss => absurd ⟨tr, c', evs, hstar, hss⟩ Hno⟩

theorem never_errors_iff (segs : List Segment) (c : config) :
    ¬ reaches_error segs c ↔ coexec segs c never_errors :=
  ⟨no_error_coexec segs c, coexec_no_error segs c⟩

/-- `Equivalence.modeled`, the same way: `covered` refutes an error taken
    from an uncovered configuration and tolerates every other. -/
theorem coexec_covered (segs : List Segment) (c : config) (Hco : coexec segs c (covered segs)) :
    ¬ reaches_unmodeled segs c := by
  intro ⟨tr, c', hstar, hun⟩
  obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error segs c' hun
  exact coexec_sound segs c (tr ++ evs) (.OError c')
    (star_mexec segs c tr c' evs (.OError c') hstar (mexec.error c' evs hss))
    (covered segs) Hco hun

theorem no_unmodeled_coexec (segs : List Segment) (c : config)
    (Hno : ¬ reaches_unmodeled segs c) : coexec segs c (covered segs) := by
  intro tr c' hstar
  exact ⟨fun _ => True.intro, fun evs _ hun => absurd ⟨tr, c', hstar, hun⟩ Hno⟩

theorem covered_iff (segs : List Segment) (c : config) :
    ¬ reaches_unmodeled segs c ↔ coexec segs c (covered segs) :=
  ⟨no_unmodeled_coexec segs c, coexec_covered segs c⟩

/- =========================================================================
   The progress-carrying alternative, kept for a local reversal
   ========================================================================= -/

/-- `coexec` with the progress premise of `exec` and
    `MustExit.must_exit_at`: a stuck configuration REFUTES it.  Not used by
    any compat lemma; see the header.  Stated, like the other two
    coinductive judgments, as the finite-unrolling limit of
  `coexec_progress`. -/
def coexec_progress (segs : List Segment) (c : config) (Q : post) : Prop :=
  coexec segs c Q ∧
  ∀ (tr : List event) (c' : config), star segs c tr c' → m_halted c'.cfg_model = none →
    ∃ evs st, sstep segs c' evs st

/-- `coexec_progress`'s halt constructor, as an intro rule. -/
theorem coexec_progress_halt (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model ≠ none) (hQ : Q [] (.OHalt c)) :
    coexec_progress segs c Q := by
  refine ⟨coexec_halt segs c Q hh hQ, ?_⟩
  intro tr c' hstar hh'
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, -, hss, -⟩
  · rw [h2] at hh'
    exact absurd hh' hh
  · exact absurd (sstep_from_running segs c evs (.SNext c2) hss) hh

/-- `coexec_progress`'s step constructor, as an intro rule. -/
theorem coexec_progress_step (segs : List Segment) (c : config) (Q : post)
    (hh : m_halted c.cfg_model = none) (hprog : ∃ evs st, sstep segs c evs st)
    (herr : ∀ evs, sstep segs c evs .SError → Q evs (.OError c))
    (hnext : ∀ evs c', sstep segs c evs (.SNext c') →
      coexec_progress segs c' (fun tr o => Q (evs ++ tr) o)) :
    coexec_progress segs c Q := by
  refine ⟨coexec_step segs c Q hh herr (fun evs c' hss => (hnext evs c' hss).1), ?_⟩
  intro tr c' hstar hh'
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, -, hss, hstar'⟩
  · rw [h2] at hh'
    rw [h2]
    exact hprog
  · exact (hnext evs c2 hss).2 tr0 c' hstar' hh'

theorem coexec_progress_implies (segs : List Segment) (c : config) (Q : post)
    (H : coexec_progress segs c Q) : coexec segs c Q :=
  H.1

/-- Where the two readings differ: a stuck configuration. -/
theorem stuck_not_coexec_progress (segs : List Segment) (c : config)
    (Hh : m_halted c.cfg_model = none) (Hstuck : ∀ evs st, ¬ sstep segs c evs st) :
    ∀ Q, ¬ coexec_progress segs c Q := by
  intro Q Hco
  obtain ⟨evs, st, hss⟩ := Hco.2 [] c (star.refl c) Hh
  exact Hstuck evs st hss

/- =========================================================================
   Prefix safety (coinductive) — what `Run.obs_trace` is
   ========================================================================= -/

/-- Every finite prefix of every execution satisfies `P`.  No progress
    premise and no error clause: a prefix property is a pure safety
    property, and this is the judgment trace equivalence lives in.
  Stated it coinductively; this tree states own
    reading of it, literally. -/
def cosafe (segs : List Segment) (c : config) (P : List event → Prop) : Prop :=
  ∀ (tr : List event) (c' : config), star segs c tr c' → P tr

/-- `cosafe`'s constructor, as an intro rule. -/
theorem cosafe_intro (segs : List Segment) (c : config) (P : List event → Prop)
    (hP : P [])
    (hnext : ∀ evs c', sstep segs c evs (.SNext c') →
      cosafe segs c' (fun tr => P (evs ++ tr))) :
    cosafe segs c P := by
  intro tr c' hstar
  rcases star_cases segs c tr c' hstar with ⟨h1, h2⟩ | ⟨evs, tr0, c2, rfl, hss, hstar'⟩
  · rw [h1]
    exact hP
  · exact hnext evs c2 hss tr0 c' hstar'

theorem cosafe_star (segs : List Segment) (c : config) (P : List event → Prop)
    (tr : List event) (c' : config) (Hsafe : cosafe segs c P) (Hstar : star segs c tr c') :
    P tr :=
  Hsafe tr c' Hstar

theorem star_cosafe (segs : List Segment) (c : config) (P : List event → Prop)
    (Hall : ∀ tr c', star segs c tr c' → P tr) : cosafe segs c P :=
  Hall

def prefix_closed (P : List event → Prop) : Prop :=
  ∀ tr tr', P tr → is_prefix tr' tr → P tr'

theorem obs_trace_is_prefix_closed (segs : List Segment) (c : config) :
    prefix_closed (obs_trace segs c) :=
  fun _ _ Ht Hp => obs_trace_prefix_closed segs c _ _ Ht Hp

/-- `Run.obs_trace`'s universal dual: on a prefix-closed `P`, "every
    observable trace satisfies `P`" is exactly `cosafe`. -/
theorem cosafe_obs_iff (segs : List Segment) (c : config) (P : List event → Prop)
    (Hpc : prefix_closed P) :
    cosafe segs c P ↔ ∀ tr, obs_trace segs c tr → P tr := by
  constructor
  · intro Hsafe tr ⟨tr', c', hstar, hp⟩
    exact Hpc tr' tr (cosafe_star segs c P tr' c' Hsafe hstar) hp
  · intro Hall
    exact fun tr c' hstar => Hall tr ⟨tr, c', hstar, is_prefix_refl tr⟩

/- =========================================================================
   The refinement pair, and trace equivalence as cosafe agreement
   ========================================================================= -/

/-- The refinement pair: each side's trace set is a prefix postcondition the
    other side satisfies.  Stated for two images, since the two runs of an
    equivalence load different segments. -/
theorem obs_equiv_iff_refinement (segs1 : List Segment) (c1 : config)
    (segs2 : List Segment) (c2 : config) :
    (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr)
    ↔ (cosafe segs1 c1 (obs_trace segs2 c2) ∧ cosafe segs2 c2 (obs_trace segs1 c1)) := by
  constructor
  · intro Heq
    exact ⟨fun tr c' hstar => (Heq tr).mp ⟨tr, c', hstar, is_prefix_refl tr⟩,
           fun tr c' hstar => (Heq tr).mpr ⟨tr, c', hstar, is_prefix_refl tr⟩⟩
  · intro ⟨H12, H21⟩ tr
    constructor
    · intro ⟨tr', c', hstar, hp⟩
      exact obs_trace_prefix_closed segs2 c2 _ _ (H12 tr' c' hstar) hp
    · intro ⟨tr', c', hstar, hp⟩
      exact obs_trace_prefix_closed segs1 c1 _ _ (H21 tr' c' hstar) hp

/-- Trace-set equality is "the two configurations satisfy the same prefix
    postconditions" — the omni statement of `Equivalence.trace_equiv`.
    Both directions are constructive; the hard direction instantiates `P`
    with the other side's trace set. -/
theorem obs_equiv_iff_cosafe (segs1 : List Segment) (c1 : config)
    (segs2 : List Segment) (c2 : config) :
    (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr)
    ↔ (∀ P, prefix_closed P → (cosafe segs1 c1 P ↔ cosafe segs2 c2 P)) := by
  constructor
  · intro Heq P Hpc
    rw [cosafe_obs_iff segs1 c1 P Hpc, cosafe_obs_iff segs2 c2 P Hpc]
    constructor
    · intro Hall tr hobs
      exact Hall tr ((Heq tr).mpr hobs)
    · intro Hall tr hobs
      exact Hall tr ((Heq tr).mp hobs)
  · intro Hall
    refine (obs_equiv_iff_refinement segs1 c1 segs2 c2).mpr ⟨?_, ?_⟩
    · exact (Hall _ (obs_trace_is_prefix_closed segs2 c2)).mpr
        (fun tr c' hstar => ⟨tr, c', hstar, is_prefix_refl tr⟩)
    · exact (Hall _ (obs_trace_is_prefix_closed segs1 c1)).mp
        (fun tr c' hstar => ⟨tr, c', hstar, is_prefix_refl tr⟩)

/- =========================================================================
   Run-level judgments: the three argument groups of `Run.run`
   ========================================================================= -/

/-- Written as a MATCH on the image and the `execve` entry for the same
    reason `Run.run` and `MustExit.must_exit_with` are: a proof unfolding one
    with `simp [omni_run]` gets the underlying `Run.init_config` application
    back as soon as those two arguments are concrete records, and every one
    of them speaks about the SAME configuration `Run.run` does. -/
def omni_run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
      exec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) Q

def omni_corun (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
      coexec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) Q

def omni_cosafe (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (P : List event → Prop) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
      cosafe segs (init_config segs pc ph sp brk0 mbase rnd lim inp) P

/-- SOME maximal execution satisfies `Q`: the existential twin. -/
def omni_may (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
      ∃ tr o, mexec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr o ∧ Q tr o

/- =========================================================================
   Compat: the four fields of `Run.run`, each unconditional
   ========================================================================= -/

theorem bh_all_errors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_all_errors ↔ omni_run img lim en inp errors := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact all_traces_error_iff segs _

theorem bh_errors_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (run img lim en inp).bh_errors ↔ omni_corun img lim en inp never_errors := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact never_errors_iff segs _

theorem bh_errors_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_errors ↔ omni_may img lim en inp errors := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact reaches_error_iff_may segs _

theorem bh_unmodeled_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ (run img lim en inp).bh_unmodeled ↔
      omni_corun img lim en inp (covered img.img_segments) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact covered_iff segs _

theorem bh_unmodeled_may_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    (run img lim en inp).bh_unmodeled ↔
      omni_may img lim en inp (uncovered img.img_segments) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact reaches_unmodeled_iff_may segs _

/-- Trace-set equality of two runs is agreement on every prefix-closed
    postcondition; `OmniEquivalence.trace_equiv_iff_omni` restates it
    through `Equivalence.trace_equiv`. -/
theorem bh_traces_iff (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) :
    (∀ tr, (run img1 lim1 en1 inp).bh_traces tr ↔ (run img2 lim2 en2 inp).bh_traces tr)
    ↔ (∀ P, prefix_closed P →
         (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P)) := by
  obtain ⟨segs1, pc1, ph1⟩ := img1
  obtain ⟨sp1, brk1, mb1, rnd1⟩ := en1
  obtain ⟨segs2, pc2, ph2⟩ := img2
  obtain ⟨sp2, brk2, mb2, rnd2⟩ := en2
  exact obs_equiv_iff_cosafe segs1 _ segs2 _



end LinuxSem.LinuxProcessSem.OmniRun
