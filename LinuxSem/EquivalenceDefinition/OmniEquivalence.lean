/-
  * EquivalenceDefinition.OmniEquivalence — the theorem families, restated through `OmniRun`

  ADDITIVE.  Every definition in `Equivalence`, `MustExit` and
  `Classifier` keeps its text; this file gives each statement family
  an `omni_*` twin built from the judgments of `OmniRun` and proves
  the two equivalent, unconditionally and without classical axioms:

    `must_exit_with_iff`                  `MustExit.must_exit_with`
    `error_free_iff`, `modeled_iff`       `Equivalence.error_free`, `Equivalence.modeled`
    `trace_equiv_iff_omni`                `Equivalence.trace_equiv` on two runs
    `equiv_iff`, `strong_equiv_iff`       `Equivalence.equiv`, `Equivalence.strong_equiv`
    `strong_universal_iff`                `Equivalence.strong_universal_T`
    `strong_equiv_error_free_iff`,
    `strong_universal_error_free_iff`     the error-free shapes
    `agree_iff`, `good_input_iff`         `Classifier.agree`, `Classifier.good_input`
    `decides_iff`, `classifier_total_iff` `Classifier.decides`, `Classifier.classifier_total_T`

  The checker-visible names (`Equivalence.SPEC`,
  `Equivalence.SPEC_ERROR_FREE`, `Equivalence.strong_universal_T`,...) are untouched; `OMNI_SPEC` and `OMNI_SPEC_ERROR_FREE` are new
  module types with the same parameter shape, and the functors
  `OmniOfSpec` / `SpecOfOmni` show how a proof in either shape is
  ascribed to the other's module type through the `iff`.

  ** How the families read in omni form

  - The escape `Run.bh_all_errors` is `omni_run … errors`: every
    maximal execution ends in an error.
  - `Equivalence.error_free` is `omni_corun … never_errors`: no
    maximal execution that ends ends in an error.
  - `Equivalence.modeled` is `omni_corun … covered`: an error may end
    an execution, but not one taken from a configuration
    `Run.unmodeled_at`.
  - `Equivalence.trace_equiv` of two runs is `omni_trace_equiv`:
    agreement on every prefix-closed `OmniRun.cosafe` postcondition
    (`omni_trace_equiv_refinement` is the refinement-pair
    introduction rule).
  - `MustExit.must_exit_with code` is `omni_run … (exits_with code)`.
  - `Classifier.agree`'s existential error facts are `omni_may`:
    some maximal execution ends the named way.

  `Equivalence.strong_equiv`'s shape — the `modeled` conjunct BESIDE
  `equiv`, never as an antecedent — is kept verbatim in
  `omni_strong_equiv`; so is every quantifier shell (`Run.valid_entry`
  per image, `Run.valid_input` on the shared input, the role budgets
  `State.source_alloc_limit` / `State.target_alloc_limit`, the
  per-entry existentials of `Classifier.agree`).


  - `Section Spec`'s two `Variable`s become EXPLICIT LEADING
    PARAMETERS, exactly as `Run.lean` and `OmniRun.lean` do for their
    sections: `omni_strong_equiv` takes `source_image` and
    `target_image` first, so every statement below reads in post-section
    form.
  -  module types `OMNI_SPEC` / `OMNI_SPEC_ERROR_FREE` are Lean
    `structure`s with one field each — the same shape
    `Equivalence.SPEC` / `Equivalence.SPEC_ERROR_FREE` have in this
    tree — and the four functors (`OmniOfSpec`, `SpecOfOmni`,
    `OmniOfSpecErrorFree`, `SpecErrorFreeOfOmni`) are `def`s
    returning that structure, with `proj1`/`proj2` becoming
    `Iff.mp`/`Iff.mpr`.
  - `OmniRun`'s coinductive judgments are its finite-unrolling
    readings (see that file's header), so every `cofix`-free proof
  carries over as an ordinary proof.  `simp [omni_run …]`
    becomes `obtain ⟨…⟩ := img` plus the record's projections
    reducing, which is what the lemmas below do.
  - `Z` is `Int`, `list` is `List`, `<>` is `≠`, `/\` is `∧`; `post`,
    `outcome`, `prefix_closed`, `errors`, `never_errors`, `covered`,
    `uncovered` and `exits_with` are `OmniRun`'s.
  - "Without classical axioms" is claim about its own
    proofs.  In this tree `#print axioms` on any statement mentioning
    `Run.sstep` or `Run.unmodeled_at` lists Lean's standard `propext`,
    `Classical.choice` and `Quot.sound`, which those definitions already
    carry; this file adds no postulate of its own (the purely logical
    `ex_and_iff` is free of extra postulates), and no proof hole / `admit` / extra postulate /
    `unsafe` is used anywhere in it.
-/
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.LinuxProcessSem.OmniRun

open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.OmniEquivalence

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.LinuxProcessSem.OmniRun
open behavior

/- =========================================================================
   Compat: `MustExit.must_exit_at` / `must_exit_with`
   ========================================================================= -/

/-- The right-to-left direction is stated over an arbitrary
    postcondition entailing `exits_with`, because induction on an
    `exec` whose postcondition is a concrete term abstracts it away. -/
theorem exec_exits_must_exit_at (segs : List Segment) (code : word) (c : config) (Q : post)
    (H : exec segs c Q) (Himp : ∀ tr o, Q tr o → exits_with code tr o) :
    must_exit_at segs code c := by
  revert Himp
  induction H with
  | halt c Q hh hQ =>
    intro Himp
    obtain ⟨hex, hk⟩ := Himp [] (.OHalt c) hQ
    exact must_exit_at.halted c hex hk
  | step c Q hh hprog herr hnext ih =>
    intro Himp
    refine must_exit_at.running c hh hprog (fun evs hss => ?_) (fun evs c' hss => ?_)
    · exact Himp evs (.OError c) (herr evs hss)
    · exact ih evs c' hss (fun tr o hq => Himp (evs ++ tr) o hq)

theorem must_exit_at_iff (segs : List Segment) (code : word) (c : config) :
    must_exit_at segs code c ↔ exec segs c (exits_with code) := by
  constructor
  · intro H
    induction H with
    | halted c hh hk =>
      exact exec.halt c (exits_with code) (by simp [hh]) ⟨hh, hk⟩
    | running c hnone hprog hnoerr hnext ih =>
      exact exec.step c (exits_with code) hnone hprog
        (fun evs hss => absurd hss (hnoerr evs))
        (fun evs c' hss => ih evs c' hss)
  · intro H
    exact exec_exits_must_exit_at segs code c (exits_with code) H (fun _ _ h => h)

theorem must_exit_with_iff (code : word) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) :
    must_exit_with code img lim en inp ↔ omni_run img lim en inp (exits_with code) := by
  obtain ⟨segs, pc, ph⟩ := img
  obtain ⟨sp, brk0, mbase, rnd⟩ := en
  exact must_exit_at_iff segs code _

/- =========================================================================
   Compat: the behaviour-level predicates of `Equivalence`
   ========================================================================= -/

theorem error_free_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    error_free (run img lim en inp) ↔ omni_corun img lim en inp never_errors :=
  bh_errors_iff img lim en inp

theorem modeled_iff (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    modeled (run img lim en inp)
    ↔ omni_corun img lim en inp (covered (img.img_segments)) :=
  bh_unmodeled_iff img lim en inp

/-- Trace equivalence of two runs is agreement on every prefix-closed
    omni postcondition. -/
def omni_trace_equiv (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) : Prop :=
  ∀ P, prefix_closed P →
    (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P)

theorem trace_equiv_iff_omni (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) :
    trace_equiv (bh_traces (run img1 lim1 en1 inp)) (bh_traces (run img2 lim2 en2 inp))
    ↔ omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp :=
  bh_traces_iff img1 lim1 en1 img2 lim2 en2 inp

/-- The introduction rule: each run's trace set is a prefix
    postcondition the other run satisfies (a refinement in each
    direction). -/
theorem omni_trace_equiv_refinement (img1 : Image) (lim1 : Int) (en1 : ExecEntry)
    (img2 : Image) (lim2 : Int) (en2 : ExecEntry) (inp : ProcInput) :
    omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp
    ↔ (omni_cosafe img1 lim1 en1 inp (bh_traces (run img2 lim2 en2 inp))
       ∧ omni_cosafe img2 lim2 en2 inp (bh_traces (run img1 lim1 en1 inp))) := by
  obtain ⟨segs1, pc1, ph1⟩ := img1
  obtain ⟨sp1, brk1, mb1, rnd1⟩ := en1
  obtain ⟨segs2, pc2, ph2⟩ := img2
  obtain ⟨sp2, brk2, mb2, rnd2⟩ := en2
  constructor
  · intro H
    exact (obs_equiv_iff_refinement segs1 _ segs2 _).mp
      ((obs_equiv_iff_cosafe segs1 _ segs2 _).mpr H)
  · intro H
    exact (obs_equiv_iff_cosafe segs1 _ segs2 _).mp
      ((obs_equiv_iff_refinement segs1 _ segs2 _).mpr H)

/-- `Equivalence.equiv` on two runs: the escape, or trace agreement
    with an error-free target. -/
def omni_equiv (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput) : Prop :=
  omni_run imgS limS enS inp errors
  ∨ (omni_trace_equiv imgS limS enS imgT limT enT inp
     ∧ omni_corun imgT limT enT inp never_errors)

theorem equiv_iff (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput) :
    equiv (run imgS limS enS inp) (run imgT limT enT inp)
    ↔ omni_equiv imgS limS enS imgT limT enT inp := by
  unfold equiv omni_equiv
  rw [bh_all_errors_iff, trace_equiv_iff_omni, bh_errors_iff]

/-- The two policy consequences, in omni form. -/
theorem omni_all_errors_equiv_any (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput)
    (H : omni_run imgS limS enS inp errors) :
    omni_equiv imgS limS enS imgT limT enT inp :=
  Or.inl H

theorem omni_equiv_target_never_errors (imgS : Image) (limS : Int) (enS : ExecEntry)
    (imgT : Image) (limT : Int) (enT : ExecEntry) (inp : ProcInput)
    (H : omni_equiv imgS limS enS imgT limT enT inp)
    (Hsurvives : ¬ omni_run imgS limS enS inp errors) :
    omni_corun imgT limT enT inp never_errors := by
  rcases H with Hall | ⟨_, Hnoerr⟩
  · exact absurd Hall Hsurvives
  · exact Hnoerr

/- =========================================================================
   The theorem statements, parameterised over the two images
   ========================================================================= -/

/-- `Equivalence.strong_equiv`, with `modeled` as `covered` BESIDE the
    equivalence — the same conjunct shape; see the comment on
    `Equivalence.modeled` for why it is not an antecedent. -/
def omni_strong_equiv (source_image target_image : Image) (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_corun source_image source_alloc_limit en_source inp
    (covered source_image.img_segments)
  ∧ omni_equiv source_image source_alloc_limit en_source
                target_image target_alloc_limit en_target inp

theorem strong_equiv_iff (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) :
    strong_equiv source_image target_image en_source en_target inp
    ↔ omni_strong_equiv source_image target_image en_source en_target inp := by
  unfold strong_equiv omni_strong_equiv
  rw [modeled_iff, equiv_iff]

def omni_strong_universal_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp →
    valid_entry target_image en_target inp →
    valid_input inp →
    omni_strong_equiv source_image target_image en_source en_target inp

theorem strong_universal_iff (source_image target_image : Image) :
    strong_universal_T source_image target_image
    ↔ omni_strong_universal_T source_image target_image := by
  unfold strong_universal_T omni_strong_universal_T
  constructor
  · intro H en_source en_target inp Hs Ht Hi
    exact (strong_equiv_iff source_image target_image en_source en_target inp).mp
      (H en_source en_target inp Hs Ht Hi)
  · intro H en_source en_target inp Hs Ht Hi
    exact (strong_equiv_iff source_image target_image en_source en_target inp).mpr
      (H en_source en_target inp Hs Ht Hi)

/-- `Equivalence.strong_equiv_error_free`: both runs never error, and
    the trace sets agree. -/
def omni_strong_equiv_error_free (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  omni_corun source_image source_alloc_limit en_source inp never_errors
  ∧ omni_corun target_image target_alloc_limit en_target inp never_errors
  ∧ omni_trace_equiv source_image source_alloc_limit en_source
                      target_image target_alloc_limit en_target inp

theorem strong_equiv_error_free_iff (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput) :
    strong_equiv_error_free source_image target_image en_source en_target inp
    ↔ omni_strong_equiv_error_free source_image target_image en_source en_target inp := by
  unfold strong_equiv_error_free omni_strong_equiv_error_free
  rw [error_free_iff, error_free_iff, trace_equiv_iff_omni]

def omni_strong_universal_error_free_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp →
    valid_entry target_image en_target inp →
    valid_input inp →
    omni_strong_equiv_error_free source_image target_image en_source en_target inp

theorem strong_universal_error_free_iff (source_image target_image : Image) :
    strong_universal_error_free_T source_image target_image
    ↔ omni_strong_universal_error_free_T source_image target_image := by
  unfold strong_universal_error_free_T omni_strong_universal_error_free_T
  constructor
  · intro H en_source en_target inp Hs Ht Hi
    exact (strong_equiv_error_free_iff source_image target_image en_source en_target inp).mp
      (H en_source en_target inp Hs Ht Hi)
  · intro H en_source en_target inp Hs Ht Hi
    exact (strong_equiv_error_free_iff source_image target_image en_source en_target inp).mpr
      (H en_source en_target inp Hs Ht Hi)

/-- The error-free shape is the stronger one, proved in omni terms:
    `never_errors` entails `covered`, and the right disjunct of
    `omni_equiv` is exactly its last two conjuncts. -/
theorem omni_strong_equiv_error_free_implies (source_image target_image : Image)
    (en_source en_target : ExecEntry) (inp : ProcInput)
    (H : omni_strong_equiv_error_free source_image target_image en_source en_target inp) :
    omni_strong_equiv source_image target_image en_source en_target inp := by
  obtain ⟨Hsrc, Htgt, Htr⟩ := H
  refine ⟨?_, Or.inr ⟨Htr, Htgt⟩⟩
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  exact coexec_conseq segs _ never_errors (covered segs) Hsrc (never_errors_covered segs)

theorem omni_strong_universal_error_free_implies (source_image target_image : Image)
    (H : omni_strong_universal_error_free_T source_image target_image) :
    omni_strong_universal_T source_image target_image := by
  intro en_source en_target inp Hs Ht Hi
  exact omni_strong_equiv_error_free_implies source_image target_image en_source en_target inp
    (H en_source en_target inp Hs Ht Hi)

/-- Where the two shapes diverge, as a refutation and in omni terms: an
    `exec … errors` judgment is realised by SOME maximal execution
    (`OmniRun.exec_realizes`), which ends in an error, and
    `coexec … never_errors` forbids exactly that (`OmniRun.coexec_sound`).
    The escape is therefore inconsistent with the error-free shape, not
    merely unused by it. -/
theorem omni_strong_equiv_error_free_no_all_errors_escape
    (source_image target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput)
    (Hall : omni_run source_image source_alloc_limit en_source inp errors) :
    ¬ omni_strong_equiv_error_free source_image target_image en_source en_target inp := by
  intro ⟨Hsrc, _, _⟩
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs _ errors Hall
  exact (coexec_sound segs _ tr o Hm never_errors Hsrc) Herr

/-- One erroring maximal execution at one valid triple refutes the
    whole error-free universal statement. -/
theorem omni_strong_universal_error_free_refuted_by_source_error
    (source_image target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput)
    (Hs : valid_entry source_image en_source inp)
    (Ht : valid_entry target_image en_target inp)
    (Hi : valid_input inp)
    (Hmay : omni_may source_image source_alloc_limit en_source inp errors) :
    ¬ omni_strong_universal_error_free_T source_image target_image := by
  intro H
  obtain ⟨Hsrc, _, _⟩ := H en_source en_target inp Hs Ht Hi
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  obtain ⟨tr, o, Hm, Herr⟩ := Hmay
  exact (coexec_sound segs _ tr o Hm never_errors Hsrc) Herr

/- =========================================================================
   OMNI_SPEC / OMNI_SPEC_ERROR_FREE — the module types, and the bridges
   ========================================================================= -/

/-- Same parameter shape as `Equivalence.SPEC`; only the statement is
    the omni one.  `Equivalence.IMAGE_WF` is unchanged and is still
    ascribed alongside, for the reason given there. -/
structure OMNI_SPEC (Source Target : MemImage) where
  omni_strong_universal : omni_strong_universal_T
    (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
    (mkImage Target.loaded_segments Target.init_pc Target.phdrs)

/-- Same shape, for the error-free statement. -/
structure OMNI_SPEC_ERROR_FREE (Source Target : MemImage) where
  omni_strong_universal_error_free : omni_strong_universal_error_free_T
    (mkImage Source.loaded_segments Source.init_pc Source.phdrs)
    (mkImage Target.loaded_segments Target.init_pc Target.phdrs)

/-- A proof in the legacy shape ascribes to the omni module type, and
    conversely: this is the whole consumer story.  A proof written
    against `omni_strong_universal_T` discharges `Equivalence.SPEC` by
    `SpecOfOmni`, so the checker a consumer pins need not change. -/
theorem OmniOfSpec (Source Target : MemImage) (S : SPEC Source Target) :
    OMNI_SPEC Source Target where
  omni_strong_universal :=
    (strong_universal_iff _ _).mp S.strong_universal

theorem SpecOfOmni (Source Target : MemImage) (O : OMNI_SPEC Source Target) :
    SPEC Source Target where
  strong_universal :=
    (strong_universal_iff _ _).mpr O.omni_strong_universal

theorem OmniOfSpecErrorFree (Source Target : MemImage) (S : SPEC_ERROR_FREE Source Target) :
    OMNI_SPEC_ERROR_FREE Source Target where
  omni_strong_universal_error_free :=
    (strong_universal_error_free_iff _ _).mp S.strong_universal_error_free

theorem SpecErrorFreeOfOmni (Source Target : MemImage) (O : OMNI_SPEC_ERROR_FREE Source Target) :
    SPEC_ERROR_FREE Source Target where
  strong_universal_error_free :=
    (strong_universal_error_free_iff _ _).mpr O.omni_strong_universal_error_free

/- =========================================================================
   Compat: the classifier families
   ========================================================================= -/

theorem ex_and_iff {A : Type} {V P P' : A → Prop} (H : ∀ x, P x ↔ P' x) :
    ((∃ x, V x ∧ P x) ↔ (∃ x, V x ∧ P' x)) := by
  constructor
  · rintro ⟨x, Hv, Hp⟩
    exact ⟨x, Hv, (H x).mp Hp⟩
  · rintro ⟨x, Hv, Hp⟩
    exact ⟨x, Hv, (H x).mpr Hp⟩

/-- `Classifier.agree`: trace agreement at every valid entry pair, and
    the three per-entry existential facts — may-error, must-error,
    may-leave-the-model — matched across the two images. -/
def omni_agree (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY,
     valid_entry X enX inp → valid_entry Y enY inp →
     omni_trace_equiv X lim enX Y lim enY inp)
  ∧ ((∃ en, valid_entry X en inp ∧ omni_may X lim en inp errors)
      ↔ (∃ en, valid_entry Y en inp ∧ omni_may Y lim en inp errors))
  ∧ ((∃ en, valid_entry X en inp ∧ omni_run X lim en inp errors)
      ↔ (∃ en, valid_entry Y en inp ∧ omni_run Y lim en inp errors))
  ∧ ((∃ en, valid_entry X en inp
                  ∧ omni_may X lim en inp (uncovered X.img_segments))
      ↔ (∃ en, valid_entry Y en inp
                      ∧ omni_may Y lim en inp (uncovered Y.img_segments)))

theorem agree_iff (X Y : Image) (lim : Int) (inp : ProcInput) :
    agree X Y lim inp ↔ omni_agree X Y lim inp := by
  unfold agree omni_agree
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro H enX enY Hx Hy
      exact (trace_equiv_iff_omni X lim enX Y lim enY inp).mp (H enX enY Hx Hy)
    · intro H enX enY Hx Hy
      exact (trace_equiv_iff_omni X lim enX Y lim enY inp).mpr (H enX enY Hx Hy)
  · constructor
    · intro H
      exact (ex_and_iff (fun en => bh_errors_may_iff X lim en inp)).symm.trans
        (H.trans (ex_and_iff (fun en => bh_errors_may_iff Y lim en inp)))
    · intro H
      exact (ex_and_iff (fun en => bh_errors_may_iff X lim en inp)).trans
        (H.trans (ex_and_iff (fun en => bh_errors_may_iff Y lim en inp)).symm)
  · constructor
    · intro H
      exact (ex_and_iff (fun en => bh_all_errors_iff X lim en inp)).symm.trans
        (H.trans (ex_and_iff (fun en => bh_all_errors_iff Y lim en inp)))
    · intro H
      exact (ex_and_iff (fun en => bh_all_errors_iff X lim en inp)).trans
        (H.trans (ex_and_iff (fun en => bh_all_errors_iff Y lim en inp)).symm)
  · constructor
    · intro H
      exact (ex_and_iff (fun en => bh_unmodeled_may_iff X lim en inp)).symm.trans
        (H.trans (ex_and_iff (fun en => bh_unmodeled_may_iff Y lim en inp)))
    · intro H
      exact (ex_and_iff (fun en => bh_unmodeled_may_iff X lim en inp)).trans
        (H.trans (ex_and_iff (fun en => bh_unmodeled_may_iff Y lim en inp)).symm)

def omni_good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  ∀ en1 en2,
    valid_entry O1 en1 inp → valid_entry O2 en2 inp →
    omni_strong_equiv_error_free O1 O2 en1 en2 inp

theorem good_input_iff (O1 O2 : Image) (inp : ProcInput) :
    good_input O1 O2 inp ↔ omni_good_input O1 O2 inp := by
  unfold good_input omni_good_input
  constructor
  · intro H en1 en2 H1 H2
    exact (strong_equiv_error_free_iff O1 O2 en1 en2 inp).mp (H en1 en2 H1 H2)
  · intro H en1 en2 H1 H2
    exact (strong_equiv_error_free_iff O1 O2 en1 en2 inp).mpr (H en1 en2 H1 H2)

/-- `Classifier.decides`, with `MustExit.must_exit_with` read as
    `omni_run … (exits_with verdict)`. -/
def omni_decides (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry C en (to_proc_input f) →
      (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
       ↔ spec (to_proc_input f))
      ∧ (omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
          ∨ omni_run C classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject))

theorem decides_iff (C : Image) (spec : ProcInput → Prop) :
    decides C spec ↔ omni_decides C spec := by
  unfold decides omni_decides
  constructor
  · intro H f Hf en Hen
    obtain ⟨Hspec, Htot⟩ := H f Hf en Hen
    refine ⟨?_, ?_⟩
    · rw [← Hspec]
      exact (must_exit_with_iff verdict_accept C classifier_alloc_limit en (to_proc_input f)).symm
    · rcases Htot with Ha | Hr
      · exact Or.inl ((must_exit_with_iff _ _ _ _ _).mp Ha)
      · exact Or.inr ((must_exit_with_iff _ _ _ _ _).mp Hr)
  · intro H f Hf en Hen
    obtain ⟨Hspec, Htot⟩ := H f Hf en Hen
    refine ⟨?_, ?_⟩
    · rw [← Hspec]
      exact must_exit_with_iff _ _ _ _ _
    · rcases Htot with Ha | Hr
      · exact Or.inl ((must_exit_with_iff _ _ _ _ _).mpr Ha)
      · exact Or.inr ((must_exit_with_iff _ _ _ _ _).mpr Hr)

/-- The spec side of `omni_decides` is respected up to `iff`, which is
    what lets the two classifier obligations be restated below. -/
theorem omni_decides_spec_iff (C : Image) (spec spec' : ProcInput → Prop)
    (Hs : ∀ inp, spec inp ↔ spec' inp) :
    omni_decides C spec ↔ omni_decides C spec' := by
  unfold omni_decides
  constructor
  · intro H f Hf en Hen
    obtain ⟨Hspec, Htot⟩ := H f Hf en Hen
    refine ⟨?_, Htot⟩
    rw [Hspec]
    exact Hs (to_proc_input f)
  · intro H f Hf en Hen
    obtain ⟨Hspec, Htot⟩ := H f Hf en Hen
    refine ⟨?_, Htot⟩
    rw [Hspec]
    exact (Hs (to_proc_input f)).symm

def omni_classifier_total_T (Cl : Image) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    ∀ en,
      valid_entry Cl en (to_proc_input f) →
      omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_accept)
      ∨ omni_run Cl classifier_alloc_limit en (to_proc_input f) (exits_with verdict_reject)

theorem classifier_total_iff (Cl : Image) :
    classifier_total_T Cl ↔ omni_classifier_total_T Cl := by
  unfold classifier_total_T omni_classifier_total_T
  constructor
  · intro H f Hf en Hen
    rcases H f Hf en Hen with Ha | Hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).mp Ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).mp Hr)
  · intro H f Hf en Hen
    rcases H f Hf en Hen with Ha | Hr
    · exact Or.inl ((must_exit_with_iff _ _ _ _ _).mpr Ha)
    · exact Or.inr ((must_exit_with_iff _ _ _ _ _).mpr Hr)

theorem omni_decides_implies_total (C : Image) (spec : ProcInput → Prop)
    (Hdec : omni_decides C spec) : omni_classifier_total_T C := by
  intro f Hf en Hen
  exact (Hdec f Hf en Hen).2

def omni_classifies_patch_diff_T (O1 P1 O2 P2 C : Image) : Prop :=
  omni_decides C (fun inp => omni_agree O1 P1 source_alloc_limit inp
                             ∧ omni_agree O2 P2 target_alloc_limit inp)

theorem classifies_patch_diff_iff (O1 P1 O2 P2 C : Image) :
    classifies_patch_diff_T O1 P1 O2 P2 C
    ↔ omni_classifies_patch_diff_T O1 P1 O2 P2 C := by
  unfold classifies_patch_diff_T omni_classifies_patch_diff_T
  rw [decides_iff]
  refine omni_decides_spec_iff C _ _ (fun inp => ?_)
  exact and_congr (agree_iff O1 P1 source_alloc_limit inp)
    (agree_iff O2 P2 target_alloc_limit inp)

def omni_classifies_good_inputs_T (O1 O2 C : Image) : Prop :=
  omni_decides C (omni_good_input O1 O2)

theorem classifies_good_inputs_iff (O1 O2 C : Image) :
    classifies_good_inputs_T O1 O2 C ↔ omni_classifies_good_inputs_T O1 O2 C := by
  unfold classifies_good_inputs_T omni_classifies_good_inputs_T
  rw [decides_iff]
  exact omni_decides_spec_iff C _ _ (fun inp => good_input_iff O1 O2 inp)

end LinuxSem.EquivalenceDefinition.OmniEquivalence
