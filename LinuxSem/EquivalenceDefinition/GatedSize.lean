/-
  * EquivalenceDefinition.GatedSize — slicing the input space by gate verdicts

  TRUST BOUNDARY: this file is part of the trusted specification.
  Proof files never edit it.  A top-level check that pins a
  [gated_slice_T] or a [weight_bound_pred_T] theorem depends on the
  definitions here remaining fixed, exactly as the baseline check
  depends on [Equivalence] and the measure check on [Measure].

  ** The family

  [Equivalence.strong_universal_T] asks one binary to reproduce
  another on EVERY valid input.  A task that scores a submission on the
  binary's SIZE as well as on its behavior charges a program for code
  it only ever runs on rare inputs, because there is only one binary
  and only one size.  This file states the shapes a task needs to
  charge for less than that: a submission may split its work into
  several programs, each answering for one PART of the input space,
  and be charged the expectation of the parts rather than the maximum.

  The parts are carved out by GATE IMAGES.  A gate is a binary that
  exits 0 on the inputs its program is meant to handle and 1 on the
  others; [Classifier.accepts] is the reading of "exits 0", and it is
  reused here unchanged rather than restated.  Given gate images
  [G_1 .. G_n] in a fixed order, the part belonging to program [k] is
  "gate [k] accepts and no earlier gate did" ([slice_accept]), and the
  part belonging to the last program is "no gate accepted"
  ([slice_rest]) — the residue, which needs no gate of its own.

  Three facts make that a partition, and all three are proved below
  rather than assumed: two parts never overlap
  ([slices_disjoint_accept_accept], [slices_disjoint_accept_rest]),
  every input lies in one ([slices_exhaustive]), and the residue after
  NO gates is everything ([slice_rest_nil], which is the one-program
  case: no gates, one part, the whole input space, and the obligation
  collapses to [Equivalence.strong_universal_T] via
  [gated_slice_of_universal]).

  Nothing here says a gate is a decider, that two gates disagree, or
  that a gate terminates.  Disjointness is a consequence of the SHAPE
  of [slice_accept] — the earlier gates are required to refuse — and
  holds whatever the gates do.

  ** What a program owes on its slice

  [gated_slice_T Src A P] is [Equivalence.strong_universal_T] with one
  hypothesis added: the input is in [P].  Everything else is the
  baseline statement's quantifier shell — the two [Run.ExecEntry]
  records quantified INDEPENDENTLY and INSIDE the input quantifier
  (never a shared entry, never an existential one), the
  [State.ProcInput] shared between the two runs, each run seeded with
  its role's allocation budget.  The input ranges over
  [FinInput.FinProcInput] rather than [State.ProcInput], because a
  slice predicate is only defined on finite inputs; that is a
  restriction to the finite inputs and nothing else, since
  [FinInput.valid_finite_input_surjection] puts every valid finite
  [State.ProcInput] in the image of [FinInput.to_proc_input] and
  [FinInput.valid_fin_input] is [Run.valid_input] of the denoted
  record, not a new predicate.

  [gated_slice_error_free_T] is the same shell over
  [Equivalence.strong_equiv_error_free], and it inherits that
  statement's properties whole: no [Run.bh_all_errors] escape, no
  separate [Equivalence.modeled] conjunct.

  THREE BUDGETS ARE IN PLAY AND THEY ARE NOT INTERCHANGEABLE.
  [Equivalence.strong_equiv] hardwires
  [State.source_alloc_limit] for the first image and
  [State.target_alloc_limit] for the second, by ROLE; the gates run at
  [Classifier.classifier_alloc_limit] through [Classifier.accepts].  A
  slice statement therefore compares the two programs at exactly the
  budgets the ungated statement compares them at, and the gate's own
  budget never enters the comparison.

  ** The bound: mass outside a predicate

  [weight_bound_pred_T P w M b] is [Measure.weight_bound_T] with the
  classifier's reject set replaced by an arbitrary predicate's
  complement: no duplicate-free-on-cores list of valid finite inputs
  OUTSIDE [P] weighs more than [b * M].  It is a strict
  generalisation, and [weight_bound_pred_of_classifier] says so
  exactly: [Measure.weight_bound_T C w M b] IS
  [weight_bound_pred_T (Classifier.accepts C) w M b], because
  [Classifier.rejects C f] is by definition
  [FinInput.valid_fin_input f /\ ~ Classifier.accepts C f].

  A bound on the complement of a slice is what a consumer turns into a
  LOWER bound on the slice's own mass, which is the direction that
  keeps a size score honest: unproven mass has to be charged at the
  most expensive part, so a submission gains only by proving MORE.

  Everything [Measure]'s header says about the [List.NoDup]-on-cores
  hypothesis carries over unchanged, including why the record-indexed
  reading would be unsatisfiable ([FinInput.fin_core_fibre_infinite])
  and what the quotient costs.  Two points specific to this file:

  - [List.NoDup] and [List.Forall] are written QUALIFIED throughout,
    for the reason [Measure]'s header gives for [List.NoDup]: another
    list predicate of the same name can be in scope through [BvBase], and
    an unqualified name would silently pick up the wrong one.
  - The predicate is on RECORDS, not on cores.  [Classifier.accepts]
    already is — it unfolds through [FinInput.to_proc_input] and the
    run reads all ten fields, [FinInput.fin_uid] among them off the
    initial stack with no syscall — so [weight_bound_pred_T] inherits
    the situation rather than creating it.  Read out loud, the
    statement bounds every core having SOME representative outside
    [P], the union over the fibre: the larger set, so the stronger
    obligation, never the weaker one.  It is not "the cores outside
    [P]", and no reader should take it as that.

  ** Vacuity routes, and where each is closed

  - AN IMAGE WITH NO VALID ENTRY.  [Classifier.accepts_vacuous_no_entries]
    says such an image ACCEPTS every input, and the direction matters:
    as a gate it does not vanish, it SWALLOWS the rest of the input
    space.  [slice_accept_vacuous_no_entries] states that consequence
    exactly — its slice is the whole of [slice_rest prev] — and
    [slice_rest_vacuous_no_entries] states the other half: once such an
    image appears among the earlier gates, every later slice and the
    residue are EMPTY, so the programs behind them owe nothing at all.
    A submission that shipped a gate that does not load could therefore
    be charged for one program and prove nothing about the rest.  The
    remedy is the one [Classifier] and [Measure] already name and it is
    not this file's to apply: a consuming checker ascribes
    [Equivalence.IMAGE_WF] to every image it names, gates included.
  - AN UNSATISFIABLE SLICE.  [gated_slice_T Src A P] holds vacuously
    when nothing valid is in [P].  This one is by design and is not a
    hole: an empty slice is a part that carries no mass, and the
    measure side is what charges for that — a bound proved on the
    complement of an empty [P] is a bound of [b * M] on the whole
    space, which buys the submission nothing.
  - AN IMAGE WITH NO VALID ENTRY ON THE EQUIVALENCE SIDE.
    [gated_slice_T] inherits [Equivalence.strong_universal_T]'s route
    unchanged: strengthening what sits under a quantifier cannot repair
    an empty range, so [Equivalence.IMAGE_WF] is owed for [Src] and [A]
    here for the same reason it is owed there.

  ** Why excluded middle is a HYPOTHESIS

  [slices_exhaustive] needs to know, of each gate, whether it accepts
  the input or not.  [Classifier.accepts] is a [forall] over entries
  ending in [MustExit.must_exit_with], an inductively defined predicate
  over an infinitely branching run tree: nothing in this development
  decides it, and no gate is required to be a
  [Classifier.classifier_total_T] decider.  So the disjunction is taken
  as a PER-GATE HYPOTHESIS at the point of use rather than as a global postulate
  of the file.  Two things follow, both intended:

  - every lemma here has a closed [Print Assumptions]: the file adds no
    postulate to a theory that a consumer would then be unable to see;
  - a consumer that wants exhaustiveness supplies the instance it can
    justify — classically at the meta level, where the arithmetic that
    splits a size across parts already lives, or constructively from a
    totality proof per gate.

  Disjointness needs no such hypothesis and gets none: it is proved
  outright.

  ** Under a spurious-failure configuration

  Everything above is the may-fail reading.  The last section of this
  file states the same shapes under a [Run.SpuriousCfg], because a
  task that forces a family states its baseline and gate obligations
  at a configuration and had no way to state its per-slice obligations
  anywhere but here, at may-fail — three obligations that would not
  then have composed into a claim about one submission.

  Two things move and one does not, and the one that does not is the
  answer to the question a reader arrives with.  THE PROGRAMS' RUNS
  follow the task, in [gated_slice_T_scfg] and
  [gated_slice_error_free_T_scfg].  THE GATES' RUNS DO NOT:
  [slice_accept_fo] and [slice_rest_fo] read the gates through
  [Classifier.accepts_fo], pinned to [Run.forced_only_cfg] whatever
  the task chose, because a gate is asked to DECIDE and its own reads
  must not be refusable without cause.  That is also why those two
  names end [_fo] and not [_s cfg]: [Classifier.accepts] has no
  [_s cfg] twin to build on, there being no reading in which a gate's
  own run follows the task.  [weight_bound_pred_T] is unchanged and
  needs no twin, because it has no run in it — every run it could
  depend on is inside the predicate it is indexed by.

  A configured task therefore emits [gated_slice_T_scfg cfg] over
  [slice_accept_fo] / [slice_rest_fo], with ONE [cfg] shared with the
  baseline and gate obligations.  That section's header carries the
  argument, including why there is no monotonicity in [cfg] in either
  direction.

  ** note (Lean rendering)

  [Q] becomes Lean's [Rat] (written [ℚ] in informal text), and [Qeq] is
  Leibniz equality there — [Rat] is a normalized structure, not a
  setoid quotient — so every `(a == b)%Q` above is stated here as
  [a = b] and [weight_bound_pred_qeq] transports along [=] by
  rewriting.  Every [Qle] fact is Lean's [≤] on [Rat]; [Qle_trans] is
  [Rat.le_trans] and [Qmult_le_compat_r] is
  [Rat.mul_le_mul_of_nonneg_right].  The [`decide`] steps in
  [weight_bound_pred_refutable] and [weight_bound_pred_needs_nodup] have
  no Lean counterpart that computes the literal, so this tree performs
  the same [Qle_bool]-to-[false] step through the order lemmas instead —
  see [one_lt_one_add_one] — while the paragraph above still applies: no
  [Q] equality is decided there.

  [List.Forall P l] is spelled
  [∀ x ∈ l, P x] here, as `Fs.lean`'s header records: the Lean 4.31
  core library has no [List.Forall], and this is the same predicate at
  the same places.  [List.NoDup] is Lean's [List.Nodup], and it keeps
  the [List.] qualifier the file insists on.
-/

import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.FinInput
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.EquivalenceDefinition.Measure

open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.GatedSize

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.Measure

/- =========================================================================
   The slices
   ========================================================================= -/

/-- The slice of the program whose gate is [G], where [prev] lists the
    gates ORDERED BEFORE it: [G] accepts [f] and every earlier gate
    refuses it.  The order is the deployed order — a gate list is read
    left to right and the first acceptance wins — and it is carried in
    the statement as the prefix [prev] rather than by an index, so that
    a lemma about two slices can say which is earlier by saying that one
    gate is a member of the other's prefix.

    "Refuses" is [~ Classifier.accepts], the negation of the
    conservative reading, which is [Classifier.rejects] minus its
    validity conjunct.  The validity conjunct is dropped deliberately:
    every statement that consumes a slice already carries
    [FinInput.valid_fin_input] as its own hypothesis
    ([gated_slice_T], [weight_bound_pred_T]), so carrying it inside the
    slice too would make the predicate say it twice and would make
    [slice_rest [] f] — the whole space — depend on validity, which is
    not what "no gate accepted" means. -/
def slice_accept (prev : List Image) (G : Image) (f : FinProcInput) : Prop :=
  accepts G f ∧ ∀ G' ∈ prev, ¬ accepts G' f

/-- The last slice: everything the gates refuse.  There is no gate for
    it — the deployed program falls through to the final one — so the
    predicate is the [prev] conjunct of [slice_accept] standing alone.
    [slice_rest [] f] is therefore the whole input space
    ([slice_rest_nil]), which is the one-program case. -/
def slice_rest (prev : List Image) (f : FinProcInput) : Prop :=
  ∀ G' ∈ prev, ¬ accepts G' f

/- =========================================================================
   Disjointness
   ========================================================================= -/

/-- Two [slice_accept] slices never share an input, whenever one's gate
    is among the other's earlier gates.  That side condition is what
    "earlier" means here, and it is the whole proof: the later slice
    requires [G] to refuse [f], the earlier one requires [G] to accept
    it.

    No hypothesis about the gates is needed — not determinism, not
    totality, not that they are distinct images, not excluded middle.
    Disjointness is a property of the SHAPE of [slice_accept]: it holds
    even if two gates are the same image, and even if a gate neither
    accepts nor is provably refuted. -/
theorem slices_disjoint_accept_accept (prev : List Image) (G : Image)
    (prev' : List Image) (G' : Image) (f : FinProcInput)
    (Hin : G ∈ prev') (Hacc : slice_accept prev G f)
    (Hacc' : slice_accept prev' G' f) : False :=
  Hacc'.2 G Hin Hacc.1

/-- ... and the residue is disjoint from every [slice_accept] slice whose
    gate it lists.  Same argument, one conjunct shorter: [slice_rest] IS
    the refusal conjunct. -/
theorem slices_disjoint_accept_rest (prev : List Image) (G : Image)
    (prev' : List Image) (f : FinProcInput)
    (Hin : G ∈ prev') (Hacc : slice_accept prev G f)
    (Hrest : slice_rest prev' f) : False :=
  Hrest G Hin Hacc.1

/- =========================================================================
   Exhaustiveness
   ========================================================================= -/

/-- The residue after no gates at all is everything.  This is the
    one-program case stated as a lemma rather than left to the reader:
    with an empty gate list there is one slice, it is the whole input
    space, and [gated_slice_T Src A (slice_rest [])] is
    [Equivalence.strong_universal_T] restricted to the finite inputs. -/
theorem slice_rest_nil (f : FinProcInput) : slice_rest [] f := by
  intro G' Hin
  exact absurd Hin (List.not_mem_nil)

/-- Every input lands somewhere: either in the slice of the FIRST gate
    that accepts it — exhibited with the prefix and suffix that place
    that gate in the list — or in the residue.

    The hypothesis is per gate and per input, not a global postulate: for
    each gate in THIS list, at THIS input, the verdict question is
    decided one way or the other.  The header says why it cannot be
    discharged here.  The proof is a plain induction on the gate list
    that consumes the hypothesis once per gate as it walks, so a
    consumer supplying decidability for [n] gates pays for exactly [n]
    instances.

    The left disjunct is stated as an existential over the LIST
    DECOMPOSITION rather than over an index, so that a consumer reading
    it back gets the prefix [slice_accept] needs handed to it, already
    known to be the gates strictly before [G]. -/
theorem slices_exhaustive : ∀ (gates : List Image) (f : FinProcInput),
    (∀ G, G ∈ gates → accepts G f ∨ ¬ accepts G f) →
    (∃ prev G suffix, gates = prev ++ G :: suffix ∧ slice_accept prev G f)
    ∨ slice_rest gates f := by
  intro gates
  induction gates with
  | nil =>
    intro f _
    exact Or.inr (slice_rest_nil f)
  | cons g gs ih =>
    intro f Hdec
    rcases Hdec g List.mem_cons_self with Hacc | Hno
    · exact Or.inl ⟨[], g, gs, rfl, Hacc, by
        intro G' Hin
        exact absurd Hin (List.not_mem_nil)⟩
    · rcases ih f (fun G HG => Hdec G (List.mem_cons_of_mem g HG)) with
        ⟨prev, G, suffix, Heq, Hacc, Hprev⟩ | Hrest
      · refine Or.inl ⟨g :: prev, G, suffix, ?_, Hacc, ?_⟩
        · rw [Heq]
          rfl
        · intro G' Hin
          rcases List.mem_cons.mp Hin with rfl | Hin
          · exact Hno
          · exact Hprev G' Hin
      · exact Or.inr (by
          intro G' Hin
          rcases List.mem_cons.mp Hin with rfl | Hin
          · exact Hno
          · exact Hrest G' Hin)

/- =========================================================================
   The per-slice equivalence obligation
   ========================================================================= -/

/-- [A] reproduces [Src] on every valid finite input in [P].  The
    baseline statement with one hypothesis added, and NOTHING else
    moved: entries quantified independently and inside the input, the
    input shared between the runs, role budgets by role.  The argument
    order is [Src] then [A] then [P], matching
    [Equivalence.strong_equiv]'s own source-then-target order, so a
    reader can put the two side by side.

    [P] is an arbitrary predicate rather than a [slice_accept]
    application on purpose: the obligation does not care how the part
    was carved out, and stating it over a bare predicate is what lets
    [gated_slice_mono] and [gated_slice_of_universal] be about slices in
    general rather than about a particular gate list. -/
def gated_slice_T (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv Src A en_s en_a (to_proc_input f)

/-- The error-free twin: the same shell over
    [Equivalence.strong_equiv_error_free].  A task whose reference
    binary can fault cannot use this variant and keeps the baseline one,
    exactly as at [Equivalence.strong_universal_error_free_T]. -/
def gated_slice_error_free_T (Src A : Image) (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_error_free Src A en_s en_a (to_proc_input f)

/-- A slice obligation is WEAKER than the ungated one, at every
    predicate: a program proved equivalent everywhere is proved
    equivalent on any part.  This is the lemma that makes the
    one-program case a special case rather than a separate scheme, and
    it is also the honest reading of what a slice proof buys — less than
    a full proof, never more.

    [FinInput.valid_fin_input] is [Run.valid_input] of the denoted
    input by definition, which is what lets the baseline statement's
    third hypothesis be discharged with the slice statement's first. -/
theorem gated_slice_of_universal (Src A : Image) (P : FinProcInput → Prop)
    (Huniv : strong_universal_T Src A) : gated_slice_T Src A P := by
  intro f Hvalid _ en_s en_a Hs Ha
  exact Huniv en_s en_a (to_proc_input f) Hs Ha Hvalid

/-- ... and the same for the error-free variant. -/
theorem gated_slice_error_free_of_universal (Src A : Image) (P : FinProcInput → Prop)
    (Huniv : strong_universal_error_free_T Src A) :
    gated_slice_error_free_T Src A P := by
  intro f Hvalid _ en_s en_a Hs Ha
  exact Huniv en_s en_a (to_proc_input f) Hs Ha Hvalid

/-- Shrinking the slice weakens the obligation.  [P'] is contained in
    [P], so a proof over [P] covers it.  The binders are [P] and [P']
    rather than the [P], [Q] a reader might expect, because [Q] is
    [QArith]'s rationals and this file states bounds over them. -/
theorem gated_slice_mono (Src A : Image) (P P' : FinProcInput → Prop)
    (Hsub : ∀ f, P' f → P f) (Hgated : gated_slice_T Src A P) :
    gated_slice_T Src A P' := by
  intro f Hvalid HP' en_s en_a Hs Ha
  exact Hgated f Hvalid (Hsub f HP') en_s en_a Hs Ha

/-- The error-free twin of [gated_slice_mono]. -/
theorem gated_slice_error_free_mono (Src A : Image) (P P' : FinProcInput → Prop)
    (Hsub : ∀ f, P' f → P f) (Hgated : gated_slice_error_free_T Src A P) :
    gated_slice_error_free_T Src A P' := by
  intro f Hvalid HP' en_s en_a Hs Ha
  exact Hgated f Hvalid (Hsub f HP') en_s en_a Hs Ha

/- =========================================================================
   The predicate-indexed weight bound
   ========================================================================= -/

/-- No duplicate-free-on-cores list of valid finite inputs OUTSIDE [P]
    weighs more than [b] times the declared total [M].  Universal over
    the list, as [Measure.weight_bound_T] is and for the same reason: a
    submission cannot pick a favorable sample.

    [FinInput.valid_fin_input f] is a CONJUNCT of the membership
    hypothesis rather than a hypothesis on the list, and that placement
    is what makes [weight_bound_pred_of_classifier] an equality rather
    than an implication — [Classifier.rejects] carries its validity the
    same way.  It also keeps the bound from being refutable by an
    invalid input, which would make every bound false and the obligation
    worthless.

    The [Measure.DISTRIBUTION] module type is the source of [w] and [M]
    here as there: TRUSTED TASK METADATA, never chosen by the
    submission.  [Measure]'s header is the authority on why —
    [fun _ => 0%Q] satisfies both of [DISTRIBUTION]'s weight
    constraints, so a submission free to pick [w] discharges every bound
    at [b = 0] and the whole measure says nothing. -/
def weight_bound_pred_T (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M b : Rat) : Prop :=
  ∀ l : List FinProcInput,
    (List.map fin_core l).Nodup →
    (∀ f, f ∈ l → valid_fin_input f ∧ ¬ P f) →
    sum_weights w l ≤ b * M

/-- The generalisation is EXACT: at [P := Classifier.accepts C] the new
    bound is the old one, not merely implied by it.  Both directions are
    the identity on proofs, because [Classifier.rejects C f] is by
    definition [FinInput.valid_fin_input f /\ ~ Classifier.accepts C f]
    — the widest reading of rejection, covering an input the classifier
    answers 1 on, one it answers inconsistently across entries, and one
    it never answers.

    This is what makes the gated measure a conservative extension of
    [Measure]: a consumer holding a [Measure.weight_bound_T] proof for a
    gate image already holds the bound this file's arithmetic reads, and
    a consumer proving a [weight_bound_pred_T] over a slice predicate
    can hand the classifier case back unchanged. -/
theorem weight_bound_pred_of_classifier (C : Image) (w : FinProcInput → Rat)
    (M b : Rat) :
    weight_bound_T C w M b ↔ weight_bound_pred_T (accepts C) w M b := by
  constructor
  · intro Hbound l Hnd Hall
    exact Hbound l Hnd (fun f Hin => Hall f Hin)
  · intro Hbound l Hnd Hall
    exact Hbound l Hnd (fun f Hin => Hall f Hin)

/-- A bound proved at [b] is a bound at any larger [b'], given [M]
    nonnegative.  The counterpart of [Measure.weight_bound_mono], with the same
    proof and the same reason for the [0 <= M] hypothesis: multiplying an
    inequality by a possibly-negative quantity can flip it.  It is what
    lets a consumer read a printed [b] as an UPPER bound claim rather
    than an exact one. -/
theorem weight_bound_pred_mono (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M b b' : Rat) (HM : 0 ≤ M) (Hbb' : b ≤ b')
    (Hbound : weight_bound_pred_T P w M b) : weight_bound_pred_T P w M b' := by
  intro l Hnd Hall
  exact Rat.le_trans (Hbound l Hnd Hall) (Rat.mul_le_mul_of_nonneg_right Hbb' HM)

/-- The bound transports along [Qeq] in [M] and [b] together: a
    submission's [1#2] and a checker's [2#4] name the same bound.  The
    counterpart of [Measure.weight_bound_qeq], and the reason is the one
    [Measure]'s header gives at length — [Q]'s propositional equality is
    [Qeq], not Leibniz [eq], so a consumer must never decide a [Q]
  equality by [`decide`] and must have this transport
    instead.  (Under Lean's [Rat], [Qeq] is [=] and [rewrite] is the
    tool.) -/
theorem weight_bound_pred_qeq (P : FinProcInput → Prop) (w : FinProcInput → Rat)
    (M M' b b' : Rat) (HM : M = M') (Hb : b = b')
    (Hbound : weight_bound_pred_T P w M b) : weight_bound_pred_T P w M' b' := by
  intro l Hnd Hall
  have H := Hbound l Hnd Hall
  rw [HM, Hb] at H
  exact H

/- =========================================================================
   Bites: what each statement rules out
   ========================================================================= -/

/-- [gated_slice_T] is refutable, and by exactly one witness: a valid
    finite input IN the slice, a valid entry on each side, and the two
    runs failing [Equivalence.strong_equiv].  So a slice obligation is a
    real claim about the two binaries on that part of the input space,
    not a statement every pair satisfies.

    All four hypotheses are load-bearing and a refutation missing any
    one of them refutes nothing: an invalid input, an input outside the
    slice, or an invalid entry on either side is a triple the statement
    never quantified over. -/
theorem gated_slice_refuted (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry)
    (Hvalid : valid_fin_input f) (HP : P f)
    (Hs : valid_entry Src en_s (to_proc_input f))
    (Ha : valid_entry A en_a (to_proc_input f))
    (Hne : ¬ strong_equiv Src A en_s en_a (to_proc_input f)) :
    ¬ gated_slice_T Src A P := by
  intro Hgated
  exact Hne (Hgated f Hvalid HP en_s en_a Hs Ha)

/-- The error-free twin of [gated_slice_refuted]. -/
theorem gated_slice_error_free_refuted (Src A : Image) (P : FinProcInput → Prop)
    (f : FinProcInput) (en_s en_a : ExecEntry)
    (Hvalid : valid_fin_input f) (HP : P f)
    (Hs : valid_entry Src en_s (to_proc_input f))
    (Ha : valid_entry A en_a (to_proc_input f))
    (Hne : ¬ strong_equiv_error_free Src A en_s en_a (to_proc_input f)) :
    ¬ gated_slice_error_free_T Src A P := by
  intro Hgated
  exact Hne (Hgated f Hvalid HP en_s en_a Hs Ha)

/-- THE VACUITY ROUTE, stated in the direction it actually runs.  A gate
    image with no valid entry at that input ACCEPTS it
    ([Classifier.accepts_vacuous_no_entries]) — vacuously, having
    executed nothing — so as a gate it does not disappear from the
    partition, it SWALLOWS whatever the earlier gates left: its slice is
    exactly [slice_rest prev], the entire residue at that point.

    That is the shape a reader is most likely to get backwards, so it is
    stated as an [iff] rather than as an implication.  "No valid entry"
    is not "accepts nothing"; it is "accepts everything".

    WHICH DEFECT ACTUALLY EMPTIES THE ENTRY SET is narrower than the
    list a reader might expect, and worth naming exactly.
    [Run.valid_entry] is [Run.valid_sp], [Run.valid_brk] of the image's
    segments, [Run.valid_mmap_base] and [Run.entry_stack_fits]; only the
    SECOND reads the image at all, and the first, third and fourth are
    satisfiable for every valid input whatever the image is.  So of
    [Equivalence.IMAGE_WF]'s three parameters exactly one bears on this
    route — [Equivalence.image_brk_satisfiable], which
    [Equivalence.image_brk_satisfiable_entry] turns into an entry for
    every valid input, and which is therefore what makes the premise of
    [Classifier.accepts] satisfiable and this lemma's hypothesis false.
    [Equivalence.image_entry_fetchable] and
    [Equivalence.image_phdrs_readable] are about what the RUN does once
    an entry is chosen; they close [Equivalence.equiv]'s
    [Run.bh_all_errors] escape, not this one.

    The remedy is still the whole of [Equivalence.IMAGE_WF] and not just
    its third parameter, because a gate image is also run: a consuming
    checker must ascribe it to every gate image it names, exactly as
    [Measure]'s header requires it for the classifier image and
    [Equivalence]'s for the two compared images. -/
theorem slice_accept_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput)
    (Hno : ∀ en, ¬ valid_entry G en (to_proc_input f)) :
    (slice_accept prev G f ↔ slice_rest prev f) := by
  constructor
  · intro H
    exact H.2
  · intro Hrest
    exact ⟨accepts_vacuous_no_entries G f Hno, Hrest⟩

/-- The other half of the same route, and the one that costs a checker
    the most: once a gate with no valid entry appears among the earlier
    gates, the residue is EMPTY, and so is every later slice
    ([slices_disjoint_accept_rest] carries the emptiness on to them).
    The programs behind those slices are then never asked about any
    input at all, and their [gated_slice_T] obligations hold with
    nothing established about their binaries.

    Stated as a refutation because that is how it is used: exhibiting a
    gate with no valid entry in [prev] is how a reviewer shows that a
    submitted partition is not one. -/
theorem slice_rest_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) (Hin : G ∈ prev)
    (Hno : ∀ en, ¬ valid_entry G en (to_proc_input f)) :
    ¬ slice_rest prev f := by
  intro Hrest
  exact Hrest G Hin (accepts_vacuous_no_entries G f Hno)

/-- [2 <= 1] is false on the rationals, in the form the refutations
    below need: [1 < 1 + 1].  The comparison has already collapsed to a
    boolean, which reduces to [false]; nothing here decides a [Rat]
    equality by computation (see the note in this file's header).  The same helper (and the same reason
    for it) appears in `Measure.lean`, where it is [private] there;
    stating it once here keeps this file independent of that one's
    private names. -/
private theorem one_lt_one_add_one : (1 : Rat) < 1 + 1 := by
  rw [Rat.lt_iff_sub_pos, Rat.add_sub_cancel]
  decide

/-- The bound [1] at unit weight and total [1] fails as soon as two valid
    inputs with DISTINCT CORES are both outside [P]: the two-element list
    has duplicate-free cores and sums to [2], and [2 <= 1 * 1] is false.
    The counterpart of [Measure.weight_bound_refutable], and it says the same
    thing — a [weight_bound_pred_T] claim is a real restriction on how
    much of the input space can fall outside [P], not something every
    distribution and every predicate satisfies.

    The hypothesis is [FinInput.fin_core f1 <> FinInput.fin_core f2]
    rather than [f1 <> f2], and that strengthening is exactly the
    content of the quotient: two records outside [P] that differ only in
    their launch environment no longer refute anything, because the
    obligation never charged for the second one. -/
theorem weight_bound_pred_refutable (P : FinProcInput → Prop) (f1 f2 : FinProcInput)
    (Hv1 : valid_fin_input f1) (Hp1 : ¬ P f1)
    (Hv2 : valid_fin_input f2) (Hp2 : ¬ P f2)
    (Hne : fin_core f1 ≠ fin_core f2) :
    ¬ weight_bound_pred_T P (fun _ => 1) 1 1 := by
  intro Hbound
  have Hnd : (List.map fin_core [f1, f2]).Nodup := by
    simp [List.nodup_cons, Hne]
  have Hall : ∀ f, f ∈ [f1, f2] → valid_fin_input f ∧ ¬ P f := by
    intro f Hin
    rcases List.mem_cons.mp Hin with rfl | Hin
    · exact ⟨Hv1, Hp1⟩
    · rcases List.mem_cons.mp Hin with rfl | Hin
      · exact ⟨Hv2, Hp2⟩
      · exact absurd Hin (List.not_mem_nil)
  have H := Hbound [f1, f2] Hnd Hall
  simp only [sum_weights, List.foldr_cons, List.foldr_nil] at H
  have H2 : (1 : Rat) + 1 ≤ (1 : Rat) := by
    simpa [Rat.mul_one, Rat.add_zero] using H
  exact (Rat.not_le (a := (1 : Rat) + 1) (b := 1)).mpr one_lt_one_add_one H2

/-- [List.NoDup] on the cores is what keeps the bound satisfiable, and
    this exhibits the list it excludes: ONE valid input outside [P],
    listed twice.  Both halves are asserted together rather than as an
    implication — the list meets the membership hypothesis and breaks the
    arithmetic, and duplicate-freedom of the cores is precisely what
    keeps [weight_bound_pred_T] from quantifying over it.

    Drop that hypothesis and the obligation is not merely harder, it is
    UNSATISFIABLE at any [b] whatever the moment anything valid falls
    outside [P]: the same input repeated [n] times sums to [n].  Which is
    [Measure]'s argument for the quotient, reached here by the shortest
    route rather than through [FinInput.fin_core_fibre_infinite], since
    one input listed twice is already enough to make the point. -/
theorem weight_bound_pred_needs_nodup (P : FinProcInput → Prop) (f : FinProcInput)
    (Hv : valid_fin_input f) (Hp : ¬ P f) :
    ¬ (List.map fin_core [f, f]).Nodup
    ∧ (∀ f', f' ∈ [f, f] → valid_fin_input f' ∧ ¬ P f')
    ∧ ¬ (sum_weights (fun _ => 1) [f, f] ≤ 1 * 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    exact (List.nodup_cons.mp Hnd).1 (by simp)
  · intro f' Hin
    rcases List.mem_cons.mp Hin with rfl | Hin
    · exact ⟨Hv, Hp⟩
    · rcases List.mem_cons.mp Hin with rfl | Hin
      · exact ⟨Hv, Hp⟩
      · exact absurd Hin (List.not_mem_nil)
  · intro Hle
    have H := Hle
    simp only [sum_weights, List.foldr_cons, List.foldr_nil] at H
    have H2 : (1 : Rat) + 1 ≤ (1 : Rat) := by
      simpa [Rat.mul_one, Rat.add_zero] using H
    exact (Rat.not_le (a := (1 : Rat) + 1) (b := 1)).mpr one_lt_one_add_one H2

/- =========================================================================
   The same shapes under a SPURIOUS-FAILURE CONFIGURATION
   ([Run.SpuriousCfg], [Run.run_scfg])
   =========================================================================

   [Equivalence]'s own configuration section is the model this follows,
   and the reason this one is needed is that a task cannot mix the two:
   a problem that forces a family states its baseline obligation at
   [Equivalence.strong_universal_T_scfg cfg] and its gate obligation at
   [Classifier.classifies_good_inputs_T_s cfg], and without this section
   would have no way to state the per-slice obligation anywhere but at
   the unparameterized [gated_slice_T].  The slice programs would then
   be judged under may-fail while the base and the gates are judged under [cfg],
   which is not a stricter reading or a looser one, it is a DIFFERENT
   one — [Equivalence]'s section says why equivalence is inherited in
   neither direction — so the three obligations would not compose
   into a claim about one submission.

   TWO THINGS ARE PARAMETERISED AND ONE IS DELIBERATELY NOT.

   - THE PROGRAMS' RUNS follow the task: [gated_slice_T_scfg cfg] and
     [gated_slice_error_free_T_scfg cfg] are the shells above over
     [Equivalence.strong_equiv_scfg cfg] and
     [Equivalence.strong_equiv_error_free_scfg cfg], with nothing else
     moved — entries quantified independently and inside the input, the
     input shared, budgets by role.
   - THE GATES' RUNS DO NOT.  [slice_accept_fo] and [slice_rest_fo] read
     the gates through [Classifier.accepts_fo], which is pinned to
     [Run.forced_only_cfg] whatever the task chose.  That is not a
     shortcut, it is [Classifier]'s forced-only rule applied here: a gate is asked
     to DECIDE, so its own reads must not be refusable without cause, or
     no gate that opens its input decides anything and the partition has
     no members.  It is also why the names are [_fo] and not [_s cfg] —
     [Classifier.accepts] has no [_s cfg] twin to build on, because
     there is no reading in which a gate's own run follows the task's
     configuration.

   WHICH PAIR A CONFIGURED TASK EMITS is therefore
   [gated_slice_T_scfg cfg] (or its error-free twin) over
   [slice_accept_fo] / [slice_rest_fo], with ONE [cfg] shared with the
   baseline and gate obligations.  Emitting the slice statements at a
   different [cfg] from the base is the failure this section exists to
   make impossible to reach by accident, and nothing mechanical catches
   it: both statements typecheck and both are provable, they simply do
   not compose.

   NO MONOTONICITY IN [cfg], IN EITHER DIRECTION, and a reader who
   expects one should read [Equivalence]'s section rather than this
   paragraph twice.  Turning a family off removes executions and adds
   none, so error-freedom and coverage of ONE run are inherited downward
   — but [gated_slice_T_scfg] is an equivalence between TWO runs, and
   removing executions from both sides can break a trace-set equality as
   easily as it can repair one.  So [gated_slice_T_scfg cfg1] says
   nothing about [gated_slice_T_scfg cfg2], which is exactly why the
   configuration is sealed by the module type the Checker ascribes.

   [weight_bound_pred_T] IS LEFT ALONE, and the argument is that it has
   no run in it.  It quantifies over lists of finite inputs outside an
   arbitrary predicate; every run it could be said to depend on is
   already inside that predicate, which for the gated case is
   [slice_accept] or [slice_accept_fo] and reads the gates itself.  So
   the configured bound is the existing definition at the configured
   predicate, with no new shape:
   [weight_bound_pred_of_classifier_fo] states the identification for
   the classifier case, exactly as [weight_bound_pred_of_classifier]
   does for the unparameterized one. -/

/- -------------------------------------------------------------------------
   The slices, with the gates pinned to forced-only
   ------------------------------------------------------------------------- -/

/-- [slice_accept] over [Classifier.accepts_fo].  Same shape, same
    dropped validity conjunct, same reading of "refuses" as the negation
    of acceptance rather than [Classifier.rejects_fo] minus its validity
    conjunct — and the [prev] list is still the gates ordered before
    [G]. -/
def slice_accept_fo (prev : List Image) (G : Image) (f : FinProcInput) : Prop :=
  accepts_fo G f ∧ ∀ G' ∈ prev, ¬ accepts_fo G' f

def slice_rest_fo (prev : List Image) (f : FinProcInput) : Prop :=
  ∀ G' ∈ prev, ¬ accepts_fo G' f

/-- Disjointness is still a property of the SHAPE and still needs
    nothing of the gates — not determinism, not totality, not that they
    are distinct images, not excluded middle.  The pin changes which
    runs [Classifier.accepts_fo] quantifies over and changes nothing
    here, which is the point of proving disjointness from the shape in
    the first place. -/
theorem slices_disjoint_accept_accept_fo (prev : List Image) (G : Image)
    (prev' : List Image) (G' : Image) (f : FinProcInput)
    (Hin : G ∈ prev') (Hacc : slice_accept_fo prev G f)
    (Hacc' : slice_accept_fo prev' G' f) : False :=
  Hacc'.2 G Hin Hacc.1

theorem slices_disjoint_accept_rest_fo (prev : List Image) (G : Image)
    (prev' : List Image) (f : FinProcInput)
    (Hin : G ∈ prev') (Hacc : slice_accept_fo prev G f)
    (Hrest : slice_rest_fo prev' f) : False :=
  Hrest G Hin Hacc.1

/-- The one-program case, unchanged: no gates, one part, the whole input
    space. -/
theorem slice_rest_fo_nil (f : FinProcInput) : slice_rest_fo [] f := by
  intro G' Hin
  exact absurd Hin (List.not_mem_nil)

/-- Exhaustiveness, with the per-gate decidability hypothesis taken at
    [Classifier.accepts_fo] instead.  The hypothesis is not lighter
    under the pin — [Classifier.accepts_fo] is still a [forall] over
    entries ending in [MustExit.must_exit_with_scfg], which nothing here
    decides — so it stays a per-gate hypothesis at the point of use for
    the reason this file's header gives, and the file keeps its closed
    [Print Assumptions]. -/
theorem slices_exhaustive_fo : ∀ (gates : List Image) (f : FinProcInput),
    (∀ G, G ∈ gates → accepts_fo G f ∨ ¬ accepts_fo G f) →
    (∃ prev G suffix, gates = prev ++ G :: suffix ∧ slice_accept_fo prev G f)
    ∨ slice_rest_fo gates f := by
  intro gates
  induction gates with
  | nil =>
    intro f _
    exact Or.inr (slice_rest_fo_nil f)
  | cons g gs ih =>
    intro f Hdec
    rcases Hdec g List.mem_cons_self with Hacc | Hno
    · exact Or.inl ⟨[], g, gs, rfl, Hacc, by
        intro G' Hin
        exact absurd Hin (List.not_mem_nil)⟩
    · rcases ih f (fun G HG => Hdec G (List.mem_cons_of_mem g HG)) with
        ⟨prev, G, suffix, Heq, Hacc, Hprev⟩ | Hrest
      · refine Or.inl ⟨g :: prev, G, suffix, ?_, Hacc, ?_⟩
        · rw [Heq]
          rfl
        · intro G' Hin
          rcases List.mem_cons.mp Hin with rfl | Hin
          · exact Hno
          · exact Hprev G' Hin
      · exact Or.inr (by
          intro G' Hin
          rcases List.mem_cons.mp Hin with rfl | Hin
          · exact Hno
          · exact Hrest G' Hin)

/-- THE VACUITY ROUTE SURVIVES THE PIN, in both halves and in the same
    direction, because it runs through the ENTRY quantifier and not
    through the run: [Classifier.accepts_fo_vacuous_no_entries] says an
    image with no valid entry ACCEPTS every input under the pin exactly
    as [Classifier.accepts_vacuous_no_entries] says it without.  So a
    gate that does not load still SWALLOWS the residue rather than
    disappearing from the partition, and still empties every later slice
    once it appears among the earlier gates.

    Pinning the gates to forced-only therefore buys nothing against this
    route, which is worth stating because it is the route a reader might
    hope the pin closed.  The remedy is unchanged: a consuming checker
    ascribes [Equivalence.IMAGE_WF] to every gate image it names. -/
theorem slice_accept_fo_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput)
    (Hno : ∀ en, ¬ valid_entry G en (to_proc_input f)) :
    (slice_accept_fo prev G f ↔ slice_rest_fo prev f) := by
  constructor
  · intro H
    exact H.2
  · intro Hrest
    exact ⟨accepts_fo_vacuous_no_entries G f Hno, Hrest⟩

theorem slice_rest_fo_vacuous_no_entries (prev : List Image) (G : Image)
    (f : FinProcInput) (Hin : G ∈ prev)
    (Hno : ∀ en, ¬ valid_entry G en (to_proc_input f)) :
    ¬ slice_rest_fo prev f := by
  intro Hrest
  exact Hrest G Hin (accepts_fo_vacuous_no_entries G f Hno)

/-- The measure layer needs no new shape: the predicate-indexed bound at
    the pinned acceptance predicate IS [Measure.weight_bound_T_fo],
    both directions the identity on proofs, because
    [Classifier.rejects_fo C f] is by definition
    [FinInput.valid_fin_input f /\ ~ Classifier.accepts_fo C f].  The
    counterpart of [weight_bound_pred_of_classifier], and it is what lets this
    section leave [weight_bound_pred_T] untouched. -/
theorem weight_bound_pred_of_classifier_fo (C : Image) (w : FinProcInput → Rat)
    (M b : Rat) :
    weight_bound_T_fo C w M b ↔ weight_bound_pred_T (accepts_fo C) w M b := by
  constructor
  · intro Hbound l Hnd Hall
    exact Hbound l Hnd (fun f Hin => Hall f Hin)
  · intro Hbound l Hnd Hall
    exact Hbound l Hnd (fun f Hin => Hall f Hin)

/- -------------------------------------------------------------------------
   The per-slice obligations, under a configuration
   ------------------------------------------------------------------------- -/

/-- [gated_slice_T] with both runs under [cfg].  The baseline shell with
    one hypothesis added and NOTHING else moved, exactly as the
    unparameterized form is: entries quantified independently and inside
    the input, the input shared between the runs, each run seeded with
    its role's allocation budget.  [cfg] leads the argument list, which
    is the order [Equivalence.strong_universal_T_scfg] discharges its
    own section variables in. -/
def gated_slice_T_scfg (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_scfg cfg Src A en_s en_a (to_proc_input f)

/-- The error-free twin, over
    [Equivalence.strong_equiv_error_free_scfg], and it inherits that
    statement's properties whole under every configuration: no
    [Run.bh_all_errors] escape, no separate [Equivalence.modeled]
    conjunct. -/
def gated_slice_error_free_T_scfg (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop) : Prop :=
  ∀ f : FinProcInput,
    valid_fin_input f →
    P f →
    ∀ en_s en_a,
      valid_entry Src en_s (to_proc_input f) →
      valid_entry A en_a (to_proc_input f) →
      strong_equiv_error_free_scfg cfg Src A en_s en_a (to_proc_input f)

/-- MEANING PRESERVED: at [Run.may_fail_cfg] each is the statement above
    this section, so every existing slice proof keeps its text.  An
    [<->] rather than a conversion, for the reason
    [Equivalence.strong_equiv_scfg_may_fail] is one — [Run.run_scfg]
    walks [Run.sstep_cfg] where [Run.run] walks [Run.sstep], and the two
    are the same relation by a lemma and not by definition. -/
theorem gated_slice_T_scfg_may_fail (Src A : Image) (P : FinProcInput → Prop) :
    gated_slice_T_scfg may_fail_cfg Src A P ↔ gated_slice_T Src A P := by
  unfold gated_slice_T_scfg gated_slice_T
  constructor
  · intro H f Hf HP en_s en_a Hs Ha
    exact (strong_equiv_scfg_may_fail Src A en_s en_a (to_proc_input f)).mp
      (H f Hf HP en_s en_a Hs Ha)
  · intro H f Hf HP en_s en_a Hs Ha
    exact (strong_equiv_scfg_may_fail Src A en_s en_a (to_proc_input f)).mpr
      (H f Hf HP en_s en_a Hs Ha)

theorem gated_slice_error_free_T_scfg_may_fail (Src A : Image)
    (P : FinProcInput → Prop) :
    gated_slice_error_free_T_scfg may_fail_cfg Src A P
    ↔ gated_slice_error_free_T Src A P := by
  unfold gated_slice_error_free_T_scfg gated_slice_error_free_T
  constructor
  · intro H f Hf HP en_s en_a Hs Ha
    exact (strong_equiv_error_free_scfg_may_fail Src A en_s en_a (to_proc_input f)).mp
      (H f Hf HP en_s en_a Hs Ha)
  · intro H f Hf HP en_s en_a Hs Ha
    exact (strong_equiv_error_free_scfg_may_fail Src A en_s en_a (to_proc_input f)).mpr
      (H f Hf HP en_s en_a Hs Ha)

/-- A slice obligation is WEAKER than the ungated one at the SAME
    configuration, at every predicate: the counterpart of
    [gated_slice_of_universal], and the honest reading of what a slice
    proof buys under a configuration is the same as without one — less
    than a full proof, never more.

    The configurations must match, and no lemma here crosses them.
    This file states no route from
    [Equivalence.strong_universal_T_scfg cfg1] to
    [gated_slice_T_scfg cfg2] and none should be expected, for the
    reason [Equivalence]'s own configuration section gives: equivalence
    compares trace SETS, so removing executions can break an equality as
    easily as repair one.  That is an argument and not a proof — what
    would settle it is a Checks witness pair, two images equivalent
    under one configuration and refutably inequivalent under another,
    which needs binaries that call into an injected family and so cannot
    be built from the exit-only images this development's checks
    currently carry.  Read the sentence as the reason no such lemma is
    offered, not as a proved impossibility. -/
theorem gated_slice_T_scfg_of_universal (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop) (Huniv : strong_universal_T_scfg cfg Src A) :
    gated_slice_T_scfg cfg Src A P := by
  intro f Hvalid _ en_s en_a Hs Ha
  exact Huniv en_s en_a (to_proc_input f) Hs Ha Hvalid

theorem gated_slice_error_free_T_scfg_of_universal (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop)
    (Huniv : strong_universal_error_free_T_scfg cfg Src A) :
    gated_slice_error_free_T_scfg cfg Src A P := by
  intro f Hvalid _ en_s en_a Hs Ha
  exact Huniv en_s en_a (to_proc_input f) Hs Ha Hvalid

/-- Shrinking the slice weakens the obligation, at a fixed
    configuration: the counterpart of [gated_slice_mono], with the same
    [P]/[P'] binders and the same reason for them ([Q] is [QArith]'s
    rationals and this file states bounds over them). -/
theorem gated_slice_T_scfg_mono (cfg : SpuriousCfg) (Src A : Image)
    (P P' : FinProcInput → Prop) (Hsub : ∀ f, P' f → P f)
    (Hgated : gated_slice_T_scfg cfg Src A P) : gated_slice_T_scfg cfg Src A P' := by
  intro f Hvalid HP' en_s en_a Hs Ha
  exact Hgated f Hvalid (Hsub f HP') en_s en_a Hs Ha

theorem gated_slice_error_free_T_scfg_mono (cfg : SpuriousCfg) (Src A : Image)
    (P P' : FinProcInput → Prop) (Hsub : ∀ f, P' f → P f)
    (Hgated : gated_slice_error_free_T_scfg cfg Src A P) :
    gated_slice_error_free_T_scfg cfg Src A P' := by
  intro f Hvalid HP' en_s en_a Hs Ha
  exact Hgated f Hvalid (Hsub f HP') en_s en_a Hs Ha

/- -------------------------------------------------------------------------
   Bites, under a configuration
   ------------------------------------------------------------------------- -/

/-- The configured obligation is refutable, and by exactly the witness
    the unparameterized one is: a valid finite input IN the slice, a
    valid entry on each side, and the two runs UNDER [cfg] failing
    [Equivalence.strong_equiv_scfg].  All four hypotheses are
    load-bearing and a refutation missing any one of them refutes
    nothing.

    Note which configuration the failing runs are under.  A pair that
    fails [Equivalence.strong_equiv] refutes nothing here unless [cfg]
    is [Run.may_fail_cfg], because removing executions can repair a
    trace-set equality as easily as break one — this is the
    no-monotonicity paragraph of the header, in the form a reviewer
    actually meets it. -/
theorem gated_slice_T_scfg_refuted (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop) (f : FinProcInput) (en_s en_a : ExecEntry)
    (Hvalid : valid_fin_input f) (HP : P f)
    (Hs : valid_entry Src en_s (to_proc_input f))
    (Ha : valid_entry A en_a (to_proc_input f))
    (Hne : ¬ strong_equiv_scfg cfg Src A en_s en_a (to_proc_input f)) :
    ¬ gated_slice_T_scfg cfg Src A P := by
  intro Hgated
  exact Hne (Hgated f Hvalid HP en_s en_a Hs Ha)

theorem gated_slice_error_free_T_scfg_refuted (cfg : SpuriousCfg) (Src A : Image)
    (P : FinProcInput → Prop) (f : FinProcInput) (en_s en_a : ExecEntry)
    (Hvalid : valid_fin_input f) (HP : P f)
    (Hs : valid_entry Src en_s (to_proc_input f))
    (Ha : valid_entry A en_a (to_proc_input f))
    (Hne : ¬ strong_equiv_error_free_scfg cfg Src A en_s en_a (to_proc_input f)) :
    ¬ gated_slice_error_free_T_scfg cfg Src A P := by
  intro Hgated
  exact Hne (Hgated f Hvalid HP en_s en_a Hs Ha)

/-- THE TWO VACUITY ROUTES, stated rather than left to the header, and
    they are the routes the header names for the unparameterized form:
    a source image with no valid entry, and an empty slice.  Neither is
    closed by the configuration and neither is closed by this file — the
    first is [Equivalence.IMAGE_WF]'s, owed per image by a consuming
    checker, and the second is by design, an empty part carrying no mass
    with the measure side charging for that.

    BOTH IMAGES, not only the source.  The header asks
    [Equivalence.IMAGE_WF] for [Src] AND [A], and the shell quantifies
    an entry of each under its own validity hypothesis, so an
    unloadable TARGET empties the range exactly as an unloadable source
    does.  A reader who checked only the source half would have the
    obligation looking one-sided when it is not, which is why both are
    stated rather than one with a remark.

    Stated at the configured form because that is the form this section
    adds; the unparameterized ones follow through
    [gated_slice_T_scfg_may_fail] and are stated below rather than
    reproved. -/
theorem gated_slice_T_scfg_vacuous_no_source_entries (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry Src en (to_proc_input f)) :
    gated_slice_T_scfg cfg Src A P := by
  intro f _ _ en_s en_a Hs _
  exact absurd Hs (Hno f en_s)

theorem gated_slice_T_scfg_vacuous_empty_slice (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hempty : ∀ f, valid_fin_input f → ¬ P f) :
    gated_slice_T_scfg cfg Src A P := by
  intro f Hf HP
  exact absurd HP (Hempty f Hf)

theorem gated_slice_T_scfg_vacuous_no_target_entries (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry A en (to_proc_input f)) :
    gated_slice_T_scfg cfg Src A P := by
  intro f _ _ en_s en_a _ Ha
  exact absurd Ha (Hno f en_a)

theorem gated_slice_error_free_T_scfg_vacuous_no_source_entries (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry Src en (to_proc_input f)) :
    gated_slice_error_free_T_scfg cfg Src A P := by
  intro f _ _ en_s en_a Hs _
  exact absurd Hs (Hno f en_s)

theorem gated_slice_error_free_T_scfg_vacuous_empty_slice (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hempty : ∀ f, valid_fin_input f → ¬ P f) :
    gated_slice_error_free_T_scfg cfg Src A P := by
  intro f Hf HP
  exact absurd HP (Hempty f Hf)

theorem gated_slice_error_free_T_scfg_vacuous_no_target_entries (cfg : SpuriousCfg)
    (Src A : Image) (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry A en (to_proc_input f)) :
    gated_slice_error_free_T_scfg cfg Src A P := by
  intro f _ _ en_s en_a _ Ha
  exact absurd Ha (Hno f en_a)

/-- ... and the unparameterized forms, as corollaries through the
    [Run.may_fail_cfg] bridge rather than as second proofs.  They belong
    to the statements above this section and are stated here so the two
    read together; the routes are the ones that section's header
    already names in prose. -/
theorem gated_slice_T_vacuous_no_source_entries (Src A : Image)
    (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry Src en (to_proc_input f)) :
    gated_slice_T Src A P :=
  (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_no_source_entries may_fail_cfg Src A P Hno)

theorem gated_slice_T_vacuous_empty_slice (Src A : Image)
    (P : FinProcInput → Prop)
    (Hempty : ∀ f, valid_fin_input f → ¬ P f) :
    gated_slice_T Src A P :=
  (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_empty_slice may_fail_cfg Src A P Hempty)

theorem gated_slice_T_vacuous_no_target_entries (Src A : Image)
    (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry A en (to_proc_input f)) :
    gated_slice_T Src A P :=
  (gated_slice_T_scfg_may_fail Src A P).mp
    (gated_slice_T_scfg_vacuous_no_target_entries may_fail_cfg Src A P Hno)

theorem gated_slice_error_free_T_vacuous_no_source_entries (Src A : Image)
    (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry Src en (to_proc_input f)) :
    gated_slice_error_free_T Src A P :=
  (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_no_source_entries may_fail_cfg Src A P Hno)

theorem gated_slice_error_free_T_vacuous_empty_slice (Src A : Image)
    (P : FinProcInput → Prop)
    (Hempty : ∀ f, valid_fin_input f → ¬ P f) :
    gated_slice_error_free_T Src A P :=
  (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_empty_slice may_fail_cfg Src A P Hempty)

theorem gated_slice_error_free_T_vacuous_no_target_entries (Src A : Image)
    (P : FinProcInput → Prop)
    (Hno : ∀ f en, ¬ valid_entry A en (to_proc_input f)) :
    gated_slice_error_free_T Src A P :=
  (gated_slice_error_free_T_scfg_may_fail Src A P).mp
    (gated_slice_error_free_T_scfg_vacuous_no_target_entries may_fail_cfg Src A P Hno)

end LinuxSem.EquivalenceDefinition.GatedSize
