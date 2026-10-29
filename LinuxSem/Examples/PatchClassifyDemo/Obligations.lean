/-
  * Examples.PatchClassifyDemo.Obligations — the five obligations
    `PatchClassifySpec.SPEC_PATCH_CLASSIFY` asks for

  DEMO FILE (not part of the trusted specification).  `Images` built
  the six images, `Verdicts` proves what each one does at every valid
  entry on every input, `Traces` proves what each one EMITS, and
  `Distribution` declared a weight.  This file is the payoff: the five
  parameters of
  `EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY`, proved
  of those six images and that distribution, so that the surface has a
  satisfying instance.

  ** The five, and where each one's content is

  - `P1_P2_strong_universal`: the two patched binaries are observably
    equivalent.  All of its content is `Traces`': the two trace sets
    are the same two-element set, and equality of the sets is the
    whole of `Equivalence.equiv`'s non-escape branch.  Note that the
    two images being byte-identical does NOT make it trivial —
    `Equivalence.strong_universal_T` quantifies the two
    `Run.ExecEntry` records INDEPENDENTLY and runs the two sides at
    DIFFERENT allocation budgets, so a program whose observable
    behavior depended on the stack placement, the break, the mmap base
    or the budget would fail this theorem against itself.  What makes
    it come out is that these programs depend on none of them, which
    is `Verdicts`' indifference lemma, and it had to be proved.
  - `C1_classifies_patch_diff`: the patch-difference classifier fires
    everywhere, correctly.  Its spec is FALSE on every input, because
    `O1` exits 1 and `P1` exits 0, so the classifier is right to fire;
    the iff is then two refutations and the totality disjunct is the
    verdict from `Verdicts`.
  - `C2_classifies_good_inputs`: the same shape over the other
    question.  Both originals here are ERROR-FREE, so the refutation
    cannot go through `Equivalence.strong_equiv_error_free`'s two
    error clauses and goes through the trace clause instead — the two
    originals disagree on every input.
  - `C1_weight_bound` and `C2_weight_bound`, both at `b = 1`: see
    `Distribution`.  The fire set is the whole input space, so the
    whole-space certificate is what discharges them.  That the
    multiplier is not free is a separate claim and is proved
    separately, at the end of this file: it cannot be dropped to `0`
    and it cannot be halved.  It is NOT proved that `1` is the least
    provable multiplier — see `demo_b_half_refutable` for why that is
    a different statement.

  ** What is deliberately degenerate, said out loud

  Both classifiers fire on EVERY valid finite input, and both bounds
  are the trivial multiplier.  That is not a shortcut taken to make
  the proofs go through — it is the CORRECT answer for this pair of
  originals, and the honest bound for a fire set that really is
  everything.  The demo's README names the refinement that would make
  the numbers interesting (a program that reads its input, whose
  classifier fires on a cylinder rather than on the whole space, with
  `b < 1` from a cylinder bound), and why it is a separate exercise.

  What the degeneracy must not be allowed to become is vacuity, and
  the two are easy to confuse.  A classifier image with no valid entry
  would satisfy both classifier obligations
  (`Classifier.decides_vacuous_no_entries`) and both weight bounds at
  every multiplier including zero
  (`Classifier.accepts_vacuous_no_entries`) with nothing established.
  The bites at the end of this file are what separate the demo from
  that: the classifier images have valid entries, exhibited; their
  reject sets contain named inputs; and a distribution that charged a
  unit per input would REFUSE the bound proved here.

  ** What this tree reproduces

  All five obligations, their bites, and the reject-set and
  multiplier-necessity arguments are here.  The classifier obligations
  run through `Traces`' trace-set characterization (the trace conjunct of
  `Classifier.agree` is the only route a refutation has, once the
  verdicts make the error and modeled conjuncts hold), so this file
  imports `Traces`; the agreement statements themselves are two
  refutations and one agreement, each a few lines over those trace sets.
-/
import LinuxSem.Examples.PatchClassifyDemo.Images
import LinuxSem.Examples.PatchClassifyDemo.Verdicts
import LinuxSem.Examples.PatchClassifyDemo.Traces
import LinuxSem.Examples.PatchClassifyDemo.Distribution
import LinuxSem.Checks.Examples
import LinuxSem.EquivalenceDefinition.MeasureLib

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
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.Measure
open LinuxSem.EquivalenceDefinition.MeasureLib

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Obligations

open Images
open Distribution
open Verdicts
open Traces

/- THE ONE UPWARD-FACING `open` IN THE TREE: `demo_entry` is a `Checks`
   fixture, and this file is below `Checks.Examples` (.y).  Naming it
   through the module rather than copying the record keeps the trap and
   the QA file's entry the SAME value. -/
open LinuxSem.Checks.Examples (demo_entry)

/- =========================================================================
   Valid entries: the premise every obligation quantifies over is
   INHABITED, per image
   ========================================================================= -/

/-- Every statement below ranges over valid `Run.ExecEntry`s, and an
    image with none satisfies all of them saying nothing — the vacuity
    route `Classifier`'s and `PatchClassifySpec`'s headers both name.
    `Equivalence.image_brk_satisfiable_entry` turns `Images`' six
    `Equivalence.image_brk_satisfiable` checks into the witnesses, one
    line each.

    THE INPUT IS A PARAMETER, and must be: `Run.valid_entry` asks that
    the entry stack image fit below the top of the address space
    (`Run.entry_stack_fits`), and that image is built from the input's
    argv and envp.  So an entry is valid FOR AN INPUT, and inhabitation
    is a statement about one — with `Run.valid_input` as the premise,
    since it is `Run.valid_argv` and `Run.valid_envp` that cap the span
    at `Run.entry_stack_span_max` and leave the bottom of the sp window
    room for it.  An input outside those caps has no valid entry at all,
    and every statement below that quantifies an entry carries the
    validity premise for exactly that reason.

    These are not decoration: two of the proofs below REFUTE a universal
    over valid entries (`Classifier.agree`'s trace conjunct, and
    `Classifier.good_input`), which cannot be done without exhibiting an
    entry at which to refute it. -/
theorem O1_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry O1_image en inp :=
  image_brk_satisfiable_entry O1_image inp H O1_brk_satisfiable

theorem O2_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry O2_image en inp :=
  image_brk_satisfiable_entry O2_image inp H O2_brk_satisfiable

theorem P1_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry P1_image en inp :=
  image_brk_satisfiable_entry P1_image inp H P1_brk_satisfiable

theorem P2_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry P2_image en inp :=
  image_brk_satisfiable_entry P2_image inp H P2_brk_satisfiable

theorem C1_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry C1_image en inp :=
  image_brk_satisfiable_entry C1_image inp H C1_brk_satisfiable

theorem C2_valid_entry_exists (inp : ProcInput) (H : valid_input inp) :
    ∃ en, valid_entry C2_image en inp :=
  image_brk_satisfiable_entry C2_image inp H C2_brk_satisfiable

/-- The trap that makes the six lemmas above worth writing rather than
  copying an entry from the QA fixture:
    `Checks.Examples.demo_entry` is NOT a valid entry for these images.
    Its program break is 0x1000, which is below the demo's page-rounded
    image top — the demo's segments reach 0x11150, where the `Checks`
    fixture's reach 0x10c.

  WHY THE ENTRY IS NAMED THROUGH `Checks`.  `Checks.Examples` sits
  BELOW this directory: it depends on
  `Verdicts`/`ExitsC`, because `exits_c` is defined there — so the
  fixture is reached from here by a dependency that runs against the
  layering.  That inversion is deliberate: one fixture and one proof,
  not two copies that could drift.

    The refutation itself never looks at the entry's stack pointer or its
    mapping base: `valid_entry_va` conjoins the SAME `valid_brk` at every
    VA size, and `valid_brk`'s first conjunct asks the break to be at or
    above `reserved_top (segments_reserved …)`, which the demo's own LOAD
    segments put far above 0x1000.  So only that conjunct can fail, which
    is why the negation holds for EVERY input — including every one whose
    other four conjuncts are satisfied — and for every VA size. -/
theorem demo_entry_is_not_valid_here (inp : ProcInput) :
    ¬ valid_entry O1_image demo_entry inp := by
  intro h
  unfold valid_entry valid_entry_va at h
  obtain ⟨-, hbrk, -, -⟩ := h
  obtain ⟨h1, -, -⟩ := hbrk
  have htop : 8192 ≤ reserved_top (segments_reserved O1_image.img_segments) := by decide
  have hbrk0 : ((demo_entry.en_brk).toNat : Int) = 4096 := by decide
  omega

/- =========================================================================
   OBLIGATIONS 4 and 5: the two weight bounds, at b1 = b2 = 1
   ========================================================================= -/

/-- Both classifiers reject everything, so the set the bound measures is
    the whole input space.  `Distribution.demo_whole_space_bound` is the
    whole-space certificate of `MeasureLib.stdin_geometric` with the
    arithmetic done; neither bound reads anything about the classifier
    it is stated for, which is the accurate way to prove a claim about a
    fire set that is everything — and it is also why proving the
    multiplier NECESSARY is separate work, done at the end of this file.

    The two are stated separately, one per classifier image, because
    `PatchClassifySpec.SPEC_PATCH_CLASSIFY` declares them separately —
    and because `C1` and `C2` share a segment list, so a single lemma
    "the bound holds for the classifier" would silently be doing the
    work of two. -/
theorem C1_weight_bound : weight_bound_T C1_image DemoDist.w DemoDist.M 1 :=
  demo_whole_space_bound C1_image

theorem C2_weight_bound : weight_bound_T C2_image DemoDist.w DemoDist.M 1 :=
  demo_whole_space_bound C2_image

/- =========================================================================
   The obligations bite
   ========================================================================= -/

/-- A finite input over the distribution's fixed launch-time
    environment, with a chosen standard input.  Built through
    `MeasureLib.core_input` so that `MeasureLib.fin_core_core_input`
    reads its core back with no computation — the inputs below differ
    in exactly the field the measure layer charges for. -/
def demo_input (s : List byte) : FinProcInput :=
  core_input (FinCore.mkFinCore demo_argv demo_envp demo_fs s)

/-- ... and it really is a valid finite input, whatever the standard
    input: `FinInput.valid_fin_input` constrains argv, envp, the file
    system, the two ids, the soft descriptor limit, the blocked signal
    mask and the published hart capabilities, and says nothing about
    `FinInput.fin_stdin`.  All seven come from `MeasureLib.core_input`,
    which puts zero in the descriptor limit and the mask — inside
    `Run.valid_nofile`'s ceiling, and the empty mask
    `Run.valid_sigmask` asks for — and `StackLayout.hwcap_rv64gc` in the
    hwcap, because `Run.valid_hwcap` admits two words and a zero is
    neither.  Without this the reject-set bite below would be about
    records the obligations never quantify over.

    The last conjunct is the one clause that is a FIX rather than a
    narrowing (`Run.valid_urandom` asks the declared random stream never
    to end), and `MeasureLib.core_input` leaves it at
    `default_urandom`, so `State.default_urandom_infinite` discharges it.

  The case split is `repeat' apply And.intro`, and each leaf is closed
  by `omega`, `decide`, `Or.inl rfl`, `default_urandom_infinite`, or
  `simp_all` for the four `Forall`-shaped leaves — a closer per
  conjunct, in a fixed order, with the witnesses the clauses name. -/
theorem demo_input_is_valid (s : List byte) : valid_fin_input (demo_input s) := by
  unfold valid_fin_input valid_input demo_input
  simp only [to_proc_input, core_input, demo_argv, demo_envp, demo_fs,
    valid_argv, valid_envp, valid_creds, valid_id, valid_nofile, valid_sigmask,
    valid_hwcap, valid_urandom, Fs.valid_fs, Fs.fs_keys_relative,
    total_arg_bytes, stream_of_list_then, in_fs, List.mem_singleton,
    List.not_mem_nil]
  repeat' apply And.intro
  all_goals first
    | omega
    | decide
    | exact Or.inl rfl
    | exact default_urandom_infinite
    | (intro x hx; simp_all)

/-- `MeasureLib`'s lower witness family, shown to lie inside the demo's
    reject set.  `MeasureLib.geo_lower_witness` is literally
    `map (fun s => core_input (mkFinCore argv envp fs s)) (short_inputs k)`
    — the same family `demo_input` belongs to — so at the demo's own
    launch-time environment every member is one of the records
    `demo_input_is_valid` validates.

    This one-line bridge is the step `MeasureLib`'s header says a
    consumer must NOT read in for free: the library is explicit that its
    lower certificate says nothing about whether the witness cores are
    rejected by anything, or even valid.  Here they are both, and it is
    proved rather than assumed — which is the only reason the multiplier
    refutation is available to this demo. -/
theorem demo_geo_witness_rejected (C : Image)
    (Hall : ∀ f, valid_fin_input f → rejects C f) (k : Nat) (f : FinProcInput)
    (Hin : f ∈ geo_lower_witness demo_argv demo_envp demo_fs k) :
    rejects C f := by
  unfold geo_lower_witness at Hin
  rw [List.mem_map] at Hin
  obtain ⟨s, _, rfl⟩ := Hin
  exact Hall _ (demo_input_is_valid s)

/-- THE MULTIPLIER IS NOT FREE, at `b = 0`.  One rejected input of
    positive weight is enough: the empty standard input weighs `1 / 8`
    under `Distribution.DemoDist` (`Distribution.demo_w_positive`), and
    a bound of `0` would have to hold of the one-element list naming
    it.  So the two obligations are not the ones an image with no valid
    entry gets for nothing — that image would satisfy `b = 0`
    (`Classifier.accepts_vacuous_no_entries`). -/
theorem demo_b_zero_refutable (C : Image)
    (Hall : ∀ f, valid_fin_input f → rejects C f) :
    ¬ weight_bound_T C DemoDist.w DemoDist.M 0 := by
  intro Hb
  have Hnd : (List.map fin_core [demo_input []]).Nodup := by simp
  have Hrej : ∀ f, f ∈ [demo_input []] → rejects C f := by
    intro f hf
    rw [List.mem_singleton] at hf
    subst hf
    exact Hall _ (demo_input_is_valid [])
  have h := Hb [demo_input []] Hnd Hrej
  have hp : 0 < DemoDist.w (demo_input []) := demo_w_positive
  simp only [sum_weights, List.foldr_cons, List.foldr_nil] at h
  rw [Rat.zero_mul] at h
  grind

/-- ... and not at `b = 1 / 2` either, which is the sharper claim and
    the one that needs the library's lower witness.  The family at
    `k = 6` — every standard input of length under six, over the fixed
    environment — is admissible (`MeasureLib.geo_lower_witness_nodup`),
    every member of it is rejected (above), and it weighs exactly
    `1 - (7 / 8)^6 = 144495 / 262144`, a shade over 0.55.  A bound of
    half the declared mass would have to cover it, and does not.

    WHAT THIS DOES AND DOES NOT SAY.  It says the demo's `b = 1` is a
    real claim about `Distribution.DemoDist`: the multiplier cannot be
    halved, so the number is not one that any distribution and any
    classifier would satisfy.  It does NOT say `1` is the LEAST provable
    multiplier, and that gap is deliberate rather than an omission —
    `MeasureLib`'s header names the inference from "the declared mass is
    the least upper bound of the admissible partial sums" to "the `b * M`
    of `Measure.weight_bound_T` cannot be lowered for a given fire set"
    as the misreading a consumer of that library is positioned to make.
    Every `b` strictly between `144495 / 262144` and `1` is left open
    here, and closing the gap would take a lower certificate over the
    REJECTED lists specifically, at every `k` rather than at one. -/
theorem demo_b_half_refutable (C : Image)
    (Hall : ∀ f, valid_fin_input f → rejects C f) :
    ¬ weight_bound_T C DemoDist.w DemoDist.M ((1 : Rat) / 2) := by
  intro Hb
  obtain ⟨Hnd, Hsum⟩ := stdin_geometric_mass_lower_witness demo_p_stop demo_argv
    demo_envp demo_fs demo_p_stop_nonneg demo_p_stop_le_1 6
  have h := Hb (geo_lower_witness demo_argv demo_envp demo_fs 6) Hnd
    (demo_geo_witness_rejected C Hall 6)
  have h1 : sum_weights (cd_lift demo_cd)
      (geo_lower_witness demo_argv demo_envp demo_fs 6)
      ≤ ((1 : Rat) / 2) * demo_cd.cd_mass := h
  rw [← core_sum_cd_lift demo_cd] at h1
  have hsum' : core_sum demo_cd.cd_weight
      (geo_lower_witness demo_argv demo_envp demo_fs 6) =
      1 - Qpow (1 - demo_p_stop) 6 := Hsum
  rw [hsum'] at h1
  have hmass : demo_cd.cd_mass = 1 := rfl
  rw [hmass] at h1
  have harith : 1 - Qpow (1 - demo_p_stop) 6 = (144495 : Rat) / 262144 := by
    unfold demo_p_stop
    rw [Qpow_succ, Qpow_succ, Qpow_succ, Qpow_succ, Qpow_succ, Qpow_succ, Qpow_0]
    grind
  rw [harith] at h1
  grind

/-- The spec the patch-difference classifier decides, named once so that
    the two `decides_fo` declarations can be compared against it: the
    conjunction of the two `Classifier.agree` statements, each at ITS
    pair's role budget.  This is `classifies_patch_diff_T`'s spec,
    unfolded — the same predicate, not a second one.  It is DECIDED by
    `C1_classifies_patch_diff` below, and the refutation runs through
    `patch_diff_spec_false`: the first conjunct is false at every valid
    input, so the spec is false wherever the classifier fires. -/
def C1_patch_diff_spec (inp : ProcInput) : Prop :=
  agree O1_image P1_image source_alloc_limit inp
  ∧ agree O2_image P2_image target_alloc_limit inp

/- =========================================================================
   The reject set is everything, and that costs something
   ========================================================================= -/

/-- THE REJECT SET IS EVERYTHING.  `Classifier.rejects` is the negation of
    `Classifier.accepts`, and refuting a universal over valid entries
    needs one exhibited entry — which is what `C1_valid_entry_exists` is
    for.  Without a statement of this shape the two bounds above would be
    compatible with an empty fire set, which is the vacuity `Measure`'s
    header warns about. -/
theorem C1_rejects_every_valid_input (f : FinProcInput) (Hf : valid_fin_input f) :
    rejects C1_image f := by
  obtain ⟨en, Hen⟩ := C1_valid_entry_exists (to_proc_input f) Hf
  exact rejects_by_exit1 C1_image f en Hf Hen
    (C1_must_exit_one classifier_alloc_limit en (to_proc_input f))

theorem C2_rejects_every_valid_input (f : FinProcInput) (Hf : valid_fin_input f) :
    rejects C2_image f := by
  obtain ⟨en, Hen⟩ := C2_valid_entry_exists (to_proc_input f) Hf
  exact rejects_by_exit1 C2_image f en Hf Hen
    (C2_must_exit_one classifier_alloc_limit en (to_proc_input f))

/-- ... AND THAT COSTS SOMETHING.  Two rejected inputs with distinct cores
    are enough to REFUTE the bound `1` under the unit weight at total `1`
    (`Measure.weight_bound_refutable`).  So the demo's `b = 1` is not a
    number that any classifier and any distribution would satisfy: it is a
    claim about this distribution, and a differently normalized one over
    the same reject set fails it.

    These are the records `demo_input_is_valid` validates, so the two
    witnesses are inside the support and inside the obligations'
    quantifier — the standard-input field is what distinguishes their
    cores. -/
theorem demo_reject_set_refutes_a_unit_weight :
    ¬ weight_bound_T C1_image (fun _ => (1 : Rat)) 1 1 := by
  refine weight_bound_refutable C1_image (demo_input [])
    (demo_input [BitVec.ofInt 8 0]) ?_ ?_ ?_
  · exact C1_rejects_every_valid_input _ (demo_input_is_valid [])
  · exact C1_rejects_every_valid_input _ (demo_input_is_valid [BitVec.ofInt 8 0])
  · intro h
    have h' := congrArg FinCore.core_stdin h
    simp [demo_input, fin_core_core_input] at h'

/-- The two instances, one per classifier image and stated separately for
    the reason the two bounds are: `C1` and `C2` share a segment list, and
    a single lemma about "the classifier" would be doing the work of
    two.  The multiplier cannot be dropped to `0` and cannot be halved. -/
theorem C1_bound_needs_the_multiplier :
    ¬ weight_bound_T C1_image DemoDist.w DemoDist.M 0
    ∧ ¬ weight_bound_T C1_image DemoDist.w DemoDist.M ((1 : Rat) / 2) :=
  ⟨demo_b_zero_refutable _ C1_rejects_every_valid_input,
   demo_b_half_refutable _ C1_rejects_every_valid_input⟩

theorem C2_bound_needs_the_multiplier :
    ¬ weight_bound_T C2_image DemoDist.w DemoDist.M 0
    ∧ ¬ weight_bound_T C2_image DemoDist.w DemoDist.M ((1 : Rat) / 2) :=
  ⟨demo_b_zero_refutable _ C2_rejects_every_valid_input,
   demo_b_half_refutable _ C2_rejects_every_valid_input⟩

/- =========================================================================
   The verdicts bite on the four images `Verdicts` left out
   ========================================================================= -/

/-! `Verdicts` proves the wrong-code refutation for `O1` and `P1`, the pair
    the patch-difference classifier is asked about.  The same refutation is
    what `Classifier.decides` needs of the CLASSIFIER images — "does not
    exit 0" is half of "the verdict is 1" — and the remaining two
    originals get it for symmetry.  Each is stated from the verdict of its
    OWN image; conversion would allow borrowing a sibling's (see `Images`'
    header), and the discipline is what keeps these four honest if the two
    classifiers are ever given different code. -/

theorem O2_does_not_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_reject O2_image lim en inp :=
  Verdicts.O2_does_not_exit_one lim en inp

theorem P2_does_not_exit_one (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_reject P2_image lim en inp :=
  Verdicts.P2_does_not_exit_one lim en inp

theorem C1_does_not_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_accept C1_image lim en inp :=
  Verdicts.C1_does_not_exit_zero lim en inp

theorem C2_does_not_exit_zero (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    ¬ must_exit_with verdict_accept C2_image lim en inp :=
  Verdicts.C2_does_not_exit_zero lim en inp

/- =========================================================================
   OBLIGATION 1: the two patches are observably equivalent
   ========================================================================= -/

/-- The error-free flavor, which is what actually falls out here: both
    patches are error-free (`Verdicts`) and their trace sets are the same
    two-element set (`Traces`).  `Equivalence.strong_equiv_error_free` is
    exactly those three conjuncts.

    Proved first because it is the STRONGER statement and it is free: the
    demo's programs cannot error, so nothing is being claimed that the
    images do not support.  The baseline obligation the SPEC asks for is
    derived from it below, by the library's own implication. -/
theorem P1_P2_strong_universal_error_free :
    strong_universal_error_free_T P1_image P2_image := by
  intro en_source en_target inp _ _ _
  refine ⟨P1_error_free _ _ _, P2_error_free _ _ _, fun tr => ?_⟩
  rw [P1_traces, P2_traces]

/-- THE OBLIGATION, as `PatchClassifySpec.SPEC_PATCH_CLASSIFY` declares
    it.  `Equivalence.strong_universal_error_free_implies` is the step,
    and it is the reason the stronger flavor is safe to prove first — the
    baseline check never rejects a pair the error-free proof accepts. -/
theorem P1_P2_strong_universal : strong_universal_T P1_image P2_image :=
  strong_universal_error_free_implies P1_image P2_image
    P1_P2_strong_universal_error_free

/- =========================================================================
   What the patch-difference classifier is asked about
   ========================================================================= -/

/-- The first pair NEVER agrees.  `O1` exits 1 and `P1` exits 0, so the
    exit-1 event is a trace of the original and not a trace of the patch,
    at the one pair of valid entries the refutation names — and
    `Classifier.agree`'s trace conjunct is universal over entry pairs, so
    one pair is enough to refute it.

    The trace conjunct is the ONLY available route: the verdicts' error and
    modeled facts make conjuncts two, three and four of
    `Classifier.agree` HOLD for this pair, since neither program can error,
    all-error or leave the modeled surface at any entry.

    Note what the input premise is and is not doing: these programs read
    nothing, so the pair disagrees on the CONTENT of every
    `State.ProcInput` whatever.  `Run.valid_input` is needed only to have
    an entry to disagree at. -/
theorem O1_P1_never_agree (inp : ProcInput) (Hinp : valid_input inp) :
    ¬ agree O1_image P1_image source_alloc_limit inp := by
  intro Hag
  obtain ⟨en1, Hen1⟩ := O1_valid_entry_exists inp Hinp
  obtain ⟨en2, Hen2⟩ := P1_valid_entry_exists inp Hinp
  exact P1_never_emits_exit_one source_alloc_limit en2 inp
    (((Hag.1 en1 en2 Hen1 Hen2) _).mp
      (O1_emits_exactly_exit_one source_alloc_limit en1 inp))

/-- The second pair ALWAYS agrees — a bonus and not an obligation: the
    conjunction the classifier decides is already false on its first
    conjunct.  It is proved because a reader should be able to see that
    the classifier fires for the right reason.

    All four conjuncts are discharged, and three of them by the SAME facts
    that made the refutation above go through the trace conjunct: neither
    image can error, all-error or go unmodeled, so each of the three
    existential iffs holds with both sides empty. -/
theorem O2_P2_agree (inp : ProcInput) :
    agree O2_image P2_image target_alloc_limit inp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro enX enY _ _ tr
    rw [O2_traces, P2_traces]
  · constructor
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (O2_error_free _ _ _)
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (P2_error_free _ _ _)
  · constructor
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (fun h => O2_error_free _ _ _ (run_all_errors_errors _ _ _ _ h))
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (fun h => P2_error_free _ _ _ (run_all_errors_errors _ _ _ _ h))
  · constructor
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (O2_modeled _ _ _)
    · rintro ⟨en, _, Hb⟩; exact absurd Hb (P2_modeled _ _ _)

/-- ... so the classifier's spec is false everywhere, which is the sentence
    the obligation below consumes. -/
theorem patch_diff_spec_false (inp : ProcInput) (Hinp : valid_input inp) :
    ¬ (agree O1_image P1_image source_alloc_limit inp
       ∧ agree O2_image P2_image target_alloc_limit inp) :=
  fun H => O1_P1_never_agree inp Hinp H.1

/- =========================================================================
   OBLIGATION 2: the patch-difference classifier
   ========================================================================= -/

/-- `C1` decides, on every valid finite input at every valid entry, whether
    both patches preserved behavior — by answering "no" everywhere, which
    is correct everywhere.

    Both halves of `Classifier.decides` are here.  The IFF: exiting 0 is
    impossible (`C1_does_not_exit_zero`), and the spec is false
    (`patch_diff_spec_false`), so the two sides are both false and the
    equivalence holds — with each side refuted separately rather than one
    being inferred from the other, which is what makes this a correctness
    claim and not a tautology.  TOTALITY: the classifier exits 1, always,
    at every budget and every entry (`Verdicts`). -/
theorem C1_classifies_patch_diff :
    classifies_patch_diff_T O1_image P1_image O2_image P2_image C1_image := by
  intro f Hf en Hen
  exact ⟨⟨fun H0 => absurd H0 (C1_does_not_exit_zero classifier_alloc_limit en (to_proc_input f)),
          fun Hspec => absurd Hspec (patch_diff_spec_false (to_proc_input f) Hf)⟩,
    Or.inr (C1_must_exit_one classifier_alloc_limit en (to_proc_input f))⟩

theorem C1_patch_diff_is_exactly_its_two_declarations :
    decides_fo C1_image C1_patch_diff_spec
      ↔ (decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec
         ∧ decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec) :=
  decides_fo_hwcap_splits C1_image C1_patch_diff_spec

theorem C1_decides_patch_diff_under_each_declaration
    (Hdec : classifier_decided C1_image) :
    decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec
    ∧ decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec := by
  exact C1_patch_diff_is_exactly_its_two_declarations.mp
    (decides_fo_of_decides C1_image C1_patch_diff_spec Hdec C1_classifies_patch_diff)

theorem C1_declarations_recover_the_undeclared_obligation
    (Hgc : decides_fo_hwcap_rv64gc C1_image C1_patch_diff_spec)
    (Hgcv : decides_fo_hwcap_rv64gcv C1_image C1_patch_diff_spec) :
    decides_fo C1_image C1_patch_diff_spec :=
  C1_patch_diff_is_exactly_its_two_declarations.mpr ⟨Hgc, Hgcv⟩

/- =========================================================================
   What the good-input classifier is asked about
   ========================================================================= -/

/-- No input is good.  `Classifier.good_input` is
    `Equivalence.strong_equiv_error_free` at all entry pairs — error
    freedom of both originals AND equality of their trace sets — and the
    refutation goes through the trace clause, not through the error
    clauses.

    That is worth saying plainly, because the obvious guess is wrong.
    `O1` is the DEFECT of this exercise and it does not crash: it exits 1,
    cleanly, on every input (`Verdicts.O1_error_free`).  So both originals
    satisfy the two error-freedom conjuncts, and what fails is that one of
    them reports failure where the other reports success — which is
    exactly the defect a good-input classifier is supposed to notice. -/
theorem O1_O2_no_good_input (inp : ProcInput) (Hinp : valid_input inp) :
    ¬ good_input O1_image O2_image inp := by
  intro Hg
  obtain ⟨en1, Hen1⟩ := O1_valid_entry_exists inp Hinp
  obtain ⟨en2, Hen2⟩ := O2_valid_entry_exists inp Hinp
  obtain ⟨-, -, Htr⟩ := Hg en1 en2 Hen1 Hen2
  exact O2_never_emits_exit_one target_alloc_limit en2 inp
    ((Htr _).mp (O1_emits_exactly_exit_one source_alloc_limit en1 inp))

/- =========================================================================
   OBLIGATION 3: the good-input classifier
   ========================================================================= -/

/-- `C2` decides whether the two originals were already error-free
    equivalent — by answering "no" everywhere, which is again correct
    everywhere.  Same shape as `C1_classifies_patch_diff`, different
    question and a different refutation underneath it. -/
theorem C2_classifies_good_inputs :
    classifies_good_inputs_T O1_image O2_image C2_image := by
  intro f Hf en Hen
  exact ⟨⟨fun H0 => absurd H0 (C2_does_not_exit_zero classifier_alloc_limit en (to_proc_input f)),
          fun Hspec => absurd Hspec (O1_O2_no_good_input (to_proc_input f) Hf)⟩,
    Or.inr (C2_must_exit_one classifier_alloc_limit en (to_proc_input f))⟩

/- =========================================================================
   The classifiers answer, observably
   ========================================================================= -/

/-- `Classifier.decides`' totality disjunct is a claim about exit codes;
    this turns it into the event an observer of the run would actually
    read — and `Traces` pins the trace exactly, so the answer is the only
    thing either classifier ever emits. -/
theorem C1_answers_one (f : FinProcInput) (en : ExecEntry) :
    bh_traces (run C1_image classifier_alloc_limit en (to_proc_input f))
      [event.ExitEv verdict_reject (in_fs (to_proc_input f))] :=
  (C1_traces _ en (to_proc_input f) _).mpr (Or.inr rfl)

/-- ... and never the other one, so a reader of the exit code is not
    reading a coin flip.  This is `Classifier.decides`' iff seen from the
    trace side. -/
theorem C1_never_answers_zero (f : FinProcInput) (en : ExecEntry) :
    ¬ bh_traces (run C1_image classifier_alloc_limit en (to_proc_input f))
      [event.ExitEv verdict_accept (in_fs (to_proc_input f))] :=
  no_exit_zero_trace_of_exit_one C1_image C1_traces _ en (to_proc_input f)

/-- Neither classifier accepts anything.  The mechanism is
    `Classifier.rejects_by_exit1`, inside `C1_rejects_every_valid_input`:
    it takes the valid entry as an argument and turns the exit-1 verdict
    there into the failure of `Classifier.accepts`' universal. -/
theorem C1_accepts_nothing (f : FinProcInput) (Hf : valid_fin_input f) :
    ¬ accepts C1_image f :=
  (C1_rejects_every_valid_input f Hf).2

theorem C2_accepts_nothing (f : FinProcInput) (Hf : valid_fin_input f) :
    ¬ accepts C2_image f :=
  (C2_rejects_every_valid_input f Hf).2

/-- The transfer that DOES spend the inhabitation, stated because it is the
    useful export: under `Classifier.decides`, accepting an input and the
    spec holding of it are the same statement.  Read against
    `C1_accepts_nothing` it is the demo's whole story in one line: the left
    side is false everywhere, so the right side is too, so the classifier
    fires everywhere and is right to. -/
theorem C1_accepts_iff_spec (f : FinProcInput) (Hf : valid_fin_input f) :
    (accepts C1_image f
     ↔ (agree O1_image P1_image source_alloc_limit (to_proc_input f)
        ∧ agree O2_image P2_image target_alloc_limit (to_proc_input f))) := by
  obtain ⟨en0, Hen0⟩ := C1_valid_entry_exists (to_proc_input f) Hf
  constructor
  · intro Hacc
    exact (C1_classifies_patch_diff f Hf en0 Hen0).1.1 (Hacc en0 Hen0)
  · intro Hspec en Hen
    exact (C1_classifies_patch_diff f Hf en Hen).1.2 Hspec

theorem C2_accepts_iff_spec (f : FinProcInput) (Hf : valid_fin_input f) :
    (accepts C2_image f ↔ good_input O1_image O2_image (to_proc_input f)) := by
  obtain ⟨en0, Hen0⟩ := C2_valid_entry_exists (to_proc_input f) Hf
  constructor
  · intro Hacc
    exact (C2_classifies_good_inputs f Hf en0 Hen0).1.1 (Hacc en0 Hen0)
  · intro Hspec en Hen
    exact (C2_classifies_good_inputs f Hf en Hen).1.2 Hspec

end Obligations

end LinuxSem.Examples.PatchClassifyDemo
