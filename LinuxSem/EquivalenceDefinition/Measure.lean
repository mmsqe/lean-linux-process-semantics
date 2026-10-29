/-
  * EquivalenceDefinition.Measure — weighted measure of the fire set

  TRUST BOUNDARY: this file is part of the trusted specification.
  Proof files never edit it.  A top-level check that ascribes against
  a module type carrying [weight_bound_T] depends on the definitions
  here remaining fixed, exactly as the baseline check depends on
  [Equivalence].

  [Classifier.rejects] names a SET of finite inputs — the ones a
  classifier does not accept — with no size on it.  A task
  that asks "how much of the input space does the classifier reject"
  needs a way to add sizes up, and this file is that: a
  task-supplied WEIGHT on [FinInput.FinProcInput], and the claim that
  no finite list of rejected inputs with pairwise distinct CORES sums
  past a stated multiple of a declared total.  Cores, not records: the
  reason is the third section below, and it is the difference between
  an obligation and an unsatisfiable one.

  ** The first use of [Rat] in this tree, and what that changes

  Every numeric quantity elsewhere in this development is a bitvector or
  an [Int]: sizes, codes, budgets, all decided by `decide` against a
  concrete value.  [Rat] is a NORMALIZED structure, so its equality is
  Leibniz equality and deciding a closed comparison works — but deciding
  a [Rat] EQUALITY is still the wrong tool: it can succeed only for a
  particular representative, and the obligation here is an order fact
  ([weight_bound_T] itself, and the three transport lemmas below).  The
  one equality stated is [sum_weights_ext], nothing here decides a [Rat]
  equality by computation, and a downstream consumer that wants to show a
  submitted bound to a reader PRINTS the [Rat] value rather than
  comparing it against one.  [weight_bound_refutable]'s proof does
  compute, and that is not a contradiction of the warning above: the
  computation is on a BOOLEAN comparison ([Rat] order collapsed to
  [Bool]), which reduces to [false], never on a [Rat] equality of open
  or checker-supplied terms the way the forbidden pattern would.

  ** [NoDup] is Leibniz equality ON CORES, and both halves are load-bearing

  [weight_bound_T] quantifies over lists whose CORES are
  duplicate-free — [List.NoDup] applied to [List.map
  FinInput.fin_core l], with [List.NoDup]'s ordinary,
  Leibniz-equality reading, nothing custom.  [List.NoDup] is written
  qualified throughout this file rather than bare [NoDup], so that the
  list predicate is never confused with another [NoDup] in scope — the
  same discipline `Checks.DispatchSurface.nodup_of_listed_once` follows.

  *** Why cores, and not records: the record reading is unprovable

  [FinInput.FinProcInput] carries seven fields the classifier is not
  obliged to look at — [fin_uid], [fin_gid], [fin_groups], [fin_net],
  [fin_nofile], [fin_sigmask], [fin_hwcap] — and two of them range
  over infinitely many values a valid input may take
  ([in_groups] is a [list word] of any length, bounded where
  [Kernel.Groups.getgroups_spec] reads it rather than in
  [Run.valid_input]; [in_net] is any [State.NetQueue]).  The other
  five are words, so their fibres are finite before any clause is
  read, and each is narrowed further by one: [Run.valid_creds] for
  [fin_uid] and [fin_gid], [Run.valid_nofile] for [fin_nofile],
  [Run.valid_sigmask] for [fin_sigmask], and [Run.valid_hwcap] for
  [fin_hwcap], which it cuts down to exactly two values.  None of
  that weakens the argument: one infinite fibre is all this needs.
  A classifier whose behavior does not depend on the launch
  environment therefore rejects either ALL of a core's launch
  environments or none of them.  That is a claim about the PROGRAM,
  not a consequence of any definition here, and it takes more than
  "issues no credential or network syscall": TWO of the seven are
  published on the initial stack, [in_uid] as AT_UID and AT_EUID and
  [in_hwcap] as AT_HWCAP ([StackLayout.auxv_entries], filled from the
  run's [State.in_uid] and [State.in_hwcap] by
  [Run.init_machine_state]), so a program can read the launching user,
  and the hart's extension mask, with no syscall at all.  The
  condition is the whole of it — no credential, network or
  signal-mask syscall AND no read of AT_UID/AT_EUID or AT_HWCAP off
  the initial stack.  [fin_gid], [fin_groups], [fin_net],
  [fin_nofile] and [fin_sigmask] reach a program only through
  syscalls; [fin_uid] and [fin_hwcap] do not.

  Read [NoDup] on the record and the obligation dies on contact with a
  nonempty reject set.  One rejected input yields the infinite family
  of [FinInput.fin_core_fibre_infinite]: pairwise distinct, hence
  [List.NoDup]; every member as VALID as the original, since
  [Run.valid_input] reads nothing the family varies (the lemma carries
  that conjunct); hence admissible lists of every length, every member
  rejected.  Any weight blind to the launch environment — which every
  weight this layer motivates is, and which [DISTRIBUTION]'s
  [w_core_blind] later makes an obligation — gives each member the
  same value, so if that value is positive the partial sums grow
  without bound and NO [b] can bound them; a task with a nonempty fire
  set and a weight positive on it could not prove [weight_bound_T] at
  any [b] whatever.  That is not a demanding
  obligation, it is an unsatisfiable one, and an unsatisfiable
  obligation is a worse failure than a vacuous one — the vacuous kind
  at least admits the submissions it should.

  Quotienting by the launch environment is the fix: the fire set this
  layer measures is a set of CORES, a core is bad when any of its
  representatives is rejected, and each core is charged once.
  [FinInput.fin_core_env_eq] pins that the core forgets the launch
  environment and nothing else, and [w_core_blind] is what makes the
  per-core charge well defined.

  *** Why Leibniz equality on cores is honest

  The core cannot hold two DIFFERENT representations of what a real
  input would consider the same value.  Three of its four fields are
  lists — of [byte] (itself `BitVec 8`) and of byte strings — and
  Leibniz equality on them is honest too, but not because they are
  "plain": two bytes of the same value are Leibniz-equal only via proof
  irrelevance on the width field, which is what
  [BitVec.eq_of_toNat_eq] supplies.  The fourth field is an [Fs.Fs] that reaches this record
  only through [Classifier.rejects] and
  [FinInput.valid_fin_input], both of which factor through
  [Run.valid_input] and so require [Fs.valid_fs] of the embedded file
  system.  It is [Fs.valid_fs] that pins the canonical,
  strictly-sorted form among its conjuncts — that is an attribute of
  [Fs.valid_fs], not an assumption made here — and without it a single
  directory could arrive under two unequal-but-equivalent [Fs.Fs]
  values, letting [NoDup] undercount duplicates that are really the
  same rejected input.

  *** What the quotient costs

  Stated plainly, because it is a WEAKENING and this file's register
  is where such things get said out loud.  [List.NoDup (List.map
  fin_core l)] implies [List.NoDup l] ([List.NoDup_map_inv]) and not
  conversely, so the hypothesis is strictly STRONGER and the
  obligation therefore asks about strictly FEWER lists: every list the
  new obligation covers was already covered by the record-indexed one,
  and lists that repeat a core are no longer asked about at all.  The
  bound is retained on exactly the lists with pairwise distinct cores
  and dropped on exactly the ones that repeat a core.  Which is the
  whole point — those dropped lists are the ones that made the
  record-indexed reading unsatisfiable — but it does mean this
  obligation does NOT imply the record-indexed one, and no reader
  should take it as doing so.  A task whose classifier genuinely
  varied its verdict with the credentials or the network would have
  its extra rejections charged at most once per core here.  That is
  the price of having an obligation at all, and the reject-set reading
  it buys — bad CORE, not bad record — is the one a task author means
  when they say "how much of the input space does this fire on".

  ** A finite partial sum, not a series

  "The measure of the fire set is at most [b] times the total [M]"
  is read here in its most literal, finitary form: for every finite
  list of rejected inputs actually exhibited, no two sharing a core,
  the weights already summed do not exceed [b * M].  There is no limit,
  no infinite series, no normalization obligation tying [M] to 1 —
  [M] is trusted metadata a [DISTRIBUTION] declares alongside its
  weight function [w], never itself proved from anything here.  [b]
  is chosen by the submission, not by this file; [weight_bound_mono]
  is what makes every [b'] at least as large as a proven [b]
  provable too, which is the fact that lets a checker trust a printed
  [b] as an upper-bound claim rather than an exact one.

  ** Equality and order on [Rat]

  [Rat]'s equality is Leibniz equality — it is a normalized structure,
  not a setoid quotient — so [sum_weights_ext] and
  [DISTRIBUTION.w_core_blind] carry [=], and [weight_bound_qeq]
  transports along [=] by rewriting.  Every order fact is [≤] on [Rat]:
  monotonicity of multiplication is [Rat.mul_le_mul_of_nonneg_right],
  transitivity is [Rat.le_trans].  [weight_bound_refutable]'s proof
  closes its refutation through the order lemmas rather than by
  computing a literal — see [one_lt_one_add_one] — and the paragraph
  above still applies: no [Rat] equality is decided there.

  [DISTRIBUTION] below is a [structure] whose fields are the parameters
  a consumer must supply, named module-qualified as [W.w] and [W.M] and
  supplied by instantiation rather than by definition here.
-/

import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.FinInput
import LinuxSem.EquivalenceDefinition.Classifier

open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.Measure

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier

/- =========================================================================
   Summing weights over a list of inputs
   ========================================================================= -/

/-- The sum of [w] over [l], zero on the empty list.  Plain
    [fold_right] over rational addition — the fold itself would
    typecheck over any element type, so the reason
    [FinInput.FinProcInput] exists rather than [State.ProcInput] is not
    this recursion but the WEIGHT FUNCTION [w] it applies: [w] must
    compute, a structural recursion over the input bytes that a
    coinductive [State.InputStream] rules out, and its representation
    must be canonical — both per [FinInput]'s header. -/
def sum_weights (w : FinProcInput → Rat) (l : List FinProcInput) : Rat :=
  List.foldr (fun f acc => w f + acc) 0 l

/-- The two computation rules, by conversion.  They are stated rather
  than left to `simp` so that a proof about a weight can [rewrite] its
    way through a list without unfolding the definition, which is what
    keeps [sum_weights_ext] below a three-line induction. -/
theorem sum_weights_nil (w : FinProcInput → Rat) : sum_weights w [] = 0 := rfl

theorem sum_weights_cons (w : FinProcInput → Rat) (f : FinProcInput)
    (l : List FinProcInput) :
    sum_weights w (f :: l) = w f + sum_weights w l := rfl

/-- [sum_weights] respects pointwise [Qeq] in the WEIGHT.  It belongs
    here rather than in a proof file because it is a fact about this
    file's own definition and mentions nothing else, and because
    [weight_bound_qeq] below — which transports [M] and [b] and says
    nothing about [w] — would otherwise be the only transport this layer
    offers, leaving the [w] direction to be re-proved by every consumer
    that needs it.  Stating it changes no definition and adds no
    obligation: this file's trust boundary is [sum_weights],
    [weight_bound_T] and [DISTRIBUTION], and none of the three moves. -/
theorem sum_weights_ext (w1 w2 : FinProcInput → Rat) (l : List FinProcInput)
    (Hext : ∀ f, w1 f = w2 f) :
    sum_weights w1 l = sum_weights w2 l := by
  induction l with
  | nil => rfl
  | cons f l ih => rw [sum_weights_cons, sum_weights_cons, ih, Hext f]

/- =========================================================================
   The weight-bound obligation
   ========================================================================= -/

/-- [C]'s rejected inputs never weigh more than [b] times the declared
    total [M], as witnessed by every finite duplicate-free sample:
    for ANY list all of whose entries [Classifier.rejects] under [C] and
    whose CORES are duplicate-free, the sum does not exceed [b * M].
    Universal over the list, not existential over one — a submission
    cannot pick a favorable sample, because the statement has to hold for
    every one, including the largest core-duplicate-free list a reader
    can exhibit.

    Duplicate-freedom is read on [FinInput.fin_core], not on the record:
    each core is charged at most once, however many launch environments
    it is offered under.  The header argues why at length; the short
    version is that reading it on the record makes the bound unprovable
    the moment anything is rejected.  Note which way this cuts — it is a
    strictly STRONGER hypothesis than [List.NoDup l]
    ([List.NoDup_map_inv]), so this is a weaker obligation than the
    record-indexed one would be, deliberately.

    That strength has one hole, and it is not this file's to close: an
    image [C] with no valid entry at all makes [Classifier.accepts]
    hold of every input vacuously
    ([Classifier.accepts_vacuous_no_entries]), which empties the
    reject set and makes [weight_bound_T C w M 0] — and so every
    larger [b], by [weight_bound_mono] — provable for ANY [w] and
    [M], said nothing about.  [Classifier]'s header names this route
    and its remedy: a consuming checker must ascribe
    [Equivalence.IMAGE_WF] to every image it names, [C] included, which
    is what keeps this statement from being satisfied by a classifier
    that was never a valid program. -/
def weight_bound_T (C : Image) (w : FinProcInput → Rat) (M b : Rat) : Prop :=
  ∀ l : List FinProcInput,
    List.Nodup (List.map fin_core l) →
    (∀ f, f ∈ l → rejects C f) →
    sum_weights w l ≤ b * M

/- =========================================================================
   The declared distribution
   ========================================================================= -/

/-- A task-supplied weight function and total, sealed as a module type
    so that they arrive by INSTANTIATION rather than by definition here.
    The instantiation is TRUSTED METADATA SUPPLIED WITH THE TASK, not
    something the submission chooses — [PatchClassifySpec]'s header says
    the same thing and is the authority on it.  The distinction is
    load-bearing rather than editorial: [DISTRIBUTION] constrains [w]
    only by [w_nonneg] and [w_core_blind], both of which
    [fun _ => 0%Q] satisfies, so a submission free to pick [w] could
    discharge [weight_bound_T] at [b = 0] for any classifier whatever
    and the two bounds in [SPEC_PATCH_CLASSIFY] would measure nothing.
    Inside a module type these names do not collide
    with anything else declared in this file or in a consumer that
    imports both; a consumer refers to them module-qualified, as [W.w]
    and [W.M] for a module [W : DISTRIBUTION].  (In Lean the module type
    is this structure: the fields are the parameters, and the same
    qualified spellings work.)

    [w_core_blind] is what makes the per-core charge in
    [weight_bound_T] WELL DEFINED: the bound counts each
    [FinInput.fin_core] once, so a weight that could tell two records
    with the same core apart would leave "the weight of a core"
    ambiguous, and which representative the list happened to name would
    change the sum.  The obligation is trivial for any real weight
    function — it recurses over argv, envp, the file system and standard
    input, which is precisely the core (see [FinInput]'s record) — but it
    is stated rather than assumed, because "the natural ones all satisfy
    it" is not something this file can check.  Note it is blindness to
    the whole LAUNCH ENVIRONMENT, credentials as well as network: a
    weight peeking at [FinInput.fin_uid] is as ill-defined here as one
    peeking at [FinInput.fin_net]. -/
structure DISTRIBUTION where
  w : FinProcInput → Rat
  M : Rat
  w_nonneg : ∀ f, 0 ≤ w f
  /- [weight_bound_mono] needs this and cannot get it from [w_nonneg]:
     [M] is declared, not summed, so nothing here forces it to agree in
     sign with the weights it is the total of.  Without it a consumer
     holding a [W : DISTRIBUTION] has nothing to discharge that
     hypothesis with, and [PatchClassifySpec]'s reading of a printed [b]
     as an upper bound rests on exactly that lemma. -/
  M_nonneg : 0 ≤ M
  w_core_blind :
    ∀ f g, fin_core f = fin_core g → w f = w g

/- =========================================================================
   Monotonicity
   ========================================================================= -/

/-- A bound proved at [b] is a bound at any larger [b'], given [M]
    nonnegative: [sum_weights w l <= b * M <= b' * M] by transitivity,
    where the second step needs [0 <= M] because multiplying an
    inequality by a possibly-negative quantity can flip it. -/
theorem weight_bound_mono (C : Image) (w : FinProcInput → Rat) (M b b' : Rat)
    (HM : 0 ≤ M) (Hbb' : b ≤ b')
    (Hbound : weight_bound_T C w M b) : weight_bound_T C w M b' := by
  intro l Hnd Hall
  exact Rat.le_trans (Hbound l Hnd Hall) (Rat.mul_le_mul_of_nonneg_right Hbb' HM)

/-- [weight_bound_T] transports along [Qeq] in [M] and [b] together: a
    submission's [1#2] and a checker's [2#4] name the same bound.  This
    is what cashes in the header's claim that the layer "stays true
    under [Qeq] as much as under [eq]" — [Qle_comp]'s [Proper] instance
    lets [rewrite] carry the fact across both equations at once, so no
    consumer has to hand-roll the transport per problem.  (Under Lean's
    [Rat] the [Qeq] is [=], and [rewrite] is exactly the tool.) -/
theorem weight_bound_qeq (C : Image) (w : FinProcInput → Rat) (M M' b b' : Rat)
    (HM : M = M') (Hb : b = b')
    (Hbound : weight_bound_T C w M b) : weight_bound_T C w M' b' := by
  intro l Hnd Hall
  have H := Hbound l Hnd Hall
  rw [HM, Hb] at H
  exact H

/-- The third transport, and the one the other two do not give: a
    pointwise [Qeq] change of the WEIGHT.  [weight_bound_mono] moves
    [b], [weight_bound_qeq] moves [M] and [b], and neither says anything
    about [w] — so without this a submission that proved its bound for
    one representative of a weight would have to re-prove it for every
    other, which is the situation the header's [Qeq]-not-[eq] warning
    describes.  The classifier, the mass and the multiplier are
    untouched here; only the weight moves, and it moves within one
    [Qeq] class. -/
theorem weight_bound_T_ext (C : Image) (w1 w2 : FinProcInput → Rat) (M b : Rat)
    (Hext : ∀ f, w1 f = w2 f)
    (Hbound : weight_bound_T C w1 M b) : weight_bound_T C w2 M b := by
  intro l Hnd Hall
  rw [← sum_weights_ext w1 w2 l Hext]
  exact Hbound l Hnd Hall

/- =========================================================================
   [weight_bound_T] bites
   ========================================================================= -/

/-- [2 <= 1] is false on the rationals, in the form the refutations
  below need: [1 < 1 + 1].  The comparison has already collapsed to a
  boolean, so nothing here decides a [Rat] equality by computation
  (see the equality note in this file's header). -/
private theorem one_lt_one_add_one : (1 : Rat) < 1 + 1 := by
  rw [Rat.lt_iff_sub_pos, Rat.add_sub_cancel]
  decide

/-- The bound [1] at unit weight and total [1] fails as soon as two
    inputs with DISTINCT CORES are both rejected: the two-element list
    [[f1; f2]] has duplicate-free cores and sums to [2], and [2 <= 1 * 1]
    is false.  This is the definition-level refutation — a
    [weight_bound_T] claim is a real restriction on the size of the
    reject set, not a statement every distribution and every classifier
    satisfies trivially.

    The hypothesis is [fin_core f1 <> fin_core f2] rather than
    [f1 <> f2], and the strengthening is exactly the content of the
    quotient: two rejected records that differ only in their launch
    environment no longer refute anything, because the obligation never
    charged for the second one.  A witness pair must now differ in argv,
    envp, the file system or standard input — which is the pair a reader
    would have had in mind anyway. -/
theorem weight_bound_refutable (C : Image) (f1 f2 : FinProcInput)
    (Hr1 : rejects C f1) (Hr2 : rejects C f2) (Hne : fin_core f1 ≠ fin_core f2) :
    ¬ weight_bound_T C (fun _ => 1) 1 1 := by
  intro Hbound
  have Hnd : (List.map fin_core [f1, f2]).Nodup := by
    simp [List.nodup_cons, Hne]
  have Hall : ∀ f, f ∈ [f1, f2] → rejects C f := by
    intro f Hin
    rcases List.mem_cons.mp Hin with Heq | Hin
    · subst f; exact Hr1
    · rcases List.mem_cons.mp Hin with Heq | Hin
      · subst f; exact Hr2
      · cases Hin
  have H := Hbound [f1, f2] Hnd Hall
  simp only [sum_weights, List.foldr_cons, List.foldr_nil] at H
  have H2 : (1 : Rat) + 1 ≤ (1 : Rat) := by
    simpa [Rat.mul_one, Rat.add_zero] using H
  exact (Rat.not_le (a := (1 : Rat) + 1) (b := 1)).mpr one_lt_one_add_one H2

/- =========================================================================
   The weight bound over the classifier pinned to forced-only
   ========================================================================= -/

/-- [weight_bound_T] with [Classifier.rejects_fo] in place of
    [Classifier.rejects]: the same lists, the same duplicate-freedom on
    cores, the same sum.  What changes is which inputs count as
    rejected — under the pin, an input the environment could only
    refuse by a refusal the state did not force is no longer one — and
    that direction is a WEAKENING of the bound wherever the filter's
    question is answered ([weight_bound_T_fo_of_weight_bound_T]), for
    the reason [Classifier.rejects_of_rejects_fo] gives. -/
def weight_bound_T_fo (C : Image) (w : FinProcInput → Rat) (M b : Rat) : Prop :=
  ∀ l : List FinProcInput,
    List.Nodup (List.map fin_core l) →
    (∀ f, f ∈ l → rejects_fo C f) →
    sum_weights w l ≤ b * M

theorem weight_bound_fo_mono (C : Image) (w : FinProcInput → Rat) (M b b' : Rat)
    (HM : 0 ≤ M) (Hbb' : b ≤ b')
    (Hbound : weight_bound_T_fo C w M b) : weight_bound_T_fo C w M b' := by
  intro l Hnd Hall
  exact Rat.le_trans (Hbound l Hnd Hall) (Rat.mul_le_mul_of_nonneg_right Hbb' HM)

theorem weight_bound_fo_qeq (C : Image) (w : FinProcInput → Rat) (M M' b b' : Rat)
    (HM : M = M') (Hb : b = b')
    (Hbound : weight_bound_T_fo C w M b) : weight_bound_T_fo C w M' b' := by
  intro l Hnd Hall
  have H := Hbound l Hnd Hall
  rw [HM, Hb] at H
  exact H

theorem weight_bound_T_fo_of_weight_bound_T (C : Image) (w : FinProcInput → Rat)
    (M b : Rat) (Hdec : classifier_decided C)
    (Hbound : weight_bound_T C w M b) : weight_bound_T_fo C w M b := by
  intro l Hnd Hall
  exact Hbound l Hnd (fun f Hin => rejects_of_rejects_fo C f Hdec (Hall f Hin))

/-- ... and it bites exactly as [weight_bound_refutable] does. -/
theorem weight_bound_fo_refutable (C : Image) (f1 f2 : FinProcInput)
    (Hr1 : rejects_fo C f1) (Hr2 : rejects_fo C f2)
    (Hne : fin_core f1 ≠ fin_core f2) :
    ¬ weight_bound_T_fo C (fun _ => 1) 1 1 := by
  intro Hbound
  have Hnd : (List.map fin_core [f1, f2]).Nodup := by
    simp [List.nodup_cons, Hne]
  have Hall : ∀ f, f ∈ [f1, f2] → rejects_fo C f := by
    intro f Hin
    rcases List.mem_cons.mp Hin with Heq | Hin
    · subst f; exact Hr1
    · rcases List.mem_cons.mp Hin with Heq | Hin
      · subst f; exact Hr2
      · cases Hin
  have H := Hbound [f1, f2] Hnd Hall
  simp only [sum_weights, List.foldr_cons, List.foldr_nil] at H
  have H2 : (1 : Rat) + 1 ≤ (1 : Rat) := by
    simpa [Rat.mul_one, Rat.add_zero] using H
  exact (Rat.not_le (a := (1 : Rat) + 1) (b := 1)).mpr one_lt_one_add_one H2

end LinuxSem.EquivalenceDefinition.Measure
