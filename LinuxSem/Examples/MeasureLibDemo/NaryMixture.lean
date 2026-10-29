/-
  * Examples.MeasureLibDemo.NaryMixture — the n-ary mixture, worked

  DEMO FILE (not part of the trusted specification, and not installed).  [MeasureLib]'s worked demonstration
  assembles a distribution out of [MeasureLib.finite_support],
  [MeasureLib.cd_scale] and [MeasureLib.cd_mix2].  It never reaches the
  `n`-ARY mixture, and this file is that instantiation: the three
  combinators [MeasureLib.cd_mix], [MeasureLib.cd_zero] and
  [MeasureLib.cd_sum_over], carried through to a
  [Measure.weight_bound_T] a task could ship.

  ** The shape, and why an `n`-ary mixture is the natural one for it

  A task whose inputs fall into named CLASSES declares one component per
  class and mixes them.  Two classes are [MeasureLib.cd_mix2]; three or
  more are a list, and writing a list of three as two nested
  `cd_mix2`s means writing the associativity by hand at every bound.
  The three classes here are read off the first byte of standard input —
  plain text, NUL-led, carriage-return-led — with a quarter of the
  space's mass carried by the class that has no leading control byte.

  ** What the `n`-ary bound asks for, and what it gives back

  [MeasureLib.cd_mix_bound] takes a bound FUNCTION `B :
  CoreDistribution → Rat` rather than a list of numbers, so the
  per-component ceilings have to be expressible as a function of the
  component.  That is not a restriction in practice and this file is the
  demonstration of why: the natural statement of a fire set that takes a
  fixed FRACTION of each class is exactly such a function,
  `fun D => (1 / 4) * D.cd_mass`, and the resulting total is a quarter
  of the mixture's own declared mass by [MeasureLib.cd_mix_mass]
  ([nary_ceiling_is_a_quarter_of_the_mass]).  A task whose per-class
  ceilings are unrelated numbers would instead reach for
  [MeasureLib.cd_mix2] twice; the two are the same object
  ([MeasureLib.cd_mix_nary_agrees]), so nothing is lost either way.

  ** Non-vacuity

  [nary_ceiling_is_attained_and_bites] closes both directions.  The fire
  set's own three records weigh EXACTLY the ceiling, so the bound is
  tight rather than slack — unlike the geometric routes, where the mass
  is a supremum and never attained.  And three records OUTSIDE the fire
  set weigh strictly more than the ceiling, so the fire-set hypothesis
  in [nary_weight_bound_T_of] is load-bearing: drop it and the
  conclusion is false at this multiplier.

  As everywhere in [MeasureLib], the records exhibited here are not
  claimed VALID ([FinInput.valid_fin_input]) and not claimed rejected by
  any classifier.  Exhibiting them is arithmetic.
-/
import LinuxSem.EquivalenceDefinition.MeasureLib

set_option autoImplicit false

open LinuxSem.Riscv

namespace LinuxSem.Examples.MeasureLibDemo

open LinuxSem.LinuxProcessSem
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Measure
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MeasureLib
open LinuxSem.LinuxProcessSem.MemImageType

namespace NaryMixture

/- =========================================================================
   The fixed launch-time environment, and the bytes the classes turn on
   ========================================================================= -/

/-- The three components hold argv, envp and the file system fixed and
    vary only standard input, exactly as [MeasureLib]'s worked
    demonstration does — a program invoked as `"wc"`, no environment, an
    empty file system.  Nothing below reads any of the three; writing
    something into argv makes it visible that they are a choice. -/
def nary_argv : List (List (BitVec 8)) :=
  [[BitVec.ofInt 8 119, BitVec.ofInt 8 99]]

def nary_envp : List (List (BitVec 8)) := []

def nary_fs : Fs.Fs := []

def nary_core (s : List (BitVec 8)) : FinCore :=
  FinCore.mkFinCore nary_argv nary_envp nary_fs s

def nary_nul : BitVec 8 := BitVec.ofInt 8 0

def nary_cr : BitVec 8 := BitVec.ofInt 8 13

def nary_a : BitVec 8 := BitVec.ofInt 8 65

def nary_b : BitVec 8 := BitVec.ofInt 8 66

def nary_c : BitVec 8 := BitVec.ofInt 8 67

/- The core embedding is injective in the standard input, which is what
   turns a comparison of cores into a comparison of byte lists.  It is
   a rewrite rule and not merely a fact because the entry-list arithmetic
   below resolves "is this entry the one that names `c`" with it. -/
@[simp] theorem nary_core_inj {s t : List (BitVec 8)} :
    nary_core s = nary_core t ↔ s = t := by
  constructor
  · intro h
    exact congrArg FinCore.core_stdin h
  · intro h
    rw [h]

/- The five class bytes, pairwise distinct.  Stated because the weights
   below are `if c₀ = c then q else 0` at closed byte lists, and the
   decision has to be available to `simp`: `Rat` arithmetic is not
   kernel-reducible and neither is `BitVec` equality. -/
@[simp] theorem nary_nul_ne_cr : nary_nul ≠ nary_cr := by decide

@[simp] theorem nary_nul_ne_a : nary_nul ≠ nary_a := by decide

@[simp] theorem nary_nul_ne_b : nary_nul ≠ nary_b := by decide

@[simp] theorem nary_nul_ne_c : nary_nul ≠ nary_c := by decide

@[simp] theorem nary_cr_ne_a : nary_cr ≠ nary_a := by decide

@[simp] theorem nary_cr_ne_b : nary_cr ≠ nary_b := by decide

@[simp] theorem nary_cr_ne_c : nary_cr ≠ nary_c := by decide

@[simp] theorem nary_a_ne_b : nary_a ≠ nary_b := by decide

@[simp] theorem nary_a_ne_c : nary_a ≠ nary_c := by decide

@[simp] theorem nary_b_ne_c : nary_b ≠ nary_c := by decide

/- The same five facts in the other orientation.  `core_indicator c₀ q c`
   tests `c₀ = c`, so which side the entry is on depends on the entry
   order, and `simp` resolves the `if` from the hypothesis whose two sides
   are the ones the test compares. -/
@[simp] theorem nary_cr_ne_nul : nary_cr ≠ nary_nul := by decide

@[simp] theorem nary_a_ne_nul : nary_a ≠ nary_nul := by decide

@[simp] theorem nary_b_ne_nul : nary_b ≠ nary_nul := by decide

@[simp] theorem nary_c_ne_nul : nary_c ≠ nary_nul := by decide

@[simp] theorem nary_a_ne_cr : nary_a ≠ nary_cr := by decide

@[simp] theorem nary_b_ne_cr : nary_b ≠ nary_cr := by decide

@[simp] theorem nary_c_ne_cr : nary_c ≠ nary_cr := by decide

@[simp] theorem nary_b_ne_a : nary_b ≠ nary_a := by decide

@[simp] theorem nary_c_ne_a : nary_c ≠ nary_a := by decide

@[simp] theorem nary_c_ne_b : nary_c ≠ nary_b := by decide

/- =========================================================================
   One [finite_support] per class
   ========================================================================= -/

/-- The plain-text class, at half the total: four named inputs, an eighth
    each.  [MeasureLib.entries_nonneg_of_forallb] is what discharges the
    combinator's one side condition, and it is the whole of what a task
    author writes per class. -/
def nary_entries_text : List (FinCore × Rat) :=
  [(nary_core [], (1 : Rat) / 8),
   (nary_core [nary_a], (1 : Rat) / 8),
   (nary_core [nary_b], (1 : Rat) / 8),
   (nary_core [nary_c], (1 : Rat) / 8)]

theorem nary_entries_text_nonneg : ∀ e, e ∈ nary_entries_text → 0 ≤ e.2 := by
  apply entries_nonneg_of_forallb
  rw [List.all_eq_true]
  intro e He
  rw [decide_eq_true_eq]
  simp only [nary_entries_text, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl | rfl <;> grind

/-- The NUL-led class, at a quarter: four inputs, a sixteenth each. -/
def nary_entries_nul : List (FinCore × Rat) :=
  [(nary_core [nary_nul], (1 : Rat) / 16),
   (nary_core [nary_nul, nary_a], (1 : Rat) / 16),
   (nary_core [nary_nul, nary_b], (1 : Rat) / 16),
   (nary_core [nary_nul, nary_c], (1 : Rat) / 16)]

theorem nary_entries_nul_nonneg : ∀ e, e ∈ nary_entries_nul → 0 ≤ e.2 := by
  apply entries_nonneg_of_forallb
  rw [List.all_eq_true]
  intro e He
  rw [decide_eq_true_eq]
  simp only [nary_entries_nul, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl | rfl <;> grind

/-- The carriage-return-led class, at the remaining quarter. -/
def nary_entries_cr : List (FinCore × Rat) :=
  [(nary_core [nary_cr], (1 : Rat) / 16),
   (nary_core [nary_cr, nary_a], (1 : Rat) / 16),
   (nary_core [nary_cr, nary_b], (1 : Rat) / 16),
   (nary_core [nary_cr, nary_c], (1 : Rat) / 16)]

theorem nary_entries_cr_nonneg : ∀ e, e ∈ nary_entries_cr → 0 ≤ e.2 := by
  apply entries_nonneg_of_forallb
  rw [List.all_eq_true]
  intro e He
  rw [decide_eq_true_eq]
  simp only [nary_entries_cr, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl | rfl <;> grind

def nary_text : CoreDistribution :=
  finite_support nary_entries_text nary_entries_text_nonneg

def nary_nul_led : CoreDistribution :=
  finite_support nary_entries_nul nary_entries_nul_nonneg

def nary_cr_led : CoreDistribution :=
  finite_support nary_entries_cr nary_entries_cr_nonneg

/-- THE DISTRIBUTION: the three classes as a list, mixed.  The list is
    named rather than written inline at every use, because
    [MeasureLib.cd_mix_bound]'s hypothesis quantifies over
    `D ∈ nary_components` and a reader has to be able to see that the
    three cases below are all of them. -/
def nary_components : List CoreDistribution :=
  [nary_text, nary_nul_led, nary_cr_led]

def nary_mix : CoreDistribution := cd_mix nary_components

/- The three declared masses, computed.  Each is `entries_mass` of a
   four-element literal, so it is arithmetic on eight numerals once the
   fold is unfolded. -/
theorem nary_text_mass : nary_text.cd_mass = (1 : Rat) / 2 := by
  show entries_mass nary_entries_text = (1 : Rat) / 2
  simp [entries_mass, nary_entries_text]
  grind

theorem nary_nul_led_mass : nary_nul_led.cd_mass = (1 : Rat) / 4 := by
  show entries_mass nary_entries_nul = (1 : Rat) / 4
  simp [entries_mass, nary_entries_nul]
  grind

theorem nary_cr_led_mass : nary_cr_led.cd_mass = (1 : Rat) / 4 := by
  show entries_mass nary_entries_cr = (1 : Rat) / 4
  simp [entries_mass, nary_entries_cr]
  grind

/-- The declared mass is `1`, and it is the components' own totals added
    up rather than a number written here: [MeasureLib.cd_mix_mass]
    identifies the mixture's declared mass with
    `MeasureLib.cd_sum_over cd_mass` over the same list, and the four
    numerals then close it. -/
theorem nary_mass_is_one : nary_mix.cd_mass = 1 := by
  rw [nary_mix, cd_mix_mass]
  unfold nary_components
  rw [cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_nil]
  rw [nary_text_mass, nary_nul_led_mass, nary_cr_led_mass]
  grind

/-- The unit and the one-element case, pinned.  Without the first, the
    fold could be anything on the empty list and
    [MeasureLib.cd_mix_mass] would still hold; without the second, the
    fixpoint could disagree with its own summand.  This is
    [MeasureLib.cd_mix_nary_agrees] at this file's own components,
    reaching [MeasureLib.cd_zero] — the only place the empty mixture is
    instantiated. -/
theorem nary_empty_mixture_is_cd_zero :
    (cd_mix []).cd_mass = cd_zero.cd_mass ∧
      (cd_mix []).cd_weight (nary_core [nary_c]) =
        cd_zero.cd_weight (nary_core [nary_c]) ∧
      (cd_mix [nary_text]).cd_mass = nary_text.cd_mass := by
  refine ⟨rfl, rfl, ?_⟩
  rw [cd_mix_cons, cd_mix_nil, cd_mix2_mass, cd_zero_mass]
  grind

/- =========================================================================
   The fire set: a quarter of every class
   ========================================================================= -/

/-- THE FIRE SET, as a predicate on cores: the one input per class whose
    last byte is [nary_c].  It is written as three decisions for the
    reason [MeasureLib.worked_is_fire] is — [MeasureLib.entries_restrict]
    has to COMPUTE, and a support this small is named rather than
    described.  A larger one would use a predicate that describes the
    set; [MeasureLib.finite_support_bound_subset] takes any `Bool`-valued
    predicate whatever. -/
def nary_is_fire (c : FinCore) : Bool :=
  if decide (c = nary_core [nary_c]) then true
  else if decide (c = nary_core [nary_nul, nary_c]) then true
  else if decide (c = nary_core [nary_cr, nary_c]) then true
  else false

/-- THE PER-COMPONENT CEILING, as a function of the component, which is
    the form [MeasureLib.cd_mix_bound] takes.  A quarter of each class's
    declared mass: an eighth of the text class's half, a sixteenth of
    each control-led class's quarter. -/
def nary_share (D : CoreDistribution) : Rat := (1 : Rat) / 4 * D.cd_mass

/-- ... and it really is a quarter of the whole, not merely three numbers
    that happen to add up.  [MeasureLib.cd_mix_mass] is what makes this
    an identity about the mixture rather than an arithmetic coincidence
    about this list. -/
theorem nary_ceiling_is_a_quarter_of_the_mass :
    cd_sum_over nary_share nary_components =
      (1 : Rat) / 4 * nary_mix.cd_mass := by
  have hR : cd_sum_over (fun D => D.cd_mass) nary_components =
      nary_text.cd_mass + (nary_nul_led.cd_mass +
        (nary_cr_led.cd_mass + 0)) := by
    unfold nary_components
    rw [cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_nil]
  rw [nary_mix, cd_mix_mass, hR]
  unfold nary_components nary_share
  rw [cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_cons, cd_sum_over_nil]
  grind

/- The restricted masses: the fire set names exactly one entry per class,
   so each class is charged what that one entry declares.  Computed, not
   asserted — [entries_restrict] is a filter and the filter is resolved
   against the entry list. -/
theorem nary_restrict_text :
    entries_mass (entries_restrict nary_is_fire nary_entries_text) =
      (1 : Rat) / 8 := by
  unfold entries_restrict
  simp [nary_is_fire, nary_entries_text, entries_mass]
  grind

theorem nary_restrict_nul :
    entries_mass (entries_restrict nary_is_fire nary_entries_nul) =
      (1 : Rat) / 16 := by
  unfold entries_restrict
  simp [nary_is_fire, nary_entries_nul, entries_mass]
  grind

theorem nary_restrict_cr :
    entries_mass (entries_restrict nary_is_fire nary_entries_cr) =
      (1 : Rat) / 16 := by
  unfold entries_restrict
  simp [nary_is_fire, nary_entries_cr, entries_mass]
  grind

/-- Each component charges the fire set a quarter of its own mass.  The
    three cases are the three components, and each is one
    [MeasureLib.finite_support_bound_subset] — the refinement that
    charges a fire set against the entries it actually names rather than
    against the class's whole declared mass — plus one closed equality
    between rationals. -/
theorem nary_component_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l → nary_is_fire (fin_core f) = true)
    (D : CoreDistribution) (HD : D ∈ nary_components) :
    core_sum D.cd_weight l ≤ nary_share D := by
  unfold nary_components at HD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at HD
  rcases HD with rfl | rfl | rfl
  · refine Rat.le_trans (finite_support_bound_subset nary_is_fire
      nary_entries_text nary_entries_text_nonneg l Hnd Hfire) ?_
    rw [nary_restrict_text]
    unfold nary_share
    rw [nary_text_mass]
    grind
  · refine Rat.le_trans (finite_support_bound_subset nary_is_fire
      nary_entries_nul nary_entries_nul_nonneg l Hnd Hfire) ?_
    rw [nary_restrict_nul]
    unfold nary_share
    rw [nary_nul_led_mass]
    grind
  · refine Rat.le_trans (finite_support_bound_subset nary_is_fire
      nary_entries_cr nary_entries_cr_nonneg l Hnd Hfire) ?_
    rw [nary_restrict_cr]
    unfold nary_share
    rw [nary_cr_led_mass]
    grind

/-- THE BOUND: every admissible list drawn from the fire set weighs at
    most a quarter of the mixture's mass.  One [MeasureLib.cd_mix_bound]
    over the whole list of components, and the arithmetic that turns the
    `MeasureLib.cd_sum_over` it produces into the literal a task would
    print. -/
theorem nary_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l → nary_is_fire (fin_core f) = true) :
    core_sum nary_mix.cd_weight l ≤ (1 : Rat) / 4 := by
  refine Rat.le_trans (cd_mix_bound nary_share nary_components l ?_) ?_
  · intro D HD
    exact nary_component_bound l Hnd Hfire D HD
  · rw [nary_ceiling_is_a_quarter_of_the_mass, nary_mass_is_one]
    grind

/-- The whole-space certificate for the same mixture, which is the other
    bound [MeasureLib.cd_mix_bound_mass] exists for: no admissible list
    at all weighs more than the declared mass, fire set or not.  A task
    that cannot describe its fire set still gets this one. -/
theorem nary_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum nary_mix.cd_weight l ≤ nary_mix.cd_mass := by
  refine cd_mix_bound_mass nary_components l ?_
  intro D HD
  unfold nary_components at HD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at HD
  rcases HD with rfl | rfl | rfl
  · exact finite_support_bound nary_entries_text nary_entries_text_nonneg l Hnd
  · exact finite_support_bound nary_entries_nul nary_entries_nul_nonneg l Hnd
  · exact finite_support_bound nary_entries_cr nary_entries_cr_nonneg l Hnd

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

/-- Both weight obligations come from the library, as they do for every
    distribution built here: the lift of a [MeasureLib.CoreDistribution]
    is nonnegative by the record's own field and core-blind by
    congruence.  `M_nonneg` is the mixture's declared mass, which
    [nary_mass_is_one] has already identified with `1`. -/
def Nary_D : DISTRIBUTION where
  w := cd_lift nary_mix
  M := nary_mix.cd_mass
  w_nonneg := cd_lift_nonneg nary_mix
  M_nonneg := by
    show 0 ≤ nary_mix.cd_mass
    rw [nary_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind nary_mix

/-- From the library's bound to the obligation itself, at any multiplier
    the ceiling fits under.  The three crossings are the ones
    [MeasureLib.worked_weight_bound_T_of] makes and no others:
    [MeasureLib.core_sum_cd_lift] carries `Measure.sum_weights` of the
    lifted weight to [MeasureLib.core_sum], the classifier hypothesis is
    spent turning "rejected" into "has a fire core", and
    [nary_mass_is_one] turns `b * M` into `b`. -/
theorem nary_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f → nary_is_fire (fin_core f) = true)
    (Hb : (1 : Rat) / 4 ≤ b) :
    weight_bound_T C Nary_D.w Nary_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift nary_mix) l ≤ b * nary_mix.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (nary_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [nary_mass_is_one, Rat.mul_one]
  exact Hb

/-- The demonstration at the tightest multiplier this route reaches.  The
    arithmetic step is [Rat.le_refl], and — unlike the geometric routes —
    there is nothing left to give away in the distribution either, which
    is what the next lemma's first two conjuncts say. -/
theorem nary_weight_bound_T_quarter (C : Image)
    (Hfire : ∀ f, rejects C f → nary_is_fire (fin_core f) = true) :
    weight_bound_T C Nary_D.w Nary_D.M ((1 : Rat) / 4) :=
  nary_weight_bound_T_of C _ Hfire Rat.le_refl

/- =========================================================================
   Non-vacuity: the ceiling is attained, and the fire hypothesis bites
   ========================================================================= -/

/-- The fire set as an admissible list: one canonical record per fire
    core, through [MeasureLib.core_input]. -/
def nary_fire_list : List FinProcInput :=
  List.map core_input
    [nary_core [nary_c], nary_core [nary_nul, nary_c],
     nary_core [nary_cr, nary_c]]

/-- Three records the fire set does NOT name, one of them from the class
    that carries the most mass. -/
def nary_off_fire_list : List FinProcInput :=
  List.map core_input
    [nary_core [nary_a], nary_core [nary_b], nary_core [nary_nul, nary_a]]

theorem nary_text_weight (c : FinCore) :
    nary_text.cd_weight c = entries_weight nary_entries_text c := rfl

theorem nary_nul_led_weight (c : FinCore) :
    nary_nul_led.cd_weight c = entries_weight nary_entries_nul c := rfl

theorem nary_cr_led_weight (c : FinCore) :
    nary_cr_led.cd_weight c = entries_weight nary_entries_cr c := rfl

/-- The mixture's weight is the sum of the three components' weights. -/
theorem nary_mix_weight (c : FinCore) :
    nary_mix.cd_weight c =
      nary_text.cd_weight c + (nary_nul_led.cd_weight c +
        (nary_cr_led.cd_weight c + 0)) := by
  rw [nary_mix, nary_components, cd_mix_cons, cd_mix_cons, cd_mix_cons,
    cd_mix_nil]
  show nary_text.cd_weight c + (nary_nul_led.cd_weight c +
      (nary_cr_led.cd_weight c + cd_zero.cd_weight c)) =
    nary_text.cd_weight c + (nary_nul_led.cd_weight c +
      (nary_cr_led.cd_weight c + 0))
  rw [cd_zero_weight]

theorem nary_fire_list_sum :
    core_sum nary_mix.cd_weight nary_fire_list = (1 : Rat) / 4 := by
  show nary_mix.cd_weight (fin_core (core_input (nary_core [nary_c]))) +
      (nary_mix.cd_weight (fin_core (core_input (nary_core [nary_nul, nary_c]))) +
        (nary_mix.cd_weight (fin_core (core_input (nary_core [nary_cr, nary_c]))) +
          0)) = _
  rw [nary_mix_weight, nary_mix_weight, nary_mix_weight]
  simp only [fin_core_core_input, nary_text_weight, nary_nul_led_weight,
    nary_cr_led_weight]
  simp [entries_weight, core_indicator, nary_entries_text, nary_entries_nul,
    nary_entries_cr]
  grind

theorem nary_off_fire_list_sum :
    core_sum nary_mix.cd_weight nary_off_fire_list = (5 : Rat) / 16 := by
  show nary_mix.cd_weight (fin_core (core_input (nary_core [nary_a]))) +
      (nary_mix.cd_weight (fin_core (core_input (nary_core [nary_b]))) +
        (nary_mix.cd_weight (fin_core (core_input (nary_core [nary_nul, nary_a]))) +
          0)) = _
  rw [nary_mix_weight, nary_mix_weight, nary_mix_weight]
  simp only [fin_core_core_input, nary_text_weight, nary_nul_led_weight,
    nary_cr_led_weight]
  simp [entries_weight, core_indicator, nary_entries_text, nary_entries_nul,
    nary_entries_cr]
  grind

/-- BOTH DIRECTIONS.  The first two conjuncts say the ceiling is REAL: the
    fire set's own records form an admissible list and weigh exactly
    `1 / 4`, so [nary_weight_bound_T_quarter] is the best this
    distribution admits and not a number with slack hidden in it.  The
    last three say the fire-set hypothesis is LOAD-BEARING: three records
    outside the fire set — computed to be outside, through [nary_is_fire]
    itself rather than argued in prose — are admissible and weigh
    `5 / 16`, which is more.  Drop the hypothesis and the conclusion is
    false at this multiplier. -/
theorem nary_ceiling_is_attained_and_bites :
    (List.map fin_core nary_fire_list).Nodup ∧
      core_sum nary_mix.cd_weight nary_fire_list = (1 : Rat) / 4 ∧
      (List.map fin_core nary_off_fire_list).Nodup ∧
      (∀ f, f ∈ nary_off_fire_list → nary_is_fire (fin_core f) = false) ∧
      ¬ (core_sum nary_mix.cd_weight nary_off_fire_list ≤ (1 : Rat) / 4) := by
  refine ⟨?_, nary_fire_list_sum, ?_, ?_, ?_⟩
  · unfold nary_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> simp at h
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        simp at h
      · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · unfold nary_off_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> simp at h
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        simp at h
      · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro f Hf
    unfold nary_off_fire_list at Hf
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at Hf
    rcases Hf with rfl | rfl | rfl <;>
      simp [fin_core_core_input, nary_is_fire]
  · rw [nary_off_fire_list_sum]
    grind

/-- The [MeasureLib.finite_support] certificate pair's LOWER half, at a
    concrete class: some admissible list weighs the class's declared mass
    exactly.  [MeasureLib.finite_support_mass_exact] proves it for every
    entry list; instantiating it here is what makes the whole-space bound
    above a two-sided statement about this distribution rather than a
    one-sided one. -/
theorem nary_text_mass_exact :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum nary_text.cd_weight l = nary_text.cd_mass :=
  finite_support_mass_exact nary_entries_text nary_entries_text_nonneg

end NaryMixture

end LinuxSem.Examples.MeasureLibDemo
