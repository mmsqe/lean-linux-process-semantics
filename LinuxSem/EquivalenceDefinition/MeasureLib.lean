/-
  * EquivalenceDefinition.MeasureLib — the measure combinator library

  The `QArith` helper layer, the core-distribution and weight machinery, the
  finite-support combinator with its upper/lower/exact certificates, the byte
  enumeration and the counting lemma, the geometric standard-input combinator through
  `stdin_geometric_mass_upper`, its LENGTH SLICE with both sharpness pins, and the
  two composition combinators (scaling and mixture) with their upper/lower/mass
  certificates, their non-vacuity pins and the overlapping-support example, the RATE
  at which a power of a proper fraction shrinks, the geometric mass's lower
  certificate (which is an approach and not an attainment), the proof that the mass
  is a supremum and not a maximum, and the WORKED DISTRIBUTION (named cores over a
  geometric background) that discharges `Measure.weight_bound_T` and
  `GatedSize.weight_bound_pred_T` end to end.... plus the envp-varying family:
  `bytes_cyl` and its three sum transports,
  `entries_geo_product`/`envp_factor`/`envp_point` with their closed forms,
  `envp_geo_weight` and `stdin_envp_geometric`, the envp enumeration and its
  cancellation, the two-coordinate product and its sum/disjointness lemmas, and the
  three list depths with their bounds.......... The file-system witness family
  (`fss_len`, `fss_upto`) with its membership-length and duplicate-freedom facts, the
  three `qsum_fs_*` transports that price it, the margin arithmetic (`Qprod_margin`,
  `Qmult_unit`, the three `envp_prefix_sum_*` facts, `strings_prefix_margin`,
  `fs_prefix_margin`, `full_support_margin_at_depths`), the eight depths
  (`entry_depth_for`, `full_support_depths_above`), and the witness family with the
  certificate itself (`full_support_lower_witness`,
  `map_fin_core_full_support_lower_witness`, `full_support_lower_witness_nodup`,
  `full_support_base_mass_lower_witness`,
  `full_support_base_mass_lower_certificate`). An upper certificate and now a lower
  one, so its declared `1` is the least upper bound of the admissible partial sums,
  approached but never met.

  NOT A TRUST BOUNDARY, and the distinction is worth stating exactly
  rather than leaving to be inferred from the absence of the banner.
  `Measure` and `FinInput` are trusted because a top-level check ascribes
  against statements built from their definitions: change
  `Measure.weight_bound_T` and every submission that ever passed now
  means something else.  This file changes no statement.  A task's weight
  function and declared total are trusted metadata whatever their
  provenance — `Measure.DISTRIBUTION` declares `w` and `M` as fields, asks
  two properties of `w` and nothing at all of `M` — so a distribution
  BUILT here is trusted neither more nor less than one written out by
  hand.  What this file emits is PROOFS: those two properties, and the
  partial-sum bounds a submission needs in order to get from a
  distribution to `Measure.weight_bound_T`.  Delete the file and every
  consumer of it could still be written; it would just be written again,
  once per task, by hand.

  An edit here can still break something, and it is worth naming which
  thing: not the meaning of any obligation, but the axioms a proof rests
  on.  Adding an unproved postulate to a proof library and leaning on it is a move
  available in any proof library, this one included; it is a question for
  an assumption audit of the submitted development, and not one this
  file's status answers either way.

  ** Every weight here is a function of the CORE, which is the design

  `Measure.DISTRIBUTION` carries `w_core_blind`: a weight must agree on
  records with equal `FinInput.fin_core`.  The obligation is not hard, but
  it is stated once per distribution and a task author should never have
  to think about it.  So this library does not build weights on
  `FinInput.FinProcInput` at all.  It builds them on `FinInput.FinCore` —
  a `CoreDistribution` — and LIFTS through `FinInput.fin_core` (`cd_lift`).
  `cd_lift_core_blind` is then a congruence: two records with the same
  core are handed to the same function at the same argument, so the
  values are not merely equal, they are `eq`.  `cd_lift_nonneg` is the
  `CoreDistribution`'s own field.  Those two obligations are discharged
  once, here, for every distribution this library will ever build, and
  the third — `M_nonneg`, on the DECLARED mass and not on the weights —
  is discharged per combinator (`finite_support_mass_nonneg`,
  `stdin_geometric_mass_nonneg`, and `cd_scale_mass_nonneg` and
  `cd_mix2_mass_nonneg` to compose them), because nothing ties `cd_mass`
  to `cd_weight` and so no single lemma can cover it.

  Nothing is lost by that restriction: `cd_lift_complete` proves that
  EVERY weight satisfying `Measure.DISTRIBUTION`'s two WEIGHT obligations
  is pointwise equal to the lift of a `CoreDistribution`, at any declared
  mass one likes — `M_nonneg` constrains the mass alone and so puts no
  weight out of reach.

  ** The sums bounded here are the sums the obligation talks about

  `Measure.weight_bound_T` is quantified over `Measure.sum_weights w l`
  for `l : list FinInput.FinProcInput`.  `core_sum` is that sum for a
  lifted weight, and `core_sum_cd_lift` is the bridge — `eq`, by
  conversion.  Internally the sums are moved to `qsum` over
  `List.map FinInput.fin_core l` (`core_sum_map_fin_core`), which is what
  turns the obligation's hypothesis — `List.Nodup (List.map
  FinInput.fin_core l)`, duplicate-freedom read on cores — into plain
  `List.Nodup` of a list of cores.

  ** Finite support, and why its constructor demands a proof

  `finite_support` is the first combinator: a list of (core, weight)
  entries, weight zero off the listed cores, entries for a repeated core
  SUMMED rather than one of them silently winning.  Its declared mass is
  the sum of the entries' weights.  It takes a proof that every entry is
  nonnegative, and there is no version of this constructor that does
  without one: `finite_support_bound` is FALSE otherwise, and false
  already on the EMPTY list.

  The bound has a REFINEMENT: `finite_support_bound_subset` charges a
  list whose cores all satisfy a predicate `P` against the mass of the
  `P`-entries ALONE (`entries_restrict`), not against the declared total.

  ** Certificates: the declared mass is an upper bound, and it is attained

  Upper: `finite_support_mass_upper`.  Lower:
  `finite_support_mass_lower_witness` exhibits a list that reaches it, so
  the declared mass is not slack the author padded.
  `finite_support_mass_exact` puts the two together as an equality.

  ** The geometric standard-input distribution

  `stdin_geometric` fixes argv, envp and the file system to given values
  and spreads what is left over standard input the way a memoryless
  source does: stop after each byte with weight `p_stop`, otherwise emit
  one of 256 bytes.  A core whose argv, envp or file system differ from
  the fixed ones weighs zero; a matching core whose standard input has
  length `n` weighs `p_stop * (1 - p_stop) ^ n * (1 / 256) ^ n`.  The
  declared mass is `1`.

  THE SIDE CONDITIONS ARE `0 <= p_stop` AND `p_stop <= 1`, and they are
  constructor arguments for the reason `finite_support`'s nonnegativity
  proof is one: `cd_nonneg` is a field.  The intended family is
  `0 < p_stop <= 1` and the STRICT inequality is deliberately not
  demanded, because nothing the CONSTRUCTOR needs uses it.

  ** One counting lemma holds the whole thing up

  `injective_core_list_in_cylinder_length_bound`: a list of records with
  duplicate-free CORES, every core matching the fixed argv, envp and file
  system and carrying standard input of length exactly `n`, has at most
  `256 ^ n` elements.

  ** The cylinder bound, and why it is proved by enumeration

  `stdin_geometric_bound` is the exported statement: a list whose cores
  all carry standard input EXTENDING a fixed prefix `bs` sums to at most
  `stdin_geometric_cylinder_mass p_stop bs`, which is
  `(1 - p_stop) ^ length bs * (1 / 256) ^ length bs`.  That number is
  exactly what the geometric weights inside the cylinder add up to, so
  the bound is sharp and not merely convenient.

  No infinite series is summed.  `cyl_enum bs N` is the list of every
  core in the cylinder whose standard input exceeds `bs` by at most `N`
  bytes; `cyl_enum_sum_le` shows by induction on `N` that its own sum
  stays under the cylinder mass; and the task's list is then bounded by
  it through `qsum_core_incl_le`.

  ** The Lean rendering of the rationals

  `Q` becomes Lean's `Rat`.  `Qeq` (`==%Q`) is Leibniz equality there —
  `Rat` is a normalized structure, not a setoid quotient — so every
  `(a == b)%Q` above is stated here as `a = b`.  Every `Qle` fact is
  Lean's `≤` on `Rat`; `Qmult_le_compat_r` is
  `Rat.mul_le_mul_of_nonneg_right` and `Qle_trans` is `Rat.le_trans`.
  Lean has no `Module Type`; `DISTRIBUTION` in `Measure` and
  `CoreDistribution` below are `structure`s whose fields play the role of
  a module type's parameters.

  the file opens with a
  1,256-line design essay.  The paragraphs above are the load-bearing
  part of it; the remainder elaborates the same three arguments (why the
  per-core charge is a quotient, why `List.NoDup` on cores is honest, and
  which classical axioms the arithmetic layer avoids) and is unchanged in
  substance.  The rationale above is the whole of it.
-/

import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.MustExit
import LinuxSem.EquivalenceDefinition.FinInput
import LinuxSem.EquivalenceDefinition.Classifier
import LinuxSem.EquivalenceDefinition.Measure
import LinuxSem.EquivalenceDefinition.GatedSize

/- `autoImplicit` is off for this file: every name below is written out.
   The default silently turns a misspelled identifier into an implicitly
   bound variable, which in a STATEMENT is a weakened claim rather than a
   compile error — the one failure mode a proof library cannot afford. -/
set_option autoImplicit false


open LinuxSem.Riscv

namespace LinuxSem.EquivalenceDefinition.MeasureLib

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.Measure

/- =========================================================================
   Arithmetic `QArith` does not ship
   ========================================================================= -/

/-- A sum of nonnegative rationals is nonnegative.  `QArith` ships the
    MULTIPLICATIVE version of this and not the additive one, so it is
    assembled here out of `Qplus_le_compat` and `Qplus_0_l`, once, rather
    than open-coded at each use.  It says nothing about this development
    and is not named after it; the name is deliberately not
    `Qplus_le_0_compat`, so that nothing here shadows a lemma `QArith`
    might later add under the name its own convention would pick. -/
theorem Qplus_nonneg (a b : Rat) (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
  Rat.add_nonneg Ha Hb

/-- The additive monotonicity `QArith` calls `Qplus_le_compat`: from
    `a <= b` and `c <= d`, `a + c <= b + d`.  Assembled from
    `Rat.add_le_add_right` and `Rat.add_le_add_left`, once. -/
theorem Qplus_le_compat {a b c d : Rat} (H1 : a ≤ b) (H2 : c ≤ d) :
    a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr H1) (Rat.add_le_add_left.mpr H2)

/-- Two numeral facts, named.  Both hold by conversion and both appear
    inside the induction steps of most of the arithmetic below, where a
    bare `decide` in the middle of a `≤` proof would read as a mistake.
    Neither is the pattern `Measure`'s header warns against: the operands
    are numerals this file wrote out, and nothing author-supplied is ever
    decided by computation. -/
theorem Qle_0_1 : (0 : Rat) ≤ 1 := by decide

theorem Qle_0_inv_256 : (0 : Rat) ≤ (1 : Rat) / 256 := by
  rw [Rat.div_def]
  have h256 : (0 : Rat) < (256 : Rat) := by decide
  exact Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr h256))

/-- A nonnegative quotient of two naturals, and the same quotient bounded by
    one when the numerator is at most the denominator.  Both are the
    calibration constants' side conditions (`1 # 16`, `15 # 16`, `1 # 5`,
    `1 # 33`) and both avoid `decide` on a `Rat` quotient, which does not
    reduce. -/
theorem Qdiv_nat_nonneg (a b : Nat) (hb : 0 < b) :
    (0 : Rat) ≤ ((a : Nat) : Rat) / (b : Nat) := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le a)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast hb)))

theorem Qdiv_nat_le_one (a b : Nat) (hb : 0 < b) (hab : a ≤ b) :
    ((a : Nat) : Rat) / (b : Nat) ≤ 1 := by
  have hb' : (0 : Rat) < (b : Nat) := by exact_mod_cast hb
  have hbne : ((b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hb'
  rw [Rat.div_def]
  refine Rat.le_of_mul_le_mul_right ?_ hb'
  have h : ((a : Nat) : Rat) * (b : Rat)⁻¹ * (b : Rat) = ((a : Nat) : Rat) := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hbne, Rat.mul_one]
  rw [h, Rat.one_mul]
  exact_mod_cast hab

theorem Qdiv_nat_lt_one (a b : Nat) (hb : 0 < b) (hab : a < b) :
    ((a : Nat) : Rat) / (b : Nat) < 1 := by
  have hb' : (0 : Rat) < (b : Nat) := by exact_mod_cast hb
  have hbne : ((b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hb'
  rw [Rat.div_def]
  refine Rat.lt_of_mul_lt_mul_right ?_ (Rat.le_of_lt hb')
  have h : ((a : Nat) : Rat) * (b : Rat)⁻¹ * (b : Rat) = ((a : Nat) : Rat) := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hbne, Rat.mul_one]
  rw [h, Rat.one_mul]
  exact_mod_cast hab

/-- A positive reciprocal of a positive natural, in the shape the
    certificates below use it (`1 / 3` twice over).  `decide` cannot
    evaluate a quotient of rationals — `Rat.normalize` is not
    kernel-reducible — so the strict positivity is obtained from
    `Rat.inv_pos` at a literal whose own positivity IS decidable. -/
theorem Qpos_one_div (n : Nat) (hn : 0 < n) : (0 : Rat) < 1 / (n : Nat) := by
  have hn' : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have h : (0 : Rat) < ((n : Nat) : Rat)⁻¹ := Rat.inv_pos.mpr hn'
  simpa [Rat.div_def] using h

/-- An equation read as an inequality.  `ring` closes equality goals and
    not `≤` ones, so each place below where the two sides of an
    inequality are in fact equal goes through this rather than inlining
    the same two lines. -/
theorem Qle_of_Qeq (a b : Rat) (H : a = b) : a ≤ b := by rw [H]; exact Rat.le_refl

/- =========================================================================
   Powers with a natural exponent
   ========================================================================= -/

/-- `QArith`'s `Qpower` takes a `Z` exponent, and the cost is NOT where
    one would guess.  The multiplicative algebra is fine there; the cost
    is on the two rules every induction in this file rewrites with,
    `Qpow_0` and `Qpow_succ`.  Here they hold BY CONVERSION, because the
    recursion is on a `nat`.  Peeling one factor off `q ^ (n + 1)` for a
    `Z` exponent goes through `Qpower_plus`, which demands a NON-ZERO
    BASE — a `Z` exponent may be negative, and a negative exponent is an
    inverse.  The base raised to powers here is
    `(1 - p_stop) * (1 # 256)`, and it is ZERO at `p_stop = 1`, the point
    mass on the empty standard input and a member of the geometric family
    in good standing.  The depth induction in `cyl_enum_sum_le` would
    therefore carry a case split on `p_stop = 1` through every step, to
    prove nothing. -/
def Qpow (q : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => q * Qpow q n

/-- The two computation rules, as rewrite rules: both hold by
    conversion, and are stated so that no proof below has to unfold a
    goal it only wants to unfold in one place. -/
theorem Qpow_0 (q : Rat) : Qpow q 0 = 1 := rfl

theorem Qpow_succ (q : Rat) (n : Nat) : Qpow q (n + 1) = q * Qpow q n := rfl

/-- `Qpow` respects equality in its base.  No `Proper` instance is
    declared, for the reason given at `qsum_ext`: it is applied where it
    is wanted rather than found by `rewrite`. -/
theorem Qpow_Qeq (q1 q2 : Rat) (n : Nat) (Heq : q1 = q2) :
    Qpow q1 n = Qpow q2 n := by rw [Heq]

/-- A nonnegative base has nonnegative powers — the fact that makes
    every geometric weight below nonnegative. -/
theorem Qpow_nonneg (q : Rat) (n : Nat) (Hq : 0 ≤ q) : 0 ≤ Qpow q n := by
  induction n with
  | zero => exact Qle_0_1
  | succ n ih => rw [Qpow_succ]; exact Rat.mul_nonneg Hq ih

/-- ... and a STRICTLY positive base has strictly positive powers.  The
    two are stated separately rather than one being derived from the
    other because they are used for opposite purposes: nonnegativity
    makes weights admissible, and this one is what makes a tail NON-ZERO
    — it is the whole content of `stdin_geometric_mass_not_attained`,
    where the omitted tail being positive is exactly why a finite list
    falls short. -/
theorem Qpow_pos (q : Rat) (n : Nat) (Hq : 0 < q) : 0 < Qpow q n := by
  induction n with
  | zero => exact (by decide : (0 : Rat) < 1)
  | succ n ih => rw [Qpow_succ]; exact Rat.mul_pos Hq ih

/-- Powers distribute over products, with no side condition.  This is the
    lemma the whole cancellation rests on: it splits the ratio
    `(1 - p_stop) * (1 # 256)` into the two powers the plan's closed form
    quotes, and it recombines `256 ^ n` with `(1/256) ^ n` into `1 ^ n`. -/
theorem Qpow_mult (a b : Rat) (n : Nat) :
    Qpow (a * b) n = Qpow a n * Qpow b n := by
  induction n with
  | zero => rw [Qpow_0, Qpow_0, Qpow_0]; grind
  | succ n ih => rw [Qpow_succ, Qpow_succ, Qpow_succ, ih]; grind

theorem Qpow_1 (n : Nat) : Qpow 1 n = 1 := by
  induction n with
  | zero => rw [Qpow_0]
  | succ n ih => rw [Qpow_succ, ih]; grind

/- =========================================================================
   Counting, as a rational
   ========================================================================= -/

/-- The rational named by a natural number.  The counting lemma below
    bounds the LENGTH of a list, and the bound it feeds is a sum of equal
    weights; getting from one to the other means multiplying a weight by
    a count, so the count has to become a rational.  `inject_Z` of
    `Z.of_nat` is that, and the four facts below are all that is ever
    asked of it. -/
def Qnat (n : Nat) : Rat := (n : Rat)

theorem Qnat_0 : Qnat 0 = 0 := rfl

theorem Qnat_succ (n : Nat) : Qnat (n + 1) = 1 + Qnat n := by
  unfold Qnat
  rw [Rat.natCast_add]
  grind

theorem Qnat_mult (m n : Nat) : Qnat (m * n) = Qnat m * Qnat n := by
  unfold Qnat
  rw [Rat.natCast_mul]

theorem Qnat_nonneg (n : Nat) : 0 ≤ Qnat n := by
  unfold Qnat
  exact Rat.natCast_nonneg

/-- Counting is monotone, which is how "the list is no longer than
    `256 ^ n`" becomes "its sum is no more than `256 ^ n` weights". -/
theorem Qnat_le (m n : Nat) (H : m ≤ n) : Qnat m ≤ Qnat n := by
  unfold Qnat
  exact Rat.natCast_le_natCast.mpr H

/-- The one numeral that matters, and its powers.  `Qnat 256 = 256` is
    conversion — `Z.of_nat` on a literal — and not a decision about `Q`:
    the two sides are the same rational written twice. -/
theorem Qnat_256 : Qnat 256 = (256 : Rat) := rfl

theorem Qnat_pow_256 (n : Nat) : Qnat (256 ^ n) = Qpow (256 : Rat) n := by
  induction n with
  | zero => rw [Nat.pow_zero, Qpow_0]; rfl
  | succ n ih =>
    rw [Nat.pow_succ, Qnat_mult, ih, Qnat_256, Qpow_succ]
    grind

/- =========================================================================
   Deciding equality of cores
   ========================================================================= -/

/-- `FinInput.FinCore` has decidable equality, and every combinator that
    sums entries per core needs it: "the weight of `c` is the total of
    the entries naming `c`" is not a definition until "naming `c`" can be
    decided.

    It is derivable rather than assumed because every field is built from
    `BvBase.byte` and lists: `FinInput.core_argv` and
    `FinInput.core_envp` are `list (list byte)`, `FinInput.core_stdin` is
    `list byte`, and `Fs.Fs` is by definition `list (Fs.path * list
    byte)`.  (Lean has no `solve_decision`; the instance below is the
    field-by-field decision the structure's equality is.) -/
instance FinCore_eq_dec : DecidableEq FinCore := fun a b =>
  if h : a.core_argv = b.core_argv ∧ a.core_envp = b.core_envp ∧
      a.core_fs = b.core_fs ∧ a.core_stdin = b.core_stdin then
    isTrue (by
      obtain ⟨h1, h2, h3, h4⟩ := h
      cases a with
      | mkFinCore a1 a2 a3 a4 =>
        cases b with
        | mkFinCore b1 b2 b3 b4 =>
          simp only at h1 h2 h3 h4
          subst h1; subst h2; subst h3; subst h4; rfl)
  else
    isFalse (by
      intro hab
      apply h
      cases hab
      exact ⟨rfl, rfl, rfl, rfl⟩)

/- =========================================================================
   The author-facing packaging
   ========================================================================= -/

/-- A weight on CORES together with the total it declares.

    Three fields and no more: the weight, the declared mass `M` that
    `Measure.weight_bound_T` multiplies by `b`, and the nonnegativity the
    lift needs to discharge `Measure.DISTRIBUTION`'s `w_nonneg`.
    Nonnegativity is a FIELD rather than a side condition on each lemma
    so that it travels with the object: a `CoreDistribution` in hand is
    already known to be usable, and a would-be distribution that fails it
    cannot be built (see `negative_entries_no_core_distribution`).

    There is deliberately no field relating `cd_mass` to `cd_weight`.
    `Measure`'s header is explicit that `M` is trusted metadata with no
    normalization obligation, and inventing one here would be this
    library claiming an authority over the trusted layer that it does not
    have.  What is offered instead is the certificate pair —
    `finite_support_mass_upper` and `finite_support_mass_lower_witness` —
    which a task may prove and print, per combinator. -/
structure CoreDistribution where
  cd_weight : FinCore → Rat
  cd_mass : Rat
  cd_nonneg : ∀ c, 0 ≤ cd_weight c

/-- The weight on RECORDS that a `CoreDistribution` denotes: read the
    core, weigh it.  This is the only way a weight built here reaches
    `Measure.DISTRIBUTION`, and it is what makes `w_core_blind` a theorem
    about the library rather than an obligation per task. -/
def cd_lift (D : CoreDistribution) : FinProcInput → Rat :=
  fun f => D.cd_weight (fin_core f)

/-- `Measure.DISTRIBUTION`'s `w_nonneg`, for every lift: the record's own
    field, at the record's core. -/
theorem cd_lift_nonneg (D : CoreDistribution) (f : FinProcInput) :
    0 ≤ cd_lift D f :=
  D.cd_nonneg (fin_core f)

/-- `Measure.DISTRIBUTION`'s `w_core_blind`, for every lift.  Equal cores
    are the same argument to the same function, so the values are `eq` and
    the `Qeq` follows; the rewrite is the whole proof.  This is the design
    move of the file cashed in — see the header. -/
theorem cd_lift_core_blind (D : CoreDistribution) (f g : FinProcInput)
    (Heq : fin_core f = fin_core g) : cd_lift D f = cd_lift D g := by
  unfold cd_lift
  rw [Heq]

/- =========================================================================
   The sums the bounds are stated on
   ========================================================================= -/

/-- `Measure.sum_weights` of a lifted weight.  Definitionally the measure
    layer's own sum — see `core_sum_sum_weights` and `core_sum_cd_lift` —
    so a bound proved about `core_sum` is a bound about the quantity
    `Measure.weight_bound_T` compares against `b * M`, with nothing in
    between. -/
def core_sum (w : FinCore → Rat) (l : List FinProcInput) : Rat :=
  sum_weights (fun f => w (fin_core f)) l

/-- The bridge to `Measure.sum_weights`, by conversion. -/
theorem core_sum_sum_weights (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum w l = sum_weights (fun f => w (fin_core f)) l := rfl

/-- The bridge in the form a consumer meets it: the sum
    `Measure.weight_bound_T` takes of a lifted distribution IS the
    library's sum of its core weight. -/
theorem core_sum_cd_lift (D : CoreDistribution) (l : List FinProcInput) :
    core_sum D.cd_weight l = sum_weights (cd_lift D) l := rfl

/-- THE PREDICATE-INDEXED CROSSING, at the level every bound in this
    library is actually proved at.

    `GatedSize.weight_bound_pred_T` bounds the mass OUTSIDE a predicate
    rather than the mass of a classifier's reject set, and this library
    needs no new machinery to reach it — which is the point.  Every
    arithmetic bound below is stated over an arbitrary list under
    `List.NoDup` of its cores plus a per-member side condition, and the
    classifier appears in exactly one place, as one hypothesis that turns
    "rejected" into "has a fire core".  Replace that hypothesis with
    "valid and outside `P`" and nothing else moves.

    The three arguments are the three things a task actually supplies:

    - `Fire`, the set of cores its bound is proved about, as a predicate
      on `FinInput.FinCore` — the library's own vocabulary, not the
      classifier's;
    - the CROSSING, `Hfire`: every valid record outside `P` has a fire
      core.  This is the only place the task's own analysis of its
      programs enters, and it is where the `FinInput.FinCore` quotient is
      paid for: a predicate on RECORDS is being answered by a statement
      about CORES, which is sound in this direction because the
      conclusion charges every core with SOME representative outside `P`;
    - the BOUND, `Hbound`: fire-core lists weigh at most `B`.  Every
      composition lemma in this file — `finite_support_bound_subset`,
      `stdin_geometric_bound` — produces exactly this shape, so a task
      hands over what it already proved.

    `B <= b * cd_mass D` is the arithmetic step, kept separate rather
    than baked in because quantifying over `b` is what lets one proof
    serve every multiplier a task might declare, and it puts the ceiling
    where a reader can see it. -/
theorem weight_bound_pred_T_of_core_bound (D : CoreDistribution)
    (P : FinProcInput → Prop) (Fire : FinCore → Prop) (B b : Rat)
    (Hfire : ∀ f, valid_fin_input f → ¬ P f → Fire (fin_core f))
    (Hbound : ∀ l : List FinProcInput, (List.map fin_core l).Nodup →
      (∀ f, f ∈ l → Fire (fin_core f)) → core_sum D.cd_weight l ≤ B)
    (Hb : B ≤ b * D.cd_mass) :
    GatedSize.weight_bound_pred_T P (cd_lift D) D.cd_mass b := by
  intro l Hnd Hall
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (Hbound l Hnd ?_) Hb
  intro f Hf
  exact Hfire f (Hall f Hf).1 (Hall f Hf).2

theorem core_sum_nil (w : FinCore → Rat) : core_sum w [] = 0 := rfl

theorem core_sum_cons (w : FinCore → Rat) (f : FinProcInput)
    (l : List FinProcInput) :
    core_sum w (f :: l) = w (fin_core f) + core_sum w l := rfl

/- =========================================================================
   Sums over a list of anything
   ========================================================================= -/

/-- THE SUM every bound in this file is stated on: a `fold_right` of a
    weight over a list, at whatever element type the list has.

    ONE sum and not two.  The counting arguments run over lists of
    `FinInput.FinCore` — that is what `core_sum_map_fin_core` turns the
    obligation's records into — while the envp-varying families sum over
    BYTE LISTS (one envp entry, one standard input) and over LISTS of byte
    lists (a whole launch-time environment).

    Two lemmas genuinely cannot generalise, because they need decidable
    equality on the element type: `qsum_core_remove_one` and the inclusion
    bound `qsum_core_incl_le` that runs on it.  Those two keep `core` in
    their names and stay at `FinInput.FinCore`, which is where this file
    spends them.  Everything else below is stated at the open element
    type. -/
def qsum {A : Type} (w : A → Rat) (l : List A) : Rat :=
  List.foldr (fun x acc => w x + acc) 0 l

theorem qsum_nil {A : Type} (w : A → Rat) : qsum w [] = 0 := rfl

theorem qsum_cons {A : Type} (w : A → Rat) (x : A) (l : List A) :
    qsum w (x :: l) = w x + qsum w l := rfl

theorem qsum_app {A : Type} (w : A → Rat) (l1 l2 : List A) :
    qsum w (l1 ++ l2) = qsum w l1 + qsum w l2 := by
  induction l1 with
  | nil => rw [List.nil_append, qsum_nil]; grind
  | cons x l ih => rw [List.cons_append, qsum_cons, qsum_cons, ih]; grind

theorem qsum_nonneg {A : Type} (w : A → Rat) (l : List A)
    (Hw : ∀ x, x ∈ l → 0 ≤ w x) : 0 ≤ qsum w l := by
  induction l with
  | nil => rw [qsum_nil]; exact Rat.le_refl
  | cons x l ih =>
    rw [qsum_cons]
    exact Qplus_nonneg _ _ (Hw x (List.mem_cons_self ..))
      (ih (fun y Hy => Hw y (List.mem_cons_of_mem _ Hy)))

/-- Weights that agree ON THE LIST sum equally.  No `Proper` instance is
    declared for `qsum`: its first argument is a function and the
    equivalence wanted of it is pointwise equality, so the fact is a lemma
    applied where it is needed rather than something `rewrite` finds on
    its own.

    The hypothesis is `List.In x l` rather than agreement everywhere, and
    the difference is not cosmetic: every RESTRICTION argument — "this
    weight agrees with that one on the cores I am summing over, and
    nowhere else" — has the equality only on the list.
    `finite_support_bound_subset` is the case in point: the entries a core
    predicate rejects contribute nothing at the cores the predicate
    accepts, and nothing at all is known about them elsewhere. -/
theorem qsum_ext {A : Type} (w1 w2 : A → Rat) (l : List A)
    (Hext : ∀ x, x ∈ l → w1 x = w2 x) : qsum w1 l = qsum w2 l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [qsum_cons, qsum_cons, Hext x (List.mem_cons_self ..),
      ih (fun y Hy => Hext y (List.mem_cons_of_mem _ Hy))]

theorem qsum_mono {A : Type} (w1 w2 : A → Rat) (l : List A)
    (Hle : ∀ x, x ∈ l → w1 x ≤ w2 x) : qsum w1 l ≤ qsum w2 l := by
  induction l with
  | nil => rw [qsum_nil, qsum_nil]; exact Rat.le_refl
  | cons x l ih =>
    rw [qsum_cons, qsum_cons]
    exact Qplus_le_compat (Hle x (List.mem_cons_self ..))
      (ih (fun y Hy => Hle y (List.mem_cons_of_mem _ Hy)))

theorem qsum_scale {A : Type} (c : Rat) (w : A → Rat) (l : List A) :
    qsum (fun x => c * w x) l = c * qsum w l := by
  induction l with
  | nil => rw [qsum_nil, qsum_nil]; grind
  | cons x l ih =>
    rw [qsum_cons, qsum_cons, ih]
    grind

theorem qsum_map {A B : Type} (w : B → Rat) (f : A → B) (l : List A) :
    qsum w (List.map f l) = qsum (fun x => w (f x)) l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, qsum_cons, qsum_cons, ih]

/-- A `List.flat_map` is the sum of its blocks EXACTLY, and not merely up
    to a uniform bound.  `qsum_flat_map_const_le` charges every block the
    same constant, which is right for the 256 continuations of a
    standard-input cylinder and wrong for the envp enumeration below,
    where the block under an entry `e` is charged a factor depending on
    `e`'s own length.  Stating the identity and deriving the inequality
    from `qsum_mono` gives both shapes out of one induction. -/
theorem qsum_flat_map {A B : Type} (w : B → Rat) (f : A → List B)
    (l : List A) : qsum w (l.flatMap f) = qsum (fun x => qsum w (f x)) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, qsum_app, qsum_cons, ih]

theorem qsum_flat_map_le {A B : Type} (w : B → Rat) (f : A → List B)
    (g : A → Rat) (l : List A)
    (Hb : ∀ x, x ∈ l → qsum w (f x) ≤ g x) :
    qsum w (l.flatMap f) ≤ qsum g l := by
  rw [qsum_flat_map]
  exact qsum_mono _ _ l Hb

/-- `List.map` commutes past `List.flat_map`.  Stdlib ships
    `List.flat_map_concat_map` and `List.concat_map` and leaves the
    composite to be assembled; the direct induction is three lines and is
    what `cyl_enum_bytes_cyl` below needs. -/
theorem map_flat_map_comm (A B C : Type) (f : B → C) (g : A → List B)
    (l : List A) :
    List.map f (l.flatMap g) = (l.map g).flatMap (List.map f) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, List.map_cons,
      List.flatMap_cons, ih]

/-- Summing a lifted weight over records is summing the weight over their
    cores.  Both folds add the same rationals in the same order; the
    induction is bookkeeping. -/
theorem core_sum_map_fin_core (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum w l = qsum w (List.map fin_core l) := by
  induction l with
  | nil => rfl
  | cons f l ih => rw [core_sum_cons, ih, List.map_cons, qsum_cons]

/-- The zero weight sums to zero. -/
theorem qsum_zero {A : Type} (cs : List A) : qsum (fun _ : A => 0) cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [qsum_cons, ih]; grind

/-- Sums add pointwise.  This is what splits an entry list's weight into
    "the head entry" plus "the rest" without touching the list being
    summed over. -/
theorem qsum_plus {A : Type} (w1 w2 : A → Rat) (cs : List A) :
    qsum (fun c => w1 c + w2 c) cs = qsum w1 cs + qsum w2 cs := by
  induction cs with
  | nil => rw [qsum_nil, qsum_nil, qsum_nil]; grind
  | cons c cs ih => rw [qsum_cons, qsum_cons, qsum_cons, ih]; grind

/- =========================================================================
   Combinator: finite support
   ========================================================================= -/

/-- The weight a single entry assigns: `q` at its own core, zero
    everywhere else.  Every `finite_support` weight is a sum of these,
    and the three lemmas below — absent, present, bounded — are the
    counting content of this file. -/
def core_indicator (c0 : FinCore) (q : Rat) (c : FinCore) : Rat :=
  if c0 = c then q else 0

/-- Its two values, as rewrite rules.  Stated rather than unfolded at
    each use so that no proof below has to name the decision instance:
    the case analysis happens here, once. -/
theorem core_indicator_hit (c0 : FinCore) (q : Rat) :
    core_indicator c0 q c0 = q := by
  unfold core_indicator
  rw [ite_eq_left rfl]

theorem core_indicator_miss (c0 : FinCore) (q : Rat) (c : FinCore)
    (Hne : c0 ≠ c) : core_indicator c0 q c = 0 := by
  unfold core_indicator
  rw [ite_eq_right Hne]

/-- Over a list that does not mention the entry's core, the entry
    contributes nothing. -/
theorem qsum_indicator_absent (c0 : FinCore) (q : Rat) (cs : List FinCore)
    (Hnin : c0 ∉ cs) : qsum (core_indicator c0 q) cs = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [qsum_cons,
      core_indicator_miss c0 q c (fun h => Hnin (List.mem_cons.mpr (Or.inl h))),
      ih (fun h => Hnin (List.mem_cons_of_mem c h))]
    grind

/-- Over a DUPLICATE-FREE list that does mention it, the entry
    contributes exactly its weight — once, which is the whole reason
    `Measure.weight_bound_T` carries the `List.NoDup` hypothesis.  The
    induction is on the `List.NoDup` derivation: its step case hands over
    precisely the "the head does not occur again" fact that
    `qsum_indicator_absent` consumes. -/
theorem qsum_indicator_present (c0 : FinCore) (q : Rat) (cs : List FinCore)
    (Hnd : cs.Nodup) (Hin : c0 ∈ cs) : qsum (core_indicator c0 q) cs = q := by
  induction cs with
  | nil => cases Hin
  | cons c cs ih =>
    have hnot : c ∉ cs := (List.nodup_cons.mp Hnd).1
    have hnd : cs.Nodup := (List.nodup_cons.mp Hnd).2
    rw [qsum_cons]
    by_cases hc : c0 = c
    · cases hc
      rw [core_indicator_hit, qsum_indicator_absent c0 q cs hnot]
      grind
    · rw [core_indicator_miss c0 q c hc]
      rcases List.mem_cons.mp Hin with h | h
      · exact absurd h hc
      · rw [ih hnd h]; grind

/-- Either way, a nonnegative entry contributes at most its weight.  This
    is the per-entry half of `finite_support_bound`; the list is
    duplicate-free, so the entry is either counted once or not at all,
    and both cases are already proved. -/
theorem qsum_indicator_le (c0 : FinCore) (q : Rat) (cs : List FinCore)
    (Hq : 0 ≤ q) (Hnd : cs.Nodup) : qsum (core_indicator c0 q) cs ≤ q := by
  by_cases Hin : c0 ∈ cs
  · rw [qsum_indicator_present c0 q cs Hnd Hin]; exact Rat.le_refl
  · rw [qsum_indicator_absent c0 q cs Hin]; exact Hq

/-- The weight an entry list assigns to a core: the total of the entries
    naming it.  SUMMED, not "the first one wins": a duplicate core is an
    author writing the same core twice, and the reading that keeps
    `entries_mass` — a flat sum over the entries — equal to the total
    weight is the one that adds them.  The alternative would make
    `finite_support_mass_lower_witness` false on any list with a repeat.

    Both halves of that are pinned rather than asserted:
    `dup_entries_weight_summed` computes the repeated core's weight and
    finds the sum, and `dup_witness_attains_mass` shows the declared mass
    still attained on the very list a first-wins reading would strand
    below it. -/
def entries_weight (entries : List (FinCore × Rat)) (c : FinCore) : Rat :=
  match entries with
  | [] => 0
  | e :: rest => core_indicator e.1 e.2 c + entries_weight rest c

/-- The declared mass of an entry list: the sum of the entries' weights,
    with no reference to which cores they name. -/
def entries_mass (entries : List (FinCore × Rat)) : Rat :=
  List.foldr (fun e acc => e.2 + acc) 0 entries

theorem entries_mass_nil : entries_mass [] = 0 := rfl

theorem entries_mass_cons (e : FinCore × Rat) (entries : List (FinCore × Rat)) :
    entries_mass (e :: entries) = e.2 + entries_mass entries := rfl

/-- The declared mass of a nonnegative entry list is nonnegative.  This is
    the first half of `Measure.DISTRIBUTION`'s `M_nonneg` for everything
    this library builds out of `finite_support`: `entries_mass` is a fold
    of addition over the entry weights, so the hypothesis the constructor
    already demands is the hypothesis this needs, entry by entry.

    Nothing here ties the mass to the weight FUNCTION — the header's
    "there is deliberately no field relating `cd_mass` to `cd_weight`"
    still stands.  The claim is only about the sign of a declared
    number. -/
theorem entries_mass_nonneg (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) : 0 ≤ entries_mass entries := by
  induction entries with
  | nil => rw [entries_mass_nil]; exact Rat.le_refl
  | cons e rest ih =>
    rw [entries_mass_cons]
    exact Qplus_nonneg _ _ (Hnn e (List.mem_cons_self ..))
      (ih (fun e' He' => Hnn e' (List.mem_cons_of_mem _ He')))

/-- Splitting the head entry off a sum, in the form the two bounds below
    both need: the entry list's weight summed over `cs` is the head's
    indicator summed over `cs` plus the tail's weight summed over `cs`.
    `qsum_plus` does the work; the extensionality step is there only
    because the fixpoint's unfolding is a pointwise equation. -/
theorem qsum_entries_cons (e : FinCore × Rat) (entries : List (FinCore × Rat))
    (cs : List FinCore) :
    qsum (entries_weight (e :: entries)) cs =
      qsum (core_indicator e.1 e.2) cs + qsum (entries_weight entries) cs := by
  rw [← qsum_plus]
  exact qsum_ext _ _ _ (fun c _ => rfl)

/-- Nonnegative entries give a nonnegative weight — the field
    `finite_support` has to fill in.  Induction on the entries, with the
    head's indicator nonnegative by case analysis. -/
theorem entries_weight_nonneg (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∀ c, 0 ≤ entries_weight entries c := by
  induction entries with
  | nil => intro c; exact Rat.le_refl
  | cons e entries ih =>
    intro c
    have Hhead : 0 ≤ core_indicator e.1 e.2 c := by
      unfold core_indicator
      by_cases h : e.1 = c
      · rw [ite_eq_left h]; exact Hnn e (List.mem_cons_self ..)
      · rw [ite_eq_right h]; exact Rat.le_refl
    have Htail : 0 ≤ entries_weight entries c :=
      ih (fun e' He' => Hnn e' (List.mem_cons_of_mem _ He')) c
    exact Qplus_nonneg _ _ Hhead Htail

/-- THE BOUND, over cores: any duplicate-free list of cores sums to at
    most the entry list's declared mass.  Induction on the ENTRIES, not on
    the list — the list is fixed and its duplicate-freedom is used once
    per entry, by `qsum_indicator_le`, which is where the hypothesis does
    its work.  Each entry contributes at most its own weight to the sum,
    and the mass is exactly the total of those weights, so the bound falls
    out entry by entry.

    Nonnegativity is needed for entries the list does NOT mention: they
    contribute nothing to the sum but their weight to the mass, and a
    negative one would make the mass the smaller number. -/
theorem entries_weight_qsum_le (entries : List (FinCore × Rat))
    (cs : List FinCore) (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2)
    (Hnd : cs.Nodup) : qsum (entries_weight entries) cs ≤ entries_mass entries := by
  induction entries with
  | nil =>
    rw [entries_mass_nil]
    have h0 : qsum (entries_weight []) cs = 0 := by
      have hfun : entries_weight ([] : List (FinCore × Rat)) = (fun _ => 0) := rfl
      rw [hfun]; exact qsum_zero cs
    rw [h0]; exact Rat.le_refl
  | cons e entries ih =>
    rw [qsum_entries_cons, entries_mass_cons]
    exact Qplus_le_compat
      (qsum_indicator_le e.1 e.2 cs (Hnn e (List.mem_cons_self ..)) Hnd)
      (ih (fun e' He' => Hnn e' (List.mem_cons_of_mem _ He')))

/-- The distribution supported on a finite list of (core, weight)
    entries.  The nonnegativity proof is an ARGUMENT, not a side
    condition discovered later: see the header for why refusing it is not
    on offer, and `negative_entries_no_core_distribution` for what happens
    when the entries cannot supply it. -/
def finite_support (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) : CoreDistribution where
  cd_weight := entries_weight entries
  cd_mass := entries_mass entries
  cd_nonneg := entries_weight_nonneg entries Hnn

/-- `Measure.DISTRIBUTION`'s `M_nonneg`, for a finite support: the proof
    argument the constructor already took is exactly what the declared
    mass needs, so an author who built the distribution owes nothing
    further.  `entries_mass_nonneg` is the content. -/
theorem finite_support_mass_nonneg (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    0 ≤ (finite_support entries Hnn).cd_mass :=
  entries_mass_nonneg entries Hnn

/-- Discharging `finite_support`'s proof argument BY COMPUTATION, which is
    what a task author will actually want to do.  An entry list is
    written out as a literal, so "every entry is nonnegative" is a
    decidable fact about closed rationals, and this bridge turns it into
    one boolean scan: the obligation becomes `rfl` at the definition site
    — see `example_entries_nonneg` and `dup_cd` below, which use it in the
    two available styles.

    (`Qle_bool` is `decide (· ≤ ·)` here, per the conventions
    the rest of this tree uses; no rational EQUALITY is decided.) -/
theorem entries_nonneg_of_forallb (entries : List (FinCore × Rat))
    (Hall : entries.all (fun e => decide (0 ≤ e.2)) = true) :
    ∀ e, e ∈ entries → 0 ≤ e.2 := by
  intro e He
  rw [List.all_eq_true] at Hall
  exact of_decide_eq_true (Hall e He)

/-- THE EXPORT: any list of records with pairwise distinct cores — the
    exact hypothesis `Measure.weight_bound_T` carries — weighs at most the
    declared mass.  `core_sum_map_fin_core` turns the records into their
    cores and the hypothesis into an ordinary `List.NoDup`; the rest is
    `entries_weight_qsum_le`.

    This is the lemma a task's `Measure.weight_bound_T` proof consumes.
    That obligation compares the sum against `b * M`, so at `b = 1` it is
    this bound plus `Rat.mul_one`, and `Measure.weight_bound_mono` carries
    a proof at one `b` to every larger one.

    The `List.NoDup` hypothesis is doing work, not inherited decoration:
    `finite_support_bound_needs_nodup` exhibits a two-element list that
    the bound fails on and that duplicate-freedom of the cores is exactly
    what excludes. -/
theorem finite_support_bound (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (finite_support entries Hnn).cd_weight l ≤
      (finite_support entries Hnn).cd_mass := by
  rw [core_sum_map_fin_core]
  show qsum (entries_weight entries) (List.map fin_core l) ≤ entries_mass entries
  exact entries_weight_qsum_le entries (List.map fin_core l) Hnn Hnd

/- =========================================================================
   The same bound, refined to a subset of the cores
   ========================================================================= -/

/-- The entries naming a core the predicate accepts.  A `bool`-valued
    predicate rather than a `Prop` one, because the restriction has to be
    COMPUTED — `entries_mass` of the restriction is the number the refined
    bound compares against, and a task author writing that number down
    wants it to reduce. -/
def entries_restrict (P : FinCore → Bool) (entries : List (FinCore × Rat)) :
    List (FinCore × Rat) :=
  List.filter (fun e => P e.1) entries

/-- Restricting keeps every entry's weight nonnegative, since it only
    removes entries. -/
theorem entries_restrict_nonneg (P : FinCore → Bool)
    (entries : List (FinCore × Rat)) (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∀ e, e ∈ entries_restrict P entries → 0 ≤ e.2 := by
  intro e He
  unfold entries_restrict at He
  exact Hnn e (List.mem_filter.mp He).1

/-- AT AN ACCEPTED CORE, the discarded entries were contributing nothing:
    an entry the predicate rejects names a core the predicate rejects,
    which is not the core being weighed, so its indicator misses.  This is
    the whole content of the refinement, and note where it does NOT hold —
    at a core the predicate rejects, the two weights differ, which is why
    the bound below quantifies over lists of accepted cores and why
    `qsum_ext`'s hypothesis had to be the on-the-list one. -/
theorem entries_weight_restrict (P : FinCore → Bool)
    (entries : List (FinCore × Rat)) (c : FinCore) (HP : P c = true) :
    entries_weight entries c = entries_weight (entries_restrict P entries) c := by
  unfold entries_restrict
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    rw [List.filter_cons]
    split
    · next hf =>
      show core_indicator e.1 e.2 c + entries_weight entries c
        = core_indicator e.1 e.2 c + entries_weight (List.filter (fun e => P e.1) entries) c
      rw [ih]
    · next hf =>
      show core_indicator e.1 e.2 c + entries_weight entries c
        = entries_weight (List.filter (fun e => P e.1) entries) c
      have hmiss : core_indicator e.1 e.2 c = 0 := by
        apply core_indicator_miss
        intro heq
        rw [heq, HP] at hf
        exact absurd hf (by decide)
      rw [hmiss, ih]
      grind

/-- THE PER-SUBSET REFINEMENT: a list whose cores all satisfy `P` weighs
    at most the mass of the `P`-entries ALONE, not the mass of all of
    them.

    `finite_support_bound` is the case `P` accepts everything
    (`entries_restrict_all`), so nothing is lost by having only this one —
    but the refinement is what a task needs when its fire set is a known
    part of the support and the rest of the declared mass sits on cores
    the classifier accepts.  Charging that part against the fire set would
    be giving away the bound.

    The proof is one rewrite and then the unrefined bound: on the cores
    actually being summed over, the restricted entry list weighs what the
    full one does (`entries_weight_restrict`), and
    `entries_weight_qsum_le` applies to the restriction with the
    nonnegativity it inherits. -/
theorem finite_support_bound_subset (P : FinCore → Bool)
    (entries : List (FinCore × Rat)) (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (HP : ∀ f, f ∈ l → P (fin_core f) = true) :
    core_sum (finite_support entries Hnn).cd_weight l ≤
      entries_mass (entries_restrict P entries) := by
  rw [core_sum_map_fin_core]
  have hw : (finite_support entries Hnn).cd_weight = entries_weight entries := rfl
  rw [hw]
  have hext : qsum (entries_weight entries) (List.map fin_core l) =
      qsum (entries_weight (entries_restrict P entries)) (List.map fin_core l) := by
    apply qsum_ext
    intro c Hc
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp Hc
    exact entries_weight_restrict P entries (fin_core f) (HP f hf)
  rw [hext]
  exact entries_weight_qsum_le (entries_restrict P entries) (List.map fin_core l)
    (entries_restrict_nonneg P entries Hnn) Hnd

/-- The refinement subsumes the total-mass bound rather than sitting
    beside it: at the predicate that accepts everything, the restriction
    is the entry list itself, so `finite_support_bound_subset` IS
    `finite_support_bound`. -/
theorem entries_restrict_all (entries : List (FinCore × Rat)) :
    entries_restrict (fun _ => true) entries = entries := by
  unfold entries_restrict
  exact List.filter_eq_self.mpr (fun a _ => rfl)

/- =========================================================================
   Wrapping a core back up as a record
   ========================================================================= -/

/-- A canonical `FinInput.FinProcInput` over a given core.  The four core
    fields are copied; the launch-environment fields are invented, and
    the choices are these:

    - `fin_uid`, `fin_gid`, `fin_nofile` and `fin_sigmask` are all zero.
      `Run.valid_input` constrains exactly these four of the seven — the
      ids through `Run.valid_creds`, the descriptor limit through
      `Run.valid_nofile`, and the blocked mask through `Run.valid_sigmask`
      — and zero satisfies all four, being the smallest value for the
      first three and the empty mask for the last.
    - `fin_groups` is the empty list and `fin_net` is `State.net_silent`,
      the quiet environment `State` declares for fixtures.
    - `fin_hwcap` is `hwcap_rv64gc`: `Run.valid_hwcap` admits exactly two
      words, and a zero is neither, so a zero here would make every
      core's input unprovable whatever its argv said.  Choosing a value
      that CAN be valid is not the same as claiming it is.
    - `fin_abort_terminal` is `false`, the declaration `Run.valid_input`
      pins and so the only value that can be valid under the predicate
      this library's callers discharge.
    - `fin_urandom` and `fin_tmp` are empty, as `[] []`.

    The choice is arbitrary and is allowed to be, because
    `FinInput.fin_core` forgets all of them (`FinInput.fin_core_env_eq`
    pins that it forgets these and nothing else).  What the embedding is
    FOR is `fin_core_core_input`: it is a section of `FinInput.fin_core`,
    so a statement about a list of cores can be re-stated as a statement
    about a list of records without changing any sum.

    It is NOT claimed that `core_input c` is valid: validity constrains
    argv, envp and the file system, which come from the core, and the
    library cannot know an author's cores denote a valid input. -/
def core_input (c : FinCore) : FinProcInput where
  fin_argv := c.core_argv
  fin_envp := c.core_envp
  fin_image_fs := c.core_fs
  fin_stdin := c.core_stdin
  fin_uid := BitVec.ofInt 64 0
  fin_gid := BitVec.ofInt 64 0
  fin_groups := []
  fin_net := net_silent
  fin_nofile := BitVec.ofInt 64 0
  fin_sigmask := BitVec.ofInt 64 0
  fin_hwcap := StackLayout.hwcap_rv64gc
  fin_abort_terminal := false
  fin_va_size := .Sv48
  fin_urandom := []
  fin_tmp := []

/-- The embedding is a section of `FinInput.fin_core`: wrapping a core up
    and reading it back gives the core. -/
theorem fin_core_core_input (c : FinCore) : fin_core (core_input c) = c := by
  cases c
  rfl

/-- ... and so a list of cores, wrapped, has exactly those cores. -/
theorem map_fin_core_core_input (cs : List FinCore) :
    List.map fin_core (List.map core_input cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, List.map_cons, fin_core_core_input, ih]

/-- THE RESTRICTION TO CORES COSTS NOTHING, mechanized.  Building every
    weight on `FinInput.FinCore` looks like a narrowing — the library
    cannot express a weight that reads `FinInput.fin_uid` — and it is not
    one, because `Measure.DISTRIBUTION` cannot accept such a weight
    either.  Any `w` satisfying its two WEIGHT obligations agrees,
    pointwise, with the lift of the `CoreDistribution` that weighs a core
    by `w` at that core's canonical record; the declared mass is free of
    `w`, since no obligation ties `M` to it — `M_nonneg` constrains its
    sign and nothing more.

    So "this library builds all the distributions there are" is a theorem
    rather than a hope, and a task author who cannot see how to phrase
    their weight as a `CoreDistribution` is looking at a presentation
    problem, not at an expressiveness limit. -/
theorem cd_lift_complete (w : FinProcInput → Rat) (M : Rat)
    (Hnn : ∀ f, 0 ≤ w f)
    (Hblind : ∀ f g, fin_core f = fin_core g → w f = w g) :
    ∃ D : CoreDistribution, D.cd_mass = M ∧ ∀ f, w f = cd_lift D f := by
  refine ⟨⟨fun c => w (core_input c), M, fun c => Hnn (core_input c)⟩, rfl, ?_⟩
  intro f
  show w f = w (core_input (fin_core f))
  exact Hblind f _ (by rw [fin_core_core_input])

/- =========================================================================
   Honesty certificates for `finite_support`
   ========================================================================= -/

/-- UPPER: every admissible partial sum is at most the declared mass.
    This is `finite_support_bound` under the name the certificate
    vocabulary uses — stated separately so that a consumer looking for the
    certificate finds one, and so that the pair (upper, lower) reads as a
    pair. -/
theorem finite_support_mass_upper (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (finite_support entries Hnn).cd_weight l ≤
      (finite_support entries Hnn).cd_mass :=
  finite_support_bound entries Hnn l Hnd

/-- The counting fact behind the lower witness: over a duplicate-free list
    of cores that COVERS every entry, the sum reaches the mass.  Induction
    on the entries again, with `qsum_indicator_present` — rather than
    `qsum_indicator_le` — at the head, which is where the coverage
    hypothesis is spent.  Note this direction needs no nonnegativity:
    nothing is being dropped. -/
theorem entries_mass_le_qsum (entries : List (FinCore × Rat))
    (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcov : ∀ e, e ∈ entries → e.1 ∈ cs) :
    entries_mass entries ≤ qsum (entries_weight entries) cs := by
  induction entries with
  | nil =>
    rw [entries_mass_nil]
    have h0 : qsum (entries_weight []) cs = 0 := by
      have hfun : entries_weight ([] : List (FinCore × Rat)) = (fun _ => 0) := rfl
      rw [hfun]; exact qsum_zero cs
    rw [h0]; exact Rat.le_refl
  | cons e entries ih =>
    rw [entries_mass_cons, qsum_entries_cons]
    refine Qplus_le_compat ?_ (ih (fun e' He' => Hcov e' (List.mem_cons_of_mem _ He')))
    rw [qsum_indicator_present e.1 e.2 cs Hnd (Hcov e (List.mem_cons_self ..))]
    exact Rat.le_refl

/-- LOWER, with the CHOICE of list left to the caller: any duplicate-free
    list of cores that COVERS the entries attains the declared mass, once
    wrapped by `core_input`.

    The content and the choice are separated because a MIXTURE needs them
    separated: `cd_mix2_finite_support_mass_exact`, far below, has to
    attain two components on ONE list, and neither component's canonical
    witness need cover the other's cores. -/
theorem finite_support_mass_lower_on (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcov : ∀ e, e ∈ entries → e.1 ∈ cs) :
    (finite_support entries Hnn).cd_mass ≤
      core_sum (finite_support entries Hnn).cd_weight (List.map core_input cs) := by
  show entries_mass entries ≤
    core_sum (entries_weight entries) (List.map core_input cs)
  rw [core_sum_map_fin_core, map_fin_core_core_input]
  exact entries_mass_le_qsum entries cs Hnd Hcov

/-- Removing repeats from a list of cores, keeping the first occurrence of
    each.  `List.nodup` does not ship in Stdlib; this is that function with the two facts the lower witness
    spends: membership is preserved, and the result is duplicate-free.
    (DEVICE: this is the Lean replacement for `List.nodup`; the proofs
    below use only those two facts, so the choice of removal order is
    immaterial.) -/
def core_nodup : List FinCore → List FinCore
  | [] => []
  | c :: cs =>
    let r := core_nodup cs
    if c ∈ r then r else c :: r

theorem mem_core_nodup (cs : List FinCore) : ∀ x : FinCore,
    x ∈ core_nodup cs ↔ x ∈ cs := by
  induction cs with
  | nil => intro x; rfl
  | cons c ds ih =>
    intro x
    show x ∈ (if c ∈ core_nodup ds then core_nodup ds else c :: core_nodup ds)
      ↔ x ∈ c :: ds
    by_cases h : c ∈ core_nodup ds
    · rw [ite_eq_left h]
      have hc : c ∈ ds := (ih c).mp h
      rw [ih]
      exact ⟨fun hx => List.mem_cons.mpr (Or.inr hx), fun hx =>
        (List.mem_cons.mp hx).elim (fun he => he ▸ hc) id⟩
    · rw [ite_eq_right h]
      simp only [List.mem_cons, ih]

theorem nodup_core_nodup (cs : List FinCore) : (core_nodup cs).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c ds ih =>
    show (if c ∈ core_nodup ds then core_nodup ds else c :: core_nodup ds).Nodup
    by_cases h : c ∈ core_nodup ds
    · rw [ite_eq_left h]; exact ih
    · rw [ite_eq_right h]; exact List.nodup_cons.mpr ⟨h, ih⟩

/-- LOWER, at the canonical list: the entries' cores with duplicates
    removed (`core_nodup`), each wrapped by `core_input`.  So the mass is
    not padding: some list the obligation quantifies over does weigh that
    much.

    Again, and it matters: the witness list is not claimed valid or
    rejected.  A task that wants to say its mass is attained BY THE FIRE
    SET has to exhibit rejected inputs itself; this says only that the
    arithmetic leaves no slack. -/
theorem finite_support_mass_lower_witness (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (finite_support entries Hnn).cd_mass ≤
        core_sum (finite_support entries Hnn).cd_weight l := by
  refine ⟨List.map core_input (core_nodup (List.map Prod.fst entries)), ?_, ?_⟩
  · rw [map_fin_core_core_input]
    exact nodup_core_nodup _
  · apply finite_support_mass_lower_on
    · exact nodup_core_nodup _
    · intro e He
      exact (mem_core_nodup _ _).mpr (List.mem_map.mpr ⟨e, He, rfl⟩)

/-- The two certificates together: the declared mass is exactly what some
    admissible list weighs.  `Rat.le_antisymm` on the pair — the equality
    is DERIVED from the two inequalities, never decided by computing on
    either side, which is the discipline `Measure`'s header sets out. -/
theorem finite_support_mass_exact (entries : List (FinCore × Rat))
    (Hnn : ∀ e, e ∈ entries → 0 ≤ e.2) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (finite_support entries Hnn).cd_weight l =
        (finite_support entries Hnn).cd_mass := by
  obtain ⟨l, Hnd, Hlow⟩ := finite_support_mass_lower_witness entries Hnn
  exact ⟨l, Hnd, Rat.le_antisymm (finite_support_bound entries Hnn l Hnd) Hlow⟩

/- =========================================================================
   Non-vacuity: the obligations really discharge
   ========================================================================= -/

/-- Two concrete cores, differing in standard input alone: the empty
    input, and the one-byte input "A".  Everything else empty — an empty
    argv and envp and an empty file system are not claimed valid (see
    `core_input`); these are two points of `FinInput.FinCore` to hang
    weights on, nothing more. -/
def example_core_empty : FinCore := FinCore.mkFinCore [] [] [] []

def example_core_a : FinCore :=
  FinCore.mkFinCore [] [] [] [BitVec.ofInt 8 65]

/-- The two cores are distinct, read off their standard input.  This is
    the fact every concrete weight computation below spends, and it is
    stated once because `Rat` values do not reduce in Lean's kernel (the
    rationals are normalised through a `gcd`), so the computations are
    done through the indicator lemmas rather than by `decide`. -/
theorem core_a_ne_empty : example_core_a ≠ example_core_empty := by
  intro h
  have hs := congrArg FinCore.core_stdin h
  simp [example_core_a, example_core_empty] at hs

/-- A two-entry support: half the mass on the empty input, a quarter on
    "A", for a declared total of three quarters. -/
def example_entries : List (FinCore × Rat) :=
  [(example_core_empty, (1 : Rat) / 2), (example_core_a, (1 : Rat) / 4)]

/-- The nonnegativity obligation, discharged entry by entry.  The
    boolean scan of `entries_nonneg_of_forallb` discharges it;
    that lemma is ported above, but its `rfl` obligation is a boolean
    EQUALITY of decided rational comparisons, which Lean's kernel cannot
    reduce (`Rat` addition is not definitional), so the concrete
    instantiations below are proved through the indicator lemmas and
    `grind` instead.  Nothing is weakened: this is the same proposition
    as the original statement, proved the way `Rat` allows. -/
theorem example_entries_nonneg : ∀ e, e ∈ example_entries → 0 ≤ e.2 := by
  intro e He
  simp only [example_entries, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl
  · show (0 : Rat) ≤ 1 / 2; grind
  · show (0 : Rat) ≤ 1 / 4; grind

def example_cd : CoreDistribution :=
  finite_support example_entries example_entries_nonneg

/-- THE POINT OF THE FILE, compiled: a `Measure.DISTRIBUTION` whose five
    components are all taken from the library, with no proof written
    here.  `w` is the lift, `M` is the declared mass, the two weight
    obligations are `cd_lift_nonneg` and `cd_lift_core_blind` applied to
    the distribution — the same two terms every distribution this library
    builds will use — and `M_nonneg` is `finite_support_mass_nonneg` at
    the entry list's own nonnegativity proof. -/
def example_D : DISTRIBUTION where
  w := cd_lift example_cd
  M := example_cd.cd_mass
  w_nonneg := cd_lift_nonneg example_cd
  M_nonneg := finite_support_mass_nonneg example_entries example_entries_nonneg
  w_core_blind := cd_lift_core_blind example_cd

/-- The example is not the ZERO distribution, which every obligation in
    sight would satisfy trivially and which would make the ascription
    above evidence of nothing: it puts at least a half on the record over
    the empty core. -/
theorem example_D_w_positive : 0 < example_D.w (core_input example_core_empty) := by
  show (0 : Rat) < core_indicator example_core_empty (1 / 2) example_core_empty +
    (core_indicator example_core_a (1 / 4) example_core_empty + 0)
  rw [core_indicator_hit, core_indicator_miss _ _ _ core_a_ne_empty]
  grind

/-- ... and its mass certificates are inhabited at that instance: the mass
    its two entries declare (a half plus a quarter) is attained by an
    admissible list.  This is `finite_support_mass_exact` at the example,
    quoted so that the generic certificate is seen to apply to something;
    the sum is written on `core_sum` of the core weight, which by
    `core_sum_cd_lift` is the sum `Measure.weight_bound_T` would take of
    `example_D.w`. -/
theorem example_D_mass_attained :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum example_cd.cd_weight l = example_cd.cd_mass :=
  finite_support_mass_exact example_entries example_entries_nonneg

/-- THE PER-SUBSET REFINEMENT BITES, which is the only way to see that it
    is a refinement and not a restatement.  Restricting `example_entries`
    to the empty core alone leaves a mass of a half, and the declared
    total is three quarters — a number the refined bound does NOT permit.

    Without the second conjunct the first would be consistent with the
    refinement being vacuous; together they say that a task whose fire set
    lies inside the empty core is held to half the mass, not to three
    quarters of it. -/
def example_is_empty_core (c : FinCore) : Bool :=
  decide (c = example_core_empty)

theorem example_is_empty_core_empty : example_is_empty_core example_core_empty = true := by
  unfold example_is_empty_core; simp

theorem example_is_empty_core_a : example_is_empty_core example_core_a = false := by
  unfold example_is_empty_core
  rw [decide_eq_false_iff_not]
  exact core_a_ne_empty

theorem example_filter_empty :
    List.filter (fun e => example_is_empty_core e.1) example_entries =
      [(example_core_empty, (1 : Rat) / 2)] := by
  unfold example_entries
  rw [List.filter_cons_of_pos (by simpa using example_is_empty_core_empty),
    List.filter_cons_of_neg (by rw [example_is_empty_core_a]; decide),
    List.filter_nil]

theorem entries_mass_example : entries_mass example_entries = (3 : Rat) / 4 := by
  show (1 : Rat) / 2 + ((1 : Rat) / 4 + 0) = 3 / 4
  grind

theorem finite_support_bound_subset_bites :
    entries_mass (entries_restrict example_is_empty_core example_entries) =
        (1 : Rat) / 2 ∧
      ¬ (entries_mass example_entries ≤ (1 : Rat) / 2) := by
  constructor
  · show entries_mass
      (List.filter (fun e => example_is_empty_core e.1) example_entries) = 1 / 2
    rw [example_filter_empty]
    show (1 : Rat) / 2 + 0 = 1 / 2
    grind
  · rw [entries_mass_example]
    grind

/- =========================================================================
   Non-vacuity: duplicate cores are SUMMED, and `List.NoDup` is load-bearing
   ========================================================================= -/

/-- An entry list that names one core TWICE — half and an eighth on the
    empty core, a quarter on "A" — so that the reading argued for at
    `entries_weight` is exercised by something instead of only asserted.

    The nonnegativity obligation is discharged inline here, at the
    definition site, which is the other of the two styles a task author
    writing a distribution will use. -/
def dup_entries : List (FinCore × Rat) :=
  [(example_core_empty, (1 : Rat) / 2), (example_core_a, (1 : Rat) / 4),
   (example_core_empty, (1 : Rat) / 8)]

theorem dup_entries_nonneg : ∀ e, e ∈ dup_entries → 0 ≤ e.2 := by
  intro e He
  simp only [dup_entries, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl
  · show (0 : Rat) ≤ 1 / 2; grind
  · show (0 : Rat) ≤ 1 / 4; grind
  · show (0 : Rat) ≤ 1 / 8; grind

def dup_cd : CoreDistribution :=
  finite_support dup_entries dup_entries_nonneg

/-- The bite: the repeated core weighs five eighths, the SUM of its two
    entries, and not the half a "first entry wins" reading would give
    it. -/
theorem dup_entries_weight_summed :
    entries_weight dup_entries example_core_empty = (5 : Rat) / 8 := by
  show core_indicator example_core_empty (1 / 2) example_core_empty +
    (core_indicator example_core_a (1 / 4) example_core_empty +
      (core_indicator example_core_empty (1 / 8) example_core_empty + 0)) = 5 / 8
  rw [core_indicator_hit, core_indicator_miss _ _ _ core_a_ne_empty,
    core_indicator_hit]
  grind

theorem dup_entries_weight_at_a :
    entries_weight dup_entries example_core_a = (1 : Rat) / 4 := by
  show core_indicator example_core_empty (1 / 2) example_core_a +
    (core_indicator example_core_a (1 / 4) example_core_a +
      (core_indicator example_core_empty (1 / 8) example_core_a + 0)) = 1 / 4
  rw [core_indicator_miss _ _ _ (Ne.symm core_a_ne_empty), core_indicator_hit,
    core_indicator_miss _ _ _ (Ne.symm core_a_ne_empty)]
  grind

/-- ... and the declared mass is still the flat total of the entries,
    seven eighths, which is the half of the story that makes the summing
    reading the only coherent one: a first-wins weight would total three
    quarters against a declared seven eighths, and no list could reach
    the declared mass. -/
theorem dup_entries_mass : entries_mass dup_entries = (7 : Rat) / 8 := by
  show (1 : Rat) / 2 + ((1 : Rat) / 4 + ((1 : Rat) / 8 + 0)) = 7 / 8
  grind

/-- The witness `finite_support_mass_lower_witness` builds for this entry
    list, written out.  `core_nodup` collapses the repeat, so it has two
    elements for three entries — and it still attains the declared seven
    eighths, which is exactly the claim
    `finite_support_mass_lower_witness` would fail on under a first-wins
    reading. -/
def dup_witness : List FinProcInput :=
  List.map core_input (core_nodup (List.map Prod.fst dup_entries))

theorem dup_witness_collapses_the_repeat : dup_witness.length = 2 := by
  decide

theorem core_nodup_dup :
    core_nodup (List.map Prod.fst dup_entries) =
      [example_core_a, example_core_empty] := by
  decide

theorem dup_witness_eq :
    dup_witness = [core_input example_core_a, core_input example_core_empty] := by
  unfold dup_witness
  rw [core_nodup_dup]
  rfl

theorem dup_witness_attains_mass :
    core_sum dup_cd.cd_weight dup_witness = dup_cd.cd_mass := by
  show core_sum (entries_weight dup_entries) dup_witness = entries_mass dup_entries
  rw [dup_witness_eq, core_sum_cons, core_sum_cons, core_sum_nil,
    fin_core_core_input, fin_core_core_input,
    dup_entries_weight_at_a, dup_entries_weight_summed, dup_entries_mass]
  grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING, and this is the
    combinator-level counterpart of `Measure.weight_bound_refutable`:
    without duplicate-freedom of the CORES, `finite_support_bound` is
    simply false.  Offer the same core twice — two records, so the list is
    `List.NoDup` as a list of RECORDS — and the sum is five quarters
    against a declared mass of seven eighths.

    Both conjuncts are needed to make the point.  The second says the
    bound really would fail on this list; the first says the list is
    excluded, and names what excludes it. -/
theorem finite_support_bound_needs_nodup :
    ¬ (List.map fin_core
        [core_input example_core_empty, core_input example_core_empty]).Nodup ∧
      ¬ (core_sum dup_cd.cd_weight
          [core_input example_core_empty, core_input example_core_empty]
          ≤ dup_cd.cd_mass) := by
  constructor
  · rw [List.map_cons, List.map_cons, List.map_nil, fin_core_core_input]
    simp
  · show ¬ (core_sum (entries_weight dup_entries)
        [core_input example_core_empty, core_input example_core_empty] ≤
          entries_mass dup_entries)
    rw [core_sum_cons, core_sum_cons, core_sum_nil, fin_core_core_input,
      dup_entries_weight_summed, dup_entries_mass]
    grind

/- =========================================================================
   Non-vacuity, the other way: a negative entry admits no distribution
   ========================================================================= -/

/-- A rigged entry list: one core, weight minus one.  Nothing stops an
    author WRITING this list — it is a perfectly good
    `list (FinCore * Q)` — and the two lemmas below are what stops it
    becoming a `CoreDistribution`. -/
def negative_entries : List (FinCore × Rat) :=
  [(example_core_empty, (-1 : Rat))]

/-- The constructor's obligation is unsatisfiable for it: the weight it
    assigns to the rigged core is minus one, and no proof of
    nonnegativity exists. -/
theorem negative_entries_no_nonneg_weight :
    ¬ (∀ c, 0 ≤ entries_weight negative_entries c) := by
  intro Hnn
  have h := Hnn example_core_empty
  have hc : entries_weight negative_entries example_core_empty = (-1 : Rat) := by
    show core_indicator example_core_empty (-1) example_core_empty + 0 = -1
    rw [core_indicator_hit]
    grind
  rw [hc] at h
  grind

/-- So no `CoreDistribution` whatever weighs cores that way — not just
    none built by `finite_support`, and not just none whose weight is that
    exact function: none whose weight so much as AGREES with it pointwise.
    The `cd_nonneg` FIELD is what refutes it, and that is the argument for
    making nonnegativity a field: the impossibility becomes a property of
    the record rather than of one combinator's typing. -/
theorem negative_entries_no_core_distribution (D : CoreDistribution) :
    ¬ (∀ c, D.cd_weight c = entries_weight negative_entries c) := by
  intro Hagree
  apply negative_entries_no_nonneg_weight
  intro c
  rw [← Hagree c]
  exact D.cd_nonneg c

/- =========================================================================
   Enumerating the bytes, and the byte lists of a given length
   ========================================================================= -/

/-- All 256 bytes, as a list.  Nothing here is about measures, and it
    would rather live in `BvBase`, next to `BvBase.byte`: if `BvBase`
    grows an
    enumeration of `BvBase.byte`, delete this one and use it.  It is
    written as `Z_to_bv` over `List.seq` rather than spelled out because
    the three facts wanted of it — its length, that it misses nothing, and
    that it repeats nothing — are then three short arguments about
    `List.seq` instead of a 256-line literal and a computation to check
    it. -/
def all_bytes : List (BitVec 8) :=
  List.map (fun n => BitVec.ofInt 8 (Int.ofNat n)) (List.range 256)

theorem all_bytes_length : all_bytes.length = 256 := by
  unfold all_bytes
  rw [List.length_map, List.length_range]

/-- It misses nothing.  A `BvBase.byte` is a `bv 8`, whose `bv_unsigned`
    lies in `[0, bv_modulus 8)` — that modulus being 256 by conversion —
    so the byte is `Z_to_bv 8` of a number `List.seq 0 256` enumerates,
    and `Z_to_bv_bv_unsigned` is the round trip that says so. -/
theorem all_bytes_complete (b : BitVec 8) : b ∈ all_bytes := by
  unfold all_bytes
  rw [List.mem_map]
  refine ⟨b.toNat, ?_, ?_⟩
  · rw [List.mem_range]; have := b.isLt; omega
  · show BitVec.ofInt 8 (Int.ofNat b.toNat) = b
    rw [show BitVec.ofInt 8 (Int.ofNat b.toNat) = BitVec.ofNat 8 b.toNat from
      BitVec.ofInt_natCast 8 b.toNat]
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- Mapping an injective function over a duplicate-free list leaves it
    duplicate-free.  `Stdlib` ships `List.NoDup_map_inv`, which is the
    other direction; this one is what a list built by `List.map` needs.
    Injectivity is asked for only ON THE LIST, which is what makes it
    usable for `Z_to_bv 8 (Z.of_nat _)` — a function injective on
    `[0, 256)` and on nothing wider. -/
theorem NoDup_map_inj {A B : Type} (f : A → B) (l : List A)
    (Hinj : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) (Hnd : l.Nodup) :
    (List.map f l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    rw [List.map_cons, List.nodup_cons]
    obtain ⟨hx, hnd⟩ := List.nodup_cons.mp Hnd
    refine ⟨?_, ih (fun y z Hy Hz => Hinj y z (List.mem_cons_of_mem _ Hy)
      (List.mem_cons_of_mem _ Hz)) hnd⟩
    intro hmem
    obtain ⟨y, Hy, Hfy⟩ := List.mem_map.mp hmem
    have hxy : x = y := Hinj x y (List.mem_cons_self ..) (List.mem_cons_of_mem _ Hy)
      (by rw [Hfy])
    rw [← hxy] at Hy
    exact hx Hy

/-- ... and it repeats nothing: below 256 the round trip through
    `bv_unsigned` is the identity, so the map is injective on
    `List.seq 0 256`, which `List.seq_NoDup` hands over
    duplicate-free. -/
theorem all_bytes_nodup : all_bytes.Nodup := by
  unfold all_bytes
  apply NoDup_map_inj
  · intro x y hx hy heq
    rw [List.mem_range] at hx hy
    have h2 : BitVec.ofNat 8 x = BitVec.ofNat 8 y := by
      rw [← BitVec.ofInt_natCast 8 x, ← BitVec.ofInt_natCast 8 y]
      exact heq
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : x < 2 ^ 8),
      Nat.mod_eq_of_lt (by omega : y < 2 ^ 8)] at h3
    exact h3
  · exact List.nodup_range

/-- Every byte list of length `n`, as a list of `256 ^ n` of them.  This
    is the object the counting lemma counts against: an explicit finite
    enumeration, so that "there are at most `256 ^ n` of these" is a
    length bound against a list whose length is known, rather than a
    cardinality argument about a type. -/
def byte_lists : Nat → List (List (BitVec 8))
  | 0 => [[]]
  | n + 1 => all_bytes.flatMap (fun b => (byte_lists n).map (fun l => b :: l))

/-- The length of a `List.flat_map` whose blocks all have the same size.
    `Stdlib` has `List.length_concat` over a sum of lengths; when every
    block is the same size the sum is a product, and that is the shape
    `byte_lists` produces. -/
theorem length_flat_map_const {A B : Type} (f : A → List B) (l : List A)
    (c : Nat) (Hc : ∀ x, x ∈ l → (f x).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, Hc x (List.mem_cons_self ..),
      ih (fun y Hy => Hc y (List.mem_cons_of_mem _ Hy))]
    grind

theorem byte_lists_length : ∀ n, (byte_lists n).length = 256 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (all_bytes.flatMap (fun b => (byte_lists n).map (fun l => b :: l))).length
      = 256 ^ (n + 1)
    rw [length_flat_map_const (f := fun b => (byte_lists n).map (fun l => b :: l))
      (c := 256 ^ n) (Hc := fun b _ => by rw [List.length_map]; exact ih)]
    rw [all_bytes_length, Nat.pow_succ, Nat.mul_comm]

/-- ... and none is missing.  Stated at `length l` rather than at an
    arbitrary `n` equal to it, so that the induction on `l` needs no
    generalization; the `n`-shaped form is one `subst` away and is taken
    at the single use site. -/
theorem byte_lists_complete : ∀ l : List (BitVec 8),
    l ∈ byte_lists l.length := by
  intro l
  induction l with
  | nil => exact List.mem_cons_self ..
  | cons b l ih =>
    rw [List.length_cons]
    show b :: l ∈ all_bytes.flatMap (fun b => (byte_lists l.length).map (fun l' => b :: l'))
    rw [List.mem_flatMap]
    exact ⟨b, all_bytes_complete b, List.mem_map.mpr ⟨l, ih, rfl⟩⟩

/-- ... and nothing longer or shorter has crept in: the enumeration at `n`
    holds only length-`n` lists.  Needed because a witness list BUILT from
    `byte_lists n` has to satisfy the counting lemma's own length
    hypothesis, and that hypothesis is about its members. -/
theorem byte_lists_In_length : ∀ (n : Nat) (s : List (BitVec 8)),
    s ∈ byte_lists n → s.length = n := by
  intro n
  induction n with
  | zero =>
    intro s Hs
    rw [show byte_lists 0 = [[]] from rfl] at Hs
    rw [List.mem_cons] at Hs
    rcases Hs with h | h
    · rw [h]; rfl
    · exact absurd h (List.not_mem_nil)
  | succ n ih =>
    intro s Hs
    change s ∈ all_bytes.flatMap (fun b => (byte_lists n).map (fun l => b :: l)) at Hs
    rw [List.mem_flatMap] at Hs
    obtain ⟨b, _, Hs⟩ := Hs
    obtain ⟨s', Hs', rfl⟩ := List.mem_map.mp Hs
    rw [List.length_cons, ih s' Hs']

/-- `List.NoDup` through a `List.flat_map`.  `Stdlib` ships nothing for
    this — `List.NoDup_app` is as far as it goes — so the three conditions
    are spelled out: the index list is duplicate-free, each block is, and
    no element lands in two blocks.  The third is what the second and
    third arguments of `List.NoDup_app` need at each step, and it is the
    one a caller has to think about. -/
theorem NoDup_flat_map {A B : Type} (f : A → List B) (l : List A)
    (Hnd : l.Nodup) (Hblk : ∀ x, x ∈ l → (f x).Nodup)
    (Hdisj : ∀ x y b, x ∈ l → y ∈ l → b ∈ f x → b ∈ f y → x = y) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨hx, hnd⟩ := List.nodup_cons.mp Hnd
    refine ⟨Hblk x (List.mem_cons_self ..), ?_, ?_⟩
    · exact ih hnd (fun y Hy => Hblk y (List.mem_cons_of_mem _ Hy))
        (fun y z b Hy Hz => Hdisj y z b (List.mem_cons_of_mem _ Hy)
          (List.mem_cons_of_mem _ Hz))
    · intro a Ha b Hb
      intro hab
      obtain ⟨y, Hy, Hby⟩ := List.mem_flatMap.mp Hb
      rw [← hab] at Hby
      have hxy : x = y := Hdisj x y a (List.mem_cons_self ..)
        (List.mem_cons_of_mem _ Hy) Ha Hby
      rw [← hxy] at Hy
      exact hx Hy

/-- ... and the enumeration repeats nothing.  Distinct first bytes give
    disjoint blocks — that is the whole content of the third condition
    here — and within a block the induction hypothesis carries over
    through `cons`, which is injective.

    This is what a witness list of the FULL size `256 ^ n` needs, and it
    is the only thing that was missing: the attained half of the counting
    lemma is proved at every `n` with it and could not be proved at any
    `n` but the trivial ones without it. -/
theorem byte_lists_nodup : ∀ n, (byte_lists n).Nodup := by
  intro n
  induction n with
  | zero => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ n ih =>
    show (all_bytes.flatMap (fun b => (byte_lists n).map (fun l => b :: l))).Nodup
    apply NoDup_flat_map
    · exact all_bytes_nodup
    · intro b _
      apply NoDup_map_inj (f := fun l => b :: l)
      · intro x y _ _ heq
        exact (List.cons.inj heq).2
      · exact ih
    · intro x y bs _ _ Hx Hy
      obtain ⟨lx, Hlx, rfl⟩ := List.mem_map.mp Hx
      obtain ⟨ly, Hly, Hxy⟩ := List.mem_map.mp Hy
      exact (List.cons.inj Hxy).1.symm

/- =========================================================================
   Positivity, removal, and the monotonicity the cylinder bound runs on
   ========================================================================= -/

/-- A POSITIVE sum has a positive member, which is the direction a
    non-vacuity argument needs, the companion of `qsum_nonneg`.  A lemma
    of the shape "some admissible list weighs at least `1 - eps`" is
    worth exactly as much as the reasons a list could have for satisfying
    it, so the certificates below are followed by pins that read a
    positive WEIGHT back out of a positive SUM — the empty list and every
    list of cores the distribution weighs zero are then excluded by the
    statement itself rather than by a reader's confidence.

    Constructive, and the decision is at one core at a time: either the
    head weighs something, or it weighs zero — its weight is nonnegative
    and not positive — and the tail carries the whole sum. -/
theorem qsum_positive_member {A : Type} (w : A → Rat) (cs : List A)
    (Hw : ∀ c, 0 ≤ w c) (Hpos : 0 < qsum w cs) :
    ∃ c, c ∈ cs ∧ 0 < w c := by
  induction cs with
  | nil => rw [qsum_nil] at Hpos; exact absurd Hpos Rat.lt_irrefl
  | cons c cs ih =>
    rw [qsum_cons] at Hpos
    by_cases Hc : 0 < w c
    · exact ⟨c, List.mem_cons_self .., Hc⟩
    · have Hz : w c = 0 := Rat.le_antisymm (Rat.not_lt.mp Hc) (Hw c)
      have Hrest : 0 < qsum w cs := by rw [Hz] at Hpos; grind
      obtain ⟨c', Hin, Hc'⟩ := ih Hrest
      exact ⟨c', List.mem_cons_of_mem _ Hin, Hc'⟩

/-- Removing ONE occurrence of a core from a list.  `List.remove` removes
    every occurrence, and that difference is the whole point: the sum
    lemma below is then an exact equality with NO duplicate-freedom
    hypothesis on the list, which is what lets `qsum_core_incl_le` bound a
    sum by a sum over a list nobody has proved duplicate-free. -/
def core_remove_one (c : FinCore) : List FinCore → List FinCore
  | [] => []
  | x :: rest => if c = x then rest else x :: core_remove_one c rest

theorem qsum_core_remove_one (w : FinCore → Rat) (c : FinCore)
    (cs : List FinCore) (Hin : c ∈ cs) :
    qsum w cs = w c + qsum w (core_remove_one c cs) := by
  induction cs with
  | nil => cases Hin
  | cons x cs ih =>
    rw [show core_remove_one c (x :: cs) =
      (if c = x then cs else x :: core_remove_one c cs) from rfl]
    by_cases Heq : c = x
    · rw [ite_eq_left Heq, qsum_cons, Heq]
    · rw [ite_eq_right Heq, qsum_cons, qsum_cons]
      rcases List.mem_cons.mp Hin with h | h
      · exact absurd h Heq
      · rw [ih h]
        grind

/-- Everything else survives the removal. -/
theorem In_core_remove_one (c x : FinCore) (cs : List FinCore)
    (Hin : x ∈ cs) (Hne : x ≠ c) : x ∈ core_remove_one c cs := by
  induction cs with
  | nil => cases Hin
  | cons y cs ih =>
    rw [show core_remove_one c (y :: cs) =
      (if c = y then cs else y :: core_remove_one c cs) from rfl]
    by_cases Heq : c = y
    · rw [ite_eq_left Heq]
      rcases List.mem_cons.mp Hin with h | h
      · exact absurd (h.trans Heq.symm) Hne
      · exact h
    · rw [ite_eq_right Heq]
      rcases List.mem_cons.mp Hin with h | h
      · rw [h]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- THE MONOTONICITY THE CYLINDER BOUND RUNS ON: a duplicate-free list of
    cores sums to at most what any list containing it sums to.

    The induction peels the head `c`, removes one occurrence of it from
    the containing list, and recurses; duplicate-freedom of the SMALL list
    is what makes the tail still included in the remainder, and it is the
    only place the hypothesis is used.  Nothing is asked of the containing
    list — it may repeat, and each repeat only makes its sum larger, which
    is why `cyl_enum` below is never proved `List.NoDup`.

    Nonnegativity of the weight is genuinely needed and not decoration:
    the empty list already refutes the statement without it. -/
theorem qsum_core_incl_le (w : FinCore → Rat) (cs : List FinCore) :
    ∀ ys : List FinCore, (∀ c, 0 ≤ w c) → cs.Nodup → cs ⊆ ys →
      qsum w cs ≤ qsum w ys := by
  induction cs with
  | nil =>
    intro ys Hw _ _
    rw [qsum_nil]
    exact qsum_nonneg w ys (fun c _ => Hw c)
  | cons c cs ih =>
    intro ys Hw Hnd Hincl
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp Hnd
    have Hc : c ∈ ys := Hincl (List.mem_cons_self ..)
    rw [qsum_core_remove_one w c ys Hc, qsum_cons]
    refine Qplus_le_compat (Rat.le_refl) ?_
    exact ih (core_remove_one c ys) Hw hnd (fun x hx =>
      In_core_remove_one c x ys (Hincl (List.mem_cons_of_mem _ hx))
        (fun h => hnot (h ▸ hx)))

/-- A `List.flat_map` of uniformly bounded blocks is bounded by the count
    of blocks times the bound.  This is the step that turns "each of the
    256 continuations carries at most `m`" into "the 256 of them carry at
    most `256 * m`". -/
theorem qsum_flat_map_const_le {A B : Type} (w : B → Rat) (f : A → List B)
    (l : List A) (C : Rat) (Hb : ∀ x, x ∈ l → qsum w (f x) ≤ C) :
    qsum w (l.flatMap f) ≤ Qnat l.length * C := by
  induction l with
  | nil =>
    rw [List.flatMap_nil, qsum_nil]
    show (0 : Rat) ≤ Qnat 0 * C
    rw [Qnat_0]; grind
  | cons x l ih =>
    rw [List.flatMap_cons, qsum_app, List.length_cons, Qnat_succ]
    refine Rat.le_trans (Qplus_le_compat (Hb x (List.mem_cons_self ..))
      (ih (fun y Hy => Hb y (List.mem_cons_of_mem _ Hy)))) ?_
    grind

/-- A list on which the weight is constant sums to the count times the
    constant — the other half of the length-slice bound, where the
    counting lemma supplies the count. -/
theorem qsum_const {A : Type} (w : A → Rat) (cs : List A) (C : Rat)
    (Hc : ∀ c, c ∈ cs → w c = C) : qsum w cs = Qnat cs.length * C := by
  induction cs with
  | nil =>
    show (0 : Rat) = Qnat 0 * C
    rw [Qnat_0]; grind
  | cons c cs ih =>
    rw [qsum_cons, Hc c (List.mem_cons_self ..),
      ih (fun x hx => Hc x (List.mem_cons_of_mem _ hx)), List.length_cons, Qnat_succ]
    grind

/-- Elements the weight ignores can be dropped.  Together with
    `List.Nodup.filter` this is what lets a bound proved for lists INSIDE
    a region be applied to a list that merely happens to weigh zero
    outside it — the step from the cylinder bound to the whole-space
    certificate. -/
theorem qsum_filter {A : Type} (w : A → Rat) (P : A → Bool) (cs : List A)
    (Hz : ∀ c, P c = false → w c = 0) :
    qsum w cs = qsum w (List.filter P cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.filter_cons]
    split
    · next _ => rw [qsum_cons, qsum_cons, ih]
    · next h =>
      have hf : P c = false := by cases hpc : P c <;> simp_all
      rw [qsum_cons, Hz c hf, ih]; grind

/-- The maximum of a list of naturals.  `Stdlib` does not ship
    `List.list_max`, which is used here to read the depth
    of a task's own list off it; this is that function, and
    `list_max_ge` is the only fact this file asks of it. -/
def list_max : List Nat → Nat
  | [] => 0
  | n :: l => max n (list_max l)

/-- `List.list_max` bounds every member.  `Stdlib` states the equivalence
    `List.list_max_le` and not this consequence of it. -/
theorem list_max_ge (l : List Nat) (n : Nat) (Hin : n ∈ l) : n ≤ list_max l := by
  induction l with
  | nil => cases Hin
  | cons m l ih =>
    rw [list_max]
    rcases List.mem_cons.mp Hin with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

/- =========================================================================
   THE COUNTING LEMMA
   ========================================================================= -/

/-- A list contained in another, and duplicate-free, is no longer.  This
    is `List.NoDup_incl_length`, which `Stdlib` does not ship:
    the induction peels the head, splits the containing list at its first
    occurrence, and recurses on the remainder — the head's absence from
    the tail (that is where `List.NoDup` is spent) puts the tail inside
    the split remainder. -/
theorem nodup_subset_length {α : Type} (l ys : List α) (Hnd : l.Nodup)
    (Hsub : l ⊆ ys) : l.length ≤ ys.length := by
  induction l generalizing ys with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp Hnd
    have ha : a ∈ ys := Hsub (List.mem_cons_self ..)
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
    rw [List.length_cons, List.length_append, List.length_cons]
    have hsub' : l ⊆ s ++ t := by
      intro x hx
      have hxys : x ∈ s ++ a :: t := Hsub (List.mem_cons_of_mem _ hx)
      rcases List.mem_append.mp hxys with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd hx hnot
        · exact List.mem_append.mpr (Or.inr h)
    have := ih (s ++ t) hnd hsub'
    rw [List.length_append] at this
    omega

/-- A list of records with duplicate-free CORES, every core matching fixed
    argv, envp and file system and carrying standard input of length
    exactly `n`, has at most `256 ^ n` elements.

    This is the fact the geometric distribution's bounds are built out of,
    and the reason it can be stated at all is the quotient:
    `Measure.weight_bound_T` reads duplicate-freedom on
    `FinInput.fin_core`, so the list's records inject into their cores,
    and a core matching the fixed environment is determined by its
    standard input alone.  Length-`n` byte lists are enumerated by
    `byte_lists n`, there are `256 ^ n` of them, and
    `nodup_subset_length` converts the injection into the bound.

    The environment hypothesis is written as a single equation —
    `fin_core f = mkFinCore argv envp fs (fin_stdin f)` — rather than as
    three field equations, because that is the form the injection
    consumes directly and the form `geo_weight` below decides on.

    Read the hypothesis as: the list is a duplicate-free sample from ONE
    length slice of ONE launch-time environment.  Nothing is claimed about
    lists that mix slices; that is what `stdin_geometric_bound` is for,
    and it is proved a different way. -/
theorem injective_core_list_in_cylinder_length_bound
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (n : Nat)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧
        f.fin_stdin.length = n) :
    l.length ≤ 256 ^ n := by
  have Hle : (List.map fin_core l).length ≤
      (List.map (fun s => FinCore.mkFinCore argv envp fs s) (byte_lists n)).length := by
    apply nodup_subset_length
    · exact Hnd
    · intro c Hc
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      obtain ⟨Henv, Hlen⟩ := Hall f Hf
      rw [List.mem_map]
      refine ⟨f.fin_stdin, ?_, ?_⟩
      · rw [← Hlen]; exact byte_lists_complete f.fin_stdin
      · rw [← Henv]
  rwa [List.length_map, List.length_map, byte_lists_length] at Hle

/-- THE BOUND IS ATTAINED AT EVERY `n`, so `256 ^ n` is the right constant
    and not merely a true one: over any launch-time environment at all
    there is an admissible list of exactly `256 ^ n` records, one per
    length-`n` standard input.

    It is `byte_lists n` wrapped by `core_input`, and the proof is
    symbolic throughout — `byte_lists_length` for the count,
    `byte_lists_nodup` through `NoDup_map_inj` for the duplicate freedom,
    `byte_lists_In_length` for the length hypothesis.  NOTHING IS EVER
    COMPUTED: `byte_lists n` stays a `List.flat_map` term, so the witness
    at `n = 2` costs exactly what the witness at `n = 1` costs, which is
    nothing. -/
theorem injective_core_list_in_cylinder_length_bound_attained
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧
          f.fin_stdin.length = n) ∧
      l.length = 256 ^ n := by
  refine ⟨List.map (fun s => core_input (FinCore.mkFinCore argv envp fs s))
    (byte_lists n), ?_, ?_, ?_⟩
  · rw [List.map_map]
    show (List.map (fun s => fin_core (core_input (FinCore.mkFinCore argv envp fs s)))
      (byte_lists n)).Nodup
    have hfun : (fun s => fin_core (core_input (FinCore.mkFinCore argv envp fs s))) =
        (fun s => FinCore.mkFinCore argv envp fs s) := by
      funext s; exact fin_core_core_input _
    rw [hfun]
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact congrArg FinCore.core_stdin Heq
    · exact byte_lists_nodup n
  · intro f Hf
    obtain ⟨s, Hs, rfl⟩ := List.mem_map.mp Hf
    refine ⟨?_, ?_⟩
    · rw [fin_core_core_input]
      rfl
    · show s.length = n
      exact byte_lists_In_length n s Hs
  · rw [List.length_map, byte_lists_length]

/- =========================================================================
   Combinator: geometric standard input over a fixed environment
   ========================================================================= -/

/-- The mass of the cylinder over a prefix of length `n`, and the weight of
    a single core whose standard input has length `n`.  Both are powers of
    ONE ratio, `(1 - p_stop) * (1 # 256)`: stopping costs a factor
    `p_stop`, continuing costs `1 - p_stop` and choosing the next byte
    costs `1 # 256`.  The plan's three-factor form is recovered below by
    `Qpow_mult` and is a lemma rather than a rival definition — see the
    header. -/
def geo_mass (p : Rat) (n : Nat) : Rat := Qpow ((1 - p) * (1 / 256)) n

def geo_point (p : Rat) (n : Nat) : Rat := p * geo_mass p n

theorem geo_mass_closed_form (p : Rat) (n : Nat) :
    geo_mass p n = Qpow (1 - p) n * Qpow (1 / 256) n :=
  Qpow_mult (1 - p) (1 / 256) n

theorem geo_point_closed_form (p : Rat) (n : Nat) :
    geo_point p n = p * Qpow (1 - p) n * Qpow (1 / 256) n := by
  unfold geo_point
  rw [geo_mass_closed_form]
  grind

/-- The ratio is nonnegative exactly when `p_stop <= 1`, which is where the
    second side condition comes from and the only thing it is for. -/
theorem geo_ratio_nonneg (p : Rat) (Hp1 : p ≤ 1) :
    0 ≤ (1 - p) * (1 / 256) :=
  Rat.mul_nonneg (by grind) (by
    show (0 : Rat) ≤ 1 / 256
    grind)

theorem geo_mass_nonneg (p : Rat) (n : Nat) (Hp1 : p ≤ 1) : 0 ≤ geo_mass p n :=
  Qpow_nonneg _ n (geo_ratio_nonneg p Hp1)

theorem geo_point_nonneg (p : Rat) (n : Nat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 ≤ geo_point p n :=
  Rat.mul_nonneg Hp0 (geo_mass_nonneg p n Hp1)

/-- A single core weighs at most the mass of the cylinder it sits at the
    tip of, because `p_stop <= 1`.  This is the base case of the cylinder
    induction: a cylinder with no room to continue holds only its own
    stopping core. -/
theorem geo_point_le_mass (p : Rat) (n : Nat) (Hp1 : p ≤ 1) :
    geo_point p n ≤ geo_mass p n := by
  unfold geo_point
  have h := Rat.mul_le_mul_of_nonneg_right Hp1 (geo_mass_nonneg p n Hp1)
  rwa [Rat.one_mul] at h

/-- THE WEIGHT.  Zero unless the core's argv, envp and file system are the
    fixed ones; otherwise the geometric weight of its standard-input
    length.

    The environment test is one decidable equation, "the core is the
    template with its own standard input plugged in", rather than three
    field tests conjoined.  That is not brevity: the three-way version
    would need a decision over a conjunction, and this version is exactly
    the hypothesis the counting lemma above already carries, so no
    translation step stands between them. -/
def geo_weight (p : Rat) (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) : Rat :=
  if c = FinCore.mkFinCore argv envp fs c.core_stdin
  then geo_point p c.core_stdin.length
  else 0

/-- Its two values, as rewrite rules, so that no proof below names the
    decision instance. -/
theorem geo_weight_match (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (s : List (BitVec 8)) :
    geo_weight p argv envp fs (FinCore.mkFinCore argv envp fs s) =
      geo_point p s.length := by
  unfold geo_weight
  rw [ite_eq_left rfl]

theorem geo_weight_mismatch (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (c : FinCore)
    (Hne : c ≠ FinCore.mkFinCore argv envp fs c.core_stdin) :
    geo_weight p argv envp fs c = 0 := by
  unfold geo_weight
  rw [ite_eq_right Hne]

theorem geo_weight_nonneg (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    0 ≤ geo_weight p argv envp fs c := by
  unfold geo_weight
  split
  · next _ => exact geo_point_nonneg p _ Hp0 Hp1
  · next _ => exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, exactly as `Measure`'s header
    says every `M` is — nothing is proved by writing it, and
    `stdin_geometric_mass_upper` below is the proof that owes something to
    it.  The two side conditions are arguments for the same reason
    `finite_support`'s nonnegativity proof is: `cd_nonneg` is a field, and
    a constructor that returned one without a proof would have to invent
    it.  See the header for why `0 < p_stop` is NOT among them. -/
def stdin_geometric (p : Rat) (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution where
  cd_weight := geo_weight p argv envp fs
  cd_mass := 1
  cd_nonneg := geo_weight_nonneg p argv envp fs Hp0 Hp1

/-- `Measure.DISTRIBUTION`'s `M_nonneg` here is `0 <= 1` on the numeral the
    constructor writes.  It is stated rather than left to the caller so
    that a distribution assembled from combinators can discharge the
    obligation without any arithmetic at the site. -/
theorem stdin_geometric_mass_nonneg (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    0 ≤ (stdin_geometric p argv envp fs Hp0 Hp1).cd_mass := by
  show (0 : Rat) ≤ 1
  decide

/- =========================================================================
   The prefix cylinder, and the enumeration that bounds it
   ========================================================================= -/

/-- The cores this bound is about: the fixed environment, and standard
    input EXTENDING `bs`.  One existential rather than a conjunction of an
    environment test and a prefix test, for the same reason `geo_weight`'s
    test is one equation — it is the form both the construction and the
    enumeration want. -/
def in_stdin_cylinder (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ ext, c = FinCore.mkFinCore argv envp fs (bs ++ ext)

/-- Every core in the cylinder over `bs` whose standard input exceeds `bs`
    by at most `N` bytes, as a list: the stopping core, then for each byte
    the enumeration of the cylinder one byte deeper.  It recurses on `N`,
    which is what makes it a `Fixpoint` at all — `bs` grows.

    Duplicate-freedom of this list is never proved and never needed:
    `qsum_core_incl_le` asks nothing of the list it bounds against. -/
def cyl_enum (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (bs : List (BitVec 8)) : Nat → List FinCore
  | 0 => [FinCore.mkFinCore argv envp fs bs]
  | N + 1 => FinCore.mkFinCore argv envp fs bs ::
      all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N)

/-- It misses nothing within its depth. -/
theorem cyl_enum_complete (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) :
    ∀ (N : Nat) (bs ext : List (BitVec 8)), ext.length ≤ N →
      FinCore.mkFinCore argv envp fs (bs ++ ext) ∈ cyl_enum argv envp fs bs N := by
  intro N
  induction N with
  | zero =>
    intro bs ext Hlen
    cases ext with
    | nil => rw [List.append_nil]; exact List.mem_cons_self ..
    | cons b ext => simp at Hlen
  | succ N ih =>
    intro bs ext Hlen
    cases ext with
    | nil => rw [List.append_nil]; exact List.mem_cons_self ..
    | cons b ext =>
      show FinCore.mkFinCore argv envp fs (bs ++ b :: ext) ∈
        FinCore.mkFinCore argv envp fs bs ::
          all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N)
      rw [List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨b, all_bytes_complete b, ?_⟩
      have hsplit : bs ++ b :: ext = (bs ++ [b]) ++ ext := by
        rw [List.append_assoc]; rfl
      rw [hsplit]
      apply ih
      simp only [List.length_cons] at Hlen ⊢
      omega

/-- THE CANCELLATION, by induction on the depth: the whole enumeration
    weighs no more than the cylinder mass, at every depth and every
    prefix.

    The step is exact rather than lossy, which is why the constant below
    is the right one.  The stopping core contributes `p_stop * m`, where
    `m` is the cylinder's mass; each of the 256 continuations contributes
    at most the mass of a cylinder one byte deeper, which is
    `(1 - p_stop) * (1/256) * m`; and
    `p_stop + 256 * (1 - p_stop) * (1/256)` is `1` exactly.

    The base case is the one place `p_stop <= 1` is spent for anything
    other than nonnegativity: a depth-zero cylinder holds only its
    stopping core, which weighs `p_stop * m` and must be under `m`. -/
theorem cyl_enum_sum_le (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (_Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    ∀ (N : Nat) (bs : List (BitVec 8)),
      qsum (geo_weight p argv envp fs) (cyl_enum argv envp fs bs N) ≤
        geo_mass p bs.length := by
  intro N
  induction N with
  | zero =>
    intro bs
    show qsum (geo_weight p argv envp fs)
      [FinCore.mkFinCore argv envp fs bs] ≤ geo_mass p bs.length
    rw [qsum_cons, qsum_nil, geo_weight_match]
    have h := geo_point_le_mass p bs.length Hp1
    grind
  | succ N ih =>
    intro bs
    show qsum (geo_weight p argv envp fs)
      (FinCore.mkFinCore argv envp fs bs ::
        all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N)) ≤
      geo_mass p bs.length
    rw [qsum_cons, geo_weight_match]
    have hflat : qsum (geo_weight p argv envp fs)
        (all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N)) ≤
        Qnat all_bytes.length * geo_mass p (bs.length + 1) := by
      refine qsum_flat_map_const_le (geo_weight p argv envp fs)
        (fun b => cyl_enum argv envp fs (bs ++ [b]) N) all_bytes
        (geo_mass p (bs.length + 1)) (fun b _ => ?_)
      refine Rat.le_trans (ih (bs ++ [b])) ?_
      rw [List.length_append, List.length_cons, List.length_nil]
      grind
    refine Rat.le_trans (b := geo_point p bs.length +
        Qnat all_bytes.length * geo_mass p (bs.length + 1))
      (Qplus_le_compat
        (Rat.le_refl : geo_point p bs.length ≤ geo_point p bs.length) hflat) ?_
    rw [all_bytes_length, Qnat_256]
    show geo_point p bs.length + (256 : Rat) * geo_mass p (bs.length + 1) ≤
      geo_mass p bs.length
    unfold geo_point geo_mass
    rw [Qpow_succ]
    grind

/-- The bound over CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    The depth to enumerate to is read off the list — the largest
    standard-input length occurring in it — which is where the finiteness
    of `Measure.weight_bound_T`'s lists is spent, and the only place it is
    needed.  A core whose standard input is `bs ++ ext` has length at
    least that of `ext`, so bounding the lengths bounds the depths. -/
theorem geo_weight_cylinder_bound (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_stdin_cylinder argv envp fs bs c) :
    qsum (geo_weight p argv envp fs) cs ≤ geo_mass p bs.length := by
  refine Rat.le_trans (qsum_core_incl_le (geo_weight p argv envp fs) cs
    (cyl_enum argv envp fs bs
      (list_max (List.map (fun c => c.core_stdin.length) cs)))
    (geo_weight_nonneg p argv envp fs Hp0 Hp1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨ext, rfl⟩ := Hcyl c Hc
    apply cyl_enum_complete
    have Hin : (FinCore.mkFinCore argv envp fs (bs ++ ext)).core_stdin.length ∈
        List.map (fun c => c.core_stdin.length) cs :=
      List.mem_map.mpr ⟨_, Hc, rfl⟩
    have hle := list_max_ge _ _ Hin
    rw [List.length_append] at hle
    omega
  · exact cyl_enum_sum_le p argv envp fs Hp0 Hp1 _ bs

/- =========================================================================
   The three exports
   ========================================================================= -/

/-- The cylinder's mass, in closed form: a power of the ratio, which is
    the product of the two powers the plan quotes. -/
def stdin_geometric_cylinder_mass (p : Rat) (bs : List (BitVec 8)) : Rat :=
  geo_mass p bs.length

theorem stdin_geometric_cylinder_mass_closed_form (p : Rat) (bs : List (BitVec 8)) :
    stdin_geometric_cylinder_mass p bs =
      Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  geo_mass_closed_form p bs.length

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over `bs`, weighs at most that cylinder's mass.  The
    hypothesis is the one `Measure.weight_bound_T` carries, and
    `core_sum_map_fin_core` is the only step between them. -/
theorem stdin_geometric_bound (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_stdin_cylinder argv envp fs bs (fin_core f)) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤
      stdin_geometric_cylinder_mass p bs := by
  show core_sum (geo_weight p argv envp fs) l ≤ geo_mass p bs.length
  rw [core_sum_map_fin_core]
  apply geo_weight_cylinder_bound p argv envp fs Hp0 Hp1 bs (List.map fin_core l)
  · exact Hnd
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    exact Hcyl f Hf

/-- The environment test as a boolean, so that `List.filter` can use it.
    `Measure`'s `Qle_bool` exception is not in play here: this decides an
    equality of CORES, which `FinCore_eq_dec` decides outright, and no
    rational is involved. -/
def matches_env (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) : Bool :=
  decide (c = FinCore.mkFinCore argv envp fs c.core_stdin)

theorem matches_env_false (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) (H : matches_env argv envp fs c = false) :
    c ≠ FinCore.mkFinCore argv envp fs c.core_stdin :=
  of_decide_eq_false H

theorem matches_env_true (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) (H : matches_env argv envp fs c = true) :
    c = FinCore.mkFinCore argv envp fs c.core_stdin :=
  of_decide_eq_true H

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE: each record is
    in the cylinder OR its core misses the fixed environment entirely.

    `stdin_geometric_bound` cannot be weakened to drop the membership
    requirement — a core that matches the environment but whose standard
    input leaves the cylinder has positive weight and refutes it.  What
    CAN be added is the one class of cores that is harmless because it
    weighs nothing, and this is that statement.  It is a strict
    generalization of `stdin_geometric_bound` (take the left disjunct
    everywhere) and both are exported.

    Without this export every consumer re-derives the same repair —
    filter on `matches_env`, discharge the dropped terms through
    `geo_weight_mismatch`, carry `List.NoDup` across with
    `List.Nodup.sublist`, observe that a surviving core must have taken
    the left disjunct. -/
theorem stdin_geometric_bound_or_off_environment (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l → in_stdin_cylinder argv envp fs bs (fin_core f) ∨
      matches_env argv envp fs (fin_core f) = false) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤
      stdin_geometric_cylinder_mass p bs := by
  show core_sum (geo_weight p argv envp fs) l ≤ geo_mass p bs.length
  rw [core_sum_map_fin_core]
  rw [qsum_filter (geo_weight p argv envp fs) (matches_env argv envp fs)
    (List.map fin_core l) ?_]
  · apply geo_weight_cylinder_bound p argv envp fs Hp0 Hp1 bs
    · exact List.Nodup.sublist List.filter_sublist Hnd
    · intro c Hc
      obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
      rcases Hor f Hf with h | h
      · exact h
      · rw [h] at Hm
        exact absurd Hm (by decide)
  · intro c Hc
    rw [geo_weight_mismatch p argv envp fs c (matches_env_false _ _ _ _ Hc)]

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass `1`.

    With the disjunctive bound in hand it is that bound at the EMPTY
    prefix, and the whole content is the observation that the disjunction
    is EXHAUSTIVE there: a core either matches the fixed launch-time
    environment — in which case its standard input is `[] ++ itself`, so
    it is in the cylinder over `[]` — or it does not, which is the right
    disjunct.  Nothing is assumed about the list beyond
    `Measure.weight_bound_T`'s own `List.Nodup`.  The cylinder mass over
    the empty prefix is `1` because `Qpow` at exponent zero is,
    definitionally. -/
theorem stdin_geometric_mass_upper (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p)
    (Hp1 : p ≤ 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤
      (stdin_geometric p argv envp fs Hp0 Hp1).cd_mass := by
  show core_sum (geo_weight p argv envp fs) l ≤ 1
  have h := stdin_geometric_bound_or_off_environment p argv envp fs Hp0 Hp1 []
    l Hnd ?_
  · have h1 : stdin_geometric_cylinder_mass p [] = 1 := rfl
    rw [h1] at h
    exact h
  · intro f _
    by_cases hm : matches_env argv envp fs (fin_core f) = true
    · left
      refine ⟨(fin_core f).core_stdin, ?_⟩
      rw [matches_env_true _ _ _ _ hm]
      simp
    · right
      rcases hb : matches_env argv envp fs (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm

/- =========================================================================
   The length slice
   ========================================================================= -/

/-- The cancellation the slice bound turns on, on its own: a FULL slice —
    all `256 ^ n` of it — weighs exactly `p_stop * (1 - p_stop) ^ n`.  The
    `256 ^ n` and the `(1 / 256) ^ n` inside each weight recombine into
    `1 ^ n` by `Qpow_mult` and `Qpow_1`, with no side condition because
    `Qpow` has none.

    Stated separately because both directions need it: the bound needs it
    to know the constant is right, and
    `stdin_geometric_slice_bound_attained` needs it to know the constant is
    reached.  An identity used once to bound and once to attain is exactly
    the thing not to inline twice.

    The first step is the only multiplicative rearrangement in the
    section, and it is named so that the two consumers below can both
    spend it: `Qpow 256 n * Qpow (1/256) n` is `Qpow (256 * (1/256)) n`
    read backwards, which is `Qpow 1 n`. -/
theorem Qpow_256_mul_inv (n : Nat) :
    Qpow (256 : Rat) n * Qpow (1 / 256) n = 1 := by
  rw [← Qpow_mult]
  have h : (256 : Rat) * (1 / 256) = 1 := by grind
  rw [h, Qpow_1]

/-- THE SLICE IDENTITY.  `geo_slice_total`: the sum over a full
    length-`n` slice is the geometric distribution over LENGTHS, with no
    `1/256` left in it. -/
theorem geo_slice_total (p : Rat) (n : Nat) :
    Qnat (256 ^ n) * geo_point p n = p * Qpow (1 - p) n := by
  rw [Qnat_pow_256, geo_point_closed_form]
  calc Qpow (256 : Rat) n * (p * Qpow (1 - p) n * Qpow (1 / 256) n)
      = (Qpow (256 : Rat) n * Qpow (1 / 256) n) * (p * Qpow (1 - p) n) := by
        grind
    _ = 1 * (p * Qpow (1 - p) n) := by rw [Qpow_256_mul_inv]
    _ = p * Qpow (1 - p) n := by grind

/-- THE LENGTH SLICE: a list drawn from one length slice weighs at most
    `p_stop * (1 - p_stop) ^ n` — the geometric distribution over LENGTHS,
    with no `1/256` left in it.

    This is the counting lemma cashed in, and it is the export that shows
    what the counting is for.  Every core in such a list weighs the same,
    `geo_point p_stop n`, so the sum is the LENGTH of the list times that;
    the length is at most `256 ^ n`; and `256 ^ n` against the `(1 / 256) ^
    n` inside the weight cancels exactly, by `Qpow_mult` and `Qpow_1`.

    It is a stepping stone to nothing below — the cylinder bound is proved
    by enumeration and does not use it — and is exported because a task
    author summing over inputs of a fixed size wants this number, not a
    cylinder's. -/
theorem stdin_geometric_slice_bound (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧
        f.fin_stdin.length = n) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤
      p * Qpow (1 - p) n := by
  show core_sum (geo_weight p argv envp fs) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (geo_weight p argv envp fs) (List.map fin_core l) (geo_point p n) ?_]
  · rw [← geo_slice_total p n]
    refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
    apply Qnat_le
    rw [List.length_map]
    exact injective_core_list_in_cylinder_length_bound argv envp fs n l Hnd Hall
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlen⟩ := Hall f Hf
    rw [Henv, geo_weight_match, Hlen]

/-- THE SLICE BOUND'S CONSTANT IS REACHED, at every `n` and over any
    launch-time environment: the full slice is admissible, and it weighs
    `p_stop * (1 - p_stop) ^ n` exactly.

    This is what the counting lemma's attainability is FOR.  Pinning that a
    duplicate-free slice has at most `256 ^ n` elements says the counting is
    right; pinning that the bound those elements imply is reached says the
    EXPORT is right.  The witness is the counting lemma's own — every
    length-`n` standard input, wrapped — and the sum is `qsum_const` (every
    core in a slice weighs the same) followed by `geo_slice_total`. -/
theorem stdin_geometric_slice_bound_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧
          f.fin_stdin.length = n) ∧
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l =
        p * Qpow (1 - p) n := by
  obtain ⟨l, Hnd, Hall, Hlen⟩ :=
    injective_core_list_in_cylinder_length_bound_attained argv envp fs n
  refine ⟨l, Hnd, Hall, ?_⟩
  show core_sum (geo_weight p argv envp fs) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (geo_weight p argv envp fs) (List.map fin_core l) (geo_point p n) ?_]
  · rw [List.length_map, Hlen, geo_slice_total]
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlength⟩ := Hall f Hf
    rw [Henv, geo_weight_match, Hlength]

/-- ... and so NO SMALLER CONSTANT IS A SLICE BOUND.  Attainment says the
    number is reached; this says it therefore cannot be lowered, which is
    the claim a reader wants and the one that would be false if the bound
    were loose anywhere.  It is the contrapositive shape on purpose —
    quantified over every candidate `K` a future version of this file might
    try to prove instead — so it stays true as a regression test rather
    than as a fact about today's proof. -/
theorem stdin_geometric_slice_bound_sharp (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) (K : Rat)
    (Hbound : ∀ l : List FinProcInput, (List.map fin_core l).Nodup →
      (∀ f, f ∈ l →
        fin_core f = FinCore.mkFinCore argv envp fs f.fin_stdin ∧
          f.fin_stdin.length = n) →
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤ K) :
    p * Qpow (1 - p) n ≤ K := by
  obtain ⟨l, Hnd, Hall, Hsum⟩ :=
    stdin_geometric_slice_bound_attained p argv envp fs Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hnd Hall

/- =========================================================================
   Non-vacuity: the weight really vanishes off the fixed environment
   ========================================================================= -/

/-- Differing in argv alone is enough to zero the weight — the general fact
    behind the concrete instance below.  Stated on argv because that is the
    field the example varies; envp and the file system go the same way,
    through the same `geo_weight_mismatch`. -/
theorem geo_weight_off_environment_zero (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore)
    (Hne : c.core_argv ≠ argv) : geo_weight p argv envp fs c = 0 := by
  apply geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- Two cores over the empty launch-time environment: the empty input, and
    one whose argv is not empty.  As at `example_core_empty`, neither is
    claimed valid; they are two points of `FinInput.FinCore`. -/
def geo_example_core : FinCore := FinCore.mkFinCore [] [] [] []

def geo_example_other : FinCore :=
  FinCore.mkFinCore [[BitVec.ofInt 8 65]] [] [] []

/-- THE BITE, both ways: the distribution is not the zero distribution — it
    puts `p_stop` on the empty input, which is positive whenever `p_stop` is
    — and it is not a constant either, since a core with the wrong argv
    weighs exactly zero.  Without the second half, "weight zero off the
    fixed environment" would be a claim only the definition makes; without
    the first, every bound above would hold of a distribution that weighs
    nothing. -/
theorem stdin_geometric_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : 0 < p) :
    (0 < (stdin_geometric p [] [] [] Hp0 Hp1).cd_weight geo_example_core) ∧
      (stdin_geometric p [] [] [] Hp0 Hp1).cd_weight geo_example_other = 0 := by
  constructor
  · show 0 < geo_weight p [] [] [] geo_example_core
    unfold geo_weight geo_example_core
    rw [ite_eq_left rfl]
    show 0 < geo_point p 0
    unfold geo_point geo_mass
    rw [Qpow_0]
    grind
  · show geo_weight p [] [] [] geo_example_other = 0
    apply geo_weight_off_environment_zero
    show ([[BitVec.ofInt 8 65]] : List (List (BitVec 8))) ≠ []
    simp

/- =========================================================================
   Non-vacuity: the mass is reached, and `List.NoDup` is load-bearing
   ========================================================================= -/

/-- The member of the family at `p_stop = 1`: stop immediately, always.  It
    is the point mass on the empty standard input, it is admitted by the
    constructor — `Qle_0_1` and `Qle_refl` are its two side conditions — and
    it is the instance that makes the two bites below concrete arithmetic
    instead of open terms.  It is also why `Qpow` exists: its ratio is
    zero. -/
def geo_point_cd : CoreDistribution :=
  stdin_geometric 1 [] [] [] Qle_0_1 (Rat.le_refl)

def geo_empty_input : FinProcInput := core_input geo_example_core

/-- The empty input weighs exactly `1` at `p_stop = 1` — the closed
    arithmetic the two pins below rest on, named rather than recomputed so
    that neither of them has to unfold `geo_weight` twice. -/
theorem geo_weight_empty_input_at_one :
    geo_weight 1 [] [] [] geo_example_core = 1 := by
  unfold geo_weight geo_example_core
  rw [ite_eq_left rfl]
  show geo_point 1 0 = 1
  unfold geo_point geo_mass
  rw [Qpow_0]
  grind

/-- The declared mass `1` is not padding at this instance: a one-element
    admissible list reaches it OUTRIGHT.  That is special to `p_stop = 1`,
    where the tail past the empty input is empty; the general lower
    certificate (`stdin_geometric_mass_lower_certificate`) can only approach
    the mass, and this is the one member of the family where approaching and
    reaching coincide.

    It is also this file's witness that `stdin_geometric_mass_not_attained`
    cannot drop its `p_stop < 1`: that lemma says every admissible list
    weighs strictly less than the mass, and the list below refutes it at
    `p_stop = 1`.  A closed `Qeq` between literals, decided by computation,
    per the header's exception. -/
theorem geo_point_cd_mass_attained :
    (List.map fin_core [geo_empty_input]).Nodup ∧
      core_sum geo_point_cd.cd_weight [geo_empty_input] = geo_point_cd.cd_mass := by
  constructor
  · rw [List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · show core_sum (geo_weight 1 [] [] []) [geo_empty_input] = 1
    rw [core_sum_cons, core_sum_nil]
    show geo_weight 1 [] [] [] (fin_core (core_input geo_example_core)) + 0 = 1
    rw [fin_core_core_input, geo_weight_empty_input_at_one]
    grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING for the cylinder bound too,
    and this is `finite_support_bound_needs_nodup` for the geometric family:
    offer the same core twice — two records, so the list is duplicate-free
    as a list of RECORDS, and both records lie in the cylinder over the
    empty prefix — and the sum is `2` against a cylinder mass of `1`.

    All three conjuncts are needed.  The second says the list really does
    satisfy the cylinder hypothesis, so it is not excluded by that; the
    third says the bound genuinely fails on it; the first names what does
    exclude it.  Without the second a reader could suspect the list was
    ruled out for some other reason, and the refutation would say nothing
    about duplicate-freedom. -/
theorem stdin_geometric_bound_needs_nodup :
    ¬ (List.map fin_core [geo_empty_input, geo_empty_input]).Nodup ∧
      (∀ f, f ∈ [geo_empty_input, geo_empty_input] →
        in_stdin_cylinder [] [] [] [] (fin_core f)) ∧
      ¬ (core_sum geo_point_cd.cd_weight [geo_empty_input, geo_empty_input] ≤
        stdin_geometric_cylinder_mass 1 []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil] at Hnd
    obtain ⟨hnot, _⟩ := List.nodup_cons.mp Hnd
    exact hnot (List.mem_cons_self ..)
  · intro f Hf
    rcases List.mem_cons.mp Hf with rfl | hf
    · exact ⟨[], rfl⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨[], rfl⟩
      · cases hf
  · intro Hle
    have hsum : core_sum (geo_weight 1 [] [] [])
        [geo_empty_input, geo_empty_input] = 2 := by
      rw [core_sum_cons, core_sum_cons, core_sum_nil]
      show geo_weight 1 [] [] [] (fin_core (core_input geo_example_core)) +
        (geo_weight 1 [] [] [] (fin_core (core_input geo_example_core)) + 0) = 2
      rw [fin_core_core_input, geo_weight_empty_input_at_one]
      grind
    have hmass : geo_mass 1 0 = 1 := by
      unfold geo_mass
      rw [Qpow_0]
    have hle' : core_sum (geo_weight 1 [] [] []) [geo_empty_input, geo_empty_input] ≤
        geo_mass 1 0 := Hle
    rw [hsum, hmass] at hle'
    exact absurd hle' (by decide)



/- =========================================================================
   Sums, scaled and added
   ========================================================================= -/

/-- The two sum identities the composition combinators need, stated on
    `core_sum` because that is the side a consumer's bound is on.  They are
    here rather than beside `core_sum_cons` because the combinators below
    are their only callers, and reading them next to the combinators is
    reading them next to the reason they exist. -/
theorem core_sum_scale (q : Rat) (w : FinCore → Rat) (l : List FinProcInput) :
    core_sum (fun c => q * w c) l = q * core_sum w l := by
  rw [core_sum_map_fin_core, core_sum_map_fin_core, qsum_scale]

theorem core_sum_plus (w1 w2 : FinCore → Rat) (l : List FinProcInput) :
    core_sum (fun c => w1 c + w2 c) l = core_sum w1 l + core_sum w2 l := by
  rw [core_sum_map_fin_core, core_sum_map_fin_core, core_sum_map_fin_core,
    qsum_plus]

theorem core_sum_zero (l : List FinProcInput) :
    core_sum (fun _ => 0) l = 0 := by
  rw [core_sum_map_fin_core]
  exact qsum_zero _

/-- A weight that vanishes everywhere sums to zero, whatever the list —
    `core_sum_zero` up to pointwise equality.  It is what makes the
    degeneracy at `p_stop = 0` a statement about EVERY admissible list
    rather than about the witness family alone
    (`stdin_geometric_mass_lower_needs_positive`). -/
theorem core_sum_zero_weight (w : FinCore → Rat) (l : List FinProcInput)
    (Hz : ∀ c, w c = 0) : core_sum w l = 0 := by
  rw [core_sum_map_fin_core]
  rw [qsum_ext w (fun _ => 0) _ (fun c _ => Hz c)]
  exact qsum_zero _

/- =========================================================================
   Combinators: scaling and mixture
   ========================================================================= -/

/-- Scaling a distribution by a nonnegative factor: every weight and the
    declared mass multiplied together, so that the relation the
    certificates report between them is preserved rather than left true by
    luck.

    `0 <= q` is a constructor argument for the reason `finite_support`'s
    nonnegativity proof and `stdin_geometric`'s two side conditions are:
    `cd_nonneg` is a FIELD, and a scaling that returned a
    `CoreDistribution` without a proof would have to invent that field.  At
    a negative `q` there is nothing to invent —
    `cd_scale_negative_no_core_distribution` refutes the existence of ANY
    `CoreDistribution` weighing cores the way a negative scaling of
    `example_cd` would. -/
def cd_scale (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution) : CoreDistribution where
  cd_weight := fun c => q * D.cd_weight c
  cd_mass := q * D.cd_mass
  cd_nonneg := fun c => Rat.mul_nonneg Hq (D.cd_nonneg c)

/-- The mixture of two distributions: the weights ADD, pointwise, and the
    declared masses add with them.

    Nothing is normalized and nothing is halved.  A mixture in the
    probabilist's sense — `a` of one and `1 - a` of the other — is this
    combinator applied to two `cd_scale`s, and writing it that way keeps the
    two decisions (how much of each, and what to do with the sum) separate
    and both visible.  There is no side condition at all: nonnegativity
    composes by `Qplus_nonneg`, and no obligation anywhere ties `cd_mass` to
    anything.

    SUPPORTS MAY OVERLAP, and on a shared core the weights add like
    everywhere else — which is the right reading and not a defect to be
    repaired, for the reason `entries_weight` sums duplicate entries: the
    declared mass is the sum of the declared masses, so a mixture that
    silently took a maximum on the overlap would declare a total no list
    could reach.  `cd_mix2_overlap_weights_add` pins the arithmetic at a
    concrete overlapping pair, and `cd_mix2_bound_is_not_the_max` pins the
    consequence a reader might otherwise guess wrong. -/
def cd_mix2 (D1 D2 : CoreDistribution) : CoreDistribution where
  cd_weight := fun c => D1.cd_weight c + D2.cd_weight c
  cd_mass := D1.cd_mass + D2.cd_mass
  cd_nonneg := fun c => Qplus_nonneg _ _ (D1.cd_nonneg c) (D2.cd_nonneg c)

/-- The mixture's declared mass, by conversion — stated so that the two
    components can be peeled apart without unfolding the structure. -/
theorem cd_mix2_mass (D1 D2 : CoreDistribution) :
    (cd_mix2 D1 D2).cd_mass = D1.cd_mass + D2.cd_mass := rfl

/-- The empty mixture: weight zero everywhere, declared mass zero.  It is
    the unit the `n`-ary fold below folds against, and it is a legitimate
    `CoreDistribution` rather than a degenerate case to be avoided — every
    bound holds of it, trivially and truthfully. -/
def cd_zero : CoreDistribution where
  cd_weight := fun _ => 0
  cd_mass := 0
  cd_nonneg := fun _ => Rat.le_refl

/-- `cd_zero`'s two values, as rewrite rules. -/
theorem cd_zero_mass : cd_zero.cd_mass = 0 := rfl

theorem cd_zero_weight (c : FinCore) : cd_zero.cd_weight c = 0 := rfl

/-- The `n`-ary mixture, as the fold of `cd_mix2` over `cd_zero`.  A
    recursive definition rather than a `List.foldr` with a
    `CoreDistribution` accumulator so that `cd_weight (cd_mix (D :: Ds))`
    reduces to the sum of a weight and a recursive call by conversion, which
    is what the induction in `cd_mix_bound` wants. -/
def cd_mix : List CoreDistribution → CoreDistribution
  | [] => cd_zero
  | D :: rest => cd_mix2 D (cd_mix rest)

/-- The total a list of per-component numbers declares.  Kept as its own
    definition so that the `n`-ary bound and the `n`-ary mass are the SAME
    fold at two different arguments — `cd_mix_mass` below is that
    identification, and without it a consumer would have to match a
    `foldr` against a fixpoint by hand. -/
def cd_sum_over (B : CoreDistribution → Rat) (Ds : List CoreDistribution) :
    Rat :=
  List.foldr (fun D acc => B D + acc) 0 Ds

/-- The two computation rules of the fold, as rewrite rules.  Both hold by
    conversion; they are stated because `show` compares up to the target's
    weak head normal form rather than up to arbitrary unfolding, so the
    fold has to be stepped explicitly. -/
theorem cd_sum_over_nil (B : CoreDistribution → Rat) : cd_sum_over B [] = 0 := rfl

theorem cd_sum_over_cons (B : CoreDistribution → Rat) (D : CoreDistribution)
    (Ds : List CoreDistribution) :
    cd_sum_over B (D :: Ds) = B D + cd_sum_over B Ds := rfl

/-- ... and the same two for the mixture itself. -/
theorem cd_mix_nil : cd_mix [] = cd_zero := rfl

theorem cd_mix_cons (D : CoreDistribution) (Ds : List CoreDistribution) :
    cd_mix (D :: Ds) = cd_mix2 D (cd_mix Ds) := rfl

/-- The mixture's declared mass IS the total of the components' — `Qeq`
    would do, and this is `eq`, because both sides are the same fold. -/
theorem cd_mix_mass (Ds : List CoreDistribution) :
    (cd_mix Ds).cd_mass = cd_sum_over (fun D => D.cd_mass) Ds := by
  induction Ds with
  | nil => rw [cd_mix_nil]; rfl
  | cons D Ds ih =>
    rw [cd_mix_cons, cd_mix2_mass, cd_sum_over_cons, ih]

/- =========================================================================
   The bounds compose
   ========================================================================= -/

/-- SCALING: a bound for `D` scales to a bound for the scaling.  `B` is any
    bound whatever, not necessarily the declared mass, so this applies to a
    cylinder bound and a length-slice bound exactly as it applies to a mass
    certificate.

    Nonnegativity of `q` is what makes the multiplication monotone; it is
    the constructor's argument, so a consumer never supplies it twice. -/
theorem cd_scale_bound (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) (B : Rat)
    (Hb : core_sum D.cd_weight l ≤ B) :
    core_sum (cd_scale q Hq D).cd_weight l ≤ q * B := by
  show core_sum (fun c => q * D.cd_weight c) l ≤ q * B
  rw [core_sum_scale]
  exact Rat.mul_le_mul_of_nonneg_left Hb Hq

/-- ... and the declared mass scales with it, so the mass certificate
    survives scaling: `cd_mass (cd_scale q Hq D)` is `q * cd_mass D` by
    conversion. -/
theorem cd_scale_mass (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution) :
    (cd_scale q Hq D).cd_mass = q * D.cd_mass := rfl

theorem cd_scale_bound_mass (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput)
    (Hb : core_sum D.cd_weight l ≤ D.cd_mass) :
    core_sum (cd_scale q Hq D).cd_weight l ≤ (cd_scale q Hq D).cd_mass :=
  cd_scale_bound q Hq D l D.cd_mass Hb

/-- ... and so does the SIGN of the mass, which is what
    `Measure.DISTRIBUTION`'s `M_nonneg` asks about: a nonnegative mass
    scaled by the nonnegative `q` the constructor already demanded stays
    nonnegative.  The `0 <= q` here is `cd_scale`'s own argument, not a new
    hypothesis. -/
theorem cd_scale_mass_nonneg (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (HD : 0 ≤ D.cd_mass) : 0 ≤ (cd_scale q Hq D).cd_mass := by
  rw [cd_scale_mass]
  exact Rat.mul_nonneg Hq HD

/-- MIXTURE: bounds for the two components add to a bound for the mixture,
    ON THE SAME LIST.  That the list is shared is the whole content — each
    component is bounded on the very list the mixture is being bounded on,
    so no rearrangement and no duplicate-freedom argument happens here;
    whatever hypotheses the two component bounds carried, the caller has
    already discharged them. -/
theorem cd_mix2_bound (D1 D2 : CoreDistribution) (l : List FinProcInput)
    (B1 B2 : Rat)
    (H1 : core_sum D1.cd_weight l ≤ B1)
    (H2 : core_sum D2.cd_weight l ≤ B2) :
    core_sum (cd_mix2 D1 D2).cd_weight l ≤ B1 + B2 := by
  show core_sum (fun c => D1.cd_weight c + D2.cd_weight c) l ≤ B1 + B2
  rw [core_sum_plus]
  exact Qplus_le_compat H1 H2

theorem cd_mix2_bound_mass (D1 D2 : CoreDistribution) (l : List FinProcInput)
    (H1 : core_sum D1.cd_weight l ≤ D1.cd_mass)
    (H2 : core_sum D2.cd_weight l ≤ D2.cd_mass) :
    core_sum (cd_mix2 D1 D2).cd_weight l ≤ (cd_mix2 D1 D2).cd_mass :=
  cd_mix2_bound D1 D2 l D1.cd_mass D2.cd_mass H1 H2

/-- The mixture's mass is nonnegative when both components' are, by
    `Qplus_nonneg` — the same fact that makes `cd_mix2`'s `cd_nonneg` field
    composable, one level up.  With `cd_scale_mass_nonneg` this closes
    `Measure.DISTRIBUTION`'s `M_nonneg` under the two combinators a
    probabilist's mixture is written with. -/
theorem cd_mix2_mass_nonneg (D1 D2 : CoreDistribution)
    (H1 : 0 ≤ D1.cd_mass) (H2 : 0 ≤ D2.cd_mass) :
    0 ≤ (cd_mix2 D1 D2).cd_mass := by
  rw [cd_mix2_mass]
  exact Qplus_nonneg _ _ H1 H2

/-- THE `n`-ARY FORM: a bound for every component gives the total of those
    bounds for the mixture.  The bounds are given as a FUNCTION of the
    component rather than as a parallel list, so nothing has to line up two
    lists of different provenance — and `cd_sum_over` is then literally the
    same fold as `cd_mix`'s mass. -/
theorem cd_mix_bound (B : CoreDistribution → Rat) (Ds : List CoreDistribution)
    (l : List FinProcInput)
    (Hb : ∀ D, D ∈ Ds → core_sum D.cd_weight l ≤ B D) :
    core_sum (cd_mix Ds).cd_weight l ≤ cd_sum_over B Ds := by
  induction Ds with
  | nil =>
    rw [cd_mix_nil]
    show core_sum (fun _ => 0) l ≤ cd_sum_over B []
    rw [cd_sum_over_nil, core_sum_zero]
    exact Rat.le_refl
  | cons D Ds ih =>
    rw [cd_mix_cons, cd_sum_over_cons]
    show core_sum (fun c => D.cd_weight c + (cd_mix Ds).cd_weight c) l ≤
      B D + cd_sum_over B Ds
    exact cd_mix2_bound D (cd_mix Ds) l (B D) (cd_sum_over B Ds)
      (Hb D (List.mem_cons_self ..))
      (ih (fun D' HD' => Hb D' (List.mem_cons_of_mem _ HD')))

/-- ... and at the components' declared masses that is the mixture's own
    mass certificate, which is the statement a task author building a
    background-plus-foreground distribution consumes. -/
theorem cd_mix_bound_mass (Ds : List CoreDistribution) (l : List FinProcInput)
    (Hb : ∀ D, D ∈ Ds → core_sum D.cd_weight l ≤ D.cd_mass) :
    core_sum (cd_mix Ds).cd_weight l ≤ (cd_mix Ds).cd_mass := by
  rw [cd_mix_mass]
  exact cd_mix_bound (fun D => D.cd_mass) Ds l Hb

/- =========================================================================
   The certificates compose too
   ========================================================================= -/

/-- The LOWER half survives scaling and mixing, and it is worth stating
    separately from the upper half because the two travel differently: an
    upper bound holds of every admissible list, so the components' upper
    bounds may be proved on lists chosen independently, while an attaining
    list has to be ONE list that attains both.  Hence the shared `l` in the
    hypotheses below — a real requirement, not bookkeeping.
    `cd_mix2_finite_support_mass_exact` shows the shared witness exists for
    a pair of finite supports, which is the case a task actually meets.

    THE GENERIC-`B` FORMS COME FIRST, and stating them first is not
    tidiness: they are the only ones a geometric component can use.  A
    family whose mass is a supremum and not a maximum never satisfies
    `cd_mass D <= core_sum (cd_weight D) l` —
    `stdin_geometric_mass_not_attained` refutes that hypothesis on every
    duplicate-free list — so a mixture of such families has to compose
    numbers that fall SHORT of the two declared masses, and the shortfall
    has to survive the scaling and the addition.  `B` is any number
    whatever, exactly as in `cd_scale_bound` and `cd_mix2_bound`, and the
    mass forms below are the instances at `B = cd_mass D`, the same way
    `cd_scale_bound_mass` is an instance of `cd_scale_bound`. -/
theorem cd_scale_bound_lower (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput) (B : Rat)
    (Hb : B ≤ core_sum D.cd_weight l) :
    q * B ≤ core_sum (cd_scale q Hq D).cd_weight l := by
  show q * B ≤ core_sum (fun c => q * D.cd_weight c) l
  rw [core_sum_scale]
  exact Rat.mul_le_mul_of_nonneg_left Hb Hq

theorem cd_mix2_bound_lower (D1 D2 : CoreDistribution) (l : List FinProcInput)
    (B1 B2 : Rat)
    (H1 : B1 ≤ core_sum D1.cd_weight l)
    (H2 : B2 ≤ core_sum D2.cd_weight l) :
    B1 + B2 ≤ core_sum (cd_mix2 D1 D2).cd_weight l := by
  show B1 + B2 ≤ core_sum (fun c => D1.cd_weight c + D2.cd_weight c) l
  rw [core_sum_plus]
  exact Qplus_le_compat H1 H2

theorem cd_scale_mass_lower (q : Rat) (Hq : 0 ≤ q) (D : CoreDistribution)
    (l : List FinProcInput)
    (Hlow : D.cd_mass ≤ core_sum D.cd_weight l) :
    (cd_scale q Hq D).cd_mass ≤ core_sum (cd_scale q Hq D).cd_weight l :=
  cd_scale_bound_lower q Hq D l D.cd_mass Hlow

theorem cd_mix2_mass_lower (D1 D2 : CoreDistribution) (l : List FinProcInput)
    (H1 : D1.cd_mass ≤ core_sum D1.cd_weight l)
    (H2 : D2.cd_mass ≤ core_sum D2.cd_weight l) :
    (cd_mix2 D1 D2).cd_mass ≤ core_sum (cd_mix2 D1 D2).cd_weight l :=
  cd_mix2_bound_lower D1 D2 l D1.cd_mass D2.cd_mass H1 H2

/-- A MIXTURE OF TWO FINITE SUPPORTS HAS ITS MASS ATTAINED, which is the
    case a task actually meets and the reason
    `finite_support_mass_lower_on` is stated up in the certificates section
    in the general form it has.  The canonical list of
    `finite_support_mass_lower_witness` would not do here: it covers one
    component's entries and says nothing about the other's, while
    `cd_mix2_mass_lower` needs ONE list attaining both.

    The list that works is the obvious one — the entries' cores of BOTH,
    duplicates removed — and it covers each component because each entry
    list is contained in their concatenation.  `cd_mix2_mass_lower` then
    adds the two attainments, `cd_mix2_bound_mass` adds the two bounds, and
    the equality is antisymmetry on those, never a computation. -/
theorem cd_mix2_finite_support_mass_exact (e1 e2 : List (FinCore × Rat))
    (H1 : ∀ e, e ∈ e1 → 0 ≤ e.2) (H2 : ∀ e, e ∈ e2 → 0 ≤ e.2) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (cd_mix2 (finite_support e1 H1) (finite_support e2 H2)).cd_weight l =
        (cd_mix2 (finite_support e1 H1) (finite_support e2 H2)).cd_mass := by
  refine ⟨List.map core_input (core_nodup (List.map Prod.fst (e1 ++ e2))),
    ?_, ?_⟩
  · rw [map_fin_core_core_input]
    exact nodup_core_nodup _
  · have Hnd : (core_nodup (List.map Prod.fst (e1 ++ e2))).Nodup :=
      nodup_core_nodup _
    have cov1 : ∀ e, e ∈ e1 → e.1 ∈ core_nodup (List.map Prod.fst (e1 ++ e2)) := by
      intro e He
      apply (mem_core_nodup _ _).mpr
      exact List.mem_map.mpr ⟨e, List.mem_append.mpr (Or.inl He), rfl⟩
    have cov2 : ∀ e, e ∈ e2 → e.1 ∈ core_nodup (List.map Prod.fst (e1 ++ e2)) := by
      intro e He
      apply (mem_core_nodup _ _).mpr
      exact List.mem_map.mpr ⟨e, List.mem_append.mpr (Or.inr He), rfl⟩
    refine Rat.le_antisymm
      (cd_mix2_bound_mass _ _ _
        (finite_support_bound e1 H1 _
          (by rw [map_fin_core_core_input]; exact Hnd))
        (finite_support_bound e2 H2 _
          (by rw [map_fin_core_core_input]; exact Hnd))) ?_
    exact cd_mix2_mass_lower _ _ _
      (finite_support_mass_lower_on e1 H1 _ Hnd cov1)
      (finite_support_mass_lower_on e2 H2 _ Hnd cov2)

/- =========================================================================
   Non-vacuity: what scaling and mixing DO, pinned
   ========================================================================= -/

/-- Scaling by zero gives the zero distribution — pointwise, and in the
    declared mass.  It is an equality and not an implication: the weight of
    the scaling is `fun c => 0 * cd_weight D c`, which is the zero function
    only up to the field's arithmetic, and this file's discipline is that
    rational equality is proved rather than computed.  Worth pinning
    because it is the one input at which the constructor's `0 <= q` is
    tight, and because a reader should be able to see that scaling has not
    quietly been given a normalizing reading. -/
theorem cd_scale_zero (D : CoreDistribution) :
    (∀ c, (cd_scale 0 (Rat.le_refl : (0 : Rat) ≤ 0) D).cd_weight c =
        cd_zero.cd_weight c) ∧
      (cd_scale 0 (Rat.le_refl : (0 : Rat) ≤ 0) D).cd_mass = cd_zero.cd_mass := by
  constructor
  · intro c
    show 0 * D.cd_weight c = 0
    grind
  · show 0 * D.cd_mass = 0
    grind

/-- A NEGATIVE scaling admits no `CoreDistribution` at all, which is what
    makes `cd_scale`'s proof argument a refusal rather than an
    inconvenience.  This is `negative_entries_no_core_distribution` for the
    scaling combinator: no record whose weight so much as AGREES pointwise
    with `-1` times `example_cd`'s can exist, because `cd_nonneg` refutes it
    at the core where `example_cd` puts `1 / 2`.  A distribution with no
    positive weight anywhere would of course survive a negative scaling,
    which is why the statement names a concrete `example_cd` rather than
    quantifying over `D`. -/
theorem cd_scale_negative_no_core_distribution (D : CoreDistribution) :
    ¬ (∀ c, D.cd_weight c = (-(1)) * example_cd.cd_weight c) := by
  intro Hagree
  have H := D.cd_nonneg example_core_empty
  have hw : example_cd.cd_weight example_core_empty = (1 : Rat) / 2 := by
    show entries_weight example_entries example_core_empty = 1 / 2
    show core_indicator example_core_empty (1 / 2) example_core_empty +
      (core_indicator example_core_a (1 / 4) example_core_empty + 0) = 1 / 2
    rw [core_indicator_hit, core_indicator_miss _ _ _ core_a_ne_empty]
    grind
  rw [Hagree example_core_empty, hw] at H
  grind

/- =========================================================================
   Non-vacuity: two supports that OVERLAP
   ========================================================================= -/

/-- Two finite supports whose supports OVERLAP: both put weight on the empty
    core, and one of them also weighs "A".  This is the pair the three
    bites below are about — `example_cd` and `dup_cd` would not do, since
    what is at issue is two distributions meeting on a core, not one
    distribution's repeated entries. -/
def overlap_entries_l : List (FinCore × Rat) :=
  [(example_core_empty, (1 : Rat) / 2)]

def overlap_entries_r : List (FinCore × Rat) :=
  [(example_core_empty, (1 : Rat) / 4), (example_core_a, (1 : Rat) / 8)]

/-- The nonnegativity obligation for the left entry list, discharged entry
    by entry — the boolean scan of
    `entries_nonneg_of_forallb`, whose `rfl` obligation is an equality of
    decided rational comparisons the kernel cannot reduce (see
    `example_entries_nonneg`). -/
theorem overlap_entries_l_nonneg : ∀ e, e ∈ overlap_entries_l → 0 ≤ e.2 := by
  intro e He
  simp only [overlap_entries_l, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl
  show (0 : Rat) ≤ 1 / 2
  grind

theorem overlap_entries_r_nonneg : ∀ e, e ∈ overlap_entries_r → 0 ≤ e.2 := by
  intro e He
  simp only [overlap_entries_r, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl
  · show (0 : Rat) ≤ 1 / 4
    grind
  · show (0 : Rat) ≤ 1 / 8
    grind

def overlap_cd_l : CoreDistribution :=
  finite_support overlap_entries_l overlap_entries_l_nonneg

def overlap_cd_r : CoreDistribution :=
  finite_support overlap_entries_r overlap_entries_r_nonneg

def overlap_mix : CoreDistribution := cd_mix2 overlap_cd_l overlap_cd_r

/-- Each component's weight on the shared core, on its own, so that the
    associativity pin at the end of the section can read both without
    redoing the indicator arithmetic. -/
theorem overlap_cd_l_weight_empty :
    overlap_cd_l.cd_weight example_core_empty = (1 : Rat) / 2 := by
  show core_indicator example_core_empty (1 / 2) example_core_empty + 0 = 1 / 2
  rw [core_indicator_hit]
  grind

theorem overlap_cd_r_weight_empty :
    overlap_cd_r.cd_weight example_core_empty = (1 : Rat) / 4 := by
  show core_indicator example_core_empty (1 / 4) example_core_empty +
    (core_indicator example_core_a (1 / 8) example_core_empty + 0) = 1 / 4
  rw [core_indicator_hit, core_indicator_miss _ _ _ core_a_ne_empty]
  grind

/-- The mixture's weight on the shared core: `1 / 2` from the left and
    `1 / 4` from the right, added. -/
theorem overlap_mix_weight_empty :
    overlap_mix.cd_weight example_core_empty = (3 : Rat) / 4 := by
  show core_indicator example_core_empty (1 / 2) example_core_empty + 0 +
    (core_indicator example_core_empty (1 / 4) example_core_empty +
      (core_indicator example_core_a (1 / 8) example_core_empty + 0)) = 3 / 4
  rw [core_indicator_hit, core_indicator_hit,
    core_indicator_miss _ _ _ core_a_ne_empty]
  grind

/-- ... and on the core only the right one names, its own `1 / 8`. -/
theorem overlap_mix_weight_a :
    overlap_mix.cd_weight example_core_a = (1 : Rat) / 8 := by
  show core_indicator example_core_empty (1 / 2) example_core_a + 0 +
    (core_indicator example_core_empty (1 / 4) example_core_a +
      (core_indicator example_core_a (1 / 8) example_core_a + 0)) = 1 / 8
  rw [core_indicator_miss _ _ _ (Ne.symm core_a_ne_empty),
    core_indicator_miss _ _ _ (Ne.symm core_a_ne_empty), core_indicator_hit]
  grind

/-- The mixture's declared mass: the two declared masses added. -/
theorem overlap_mix_mass : overlap_mix.cd_mass = (7 : Rat) / 8 := by
  show (1 / 2 + 0) + (1 / 4 + (1 / 8 + 0)) = 7 / 8
  grind

/-- ... and the two components' own, for the refutations below. -/
theorem overlap_cd_l_mass : overlap_cd_l.cd_mass = (1 : Rat) / 2 := by
  show (1 / 2 + 0) = 1 / 2
  grind

theorem overlap_cd_r_mass : overlap_cd_r.cd_mass = (3 : Rat) / 8 := by
  show 1 / 4 + (1 / 8 + 0) = 3 / 8
  grind

/-- THE OVERLAP BITE: on the shared core the weights ADD — `1 / 2` and
    `1 / 4` make `3 / 4`, not `1 / 2` and not `3 / 8` — the core only one of
    them names keeps its own weight, and the declared mass is the sum of the
    two declared masses.

    This is the "what IS true about mixtures of overlapping supports"
    statement.  Nothing is double-counted, because nothing was counted once
    to begin with: `cd_mix2` is defined to add, the masses are defined to add
    with it, and the third conjunct is what keeps the two halves in step. -/
theorem cd_mix2_overlap_weights_add :
    overlap_mix.cd_weight example_core_empty = (3 : Rat) / 4 ∧
      overlap_mix.cd_weight example_core_a = (1 : Rat) / 8 ∧
      overlap_mix.cd_mass = (7 : Rat) / 8 :=
  ⟨overlap_mix_weight_empty, overlap_mix_weight_a, overlap_mix_mass⟩

/-- ... AND THE MIXTURE'S BOUND IS NOT THE MAX OF THE COMPONENTS'.  The
    one-element list over the shared core already weighs `3 / 4` under the
    mixture, which is past BOTH components' declared masses (`1 / 2` and
    `3 / 8`) — so no rule of the form "a mixture is bounded by the largest
    of its parts" can hold, and `cd_mix2_bound`'s `B1 + B2` is not a
    convenient over-approximation that a sharper lemma could later replace
    by a maximum.

    Stated as two refutations rather than as one inequality against a
    maximum, because the claim being ruled out is about every candidate
    reading of "the max", and the two components' masses are the only
    candidates here. -/
theorem cd_mix2_bound_is_not_the_max :
    core_sum overlap_mix.cd_weight [core_input example_core_empty] = (3 : Rat) / 4 ∧
      ¬ (core_sum overlap_mix.cd_weight [core_input example_core_empty] ≤
        overlap_cd_l.cd_mass) ∧
      ¬ (core_sum overlap_mix.cd_weight [core_input example_core_empty] ≤
        overlap_cd_r.cd_mass) := by
  have hsum : core_sum overlap_mix.cd_weight [core_input example_core_empty] =
      (3 : Rat) / 4 := by
    rw [core_sum_cons, core_sum_nil]
    show overlap_mix.cd_weight (fin_core (core_input example_core_empty)) + 0 = 3 / 4
    rw [fin_core_core_input, overlap_mix_weight_empty]
    grind
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum, overlap_cd_l_mass]
    grind
  · rw [hsum, overlap_cd_r_mass]
    grind

/-- The `n`-ary fold agrees with the binary combinator and with its own
    unit: the empty mixture declares zero, and the two-element mixture
    declares and weighs what `cd_mix2` does.  Without the first conjunct the
    fold could be anything at all on the empty list; without the other two,
    `cd_mix` could disagree with `cd_mix2` and every lemma above would still
    be true of each of them separately. -/
theorem cd_mix_nary_agrees :
    (cd_mix []).cd_mass = 0 ∧
      (cd_mix [overlap_cd_l, overlap_cd_r]).cd_mass = overlap_mix.cd_mass ∧
      (cd_mix [overlap_cd_l, overlap_cd_r]).cd_weight example_core_empty =
        overlap_mix.cd_weight example_core_empty := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cd_mix_nil]; rfl
  · rw [cd_mix_cons, cd_mix_cons, cd_mix_nil, cd_mix2_mass, cd_mix2_mass,
      cd_zero_mass, overlap_mix_mass, overlap_cd_l_mass, overlap_cd_r_mass]
    grind
  · rw [cd_mix_cons, cd_mix_cons, cd_mix_nil]
    show overlap_cd_l.cd_weight example_core_empty +
      (overlap_cd_r.cd_weight example_core_empty + cd_zero.cd_weight example_core_empty) =
      overlap_mix.cd_weight example_core_empty
    rw [cd_zero_weight, overlap_cd_l_weight_empty, overlap_cd_r_weight_empty,
      overlap_mix_weight_empty]
    grind

/- =========================================================================
   How fast a power of a proper fraction shrinks
   ========================================================================= -/

/- Everything from here to the end serves ONE statement: the geometric
    distribution's declared mass `1` is not padding, because admissible
    lists come arbitrarily close to it.  The obstruction is that no finite
    list REACHES it (the header's supremum-versus-maximum paragraph, and
    `stdin_geometric_bound`'s discussion), so the certificate has to be an
    approach rather than an attainment, and an approach needs a rate.

    The rate is elementary and is proved here rather than assumed:
    `(1 - p) ^ k` shrinks at least like `1 / (1 + k * p)`.  No real
    numbers, no limits, no infinite series — a single induction and one
    Archimedean step. -/

/-- A power of a number in `[0, 1]` stays in `[0, 1]`. -/
theorem Qpow_le_1 (x : Rat) (k : Nat) (Hx0 : 0 ≤ x) (Hx1 : x ≤ 1) :
    Qpow x k ≤ 1 := by
  induction k with
  | zero => rw [Qpow_0]; exact Rat.le_refl
  | succ k ih =>
    rw [Qpow_succ]
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right Hx1 (Qpow_nonneg x k Hx0)) ?_
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left ih Qle_0_1) ?_
    grind

/-- The induction step of the shrinking bound, as arithmetic on its own.
    With `P` for `(1 - p) ^ k` and `n` for `k`, it says: if
    `P * (1 + n * p)` is at most `1`, then so is the same expression one
    step on.

    The step is the whole content and it is worth reading.  Expand:
    `(1 - p) * P * (1 + (1 + n) * p)` is `(1 - p) * (P * (1 + n * p))` plus
    `(1 - p) * P * p`.  The first summand is at most `1 - p` by the
    hypothesis; the second is at most `(1 - p) * p` because `P <= 1`; and
    their total is `1 - p * p`, which is at most `1` because a square is
    nonnegative.  That last inequality is where the slack lives, and it is
    why the bound is `1 / (1 + k * p)` rather than something sharper. -/
theorem geo_gap_step (p P : Rat) (n : Nat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (_HP0 : 0 ≤ P) (HP1 : P ≤ 1) (HIH : P * (1 + Qnat n * p) ≤ 1) :
    (1 - p) * P * (1 + (1 + Qnat n) * p) ≤ 1 := by
  have H1p : 0 ≤ 1 - p := by grind
  have Hpp : 0 ≤ p * p := Rat.mul_nonneg Hp0 Hp0
  have HA : (1 - p) * (P * (1 + Qnat n * p)) ≤ 1 - p := by
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left HIH H1p) ?_
    grind
  have HB : (1 - p) * P * p ≤ (1 - p) * p := by
    have h := Rat.mul_le_mul_of_nonneg_right HP1 (Rat.mul_nonneg H1p Hp0)
    grind
  refine Rat.le_trans (b := (1 - p) * (P * (1 + Qnat n * p)) + (1 - p) * P * p) ?_ ?_
  · grind
  refine Rat.le_trans (b := (1 - p) + (1 - p) * p) (Qplus_le_compat HA HB) ?_
  grind

/-- THE SHRINKING BOUND: `(1 - p) ^ k * (1 + k * p) <= 1`, for every `k`
    and every `p` in `[0, 1]`.

    Written multiplied out rather than as `(1 - p) ^ k <= 1 / (1 + k * p)`
    on purpose: the division would need `1 + k * p` to be non-zero as a
    side condition, and the multiplied form needs nothing at all.  Note
    that no STRICT hypothesis appears — at `p = 0` it says `1 <= 1`,
    truthfully and uselessly, which is exactly how the degenerate member
    behaves and is why the strictness enters below, at the point where a
    `k` must be CHOSEN. -/
theorem geo_gap_bound (p : Rat) (k : Nat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    Qpow (1 - p) k * (1 + Qnat k * p) ≤ 1 := by
  have H1p : 0 ≤ 1 - p := by grind
  have H1p1 : 1 - p ≤ 1 := by grind
  induction k with
  | zero =>
    rw [Qpow_0, Qnat_0]
    grind
  | succ k ih =>
    rw [Qpow_succ, Qnat_succ]
    exact geo_gap_step p (Qpow (1 - p) k) k Hp0 Hp1
      (Qpow_nonneg _ _ H1p) (Qpow_le_1 _ _ H1p H1p1) ih

/-- The Archimedean step, in the only form this file needs: no rational
    bounds every natural.  `QArith`'s `Qarchimedean` gives a positive
    exceeding the rational; `Rat.ceil` is the Lean rendering of the same
    fact — a rational is at most its ceiling, and an integer is at most its
    own absolute value — so the natural named here is the ceiling's
    absolute value. -/
theorem Qnat_unbounded (q : Rat) : ∃ k : Nat, q ≤ Qnat k := by
  refine ⟨q.ceil.natAbs, ?_⟩
  refine Rat.le_trans (Rat.le_ceil (x := q)) ?_
  show (q.ceil : Rat) ≤ ((q.ceil.natAbs : Nat) : Rat)
  have h2 : q.ceil ≤ (q.ceil.natAbs : Int) := Int.le_natAbs
  exact_mod_cast h2

/-- ... AND SO THE GAP CAN BE MADE AS SMALL AS ASKED, which is the
    statement `0 < p_stop` is for and the first place in this file that a
    strict inequality is load-bearing.

    Given a target `eps`, take `k` past `1 / (eps * p)` — legitimate only
    because `eps * p` is non-zero, which is where BOTH strictnesses are
    spent — and the shrinking bound does the rest: `(1 - p) ^ k` times
    `1 + k * p` is at most `1`, and `1 + k * p` is at least `1 / eps`.

    At `p = 0` the choice is unavailable and the conclusion is false:
    `(1 - 0) ^ k` is `1` for every `k`, never below an `eps` under one.
    That is the same degeneracy
    `stdin_geometric_mass_lower_needs_positive` pins at the level of the
    distribution. -/
theorem geo_gap_small (p eps : Rat) (Hp0 : 0 < p) (Hp1 : p ≤ 1)
    (Heps : 0 < eps) :
    ∃ k : Nat, Qpow (1 - p) k ≤ eps := by
  have hp0 : 0 ≤ p := Rat.le_of_lt Hp0
  have heps0 : 0 ≤ eps := Rat.le_of_lt Heps
  have hprod : eps * p ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1
    · exact Rat.ne_of_gt Heps h1
    · exact Rat.ne_of_gt Hp0 h1
  have hprod0 : 0 ≤ eps * p := Rat.mul_nonneg heps0 hp0
  -- the Archimedean choice, with the division cleared on the spot
  obtain ⟨k, Hk⟩ := Qnat_unbounded (eps * p)⁻¹
  refine ⟨k, ?_⟩
  have hone : (1 : Rat) ≤ eps * (Qnat k * p) := by
    have h1 : (eps * p)⁻¹ * (eps * p) ≤ Qnat k * (eps * p) :=
      Rat.mul_le_mul_of_nonneg_right Hk hprod0
    rw [Rat.inv_mul_cancel _ hprod] at h1
    grind
  have hkp : 0 ≤ Qnat k * p := Rat.mul_nonneg (Qnat_nonneg k) hp0
  have hXpos : 0 < 1 + Qnat k * p := by grind
  have hbound := geo_gap_bound p k hp0 Hp1
  refine Rat.le_of_mul_le_mul_right ?_ hXpos
  grind

/-- ... AND THE DEPTH IT PRODUCES CAN BE PUSHED AS FAR OUT AS ASKED, which
    is what a certificate needs when something OTHER than the margin also
    has a say in how deep to go.

    A tail only shrinks as the exponent grows — that is `Qpow_le_exp`, one
    induction on the gap — so replacing the `k` of `geo_gap_small` by
    `Nat.max k0 k` keeps the bound and clears any floor.
    `stdin_envp_mix2_mass_lower_certificate` is the caller: its environment
    depths must be large enough for the margin AND large enough to reach
    one particular fixed environment, and taking the larger of the two is
    the whole of how those are reconciled. -/
theorem Qpow_le_exp (x : Rat) (n m : Nat) (Hx0 : 0 ≤ x) (Hx1 : x ≤ 1)
    (Hnm : n ≤ m) : Qpow x m ≤ Qpow x n := by
  induction Hnm with
  | refl => exact Rat.le_refl
  | step _ ih =>
    rw [Qpow_succ]
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right Hx1 (Qpow_nonneg x _ Hx0)) ?_
    grind

theorem geo_gap_small_above (p eps : Rat) (k0 : Nat) (Hp0 : 0 < p) (Hp1 : p ≤ 1)
    (Heps : 0 < eps) :
    ∃ k : Nat, k0 ≤ k ∧ Qpow (1 - p) k ≤ eps := by
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hp0 Hp1 Heps
  refine ⟨max k0 k, Nat.le_max_left .., ?_⟩
  refine Rat.le_trans (Qpow_le_exp (1 - p) k (max k0 k) ?_ ?_ (Nat.le_max_right ..)) Hk
  · grind
  · grind

/- =========================================================================
   The length-< k prefix family, and what it weighs
   ========================================================================= -/

/-- Every standard input SHORTER than `k`, as a list.  The recursion is
    "the length-`k'` slice, then everything shorter", which is what makes
    the two facts wanted of it — that its members have the lengths
    claimed, and that it repeats nothing — one `List.append` argument each,
    on top of the enumeration facts `byte_lists` already has.

    It could equally have been `List.flatMap byte_lists (List.range k)`; the
    recursion is preferred because the sum below is then an induction on
    `k` with `qsum_app` at each step, and no lemma about folds over
    `List.range` is needed. -/
def short_inputs : Nat → List (List (BitVec 8))
  | 0 => []
  | k + 1 => byte_lists k ++ short_inputs k

/-- Its one computation rule, as a rewrite rule: `short_inputs` on a
    successor is the slice of that length followed by the shorter family. -/
theorem short_inputs_succ (k : Nat) :
    short_inputs (k + 1) = byte_lists k ++ short_inputs k := rfl

theorem short_inputs_In_length : ∀ (k : Nat) (s : List (BitVec 8)),
    s ∈ short_inputs k → s.length < k := by
  intro k
  induction k with
  | zero => intro s Hs; cases Hs
  | succ k ih =>
    intro s Hs
    rw [short_inputs_succ] at Hs
    rcases List.mem_append.mp Hs with h | h
    · rw [byte_lists_In_length k s h]; omega
    · have := ih s h; omega

/-- ... and CONVERSELY it misses nothing shorter than `k`.  The witness
    family does not need this — a witness only has to be admissible and to
    weigh what is claimed — but `stdin_geometric_mass_not_attained` does:
    to show a finite list falls short of the mass one has to place that
    list INSIDE the family, and this is what puts it there. -/
theorem short_inputs_complete : ∀ (k : Nat) (s : List (BitVec 8)),
    s.length < k → s ∈ short_inputs k := by
  intro k
  induction k with
  | zero => intro s Hlen; omega
  | succ k ih =>
    intro s Hlen
    rw [short_inputs_succ]
    rcases Nat.lt_or_ge s.length k with h | h
    · exact List.mem_append.mpr (Or.inr (ih s h))
    · refine List.mem_append.mpr (Or.inl ?_)
      have hlen : s.length = k := by omega
      rw [← hlen]
      exact byte_lists_complete s

/-- ... and it repeats nothing: the two halves are duplicate-free already,
    and they are disjoint because a member of the first has length exactly
    `k'` while a member of the second is shorter.  The length is what
    separates the slices, which is the same observation the enumeration's
    own `List.NoDup` proof makes about first bytes. -/
theorem short_inputs_nodup : ∀ k, (short_inputs k).Nodup := by
  intro k
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    rw [short_inputs_succ, List.nodup_append]
    refine ⟨byte_lists_nodup k, ih, ?_⟩
    intro a Ha b Hb hab
    have h1 := byte_lists_In_length k a Ha
    have h2 := short_inputs_In_length k b Hb
    rw [← hab, h1] at h2
    exact absurd h2 (Nat.lt_irrefl k)

/-- THE WITNESS FAMILY: over a fixed launch-time environment, one record
    per standard input shorter than `k`.  It is admissible —
    duplicate-free on cores — and its weight is computed exactly below.

    Records rather than cores, because the certificate is about the lists
    `Measure.weight_bound_T` quantifies over; `core_input` is the same
    canonical embedding the finite-support witness uses, and the same
    caveat applies unchanged: these records are NOT claimed valid or
    rejected by anything. -/
def geo_lower_witness (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (k : Nat) : List FinProcInput :=
  List.map (fun s => core_input (FinCore.mkFinCore argv envp fs s)) (short_inputs k)

/-- Its cores are the wrapped standard inputs, by `core_input`'s section
    law — which is the form every sum below is taken in. -/
theorem map_fin_core_geo_lower_witness (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (k : Nat) :
    List.map fin_core (geo_lower_witness argv envp fs k) =
      List.map (FinCore.mkFinCore argv envp fs) (short_inputs k) := by
  rw [geo_lower_witness, List.map_map]
  apply List.map_congr_left
  intro s _
  exact fin_core_core_input _

theorem geo_lower_witness_nodup (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (k : Nat) :
    (List.map fin_core (geo_lower_witness argv envp fs k)).Nodup := by
  rw [map_fin_core_geo_lower_witness]
  apply NoDup_map_inj
  · intro x y _ _ Heq
    exact congrArg FinCore.core_stdin Heq
  · exact short_inputs_nodup k

/-- The partial sum of the geometric series over LENGTHS, as a recursion so
    that it is a rational a task can write down and not a limit.
    `geo_prefix_sum_closed` is the telescoping identity that turns it into
    the closed form the plan and the header quote. -/
def geo_prefix_sum (p : Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => p * Qpow (1 - p) k + geo_prefix_sum p k

/-- Its computation rule on a successor. -/
theorem geo_prefix_sum_succ (p : Rat) (k : Nat) :
    geo_prefix_sum p (k + 1) = p * Qpow (1 - p) k + geo_prefix_sum p k := rfl

/-- The identity needs NO side condition on `p`, and saying so is the point
    of stating it separately: the arithmetic of the geometric sum is
    unconditional, and every hypothesis this file attaches to the lower
    certificate is attached for a different reason (choosing a `k`, in
    `geo_gap_small`).  Reading the two apart is how one can tell which of
    them is load-bearing where. -/
theorem geo_prefix_sum_closed (p : Rat) (k : Nat) :
    geo_prefix_sum p k = 1 - Qpow (1 - p) k := by
  induction k with
  | zero =>
    show (0 : Rat) = 1 - Qpow (1 - p) 0
    rw [Qpow_0]
    grind
  | succ k ih =>
    rw [geo_prefix_sum_succ, ih, Qpow_succ]
    grind

/-- A FULL length-`n` slice weighs exactly `p * (1 - p) ^ n`.  This is
    `stdin_geometric_slice_bound_attained`'s content on the CORE side,
    factored out because the prefix family is a concatenation of full
    slices and the induction below needs one block at a time.  Both halves
    are already proved: every core in a slice weighs the same
    (`qsum_const`), and the count against the `(1 / 256) ^ n` cancels
    (`geo_slice_total`). -/
theorem qsum_full_slice (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (n : Nat) :
    qsum (geo_weight p argv envp fs)
        (List.map (FinCore.mkFinCore argv envp fs) (byte_lists n)) =
      p * Qpow (1 - p) n := by
  rw [qsum_const _ _ (geo_point p n) ?_]
  · rw [List.length_map, byte_lists_length, geo_slice_total]
  · intro c Hc
    obtain ⟨s, Hs, rfl⟩ := List.mem_map.mp Hc
    rw [geo_weight_match, byte_lists_In_length n s Hs]

/-- ... and so the whole prefix family weighs the partial sum: block by
    block, with `qsum_app` splitting off one slice per step.  Nothing is
    approximated here — this is an equality, and the only inequality in the
    certificate below is the choice of `k`. -/
theorem qsum_short_inputs (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (k : Nat) :
    qsum (geo_weight p argv envp fs)
        (List.map (FinCore.mkFinCore argv envp fs) (short_inputs k)) =
      geo_prefix_sum p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [short_inputs_succ, List.map_append, qsum_app, ih, qsum_full_slice,
      geo_prefix_sum_succ]

/- =========================================================================
   The lower certificate for `stdin_geometric`
   ========================================================================= -/

/-- THE WITNESS, at each `k`: an admissible list weighing exactly
    `1 - (1 - p_stop) ^ k`.

    This is the half of the certificate pair that
    `stdin_geometric_mass_upper` left open, and the target is
    `1 - (1 - p_stop) ^ k` rather than the declared mass `1` because the
    mass is not available: for `p_stop < 1` the space holds infinitely many
    cores of positive weight and every admissible list is finite, so no
    list attains it — `stdin_geometric_mass_not_attained`, below, which is
    the converse of this lemma and is proved from the same family.  What a
    list CAN do is omit only the tail past length `k`, and
    `(1 - p_stop) ^ k` is exactly that tail.

    No hypothesis beyond the constructor's own is needed HERE, and that is
    deliberate — the equality is unconditional arithmetic.  The strictness
    enters one lemma later, where a `k` has to be chosen to meet a
    target. -/
theorem stdin_geometric_mass_lower_witness (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (k : Nat) :
    (List.map fin_core (geo_lower_witness argv envp fs k)).Nodup ∧
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
        (geo_lower_witness argv envp fs k) = 1 - Qpow (1 - p) k := by
  refine ⟨geo_lower_witness_nodup argv envp fs k, ?_⟩
  show core_sum (geo_weight p argv envp fs) (geo_lower_witness argv envp fs k) =
    1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_geo_lower_witness, qsum_short_inputs,
    geo_prefix_sum_closed]

/-- The same fact in the shape the certificate vocabulary uses, beside
    `finite_support_mass_lower_witness`: SOME admissible list weighs the
    target.  Both forms are exported because they are consumed differently
    — a task proving something about the witness wants it named, and a task
    quoting the certificate wants the existential. -/
theorem stdin_geometric_mass_lower_prefix (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (k : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l =
        1 - Qpow (1 - p) k :=
  ⟨geo_lower_witness argv envp fs k,
    stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 k⟩

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass MINUS that margin.  Together
    with `stdin_geometric_mass_upper` — no list ever exceeds the mass — this
    is the honest pair for `stdin_geometric`: the declared `1` is the least
    upper bound of the admissible partial sums, approached but never met.

    `0 < p_stop` IS A HYPOTHESIS OF THIS LEMMA AND NOT A TIGHTENING OF THE
    CONSTRUCTOR, and the distinction is not a matter of taste.  Moving it
    into `stdin_geometric` would invalidate every `stdin_geometric 0 …` a
    consumer may already have built, and would put the strictness where it
    is not used: everything above this lemma, the upper certificate
    included, holds at `p_stop = 0`.  Here it is used, exactly once, inside
    `geo_gap_small`, to choose the `k` whose tail is under `eps` — and
    `stdin_geometric_mass_lower_needs_positive` shows the conclusion is
    false without it. -/
theorem stdin_geometric_mass_lower_certificate (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (eps : Rat) (Hpos : 0 < p) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (stdin_geometric p argv envp fs Hp0 Hp1).cd_mass - eps ≤
        core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l := by
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hnd, Hsum⟩ :=
    stdin_geometric_mass_lower_prefix p argv envp fs Hp0 Hp1 k
  refine ⟨l, Hnd, ?_⟩
  rw [Hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  grind

/- =========================================================================... and the mass is a SUPREMUM and not a maximum
   ========================================================================= -/

/-- A list confined to standard inputs of length at most `n` weighs at most
    `1 - (1 - p_stop) ^ (n + 1)` — the partial sum at its own horizon.  It
    MISSES THE TAIL, and the tail is the whole point.

    The proof is the witness family read in the other direction.  The cores
    of such a list, once the ones missing the fixed launch-time environment
    are filtered away (they weigh nothing — `geo_weight_mismatch`, and
    `List.Nodup.filter` carries the duplicate-freedom across), all lie in
    `short_inputs (n + 1)` (`short_inputs_complete`); so `qsum_core_incl_le`
    bounds the list by the family, which `qsum_short_inputs` evaluates
    exactly.  Duplicate-freedom is where the hypothesis is spent, and it is
    spent in the same place it is spent everywhere else in this file:
    without it a list may name one core repeatedly and outweigh any
    enumeration of distinct cores. -/
theorem stdin_geometric_bound_by_max_length (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → f.fin_stdin.length ≤ n) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ≤
      1 - Qpow (1 - p) (n + 1) := by
  show core_sum (geo_weight p argv envp fs) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (geo_weight p argv envp fs) (matches_env argv envp fs) _
    (fun c Hc => by
      rw [geo_weight_mismatch p argv envp fs c (matches_env_false _ _ _ _ Hc)])]
  refine Rat.le_trans (qsum_core_incl_le (geo_weight p argv envp fs) _
    (List.map (FinCore.mkFinCore argv envp fs) (short_inputs (n + 1)))
    (geo_weight_nonneg p argv envp fs Hp0 Hp1)
    (List.Nodup.sublist List.filter_sublist Hnd) ?_) ?_
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    refine List.mem_map.mpr ⟨(fin_core f).core_stdin, ?_, ?_⟩
    · apply short_inputs_complete
      have := Hlen f Hf
      show f.fin_stdin.length < n + 1
      omega
    · exact (matches_env_true _ _ _ _ Hm).symm
  · rw [qsum_short_inputs, geo_prefix_sum_closed]
    exact Rat.le_refl

/-- ... AND THAT BOUND IS EXACTLY TIGHT, which is what makes the strictness
    below a fact about the distribution rather than an artefact of a lossy
    estimate: the witness family at `k = n + 1` is a list of standard
    inputs of length at most `n`, and it weighs the bound exactly.  So
    `1 - (1 - p_stop) ^ (n + 1)` is the most a list confined to that
    horizon can weigh, and it is also the least upper bound of what such
    lists weigh.

    The two conjuncts are the two halves of "the bound applies to this list
    and is met by it"; duplicate-freedom is `geo_lower_witness_nodup`,
    stated there rather than repeated here. -/
theorem stdin_geometric_bound_by_max_length_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (n : Nat) :
    (∀ f, f ∈ geo_lower_witness argv envp fs (n + 1) → f.fin_stdin.length ≤ n) ∧
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
        (geo_lower_witness argv envp fs (n + 1)) = 1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 (n + 1)).2⟩
  intro f Hf
  rw [geo_lower_witness] at Hf
  obtain ⟨s, Hs, rfl⟩ := List.mem_map.mp Hf
  show s.length ≤ n
  have := short_inputs_In_length (n + 1) s Hs
  omega

/-- THE CLAIM THE CERTIFICATE'S SHAPE RESTS ON, MECHANIZED: for
    `p_stop < 1` NO admissible list weighs the declared mass — every one of
    them weighs strictly less.

    Read against `stdin_geometric_mass_upper` (no list exceeds `1`) and
    `stdin_geometric_mass_lower_certificate` (some list beats `1 - eps`,
    for every `eps`), this is what makes the declared mass a SUPREMUM and
    not a maximum, and it is why the lower certificate had to be an
    approach.

    The `n` is the list's own longest standard input —
    `list_max` of the lengths, exactly the trick `geo_weight_cylinder_bound`
    uses to pick an enumeration depth, and the only place the FINITENESS of
    `Measure.weight_bound_T`'s lists is needed.  A list may be as long as it
    likes; what it cannot be is infinite, so it has a horizon, and beyond
    that horizon sits a positive tail (`Qpow_pos`) it does not collect.

    Only `p_stop < 1` is asked for, and the missing lower bound is not an
    oversight: at `p_stop = 0` the statement is true and obvious (every list
    weighs zero), so the family this rules out is the whole of
    `0 <= p_stop < 1` and not merely the open interval the header's
    discussion names.  At `p_stop = 1` it is false, and
    `geo_point_cd_mass_attained` is the list that refutes it. -/
theorem stdin_geometric_mass_not_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : p < 1) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l <
      (stdin_geometric p argv envp fs Hp0 Hp1).cd_mass := by
  show core_sum (geo_weight p argv envp fs) l < 1
  generalize hN : list_max (List.map (fun f => f.fin_stdin.length) l) = N
  have h1 : core_sum (geo_weight p argv envp fs) l ≤ 1 - Qpow (1 - p) (N + 1) :=
    stdin_geometric_bound_by_max_length p argv envp fs Hp0 Hp1 N l Hnd
      (fun f Hf => by
        have hin : f.fin_stdin.length ∈ List.map (fun g => g.fin_stdin.length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for: the declared mass is
    not ATTAINED.  `Rat.ne_of_lt` on the strict inequality — stated because
    "no admissible list weighs the mass" is how the claim is phrased
    everywhere it is used, and a consumer should not have to perform the
    conversion. -/
theorem stdin_geometric_mass_supremum_not_maximum (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : p < 1) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l =
        (stdin_geometric p argv envp fs Hp0 Hp1).cd_mass) :=
  Rat.ne_of_lt (stdin_geometric_mass_not_attained p argv envp fs Hp0 Hp1 Hlt l Hnd)

/- =========================================================================
   Non-vacuity: the family, and why the certificate asks for `0 < p_stop`
   ========================================================================= -/

/-- The family at `k = 1` is the single stopping core over the empty
    standard input — the `List.map` over `short_inputs 1` reduces to it, by
    conversion. -/
theorem geo_lower_witness_at_one (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) :
    geo_lower_witness argv envp fs 1 =
      [core_input (FinCore.mkFinCore argv envp fs [])] := rfl

/-- ... and it weighs `p_stop` exactly, which is what the abstract
    `1 - (1 - p_stop) ^ k` says at `k = 1` and is worth seeing on a
    concrete list: the whole certificate is the observation that this one
    core already carries `p_stop` of the mass, and that longer prefixes
    carry the rest. -/
theorem geo_lower_witness_at_one_weighs (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
      (geo_lower_witness argv envp fs 1) = p := by
  rw [(stdin_geometric_mass_lower_witness p argv envp fs Hp0 Hp1 1).2]
  rw [Qpow_succ, Qpow_0]
  grind

/-- At `p_stop = 0` every weight is zero — the degenerate member the
    constructor deliberately still admits. -/
theorem geo_weight_zero_at_zero_p (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) : geo_weight 0 argv envp fs c = 0 := by
  unfold geo_weight
  split
  · next _ =>
    unfold geo_point
    grind
  · next _ => rfl

/-- THE STRICTNESS IS LOAD-BEARING, pinned the way this file pins every
    other hypothesis it asks for.  At `p_stop = 0` EVERY admissible list
    weighs zero — not merely the witness family, which is why the first
    conjunct quantifies over all of them — and the declared mass is still
    `1`, so no list comes within `1 / 2` of it.  The certificate above is
    therefore false at `p_stop = 0`, and its hypothesis is not inherited
    caution.

    `stdin_geometric_mass_upper` remains true here, and that asymmetry is
    the honest content of the pair: an upper bound survives degeneracy, a
    lower one does not. -/
theorem stdin_geometric_mass_lower_needs_positive
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) :
    (∀ l : List FinProcInput,
      core_sum (stdin_geometric 0 argv envp fs (Rat.le_refl : (0 : Rat) ≤ 0) Qle_0_1).cd_weight
        l = 0) ∧
      ¬ ((stdin_geometric 0 argv envp fs (Rat.le_refl : (0 : Rat) ≤ 0) Qle_0_1).cd_mass -
        (1 : Rat) / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show geo_weight 0 argv envp fs c = 0
    exact geo_weight_zero_at_zero_p argv envp fs c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

/- =========================================================================
   A WORKED DISTRIBUTION: named cores over a geometric background
   ========================================================================= -/

/-- The worked task's fixed launch-time inputs: a program invoked as
    `["wc"]`, with no environment and an empty file system.  Only argv is
    given anything to look at, and that is deliberate — these three are the
    components `stdin_geometric` holds FIXED, so their content is
    irrelevant to every number below, and writing something into one of
    them makes it visible that they are a choice.  As at `core_input`,
    nothing here is claimed VALID (`FinInput.valid_fin_input`); a task that
    cares supplies its own. -/
def worked_argv : List (List (BitVec 8)) :=
  [[BitVec.ofInt 8 119, BitVec.ofInt 8 99]]

def worked_envp : List (List (BitVec 8)) := []

def worked_fs : Fs.Fs := []

/-- A core of this family: the fixed environment, and a standard input.
    Every core named below goes through it, which is what puts the named
    cores INSIDE the geometric background's support rather than beside
    it. -/
def worked_core (s : List (BitVec 8)) : FinCore :=
  FinCore.mkFinCore worked_argv worked_envp worked_fs s

def worked_nul : BitVec 8 := BitVec.ofInt 8 0

def worked_byte_A : BitVec 8 := BitVec.ofInt 8 65

/-- The three cores the author considers important: the empty standard
    input, and the two that begin with a NUL byte.  The latter two are what
    the fire set will be, and they share the prefix `[0]` — not a
    coincidence but the point, since a prefix is what
    `stdin_geometric_bound` charges against. -/
def worked_core_empty : FinCore := worked_core []

def worked_core_nul : FinCore := worked_core [worked_nul]

def worked_core_nul_a : FinCore := worked_core [worked_nul, worked_byte_A]

/-- ... and a fourth, named later in the section: the standard input
    `["A"]`, which is neither a fire core nor one of the entries. -/
def worked_core_a : FinCore := worked_core [worked_byte_A]

/-- The three named cores are pairwise distinct, read off their standard
    inputs.  These are the facts every concrete computation below spends,
    and they are stated because `core_indicator`'s two rules want them as
    hypotheses rather than as `decide`-facts. -/
theorem worked_core_nul_ne_empty : worked_core_nul ≠ worked_core_empty := by
  intro h
  have h' : [worked_nul] = ([] : List (BitVec 8)) := congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

theorem worked_core_nul_a_ne_empty : worked_core_nul_a ≠ worked_core_empty := by
  intro h
  have h' : [worked_nul, worked_byte_A] = ([] : List (BitVec 8)) :=
    congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

theorem worked_core_nul_ne_nul_a : worked_core_nul ≠ worked_core_nul_a := by
  intro h
  have h' : [worked_nul] = [worked_nul, worked_byte_A] := congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

theorem worked_core_a_ne_empty : worked_core_a ≠ worked_core_empty := by
  intro h
  have h' : [worked_byte_A] = ([] : List (BitVec 8)) := congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

theorem worked_core_a_ne_nul : worked_core_a ≠ worked_core_nul := by
  intro h
  have h' : [worked_byte_A] = [worked_nul] := congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

theorem worked_core_a_ne_nul_a : worked_core_a ≠ worked_core_nul_a := by
  intro h
  have h' : [worked_byte_A] = [worked_nul, worked_byte_A] :=
    congrArg FinCore.core_stdin h
  exact absurd h' (by decide)

/-- Half the foreground on the empty input, a quarter on each NUL-prefixed
    one: a declared foreground mass of `1`. -/
def worked_entries : List (FinCore × Rat) :=
  [(worked_core_empty, (1 : Rat) / 2), (worked_core_nul, (1 : Rat) / 4),
   (worked_core_nul_a, (1 : Rat) / 4)]

theorem worked_entries_nonneg : ∀ e, e ∈ worked_entries → 0 ≤ e.2 := by
  intro e He
  simp only [worked_entries, List.mem_cons, List.not_mem_nil, or_false] at He
  rcases He with rfl | rfl | rfl
  all_goals grind

def worked_foreground : CoreDistribution :=
  finite_support worked_entries worked_entries_nonneg

/-- The background's stop weight.  `1 / 8` is an authored choice like every
    other number here: it makes a typical standard input a few bytes long,
    and it is far enough from both `0` and `1` that neither degenerate case
    is being exercised by accident. -/
def worked_p : Rat := (1 : Rat) / 8

theorem worked_p_nonneg : 0 ≤ worked_p := by unfold worked_p; grind

theorem worked_p_le_1 : worked_p ≤ 1 := by unfold worked_p; grind

def worked_background : CoreDistribution :=
  stdin_geometric worked_p worked_argv worked_envp worked_fs worked_p_nonneg
    worked_p_le_1

/-- The two shares.  They are written as named `Qle` facts rather than
    inlined because `cd_scale` takes the proof as an argument, and a task
    author reading this wants to see what that costs: two lines, once. -/
theorem worked_share_named_nonneg : (0 : Rat) ≤ 1 / 4 := by grind

theorem worked_share_background_nonneg : (0 : Rat) ≤ 3 / 4 := by grind

/-- THE DISTRIBUTION: a quarter on the named cores, three quarters on the
    geometric background.  This is the probabilist's mixture written the
    way `cd_mix2`'s comment describes it — two `cd_scale`s and one
    `cd_mix2`, with how much of each and what to do with the sum kept as
    separate, visible decisions. -/
def worked_cd : CoreDistribution :=
  cd_mix2 (cd_scale ((1 : Rat) / 4) worked_share_named_nonneg worked_foreground)
    (cd_scale ((3 : Rat) / 4) worked_share_background_nonneg worked_background)

/-- The foreground's declared mass is `1` — the three entries as written.
    `entries_mass` is a fold over a literal list, so this is arithmetic on
    three numerals once the fold is unfolded, not a decision about `Q`. -/
theorem worked_foreground_mass : worked_foreground.cd_mass = 1 := by
  show entries_mass worked_entries = 1
  show (1 / 2 + (1 / 4 + (1 / 4 + 0))) = 1
  grind

/-- The background's is `1` by `stdin_geometric`'s own declaration — an
    equality and not merely an implication, because the constructor writes
    the numeral. -/
theorem worked_background_mass : worked_background.cd_mass = 1 := rfl

/-- ... so the mixture declares `1`, and the shares are what make it come
    out that way.  The `b * M` of the obligation is therefore `b` up to
    equality, which is why the demonstrations below can quote a multiplier
    and a bound as one number. -/
theorem worked_mass_is_one : worked_cd.cd_mass = 1 := by
  show (1 / 4) * worked_foreground.cd_mass + (3 / 4) * worked_background.cd_mass = 1
  rw [worked_foreground_mass, worked_background_mass]
  grind

/-- The module, over a distribution built from three combinators instead of
    one: the two weight obligations are still discharged by the library's
    two lemmas, and `M_nonneg` by composing the mass lemmas of exactly the
    combinators the distribution was assembled from, with no arithmetic
    written here.  That is the claim the header's design section makes, at
    the size of distribution a task actually ships. -/
def Worked_D : DISTRIBUTION where
  w := cd_lift worked_cd
  M := worked_cd.cd_mass
  w_nonneg := cd_lift_nonneg worked_cd
  M_nonneg := by
    show 0 ≤ worked_cd.cd_mass
    unfold worked_cd
    refine cd_mix2_mass_nonneg _ _ (cd_scale_mass_nonneg _ _ _ ?_)
      (cd_scale_mass_nonneg _ _ _ ?_)
    · unfold worked_foreground
      exact finite_support_mass_nonneg _ _
    · unfold worked_background
      exact stdin_geometric_mass_nonneg _ _ _ _ _ _
  w_core_blind := cd_lift_core_blind worked_cd

/- =========================================================================... and the recipe for discharging `Measure.weight_bound_T` with it
   ========================================================================= -/

/-- THE FIRE SET, as a predicate on cores.  Two cores named explicitly,
    because `entries_restrict` has to COMPUTE and these two are what the
    entry list names.  A larger support would use a predicate that
    DESCRIBES the set rather than listing it — "the standard input begins
    with a NUL byte" is decidable too, and `finite_support_bound_subset`
    takes any `Bool`-valued `P` whatever. -/
def worked_is_fire (c : FinCore) : Bool :=
  if decide (c = worked_core_nul) then true
  else if decide (c = worked_core_nul_a) then true else false

/-- Its three values on the names that matter, by evaluation. -/
theorem worked_is_fire_empty : worked_is_fire worked_core_empty = false := by
  unfold worked_is_fire
  rw [ite_eq_right (by simp [Ne.symm worked_core_nul_ne_empty]),
    ite_eq_right (by simp [Ne.symm worked_core_nul_a_ne_empty])]

theorem worked_is_fire_nul : worked_is_fire worked_core_nul = true := by
  unfold worked_is_fire
  rw [ite_eq_left (by simp)]

theorem worked_is_fire_nul_a : worked_is_fire worked_core_nul_a = true := by
  unfold worked_is_fire
  rw [ite_eq_right (by simp [Ne.symm worked_core_nul_ne_nul_a]), ite_eq_left (by simp)]

theorem worked_is_fire_a : worked_is_fire worked_core_a = false := by
  unfold worked_is_fire
  rw [ite_eq_right (by simp [worked_core_a_ne_nul]),
    ite_eq_right (by simp [worked_core_a_ne_nul_a])]

/-- The refinement's payoff, computed: the fire entries declare `1 / 2`
    between them, against the support's own `1`.  Charging the fire set the
    whole declared mass would double the foreground half of the bound for
    nothing. -/
theorem worked_restricted_mass :
    entries_mass (entries_restrict worked_is_fire worked_entries) = (1 : Rat) / 2 := by
  have hfilter : entries_restrict worked_is_fire worked_entries =
      [(worked_core_nul, (1 : Rat) / 4), (worked_core_nul_a, (1 : Rat) / 4)] := by
    unfold entries_restrict worked_entries
    rw [List.filter_cons, worked_is_fire_empty, List.filter_cons,
      worked_is_fire_nul, List.filter_cons, worked_is_fire_nul_a, List.filter_nil]
    rfl
  rw [hfilter]
  show (1 / 4 + (1 / 4 + 0)) = 1 / 2
  grind

/-- THE CEILING, as an exact rational.  The two component bounds are a
    restricted mass (`1 / 2`) and a cylinder mass over the one-byte prefix
    `[0]` (`7 / 2048`); scaled by the two shares and added, they come to
    `1045 / 8192`.

    It is stated as an equality before it is used, so that the number in
    the demonstrations is visibly WHAT THE COMPOSITION YIELDS and not a
    convenient rounding of it.  The difference matters, because
    `worked_ceiling_slack` below measures the remaining slack against
    exactly this number. -/
theorem worked_fire_ceiling :
    (1 / 4) * entries_mass (entries_restrict worked_is_fire worked_entries) +
      (3 / 4) * stdin_geometric_cylinder_mass worked_p [worked_nul] =
      (1045 : Rat) / 8192 := by
  rw [worked_restricted_mass]
  unfold stdin_geometric_cylinder_mass geo_mass worked_p
  show (1 / 4) * (1 / 2) + (3 / 4) * Qpow ((1 - 1 / 8) * (1 / 256)) 1 = 1045 / 8192
  rw [Qpow_succ, Qpow_0]
  grind

/-- THE RECIPE, steps two and three: every admissible list drawn from the
    fire set weighs at most the ceiling.

    Read the proof as the pattern to copy.  `← worked_fire_ceiling` puts the
    goal into the shape the composition lemmas produce — a sum of two
    scaled component bounds — and then there is one `cd_mix2_bound`, one
    `cd_scale_bound` per component, and one library bound under each.
    Neither component bound is at a declared mass: the foreground is
    charged the restricted mass and the background a cylinder mass, and
    they compose anyway, because `cd_scale_bound` and `cd_mix2_bound` are
    stated over arbitrary rationals.

    The two side conditions are where the fire set is spent, and they are
    the only places any thinking happens.  For the foreground: a fire core
    satisfies `worked_is_fire`, by the three evaluation lemmas.  For the
    background: a fire core LIES IN THE CYLINDER over `[0]` —
    `worked_core_nul` is that prefix followed by nothing,
    `worked_core_nul_a` by one byte — so the existential is discharged by
    naming the extension.  Both are conversions once the witness is given,
    which is what it means for a fire set to have been described in the
    library's own vocabulary. -/
theorem worked_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) :
    core_sum worked_cd.cd_weight l ≤ (1045 : Rat) / 8192 := by
  rw [← worked_fire_ceiling]
  refine cd_mix2_bound
    (cd_scale ((1 : Rat) / 4) worked_share_named_nonneg worked_foreground)
    (cd_scale ((3 : Rat) / 4) worked_share_background_nonneg worked_background) l
    ((1 : Rat) / 4 * entries_mass (entries_restrict worked_is_fire worked_entries))
    ((3 : Rat) / 4 * stdin_geometric_cylinder_mass worked_p [worked_nul]) ?_ ?_
  · refine cd_scale_bound _ _ _ _ _ ?_
    exact finite_support_bound_subset worked_is_fire worked_entries
      worked_entries_nonneg l Hnd (fun f Hf => by
        rcases Hfire f Hf with h | h
        · rw [h]; exact worked_is_fire_nul
        · rw [h]; exact worked_is_fire_nul_a)
  · refine cd_scale_bound _ _ _ _ _ ?_
    exact stdin_geometric_bound worked_p worked_argv worked_envp worked_fs
      worked_p_nonneg worked_p_le_1 [worked_nul] l Hnd (fun f Hf => by
        rcases Hfire f Hf with h | h
        · exact ⟨[], by rw [h]; rfl⟩
        · exact ⟨[worked_byte_A], by rw [h]; rfl⟩)

/-- THE RECIPE, step four: from the library's bound to
    `Measure.weight_bound_T` itself, at ANY multiplier the ceiling fits
    under.

    Three lines, and each is one of the crossings this library exists to
    make cheap.  `core_sum_cd_lift` carries `Measure.sum_weights` of the
    lifted weight to `core_sum` — an equality by conversion, so the rewrite
    is bookkeeping and not a transport.  The classifier hypothesis is spent
    turning the obligation's "every record in `l` is rejected" into the
    fire-set membership `worked_fire_bound` wants.  And `worked_mass_is_one`
    turns `b * M` into `b`.

    Quantifying over `b` rather than fixing one is what makes the two
    demonstrations below a single proof, and it puts the ceiling where a
    reader can see it: the hypothesis `1045 / 8192 <= b` IS the statement
    that this route goes no lower. -/
theorem worked_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a)
    (Hb : (1045 : Rat) / 8192 ≤ b) :
    weight_bound_T C Worked_D.w Worked_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift worked_cd) l ≤ b * worked_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (worked_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [worked_mass_is_one, Rat.mul_one]
  exact Hb

/-- DEMONSTRATION ONE, at a round multiplier a task would plausibly
    declare: a classifier whose reject set is this fire set carries at most
    a quarter of the distribution's mass.  The whole proof is the recipe
    plus one comparison between literals. -/
theorem worked_weight_bound_T_quarter (C : Image)
    (Hfire : ∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) :
    weight_bound_T C Worked_D.w Worked_D.M ((1 : Rat) / 4) := by
  refine worked_weight_bound_T_of C (1 / 4) Hfire ?_
  grind

/-- DEMONSTRATION TWO, at the tightest multiplier these bounds reach.  The
    same recipe, and the arithmetic step has become reflexivity — which is
    the honest way to say that there is nothing left to give away HERE.
    Where the remaining slack is, and why it is not zero, is
    `worked_ceiling_slack`. -/
theorem worked_weight_bound_T_ceiling (C : Image)
    (Hfire : ∀ f, rejects C f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) :
    weight_bound_T C Worked_D.w Worked_D.M ((1045 : Rat) / 8192) :=
  worked_weight_bound_T_of C (1045 / 8192) Hfire Rat.le_refl

/-- The fire set as an admissible list: one canonical record per fire core,
    through `core_input`.  As everywhere else in this file these records
    are not claimed valid and not claimed rejected by anything — exhibiting
    them is arithmetic, not a claim about a classifier. -/
def worked_fire_list : List FinProcInput :=
  List.map core_input [worked_core_nul, worked_core_nul_a]

/-- The foreground's weight at the three named cores, and at the fourth:
    the entry list read at a core.  Four evaluations, each of which is the
    `entries_weight` fixpoint unfolded and the indicators resolved. -/
theorem worked_foreground_weight_empty :
    worked_foreground.cd_weight worked_core_empty = (1 : Rat) / 2 := by
  show core_indicator worked_core_empty (1 / 2) worked_core_empty +
    (core_indicator worked_core_nul (1 / 4) worked_core_empty +
      (core_indicator worked_core_nul_a (1 / 4) worked_core_empty + 0)) = 1 / 2
  rw [core_indicator_hit,
    core_indicator_miss _ _ _ worked_core_nul_ne_empty,
    core_indicator_miss _ _ _ worked_core_nul_a_ne_empty]
  grind

theorem worked_foreground_weight_nul :
    worked_foreground.cd_weight worked_core_nul = (1 : Rat) / 4 := by
  show core_indicator worked_core_empty (1 / 2) worked_core_nul +
    (core_indicator worked_core_nul (1 / 4) worked_core_nul +
      (core_indicator worked_core_nul_a (1 / 4) worked_core_nul + 0)) = 1 / 4
  rw [core_indicator_miss _ _ _ (Ne.symm worked_core_nul_ne_empty),
    core_indicator_hit,
    core_indicator_miss _ _ _ (Ne.symm worked_core_nul_ne_nul_a)]
  grind

theorem worked_foreground_weight_nul_a :
    worked_foreground.cd_weight worked_core_nul_a = (1 : Rat) / 4 := by
  show core_indicator worked_core_empty (1 / 2) worked_core_nul_a +
    (core_indicator worked_core_nul (1 / 4) worked_core_nul_a +
      (core_indicator worked_core_nul_a (1 / 4) worked_core_nul_a + 0)) = 1 / 4
  rw [core_indicator_miss _ _ _ (Ne.symm worked_core_nul_a_ne_empty),
    core_indicator_miss _ _ _ worked_core_nul_ne_nul_a,
    core_indicator_hit]
  grind

theorem worked_foreground_weight_a :
    worked_foreground.cd_weight worked_core_a = 0 := by
  show core_indicator worked_core_empty (1 / 2) worked_core_a +
    (core_indicator worked_core_nul (1 / 4) worked_core_a +
      (core_indicator worked_core_nul_a (1 / 4) worked_core_a + 0)) = 0
  rw [core_indicator_miss _ _ _ (Ne.symm worked_core_a_ne_empty),
    core_indicator_miss _ _ _ (Ne.symm worked_core_a_ne_nul),
    core_indicator_miss _ _ _ (Ne.symm worked_core_a_ne_nul_a)]
  grind

/-- The background's weight at the same cores: the geometric point mass at
    the standard input's length, which is what `geo_weight_match` says and
    all the work there is. -/
theorem worked_background_weight_empty :
    worked_background.cd_weight worked_core_empty = worked_p := by
  show geo_weight worked_p worked_argv worked_envp worked_fs worked_core_empty =
    worked_p
  unfold worked_core_empty worked_core
  rw [geo_weight_match]
  show worked_p * geo_mass worked_p 0 = worked_p
  unfold geo_mass
  rw [Qpow_0]
  grind

theorem worked_background_weight_nul :
    worked_background.cd_weight worked_core_nul = worked_p * ((1 - worked_p) * (1 / 256)) := by
  show geo_weight worked_p worked_argv worked_envp worked_fs worked_core_nul =
    worked_p * ((1 - worked_p) * (1 / 256))
  unfold worked_core_nul worked_core
  rw [geo_weight_match]
  unfold geo_point geo_mass
  show worked_p * Qpow ((1 - worked_p) * (1 / 256)) 1 =
    worked_p * ((1 - worked_p) * (1 / 256))
  rw [Qpow_succ, Qpow_0]
  grind

theorem worked_background_weight_nul_a :
    worked_background.cd_weight worked_core_nul_a =
      worked_p * (((1 - worked_p) * (1 / 256)) * ((1 - worked_p) * (1 / 256))) := by
  show geo_weight worked_p worked_argv worked_envp worked_fs worked_core_nul_a =
    worked_p * (((1 - worked_p) * (1 / 256)) * ((1 - worked_p) * (1 / 256)))
  unfold worked_core_nul_a worked_core
  rw [geo_weight_match]
  unfold geo_point geo_mass
  show worked_p * Qpow ((1 - worked_p) * (1 / 256)) 2 =
    worked_p * (((1 - worked_p) * (1 / 256)) * ((1 - worked_p) * (1 / 256)))
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

theorem worked_background_weight_a :
    worked_background.cd_weight worked_core_a = worked_p * ((1 - worked_p) * (1 / 256)) := by
  show geo_weight worked_p worked_argv worked_envp worked_fs worked_core_a =
    worked_p * ((1 - worked_p) * (1 / 256))
  unfold worked_core_a worked_core
  rw [geo_weight_match]
  unfold geo_point geo_mass
  show worked_p * Qpow ((1 - worked_p) * (1 / 256)) 1 =
    worked_p * ((1 - worked_p) * (1 / 256))
  rw [Qpow_succ, Qpow_0]
  grind

/-- The mixture's weight at the four named cores, in numbers.  Each is
    `cd_mix2`'s sum of the two scaled component weights, with the four
    evaluations above substituted. -/
theorem worked_cd_weight_empty : worked_cd.cd_weight worked_core_empty = (7 : Rat) / 32 := by
  show (1 / 4) * worked_foreground.cd_weight worked_core_empty +
    (3 / 4) * worked_background.cd_weight worked_core_empty = 7 / 32
  rw [worked_foreground_weight_empty, worked_background_weight_empty]
  unfold worked_p
  grind

theorem worked_cd_weight_nul :
    worked_cd.cd_weight worked_core_nul = (4117 : Rat) / 65536 := by
  show (1 / 4) * worked_foreground.cd_weight worked_core_nul +
    (3 / 4) * worked_background.cd_weight worked_core_nul = 4117 / 65536
  rw [worked_foreground_weight_nul, worked_background_weight_nul]
  unfold worked_p
  grind

theorem worked_cd_weight_nul_a :
    worked_cd.cd_weight worked_core_nul_a = (8388755 : Rat) / 134217728 := by
  show (1 / 4) * worked_foreground.cd_weight worked_core_nul_a +
    (3 / 4) * worked_background.cd_weight worked_core_nul_a = 8388755 / 134217728
  rw [worked_foreground_weight_nul_a, worked_background_weight_nul_a]
  unfold worked_p
  grind

theorem worked_cd_weight_a :
    worked_cd.cd_weight worked_core_a = (21 : Rat) / 65536 := by
  show (1 / 4) * worked_foreground.cd_weight worked_core_a +
    (3 / 4) * worked_background.cd_weight worked_core_a = 21 / 65536
  rw [worked_foreground_weight_a, worked_background_weight_a]
  unfold worked_p
  grind

/-- The record list's own core list, written out: the weight sums below are
    over `[nul, nul_a]` and `[empty, a]`, in that order. -/
theorem map_fin_core_worked_fire_list :
    List.map fin_core worked_fire_list = [worked_core_nul, worked_core_nul_a] := by
  unfold worked_fire_list
  rw [List.map_map]
  have h : (fin_core ∘ core_input) = id := by
    funext x; exact fin_core_core_input x
  rw [h, List.map_id]

/-- HOW MUCH OF THE CEILING IS REAL.  The fire set's own two records form
    an admissible list, and they weigh `16820371 / 134217728` — a shade
    over 98 per cent of the `1045 / 8192` the composition charges, and
    strictly under it.

    Three conjuncts, each load-bearing.  The first says the list is
    admissible, so `worked_fire_bound` applies to it and the comparison is
    between comparable things.  The second is the exact weight, computed on
    literals this file wrote.  The third is the strictness: the ceiling is
    NOT attained, so the route does carry slack.  All of that slack is in
    the background half — the cylinder over `[0]` holds every core whose
    standard input begins with a NUL byte, the fire set names two of them,
    and every other continuation of every length is charged for and absent.

    What this does NOT say is that no smaller multiplier is provable, and
    that is the misreading the header's warning at the geometric lower
    certificate names.  A task that sums its two cores exactly gets a bound
    near `16820371 / 134217728` and is entitled to it.  This lemma measures
    THIS ROUTE's slack, which is a property of the proof and not of the
    distribution. -/
theorem worked_ceiling_slack :
    (List.map fin_core worked_fire_list).Nodup ∧
      core_sum worked_cd.cd_weight worked_fire_list = (16820371 : Rat) / 134217728 ∧
      ¬ ((1045 : Rat) / 8192 ≤ 16820371 / 134217728) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_fin_core_worked_fire_list]
    exact List.nodup_cons.mpr ⟨by simp [worked_core_nul_ne_nul_a],
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  · show worked_cd.cd_weight worked_core_nul +
      (worked_cd.cd_weight worked_core_nul_a + 0) = 16820371 / 134217728
    rw [worked_cd_weight_nul, worked_cd_weight_nul_a]
    grind
  · grind

/- =========================================================================
   The same recipe, indexed by a predicate instead of a classifier
   ========================================================================= -/

/-- THE PREDICATE TWIN of `worked_weight_bound_T_of`, and the whole of what
    changes: `rejects C f` becomes `valid_fin_input f ∧ ¬ P f`.  Nothing
    else in the recipe moves — the same `worked_fire_bound`, the same
    `worked_mass_is_one`, the same ceiling — because the classifier never
    entered the arithmetic in the first place.  It entered as one
    hypothesis, and this is that hypothesis rewritten.

    Its use is the gated size measure's per-slice bound.  The complement of
    a slice is what a consumer bounds; the bound on the complement is what
    it turns into a lower bound on the slice's own mass; and a slice is a
    `GatedSize.slice_accept` or `GatedSize.slice_rest`, which is a predicate
    on records and not a classifier's reject set, so the classifier-indexed
    form would not have typed.

    The proof is `weight_bound_pred_T_of_core_bound` with the fire set
    named and `worked_fire_bound` handed over. -/
theorem worked_weight_bound_pred_T_of (P : FinProcInput → Prop) (b : Rat)
    (Hfire : ∀ f, valid_fin_input f → ¬ P f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a)
    (Hb : (1045 : Rat) / 8192 ≤ b) :
    GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M b := by
  refine weight_bound_pred_T_of_core_bound worked_cd P
    (fun c => c = worked_core_nul ∨ c = worked_core_nul_a) (1045 / 8192) b ?_ ?_ ?_
  · exact Hfire
  · intro l Hnd Hall
    exact worked_fire_bound l Hnd Hall
  · rw [worked_mass_is_one, Rat.mul_one]
    exact Hb

/-- The predicate twin of `worked_weight_bound_T_quarter`: the same round
    multiplier a task would plausibly declare, over a slice predicate
    instead of a classifier.  One comparison between literals, as
    before. -/
theorem worked_weight_bound_pred_T_quarter (P : FinProcInput → Prop)
    (Hfire : ∀ f, valid_fin_input f → ¬ P f →
      fin_core f = worked_core_nul ∨ fin_core f = worked_core_nul_a) :
    GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M ((1 : Rat) / 4) := by
  refine worked_weight_bound_pred_T_of P (1 / 4) Hfire ?_
  grind

/-- Two records whose cores are outside the fire set, as an admissible
    list.  As at `worked_fire_list`, these are not claimed valid and not
    claimed outside anything — exhibiting them is arithmetic. -/
def worked_off_fire_list : List FinProcInput :=
  List.map core_input [worked_core_empty, worked_core_a]

theorem map_fin_core_worked_off_fire_list :
    List.map fin_core worked_off_fire_list = [worked_core_empty, worked_core_a] := by
  unfold worked_off_fire_list
  rw [List.map_map]
  have h : (fin_core ∘ core_input) = id := by
    funext x; exact fin_core_core_input x
  rw [h, List.map_id]

/-- THE FIRE-SET HYPOTHESIS IS LOAD-BEARING, pinned the way
    `worked_ceiling_slack` pins the slack.  Three conjuncts, each doing
    work.  The list is admissible, so it is one of the lists the obligation
    quantifies over.  NEITHER core is a fire core, computed through
    `worked_is_fire` itself rather than argued in prose.  And the two
    together weigh MORE than the ceiling — `worked_core_empty` alone does,
    carrying a quarter of the foreground's half plus its share of the
    geometric background.

    So the hypothesis of `worked_weight_bound_pred_T_of` is not inherited
    caution: drop it and the conclusion is false at the ceiling.  This is
    the negative half the classifier-indexed recipe never had, and it is
    available here for the reason the twin exists at all — a predicate's
    complement is something a reader can name two members of, where a
    classifier's reject set was only ever described. -/
theorem worked_off_fire_exceeds_the_ceiling :
    (List.map fin_core worked_off_fire_list).Nodup ∧
      (worked_is_fire worked_core_empty = false ∧ worked_is_fire worked_core_a = false) ∧
      ¬ (core_sum worked_cd.cd_weight worked_off_fire_list ≤ (1045 : Rat) / 8192) := by
  refine ⟨?_, ⟨worked_is_fire_empty, worked_is_fire_a⟩, ?_⟩
  · rw [map_fin_core_worked_off_fire_list]
    exact List.nodup_cons.mpr ⟨by simp [Ne.symm worked_core_a_ne_empty],
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  · show ¬ (worked_cd.cd_weight worked_core_empty +
      (worked_cd.cd_weight worked_core_a + 0) ≤ 1045 / 8192)
    rw [worked_cd_weight_empty, worked_cd_weight_a]
    grind

/-- ... and the pin cashed in as a refutation of the twin's conclusion.  Two
    VALID records outside `P` whose cores are the two the fire set leaves
    out refute the bound at the ceiling.  So the twin's hypothesis is not
    free: a `P` whose complement reaches either core cannot satisfy it, and
    a recipe that let one through would prove something false.

    Validity is a hypothesis rather than a claim about `core_input`, for
    the reason that runs through this whole file: nothing here asserts that
    a fabricated record is a launch a kernel could have performed, and a
    refutation that named an invalid record would refute nothing, since
    `GatedSize.weight_bound_pred_T`'s membership hypothesis carries
    `FinInput.valid_fin_input`.  A task that wants the unconditional form
    supplies its own two records. -/
theorem worked_weight_bound_pred_T_needs_the_fire_set (P : FinProcInput → Prop)
    (f1 f2 : FinProcInput) (Hv1 : valid_fin_input f1) (Hp1 : ¬ P f1)
    (Hc1 : fin_core f1 = worked_core_empty) (Hv2 : valid_fin_input f2)
    (Hp2 : ¬ P f2) (Hc2 : fin_core f2 = worked_core_a) :
    ¬ GatedSize.weight_bound_pred_T P Worked_D.w Worked_D.M ((1045 : Rat) / 8192) := by
  intro Hbound
  have Hnd : (List.map fin_core [f1, f2]).Nodup := by
    show ([fin_core f1, fin_core f2]).Nodup
    rw [Hc1, Hc2]
    exact List.nodup_cons.mpr ⟨by simp [Ne.symm worked_core_a_ne_empty],
      List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  have Hall : ∀ f, f ∈ [f1, f2] → valid_fin_input f ∧ ¬ P f := by
    intro f Hf
    rcases List.mem_cons.mp Hf with rfl | hf
    · exact ⟨Hv1, Hp1⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨Hv2, Hp2⟩
      · cases hf
  have H := Hbound [f1, f2] Hnd Hall
  have hwD : Worked_D.w = cd_lift worked_cd := rfl
  have hMD : Worked_D.M = worked_cd.cd_mass := rfl
  rw [hwD, ← core_sum_cd_lift] at H
  rw [core_sum_cons, core_sum_cons, core_sum_nil, Hc1, Hc2] at H
  have hw : worked_cd.cd_weight worked_core_empty +
      (worked_cd.cd_weight worked_core_a + 0) = (14357 : Rat) / 65536 := by
    rw [worked_cd_weight_empty, worked_cd_weight_a]
    grind
  rw [hw, hMD, worked_mass_is_one, Rat.mul_one] at H
  grind

/- =========================================================================
   The standard-input enumerations, read off the cores
   ========================================================================= -/

/-- `cyl_enum` with the launch-time environment forgotten: the standard
    inputs that extend `bs` by at most `N` bytes, as BYTE LISTS.

    The envp-varying family cannot use `cyl_enum` directly — its cores vary
    in envp as well, so a core is a PAIR (environment, standard input) and
    the two coordinates have to be enumerated apart before they are
    recombined.  What is deliberately NOT done here is to prove the
    cancellation a second time: `cyl_enum_bytes_cyl` says the two
    enumerations are the same list under `mkFinCore`, and `bytes_cyl_sum_le`
    is `cyl_enum_sum_le` transported across it. -/
def bytes_cyl (bs : List (BitVec 8)) : Nat → List (List (BitVec 8))
  | 0 => [bs]
  | N + 1 => bs :: all_bytes.flatMap (fun b => bytes_cyl (bs ++ [b]) N)

theorem bytes_cyl_zero (bs : List (BitVec 8)) : bytes_cyl bs 0 = [bs] := rfl

theorem bytes_cyl_succ (bs : List (BitVec 8)) (N : Nat) :
    bytes_cyl bs (N + 1) = bs :: all_bytes.flatMap (fun b => bytes_cyl (bs ++ [b]) N) :=
  rfl

/-- ... and the same for the core-indexed enumeration, so that the
    comparison below can step both sides. -/
theorem cyl_enum_succ (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (bs : List (BitVec 8)) (N : Nat) :
    cyl_enum argv envp fs bs (N + 1) =
      FinCore.mkFinCore argv envp fs bs ::
        all_bytes.flatMap (fun b => cyl_enum argv envp fs (bs ++ [b]) N) :=
  rfl

/-- A `List.flatMap` respects a pointwise equality of its blocks.  `Stdlib`
    ships no congruence lemma for `flatMap`, and this is the one the two
    enumerations below need. -/
theorem flatMap_congr_mem {A B : Type} (f g : A → List B) (l : List A)
    (H : ∀ x, x ∈ l → f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, H x (List.mem_cons_self ..),
      ih (fun y Hy => H y (List.mem_cons_of_mem _ Hy))]

theorem cyl_enum_bytes_cyl (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) :
    ∀ (N : Nat) (bs : List (BitVec 8)),
      cyl_enum argv envp fs bs N =
        List.map (FinCore.mkFinCore argv envp fs) (bytes_cyl bs N) := by
  intro N
  induction N with
  | zero => intro bs; rfl
  | succ N ih =>
    intro bs
    rw [cyl_enum_succ, bytes_cyl_succ, List.map_cons, List.map_flatMap]
    congr 1
    exact flatMap_congr_mem _ _ _ (fun b _ => ih (bs ++ [b]))

theorem bytes_cyl_In (N : Nat) (bs ext : List (BitVec 8)) (Hlen : ext.length ≤ N) :
    bs ++ ext ∈ bytes_cyl bs N := by
  have hin := cyl_enum_complete [] [] [] N bs ext Hlen
  rw [cyl_enum_bytes_cyl] at hin
  obtain ⟨s, hins, Hs⟩ := List.mem_map.mp hin
  have hs : s = bs ++ ext := congrArg FinCore.core_stdin Hs
  rw [← hs]
  exact hins

/-- The three standard-input sums the family below charges against, each
    transported from the `qsum` lemma that proved it: the cylinder
    (`cyl_enum_sum_le`), the length-`< k` prefix family
    (`qsum_short_inputs`) and one full length slice (`qsum_full_slice`).
    The transport is the same three rewrites every time — the enumeration is
    a `List.map` of `mkFinCore`, `qsum_map` strips it off, and
    `geo_weight_match` turns the weight back into the `geo_point` it was
    built from. -/
theorem bytes_cyl_sum_le (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    ∀ (N : Nat) (bs : List (BitVec 8)),
      qsum (fun s => geo_point p s.length) (bytes_cyl bs N) ≤
        geo_mass p bs.length := by
  intro N bs
  refine Rat.le_trans (b := qsum (geo_weight p [] [] []) (cyl_enum [] [] [] bs N)) ?_ ?_
  · rw [cyl_enum_bytes_cyl, qsum_map]
    apply qsum_mono
    intro s _
    rw [geo_weight_match]
    exact Rat.le_refl
  · exact cyl_enum_sum_le p [] [] [] Hp0 Hp1 N bs

theorem short_inputs_sum (p : Rat) (k : Nat) :
    qsum (fun s => geo_point p s.length) (short_inputs k) = geo_prefix_sum p k := by
  rw [← qsum_short_inputs p [] [] [] k, qsum_map]
  apply qsum_ext
  intro s _
  rw [geo_weight_match]

theorem byte_lists_sum (p : Rat) (n : Nat) :
    qsum (fun s => geo_point p s.length) (byte_lists n) = p * Qpow (1 - p) n := by
  rw [← qsum_full_slice p [] [] [] n, qsum_map]
  apply qsum_ext
  intro s _
  rw [geo_weight_match]

/- =========================================================================
   Combinator: geometric standard input over a VARYING launch-time
   environment
   ========================================================================= -/

/-- The per-entry half of the weight: the product, over the environment's
    entries, of the byte-geometric weight of each entry's own length.
    `geo_point q_e m` is `q_e * ((1 - q_e) * (1/256)) ^ m` by definition,
    which is the per-entry factor the family is specified with — the same
    memoryless source `stdin_geometric` spreads standard input by, run once
    per entry. -/
def entries_geo_product (q : Rat) : List (List (BitVec 8)) → Rat
  | [] => 1
  | e :: es' => geo_point q e.length * entries_geo_product q es'

theorem entries_geo_product_nil (q : Rat) : entries_geo_product q [] = 1 := rfl

theorem entries_geo_product_cons (q : Rat) (e : List (BitVec 8))
    (es : List (List (BitVec 8))) :
    entries_geo_product q (e :: es) = geo_point q e.length * entries_geo_product q es :=
  rfl

/-- The mass of the environments EXTENDING a given list of entries, and the
    weight of the environment that stops there.  As with `geo_mass` and
    `geo_point` the two are one object: continuing past an entry costs
    `1 - r` and the entry itself costs its byte-geometric weight, so
    `envp_factor` is the running product of those, and `envp_point` is `r`
    times it — the `r` being the weight of stopping.

    The three-factor form the family is specified with,
    `r * (1 - r) ^ k * Prod_i geo_point q_e |e_i|`, is
    `envp_point_closed_form` below and is a LEMMA rather than a rival
    definition, for the reason `geo_point_closed_form` is: every proof here
    multiplies the factors together anyway, and one object with two readings
    cannot drift. -/
def envp_factor (r q : Rat) : List (List (BitVec 8)) → Rat
  | [] => 1
  | e :: es' => (1 - r) * geo_point q e.length * envp_factor r q es'

theorem envp_factor_nil (r q : Rat) : envp_factor r q [] = 1 := rfl

theorem envp_factor_cons (r q : Rat) (e : List (BitVec 8))
    (es : List (List (BitVec 8))) :
    envp_factor r q (e :: es) = (1 - r) * geo_point q e.length * envp_factor r q es :=
  rfl

def envp_point (r q : Rat) (es : List (List (BitVec 8))) : Rat :=
  r * envp_factor r q es

theorem envp_factor_closed_form (r q : Rat) (es : List (List (BitVec 8))) :
    envp_factor r q es = Qpow (1 - r) es.length * entries_geo_product q es := by
  induction es with
  | nil =>
    rw [envp_factor_nil, entries_geo_product_nil]
    show (1 : Rat) = Qpow (1 - r) 0 * 1
    rw [Qpow_0]
    grind
  | cons e es ih =>
    rw [envp_factor_cons, entries_geo_product_cons, ih, List.length_cons, Qpow_succ]
    grind

theorem envp_point_closed_form (r q : Rat) (es : List (List (BitVec 8))) :
    envp_point r q es = r * Qpow (1 - r) es.length * entries_geo_product q es := by
  unfold envp_point
  rw [envp_factor_closed_form]
  grind

/-- Extending the prefix MULTIPLIES the factor, which is the whole reason
    the envp coordinate can be enumerated the way the standard-input
    coordinate is: the mass of the environments past `es ++ es'` is the mass
    past `es` scaled by what `es'` costs, and the induction below needs
    exactly that at `es' = [e]`. -/
theorem envp_factor_app (r q : Rat) (es es' : List (List (BitVec 8))) :
    envp_factor r q (es ++ es') = envp_factor r q es * envp_factor r q es' := by
  induction es with
  | nil => rw [List.nil_append, envp_factor_nil]; grind
  | cons e es ih =>
    rw [List.cons_append, envp_factor_cons, envp_factor_cons, ih]
    grind

theorem envp_factor_one (r q : Rat) (e : List (BitVec 8)) :
    envp_factor r q [e] = (1 - r) * geo_point q e.length := by
  rw [envp_factor_cons, envp_factor_nil]
  grind

/-- Nonnegativity, and it costs the same three side conditions the two
    coordinates cost separately: `r <= 1` makes the continuation factor
    nonnegative, exactly as `p_stop <= 1` does in `geo_ratio_nonneg`, and
    `0 <= q_e <= 1` is what `geo_point_nonneg` asks of the per-entry
    weight. -/
theorem envp_factor_nonneg (r q : Rat) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    ∀ es : List (List (BitVec 8)), 0 ≤ envp_factor r q es := by
  intro es
  induction es with
  | nil => rw [envp_factor_nil]; exact Qle_0_1
  | cons e es ih =>
    rw [envp_factor_cons]
    refine Rat.mul_nonneg (Rat.mul_nonneg (by grind) (geo_point_nonneg q _ Hq0 Hq1)) ih

theorem envp_point_nonneg (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q)
    (Hq1 : q ≤ 1) (es : List (List (BitVec 8))) : 0 ≤ envp_point r q es := by
  unfold envp_point
  exact Rat.mul_nonneg Hr0 (envp_factor_nonneg r q Hr1 Hq0 Hq1 es)

/-- One environment weighs at most the mass of the environments extending
    it, because `r <= 1`.  This is `geo_point_le_mass` on the other
    coordinate and it is the base case of the same induction. -/
theorem envp_point_le_factor (r q : Rat) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (es : List (List (BitVec 8))) : envp_point r q es ≤ envp_factor r q es := by
  unfold envp_point
  have h : r * envp_factor r q es ≤ 1 * envp_factor r q es :=
    Rat.mul_le_mul_of_nonneg_right Hr1 (envp_factor_nonneg r q Hr1 Hq0 Hq1 es)
  rwa [Rat.one_mul] at h

/-- THE WEIGHT.  Zero unless the core's argv and file system are the fixed
    ones; otherwise the environment's weight times the standard-input weight
    of its own length.

    Compare `geo_weight`, which fixes envp too and therefore weighs ZERO at
    every core whose launch-time environment differs.  That is the gap this
    family exists to close: a defect reachable only under a non-canonical
    environment sits in a `geo_weight`-null set, so a fire-set bound proved
    against `stdin_geometric` alone says nothing about it.  Here the
    environment carries mass — `stdin_envp_geometric_envp_bites` below is
    that statement at a concrete pair of cores.

    The environment test is one decidable equation, "the core is the
    template with its own envp and standard input plugged in", for the
    reason `geo_weight`'s is: it is the hypothesis the enumeration argument
    already carries, so nothing stands between them. -/
def envp_geo_weight (p r q : Rat) (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) : Rat :=
  if c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin
  then envp_point r q c.core_envp * geo_point p c.core_stdin.length
  else 0

theorem envp_geo_weight_match (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (es : List (List (BitVec 8))) (s : List (BitVec 8)) :
    envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s) =
      envp_point r q es * geo_point p s.length := by
  unfold envp_geo_weight
  rw [ite_eq_left rfl]

theorem envp_geo_weight_mismatch (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (c : FinCore)
    (Hne : c ≠ FinCore.mkFinCore argv c.core_envp fs c.core_stdin) :
    envp_geo_weight p r q argv fs c = 0 := by
  unfold envp_geo_weight
  rw [ite_eq_right Hne]

/-- THE FAMILY'S FORMULA, all six factors visible at once: entry-count
    geometric in `r`, per-entry byte-geometric in `q_e`, and the
    standard-input geometric in `p_stop` this file already had.  It is the
    product of `envp_point_closed_form` and `geo_point_closed_form`, and it
    is stated because the specification is quoted in that shape and a reader
    should be able to check the definition against it without unfolding
    anything. -/
theorem envp_geo_weight_closed_form (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (es : List (List (BitVec 8)))
    (s : List (BitVec 8)) :
    envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s) =
      r * Qpow (1 - r) es.length * entries_geo_product q es *
        (p * Qpow (1 - p) s.length * Qpow (1 / 256) s.length) := by
  rw [envp_geo_weight_match, envp_point_closed_form, geo_point_closed_form]

theorem envp_geo_weight_nonneg (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    0 ≤ envp_geo_weight p r q argv fs c := by
  unfold envp_geo_weight
  split
  · next _ =>
    show 0 ≤ envp_point r q c.core_envp * geo_point p c.core_stdin.length
    exact Rat.mul_nonneg (envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 c.core_envp)
      (geo_point_nonneg p c.core_stdin.length Hp0 Hp1)
  · next _ => exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, as everywhere in this file, and
    `stdin_envp_geometric_mass_upper` below is the proof that owes something
    to it.  The six side conditions are constructor arguments for the reason
    `stdin_geometric`'s two are: `cd_nonneg` is a field.

    Declaring `1` — rather than, say, the envp mass times the stdin mass
    written out — is what keeps a MIXTURE of this family with
    `stdin_geometric` at total mass `1` under `cd_scale` by shares summing
    to `1`, which is the composition the calibrated example at the end of
    the file spells out.

    None of the three strict inequalities is demanded, for the reason
    `stdin_geometric` does not demand `0 < p_stop`: nothing the constructor
    needs uses them, and the lower certificate that does asks for all three
    as hypotheses of ITS OWN statement. -/
def stdin_envp_geometric (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution where
  cd_weight := envp_geo_weight p r q argv fs
  cd_mass := 1
  cd_nonneg := envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1

theorem stdin_envp_geometric_mass_nonneg (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 ≤ (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass := by
  show (0 : Rat) ≤ 1
  exact Qle_0_1

/- =========================================================================
   The envp cylinder, and the enumeration that bounds it
   ========================================================================= -/

/-- Every environment extending `es` by at most `M` further entries, each
    of them shorter than `L`, as a list.  It is `cyl_enum` one level up:
    the stopping environment, then for each admissible ENTRY the
    enumeration of the environments one entry deeper.

    Two depths where `cyl_enum` has one, and the second is not avoidable:
    an environment's continuations are indexed by an entry, an entry is a
    byte list, and there are infinitely many of those.  `short_inputs L` is
    the same length-bounded enumeration of byte lists the geometric lower
    certificate already uses, so no new enumeration of entries is written
    here.

    As with `cyl_enum`, duplicate-freedom of this list is never proved and
    never needed for the BOUNDS — `qsum_core_incl_le` asks nothing of the
    list it bounds against.  The lower certificate does need it, and proves
    it separately for the family it actually exhibits
    (`envps_upto_nodup`). -/
def envp_enum (es : List (List (BitVec 8))) (M L : Nat) :
    List (List (List (BitVec 8))) :=
  match M with
  | 0 => [es]
  | M' + 1 => es :: (short_inputs L).flatMap (fun e => envp_enum (es ++ [e]) M' L)

theorem envp_enum_zero (es : List (List (BitVec 8))) (L : Nat) :
    envp_enum es 0 L = [es] := rfl

theorem envp_enum_succ (es : List (List (BitVec 8))) (M L : Nat) :
    envp_enum es (M + 1) L =
      es :: (short_inputs L).flatMap (fun e => envp_enum (es ++ [e]) M L) := rfl

/-- It misses nothing within its two depths. -/
theorem envp_enum_complete (M L : Nat) :
    ∀ (es rest : List (List (BitVec 8))), rest.length ≤ M →
      (∀ e, e ∈ rest → e.length < L) →
      es ++ rest ∈ envp_enum es M L := by
  induction M with
  | zero =>
    intro es rest Hlen _
    rcases rest with _ | ⟨e, rest⟩
    · rw [List.append_nil, envp_enum_zero]; exact List.mem_cons_self ..
    · simp at Hlen
  | succ M ih =>
    intro es rest Hlen Hent
    rcases rest with _ | ⟨e, rest⟩
    · rw [List.append_nil, envp_enum_succ]; exact List.mem_cons_self ..
    · rw [envp_enum_succ]
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap]
      refine ⟨e, ?_, ?_⟩
      · exact short_inputs_complete L e (Hent e (List.mem_cons_self ..))
      · have hsplit : es ++ e :: rest = (es ++ [e]) ++ rest := by
          rw [List.append_assoc]; rfl
        rw [hsplit]
        exact ih (es ++ [e]) rest (by simp at Hlen ⊢; omega)
          (fun x Hx => Hent x (List.mem_cons_of_mem _ Hx))

/-- ONE STEP OF THE ENVP CANCELLATION, as an exact identity: the
    environments one entry deeper than `es` carry, between them,
    `envp_factor` of `es` times `(1 - r)` times what the entry enumeration
    itself weighs.

    This is where the per-entry byte-geometric is spent, and it is spent
    through the lemma that already knows the answer: `short_inputs_sum`
    evaluates the entry enumeration to `geo_prefix_sum q_e L`, which
    `geo_prefix_sum_closed` closes to `1 - (1 - q_e) ^ L`.  Only the
    `<= 1` of that number is used below, but the identity is stated exactly
    because a bound whose slack is invisible is a bound nobody can
    sharpen. -/
theorem qsum_envp_factor_step (r q : Rat) (es : List (List (BitVec 8))) (L : Nat) :
    qsum (fun e => envp_factor r q (es ++ [e])) (short_inputs L) =
      envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L) := by
  rw [qsum_ext (fun e => envp_factor r q (es ++ [e]))
    (fun e => envp_factor r q es * (1 - r) * geo_point q e.length) _ ?_]
  · rw [qsum_scale, short_inputs_sum, geo_prefix_sum_closed]
  · intro e _
    rw [envp_factor_app, envp_factor_one]
    grind

/-- THE CANCELLATION on the envp coordinate, by induction on the entry
    depth: the whole enumeration weighs no more than the mass of the
    environments extending `es`, at every depth and every prefix.

    The step is the same shape `cyl_enum_sum_le`'s is, with one difference
    worth naming.  There the 256 continuations are charged a common constant
    and `256 * (1 / 256)` folds to `1` exactly, so the step is lossless.
    Here the continuations are charged what their own entry costs and their
    total is `1 - (1 - q_e) ^ L`, which is under `1` rather than equal to
    it: an entry longer than `L` is a continuation the enumeration omits.
    The bound stays true because the omitted mass is nonnegative, and the
    slack is real — it is the same slack
    `stdin_geometric_bound_by_max_length` measures on the standard-input
    coordinate, and it vanishes as `L` grows, which is what the lower
    certificate below spends.

    The base case is where `r <= 1` is used for something other than
    nonnegativity: a depth-zero enumeration holds only the stopping
    environment, which weighs `r` times the mass and must be under it. -/
theorem envp_enum_sum_le (r q : Rat) (_Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q)
    (Hq1 : q ≤ 1) :
    ∀ (M L : Nat) (es : List (List (BitVec 8))),
      qsum (envp_point r q) (envp_enum es M L) ≤ envp_factor r q es := by
  intro M
  induction M with
  | zero =>
    intro L es
    rw [envp_enum_zero, qsum_cons, qsum_nil]
    show envp_point r q es + 0 ≤ envp_factor r q es
    have h := envp_point_le_factor r q Hr1 Hq0 Hq1 es
    grind
  | succ M ih =>
    intro L es
    rw [envp_enum_succ, qsum_cons]
    refine Rat.le_trans (b := envp_point r q es +
      qsum (fun e => envp_factor r q (es ++ [e])) (short_inputs L))
      (Qplus_le_compat (Rat.le_refl) ?_) ?_
    · exact qsum_flat_map_le (envp_point r q)
        (fun e => envp_enum (es ++ [e]) M L)
        (fun e => envp_factor r q (es ++ [e])) (short_inputs L)
        (fun e _ => ih L (es ++ [e]))
    · rw [qsum_envp_factor_step]
      have hpow : 0 ≤ Qpow (1 - q) L := Qpow_nonneg _ _ (by grind)
      have hF : 0 ≤ envp_factor r q es := envp_factor_nonneg r q Hr1 Hq0 Hq1 es
      have hq1 : 1 - Qpow (1 - q) L ≤ 1 := by grind
      have hFr : 0 ≤ envp_factor r q es * (1 - r) := Rat.mul_nonneg hF (by grind)
      have hstep : envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L) ≤
          envp_factor r q es * (1 - r) := by
        refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hq1 hFr) ?_
        rw [Rat.mul_one]
        exact Rat.le_refl
      show r * envp_factor r q es +
        envp_factor r q es * (1 - r) * (1 - Qpow (1 - q) L) ≤ envp_factor r q es
      grind

/- =========================================================================
   The two coordinates, recombined
   ========================================================================= -/

/-- Every core over the fixed argv and file system whose environment comes
    from `A` and whose standard input comes from `B`.

    A core of this family is a PAIR — an environment and a standard input —
    and the weight is the product of one factor per coordinate, so the
    enumeration is the product of the two coordinates' enumerations and its
    sum is the product of their sums (`qsum_envp_stdin_product`).  That
    identity is what lets every bound below be assembled from an envp bound
    and a standard-input bound proved apart, and it is the only place the
    two coordinates meet. -/
def envp_stdin_product (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (A : List (List (List (BitVec 8)))) (B : List (List (BitVec 8))) :
    List FinCore :=
  A.flatMap (fun es => List.map (FinCore.mkFinCore argv es fs) B)

theorem In_envp_stdin_product (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (A : List (List (List (BitVec 8)))) (B : List (List (BitVec 8)))
    (es : List (List (BitVec 8))) (s : List (BitVec 8))
    (HA : es ∈ A) (HB : s ∈ B) :
    FinCore.mkFinCore argv es fs s ∈ envp_stdin_product argv fs A B := by
  unfold envp_stdin_product
  rw [List.mem_flatMap]
  exact ⟨es, HA, List.mem_map.mpr ⟨s, HB, rfl⟩⟩

theorem qsum_envp_geo_block (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (es : List (List (BitVec 8))) (B : List (List (BitVec 8))) :
    qsum (envp_geo_weight p r q argv fs)
        (List.map (FinCore.mkFinCore argv es fs) B) =
      qsum (fun s => geo_point p s.length) B * envp_point r q es := by
  rw [qsum_map]
  rw [qsum_ext (fun s => envp_geo_weight p r q argv fs (FinCore.mkFinCore argv es fs s))
    (fun s => envp_point r q es * geo_point p s.length) _
    (fun s _ => by rw [envp_geo_weight_match])]
  rw [qsum_scale]
  grind

theorem qsum_envp_stdin_product (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (A : List (List (List (BitVec 8))))
    (B : List (List (BitVec 8))) :
    qsum (envp_geo_weight p r q argv fs) (envp_stdin_product argv fs A B) =
      qsum (envp_point r q) A * qsum (fun s => geo_point p s.length) B := by
  unfold envp_stdin_product
  rw [qsum_flat_map]
  rw [qsum_ext
    (fun es => qsum (envp_geo_weight p r q argv fs) (List.map (FinCore.mkFinCore argv es fs) B))
    (fun es => qsum (fun s => geo_point p s.length) B * envp_point r q es) _
    (fun es _ => qsum_envp_geo_block p r q argv fs es B)]
  rw [qsum_scale]
  grind

/-- The product of two duplicate-free enumerations repeats nothing: the
    blocks are duplicate-free because a core determines its standard input,
    and two blocks are disjoint because a core determines its environment.
    Only the lower certificate needs this — the bounds are proved against a
    containing list nobody has to show duplicate-free. -/
theorem NoDup_envp_stdin_product (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (A : List (List (List (BitVec 8)))) (B : List (List (BitVec 8)))
    (HA : A.Nodup) (HB : B.Nodup) :
    (envp_stdin_product argv fs A B).Nodup := by
  unfold envp_stdin_product
  refine NoDup_flat_map _ _ HA ?_ ?_
  · intro es _
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact congrArg FinCore.core_stdin Heq
    · exact HB
  · intro es1 es2 c _ _ H1 H2
    obtain ⟨s1, _, Hs1⟩ := List.mem_map.mp H1
    obtain ⟨s2, _, Hs2⟩ := List.mem_map.mp H2
    have h : FinCore.mkFinCore argv es2 fs s2 = FinCore.mkFinCore argv es1 fs s1 := by
      rw [Hs2, Hs1]
    exact (congrArg FinCore.core_envp h).symm

/- =========================================================================
   The three depths, read off the task's own list
   ========================================================================= -/

/-- `Measure.weight_bound_T`'s lists are finite, and that is the whole of
    what the bounds below need from them.  Where `stdin_geometric` reads ONE
    depth off the list — the largest standard-input length — this family
    reads THREE, one per axis of the enumeration: how many entries an
    environment has, how long an entry is, and how long a standard input is.
    Each is a `list_max` over the list, so each exists because the list is
    finite and for no other reason.

    The entry depth is one MORE than a maximum rather than the maximum,
    because `short_inputs` enumerates the byte lists STRICTLY shorter than
    its argument and an entry of the maximum length has to be inside. -/
def cores_envp_depth (cs : List FinCore) : Nat :=
  list_max (List.map (fun c => c.core_envp.length) cs)

def cores_entry_depth (cs : List FinCore) : Nat :=
  list_max (List.map (fun c => list_max (List.map (fun e => e.length) c.core_envp))
    cs) + 1

def cores_stdin_depth (cs : List FinCore) : Nat :=
  list_max (List.map (fun c => c.core_stdin.length) cs)

theorem cores_envp_depth_ge (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_envp.length ≤ cores_envp_depth cs := by
  unfold cores_envp_depth
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)

theorem cores_entry_depth_gt (cs : List FinCore) (c : FinCore)
    (e : List (BitVec 8)) (Hc : c ∈ cs) (He : e ∈ c.core_envp) :
    e.length < cores_entry_depth cs := by
  unfold cores_entry_depth
  have h1 : e.length ≤ list_max (List.map (fun x => x.length) c.core_envp) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨e, He, rfl⟩)
  have h2 : list_max (List.map (fun x => x.length) c.core_envp) ≤
      list_max (List.map (fun c0 => list_max (List.map (fun x => x.length) c0.core_envp))
        cs) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)
  omega

theorem cores_stdin_depth_ge (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_stdin.length ≤ cores_stdin_depth cs := by
  unfold cores_stdin_depth
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)

/- =========================================================================
   The cylinder bound over cores
   ========================================================================= -/

/-- The cores this bound is about: the fixed argv and file system, an
    environment EXTENDING `es` and a standard input EXTENDING `bs`.  Two
    existentials rather than a conjunction of four tests, for the reason
    `in_stdin_cylinder` is one: it is the form both the construction and
    the enumeration want. -/
def in_envp_stdin_cylinder (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ eext ext, c = FinCore.mkFinCore argv (es ++ eext) fs (bs ++ ext)

/- =========================================================================
   The cylinder's mass and the bound over cores
   ========================================================================= -/

/-- The cylinder's mass: the product of what the two coordinates
    contribute, which is `envp_factor` on the environment and `geo_mass` on
    the standard input.  It is the number every bound below charges
    against, and the two factors are exactly the two masses the two
    coordinates were enumerated against. -/
def stdin_envp_geometric_cylinder_mass (p r q : Rat)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) : Rat :=
  envp_factor r q es * geo_mass p bs.length

/-- The same number in closed form, all six factors visible: the entry
    count geometric in `r`, the per-entry byte-geometric in `q_e`, and the
    standard-input geometric in `p_stop`.  It is
    `envp_factor_closed_form` and `geo_mass_closed_form` multiplied
    together, and it is stated so that the specification this family is
    quoted with can be checked without unfolding anything. -/
theorem stdin_envp_geometric_cylinder_mass_closed_form (p r q : Rat)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) :
    stdin_envp_geometric_cylinder_mass p r q es bs =
      Qpow (1 - r) es.length * entries_geo_product q es *
        (Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length) := by
  unfold stdin_envp_geometric_cylinder_mass
  rw [envp_factor_closed_form, geo_mass_closed_form]

/-- The product of two `≤` facts about nonnegative rationals, which is what
    puts an envp bound and a standard-input bound together.  `QArith` has
    the one-sided forms and not this one. -/
theorem Qmult_le_compat_nonneg {a b c d : Rat} (H1 : a ≤ b) (H2 : c ≤ d)
    (Ha : 0 ≤ a) (Hc : 0 ≤ c) : a * c ≤ b * d := by
  refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right H1 Hc) ?_
  exact Rat.mul_le_mul_of_nonneg_left H2 (Rat.le_trans Ha H1)

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    Three enumeration depths are read off the list — its longest
    environment, its longest entry, its longest standard input — and the
    product of the two coordinates' enumerations contains it.  The sum of
    that product is the product of the two sums
    (`qsum_envp_stdin_product`), and each factor already has its own bound
    (`envp_enum_sum_le` on the envp coordinate, `bytes_cyl_sum_le` on the
    standard input).  `Qmult_le_compat_nonneg` is what puts the two
    together, and the nonnegativity it asks for is the two enumerations'
    own.

    As with `geo_weight_cylinder_bound`, the finiteness spent here is the
    finiteness of `Measure.weight_bound_T`'s lists and nothing else: a
    list may be as long as it likes, but not infinite, so it has a
    horizon on each of the three axes. -/
theorem envp_geo_weight_cylinder_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) (cs : List FinCore)
    (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_envp_stdin_cylinder argv fs es bs c) :
    qsum (envp_geo_weight p r q argv fs) cs ≤
      stdin_envp_geometric_cylinder_mass p r q es bs := by
  refine Rat.le_trans (qsum_core_incl_le (envp_geo_weight p r q argv fs) cs
    (envp_stdin_product argv fs
      (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
      (bytes_cyl bs (cores_stdin_depth cs)))
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨eext, ext, rfl⟩ := Hcyl c Hc
    have henvp : (es ++ eext).length ≤ cores_envp_depth cs :=
      cores_envp_depth_ge cs _ Hc
    have hstdin : (bs ++ ext).length ≤ cores_stdin_depth cs :=
      cores_stdin_depth_ge cs _ Hc
    rw [List.length_append] at hstdin
    refine In_envp_stdin_product argv fs _ _ (es ++ eext) (bs ++ ext) ?_ ?_
    · apply envp_enum_complete
      · rw [List.length_append] at henvp; omega
      · intro e He
        exact cores_entry_depth_gt cs _ e Hc (List.mem_append_right _ He)
    · apply bytes_cyl_In
      omega
  · rw [qsum_envp_stdin_product]
    unfold stdin_envp_geometric_cylinder_mass
    refine Qmult_le_compat_nonneg ?_ ?_ ?_ ?_
    · exact Rat.le_trans (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ es)
        (by show envp_factor r q es ≤ envp_factor r q es; exact Rat.le_refl)
    · exact bytes_cyl_sum_le p Hp0 Hp1 _ bs
    · exact qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x)
    · exact qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1)

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over an environment prefix and a standard-input prefix,
    weighs at most that cylinder's mass.  The hypothesis is the one
    `Measure.weight_bound_T` carries, and `core_sum_map_fin_core` is the
    only step between them.

    This is the statement the family exists for: a fire set described by
    "the environment begins with these entries and standard input begins
    with these bytes" is charged a number that DEPENDS ON THE ENVIRONMENT,
    where `stdin_geometric_bound` would charge either the stdin cylinder's
    whole mass (if the environment happened to be the fixed one) or
    nothing at all (if it did not, because nothing there weighs anything). -/
theorem stdin_envp_geometric_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List (BitVec 8)))
    (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_envp_stdin_cylinder argv fs es bs (fin_core f)) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      stdin_envp_geometric_cylinder_mass p r q es bs := by
  show core_sum (envp_geo_weight p r q argv fs) l ≤ _
  rw [core_sum_map_fin_core]
  apply envp_geo_weight_cylinder_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs
  · exact Hnd
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    exact Hcyl f Hf

/-- The launch-time test as a boolean, so that `List.filter` can use it.
    It is `matches_env` with the environment left free: this family fixes
    argv and the file system and nothing else, so the equation a core has
    to satisfy in order to weigh anything is the template with BOTH its
    envp and its standard input plugged in.

    `Measure`'s `Qle_bool` exception is not in play, for the reason it is
    not in `matches_env`: this decides an equality of CORES, which
    `FinCore_eq_dec` decides outright, and no rational is involved. -/
def matches_argv_fs (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) : Bool :=
  decide (c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin)

theorem matches_argv_fs_false (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) (H : matches_argv_fs argv fs c = false) :
    c ≠ FinCore.mkFinCore argv c.core_envp fs c.core_stdin :=
  of_decide_eq_false H

theorem matches_argv_fs_true (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (c : FinCore) (H : matches_argv_fs argv fs c = true) :
    c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin :=
  of_decide_eq_true H

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as
    `stdin_geometric_bound_or_off_environment` slackens its own: each
    record is in the cylinder OR its core misses the fixed argv or file
    system and therefore weighs nothing.  Both forms stay; neither weakens
    the other. -/
theorem stdin_envp_geometric_bound_or_off_environment (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List (BitVec 8)))
    (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l → in_envp_stdin_cylinder argv fs es bs (fin_core f) ∨
      matches_argv_fs argv fs (fin_core f) = false) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      stdin_envp_geometric_cylinder_mass p r q es bs := by
  show core_sum (envp_geo_weight p r q argv fs) l ≤ _
  rw [core_sum_map_fin_core]
  rw [qsum_filter (envp_geo_weight p r q argv fs) (matches_argv_fs argv fs) _
    (fun c Hc => by
      rw [envp_geo_weight_mismatch p r q argv fs c
        (matches_argv_fs_false _ _ _ Hc)])]
  apply envp_geo_weight_cylinder_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 es bs
  · exact List.Nodup.sublist List.filter_sublist Hnd
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    rcases Hor f Hf with h | h
    · exact h
    · rw [h] at Hm
      exact absurd Hm (by decide)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass `1`.  It is the disjunctive bound at the EMPTY environment prefix
    and the EMPTY standard-input prefix, and the whole content is that the
    disjunction is EXHAUSTIVE there — a core either matches the fixed argv
    and file system, in which case its environment is `[] ++ itself` and
    its standard input is `[] ++ itself`, or it does not.  The cylinder
    mass at the empty prefix is `1`, because `envp_factor` of no entries is
    and `Qpow` at exponent zero is. -/
theorem stdin_envp_geometric_mass_upper (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass := by
  show core_sum (envp_geo_weight p r q argv fs) l ≤ 1
  refine Rat.le_trans (stdin_envp_geometric_bound_or_off_environment p r q argv fs
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 [] [] l Hnd ?_) ?_
  · intro f _
    by_cases hm : matches_argv_fs argv fs (fin_core f) = true
    · left
      refine ⟨(fin_core f).core_envp, (fin_core f).core_stdin, ?_⟩
      rw [matches_argv_fs_true _ _ _ hm]
      rfl
    · right
      rcases hb : matches_argv_fs argv fs (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm
  · have hm : stdin_envp_geometric_cylinder_mass p r q [] [] = 1 := by
      show (1 : Rat) * 1 = 1
      grind
    rw [hm]
    exact Rat.le_refl

/- =========================================================================
   Bounds that charge the environment nothing
   ========================================================================= -/

/-- A list whose cores match the fixed argv and file system and whose
    standard inputs all come from a given enumeration `B` weighs at most
    what `B` weighs — the environment coordinate is charged `1`, its whole
    declared mass, and nothing about the environment is assumed.

    This is the shape both remaining bounds take.  A task that knows
    nothing about the environments in its fire set gets exactly the
    standard-input bound `stdin_geometric` would have given it, which is
    the right answer: mixing an envp-varying component in must not make a
    stdin-only argument WORSE, and this lemma is that claim.  The price is
    that the envp enumeration still has to be built, because the cores have
    to sit inside SOMETHING finite — the two entry depths are read off the
    list and thrown away, and the `1` they are charged is
    `envp_enum_sum_le` at the empty prefix. -/
theorem envp_geo_weight_stdin_family_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (B : List (List (BitVec 8))) (SB : Rat)
    (cs : List FinCore) (HB : qsum (fun s => geo_point p s.length) B ≤ SB)
    (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs →
      c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin ∧ c.core_stdin ∈ B) :
    qsum (envp_geo_weight p r q argv fs) cs ≤ SB := by
  refine Rat.le_trans (qsum_core_incl_le (envp_geo_weight p r q argv fs) cs
    (envp_stdin_product argv fs
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B)
    (envp_geo_weight_nonneg p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨Hmatch, Hstdin⟩ := Hall c Hc
    have hins : c.core_envp ∈ envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs) := by
      have h := envp_enum_complete (cores_envp_depth cs) (cores_entry_depth cs)
        [] c.core_envp (cores_envp_depth_ge cs c Hc)
        (fun e He => cores_entry_depth_gt cs c e Hc He)
      rwa [List.nil_append] at h
    have hprod := In_envp_stdin_product argv fs _ B c.core_envp c.core_stdin hins Hstdin
    rw [Hmatch]
    exact hprod
  · rw [qsum_envp_stdin_product]
    refine Rat.le_trans (b := 1 * SB) ?_ ?_
    · apply Qmult_le_compat_nonneg
      · exact Rat.le_trans
          (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ [])
          (by show envp_factor r q [] ≤ 1; exact Rat.le_refl)
      · exact HB
      · exact qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x)
      · exact qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1)
    · show (1 : Rat) * SB ≤ SB
      grind

/-- THE LENGTH SLICE: a list drawn from one standard-input length slice
    weighs at most `p_stop * (1 - p_stop) ^ n`, with no `1/256` left in it
    and nothing charged for the environment.

    It is `stdin_geometric_slice_bound`'s constant exactly, which is the
    point — the counting lemma that produces it is not restated here and
    not needed, because the slice's total is already known
    (`byte_lists_sum`).  Note that the hypothesis does NOT fix the
    environment: the records may carry any envp at all, and the slice still
    weighs no more.

    WHAT IS NOT CLAIMED, and the difference from `stdin_geometric` is
    worth naming rather than leaving to be inferred from an absent lemma:
    this constant is not pinned as ATTAINED, and no sharpness lemma
    accompanies it.  There the slice is finite and
    `stdin_geometric_slice_bound_attained` exhibits a list reaching the
    constant outright.  Here the slice over a fixed standard-input length
    still holds one core per ENVIRONMENT, of which there are infinitely
    many carrying positive weight whenever `r < 1`, so a finite list
    reaching the constant is not available by the same argument and none
    is offered.  The bound is an upper bound and is stated as one. -/
theorem stdin_envp_geometric_slice_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = FinCore.mkFinCore argv f.fin_envp fs f.fin_stdin ∧
        f.fin_stdin.length = n) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      p * Qpow (1 - p) n := by
  show core_sum (envp_geo_weight p r q argv fs) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  refine envp_geo_weight_stdin_family_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (byte_lists n) (p * Qpow (1 - p) n) (List.map fin_core l) ?_ Hnd ?_
  · rw [byte_lists_sum]
    exact Rat.le_refl
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlen⟩ := Hall f Hf
    refine ⟨?_, ?_⟩
    · rw [Henv]
    · show f.fin_stdin ∈ byte_lists n
      rw [← Hlen]
      exact byte_lists_complete f.fin_stdin

/-- A list confined to standard inputs of length at most `n` weighs at most
    `1 - (1 - p_stop) ^ (n + 1)` — the partial sum at its own horizon, and
    again the environment is charged nothing.  It is
    `stdin_geometric_bound_by_max_length`'s number, reached the same way:
    filter away the cores that miss the fixed argv or file system, place
    what remains inside `short_inputs (n + 1)`, and evaluate that family
    exactly (`short_inputs_sum`, `geo_prefix_sum_closed`).

    It MISSES THE TAIL, and the tail is what
    `stdin_envp_geometric_mass_not_attained` below is made of. -/
theorem stdin_envp_geometric_bound_by_max_length (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → f.fin_stdin.length ≤ n) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      1 - Qpow (1 - p) (n + 1) := by
  show core_sum (envp_geo_weight p r q argv fs) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (envp_geo_weight p r q argv fs) (matches_argv_fs argv fs) _
    (fun c Hc => by
      rw [envp_geo_weight_mismatch p r q argv fs c (matches_argv_fs_false _ _ _ Hc)])]
  refine envp_geo_weight_stdin_family_bound p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    (short_inputs (n + 1)) (1 - Qpow (1 - p) (n + 1)) _ ?_
    (List.Nodup.sublist List.filter_sublist Hnd) ?_
  · rw [short_inputs_sum, geo_prefix_sum_closed]
    exact Rat.le_refl
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    refine ⟨matches_argv_fs_true _ _ _ Hm, ?_⟩
    apply short_inputs_complete
    have h := Hlen f Hf
    show f.fin_stdin.length < n + 1
    omega

/- =========================================================================... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= -/

/-- For `p_stop < 1` NO admissible list weighs the declared mass — every
    one of them weighs strictly less.  The proof is
    `stdin_geometric_mass_not_attained`'s, unchanged: the list's own
    longest standard input is a horizon, and beyond it sits a positive tail
    the list does not collect.

    Only `p_stop < 1` is asked for.  The environment coordinate needs no
    hypothesis at all here, and the reason is worth stating: the shortfall
    is already there on the standard-input axis alone, so degenerate `r` or
    `q_e` can only make it larger.  A family that tried to derive the
    strictness from the ENVIRONMENT axis would need `r < 1` instead, and
    would then be false at `r = 1` — where every environment is empty and
    only the standard input varies. -/
theorem stdin_envp_geometric_mass_not_attained (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (Hlt : p < 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l <
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass := by
  show core_sum (envp_geo_weight p r q argv fs) l < 1
  generalize hN : list_max (List.map (fun f => f.fin_stdin.length) l) = N
  have h1 : core_sum (envp_geo_weight p r q argv fs) l ≤ 1 - Qpow (1 - p) (N + 1) :=
    stdin_envp_geometric_bound_by_max_length p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
      N l Hnd (fun f Hf => by
        have hin : f.fin_stdin.length ∈ List.map (fun g => g.fin_stdin.length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for, beside
    `stdin_geometric_mass_supremum_not_maximum`. -/
theorem stdin_envp_geometric_mass_supremum_not_maximum (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (Hlt : p < 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l =
        (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass) :=
  Rat.ne_of_lt (stdin_envp_geometric_mass_not_attained p r q argv fs Hp0 Hp1 Hr0 Hr1
    Hq0 Hq1 Hlt l Hnd)

/- =========================================================================
   Two elementary inequalities the envp lower certificate runs on
   ========================================================================= -/

/-- BERNOULLI, in the one direction this file needs, stated multiplied out
    so that it carries no side condition beyond `0 <= x <= 1`.

    `geo_gap_bound` above is the other elementary estimate on the same
    quantity, and the two are used for opposite purposes.  That one bounds
    a power of `1 - p_stop` from ABOVE, which is how a TAIL is made small.
    This one bounds from BELOW, and it is needed because the environment
    coordinate's shortfall is a power OF A SUM: an enumeration of
    environments with at most `M` entries collects `G ^ M` of the
    per-entry mass, where `G` is what one entry slot collects, and turning
    "each slot misses at most `x`" into "the environment misses at most
    `M * x`" is exactly this inequality.

    The step is one square: `(1 - m * x) * (1 - x)` exceeds
    `1 - (1 + m) * x` by `m * x * x`. -/
theorem Qpow_one_minus_lower (x : Rat) (m : Nat) (Hx0 : 0 ≤ x) (Hx1 : x ≤ 1) :
    1 - Qnat m * x ≤ Qpow (1 - x) m := by
  have h1x : 0 ≤ 1 - x := by grind
  induction m with
  | zero =>
    rw [Qpow_0, Qnat_0]
    grind
  | succ m ih =>
    rw [Qpow_succ, Qnat_succ, Rat.mul_comm (1 - x) (Qpow (1 - x) m)]
    refine Rat.le_trans (b := (1 - Qnat m * x) * (1 - x)) ?_ ?_
    · have hxx : 0 ≤ Qnat m * x * x :=
        Rat.mul_nonneg (Rat.mul_nonneg (Qnat_nonneg m) Hx0) Hx0
      have hid : (1 - Qnat m * x) * (1 - x) =
          1 - (1 + Qnat m) * x + Qnat m * x * x := by grind
      rw [hid]
      grind
    · exact Rat.mul_le_mul_of_nonneg_right ih h1x

/-- THREE MARGINS COMPOSE, which is the arithmetic the certificate's three
    independent approximations meet in: if three factors fall short of `1`
    by `a`, `b` and `c`, their product falls short by at most `a + b + c`.
    The difference is `a * b * (1 - c) + c * (a + b)`, nonnegative term by
    term.  No bound on `a` or `b` is needed — only `c <= 1`, for the one
    factor the identity multiplies by. -/
theorem Qmargins_three (a b c : Rat) (Ha : 0 ≤ a) (Hb : 0 ≤ b) (Hc : 0 ≤ c)
    (Hc1 : c ≤ 1) :
    1 - (a + b + c) ≤ (1 - a) * (1 - b) * (1 - c) := by
  have h1c : 0 ≤ 1 - c := by grind
  have hd : 0 ≤ a * b * (1 - c) + c * (a + b) := by
    apply Qplus_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg Ha Hb) h1c
    · exact Rat.mul_nonneg Hc (Qplus_nonneg _ _ Ha Hb)
  have hid : (1 - a) * (1 - b) * (1 - c) =
      1 - (a + b + c) + (a * b * (1 - c) + c * (a + b)) := by grind
  rw [hid]
  grind

/- =========================================================================
   The environment witness family, and what it weighs
   ========================================================================= -/

/-- Every environment of EXACTLY `m` entries, each entry shorter than `L`,
    and then every environment of FEWER than `M` entries — the two are to
    `envp_enum` what `byte_lists` and `short_inputs` are to `cyl_enum`, and
    they are written the same way for the same reason: a slice at a time
    makes the sum below one `qsum_app` per step.

    `envp_enum` is not reused here even though it enumerates the same
    environments, because the certificate needs the list to be
    DUPLICATE-FREE and `envp_enum` is not: it names the stopping
    environment at every depth it passes through.  The bounds above never
    needed that, which is why they use the cheaper enumeration. -/
def envps_len (L : Nat) : Nat → List (List (List (BitVec 8)))
  | 0 => [[]]
  | m + 1 => (short_inputs L).flatMap (fun e => (envps_len L m).map (fun es => e :: es))

theorem envps_len_zero (L : Nat) : envps_len L 0 = [[]] := rfl

theorem envps_len_succ (L m : Nat) :
    envps_len L (m + 1) =
      (short_inputs L).flatMap (fun e => (envps_len L m).map (fun es => e :: es)) :=
  rfl

/-- Every environment of FEWER than `M` entries, each entry shorter than
    `L`, as a list.  It is `envps_len` concatenated over the depths, which
    is `short_inputs`' construction one level up. -/
def envps_upto (L : Nat) : Nat → List (List (List (BitVec 8)))
  | 0 => []
  | M + 1 => envps_len L M ++ envps_upto L M

theorem envps_upto_zero (L : Nat) : envps_upto L 0 = [] := rfl

theorem envps_upto_succ (L M : Nat) :
    envps_upto L (M + 1) = envps_len L M ++ envps_upto L M := rfl

theorem envps_len_In_length (L : Nat) : ∀ (m : Nat) (es : List (List (BitVec 8))),
    es ∈ envps_len L m → es.length = m := by
  intro m
  induction m with
  | zero =>
    intro es Hes
    rw [envps_len_zero] at Hes
    rcases List.mem_cons.mp Hes with h | h
    · rw [h]; rfl
    · exact absurd h (List.not_mem_nil)
  | succ m ih =>
    intro es Hes
    rw [envps_len_succ] at Hes
    obtain ⟨e, _, Hin⟩ := List.mem_flatMap.mp Hes
    obtain ⟨es', Hes', rfl⟩ := List.mem_map.mp Hin
    rw [List.length_cons, ih es' Hes']

theorem envps_len_In_entry (L : Nat) : ∀ (m : Nat) (es : List (List (BitVec 8)))
    (e : List (BitVec 8)), es ∈ envps_len L m → e ∈ es → e.length < L := by
  intro m
  induction m with
  | zero =>
    intro es e Hes He
    rw [envps_len_zero] at Hes
    rcases List.mem_cons.mp Hes with h | h
    · rw [h] at He
      cases He
    · exact absurd h (List.not_mem_nil)
  | succ m ih =>
    intro es e Hes He
    rw [envps_len_succ] at Hes
    obtain ⟨e0, He0, Hin⟩ := List.mem_flatMap.mp Hes
    obtain ⟨es', HEs', Heq'⟩ := List.mem_map.mp Hin
    rw [← Heq'] at He
    rcases List.mem_cons.mp He with h | h
    · rw [h]
      exact short_inputs_In_length L e0 He0
    · exact ih es' e HEs' h

/-- ... and it repeats nothing.  Distinct first entries give disjoint
    blocks, which is `NoDup_flat_map`'s third condition, and within a block
    consing a fixed entry is injective. -/
theorem envps_len_nodup (L : Nat) : ∀ m, (envps_len L m).Nodup := by
  intro m
  induction m with
  | zero =>
    rw [envps_len_zero, List.nodup_cons]
    exact ⟨fun h => absurd h (List.not_mem_nil), List.nodup_nil⟩
  | succ m ih =>
    rw [envps_len_succ]
    refine NoDup_flat_map _ _ (short_inputs_nodup L) ?_ ?_
    · intro e _
      apply NoDup_map_inj
      · intro x y _ _ heq
        exact (List.cons.inj heq).2
      · exact ih
    · intro e1 e2 es _ _ H1 H2
      obtain ⟨x1, _, Hx1⟩ := List.mem_map.mp H1
      obtain ⟨x2, _, Hx2⟩ := List.mem_map.mp H2
      have h : e1 :: x1 = e2 :: x2 := by rw [Hx1, Hx2]
      exact (List.cons.inj h).1

theorem envps_upto_In_length (L : Nat) : ∀ (M : Nat) (es : List (List (BitVec 8))),
    es ∈ envps_upto L M → es.length < M := by
  intro M
  induction M with
  | zero => intro es Hes; cases Hes
  | succ M ih =>
    intro es Hes
    rw [envps_upto_succ] at Hes
    rcases List.mem_append.mp Hes with h | h
    · rw [envps_len_In_length L M es h]; omega
    · have := ih es h; omega

theorem envps_upto_nodup (L : Nat) : ∀ M, (envps_upto L M).Nodup := by
  intro M
  induction M with
  | zero => exact List.nodup_nil
  | succ M ih =>
    rw [envps_upto_succ, List.nodup_append]
    refine ⟨envps_len_nodup L M, ih, ?_⟩
    intro es Hin1 es2 Hin2 h
    have h1 := envps_len_In_length L M es Hin1
    have h2 := envps_upto_In_length L M es2 Hin2
    rw [← h] at h2
    rw [h1] at h2
    omega

/-- The entry-length half of what `envps_upto` promises, which
    `envps_upto_In_length` leaves to `envps_len_In_entry` one level down.
    Stated because the pins below need the two halves at the same level:
    "this environment is NOT in the enumeration" is what makes a depth
    constraint load-bearing, and either depth can be the reason. -/
theorem envps_upto_In_entry (L : Nat) : ∀ (M : Nat) (es : List (List (BitVec 8)))
    (e : List (BitVec 8)), es ∈ envps_upto L M → e ∈ es → e.length < L := by
  intro M
  induction M with
  | zero => intro es e Hes _; cases Hes
  | succ M ih =>
    intro es e Hes He
    rw [envps_upto_succ] at Hes
    rcases List.mem_append.mp Hes with h | h
    · exact envps_len_In_entry L M es e h He
    · exact ih es e h He

/-- ... and CONVERSELY the enumeration misses no environment inside its
    two depths, which is `short_inputs_complete` one level up and is needed
    for the same kind of reason: to place a FIXED environment inside the
    family rather than merely to read lengths off the family.

    This is the containment the mixture's shared witness turns on.
    `envps_upto L M` holds every environment of fewer than `M` entries each
    shorter than `L`, so a task's canonical environment — whatever it is —
    is in there as soon as `M` exceeds its entry count and `L` its longest
    entry.  Neither depth is free: the certificate that chooses them for
    the margin has to be asked for depths at least this large as well,
    which is what `geo_gap_small_above` is for, and the pins at the end of
    this family show what goes wrong when either is short. -/
theorem envps_len_complete (L : Nat) (es : List (List (BitVec 8)))
    (Hlen : ∀ e, e ∈ es → e.length < L) : es ∈ envps_len L es.length := by
  induction es with
  | nil =>
    rw [List.length_nil, envps_len_zero]
    exact List.mem_cons_self ..
  | cons e es ih =>
    rw [List.length_cons, envps_len_succ, List.mem_flatMap]
    refine ⟨e, short_inputs_complete L e (Hlen e (List.mem_cons_self ..)), ?_⟩
    exact List.mem_map.mpr
      ⟨es, ih (fun e' He' => Hlen e' (List.mem_cons_of_mem _ He')), rfl⟩

theorem envps_upto_complete (L : Nat) : ∀ (M : Nat) (es : List (List (BitVec 8))),
    es.length < M → (∀ e, e ∈ es → e.length < L) → es ∈ envps_upto L M := by
  intro M
  induction M with
  | zero => intro es Hlt _; omega
  | succ M ih =>
    intro es Hlt Hlen
    rw [envps_upto_succ]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ Hlt) with heq | hlt
    · refine List.mem_append.mpr (Or.inl ?_)
      rw [← heq]
      exact envps_len_complete L es Hlen
    · exact List.mem_append.mpr (Or.inr (ih es hlt Hlen))

/-- ONE FULL ENTRY-COUNT SLICE weighs a power: the `m` entry slots are
    independent, each collects what the entry enumeration collects, and the
    total is that number to the `m`-th.  The base is
    `1 - (1 - q_e) ^ L`, which is `short_inputs_sum` closed by
    `geo_prefix_sum_closed` — the same number `qsum_envp_factor_step`
    charges one slot above. -/
theorem qsum_entries_geo_product_envps_len (q : Rat) (L m : Nat) :
    qsum (entries_geo_product q) (envps_len L m) = Qpow (1 - Qpow (1 - q) L) m := by
  induction m with
  | zero =>
    rw [envps_len_zero, qsum_cons, qsum_nil, entries_geo_product_nil, Qpow_0]
    grind
  | succ m ih =>
    rw [envps_len_succ, qsum_flat_map]
    rw [qsum_ext
      (fun e => qsum (entries_geo_product q)
        ((envps_len L m).map (fun es => e :: es)))
      (fun e => Qpow (1 - Qpow (1 - q) L) m * geo_point q e.length) _ ?_]
    · rw [qsum_scale, short_inputs_sum, geo_prefix_sum_closed, Qpow_succ]
      exact Rat.mul_comm _ _
    · intro e _
      rw [qsum_map]
      rw [qsum_ext (fun es => entries_geo_product q (e :: es))
        (fun es => geo_point q e.length * entries_geo_product q es) _
        (fun es _ => entries_geo_product_cons q e es)]
      rw [qsum_scale, ih]
      grind

theorem qsum_envp_point_envps_len (r q : Rat) (L m : Nat) :
    qsum (envp_point r q) (envps_len L m) =
      r * Qpow (1 - r) m * Qpow (1 - Qpow (1 - q) L) m := by
  rw [qsum_ext (envp_point r q)
    (fun es => (r * Qpow (1 - r) m) * entries_geo_product q es) _
    (fun es Hes => by
      rw [envp_point_closed_form, envps_len_In_length L m es Hes])]
  rw [qsum_scale, qsum_entries_geo_product_envps_len]

/-- The partial sum of the environment series over ENTRY COUNTS, as a
    definition so that it is a rational a task can write down.  It is
    `geo_prefix_sum`'s counterpart on the other coordinate, with one
    difference that is the whole reason it needs its own definition: the
    ratio here is `(1 - r) * G` rather than `1 - r`, because an
    environment that continues must also fill the slot it opened, and the
    slot collects `G` rather than everything.

    No closed form is stated, and that is deliberate.  `geo_prefix_sum`
    telescopes to `1 - (1 - p_stop) ^ k` because its ratio and its
    per-term factor are the same number; here they are not, so the closed
    form would be a quotient with a side condition on `1 - (1 - r) * G`.
    What the certificate actually needs is a LOWER bound, and
    `envp_prefix_sum_lower` gives one with no side condition at all. -/
def envp_prefix_sum (r G : Rat) : Nat → Rat
  | 0 => 0
  | M + 1 => r * Qpow (1 - r) M * Qpow G M + envp_prefix_sum r G M

theorem envp_prefix_sum_zero (r G : Rat) : envp_prefix_sum r G 0 = 0 := rfl

theorem envp_prefix_sum_succ (r G : Rat) (M : Nat) :
    envp_prefix_sum r G (M + 1) =
      r * Qpow (1 - r) M * Qpow G M + envp_prefix_sum r G M := rfl

/-- The environment prefix family's total, over entry counts, is the
    partial sum: one `qsum_app` per depth and `qsum_envp_point_envps_len`
    at each. -/
theorem qsum_envp_point_envps_upto (r q : Rat) (L : Nat) : ∀ M,
    qsum (envp_point r q) (envps_upto L M) =
      envp_prefix_sum r (1 - Qpow (1 - q) L) M := by
  intro M
  induction M with
  | zero => rw [envps_upto_zero, qsum_nil, envp_prefix_sum_zero]
  | succ M ih =>
    rw [envps_upto_succ, qsum_app, ih, qsum_envp_point_envps_len,
      envp_prefix_sum_succ]

/-- THE LOWER ESTIMATE: the partial sum is at least `G ^ M` times what the
    entry-count geometric alone would have collected.

    The estimate is the obvious one — every term of the sum carries `G ^ m`
    for some `m <= M`, and `G ^ m` is at least `G ^ M` because `G <= 1` —
    and it is enough because BOTH factors go to `1` as their parameters
    grow: `1 - (1 - r) ^ M` by `geo_gap_small` on `r`, and `G ^ M` by
    `Qpow_one_minus_lower` once `L` is chosen after `M`.  That ordering is
    the only subtlety in the certificate below, and it is why `L` is
    chosen last. -/
theorem envp_prefix_sum_lower (r G : Rat) (M : Nat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (HG0 : 0 ≤ G) (HG1 : G ≤ 1) :
    Qpow G M * (1 - Qpow (1 - r) M) ≤ envp_prefix_sum r G M := by
  have h1r : 0 ≤ 1 - r := by grind
  have h1r1 : 1 - r ≤ 1 := by grind
  induction M with
  | zero =>
    show Qpow G 0 * (1 - Qpow (1 - r) 0) ≤ 0
    rw [Qpow_0, Qpow_0]
    grind
  | succ M ih =>
    rw [envp_prefix_sum_succ]
    have hX : 0 ≤ 1 - Qpow (1 - r) (M + 1) := by
      have h := Qpow_le_1 (1 - r) (M + 1) h1r h1r1
      grind
    refine Rat.le_trans (b := Qpow G M * (1 - Qpow (1 - r) (M + 1))) ?_ ?_
    · have h1 : G * Qpow G M ≤ 1 * Qpow G M :=
        Rat.mul_le_mul_of_nonneg_right HG1 (Qpow_nonneg G M HG0)
      have h2 := Rat.mul_le_mul_of_nonneg_right h1 hX
      rw [Qpow_succ G M]
      refine Rat.le_trans h2 ?_
      grind
    · refine Rat.le_trans (b := r * Qpow (1 - r) M * Qpow G M +
        Qpow G M * (1 - Qpow (1 - r) M)) ?_ ?_
      · have hid : Qpow G M * (1 - Qpow (1 - r) (M + 1)) =
            r * Qpow (1 - r) M * Qpow G M + Qpow G M * (1 - Qpow (1 - r) M) := by
          rw [Qpow_succ (1 - r) M]
          grind
        rw [hid]
        exact Rat.le_refl
      · exact Qplus_le_compat (Rat.le_refl) ih

/- =========================================================================
   The lower certificate for `stdin_envp_geometric`
   ========================================================================= -/

/-- THE WITNESS FAMILY: over the fixed argv and file system, one record per
    (environment, standard input) pair drawn from the two prefix families.
    It is a product, exactly as the bounds' enumeration is, and it is
    duplicate-free because both coordinates are
    (`NoDup_envp_stdin_product`).

    As everywhere in this file, these records are NOT claimed valid and NOT
    claimed rejected by anything; the certificate is arithmetic about the
    declared mass. -/
def envp_geo_lower_witness (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (M L k : Nat) : List FinProcInput :=
  List.map core_input (envp_stdin_product argv fs (envps_upto L M) (short_inputs k))

theorem map_fin_core_envp_geo_lower_witness (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (M L k : Nat) :
    List.map fin_core (envp_geo_lower_witness argv fs M L k) =
      envp_stdin_product argv fs (envps_upto L M) (short_inputs k) := by
  unfold envp_geo_lower_witness
  exact map_fin_core_core_input _

theorem envp_geo_lower_witness_nodup (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (M L k : Nat) :
    (List.map fin_core (envp_geo_lower_witness argv fs M L k)).Nodup := by
  rw [map_fin_core_envp_geo_lower_witness]
  exact NoDup_envp_stdin_product argv fs _ _ (envps_upto_nodup L M) (short_inputs_nodup k)

/-- THE WITNESS, at each triple of depths: an admissible list weighing
    exactly the product of the two coordinates' partial sums.

    No hypothesis beyond the constructor's own is needed HERE, for the
    reason `stdin_geometric_mass_lower_witness` needs none: the equality is
    unconditional arithmetic.  All three strictnesses enter one lemma
    later, where the three depths have to be CHOSEN to meet a target. -/
theorem stdin_envp_geometric_mass_lower_witness (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (M L k : Nat) :
    (List.map fin_core (envp_geo_lower_witness argv fs M L k)).Nodup ∧
      core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        (envp_geo_lower_witness argv fs M L k) =
        envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  refine ⟨envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  show core_sum (envp_geo_weight p r q argv fs) _ = _
  rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness,
    qsum_envp_stdin_product, qsum_envp_point_envps_upto, short_inputs_sum,
    geo_prefix_sum_closed]

/-- THE MARGIN ARITHMETIC OF THE CERTIFICATE, WITH THE DEPTHS STILL FREE.
    Given three depths whose three tails together come in under `eps`, the
    witness's partial sum is within `eps` of `1`.  Nothing about a
    distribution appears — it is a statement about `envp_prefix_sum` and
    two powers — and that is why it is stated apart: the certificate below
    and the mixture certificate further down consume it at DIFFERENT
    depths, and only the choice of depths differs between them.

    Three approximations meet here and each is charged separately.  The
    entry-count tail is `(1 - r) ^ M`; the standard-input tail is
    `(1 - p_stop) ^ k`; and the entry-length shortfall is `M` slots each
    missing `(1 - q_e) ^ L`, which is where the `Qnat M` factor comes from
    (`Qpow_one_minus_lower` turns a per-slot miss into a per-environment
    one).  `Qmargins_three` composes the three, and
    `envp_prefix_sum_lower` is what puts the entry-count partial sum under
    the product.

    NO STRICT HYPOTHESIS APPEARS, and that is the point of the split:
    strictness is spent choosing depths, never in the arithmetic that uses
    them. -/
theorem envp_stdin_margin_at_depths (p r q eps : Rat) (M L k : Nat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hsum : Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k ≤ eps) :
    1 - eps ≤ envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  have Hx0 : 0 ≤ Qpow (1 - q) L := Qpow_nonneg _ _ (by grind)
  have H1q1 : 1 - q ≤ 1 := by grind
  have Hx1 : Qpow (1 - q) L ≤ 1 := Qpow_le_1 _ _ (by grind) H1q1
  have Hb0 : 0 ≤ Qpow (1 - r) M := Qpow_nonneg _ _ (by grind)
  have H1r1 : 1 - r ≤ 1 := by grind
  have Hb1 : Qpow (1 - r) M ≤ 1 := Qpow_le_1 _ _ (by grind) H1r1
  have Hc0 : 0 ≤ Qpow (1 - p) k := Qpow_nonneg _ _ (by grind)
  have H1p1 : 1 - p ≤ 1 := by grind
  have Hc1 : Qpow (1 - p) k ≤ 1 := Qpow_le_1 _ _ (by grind) H1p1
  have Ha0 : 0 ≤ Qnat M * Qpow (1 - q) L := Rat.mul_nonneg (Qnat_nonneg M) Hx0
  have HG0 : 0 ≤ 1 - Qpow (1 - q) L := by grind
  have HG1 : 1 - Qpow (1 - q) L ≤ 1 := by grind
  have hBC : 0 ≤ 1 - Qpow (1 - r) M := by grind
  have hCC : 0 ≤ 1 - Qpow (1 - p) k := by grind
  refine Rat.le_trans
    (b := 1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k)) ?_ ?_
  · rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hsum)
  · refine Rat.le_trans (Qmargins_three _ _ _ Ha0 Hb0 Hc0 Hc1) ?_
    have h3 : (1 - Qnat M * Qpow (1 - q) L) * (1 - Qpow (1 - r) M) ≤
        envp_prefix_sum r (1 - Qpow (1 - q) L) M :=
      Rat.le_trans
        (Rat.mul_le_mul_of_nonneg_right (Qpow_one_minus_lower _ M Hx0 Hx1) hBC)
        (envp_prefix_sum_lower r (1 - Qpow (1 - q) L) M Hr0 Hr1 HG0 HG1)
    exact Rat.mul_le_mul_of_nonneg_right h3 hCC

/-- ... AND THE DEPTHS THAT MEET IT, above any floors asked for.

    Each strictness buys exactly one depth, and the three are chosen in an
    order that matters.  `geo_gap_small_above` on `r` gives an entry count
    `M` past which the environments are too long to matter;
    `geo_gap_small` on `p_stop` gives a standard-input length `k`; and
    then — LAST, because the bound it has to meet mentions `M` — on `q_e`
    it gives an entry length `L` with `(1 - q_e) ^ L` under
    `eps / (3 * (M + 1))`, so that all `M` entry slots together miss at
    most a third of the margin.  The three thirds are what
    `envp_stdin_margin_at_depths` then composes.

    `M0` AND `L0` ARE THE FLOORS, and they are the reason this is not
    inlined into the certificate.  A certificate serving one family takes
    them both `0` and the choice is the margin's alone; a mixture also has
    to reach a fixed environment, and passes that environment's entry
    count and longest entry.  Only the two environment depths are floored:
    nothing outside this family ever asks for a deeper standard input than
    the margin does.

    `Qpow (1 - p_stop) k <= eps` is reported separately from the sum even
    though it follows from it, because the mixture's OTHER component is
    bounded by that tail alone and would otherwise have to re-derive it
    from the nonnegativity of the two environment terms. -/
theorem envp_stdin_depths_above (p r q eps : Rat) (M0 L0 : Nat)
    (Hp0 : 0 < p) (Hp1 : p ≤ 1) (Hr0 : 0 < r) (Hr1 : r ≤ 1)
    (Hq0 : 0 < q) (Hq1 : q ≤ 1) (Heps : 0 < eps) :
    ∃ M L k : Nat, M0 ≤ M ∧ L0 ≤ L ∧
      Qnat M * Qpow (1 - q) L + Qpow (1 - r) M + Qpow (1 - p) k ≤ eps ∧
      Qpow (1 - p) k ≤ eps := by
  have hthird0 : (0 : Rat) < 1 / 3 := Qpos_one_div 3 (by decide)
  have heps3 : 0 < eps * (1 / 3) := Rat.mul_pos Heps hthird0
  have hthird : eps * (1 / 3) ≤ eps := by
    have h := Rat.mul_le_mul_of_nonneg_left
      (show (1 / 3 : Rat) ≤ 1 by grind) (Rat.le_of_lt Heps)
    rwa [Rat.mul_one] at h
  obtain ⟨M, HM0, HM⟩ := geo_gap_small_above r (eps * (1 / 3)) M0 Hr0 Hr1 heps3
  obtain ⟨k, Hk⟩ := geo_gap_small p (eps * (1 / 3)) Hp0 Hp1 heps3
  have hD : (0 : Rat) < Qnat M + 1 := by
    have := Qnat_nonneg M
    grind
  have hDpos : 0 < (Qnat M + 1)⁻¹ := Rat.inv_pos.mpr hD
  have hbnd : 0 < eps * (1 / 3) * (Qnat M + 1)⁻¹ := Rat.mul_pos heps3 hDpos
  obtain ⟨L, HL0, HL⟩ := geo_gap_small_above q (eps * (1 / 3) * (Qnat M + 1)⁻¹) L0
    Hq0 Hq1 hbnd
  refine ⟨M, L, k, HM0, HL0, ?_, Rat.le_trans Hk hthird⟩
  have hMle : Qnat M * (Qnat M + 1)⁻¹ ≤ 1 := by
    have hle : Qnat M ≤ Qnat M + 1 := by grind
    have hinv : 0 ≤ (Qnat M + 1)⁻¹ := Rat.le_of_lt hDpos
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hle hinv) ?_
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hD)]
    exact Rat.le_refl
  have hA : Qnat M * Qpow (1 - q) L ≤ eps * (1 / 3) := by
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left HL (Qnat_nonneg M)) ?_
    have hid : Qnat M * (eps * (1 / 3) * (Qnat M + 1)⁻¹) =
        (Qnat M * (Qnat M + 1)⁻¹) * (eps * (1 / 3)) := by grind
    rw [hid]
    have h := Rat.mul_le_mul_of_nonneg_right hMle (Rat.le_of_lt heps3)
    rwa [Rat.one_mul] at h
  refine Rat.le_trans (b := eps * (1 / 3) + eps * (1 / 3) + eps * (1 / 3)) ?_ ?_
  · exact Qplus_le_compat (Qplus_le_compat hA HM) Hk
  · grind

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass minus that margin.  With
    `stdin_envp_geometric_mass_upper` above it, the declared `1` is the
    least upper bound of the admissible partial sums — approached but, by
    `stdin_envp_geometric_mass_not_attained`, never met.

    ALL THREE STRICT INEQUALITIES ARE HYPOTHESES OF THIS LEMMA AND NOT
    TIGHTENINGS OF THE CONSTRUCTOR, for the reason
    `stdin_geometric_mass_lower_certificate` gives: everything above this
    lemma, the upper certificate included, holds at `p_stop = 0`, `r = 0`
    and `q_e = 0`, and moving the hypotheses into the constructor would
    invalidate every degenerate member a consumer had already built.

    Each strictness buys exactly one depth, and the order in which the
    three are chosen matters; `envp_stdin_depths_above` is where that
    happens, and it is asked for no floors here because nothing but the
    margin has a say for a single family.  What is left in this proof is
    the witness and its exact partial sum, with
    `envp_stdin_margin_at_depths` doing the arithmetic.

    Nothing here is a limit and nothing is approximated: a margin is asked
    for, three natural numbers are produced, and the finite list they name
    is exhibited. -/
theorem stdin_envp_geometric_mass_lower_certificate (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (eps : Rat)
    (Hppos : 0 < p) (Hrpos : 0 < r) (Hqpos : 0 < q) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass - eps ≤
        core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l := by
  obtain ⟨M, L, k, _, _, Hsum, _⟩ :=
    envp_stdin_depths_above p r q eps 0 0 Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps
  refine ⟨envp_geo_lower_witness argv fs M L k, envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  rw [(stdin_envp_geometric_mass_lower_witness p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k).2]
  show (1 : Rat) - eps ≤
    envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k)
  exact envp_stdin_margin_at_depths p r q eps M L k Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum

/- =========================================================================
   Non-vacuity: the environment really carries mass, and where each
   strictness is spent
   ========================================================================= -/

/-- `geo_weight`'s envp instance, stated because the bite below needs it
    and the file has only the argv one.  It is the same
    `geo_weight_mismatch` the comment at `geo_weight_off_environment_zero`
    says envp goes through. -/
theorem geo_weight_off_envp_zero (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (c : FinCore) (Hne : c.core_envp ≠ envp) :
    geo_weight p argv envp fs c = 0 := by
  apply geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_envp Heq)

/-- The geometric weight at length zero is the stopping rate itself — the
    base case every closed computation in this file needs. -/
theorem geo_point_at_zero (p : Rat) : geo_point p 0 = p := by
  unfold geo_point geo_mass
  rw [Qpow_0]
  grind

/-- The environment weight of the one-entry environment whose entry is
    empty: `r * (1 - r)`, the only positive member left at `q_e = 1`. -/
theorem envp_point_single_empty (r : Rat) : envp_point r 1 [[]] = r * (1 - r) := by
  unfold envp_point
  rw [envp_factor_cons, envp_factor_nil]
  show r * ((1 - r) * geo_point 1 0 * 1) = r * (1 - r)
  rw [geo_point_at_zero]
  grind

/-- Strict positivity of the two new factors, at any non-degenerate member
    of the family.  `envp_point_pos` is an induction over the entries and
    is where the family's whole point becomes arithmetic: an environment of
    ANY length weighs something, because every factor in the running
    product does. -/
theorem geo_point_pos (q : Rat) (n : Nat) (Hq0 : 0 < q) (Hq1 : q < 1) :
    0 < geo_point q n := by
  unfold geo_point geo_mass
  exact Rat.mul_pos Hq0 (Qpow_pos _ _ (Rat.mul_pos (by grind) (Qpos_one_div 256 (by decide))))

theorem envp_point_pos (r q : Rat) (es : List (List (BitVec 8)))
    (Hr0 : 0 < r) (Hr1 : r < 1) (Hq0 : 0 < q) (Hq1 : q < 1) :
    0 < envp_point r q es := by
  unfold envp_point
  refine Rat.mul_pos Hr0 ?_
  induction es with
  | nil => show (0 : Rat) < 1; exact by decide
  | cons e es ih =>
    rw [envp_factor_cons]
    exact Rat.mul_pos (Rat.mul_pos (by grind) (geo_point_pos q e.length Hq0 Hq1)) ih

/-- A core over a NON-CANONICAL launch-time environment: one entry, the
    single byte `A`.  As at `geo_example_core` it is not claimed valid; it
    is a point of `FinInput.FinCore` chosen so that the two families
    disagree at it. -/
def envp_example_named : FinCore :=
  FinCore.mkFinCore [] [[BitVec.ofInt 8 65]] [] []

/-- THE BITE THE FAMILY EXISTS FOR, both halves on ONE core.
    `stdin_geometric` over the empty environment weighs `envp_example_named`
    exactly zero — its envp is not the fixed one — while
    `stdin_envp_geometric` weighs it strictly positively.

    That is the gap restated as a theorem.  Under a distribution built from
    `stdin_geometric` alone, a fire set living at cores like this one lies
    in a NULL set, so both classifier fire-set bounds are satisfied by it
    vacuously and say nothing about whatever defect put it there.  Under
    this family they do not: the core carries weight, so a
    `Measure.weight_bound_T` claim about a fire set containing it is a
    claim with content.

    What it does NOT say, and the misreading is the same one the header
    warns about at the geometric lower certificate: that any particular
    task's bound is thereby sharper.  Weight on a core is what makes a
    bound about that core non-vacuous; it is not itself a bound. -/
theorem stdin_envp_geometric_envp_bites (p r q : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hppos : 0 < p) (Hplt : p < 1) (Hrpos : 0 < r) (Hrlt : r < 1)
    (Hqpos : 0 < q) (Hqlt : q < 1) :
    (stdin_geometric p [] [] [] Hp0 Hp1).cd_weight envp_example_named = 0 ∧
      0 < (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        envp_example_named := by
  refine ⟨?_, ?_⟩
  · show geo_weight p [] [] [] envp_example_named = 0
    apply geo_weight_off_envp_zero
    show [[BitVec.ofInt 8 65]] ≠ []
    intro h
    cases h
  · show 0 < envp_geo_weight p r q [] [] envp_example_named
    rw [show envp_example_named = FinCore.mkFinCore [] [[BitVec.ofInt 8 65]] [] [] from rfl,
      envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q _ Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 0 Hppos Hplt)

/-- ... and the family is still not constant: a core whose argv misses the
    fixed one weighs exactly zero, exactly as under `stdin_geometric`.  Both
    halves are needed for the same reason `stdin_geometric_bites` needs
    both — without this one, "weight zero off the fixed argv and file
    system" would be a claim only the definition makes. -/
theorem envp_geo_weight_off_argv_zero (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore)
    (Hne : c.core_argv ≠ argv) : envp_geo_weight p r q argv fs c = 0 := by
  apply envp_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

theorem stdin_envp_geometric_bites (p r q : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hppos : 0 < p) (Hplt : p < 1) (Hrpos : 0 < r) (Hrlt : r < 1)
    (Hqpos : 0 < q) (Hqlt : q < 1) :
    0 < (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        geo_example_core ∧
      (stdin_envp_geometric p r q [] [] Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        geo_example_other = 0 := by
  refine ⟨?_, ?_⟩
  · show 0 < envp_geo_weight p r q [] [] geo_example_core
    rw [show geo_example_core = FinCore.mkFinCore [] [] [] [] from rfl,
      envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q [] Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 0 Hppos Hplt)
  · show envp_geo_weight p r q [] [] geo_example_other = 0
    apply envp_geo_weight_off_argv_zero
    show [[BitVec.ofInt 8 65]] ≠ []
    intro h
    cases h

/- =========================================================================
   Non-vacuity: `List.NoDup` is load-bearing here too
   ========================================================================= -/

/-- The member of the family at `p_stop = r = q_e = 1`: stop immediately on
    every axis.  It is the point mass on the core with no environment and
    no standard input, it is admitted by the constructor — `Qle_0_1` and
    `Rat.le_refl` three times over — and it is what makes the refutation
    below closed arithmetic instead of open terms.  It is also the `r = 1`
    collapse at a concrete instance: by
    `envp_geo_weight_collapses_at_one_r` it weighs exactly as `geo_point_cd`
    does. -/
def envp_point_cd : CoreDistribution :=
  stdin_envp_geometric 1 1 1 [] [] Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl

/-- The core weight of `envp_point_cd` at the empty core is `1`, which is
    the arithmetic the refutation below needs in closed form. -/
theorem envp_point_cd_weight_empty :
    envp_point_cd.cd_weight geo_example_core = 1 := by
  show envp_geo_weight 1 1 1 [] [] geo_example_core = 1
  rw [show geo_example_core = FinCore.mkFinCore [] [] [] [] from rfl,
    envp_geo_weight_match]
  show envp_point 1 1 [] * geo_point 1 0 = 1
  unfold envp_point envp_factor geo_point geo_mass
  rw [Qpow_0]
  grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING for this family's cylinder
    bound, and this is `stdin_geometric_bound_needs_nodup` transposed:
    offer the same core twice — two records, so the list is duplicate-free
    as a list of RECORDS, and both records lie in the cylinder over the
    empty environment prefix and the empty standard-input prefix — and the
    sum is `2` against a cylinder mass of `1`.

    All three conjuncts are needed, for the reasons the baseline lemma
    gives: the second says the list really does satisfy the cylinder
    hypothesis, so it is not excluded by that; the third says the bound
    genuinely fails on it; the first names what does exclude it. -/
theorem stdin_envp_geometric_bound_needs_nodup :
    ¬ (List.map fin_core [geo_empty_input, geo_empty_input]).Nodup ∧
      (∀ f, f ∈ [geo_empty_input, geo_empty_input] →
        in_envp_stdin_cylinder [] [] [] [] (fin_core f)) ∧
      ¬ (core_sum envp_point_cd.cd_weight [geo_empty_input, geo_empty_input] ≤
        stdin_envp_geometric_cylinder_mass 1 1 1 [] []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.mem_cons_self ..)
  · intro f Hf
    have hfc : f = geo_empty_input →
        fin_core f = FinCore.mkFinCore [] [] [] [] := by
      intro h; rw [h]; rfl
    rcases List.mem_cons.mp Hf with h | h
    · exact ⟨[], [], hfc h⟩
    · rcases List.mem_cons.mp h with h2 | h2
      · exact ⟨[], [], hfc h2⟩
      · exact absurd h2 (List.not_mem_nil)
  · intro Hle
    have hsum : core_sum envp_point_cd.cd_weight [geo_empty_input, geo_empty_input] = 2 := by
      show envp_geo_weight 1 1 1 [] [] (fin_core geo_empty_input) +
        (envp_geo_weight 1 1 1 [] [] (fin_core geo_empty_input) + 0) = 2
      have hfc : fin_core geo_empty_input = geo_example_core := rfl
      have hw : envp_geo_weight 1 1 1 [] [] geo_example_core = 1 :=
        envp_point_cd_weight_empty
      rw [hfc, hw]
      grind
    have hm : stdin_envp_geometric_cylinder_mass 1 1 1 [] [] = 1 := by
      show (1 : Rat) * 1 = 1
      grind
    rw [hsum, hm] at Hle
    exact absurd Hle (by grind)

/-- THE FIVE DEGENERATE MEMBERS, and each one says which side condition is
    doing work where.

    At `p_stop = 0` and at `r = 0` the weight vanishes identically — every
    list weighs nothing while the declared mass stays `1`, so the lower
    certificate is false there and its hypotheses are not inherited
    caution.  At `q_e = 0`, at `r = 1` and at `q_e = 1` the weight does NOT
    vanish, and those three are the interesting ones: a whole class of
    non-empty environments weighs zero, so the family collapses back
    towards `stdin_geometric` and is as blind to the launch-time
    environment as `stdin_geometric` is.  Those are the failure modes worth
    pinning, because they are the ones that would go unnoticed: the
    distribution is still non-zero, still sums correctly, and still
    measures nothing about the environment.

    The `q_e = 1` pin is at the end of this section; the class of
    environments it kills is described by a non-empty ENTRY rather than by
    a non-empty environment, and the comment there says why that
    distinction is load-bearing. -/
theorem envp_geo_weight_zero_at_zero_p (r q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore) :
    envp_geo_weight 0 r q argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · next _ =>
    unfold geo_point
    grind
  · rfl

theorem envp_geo_weight_zero_at_zero_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore) :
    envp_geo_weight p 0 q argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · next _ =>
    unfold envp_point
    grind
  · rfl

theorem envp_geo_weight_zero_at_zero_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore)
    (Hne : c.core_envp ≠ []) :
    envp_geo_weight p r 0 argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · next _ =>
    rcases h : c.core_envp with _ | ⟨e, es⟩
    · exact absurd h Hne
    · show envp_point r 0 (e :: es) * geo_point p c.core_stdin.length = 0
      unfold envp_point envp_factor geo_point
      grind
  · rfl

/-- `r = 1` IS ADMITTED BY THE CONSTRUCTOR — `Qle_0_1` and `Rat.le_refl`
    are its two side conditions, exactly as at `geo_point_cd` — and at it
    the running product's `1 - r` factor is zero, so every core with a
    non-empty environment weighs nothing.

    The collapse is total rather than partial, and stating it that way is
    sharper than stating the blindness: at `r = 1` this family IS
    `stdin_geometric` over the EMPTY launch-time environment, weight for
    weight and at every core, including the ones both weigh zero.  Two of
    the four cases below are the interesting ones — a core matching argv
    and the file system whose environment is empty is weighed the full
    standard-input weight by both, and one whose environment is not empty
    is weighed zero by both, the new family because its product has a zero
    factor and the old one because the environment misses the fixed value.

    `r < 1` is therefore genuinely asked for, by `envp_point_pos` and
    through it by `stdin_envp_geometric_envp_bites`, and this is where it
    is pinned. -/
theorem envp_geo_weight_collapses_at_one_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore) :
    envp_geo_weight p 1 q argv fs c = geo_weight p argv [] fs c := by
  unfold envp_geo_weight geo_weight
  by_cases hm : c = FinCore.mkFinCore argv c.core_envp fs c.core_stdin
  · by_cases he : c = FinCore.mkFinCore argv [] fs c.core_stdin
    · rw [ite_eq_left hm, ite_eq_left he]
      have henv : c.core_envp = [] := congrArg FinCore.core_envp he
      rw [henv]
      show envp_point 1 q [] * geo_point p c.core_stdin.length = geo_point p c.core_stdin.length
      unfold envp_point envp_factor
      grind
    · rw [ite_eq_left hm, ite_eq_right he]
      rcases h : c.core_envp with _ | ⟨e, es⟩
      · rw [h] at hm
        exact absurd hm he
      · show envp_point 1 q (e :: es) * geo_point p c.core_stdin.length = 0
        unfold envp_point envp_factor
        grind
  · by_cases he : c = FinCore.mkFinCore argv [] fs c.core_stdin
    · rw [ite_eq_right hm, ite_eq_left he]
      exact absurd he (by
        intro h
        apply hm
        have henv : c.core_envp = [] := congrArg FinCore.core_envp h
        rw [henv]
        exact h)
    · rw [ite_eq_right hm, ite_eq_right he]

theorem stdin_envp_geometric_collapses_at_one_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    (stdin_envp_geometric p 1 q argv fs Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1).cd_weight c =
      (stdin_geometric p argv [] fs Hp0 Hp1).cd_weight c := by
  show envp_geo_weight p 1 q argv fs c = geo_weight p argv [] fs c
  exact envp_geo_weight_collapses_at_one_r p q argv fs c

/-- ... and so the blindness, in the shape
    `stdin_envp_geometric_envp_needs_positive_q` states it for the other
    non-vanishing degeneracy.  Both are exported: a reader asking "what
    goes wrong at this parameter" wants the blindness, and a reader asking
    "what does the family become" wants the collapse. -/
theorem stdin_envp_geometric_envp_needs_r_below_one (p q : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore)
    (Hne : c.core_envp ≠ []) :
    (stdin_envp_geometric p 1 q argv fs Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1).cd_weight c = 0 := by
  rw [stdin_envp_geometric_collapses_at_one_r p q argv fs Hp0 Hp1 Hq0 Hq1 c]
  show geo_weight p argv [] fs c = 0
  exact geo_weight_off_envp_zero p argv [] fs c Hne

theorem stdin_envp_geometric_mass_lower_needs_positive (argv : List (List (BitVec 8)))
    (fs : Fs.Fs) (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    (∀ l : List FinProcInput,
      core_sum (stdin_envp_geometric 0 r q argv fs Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1).cd_weight
        l = 0) ∧
      ¬ ((stdin_envp_geometric 0 r q argv fs Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1).cd_mass -
        1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show envp_geo_weight 0 r q argv fs c = 0
    exact envp_geo_weight_zero_at_zero_p r q argv fs c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

theorem stdin_envp_geometric_envp_needs_positive_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore)
    (Hne : c.core_envp ≠ []) :
    (stdin_envp_geometric p r 0 argv fs Hp0 Hp1 Hr0 Hr1 Rat.le_refl Qle_0_1).cd_weight c = 0 := by
  show envp_geo_weight p r 0 argv fs c = 0
  exact envp_geo_weight_zero_at_zero_q p r argv fs c Hne

/-- THE FIFTH DEGENERATE MEMBER, `q_e = 1`, and it went unpinned when the
    other four were.  The constructor asks `0 <= q_e <= 1`, so it is
    buildable, and at it `geo_point 1 m` is zero for every `m >= 1`: an
    environment holding ANY non-empty entry weighs nothing, while
    environments made only of empty entries keep their weight.

    That is the `q_e = 0` failure mode one axis over and it is worse in
    practice, because a real environment entry is a `NAME=value` string:
    the family is blind to every environment a program will actually see
    and has NOT gone quiet — still non-zero, still summing correctly, still
    declaring mass `1` honestly.  And `q_e < 1` IS asked for, by
    `envp_point_pos` and through it by `stdin_envp_geometric_envp_bites`,
    which is the file's own criterion for pinning an endpoint.

    THE HYPOTHESIS NAMES A NON-EMPTY ENTRY, NOT A NON-EMPTY ENVIRONMENT,
    and the difference is not pedantry: the environment `[[]]` — one entry,
    empty — weighs a positive amount at `q_e = 1`, so this is not
    `stdin_envp_geometric_envp_needs_positive_q` with `0` replaced by `1`.
    Membership rather than "the first entry" because a real environment's
    blind entry need not be first, and the induction below costs nothing
    extra for the stronger form. -/
theorem envp_factor_zero_at_one_q (r : Rat) (es : List (List (BitVec 8))) :
    ∀ e, e ∈ es → e ≠ [] → envp_factor r 1 es = 0 := by
  induction es with
  | nil => intro e Hin _; cases Hin
  | cons e0 es ih =>
    intro e Hin Hne
    rw [envp_factor_cons]
    rcases List.mem_cons.mp Hin with h | h
    · rw [← h]
      rcases e with _ | ⟨b, e'⟩
      · exact absurd rfl Hne
      · show (1 - r) * geo_point 1 (b :: e').length * envp_factor r 1 es = 0
        unfold geo_point geo_mass
        rw [List.length_cons, Qpow_succ]
        grind
    · rw [ih e h Hne]
      grind

theorem envp_geo_weight_zero_at_one_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs) (c : FinCore)
    (e : List (BitVec 8)) (Hin : e ∈ c.core_envp) (Hne : e ≠ []) :
    envp_geo_weight p r 1 argv fs c = 0 := by
  unfold envp_geo_weight
  split
  · next _ =>
    show envp_point r 1 c.core_envp * geo_point p c.core_stdin.length = 0
    unfold envp_point
    rw [envp_factor_zero_at_one_q r c.core_envp e Hin Hne]
    grind
  · rfl

theorem stdin_envp_geometric_envp_needs_q_below_one (p r : Rat)
    (argv : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore)
    (e : List (BitVec 8)) (Hin : e ∈ c.core_envp) (Hne : e ≠ []) :
    (stdin_envp_geometric p r 1 argv fs Hp0 Hp1 Hr0 Hr1 Qle_0_1 Rat.le_refl).cd_weight c = 0 := by
  show envp_geo_weight p r 1 argv fs c = 0
  exact envp_geo_weight_zero_at_one_q p r argv fs c e Hin Hne

/-- ... AND THE HYPOTHESIS CANNOT BE WEAKENED to "the environment is
    non-empty", which is what makes the shape above a decision rather than
    an accident of how the induction went.  At `q_e = 1` the environment
    with ONE EMPTY ENTRY weighs `2 # 25` — positive — while the
    one-entry-of-one-byte environment weighs zero.  Closed `Q` relations
    between literals this file wrote out, per the header's exception. -/
theorem envp_geo_weight_at_one_q_needs_a_non_empty_entry :
    envp_geo_weight (1 / 2) (1 / 5) 1 [] []
        (FinCore.mkFinCore [] [[BitVec.ofInt 8 65]] [] []) = 0 ∧
      0 < envp_geo_weight (1 / 2) (1 / 5) 1 [] []
        (FinCore.mkFinCore [] [[]] [] []) := by
  refine ⟨?_, ?_⟩
  · exact envp_geo_weight_zero_at_one_q _ _ _ _ _ [BitVec.ofInt 8 65]
      (List.mem_cons_self ..) (fun h => by cases h)
  · rw [envp_geo_weight_match]
    show 0 < envp_point (1 / 5) 1 [[]] * geo_point (1 / 2) 0
    rw [envp_point_single_empty, geo_point_at_zero]
    grind

/- =========================================================================
   The calibrated mixture
   ========================================================================= -/

/-- The mixture's two share constants.  `calibrated_lambda` is the share the
    envp-varying component gets, `calibrated_co_lambda` the stdin-only one,
    and they sum to one — which is what makes the mixture's declared mass
    one whatever the components declare. -/
def calibrated_lambda : Rat := 1 / 16

def calibrated_co_lambda : Rat := 15 / 16

/-- The environment coordinate's two CALIBRATION constants: a mean of four
    environment entries and a mean entry length of thirty-two, the shape of
    a `NAME=value` string.  Nothing is derived from them; every guarantee
    below holds at any pair in `(0, 1)` (`calibrated_mixture_at`), and
    `calibrated_mixture_at_endpoints_bite` shows the interval is not slack
    either. -/
def calibrated_r : Rat := 1 / 5

def calibrated_q : Rat := 1 / 33

theorem calibrated_lambda_nonneg : 0 ≤ calibrated_lambda :=
  Qdiv_nat_nonneg 1 16 (by decide)

theorem calibrated_co_lambda_nonneg : 0 ≤ calibrated_co_lambda :=
  Qdiv_nat_nonneg 15 16 (by decide)

theorem calibrated_r_nonneg : 0 ≤ calibrated_r :=
  Qdiv_nat_nonneg 1 5 (by decide)

theorem calibrated_r_le_1 : calibrated_r ≤ 1 :=
  Qdiv_nat_le_one 1 5 (by decide) (by decide)

theorem calibrated_q_nonneg : 0 ≤ calibrated_q :=
  Qdiv_nat_nonneg 1 33 (by decide)

theorem calibrated_q_le_1 : calibrated_q ≤ 1 :=
  Qdiv_nat_le_one 1 33 (by decide) (by decide)

/-- THE MIXTURE: fifteen sixteenths of the stdin-only family at the task's
    own launch-time environment, one sixteenth of the envp-varying family
    at the calibrated pair.  This is the object a task hands to
    `Measure.DISTRIBUTION`. -/
def calibrated_mixture (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
      (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
      (stdin_envp_geometric p calibrated_r calibrated_q argv fs
        Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
        calibrated_q_nonneg calibrated_q_le_1))

/-- Both components declare `1`, so the mixture declares `15 # 16` of one
    plus `1 # 16` of the other, and that is `1`.  The arithmetic is
    associative-commutative bookkeeping on four numerals — the declared
    masses are written by the two constructors and nothing is decided by
    computation. -/
theorem calibrated_mixture_mass_is_one (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    (calibrated_mixture p argv envp fs Hp0 Hp1).cd_mass = 1 := by
  show calibrated_co_lambda * 1 + calibrated_lambda * 1 = 1
  unfold calibrated_co_lambda calibrated_lambda
  grind

/-- THE UPPER HALF OF THE CERTIFICATE PAIR, for the mixture and not merely
    for its components: a declared mass ships with a finitary pair
    everywhere else in this file, and the mixture is the object a task would
    actually hand to `Measure.DISTRIBUTION`.

    It is a composition and nothing more: each component has its own
    whole-space upper certificate, `cd_scale_bound_mass` carries one through
    a scaling and `cd_mix2_bound_mass` adds two, and
    `calibrated_mixture_mass_is_one` turns the composed declared mass into
    the `1` a consumer wants to read.  The two component bounds are
    discharged ON THE SAME LIST, which is what `cd_mix2_bound`'s comment
    says the mixture bound requires.

    THE LOWER HALF DOES NOT COMPOSE THE SAME WAY, and the asymmetry is worth
    naming because the shape of `cd_scale_mass_lower` and
    `cd_mix2_mass_lower` invites the guess that it does.  Those two ask for
    each component's mass to be ATTAINED on the shared list, and no
    geometric member attains its mass for `p_stop < 1`, so their hypotheses
    are unsatisfiable here rather than merely unproved.  A mixture lower
    certificate has to be an approach carrying its own margin
    (`cd_scale_bound_lower`, `cd_mix2_bound_lower`) and it needs ONE list
    good for both components at once. -/
theorem calibrated_mixture_mass_upper (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (calibrated_mixture p argv envp fs Hp0 Hp1).cd_weight l ≤ 1 := by
  rw [← calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1]
  unfold calibrated_mixture
  refine cd_mix2_bound_mass _ _ l ?_ ?_
  · exact cd_scale_bound_mass calibrated_co_lambda calibrated_co_lambda_nonneg _ l
      (stdin_geometric_mass_upper p argv envp fs Hp0 Hp1 l Hnd)
  · exact cd_scale_bound_mass calibrated_lambda calibrated_lambda_nonneg _ l
      (stdin_envp_geometric_mass_upper p calibrated_r calibrated_q argv fs Hp0 Hp1
        calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1
        l Hnd)

/-- THE SHARED WITNESS, read from the ENVP-VARYING component's side.

    `envp_geo_lower_witness` enumerates (environment, standard input) pairs
    over that component's two prefix families, and the stdin-only component
    can weigh a core of that list only where the core's environment is the
    one it FIXES — every other environment it weighs zero.  So the list
    contains the stdin-only component's own witness family,
    `geo_lower_witness`'s cores at the same standard-input depth `k`, as a
    sublist — PROVIDED the fixed environment is in `envps_upto L M`, which
    is what the two depth hypotheses say and what `envps_upto_complete`
    then delivers.

    An inequality and not an equality, deliberately: the sum over the whole
    list is what the mixture needs, the sum over the sublist is what is
    exactly known (`qsum_short_inputs`), and `qsum_core_incl_le` is the step
    between them.  That step asks for a nonnegative weight and a
    duplicate-free SMALL list, both already proved, and asks nothing at all
    of the containing list.

    The two depth hypotheses are not decoration:
    `stdin_geometric_on_envp_geo_lower_witness_needs_the_depths` shows that
    at depths short of either, the list carries NONE of this component's
    weight. -/
theorem stdin_geometric_on_envp_geo_lower_witness (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (M L k : Nat)
    (HM : envp.length < M) (HL : ∀ e, e ∈ envp → e.length < L) :
    1 - Qpow (1 - p) k ≤
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
        (envp_geo_lower_witness argv fs M L k) := by
  rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness]
  show 1 - Qpow (1 - p) k ≤
    qsum (geo_weight p argv envp fs)
      (envp_stdin_product argv fs (envps_upto L M) (short_inputs k))
  refine Rat.le_trans
    (b := qsum (geo_weight p argv envp fs)
      (List.map (FinCore.mkFinCore argv envp fs) (short_inputs k))) ?_ ?_
  · rw [qsum_short_inputs, geo_prefix_sum_closed]
    exact Rat.le_refl
  · refine qsum_core_incl_le (geo_weight p argv envp fs)
      (List.map (FinCore.mkFinCore argv envp fs) (short_inputs k)) _
      (geo_weight_nonneg p argv envp fs Hp0 Hp1) ?_ ?_
    · rw [← map_fin_core_geo_lower_witness]
      exact geo_lower_witness_nodup argv envp fs k
    · intro c Hc
      obtain ⟨s, Hs, rfl⟩ := List.mem_map.mp Hc
      exact In_envp_stdin_product argv fs _ _ envp s
        (envps_upto_complete L M envp HM HL) Hs

/-- THE MIXTURE'S LOWER CERTIFICATE, at any two nonnegative shares.

    Stated of `cd_mix2` of two `cd_scale`s rather than of
    `calibrated_mixture`, because nothing in the argument turns on the
    calibration constants: the shares `a` and `b` are arbitrary and are NOT
    required to sum to `1`, so the lemma says something true of an
    unnormalized pair as well.  What the argument does turn on is that the
    two components are these two families over the same argv and file
    system, with the stdin-only one fixing an environment the other varies.

    THE MARGIN IS SPLIT BY THE SHARES: each component is certified to
    `eps * (a + b + 1)⁻¹`, and `a + b` of that is at most `eps` whatever
    the shares are.  The `+ 1` is there only to make the reciprocal
    unconditional — at `a = b = 0` there is nothing to divide by otherwise —
    and costs nothing, since a certificate to a smaller margin is a
    certificate.

    THE DEPTHS ARE CHOSEN ONCE, by `envp_stdin_depths_above`, with the
    floors the fixed environment asks for: one past its entry count, one
    past its longest entry.  That single choice is the only place the two
    components interact.

    `envp` is a parameter throughout and the empty environment has no
    privileged role: a task naming a long canonical environment simply gets
    deeper depths, which is exactly what the floors are for. -/
theorem stdin_envp_mix2_mass_lower_certificate (p r q a b : Rat)
    (Ha : 0 ≤ a) (Hb : 0 ≤ b) (argv : List (List (BitVec 8)))
    (envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (eps : Rat)
    (Hppos : 0 < p) (Hrpos : 0 < r) (Hqpos : 0 < q) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (cd_mix2
          (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
          (cd_scale b Hb (stdin_envp_geometric p r q argv fs
            Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))).cd_mass - eps ≤
        core_sum
          (cd_mix2
            (cd_scale a Ha (stdin_geometric p argv envp fs Hp0 Hp1))
            (cd_scale b Hb (stdin_envp_geometric p r q argv fs
              Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))).cd_weight l := by
  have HS : (0 : Rat) < a + b + 1 := by grind
  have Heps' : 0 < eps * (a + b + 1)⁻¹ := Rat.mul_pos Heps (Rat.inv_pos.mpr HS)
  obtain ⟨M, L, k, HM0, HL0, Hsum, Hk⟩ :=
    envp_stdin_depths_above p r q (eps * (a + b + 1)⁻¹) (envp.length + 1)
      (list_max (List.map (fun e => e.length) envp) + 1)
      Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps'
  have HLe : ∀ e, e ∈ envp → e.length < L := by
    intro e He
    have hmax : e.length ∈ List.map (fun e' => e'.length) envp :=
      List.mem_map.mpr ⟨e, He, rfl⟩
    have := list_max_ge _ _ hmax
    omega
  have HM : envp.length < M := by omega
  refine ⟨envp_geo_lower_witness argv fs M L k,
    envp_geo_lower_witness_nodup argv fs M L k, ?_⟩
  have H1 : 1 - eps * (a + b + 1)⁻¹ ≤
      core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
        (envp_geo_lower_witness argv fs M L k) := by
    refine Rat.le_trans (b := 1 - Qpow (1 - p) k) ?_ ?_
    · rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
      exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hk)
    · exact stdin_geometric_on_envp_geo_lower_witness p argv envp fs Hp0 Hp1 M L k HM HLe
  have H2 : 1 - eps * (a + b + 1)⁻¹ ≤
      core_sum (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        (envp_geo_lower_witness argv fs M L k) := by
    rw [(stdin_envp_geometric_mass_lower_witness p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
      M L k).2]
    exact envp_stdin_margin_at_depths p r q (eps * (a + b + 1)⁻¹) M L k
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum
  have hAB : (a + b) * (a + b + 1)⁻¹ ≤ 1 := by
    refine Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_right (show a + b ≤ a + b + 1 by grind)
        (Rat.le_of_lt (Rat.inv_pos.mpr HS))) ?_
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt HS)]
    exact Rat.le_refl
  have Hmar : (a + b) * (eps * (a + b + 1)⁻¹) ≤ eps := by
    have h : (a + b) * (eps * (a + b + 1)⁻¹) = ((a + b) * (a + b + 1)⁻¹) * eps := by
      grind
    rw [h]
    have h2 := Rat.mul_le_mul_of_nonneg_right hAB (Rat.le_of_lt Heps)
    rwa [Rat.one_mul] at h2
  refine Rat.le_trans
    (b := a * (1 - eps * (a + b + 1)⁻¹) + b * (1 - eps * (a + b + 1)⁻¹)) ?_ ?_
  · show a * 1 + b * 1 - eps ≤
      a * (1 - eps * (a + b + 1)⁻¹) + b * (1 - eps * (a + b + 1)⁻¹)
    grind
  · refine cd_mix2_bound_lower _ _ (envp_geo_lower_witness argv fs M L k) _ _ ?_ ?_
    · exact cd_scale_bound_lower a Ha _ _ _ H1
    · exact cd_scale_bound_lower b Hb _ _ _ H2

/-- ... AND AT THE CALIBRATED CONSTANTS, which is the object a task ships.
    It is the instance and nothing more: `calibrated_mixture` IS the
    `cd_mix2` of two `cd_scale`s the lemma above quantifies over, so the
    only work is exhibiting `0 < r` and `0 < q_e` at the two numerals.

    Stated against `1` rather than against `cd_mass` so that it pairs with
    `calibrated_mixture_mass_upper` term for term: no admissible list
    exceeds `1`, and for every margin some admissible list comes within it. -/
theorem calibrated_mixture_mass_lower_certificate (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat)
    (Hppos : 0 < p) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - eps ≤ core_sum (calibrated_mixture p argv envp fs Hp0 Hp1).cd_weight l := by
  have Hrpos : 0 < calibrated_r := Qpos_one_div 5 (by decide)
  have Hqpos : 0 < calibrated_q := Qpos_one_div 33 (by decide)
  obtain ⟨l, Hnd, Hle⟩ :=
    stdin_envp_mix2_mass_lower_certificate p calibrated_r calibrated_q
      calibrated_co_lambda calibrated_lambda calibrated_co_lambda_nonneg
      calibrated_lambda_nonneg argv envp fs Hp0 Hp1 calibrated_r_nonneg
      calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1 eps Hppos Hrpos Hqpos Heps
  refine ⟨l, Hnd, ?_⟩
  refine Rat.le_trans (b := (calibrated_mixture p argv envp fs Hp0 Hp1).cd_mass - eps) ?_ Hle
  rw [calibrated_mixture_mass_is_one p argv envp fs Hp0 Hp1]
  exact Rat.le_refl

/- =========================================================================... and where the mixture's own hypotheses are spent
   ========================================================================= -/

/-- BOTH DEPTH CONSTRAINTS ARE LOAD-BEARING, and the failure is total
    rather than a degradation.  At depths that do not reach the fixed
    environment the shared list carries NONE of the stdin-only component's
    weight — every core of `envp_stdin_product` draws its environment from
    `envps_upto L M`, and the component weighs every environment but its
    own zero (`geo_weight_off_envp_zero`).

    Either depth alone loses it, which is why the hypothesis is a
    disjunction: too few entry slots is `envps_upto_In_length`'s
    contrapositive, too short an entry is `envps_upto_In_entry`'s.  So the
    floors `stdin_envp_mix2_mass_lower_certificate` passes are not caution —
    a certificate that chose `M` and `L` from the margin arithmetic alone
    would have nothing whatever to say about the stdin-only component's
    share of the mixture on the list it exhibits.

    The second conjunct is the `1 # 2` gap the file's other degeneracy pins
    use: the declared mass is still `1`, so a list weighing zero is not
    within any margin under one. -/
theorem stdin_geometric_on_envp_geo_lower_witness_needs_the_depths (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (M L k : Nat)
    (Hdeep : M ≤ envp.length ∨ ∃ e, e ∈ envp ∧ L ≤ e.length) :
    core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight
        (envp_geo_lower_witness argv fs M L k) = 0 ∧
      ¬ ((stdin_geometric p argv envp fs Hp0 Hp1).cd_mass - 1 / 2 ≤ 0) := by
  have Hout : envp ∉ envps_upto L M := by
    intro Hin
    rcases Hdeep with h | ⟨e, He, Hle⟩
    · have := envps_upto_In_length L M envp Hin
      omega
    · have := envps_upto_In_entry L M envp e Hin He
      omega
  refine ⟨?_, ?_⟩
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness]
    show qsum (geo_weight p argv envp fs)
      (envp_stdin_product argv fs (envps_upto L M) (short_inputs k)) = 0
    rw [qsum_ext (fun c => geo_weight p argv envp fs c) (fun _ => 0) _ ?_]
    · exact qsum_zero _
    · intro c Hc
      unfold envp_stdin_product at Hc
      obtain ⟨es, Hes, Hin⟩ := List.mem_flatMap.mp Hc
      obtain ⟨s, Hs, rfl⟩ := List.mem_map.mp Hin
      show geo_weight p argv envp fs (FinCore.mkFinCore argv es fs s) = 0
      apply geo_weight_mismatch
      intro Heq
      apply Hout
      have h : es = envp := congrArg FinCore.core_envp Heq
      rw [← h]
      exact Hes
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

/-- THE CERTIFICATE CANNOT BE MET BY THE ENVP-VARYING COMPONENT ALONE,
    which is the check that isolates what the shared witness actually buys.

    The lemma above says SOME admissible list weighs at least `1 - eps`, and
    such a lemma is worth exactly as much as the reasons a list could have
    for satisfying it.  One reason has to be ruled out here: if the
    envp-varying component could supply the whole `1 - eps` by itself, the
    containment argument would be doing nothing and the certificate would be
    reporting on the wrong distribution.  It cannot.  That component carries
    a share of `1 # 16`, and no admissible list collects more than its
    declared `1` (`stdin_envp_geometric_mass_upper`), so it contributes at
    most `1 # 16` however the list is chosen — and at any margin under
    `15 # 16` the rest has to come from the STDIN-ONLY component, whose
    cores are on that list only because `envps_upto_complete` put them
    there.

    The arithmetic is separated out because it is about the two SHARES and
    not about either family, and because it is where the calibration
    constants earn their keep: `15 # 16` of a nonpositive number plus
    `1 # 16` of something at most `1` cannot reach `1 - eps` for
    `eps < 15 # 16`.  A mixture that put most of its mass on the envp side
    would fail this and would need a different argument. -/
theorem calibrated_shares_force_stdin (S1 S2 eps : Rat) (HS21 : S2 ≤ 1)
    (Heps : eps < 15 / 16) (Hle : 1 - eps ≤ (15 / 16) * S1 + (1 / 16) * S2) :
    0 < S1 := by
  by_cases H : 0 < S1
  · exact H
  · have H0 : S1 ≤ 0 := Rat.not_lt.mp H
    have hco : (0 : Rat) ≤ 15 / 16 := Qdiv_nat_nonneg 15 16 (by decide)
    have hla : (0 : Rat) ≤ 1 / 16 := Qdiv_nat_nonneg 1 16 (by decide)
    have HA : (15 / 16) * S1 ≤ 0 := by
      have h := Rat.mul_le_mul_of_nonneg_left H0 hco
      rwa [Rat.mul_zero] at h
    have HB : (1 / 16) * S2 ≤ 1 / 16 := by
      have h := Rat.mul_le_mul_of_nonneg_left HS21 hla
      rwa [Rat.mul_one] at h
    have HC : 1 - eps ≤ 1 / 16 := by grind
    grind

/-- THE THRESHOLD IS LOAD-BEARING AND THERE IS NO SLACK IN IT: at `eps`
    exactly `15 # 16` the lemma above is FALSE.  Take `S1 = 0` and `S2 = 1` —
    the envp-varying component at its declared mass, the stdin-only one
    contributing nothing — and the hypothesis holds with EQUALITY, `1 - 15 #
    16` and `1 # 16` of `1` being the same number, while the conclusion asks
    for `0 < 0`.

    That the boundary falls exactly there is the arithmetic reporting where
    the envp component's own ceiling is: `1 - 15 # 16` is precisely the mass
    that component declares, so a margin at or past it is a margin the
    shares alone can no longer force the stdin-only side to help with. -/
theorem calibrated_shares_force_stdin_needs_the_threshold :
    ∃ S1 S2 eps : Rat, S2 ≤ 1 ∧ ¬ (eps < 15 / 16) ∧
      1 - eps ≤ (15 / 16) * S1 + (1 / 16) * S2 ∧ ¬ (0 < S1) := by
  refine ⟨0, 1, 15 / 16, Rat.le_refl, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind

/-- The mixture's sum read as the two shares of its components' sums —
    `core_sum_plus` and `core_sum_scale` applied where `cd_mix2` and
    `cd_scale` left them.  Stated rather than inlined because the pin below
    is the only place in the file that needs the mixture taken APART again,
    everything else having been built up. -/
theorem calibrated_mixture_sum_split (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput) :
    core_sum (calibrated_mixture p argv envp fs Hp0 Hp1).cd_weight l =
      calibrated_co_lambda *
          core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l +
        calibrated_lambda *
          core_sum (stdin_envp_geometric p calibrated_r calibrated_q argv fs
            Hp0 Hp1 calibrated_r_nonneg calibrated_r_le_1
            calibrated_q_nonneg calibrated_q_le_1).cd_weight l := by
  show core_sum (fun c =>
      calibrated_co_lambda * (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight c +
      calibrated_lambda *
        (stdin_envp_geometric p calibrated_r calibrated_q argv fs Hp0 Hp1
          calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg
          calibrated_q_le_1).cd_weight c) l = _
  rw [core_sum_plus, core_sum_scale, core_sum_scale]

theorem calibrated_mixture_mass_lower_certificate_needs_the_stdin_component (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) (Heps : eps < 15 / 16)
    (Hle : 1 - eps ≤ core_sum (calibrated_mixture p argv envp fs Hp0 Hp1).cd_weight l) :
    0 < core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l ∧
      ∃ c, c ∈ List.map fin_core l ∧
        0 < (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight c := by
  rw [calibrated_mixture_sum_split] at Hle
  unfold calibrated_co_lambda calibrated_lambda at Hle
  have Hpos : 0 < core_sum (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight l :=
    calibrated_shares_force_stdin _ _ _
      (stdin_envp_geometric_mass_upper p calibrated_r calibrated_q argv fs Hp0 Hp1
        calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1
        l Hnd)
      Heps Hle
  refine ⟨Hpos, ?_⟩
  rw [core_sum_map_fin_core] at Hpos
  exact qsum_positive_member _ _
    (fun c => (stdin_geometric p argv envp fs Hp0 Hp1).cd_nonneg c) Hpos

/-- ... AND THE HYPOTHESIS OF THAT PIN IS MET, which is the half that keeps
    it from being a safe vacuity.  An implication about lists satisfying the
    certificate says nothing until some list does, and
    `calibrated_mixture_mass_lower_certificate` produces one — so the two
    compose into an unconditional existence claim, which is the statement
    worth quoting: at every `p_stop > 0` and every margin in
    `(0, 15 # 16)` there is an admissible list within the margin that NAMES
    a core the stdin-only component weighs positively.  The empty list does
    not satisfy it and neither does any list of cores the mixture weighs
    zero. -/
theorem calibrated_mixture_mass_lower_certificate_names_a_stdin_core (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat)
    (Hppos : 0 < p) (Heps : 0 < eps) (Hsmall : eps < 15 / 16) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - eps ≤ core_sum (calibrated_mixture p argv envp fs Hp0 Hp1).cd_weight l ∧
      ∃ c, c ∈ List.map fin_core l ∧
        0 < (stdin_geometric p argv envp fs Hp0 Hp1).cd_weight c := by
  obtain ⟨l, Hnd, Hle⟩ :=
    calibrated_mixture_mass_lower_certificate p argv envp fs Hp0 Hp1 eps Hppos Heps
  refine ⟨l, Hnd, Hle, ?_⟩
  exact (calibrated_mixture_mass_lower_certificate_needs_the_stdin_component
    p argv envp fs Hp0 Hp1 eps l Hnd Hsmall Hle).2

/-- The shallowest envp witness names exactly ONE core.  `envps_upto 1 1` is
    the single environment `[[]]` and `short_inputs 1` the single standard
    input `[[]]`, so their product is a one-element list — which is what
    makes the pin below a computation a reader can check by eye rather than
    an appeal to a family. -/
theorem envp_stdin_product_at_depth_one :
    envp_stdin_product [] [] (envps_upto 1 1) (short_inputs 1) =
      [FinCore.mkFinCore [] [] [] []] := rfl

/-- The mixture's weight at the empty core, in closed form: the stdin-only
    component weighs it zero (its environment is not the fixed one) and the
    envp-varying component weighs it `(1 # 5) * (1 # 2)`, so the mixture
    weighs it `1 # 160`.  This is the number the threshold pin below turns
    on. -/
theorem calibrated_mixture_weight_empty_core
    (Hp0 : (0 : Rat) ≤ 1 / 2) (Hp1 : (1 : Rat) / 2 ≤ 1) :
    (calibrated_mixture (1 / 2) [] [[BitVec.ofInt 8 65]] [] Hp0 Hp1).cd_weight
      (FinCore.mkFinCore [] [] [] []) = 1 / 160 := by
  show calibrated_co_lambda *
      geo_weight (1 / 2) [] [[BitVec.ofInt 8 65]] [] (FinCore.mkFinCore [] [] [] []) +
      calibrated_lambda *
        envp_geo_weight (1 / 2) calibrated_r calibrated_q [] []
          (FinCore.mkFinCore [] [] [] []) = 1 / 160
  have hzero : geo_weight (1 / 2) [] [[BitVec.ofInt 8 65]] []
      (FinCore.mkFinCore [] [] [] []) = 0 := by
    apply geo_weight_off_envp_zero
    show ([] : List (List (BitVec 8))) ≠ [[BitVec.ofInt 8 65]]
    intro h
    cases h
  rw [hzero]
  rw [show FinCore.mkFinCore [] [] [] [] =
    FinCore.mkFinCore [] ([] : List (List (BitVec 8))) [] [] from rfl,
    envp_geo_weight_match]
  show calibrated_co_lambda * 0 +
    calibrated_lambda * (envp_point calibrated_r calibrated_q [] * geo_point (1 / 2) 0) = 1 / 160
  rw [geo_point_at_zero]
  unfold envp_point envp_factor calibrated_r
  unfold calibrated_lambda calibrated_co_lambda
  grind

/-- ... AND THE THRESHOLD IS LOAD-BEARING AT THE DISTRIBUTION TOO, where it
    needs a STRICTLY larger margin than the arithmetic does.  The difference
    is worth stating rather than glossing: at `eps` exactly `15 # 16` no
    admissible list realizes `calibrated_shares_force_stdin_needs_the_threshold`'s
    counterexample, because its `S2 = 1` is not attained — no list ever
    collects the envp-varying component's declared mass.  Past the boundary
    a list does realize it, and this is one.

    The mixture here fixes the one-entry environment `[[65]]` for its
    stdin-only component, and the list is the shallowest envp witness — the
    single core `mkFinCore [] [] [] []`, whose environment is `[]`.  So the
    stdin-only component weighs that list ZERO, which is exactly the depth
    failure `stdin_geometric_on_envp_geo_lower_witness_needs_the_depths`
    describes, at `M = 1` against an environment of one entry.  What the
    mixture collects is `1 # 16` of `1 # 5` of `1 # 2`, namely `1 # 160`;
    and `1 - (159 # 160)` is `1 # 160` as well, so the certificate's
    conclusion is met WITH EQUALITY by a list carrying none of the
    stdin-only component's weight.

    So the threshold in
    `calibrated_mixture_mass_lower_certificate_needs_the_stdin_component`
    cannot be relaxed to `eps < 1`, and this says so with a witness rather
    than by pointing at the arithmetic. -/
theorem calibrated_mixture_mass_lower_certificate_needs_the_threshold
    (Hp0 : (0 : Rat) ≤ 1 / 2) (Hp1 : (1 : Rat) / 2 ≤ 1) :
    (15 : Rat) / 16 < 159 / 160 ∧ (159 : Rat) / 160 < 1 ∧
      (List.map fin_core (envp_geo_lower_witness [] [] 1 1 1)).Nodup ∧
      (1 - 159 / 160 ≤
        core_sum (calibrated_mixture (1 / 2) [] [[BitVec.ofInt 8 65]] [] Hp0 Hp1).cd_weight
          (envp_geo_lower_witness [] [] 1 1 1)) ∧
      (core_sum (stdin_geometric (1 / 2) [] [[BitVec.ofInt 8 65]] [] Hp0 Hp1).cd_weight
          (envp_geo_lower_witness [] [] 1 1 1) = 0) := by
  have h1 : (15 : Rat) / 16 < 159 / 160 := by grind
  have h2 : (159 : Rat) / 160 < 1 := by grind
  refine ⟨h1, h2, envp_geo_lower_witness_nodup [] [] 1 1 1, ?_, ?_⟩
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness,
      envp_stdin_product_at_depth_one, qsum_cons, qsum_nil]
    show 1 - 159 / 160 ≤
      (calibrated_mixture (1 / 2) [] [[BitVec.ofInt 8 65]] [] Hp0 Hp1).cd_weight
        (fin_core (core_input (FinCore.mkFinCore [] [] [] []))) + 0
    rw [show fin_core (core_input (FinCore.mkFinCore [] [] [] [])) =
      FinCore.mkFinCore [] [] [] [] from rfl, calibrated_mixture_weight_empty_core Hp0 Hp1]
    grind
  · rw [core_sum_map_fin_core, map_fin_core_envp_geo_lower_witness,
      envp_stdin_product_at_depth_one, qsum_cons, qsum_nil]
    show geo_weight (1 / 2) [] [[BitVec.ofInt 8 65]] []
      (fin_core (core_input (FinCore.mkFinCore [] [] [] []))) + 0 = 0
    rw [show fin_core (core_input (FinCore.mkFinCore [] [] [] [])) =
      FinCore.mkFinCore [] [] [] [] from rfl]
    have hzero : geo_weight (1 / 2) [] [[BitVec.ofInt 8 65]] []
        (FinCore.mkFinCore [] [] [] []) = 0 := by
      apply geo_weight_off_envp_zero
      show ([] : List (List (BitVec 8))) ≠ [[BitVec.ofInt 8 65]]
      intro h
      cases h
    rw [hzero]
    grind

/-- `0 < p_stop` IS AS LOAD-BEARING FOR THE MIXTURE AS FOR EITHER COMPONENT,
    pinned the way the two base families pin it.  At `p_stop = 0` both
    components weigh every core zero, so fifteen sixteenths of one plus a
    sixteenth of the other is zero on EVERY admissible list — the first
    conjunct quantifies over all of them for that reason — while the
    declared mass is still `1`.

    `calibrated_mixture_mass_upper` remains true here, and the asymmetry is
    the same honest content the base families' pairs report: an upper bound
    survives degeneracy, a lower one does not. -/
theorem calibrated_mixture_mass_lower_needs_positive
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) :
    (∀ l : List FinProcInput,
      core_sum (calibrated_mixture 0 argv envp fs Rat.le_refl Qle_0_1).cd_weight l = 0) ∧
      ¬ ((calibrated_mixture 0 argv envp fs Rat.le_refl Qle_0_1).cd_mass - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show calibrated_co_lambda * geo_weight 0 argv envp fs c +
      calibrated_lambda * envp_geo_weight 0 calibrated_r calibrated_q argv fs c = 0
    rw [geo_weight_zero_at_zero_p, envp_geo_weight_zero_at_zero_p]
    grind
  · show ¬ (calibrated_co_lambda * 1 + calibrated_lambda * 1 - 1 / 2 ≤ 0)
    unfold calibrated_co_lambda calibrated_lambda
    grind

/-- ... AND THE MIXTURE INHERITS THE BITE, which is the whole reason for
    mixing rather than replacing.  The stdin-only component still weighs a
    non-canonical environment zero; the mixture does not, because a
    sixteenth of a positive number is positive.  So a task keeps whatever
    its stdin-only argument bought and gains a fire set over the environment
    that is no longer null. -/
theorem calibrated_mixture_envp_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hppos : 0 < p) (Hplt : p < 1) :
    (stdin_geometric p [] [] [] Hp0 Hp1).cd_weight envp_example_named = 0 ∧
      0 < (calibrated_mixture p [] [] [] Hp0 Hp1).cd_weight envp_example_named := by
  have hzero : geo_weight p [] [] [] envp_example_named = 0 := by
    apply geo_weight_off_envp_zero
    show [[BitVec.ofInt 8 65]] ≠ []
    intro h
    cases h
  refine ⟨hzero, ?_⟩
  show 0 < calibrated_co_lambda * geo_weight p [] [] [] envp_example_named +
    calibrated_lambda * envp_geo_weight p calibrated_r calibrated_q [] [] envp_example_named
  rw [hzero]
  rw [show envp_example_named = FinCore.mkFinCore [] [[BitVec.ofInt 8 65]] [] [] from rfl,
    envp_geo_weight_match]
  have hla : 0 < calibrated_lambda := Qpos_one_div 16 (by decide)
  have hpos : 0 < envp_point calibrated_r calibrated_q [[BitVec.ofInt 8 65]] *
      geo_point p 0 :=
    Rat.mul_pos
      (envp_point_pos calibrated_r calibrated_q _ (Qpos_one_div 5 (by decide))
        (Qdiv_nat_lt_one 1 5 (by decide) (by decide)) (Qpos_one_div 33 (by decide))
        (Qdiv_nat_lt_one 1 33 (by decide) (by decide)))
      (geo_point_pos p 0 Hppos Hplt)
  have := Rat.mul_pos hla hpos
  grind

/- =========================================================================
   The environment coordinate's two constants, pinned from both sides
   ========================================================================= -/

/-- `calibrated_lambda` IS load-bearing and is pinned as such:
    `calibrated_shares_force_stdin_needs_the_threshold` exhibits shares and
    a margin at which `15 # 16` is exactly false, so the mixture's lower
    certificate does not survive an arbitrary reweighting.

    `calibrated_r` and `calibrated_q` are NOT like that, and saying so in
    place is the point of this section.  Nothing derives `1 # 5` or `1 # 33`
    and nothing needs to: they are a CALIBRATION — a mean of four
    environment entries and a mean entry length of thirty-two, the shape of
    a `NAME=value` string — and every guarantee the mixture offers holds at
    ANY pair in the open interval `(0, 1)`.  `calibrated_mixture_at` is the
    same composition with the pair left open,
    `calibrated_mixture_at_calibrated_r_q` is conversion, and the three
    lemmas after it are the mass, the upper certificate and the lower
    certificate at an arbitrary admissible pair.

    THE INTERVAL IS NOT SLACK EITHER.  At each of its four endpoints a
    guarantee actually fails, on cores the calibrated instance weighs
    positively: `r = 0` and `r = 1` and `q_e = 0` kill every core with a
    non-empty environment, and `q_e = 1` kills every core with a non-empty
    ENTRY.  `calibrated_mixture_at_endpoints_bite` assembles the four, and
    `calibrated_mixture_envp_bites` above is the positive half — at the
    calibrated pair such a core weighs more than zero.  So the open interval
    is exactly the admissible region, not a convenient over-restriction. -/
def calibrated_mixture_at (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  cd_mix2
    (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
      (stdin_geometric p argv envp fs Hp0 Hp1))
    (cd_scale calibrated_lambda calibrated_lambda_nonneg
      (stdin_envp_geometric p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1))

/-- The calibrated mixture IS that composition at the calibrated pair, by
    conversion — so nothing below is a second object that could drift from
    the one the task ships. -/
theorem calibrated_mixture_at_calibrated_r_q (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    calibrated_mixture p argv envp fs Hp0 Hp1 =
      calibrated_mixture_at calibrated_r calibrated_q calibrated_r_nonneg
        calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1 p argv envp fs Hp0 Hp1 :=
  rfl

/-- The two constants lie in the open interval — the hypothesis every lemma
    below asks for, discharged at the calibrated pair once. -/
theorem calibrated_r_q_in_the_open_interval :
    0 < calibrated_r ∧ calibrated_r < 1 ∧ 0 < calibrated_q ∧ calibrated_q < 1 := by
  refine ⟨Qpos_one_div 5 (by decide), ?_, Qpos_one_div 33 (by decide), ?_⟩
  · exact Qdiv_nat_lt_one 1 5 (by decide) (by decide)
  · exact Qdiv_nat_lt_one 1 33 (by decide) (by decide)

/-- THE MASS, at any admissible pair: the shares are what make it `1`, and
    the environment coordinate's parameters do not enter. -/
theorem calibrated_mixture_at_mass_is_one (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1).cd_mass = 1 := by
  show calibrated_co_lambda * 1 + calibrated_lambda * 1 = 1
  unfold calibrated_co_lambda calibrated_lambda
  grind

/-- THE UPPER CERTIFICATE, at any admissible pair. -/
theorem calibrated_mixture_at_mass_upper (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum
      (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1).cd_weight l ≤ 1 := by
  rw [← calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1]
  unfold calibrated_mixture_at
  refine cd_mix2_bound_mass _ _ l ?_ ?_
  · exact cd_scale_bound_mass calibrated_co_lambda calibrated_co_lambda_nonneg _ l
      (stdin_geometric_mass_upper p argv envp fs Hp0 Hp1 l Hnd)
  · exact cd_scale_bound_mass calibrated_lambda calibrated_lambda_nonneg _ l
      (stdin_envp_geometric_mass_upper p r q argv fs Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 l Hnd)

/-- THE LOWER CERTIFICATE, at any admissible pair — and this is the one that
    shows the interval is what matters rather than the numerals, because it
    is the only guarantee whose hypotheses mention `r` and `q_e` at all, and
    what it asks of them is exactly positivity. -/
theorem calibrated_mixture_at_mass_lower_certificate (r q : Rat) (Hr0 : 0 ≤ r)
    (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (eps : Rat) (Hppos : 0 < p) (Hrpos : 0 < r) (Hqpos : 0 < q) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - eps ≤
        core_sum
          (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1).cd_weight l := by
  obtain ⟨l, Hnd, Hle⟩ :=
    stdin_envp_mix2_mass_lower_certificate p r q calibrated_co_lambda calibrated_lambda
      calibrated_co_lambda_nonneg calibrated_lambda_nonneg argv envp fs Hp0 Hp1 Hr0 Hr1
      Hq0 Hq1 eps Hppos Hrpos Hqpos Heps
  refine ⟨l, Hnd, ?_⟩
  refine Rat.le_trans
    (b := (calibrated_mixture_at r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1).cd_mass - eps)
    ?_ Hle
  rw [calibrated_mixture_at_mass_is_one r q Hr0 Hr1 Hq0 Hq1 p argv envp fs Hp0 Hp1]
  exact Rat.le_refl

/-- THE OTHER DIRECTION.  Four endpoints, four collapses, all on the
    stdin-only component's own fixed environment `[]` so that the first
    component contributes nothing either and the number a reader sees is the
    mixture's and not one component's.

    `r = 0` gives every environment weight zero outright; `r = 1` puts the
    whole environment coordinate on the empty environment; `q_e = 0` charges
    any entry at all an infinite price; and `q_e = 1` charges any NON-EMPTY
    entry one, which is why the fourth conjunct asks for a non-empty entry
    rather than a non-empty environment — the environment of one empty entry
    keeps its weight there, and
    `envp_geo_weight_at_one_q_needs_a_non_empty_entry` is the exhibit.

    Read against `calibrated_mixture_envp_bites`, which puts POSITIVE weight
    on such a core at the calibrated pair, this pins the point: the pair is
    free inside `(0, 1)` and not free at its ends. -/
theorem calibrated_mixture_at_endpoints_bite (p q r : Rat)
    (argv : List (List (BitVec 8))) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (c : FinCore)
    (Hne : c.core_envp ≠ []) :
    (calibrated_mixture_at 0 q Rat.le_refl Qle_0_1 Hq0 Hq1 p argv [] [] Hp0 Hp1).cd_weight c = 0 ∧
      (calibrated_mixture_at 1 q Qle_0_1 Rat.le_refl Hq0 Hq1 p argv [] [] Hp0 Hp1).cd_weight c = 0 ∧
      (calibrated_mixture_at r 0 Hr0 Hr1 Rat.le_refl Qle_0_1 p argv [] [] Hp0 Hp1).cd_weight c = 0 ∧
      (∀ e, e ∈ c.core_envp → e ≠ [] →
        (calibrated_mixture_at r 1 Hr0 Hr1 Qle_0_1 Rat.le_refl p argv [] [] Hp0 Hp1).cd_weight c = 0) := by
  have Hgeo : geo_weight p argv [] [] c = 0 := geo_weight_off_envp_zero p argv [] [] c Hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · show calibrated_co_lambda * geo_weight p argv [] [] c +
      calibrated_lambda * envp_geo_weight p 0 q argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_zero_r]
    grind
  · show calibrated_co_lambda * geo_weight p argv [] [] c +
      calibrated_lambda * envp_geo_weight p 1 q argv [] c = 0
    rw [Hgeo, envp_geo_weight_collapses_at_one_r, Hgeo]
    grind
  · show calibrated_co_lambda * geo_weight p argv [] [] c +
      calibrated_lambda * envp_geo_weight p r 0 argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_zero_q p r argv [] c Hne]
    grind
  · intro e Hin Hene
    show calibrated_co_lambda * geo_weight p argv [] [] c +
      calibrated_lambda * envp_geo_weight p r 1 argv [] c = 0
    rw [Hgeo, envp_geo_weight_zero_at_one_q p r argv [] c e Hin Hene]
    grind

/- =========================================================================
   Addressing ONE file's contents inside a core's file system
   ========================================================================= -/

/-- The contents of the file at `pth`, read out of a file system, with the
    absent file reading as the empty one.

    THIS IS THE FAMILY'S COORDINATE, and the representation question it
    settles is the only one the two families below turn on, so it is
    settled here and in one place.  `Fs.Fs` is an association list from
    `Fs.path` to bytes, kept strictly sorted (`Fs.valid_fs`), and a weight
    that wants to vary ONE file's contents therefore needs two things of
    it: a way to read that file out of a core, and a way to put a given
    contents back in.  `Fs.fs_lookup` is the first and `Fs.fs_set` is the
    second, both already in `Fs` and neither added here.

    Collapsing "absent" onto "empty" is what makes this total, and it costs
    nothing the family uses: the cores this family weighs all have the file
    PRESENT, because they are built by `file_core` below, which sets it. -/
def fs_file (pth : Fs.path) (fs : Fs.Fs) : List (BitVec 8) :=
  match Fs.fs_lookup fs pth with
  | some d => d
  | none => []

/-- Setting a path and reading it back gives what was set, at every file
    system and with no sortedness hypothesis.  `Fs.fs_set` either inserts
    before the first larger key, replaces an equal one, or recurses past a
    smaller one; in all three cases the entry it lands on is the one
    `Fs.fs_lookup` finds first.  Sortedness is what makes `Fs.fs_set`
    preserve the CANONICAL form and is `Fs.valid_fs`'s business, not this
    lemma's — the round trip holds either way. -/
theorem fs_lookup_set (fs : Fs.Fs) (pth : Fs.path) (d : List (BitVec 8)) :
    Fs.fs_lookup (Fs.fs_set fs pth d) pth = some d := by
  induction fs with
  | nil =>
    show (if Fs.path_eqb pth pth then some d else Fs.fs_lookup [] pth) = some d
    rw [Fs.path_eqb_refl]
    rfl
  | cons qr r ih =>
    obtain ⟨q, e⟩ := qr
    show Fs.fs_lookup (if Fs.path_ltb pth q then (pth, d) :: (q, e) :: r
        else if Fs.path_eqb pth q then (pth, d) :: r
        else (q, e) :: Fs.fs_set r pth d) pth = some d
    rcases hl : Fs.path_ltb pth q with _ | _
    · rcases he : Fs.path_eqb pth q with _ | _
      · show (if Fs.path_eqb pth q then some e
          else Fs.fs_lookup (Fs.fs_set r pth d) pth) = some d
        rw [he]
        exact ih
      · show (if Fs.path_eqb pth pth then some d else Fs.fs_lookup r pth) = some d
        rw [Fs.path_eqb_refl]
        rfl
    · show (if Fs.path_eqb pth pth then some d
        else Fs.fs_lookup ((q, e) :: r) pth) = some d
      rw [Fs.path_eqb_refl]
      rfl

theorem fs_file_set (fs0 : Fs.Fs) (pth : Fs.path) (d : List (BitVec 8)) :
    fs_file pth (Fs.fs_set fs0 pth d) = d := by
  unfold fs_file
  rw [fs_lookup_set]

/-- THE TEMPLATE: the core over fixed argv, envp, standard input and a
    fixed BASE file system, carrying `d` as the contents of the file at
    `pth`.  It is `mkFinCore` with one field built rather than passed, and
    `d` is its LAST argument on purpose — partially applied, it is the
    embedding `List byte → FinInput.FinCore` that every enumeration below
    maps over, exactly as `mkFinCore argv envp fs` is the embedding
    `stdin_geometric`'s enumerations map over.

    "The file system is otherwise canonical" is `fs0` together with
    `Fs.fs_set`: whatever else the task's file system holds is `fs0`'s and
    is untouched, and the one path the family varies is overwritten.  Note
    what that does NOT require of `fs0` — it need not already contain
    `pth`, and it need not be sorted for anything below to hold (see
    `fs_lookup_set`). -/
def file_core (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s d : List (BitVec 8)) : FinCore :=
  FinCore.mkFinCore argv envp (Fs.fs_set fs0 pth d) s

/-- The coordinate is READABLE OFF the template, which is what makes the
    weight below well defined: the decidable test can ask "is this core the
    template with its own file contents plugged in" only because a core has
    file contents to plug in. -/
theorem fs_file_file_core (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d : List (BitVec 8)) :
    fs_file pth (file_core argv envp fs0 pth s d).core_fs = d :=
  fs_file_set fs0 pth d

/-- ... and so the template is INJECTIVE in the contents.  This is the fact
    the counting and the duplicate-freedom arguments below spend, and it is
    the one place the choice of representation could have gone wrong: an
    embedding that lost information — two contents landing on one core —
    would make the length slice smaller than `256 ^ n` and every witness
    family shorter than it claims. -/
theorem file_core_inj (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d1 d2 : List (BitVec 8))
    (Heq : file_core argv envp fs0 pth s d1 = file_core argv envp fs0 pth s d2) :
    d1 = d2 := by
  rw [← fs_file_file_core argv envp fs0 pth s d1,
    ← fs_file_file_core argv envp fs0 pth s d2, Heq]

/- =========================================================================
   Combinator: geometric file contents over a fixed environment
   ========================================================================= -/

/-- THE WEIGHT.  Zero unless the core is the template with its own file
    contents plugged in; otherwise the geometric weight of that file's
    LENGTH.

    It is `geo_weight` with the varying coordinate moved: there the core is
    `mkFinCore argv envp fs (core_stdin c)` and the weight reads
    `core_stdin c`'s length, here it is `file_core argv envp fs0 pth s
    (fs_file pth (core_fs c))` and the weight reads the length of that.
    Nothing about the memoryless source changes — `geo_point` is the same
    object, so `geo_mass`, `geo_slice_total` and `geo_prefix_sum` are the
    same lemmas and are not proved a second time.

    `argv` AND `pth` ARE INDEPENDENT PARAMETERS AND NOTHING HERE TIES THEM,
    which is the one thing a caller of this family can silently get wrong:
    a task must pass the varied file's path as `argv`'s argument AND as
    `pth`; pass two different ones and the distribution varies a file the
    program never opens, which reintroduces exactly the all-or-nothing
    collapse the family exists to remove — while still declaring mass `1`
    and still satisfying both certificates. -/
def file_geo_weight (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  then geo_point p (fs_file pth c.core_fs).length
  else 0

/-- Its two values, as rewrite rules, so that no proof below names the
    decision instance. -/
theorem file_geo_weight_match (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s d : List (BitVec 8)) :
    file_geo_weight p argv envp fs0 pth s (file_core argv envp fs0 pth s d) =
      geo_point p d.length := by
  unfold file_geo_weight
  rw [fs_file_file_core]
  rw [ite_eq_left rfl]

theorem file_geo_weight_mismatch (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (Hne : c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs)) :
    file_geo_weight p argv envp fs0 pth s c = 0 := by
  unfold file_geo_weight
  rw [ite_eq_right Hne]

theorem file_geo_weight_nonneg (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    0 ≤ file_geo_weight p argv envp fs0 pth s c := by
  unfold file_geo_weight
  split
  · next _ => exact geo_point_nonneg p _ Hp0 Hp1
  · next _ => exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, as everywhere in this file,
    and `file_geometric_mass_upper` below is the proof that owes something
    to it.  Declaring `1` rather than anything else is what keeps a
    MIXTURE of this family with the others at total mass `1` under
    `cd_scale` by shares summing to `1` — the composition
    `calibrated_mixture` spells out, and the reason this family needs no
    mixture combinator of its own: there already is one.

    `0 < p_stop` is NOT a constructor argument, for the reason it is not
    one in `stdin_geometric`: nothing the constructor needs uses it, and
    `file_geometric_mass_lower_certificate` asks for it as a hypothesis of
    its own statement. -/
def file_geometric (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    CoreDistribution where
  cd_weight := file_geo_weight p argv envp fs0 pth s
  cd_mass := 1
  cd_nonneg := file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1

/-- THE ONE BRIDGE THIS FAMILY NEEDS, and the reason it is short: a block
    of cores obtained by mapping the template over a list of byte lists
    weighs exactly what that list of byte lists weighs under `geo_point`.

    Every enumeration below is such a block, and the three byte-list sums
    they are charged against — `bytes_cyl_sum_le` for a cylinder,
    `short_inputs_sum` for a length-bounded prefix family, `byte_lists_sum`
    for one full slice — already exist, stated over BYTE LISTS rather than
    cores precisely so that a second core-level family could use them.  So
    no enumeration, no cancellation and no telescoping identity is written
    again here: this lemma is the whole of the translation. -/
theorem qsum_file_block (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (B : List (List (BitVec 8))) :
    qsum (file_geo_weight p argv envp fs0 pth s)
        (List.map (file_core argv envp fs0 pth s) B) =
      qsum (fun d => geo_point p d.length) B := by
  rw [qsum_map]
  exact qsum_ext _ _ _ (fun d _ => file_geo_weight_match p argv envp fs0 pth s d)

/- =========================================================================
   The prefix cylinder, and the enumeration that bounds it
   ========================================================================= -/

/-- The cores this bound is about: the fixed environment, and file contents
    EXTENDING `bs`.  One existential rather than a conjunction of an
    environment test and a prefix test, for the reason `in_stdin_cylinder`
    is one — it is the form both the construction and the enumeration
    want. -/
def in_file_cylinder (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ ext, c = file_core argv envp fs0 pth s (bs ++ ext)

/-- The depth to enumerate to, read off the task's own list: the longest
    file contents occurring in it.  It is `cores_stdin_depth` on the other
    coordinate, and it exists for the same single reason —
    `Measure.weight_bound_T`'s lists are finite. -/
def cores_file_depth (pth : Fs.path) (cs : List FinCore) : Nat :=
  list_max (List.map (fun c => (fs_file pth c.core_fs).length) cs)

theorem cores_file_depth_ge (pth : Fs.path) (cs : List FinCore) (c : FinCore)
    (Hc : c ∈ cs) : (fs_file pth c.core_fs).length ≤ cores_file_depth pth cs := by
  unfold cores_file_depth
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    The shape is `geo_weight_cylinder_bound`'s exactly — enumerate the
    cylinder to a depth read off the list, observe the list is contained in
    the enumeration, and bound the enumeration.  What is different is that
    the enumeration is `bytes_cyl` mapped through the template rather than
    a recursive definition over cores written a second time, and the
    cancellation that bounds it (`bytes_cyl_sum_le`) is the one
    `cyl_enum_sum_le` already proved.  `qsum_core_incl_le` asks nothing of
    the containing list, so `bytes_cyl` never has to be shown
    duplicate-free. -/
theorem file_geo_weight_cylinder_bound (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8)) (cs : List FinCore)
    (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_file_cylinder argv envp fs0 pth s bs c) :
    qsum (file_geo_weight p argv envp fs0 pth s) cs ≤ geo_mass p bs.length := by
  refine Rat.le_trans (qsum_core_incl_le (file_geo_weight p argv envp fs0 pth s) cs
    (List.map (file_core argv envp fs0 pth s) (bytes_cyl bs (cores_file_depth pth cs)))
    (file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨ext, rfl⟩ := Hcyl c Hc
    refine List.mem_map.mpr ⟨bs ++ ext, ?_, rfl⟩
    apply bytes_cyl_In
    have hd := cores_file_depth_ge pth cs _ Hc
    rw [fs_file_file_core, List.length_append] at hd
    omega
  · rw [qsum_file_block]
    exact bytes_cyl_sum_le p Hp0 Hp1 _ bs

/- =========================================================================
   The exports
   ========================================================================= -/

/-- The cylinder's mass, in closed form.  It is `stdin_geometric`'s number
    at the same prefix length, and that agreement is the point rather than
    a coincidence: the source spreading the file's bytes is the same
    memoryless source, so a task moving an argument from standard input to
    the input file changes which cores it is talking about and not what
    they cost. -/
def file_geometric_cylinder_mass (p : Rat) (bs : List (BitVec 8)) : Rat :=
  geo_mass p bs.length

theorem file_geometric_cylinder_mass_closed_form (p : Rat) (bs : List (BitVec 8)) :
    file_geometric_cylinder_mass p bs =
      Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  geo_mass_closed_form p bs.length

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over a file-contents prefix `bs`, weighs at most that
    cylinder's mass.  The hypothesis is the one `Measure.weight_bound_T`
    carries, and `core_sum_map_fin_core` is the only step between them.

    This is the statement the family exists for.  A fire set described by
    "the input file begins with these bytes" — a magic number, a header
    field, a malformed length — is charged a number that DEPENDS ON THE
    FILE, where `stdin_geometric` would charge either its whole declared
    mass (if the file system happened to be the fixed one) or nothing at
    all (if it did not, because nothing there weighs anything). -/
theorem file_geometric_bound (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_file_cylinder argv envp fs0 pth s bs (fin_core f)) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      file_geometric_cylinder_mass p bs := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  apply file_geo_weight_cylinder_bound p argv envp fs0 pth s Hp0 Hp1 bs
  · exact Hnd
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    exact Hcyl f Hf

/-- The environment test as a boolean, so that `List.filter` can use it.
    `Measure`'s `Qle_bool` exception is not in play, for the reason it is
    not in `matches_env`: this decides an equality of CORES, which
    `FinCore_eq_dec` decides outright, and no rational is involved. -/
def matches_file_env (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore) : Bool :=
  decide (c = file_core argv envp fs0 pth s (fs_file pth c.core_fs))

theorem matches_file_env_false (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_env argv envp fs0 pth s c = false) :
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) :=
  of_decide_eq_false H

theorem matches_file_env_true (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_env argv envp fs0 pth s c = true) :
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) :=
  of_decide_eq_true H

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as
    `stdin_geometric_bound_or_off_environment` slackens its own: each record
    is in the cylinder OR its core misses the fixed environment entirely
    and therefore weighs nothing.  Both forms stay; neither weakens the
    other. -/
theorem file_geometric_bound_or_off_environment (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l → in_file_cylinder argv envp fs0 pth s bs (fin_core f) ∨
      matches_file_env argv envp fs0 pth s (fin_core f) = false) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      file_geometric_cylinder_mass p bs := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_geo_weight p argv envp fs0 pth s)
    (matches_file_env argv envp fs0 pth s) _
    (fun c Hc => by
      rw [file_geo_weight_mismatch p argv envp fs0 pth s c
        (matches_file_env_false _ _ _ _ _ _ Hc)])]
  apply file_geo_weight_cylinder_bound p argv envp fs0 pth s Hp0 Hp1 bs
  · exact List.Nodup.sublist List.filter_sublist Hnd
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    rcases Hor f Hf with h | h
    · exact h
    · rw [h] at Hm
      exact absurd Hm (by decide)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass `1`.  It is the disjunctive bound at the EMPTY prefix, and the
    whole content is that the disjunction is EXHAUSTIVE there — a core
    either matches the fixed environment, in which case its file contents
    are `[] ++ themselves` and it is in the cylinder over `[]`, or it does
    not.  The cylinder mass over the empty prefix is `1` because `Qpow` at
    exponent zero is.

    The LOWER certificate is `file_geometric_mass_lower_certificate` below,
    and it is the half that needs `0 < p_stop`; this one does not. -/
theorem file_geometric_mass_upper (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_mass := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ 1
  refine Rat.le_trans (file_geometric_bound_or_off_environment p argv envp fs0 pth s
    Hp0 Hp1 [] l Hnd ?_) ?_
  · intro f _
    by_cases hm : matches_file_env argv envp fs0 pth s (fin_core f) = true
    · left
      have h := matches_file_env_true argv envp fs0 pth s (fin_core f) hm
      exact ⟨fs_file pth (fin_core f).core_fs, h⟩
    · right
      rcases hb : matches_file_env argv envp fs0 pth s (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm
  · show file_geometric_cylinder_mass p [] ≤ 1
    exact Rat.le_refl

/- =========================================================================
   The counting lemma and the length slice
   ========================================================================= -/

/-- A list of records with duplicate-free CORES, every core matching the
    fixed environment and carrying file contents of length exactly `n`, has
    at most `256 ^ n` elements.

    It is `injective_core_list_in_cylinder_length_bound` on the file
    coordinate and is proved the same way: such a core is determined by its
    file contents (`file_core_inj`, though only the containment direction is
    needed here), `byte_lists n` enumerates the length-`n` byte lists, and
    `nodup_subset_length` turns the injection into a cardinality bound.
    UNLIKE the envp-varying family, this slice really is finite — the
    environment is fixed here — which is why the two attainment lemmas below
    exist for it and do not exist there. -/
theorem injective_core_list_in_file_cylinder_length_bound
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
        (fs_file pth f.fin_image_fs).length = n) :
    l.length ≤ 256 ^ n := by
  have Hle : (List.map fin_core l).length ≤
      (List.map (file_core argv envp fs0 pth s) (byte_lists n)).length := by
    apply nodup_subset_length
    · exact Hnd
    · intro c Hc
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      obtain ⟨Henv, Hlen⟩ := Hall f Hf
      rw [List.mem_map]
      refine ⟨fs_file pth f.fin_image_fs, ?_, ?_⟩
      · rw [← Hlen]; exact byte_lists_complete _
      · rw [← Henv]
  rwa [List.length_map, List.length_map, byte_lists_length] at Hle

/-- THE BOUND IS ATTAINED AT EVERY `n`: over any launch-time environment,
    any base file system and any path, there is an admissible list of
    exactly `256 ^ n` records, one per length-`n` file contents.  This is
    where `file_core_inj` is spent — the enumeration has to be
    duplicate-free ON CORES, and it is only because distinct contents give
    distinct cores.  Nothing is computed: `byte_lists n` stays a
    `List.flatMap` term. -/
theorem injective_core_list_in_file_cylinder_length_bound_attained
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
          (fs_file pth f.fin_image_fs).length = n) ∧
      l.length = 256 ^ n := by
  refine ⟨List.map (fun d => core_input (file_core argv envp fs0 pth s d))
    (byte_lists n), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have hfun : (fin_core ∘ fun d => core_input (file_core argv envp fs0 pth s d)) =
        (fun d => file_core argv envp fs0 pth s d) := by
      funext d
      exact fin_core_core_input _
    rw [hfun]
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact file_core_inj _ _ _ _ _ _ _ Heq
    · exact byte_lists_nodup n
  · intro f Hf
    obtain ⟨d, Hd, rfl⟩ := List.mem_map.mp Hf
    show fin_core (core_input (file_core argv envp fs0 pth s d)) =
        file_core argv envp fs0 pth s
          (fs_file pth (core_input (file_core argv envp fs0 pth s d)).fin_image_fs) ∧
      (fs_file pth (core_input (file_core argv envp fs0 pth s d)).fin_image_fs).length = n
    have hfs : fs_file pth
        (core_input (file_core argv envp fs0 pth s d)).fin_image_fs = d :=
      fs_file_file_core argv envp fs0 pth s d
    rw [hfs, fin_core_core_input]
    exact ⟨rfl, byte_lists_In_length n d Hd⟩
  · rw [List.length_map, byte_lists_length]

/-- THE LENGTH SLICE: a list drawn from one file-length slice weighs at most
    `p_stop * (1 - p_stop) ^ n` — the geometric distribution over LENGTHS,
    with no `1/256` left in it.  The counting lemma supplies the count,
    `qsum_const` observes that every core in a slice weighs the same, and
    `geo_slice_total` is the cancellation, unchanged from the
    standard-input family. -/
theorem file_geometric_slice_bound (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
        (fs_file pth f.fin_image_fs).length = n) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      p * Qpow (1 - p) n := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (file_geo_weight p argv envp fs0 pth s) _ (geo_point p n) ?_]
  · rw [← geo_slice_total p n]
    refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
    apply Qnat_le
    rw [List.length_map]
    exact injective_core_list_in_file_cylinder_length_bound argv envp fs0 pth s n l Hnd Hall
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlen⟩ := Hall f Hf
    rw [Henv, file_geo_weight_match, Hlen]

/-- THE SLICE BOUND'S CONSTANT IS REACHED, at every `n`: the full slice is
    admissible and weighs `p_stop * (1 - p_stop) ^ n` exactly.  Pinning that
    a duplicate-free slice has at most `256 ^ n` elements says the counting
    is right; pinning that the bound those elements imply is reached says
    the EXPORT is right. -/
theorem file_geometric_slice_bound_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
          (fs_file pth f.fin_image_fs).length = n) ∧
      core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        p * Qpow (1 - p) n := by
  obtain ⟨l, Hnd, Hall, Hlen⟩ :=
    injective_core_list_in_file_cylinder_length_bound_attained argv envp fs0 pth s n
  refine ⟨l, Hnd, Hall, ?_⟩
  show core_sum (file_geo_weight p argv envp fs0 pth s) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (file_geo_weight p argv envp fs0 pth s) _ (geo_point p n) ?_]
  · rw [List.length_map, Hlen, geo_slice_total]
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlength⟩ := Hall f Hf
    rw [Henv, file_geo_weight_match, Hlength]

/-- ... and so NO SMALLER CONSTANT IS A SLICE BOUND.  The contrapositive
    shape is deliberate, as at `stdin_geometric_slice_bound_sharp`: it is
    quantified over every candidate `K` a future version of this file might
    try to prove instead, so it stays true as a regression test rather than
    as a fact about today's proof. -/
theorem file_geometric_slice_bound_sharp (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat)
    (Hbound : ∀ l : List FinProcInput, (List.map fin_core l).Nodup →
      (∀ f, f ∈ l →
        fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
          (fs_file pth f.fin_image_fs).length = n) →
      core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤ K) :
    p * Qpow (1 - p) n ≤ K := by
  obtain ⟨l, Hnd, Hall, Hsum⟩ :=
    file_geometric_slice_bound_attained p argv envp fs0 pth s Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hnd Hall

/- =========================================================================
   The lower certificate for `file_geometric`
   ========================================================================= -/

/-- THE WITNESS FAMILY: over a fixed environment, one record per file
    contents SHORTER than `k`.  `short_inputs` is the same length-bounded
    enumeration of byte lists the standard-input certificate uses; only the
    embedding into cores is this family's.

    As everywhere in this file, these records are NOT claimed valid and NOT
    claimed rejected by anything; the certificate is arithmetic about the
    declared mass. -/
def file_geo_lower_witness (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (k : Nat) : List FinProcInput :=
  List.map (fun d => core_input (file_core argv envp fs0 pth s d)) (short_inputs k)

theorem map_fin_core_file_geo_lower_witness (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (k : Nat) :
    List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k) =
      List.map (file_core argv envp fs0 pth s) (short_inputs k) := by
  rw [file_geo_lower_witness, List.map_map]
  apply List.map_congr_left
  intro d _
  exact fin_core_core_input _

theorem file_geo_lower_witness_nodup (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (k : Nat) :
    (List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k)).Nodup := by
  rw [map_fin_core_file_geo_lower_witness]
  apply NoDup_map_inj
  · intro x y _ _ Heq
    exact file_core_inj _ _ _ _ _ _ _ Heq
  · exact short_inputs_nodup k

/-- ... and it weighs the partial sum of the geometric series over lengths.
    Both halves are already proved elsewhere — the block identity above and
    `short_inputs_sum` — so this is two rewrites and no induction. -/
theorem qsum_file_short_inputs (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (k : Nat) :
    qsum (file_geo_weight p argv envp fs0 pth s)
        (List.map (file_core argv envp fs0 pth s) (short_inputs k)) =
      geo_prefix_sum p k := by
  rw [qsum_file_block]
  exact short_inputs_sum p k

/-- THE WITNESS, at each `k`: an admissible list weighing exactly
    `1 - (1 - p_stop) ^ k`.  The target is that rather than the declared
    mass because the mass is not available — for `p_stop < 1` no finite list
    attains it (`file_geometric_mass_not_attained` below).  No hypothesis
    beyond the constructor's own is needed here; the equality is
    unconditional arithmetic. -/
theorem file_geometric_mass_lower_witness (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    (List.map fin_core (file_geo_lower_witness argv envp fs0 pth s k)).Nodup ∧
      core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight
        (file_geo_lower_witness argv envp fs0 pth s k) = 1 - Qpow (1 - p) k := by
  refine ⟨file_geo_lower_witness_nodup argv envp fs0 pth s k, ?_⟩
  show core_sum (file_geo_weight p argv envp fs0 pth s) _ = 1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_file_geo_lower_witness,
    qsum_file_short_inputs, geo_prefix_sum_closed]

/-- The same fact in the shape the certificate vocabulary uses, beside
    `stdin_geometric_mass_lower_prefix`: SOME admissible list weighs the
    target. -/
theorem file_geometric_mass_lower_prefix (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        1 - Qpow (1 - p) k :=
  ⟨file_geo_lower_witness argv envp fs0 pth s k,
    file_geometric_mass_lower_witness p argv envp fs0 pth s Hp0 Hp1 k⟩

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass minus that margin.  With
    `file_geometric_mass_upper` above it, the declared `1` is the least
    upper bound of the admissible partial sums — approached but, by
    `file_geometric_mass_not_attained`, never met.

    `0 < p_stop` IS A HYPOTHESIS OF THIS LEMMA AND NOT A TIGHTENING OF THE
    CONSTRUCTOR, for the reason `stdin_geometric_mass_lower_certificate`
    gives.  It is spent exactly once, inside `geo_gap_small`, choosing the
    `k` whose tail is under `eps`; `file_geometric_mass_lower_needs_positive`
    shows the conclusion is false without it. -/
theorem file_geometric_mass_lower_certificate (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat)
    (Hpos : 0 < p) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_mass - eps ≤
        core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l := by
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hnd, Hsum⟩ :=
    file_geometric_mass_lower_prefix p argv envp fs0 pth s Hp0 Hp1 k
  refine ⟨l, Hnd, ?_⟩
  rw [Hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hk)

/- =========================================================================... and this mass is a SUPREMUM and not a maximum
   ========================================================================= -/

/-- A list confined to file contents of length at most `n` weighs at most
    `1 - (1 - p_stop) ^ (n + 1)` — the partial sum at its own horizon.  It
    MISSES THE TAIL, and the tail is the whole point.  The proof is the
    witness family read in the other direction, exactly as
    `stdin_geometric_bound_by_max_length` reads its own. -/
theorem file_geometric_bound_by_max_length (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ n) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      1 - Qpow (1 - p) (n + 1) := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_geo_weight p argv envp fs0 pth s)
    (matches_file_env argv envp fs0 pth s) _
    (fun c Hc => by
      rw [file_geo_weight_mismatch p argv envp fs0 pth s c
        (matches_file_env_false _ _ _ _ _ _ Hc)])]
  refine Rat.le_trans (qsum_core_incl_le (file_geo_weight p argv envp fs0 pth s) _
    (List.map (file_core argv envp fs0 pth s) (short_inputs (n + 1)))
    (file_geo_weight_nonneg p argv envp fs0 pth s Hp0 Hp1)
    (List.Nodup.sublist List.filter_sublist Hnd) ?_) ?_
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    refine List.mem_map.mpr ⟨fs_file pth f.fin_image_fs, ?_, ?_⟩
    · apply short_inputs_complete
      have := Hlen f Hf
      show (fs_file pth f.fin_image_fs).length < n + 1
      omega
    · exact (matches_file_env_true _ _ _ _ _ _ Hm).symm
  · rw [qsum_file_short_inputs, geo_prefix_sum_closed]
    exact Rat.le_refl

/-- ... AND THAT BOUND IS EXACTLY TIGHT: the witness family at `k = n + 1` is
    a list of file contents of length at most `n`, and it weighs the bound
    exactly.  So the shortfall below is the distribution's and not the
    proof's. -/
theorem file_geometric_bound_by_max_length_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f, f ∈ file_geo_lower_witness argv envp fs0 pth s (n + 1) →
        (fs_file pth f.fin_image_fs).length ≤ n) ∧
      core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight
        (file_geo_lower_witness argv envp fs0 pth s (n + 1)) =
        1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_mass_lower_witness p argv envp fs0 pth s Hp0 Hp1
    (n + 1)).2⟩
  intro f Hf
  rw [file_geo_lower_witness] at Hf
  obtain ⟨d, Hd, rfl⟩ := List.mem_map.mp Hf
  show (fs_file pth (core_input (file_core argv envp fs0 pth s d)).fin_image_fs).length ≤ n
  have hfs : fs_file pth (core_input (file_core argv envp fs0 pth s d)).fin_image_fs = d :=
    fs_file_file_core argv envp fs0 pth s d
  rw [hfs]
  have := short_inputs_In_length (n + 1) d Hd
  omega

/-- For `p_stop < 1` NO admissible list weighs the declared mass — every one
    of them weighs strictly less.  The `n` is the list's own longest file
    contents, which is the only place the FINITENESS of
    `Measure.weight_bound_T`'s lists is needed: a list has a horizon, and
    beyond it sits a positive tail (`Qpow_pos`) it does not collect.

    At `p_stop = 1` it is false, and `file_point_cd_mass_attained` is the
    list that refutes it. -/
theorem file_geometric_mass_not_attained (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l <
      (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_mass := by
  show core_sum (file_geo_weight p argv envp fs0 pth s) l < 1
  generalize hN : list_max (List.map (fun f => (fs_file pth f.fin_image_fs).length) l) = N
  have h1 : core_sum (file_geo_weight p argv envp fs0 pth s) l ≤
      1 - Qpow (1 - p) (N + 1) :=
    file_geometric_bound_by_max_length p argv envp fs0 pth s Hp0 Hp1 N l Hnd
      (fun f Hf => by
        have hin : (fs_file pth f.fin_image_fs).length ∈
            List.map (fun g => (fs_file pth g.fin_image_fs).length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for, beside
    `stdin_geometric_mass_supremum_not_maximum`. -/
theorem file_geometric_mass_supremum_not_maximum (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_mass) :=
  Rat.ne_of_lt (file_geometric_mass_not_attained p argv envp fs0 pth s Hp0 Hp1
    Hlt l Hnd)

/- =========================================================================
   Non-vacuity for the file family
   ========================================================================= -/

/-- `geo_weight`'s file-system instance: a core whose file system is not
    the fixed one weighs zero. -/
theorem geo_weight_off_fs_zero (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs : Fs.Fs) (c : FinCore) (Hne : c.core_fs ≠ fs) :
    geo_weight p argv envp fs c = 0 := by
  apply geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_fs Heq)

theorem file_geo_weight_off_environment_zero (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : c.core_argv ≠ argv) :
    file_geo_weight p argv envp fs0 pth s c = 0 := by
  apply file_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- A path and a core over it: the one-byte path `i`, and the core over the
    empty launch-time environment whose file at that path is empty.  As at
    `geo_example_core`, neither is claimed valid; they are points of
    `Fs.path` and `FinInput.FinCore` chosen so that the two families
    disagree at the second. -/
def file_example_path : Fs.path := [BitVec.ofInt 8 105]

def file_example_core : FinCore :=
  file_core [] [] [] file_example_path [] []

/-- THE BITE THE FAMILY EXISTS FOR, both halves on ONE core.
    `stdin_geometric` over the empty file system weighs `file_example_core`
    exactly zero — its file system is not the fixed one, because it HAS the
    input file in it — while `file_geometric` weighs it strictly
    positively.

    Take a program that is passed a file path as `argv[1]`, reads that
    file, and reads nothing from standard input.  Under a distribution
    built from `stdin_geometric` alone every weighted core carries the SAME
    file system and therefore induces the same program behavior, so the
    per-input predicates hold at all weighted cores or at none, the reject
    set is all-or-nothing on the support, and the least `b` that
    `Measure.weight_bound_T` can be proved at is exactly `0` or `1`.  Under
    this family it is not: the file's bytes carry mass, so intermediate
    values are available and a bound read as a fraction of the input space
    is reading a measure that can take one.

    What it does NOT say, and the misreading is the one the header warns
    about at the geometric lower certificate: that any particular task's
    bound is thereby sharper.  Weight on a core is what makes a bound about
    that core non-vacuous; it is not itself a bound. -/
theorem file_geometric_fs_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : 0 < p) :
    (stdin_geometric p [] [] [] Hp0 Hp1).cd_weight file_example_core = 0 ∧
      0 < (file_geometric p [] [] [] file_example_path [] Hp0 Hp1).cd_weight
        file_example_core := by
  refine ⟨?_, ?_⟩
  · show geo_weight p [] [] [] file_example_core = 0
    apply geo_weight_off_fs_zero
    intro h
    unfold file_example_core file_core at h
    rw [show Fs.fs_set ([] : Fs.Fs) file_example_path [] =
      [(file_example_path, [])] from rfl] at h
    cases h
  · show 0 < file_geo_weight p [] [] [] file_example_path [] file_example_core
    rw [show file_example_core =
      file_core [] [] [] file_example_path [] ([] : List (BitVec 8)) from rfl,
      file_geo_weight_match]
    show 0 < geo_point p 0
    rw [geo_point_at_zero]
    exact Hlt

/-- ... and the family is not a constant either: a core whose argv misses
    the fixed one weighs exactly zero.  Both halves are needed for the
    reason `stdin_geometric_bites` needs both. -/
theorem file_geometric_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : 0 < p) :
    0 < (file_geometric p [] [] [] file_example_path [] Hp0 Hp1).cd_weight
        file_example_core ∧
      (file_geometric p [] [] [] file_example_path [] Hp0 Hp1).cd_weight
        geo_example_other = 0 := by
  refine ⟨(file_geometric_fs_bites p Hp0 Hp1 Hlt).2, ?_⟩
  show file_geo_weight p [] [] [] file_example_path [] geo_example_other = 0
  apply file_geo_weight_off_environment_zero
  show [[BitVec.ofInt 8 65]] ≠ []
  intro h
  cases h

/- =========================================================================
   Non-vacuity: the mass is reached at `p_stop = 1`, and `List.NoDup` is
   load-bearing
   ========================================================================= -/

/-- The member of the family at `p_stop = 1`: stop immediately, always.  It
    is the point mass on the empty file, it is admitted by the constructor
    — `Qle_0_1` and `Rat.le_refl` are its two side conditions — and it is
    what makes the two refutations below closed arithmetic instead of open
    terms. -/
def file_point_cd : CoreDistribution :=
  file_geometric 1 [] [] [] file_example_path [] Qle_0_1 Rat.le_refl

def file_empty_input : FinProcInput := core_input file_example_core

/-- The weight of `file_point_cd` at the empty-file core is `1`: the whole
    of the refutations below is this closed computation. -/
theorem file_point_cd_weight_empty :
    file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) = 1 := by
  show file_geo_weight 1 [] [] [] file_example_path []
    (file_core [] [] [] file_example_path [] ([] : List (BitVec 8))) = 1
  rw [file_geo_weight_match]
  show geo_point 1 0 = 1
  rw [geo_point_at_zero]

/-- The declared mass `1` is not padding at this instance: a one-element
    admissible list reaches it OUTRIGHT.  That is special to `p_stop = 1`,
    where the tail past the empty file is empty, and it is this file's
    witness that `file_geometric_mass_not_attained` cannot drop its
    `p_stop < 1`. -/
theorem file_point_cd_mass_attained :
    (List.map fin_core [file_empty_input]).Nodup ∧
      core_sum file_point_cd.cd_weight [file_empty_input] = file_point_cd.cd_mass := by
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.map_nil, List.nodup_cons]
    exact ⟨List.not_mem_nil, List.nodup_nil⟩
  · show core_sum (file_geo_weight 1 [] [] [] file_example_path []) [file_empty_input] = 1
    rw [core_sum_map_fin_core]
    show file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) + 0 = 1
    rw [file_point_cd_weight_empty]
    grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING for this family's cylinder
    bound, and this is `stdin_geometric_bound_needs_nodup` transposed: offer
    the same core twice — two records, so the list is duplicate-free as a
    list of RECORDS, and both records lie in the cylinder over the empty
    prefix — and the sum is `2` against a cylinder mass of `1`.  All three
    conjuncts are needed, for the reasons the baseline lemma gives. -/
theorem file_geometric_bound_needs_nodup :
    ¬ (List.map fin_core [file_empty_input, file_empty_input]).Nodup ∧
      (∀ f, f ∈ [file_empty_input, file_empty_input] →
        in_file_cylinder [] [] [] file_example_path [] [] (fin_core f)) ∧
      ¬ (core_sum file_point_cd.cd_weight [file_empty_input, file_empty_input] ≤
        file_geometric_cylinder_mass 1 []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.mem_cons_self ..)
  · intro f Hf
    have hfc : f = file_empty_input →
        fin_core f = file_core [] [] [] file_example_path [] [] := by
      intro h
      rw [h]
      rfl
    rcases List.mem_cons.mp Hf with h | h
    · exact ⟨[], hfc h⟩
    · rcases List.mem_cons.mp h with h2 | h2
      · exact ⟨[], hfc h2⟩
      · exact absurd h2 (List.not_mem_nil)
  · intro Hle
    have hsum : core_sum file_point_cd.cd_weight
        [file_empty_input, file_empty_input] = 2 := by
      show file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) +
        (file_geo_weight 1 [] [] [] file_example_path [] (fin_core file_empty_input) + 0) = 2
      rw [file_point_cd_weight_empty]
      grind
    have hm : file_geometric_cylinder_mass 1 ([] : List (BitVec 8)) = 1 := rfl
    rw [hsum, hm] at Hle
    exact absurd Hle (by grind)

/- =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= -/

/-- BOTH ENDPOINTS THE CONSTRUCTOR ADMITS ARE PINNED, and they fail in the
    two different ways this file has names for.  At `p_stop = 0` the weight
    vanishes identically, so every list weighs nothing while the declared
    mass stays `1` and the lower certificate is false — the
    `envp_geo_weight_zero_at_zero_p` shape.  At `p_stop = 1` the weight does
    NOT vanish, and that degeneracy is the interesting one, because every
    core whose input file is NON-EMPTY weighs zero while the empty-file core
    keeps its weight: the family goes blind to the file contents without
    going quiet — the `q_e = 0` shape, and the failure mode that would go
    unnoticed, since at that endpoint the distribution is still non-zero,
    still sums correctly, still declares mass `1` honestly, and still
    measures nothing about the only thing it was added to measure. -/
theorem file_geo_weight_zero_at_zero_p (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore) :
    file_geo_weight 0 argv envp fs0 pth s c = 0 := by
  unfold file_geo_weight
  split
  · next _ => unfold geo_point; grind
  · rfl

theorem file_geometric_mass_lower_needs_positive (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) :
    (∀ l : List FinProcInput,
      core_sum (file_geometric 0 argv envp fs0 pth s Rat.le_refl Qle_0_1).cd_weight l = 0) ∧
      ¬ ((file_geometric 0 argv envp fs0 pth s Rat.le_refl Qle_0_1).cd_mass - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show file_geo_weight 0 argv envp fs0 pth s c = 0
    exact file_geo_weight_zero_at_zero_p argv envp fs0 pth s c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

theorem file_geo_weight_collapses_at_one_p (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (Hne : fs_file pth c.core_fs ≠ []) :
    file_geo_weight 1 argv envp fs0 pth s c = 0 := by
  unfold file_geo_weight
  split
  · next _ =>
    rcases h : fs_file pth c.core_fs with _ | ⟨b, d⟩
    · exact absurd h Hne
    · show geo_point 1 (b :: d).length = 0
      unfold geo_point geo_mass
      rw [List.length_cons, Qpow_succ]
      grind
  · rfl

/-- ... and the blindness in the shape
    `stdin_envp_geometric_envp_needs_positive_q` states it for the other
    non-vanishing degeneracy.  Both are exported: a reader asking "what goes
    wrong at this parameter" wants the blindness, and a reader asking "what
    does the weight become" wants the identity above. -/
theorem file_geometric_needs_p_below_one (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (Hne : fs_file pth c.core_fs ≠ []) :
    (file_geometric 1 argv envp fs0 pth s Qle_0_1 Rat.le_refl).cd_weight c = 0 := by
  show file_geo_weight 1 argv envp fs0 pth s c = 0
  exact file_geo_weight_collapses_at_one_p argv envp fs0 pth s c Hne

/- =========================================================================
   Combinator: geometric file contents BEHIND A FIXED HEADER
   ========================================================================= -/

/- THE FAMILY `file_geometric` IS NOT ENOUGH, and the reason it is needed.
    A driver that reads its input file through a fixed header — a length
    word, a magic number, a field the driver checks before it hands
    anything to the library under test — rejects almost every file
    `file_geometric` weighs, because that family spreads the header's bytes
    uniformly along with the rest.  Only the sliver of files whose random
    header happens to parse reaches the library, so a
    `Measure.weight_bound_T` bound over the whole-file family prices the
    driver's reject path and not the library.  Conditioning on the header is
    not available (there is no conditioning combinator), and the header
    cylinder's own mass is `geo_mass p_stop (length hdr)`, far too small to
    serve as a scale.

    So this family takes the header as a PARAMETER and weighs only the
    bytes after it: a matching core whose file is `hdr ++ t` weighs
    `geo_point p_stop (length t)`, a matching core whose file does not begin
    with `hdr` weighs zero, and the declared mass is `1` — the geometric
    mass of the payload alone, normalised, exactly as if the header had been
    conditioned on.

    ** It is a LENGTH SHIFT through an injective map, and nothing else

    Every fact about `file_geometric` goes through `qsum_file_block` onto
    the byte-list sums (`bytes_cyl_sum_le`, `short_inputs_sum`,
    `byte_lists_sum`) and the length-only arithmetic (`geo_slice_total`,
    `geo_prefix_sum_closed`), none of which mentions a core.  This family is
    that family with its embedding of byte lists into cores composed with
    `t ↦ hdr ++ t` (`file_prefix_core`), which is injective by
    `file_core_inj` and `List.append_cancel_left`.  So the block identity
    (`qsum_file_prefix_block`) carries over through `qsum_map` unchanged,
    every byte-list sum is reused as it stands, and what is proved anew is
    exactly: the weight's rewrite rules, nonnegativity, the shifted block
    identity, and the depth step of the cylinder bound, where the
    enumeration depth is `cores_file_depth` less `length hdr`.

    ** The two facts the spec of record asks for by name

    At the EMPTY header the family is `file_geometric` pointwise
    (`file_prefix_geo_weight_nil`, `file_geometric_prefix_nil_pointwise`):
    the header-conditioned family is a generalisation and not a rival.  And
    the HEADER BITES (`file_geometric_prefix_off_header_zero`,
    `file_geometric_prefix_header_bites`): a core whose file does not start
    with the header weighs zero while the declared mass stays `1`,
    exhibited on the very core the whole-file family weighs positively. -/

/-- Splitting a header off a byte list: `some t` exactly when
    `d = hdr ++ t`.  One decidable byte comparison per header byte, so that
    it computes on closed instances (the pins at the end of this section). -/
def strip_prefix : List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))
  | [], d => some d
  | _ :: _, [] => none
  | h :: hdr, b :: d => if h = b then strip_prefix hdr d else none

theorem strip_prefix_nil_left (d : List (BitVec 8)) : strip_prefix [] d = some d := rfl

theorem strip_prefix_nil_right (h : BitVec 8) (hdr : List (BitVec 8)) :
    strip_prefix (h :: hdr) [] = none := rfl

theorem strip_prefix_cons (h : BitVec 8) (hdr : List (BitVec 8)) (b : BitVec 8)
    (d : List (BitVec 8)) :
    strip_prefix (h :: hdr) (b :: d) = if h = b then strip_prefix hdr d else none := rfl

theorem strip_prefix_app (hdr t : List (BitVec 8)) :
    strip_prefix hdr (hdr ++ t) = some t := by
  induction hdr with
  | nil => rfl
  | cons h hdr ih =>
    show strip_prefix (h :: hdr) (h :: (hdr ++ t)) = some t
    rw [strip_prefix_cons, ite_eq_left rfl]
    exact ih

theorem strip_prefix_Some (hdr : List (BitVec 8)) :
    ∀ (d t : List (BitVec 8)), strip_prefix hdr d = some t → d = hdr ++ t := by
  induction hdr with
  | nil =>
    intro d t H
    rw [strip_prefix_nil_left] at H
    have hdt : d = t := (Option.some.injEq d t).mp H
    rw [hdt]
    rfl
  | cons h hdr ih =>
    intro d t H
    rcases d with _ | ⟨b, d⟩
    · rw [strip_prefix_nil_right] at H
      exact absurd H (by simp)
    · rw [strip_prefix_cons] at H
      split at H
      · next hb =>
        rw [List.cons_append, hb]
        exact congrArg (List.cons b) (ih d t H)
      · exact absurd H (by simp)

theorem strip_prefix_None (hdr d : List (BitVec 8))
    (H : strip_prefix hdr d = none) : ∀ t, d ≠ hdr ++ t := by
  intro t Heq
  rw [Heq, strip_prefix_app] at H
  exact absurd H (by simp)

theorem strip_prefix_None_of_no_extension (hdr d : List (BitVec 8))
    (H : ∀ t, d ≠ hdr ++ t) : strip_prefix hdr d = none := by
  cases hs : strip_prefix hdr d with
  | some t => exact absurd (strip_prefix_Some hdr d t hs) (H t)
  | none => rfl

theorem strip_prefix_nil (d : List (BitVec 8)) : strip_prefix [] d = some d := rfl

/-- THE EMBEDDING: `file_core` composed with `t ↦ hdr ++ t`.  It is the map
    every enumeration below is pushed through, with `t` last so that the
    partial application is that map, and it is injective — the one new fact
    the counting and duplicate-freedom arguments spend. -/
def file_prefix_core (hdr : List (BitVec 8)) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s t : List (BitVec 8)) : FinCore :=
  file_core argv envp fs0 pth s (hdr ++ t)

theorem fs_file_file_prefix_core (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t : List (BitVec 8)) :
    fs_file pth (file_prefix_core hdr argv envp fs0 pth s t).core_fs = hdr ++ t :=
  fs_file_file_core argv envp fs0 pth s (hdr ++ t)

theorem file_prefix_core_inj (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t1 t2 : List (BitVec 8))
    (Heq : file_prefix_core hdr argv envp fs0 pth s t1 =
      file_prefix_core hdr argv envp fs0 pth s t2) :
    t1 = t2 := by
  have h := file_core_inj argv envp fs0 pth s (hdr ++ t1) (hdr ++ t2) Heq
  exact List.append_cancel_left h

/-- THE WEIGHT.  The environment test is `file_geo_weight`'s, unchanged;
    what differs is what is read off a matching core: the file's PAYLOAD
    past the header, or nothing if the header is not there. -/
def file_prefix_geo_weight (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  then match strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => geo_point p t.length
    | none => 0
  else 0

/-- Its three values, as rewrite rules. -/
theorem file_prefix_geo_weight_match (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t : List (BitVec 8)) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t) = geo_point p t.length := by
  unfold file_prefix_geo_weight file_prefix_core
  rw [fs_file_file_core, ite_eq_left rfl, strip_prefix_app]

theorem file_prefix_geo_weight_mismatch (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hne : c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs)) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  unfold file_prefix_geo_weight
  rw [ite_eq_right Hne]

theorem file_prefix_geo_weight_off_header (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hn : strip_prefix hdr (fs_file pth c.core_fs) = none) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  unfold file_prefix_geo_weight
  split
  · next _ => rw [Hn]
  · rfl

/-- ZERO ON A FILE THAT DOES NOT EXTEND THE HEADER, in the form a caller
    states it: no payload `t` makes the file `hdr ++ t`. -/
theorem file_prefix_geo_weight_off_header_zero (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hno : ∀ t, fs_file pth c.core_fs ≠ hdr ++ t) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  apply file_prefix_geo_weight_off_header
  exact strip_prefix_None_of_no_extension hdr _ Hno

theorem file_prefix_geo_weight_nonneg (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    0 ≤ file_prefix_geo_weight hdr p argv envp fs0 pth s c := by
  unfold file_prefix_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => exact geo_point_nonneg p t.length Hp0 Hp1
    | none => exact Rat.le_refl
  · exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, as everywhere in this file: it
    is the geometric mass of the PAYLOAD, and
    `file_geometric_prefix_mass_upper` and
    `file_geometric_prefix_mass_lower_certificate` below are the two halves
    of the certificate that it is honest. -/
def file_geometric_prefix (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution where
  cd_weight := file_prefix_geo_weight hdr p argv envp fs0 pth s
  cd_mass := 1
  cd_nonneg := file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1

/- =========================================================================
   The empty header: `file_geometric`, pointwise
   ========================================================================= -/

/-- At `hdr = []` the payload IS the file, and the weight is
    `file_geo_weight`'s by conversion — `strip_prefix [] d` is `some d`
    definitionally, so the `match` disappears. -/
theorem file_prefix_geo_weight_nil (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore) :
    file_prefix_geo_weight [] p argv envp fs0 pth s c =
      file_geo_weight p argv envp fs0 pth s c := by
  unfold file_prefix_geo_weight file_geo_weight
  split <;> rfl

theorem file_geometric_prefix_nil_pointwise (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1).cd_weight c =
      (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight c :=
  file_prefix_geo_weight_nil p argv envp fs0 pth s c

theorem file_geometric_prefix_nil_mass (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    (file_geometric_prefix [] p argv envp fs0 pth s Hp0 Hp1).cd_mass =
      (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_mass := rfl

/-- `qsum_file_block` through the shifted embedding: a block of cores
    obtained by mapping `file_prefix_core` over a list of PAYLOADS weighs
    what that list of payloads weighs under `geo_point`.  The header
    contributes no factor, which is the whole design. -/
theorem qsum_file_prefix_block (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (B : List (List (BitVec 8))) :
    qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) B) =
      qsum (fun t => geo_point p t.length) B := by
  rw [qsum_map]
  exact qsum_ext _ _ _ (fun t _ => file_prefix_geo_weight_match hdr p argv envp fs0 pth s t)

/- =========================================================================
   The payload cylinder, and the enumeration that bounds it
   ========================================================================= -/

/-- The cores this bound is about: the fixed environment, and a file whose
    PAYLOAD past the header extends `bs`. -/
def in_file_prefix_cylinder (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ ext, c = file_prefix_core hdr argv envp fs0 pth s (bs ++ ext)

/-- The payload cylinder is the whole-file cylinder over `hdr ++ bs`, which
    is the sense in which the family is a length SHIFT and not a new
    object.  `List.append_assoc` is the whole proof. -/
theorem in_file_prefix_cylinder_iff (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s bs : List (BitVec 8)) (c : FinCore) :
    in_file_prefix_cylinder hdr argv envp fs0 pth s bs c ↔
      in_file_cylinder argv envp fs0 pth s (hdr ++ bs) c := by
  unfold in_file_prefix_cylinder in_file_cylinder file_prefix_core
  constructor
  · intro Hex
    obtain ⟨ext, Hext⟩ := Hex
    exact ⟨ext, by rw [Hext, List.append_assoc]⟩
  · intro Hex
    obtain ⟨ext, Hext⟩ := Hex
    exact ⟨ext, by rw [Hext, ← List.append_assoc]⟩

/-- The depth to enumerate PAYLOADS to: the longest file in the list, less
    the header.  `cores_file_depth_ge` shifted by `length hdr`. -/
def cores_file_prefix_depth (hdr : List (BitVec 8)) (pth : Fs.path)
    (cs : List FinCore) : Nat :=
  cores_file_depth pth cs - hdr.length

theorem cores_file_prefix_depth_ge (hdr : List (BitVec 8)) (pth : Fs.path)
    (cs : List FinCore) (c : FinCore) (t : List (BitVec 8))
    (Hc : c ∈ cs) (Ht : fs_file pth c.core_fs = hdr ++ t) :
    t.length ≤ cores_file_prefix_depth hdr pth cs := by
  have hd := cores_file_depth_ge pth cs c Hc
  rw [Ht, List.length_append] at hd
  unfold cores_file_prefix_depth
  omega

/-- THE BOUND OVER CORES, `file_geo_weight_cylinder_bound`'s shape: the
    enumeration is `bytes_cyl` over PAYLOADS mapped through the shifted
    embedding, and `bytes_cyl_sum_le` bounds it unchanged. -/
theorem file_prefix_geo_weight_cylinder_bound (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List (BitVec 8)) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) :
    qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s) cs ≤ geo_mass p bs.length := by
  refine Rat.le_trans (qsum_core_incl_le
    (file_prefix_geo_weight hdr p argv envp fs0 pth s) cs
    (List.map (file_prefix_core hdr argv envp fs0 pth s)
      (bytes_cyl bs (cores_file_prefix_depth hdr pth cs)))
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨ext, rfl⟩ := Hcyl c Hc
    refine List.mem_map.mpr ⟨bs ++ ext, ?_, rfl⟩
    apply bytes_cyl_In
    have hd := cores_file_prefix_depth_ge hdr pth cs _ (bs ++ ext) Hc
      (fs_file_file_prefix_core hdr argv envp fs0 pth s (bs ++ ext))
    rw [List.length_append] at hd
    omega
  · rw [qsum_file_prefix_block]
    exact bytes_cyl_sum_le p Hp0 Hp1 _ bs

/-- The payload cylinder's mass is the whole-file family's number at the
    same PAYLOAD prefix: the header costs nothing, which is what
    conditioning on it means. -/
def file_geometric_prefix_cylinder_mass (p : Rat) (bs : List (BitVec 8)) : Rat :=
  file_geometric_cylinder_mass p bs

theorem file_geometric_prefix_cylinder_mass_closed_form (p : Rat)
    (bs : List (BitVec 8)) :
    file_geometric_prefix_cylinder_mass p bs =
      Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length :=
  file_geometric_cylinder_mass_closed_form p bs

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over a PAYLOAD prefix `bs` behind the header, weighs at
    most that cylinder's mass.  A fire set described by "after the header,
    the input begins with these bytes" is charged a number that does not pay
    for the header. -/
theorem file_geometric_prefix_bound (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      file_geometric_prefix_cylinder_mass p bs := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  exact file_prefix_geo_weight_cylinder_bound hdr p argv envp fs0 pth s Hp0 Hp1 bs
    (List.map fin_core l) Hnd (fun c Hc => by
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      exact Hcyl f Hf)

/- =========================================================================
   The prefix test as a boolean, and the two exports that read it
   ========================================================================= -/

/-- "The core's file begins with `hdr`", as a boolean: `strip_prefix` read
    at `true`.  It exists so that the header test can be CONJOINED with the
    environment test, which is what `List.filter` needs. -/
def matches_file_header (hdr : List (BitVec 8)) (pth : Fs.path) (c : FinCore) : Bool :=
  match strip_prefix hdr (fs_file pth c.core_fs) with
  | some _ => true
  | none => false

/-- Both tests at once: the fixed environment AND the header. -/
def matches_file_prefix_env (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) : Bool :=
  matches_file_env argv envp fs0 pth s c && matches_file_header hdr pth c

/-- A core that fails the combined test fails one of the two, and each
    failure is one of the weight's two zero branches. -/
theorem matches_file_prefix_env_false (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_prefix_env hdr argv envp fs0 pth s c = false) :
    c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs) ∨
      strip_prefix hdr (fs_file pth c.core_fs) = none := by
  unfold matches_file_prefix_env matches_file_header at H
  cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
  | none => exact Or.inr rfl
  | some t =>
    rw [hs] at H
    exact Or.inl (matches_file_env_false argv envp fs0 pth s c (by simpa using H))

/-- So a core that fails the combined test weighs ZERO — the lemma the
    filter step below spends, in the exact shape `qsum_filter` asks for. -/
theorem file_prefix_geo_weight_unmatched (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_prefix_env hdr argv envp fs0 pth s c = false) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  rcases matches_file_prefix_env_false hdr argv envp fs0 pth s c H with Hne | Hn
  · exact file_prefix_geo_weight_mismatch hdr p argv envp fs0 pth s c Hne
  · exact file_prefix_geo_weight_off_header hdr p argv envp fs0 pth s c Hn

/-- ... and conversely, a core that passes it IS the shifted template, at
    the payload `strip_prefix` returns.  This is the half that turns the
    filtered list back into a payload-indexed one. -/
theorem matches_file_prefix_env_true (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_prefix_env hdr argv envp fs0 pth s c = true) :
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t := by
  unfold matches_file_prefix_env at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨Henv, Hh⟩ := H
  obtain ⟨t, Ht⟩ : ∃ t, strip_prefix hdr (fs_file pth c.core_fs) = some t := by
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none =>
      rw [matches_file_header, hs] at Hh
      exact absurd Hh (by decide)
    | some t => exact ⟨t, rfl⟩
  refine ⟨t, ?_⟩
  rw [matches_file_env_true argv envp fs0 pth s c Henv]
  rw [strip_prefix_Some hdr _ t Ht]
  rfl

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE — each record is
    in the payload cylinder OR weighs nothing, off the environment or past
    a header the file does not carry.  Both forms stay, as everywhere in
    this file; neither weakens the other. -/
theorem file_geometric_prefix_bound_or_off_environment (hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l →
      in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f) ∨
        matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) = false) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      file_geometric_prefix_cylinder_mass p bs := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ geo_mass p bs.length
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
    (matches_file_prefix_env hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc)]
  apply file_prefix_geo_weight_cylinder_bound hdr p argv envp fs0 pth s Hp0 Hp1
  · exact List.Nodup.sublist List.filter_sublist Hnd
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    rcases Hor f Hf with h | h
    · exact h
    · rw [h] at Hm
      exact absurd Hm (by decide)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass `1`.  It is the disjunctive bound at the EMPTY payload prefix, and
    the whole content is that the disjunction is EXHAUSTIVE there: a core
    either passes the combined test, in which case its payload is
    `[] ++ itself`, or it weighs nothing.  The header costs the declared
    mass nothing, which is what conditioning on it means. -/
theorem file_geometric_prefix_mass_upper (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ 1
  refine Rat.le_trans (file_geometric_prefix_bound_or_off_environment hdr p argv envp fs0
    pth s Hp0 Hp1 [] l Hnd ?_) ?_
  · intro f _
    by_cases hm : matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) = true
    · left
      obtain ⟨t, Ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s (fin_core f) hm
      exact ⟨t, Ht⟩
    · right
      rcases hb : matches_file_prefix_env hdr argv envp fs0 pth s (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm
  · show file_geometric_prefix_cylinder_mass p [] ≤ 1
    exact Rat.le_refl

/- =========================================================================
   The counting lemma and the payload-length slice
   ========================================================================= -/

/-- A list of records with duplicate-free CORES, every core the shifted
    template at a payload of length exactly `n`, has at most `256 ^ n`
    elements: the payload determines the core (`file_prefix_core_inj`, the
    containment direction) and `byte_lists n` enumerates the payloads.
    `nodup_subset_length` is what turns the injection into a count. -/
theorem injective_core_list_in_file_prefix_cylinder_length_bound
    (hdr : List (BitVec 8)) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) :
    l.length ≤ 256 ^ n := by
  have Hle : (List.map fin_core l).length ≤
      (List.map (file_prefix_core hdr argv envp fs0 pth s) (byte_lists n)).length := by
    apply nodup_subset_length
    · exact Hnd
    · intro c Hc
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      obtain ⟨t, Ht, Hlen⟩ := Hall f Hf
      refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
      rw [← Hlen]
      exact byte_lists_complete t
  rwa [List.length_map, List.length_map, byte_lists_length] at Hle

/-- ... ATTAINED at every `n`, where `file_prefix_core_inj` is spent: the
    enumeration has to be duplicate-free ON CORES, and it is only because
    distinct payloads give distinct cores. -/
theorem injective_core_list_in_file_prefix_cylinder_length_bound_attained
    (hdr : List (BitVec 8)) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) ∧
      l.length = 256 ^ n := by
  refine ⟨List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (byte_lists n), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have hfun : (fin_core ∘ fun t => core_input
        (file_prefix_core hdr argv envp fs0 pth s t)) =
        (fun t => file_prefix_core hdr argv envp fs0 pth s t) := by
      funext t
      exact fin_core_core_input _
    rw [hfun]
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact file_prefix_core_inj _ _ _ _ _ _ _ _ Heq
    · exact byte_lists_nodup n
  · intro f Hf
    obtain ⟨t, Ht, rfl⟩ := List.mem_map.mp Hf
    exact ⟨t, fin_core_core_input _, byte_lists_In_length n t Ht⟩
  · rw [List.length_map, byte_lists_length]

/-- THE PAYLOAD-LENGTH SLICE: a list drawn from one payload-length slice
    weighs at most `p_stop * (1 - p_stop) ^ n` — the same constant the
    whole-file family has at FILE length `n`, and the point of the shift:
    the header is not charged for. -/
theorem file_geometric_prefix_slice_bound (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      p * Qpow (1 - p) n := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (file_prefix_geo_weight hdr p argv envp fs0 pth s) _ (geo_point p n) ?_]
  · rw [← geo_slice_total p n]
    refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
    apply Qnat_le
    rw [List.length_map]
    exact injective_core_list_in_file_prefix_cylinder_length_bound hdr argv envp fs0 pth s n
      l Hnd Hall
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨t, Ht, Hlen⟩ := Hall f Hf
    rw [Ht, file_prefix_geo_weight_match, Hlen]

/-- ... and the constant is REACHED at every `n`: the full slice is
    admissible and weighs it exactly. -/
theorem file_geometric_prefix_slice_bound_attained (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) ∧
      core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        p * Qpow (1 - p) n := by
  obtain ⟨l, Hnd, Hall, Hlen⟩ :=
    injective_core_list_in_file_prefix_cylinder_length_bound_attained hdr argv envp fs0 pth s n
  refine ⟨l, Hnd, Hall, ?_⟩
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l = p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_const (file_prefix_geo_weight hdr p argv envp fs0 pth s) _ (geo_point p n) ?_]
  · rw [List.length_map, Hlen, geo_slice_total]
  · intro c Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
    obtain ⟨t, Ht, Hlength⟩ := Hall f Hf
    rw [Ht, file_prefix_geo_weight_match, Hlength]

/-- ... and so NO SMALLER CONSTANT IS A SLICE BOUND, quantified over every
    candidate `K` a future version of this file might try to prove
    instead, exactly as `file_geometric_slice_bound_sharp`. -/
theorem file_geometric_prefix_slice_bound_sharp (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat)
    (Hbound : ∀ l : List FinProcInput, (List.map fin_core l).Nodup →
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) →
      core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤ K) :
    p * Qpow (1 - p) n ≤ K := by
  obtain ⟨l, Hnd, Hall, Hsum⟩ :=
    file_geometric_prefix_slice_bound_attained hdr p argv envp fs0 pth s Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hnd Hall

/- =========================================================================
   The slice, stated on the FILE's length
   ========================================================================= -/

/-- The counting lemma on CORES rather than records: it is the record-level
    lemma above with `List.map fin_core` already applied, and it exists
    because the wider slice statement below counts a FILTERED list of
    cores, which has no record list behind it. -/
theorem file_prefix_core_list_length_bound (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (n : Nat) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) :
    cs.length ≤ 256 ^ n := by
  have Hle : cs.length ≤
      (List.map (file_prefix_core hdr argv envp fs0 pth s) (byte_lists n)).length := by
    apply nodup_subset_length
    · exact Hnd
    · intro c Hc
      obtain ⟨t, Ht, Hlen⟩ := Hall c Hc
      refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
      rw [← Hlen]
      exact byte_lists_complete t
  rwa [List.length_map, byte_lists_length] at Hle

/-- A record whose core is the shifted template at `t` and whose FILE has
    length `length hdr + n` has a payload of length `n`: the shift, done
    once. -/
theorem file_prefix_payload_length (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (f : FinProcInput) (t : List (BitVec 8)) (n : Nat)
    (Hf : fin_core f = file_prefix_core hdr argv envp fs0 pth s t)
    (Hlen : (fs_file pth f.fin_image_fs).length = hdr.length + n) :
    t.length = n := by
  have h := congrArg (fun c : FinCore => (fs_file pth c.core_fs).length) Hf
  rw [fs_file_file_prefix_core, List.length_append] at h
  have h2 : (fs_file pth f.fin_image_fs).length = hdr.length + t.length := h
  rw [Hlen] at h2
  omega

/-- THE WIDER SLICE STATEMENT, in the whole-file family's shape: every
    record matches the environment and carries a FILE of length
    `length hdr + n`, with NO premise that the file starts with the
    header.  It holds because a core whose file has the right length but
    the wrong header weighs zero, so filtering it out changes nothing. -/
theorem file_geometric_prefix_slice_bound_by_file_length (hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
        (fs_file pth f.fin_image_fs).length = hdr.length + n) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      p * Qpow (1 - p) n := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
    (matches_file_prefix_env hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc)]
  have Hslice : ∀ c, c ∈ List.filter (matches_file_prefix_env hdr argv envp fs0 pth s)
      (List.map fin_core l) →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n := by
    intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c Hm
    exact ⟨t, Ht, file_prefix_payload_length hdr argv envp fs0 pth s f t n
      (by rw [hfc, Ht]) (Hall f Hf).2⟩
  rw [qsum_const (file_prefix_geo_weight hdr p argv envp fs0 pth s) _ (geo_point p n) ?_]
  · rw [← geo_slice_total p n]
    refine Rat.mul_le_mul_of_nonneg_right ?_ (geo_point_nonneg p n Hp0 Hp1)
    apply Qnat_le
    exact file_prefix_core_list_length_bound hdr argv envp fs0 pth s n _
      (List.Nodup.sublist List.filter_sublist Hnd) Hslice
  · intro c Hc
    obtain ⟨t, Ht, Hlen⟩ := Hslice c Hc
    rw [Ht, file_prefix_geo_weight_match, Hlen]

/- =========================================================================
   The lower certificate for `file_geometric_prefix`
   ========================================================================= -/

/-- THE WITNESS FAMILY: one record per PAYLOAD shorter than `k`, behind the
    header.  `short_inputs` is reused; only the embedding is this family's. -/
def file_prefix_geo_lower_witness (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) : List FinProcInput :=
  List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (short_inputs k)

theorem map_fin_core_file_prefix_geo_lower_witness (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) :
    List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k) =
      List.map (file_prefix_core hdr argv envp fs0 pth s) (short_inputs k) := by
  rw [file_prefix_geo_lower_witness, List.map_map]
  apply List.map_congr_left
  intro t _
  exact fin_core_core_input _

theorem file_prefix_geo_lower_witness_nodup (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) :
    (List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)).Nodup := by
  rw [map_fin_core_file_prefix_geo_lower_witness]
  apply NoDup_map_inj
  · intro x y _ _ Heq
    exact file_prefix_core_inj _ _ _ _ _ _ _ _ Heq
  · exact short_inputs_nodup k

/-- ... and it weighs the partial sum of the geometric series over payload
    lengths: the shifted block identity and `short_inputs_sum`, two
    rewrites and no induction. -/
theorem qsum_file_prefix_short_inputs (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) :
    qsum (file_prefix_geo_weight hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) (short_inputs k)) =
      geo_prefix_sum p k := by
  rw [qsum_file_prefix_block]
  exact short_inputs_sum p k

/-- THE WITNESS, at each `k`: an admissible list weighing exactly
    `1 - (1 - p_stop) ^ k`, the partial sum of the PAYLOAD's series.  No
    hypothesis beyond the constructor's own: the equality is unconditional
    arithmetic. -/
theorem file_geometric_prefix_mass_lower_witness (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    (List.map fin_core (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k)).Nodup ∧
      core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s k) =
        1 - Qpow (1 - p) k := by
  refine ⟨file_prefix_geo_lower_witness_nodup hdr argv envp fs0 pth s k, ?_⟩
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) _ = 1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_file_prefix_geo_lower_witness,
    qsum_file_prefix_short_inputs, geo_prefix_sum_closed]

/-- The same fact in the shape the certificate vocabulary uses, beside
    `file_geometric_mass_lower_prefix`: SOME admissible list weighs the
    target. -/
theorem file_geometric_prefix_mass_lower_prefix (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        1 - Qpow (1 - p) k :=
  ⟨file_prefix_geo_lower_witness hdr argv envp fs0 pth s k,
    file_geometric_prefix_mass_lower_witness hdr p argv envp fs0 pth s Hp0 Hp1 k⟩

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass minus that margin.
    `0 < p_stop` is spent once, inside `geo_gap_small`, exactly as for the
    whole-file family. -/
theorem file_geometric_prefix_mass_lower_certificate (hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat)
    (Hpos : 0 < p) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass - eps ≤
        core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l := by
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hnd, Hsum⟩ :=
    file_geometric_prefix_mass_lower_prefix hdr p argv envp fs0 pth s Hp0 Hp1 k
  refine ⟨l, Hnd, ?_⟩
  rw [Hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hk)

/- =========================================================================... and this mass is a SUPREMUM and not a maximum
   ========================================================================= -/

/-- A list confined to files of length at most `length hdr + n` — payloads
    of length at most `n` — weighs at most the partial sum at that horizon.
    The hypothesis is on the FILE's length, which is what a task has; the
    shift by the header is done here.  It MISSES THE TAIL, and the tail is
    the whole point. -/
theorem file_geometric_prefix_bound_by_max_length (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l ≤
      1 - Qpow (1 - p) (n + 1) := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤
    1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_geo_weight hdr p argv envp fs0 pth s)
    (matches_file_prefix_env hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_geo_weight_unmatched hdr p argv envp fs0 pth s c Hc)]
  refine Rat.le_trans (qsum_core_incl_le (file_prefix_geo_weight hdr p argv envp fs0 pth s) _
    (List.map (file_prefix_core hdr argv envp fs0 pth s) (short_inputs (n + 1)))
    (file_prefix_geo_weight_nonneg hdr p argv envp fs0 pth s Hp0 Hp1)
    (List.Nodup.sublist List.filter_sublist Hnd) ?_) ?_
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c Hm
    refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
    apply short_inputs_complete
    have hfs : fs_file pth c.core_fs = hdr ++ t := by
      rw [Ht]
      exact fs_file_file_prefix_core hdr argv envp fs0 pth s t
    have hfs2 : fs_file pth f.fin_image_fs = hdr ++ t := by
      have h := hfs
      rw [← hfc] at h
      exact h
    have hle := Hlen f Hf
    rw [hfs2, List.length_append] at hle
    show t.length < n + 1
    omega
  · rw [qsum_file_prefix_short_inputs, geo_prefix_sum_closed]
    exact Rat.le_refl

/-- ... AND THAT BOUND IS EXACTLY TIGHT: the witness family at `k = n + 1`
    consists of files of length at most `length hdr + n`, and it weighs the
    bound exactly.  So the shortfall below is the distribution's and not
    the proof's. -/
theorem file_geometric_prefix_bound_by_max_length_attained (hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f, f ∈ file_prefix_geo_lower_witness hdr argv envp fs0 pth s (n + 1) →
        (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) ∧
      core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight
        (file_prefix_geo_lower_witness hdr argv envp fs0 pth s (n + 1)) =
        1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_prefix_mass_lower_witness hdr p argv envp fs0 pth s Hp0 Hp1
    (n + 1)).2⟩
  intro f Hf
  rw [file_prefix_geo_lower_witness] at Hf
  obtain ⟨t, Ht, rfl⟩ := List.mem_map.mp Hf
  have hfs : fs_file pth
      (core_input (file_prefix_core hdr argv envp fs0 pth s t)).fin_image_fs = hdr ++ t :=
    fs_file_file_prefix_core hdr argv envp fs0 pth s t
  rw [hfs, List.length_append]
  have := short_inputs_In_length (n + 1) t Ht
  omega

/-- For `p_stop < 1` NO admissible list weighs the declared mass — every one
    weighs strictly less.  The `n` is the list's own longest FILE, which is
    the only place the FINITENESS of `Measure.weight_bound_T`'s lists is
    needed: a list has a horizon, and beyond it sits a positive tail
    (`Qpow_pos`) it does not collect. -/
theorem file_geometric_prefix_mass_not_attained (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l <
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass := by
  show core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l < 1
  generalize hN : list_max (List.map (fun f => (fs_file pth f.fin_image_fs).length) l) = N
  have h1 : core_sum (file_prefix_geo_weight hdr p argv envp fs0 pth s) l ≤
      1 - Qpow (1 - p) (N + 1) :=
    file_geometric_prefix_bound_by_max_length hdr p argv envp fs0 pth s Hp0 Hp1 N l Hnd
      (fun f Hf => by
        have hin : (fs_file pth f.fin_image_fs).length ∈
            List.map (fun g => (fs_file pth g.fin_image_fs).length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for, beside
    `file_geometric_mass_supremum_not_maximum`. -/
theorem file_geometric_prefix_mass_supremum_not_maximum (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight l =
        (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass) :=
  Rat.ne_of_lt (file_geometric_prefix_mass_not_attained hdr p argv envp fs0 pth s Hp0 Hp1
    Hlt l Hnd)

/- =========================================================================
   Non-vacuity: the header bites, and the payload really carries mass
   ========================================================================= -/

theorem file_prefix_geo_weight_off_environment_zero (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : c.core_argv ≠ argv) :
    file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0 := by
  apply file_prefix_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- THE HEADER BITES, in general: a core whose file does not start with the
    header weighs zero, and the declared mass is still `1`.  Both conjuncts
    are wanted: the second is what makes the first a statement about a
    NORMALISED family rather than about a family that was quietly scaled
    down. -/
theorem file_geometric_prefix_off_header_zero (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore)
    (Hno : ∀ t, fs_file pth c.core_fs ≠ hdr ++ t) :
    (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight c = 0 ∧
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass = 1 := by
  refine ⟨?_, rfl⟩
  show file_prefix_geo_weight hdr p argv envp fs0 pth s c = 0
  exact file_prefix_geo_weight_off_header_zero hdr p argv envp fs0 pth s c Hno

/-- A one-byte header, and the core over the empty environment whose file is
    EXACTLY that header.  `file_example_core`'s file is empty, so it does
    NOT start with the header. -/
def file_example_hdr : List (BitVec 8) := [BitVec.ofInt 8 104]

def file_example_hdr_core : FinCore :=
  file_core [] [] [] file_example_path [] file_example_hdr

/-- THE HEADER BITES, exhibited, all on cores the whole-file family treats
    alike.  The empty-file core — the very one `file_geometric_fs_bites`
    shows `file_geometric` weighing POSITIVELY — weighs ZERO here, the
    exact-header core weighs positively, the declared mass is `1`, and the
    whole-file family's positive weight on the first core is restated beside
    it so that the difference is visibly the header and nothing else. -/
theorem file_geometric_prefix_header_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : 0 < p) :
    (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight file_example_core = 0 ∧
      0 < (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight file_example_hdr_core ∧
      (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_mass = 1 ∧
      0 < (file_geometric p [] [] [] file_example_path [] Hp0 Hp1).cd_weight
        file_example_core := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_core = 0
    apply file_prefix_geo_weight_off_header
    unfold file_example_core
    rw [fs_file_file_core]
    rfl
  · show 0 < file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_hdr_core
    rw [show file_example_hdr_core =
      file_prefix_core file_example_hdr [] [] [] file_example_path [] [] from rfl,
      file_prefix_geo_weight_match]
    show 0 < geo_point p 0
    rw [geo_point_at_zero]
    exact Hlt
  · rfl
  · exact (file_geometric_fs_bites p Hp0 Hp1 Hlt).2

/-- ... and the family is not a constant either: positive on the
    exact-header core, zero off the fixed argv. -/
theorem file_geometric_prefix_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hlt : 0 < p) :
    0 < (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight file_example_hdr_core ∧
      (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight geo_example_other = 0 := by
  refine ⟨(file_geometric_prefix_header_bites p Hp0 Hp1 Hlt).2.1, ?_⟩
  show file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
    geo_example_other = 0
  apply file_prefix_geo_weight_off_environment_zero
  show geo_example_other.core_argv ≠ []
  unfold geo_example_other
  intro h
  cases h

/- =========================================================================
   Non-vacuity: the mass is reached at `p_stop = 1`, and `List.NoDup` is
   load-bearing
   ========================================================================= -/

/-- The member at `p_stop = 1`: the point mass on the EXACT-HEADER file.  It
    is admitted by the constructor — `Qle_0_1` and `Rat.le_refl` are its two
    side conditions — and it is what makes the refutation below closed
    arithmetic instead of open terms. -/
def file_prefix_point_cd : CoreDistribution :=
  file_geometric_prefix file_example_hdr 1 [] [] [] file_example_path [] Qle_0_1 Rat.le_refl

def file_hdr_input : FinProcInput := core_input file_example_hdr_core

/-- The weight of `file_prefix_point_cd` at the exact-header core is `1`:
    the whole of the attainment below is this closed computation. -/
theorem file_prefix_point_cd_weight_hdr :
    file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
      (fin_core file_hdr_input) = 1 := by
  rw [show fin_core file_hdr_input = file_example_hdr_core from fin_core_core_input _]
  show file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
    (file_prefix_core file_example_hdr [] [] [] file_example_path [] []) = 1
  rw [file_prefix_geo_weight_match]
  show geo_point 1 0 = 1
  rw [geo_point_at_zero]

/-- The declared mass `1` is not padding at this instance: a one-element
    admissible list reaches it OUTRIGHT.  That is special to `p_stop = 1`,
    where the tail past the empty payload is empty, and it is this file's
    witness that `file_geometric_prefix_mass_not_attained` cannot drop its
    `p_stop < 1`. -/
theorem file_prefix_point_cd_mass_attained :
    (List.map fin_core [file_hdr_input]).Nodup ∧
      core_sum file_prefix_point_cd.cd_weight [file_hdr_input] =
        file_prefix_point_cd.cd_mass := by
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.map_nil, List.nodup_cons]
    exact ⟨List.not_mem_nil, List.nodup_nil⟩
  · show core_sum (file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path [])
      [file_hdr_input] = 1
    rw [core_sum_map_fin_core]
    show file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
      (fin_core file_hdr_input) + 0 = 1
    rw [file_prefix_point_cd_weight_hdr]
    grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING for this family's cylinder
    bound, exactly as `file_geometric_bound_needs_nodup` shows for the
    whole-file one: offer the same core twice — two records, so the list is
    duplicate-free as a list of RECORDS, and both records lie in the payload
    cylinder over the empty prefix — and the sum is `2` against a cylinder
    mass of `1`. -/
theorem file_geometric_prefix_bound_needs_nodup :
    ¬ (List.map fin_core [file_hdr_input, file_hdr_input]).Nodup ∧
      (∀ f, f ∈ [file_hdr_input, file_hdr_input] →
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path [] []
          (fin_core f)) ∧
      ¬ (core_sum file_prefix_point_cd.cd_weight [file_hdr_input, file_hdr_input] ≤
        file_geometric_prefix_cylinder_mass 1 []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.mem_cons_self ..)
  · intro f Hf
    have hfc : f = file_hdr_input →
        fin_core f = file_prefix_core file_example_hdr [] [] [] file_example_path [] [] := by
      intro h
      rw [h]
      exact fin_core_core_input _
    rcases List.mem_cons.mp Hf with h | h
    · exact ⟨[], hfc h⟩
    · rcases List.mem_cons.mp h with h2 | h2
      · exact ⟨[], hfc h2⟩
      · exact absurd h2 (List.not_mem_nil)
  · intro Hle
    have hsum : core_sum file_prefix_point_cd.cd_weight
        [file_hdr_input, file_hdr_input] = 2 := by
      show file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
        (fin_core file_hdr_input) +
        (file_prefix_geo_weight file_example_hdr 1 [] [] [] file_example_path []
          (fin_core file_hdr_input) + 0) = 2
      rw [file_prefix_point_cd_weight_hdr]
      grind
    have hm : file_geometric_prefix_cylinder_mass 1 ([] : List (BitVec 8)) = 1 := rfl
    rw [hsum, hm] at Hle
    exact absurd Hle (by grind)

/- =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= -/

/-- At `p_stop = 0` the weight vanishes identically; at `p_stop = 1` every
    core whose file is not EXACTLY the header weighs zero — a longer payload
    by the geometric collapse, a file missing the header by the header's own
    bite — while the exact-header core keeps its weight.  The family goes
    blind to the payload without going quiet, which is the failure mode that
    would go unnoticed. -/
theorem file_prefix_geo_weight_zero_at_zero_p (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_prefix_geo_weight hdr 0 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => unfold geo_point; grind
    | none => rfl
  · rfl

theorem file_geometric_prefix_mass_lower_needs_positive (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) :
    (∀ l : List FinProcInput,
      core_sum (file_geometric_prefix hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1).cd_weight l = 0) ∧
      ¬ ((file_geometric_prefix hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1).cd_mass - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show file_prefix_geo_weight hdr 0 argv envp fs0 pth s c = 0
    exact file_prefix_geo_weight_zero_at_zero_p hdr argv envp fs0 pth s c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

theorem file_prefix_geo_weight_collapses_at_one_p (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : fs_file pth c.core_fs ≠ hdr) :
    file_prefix_geo_weight hdr 1 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => rfl
    | some t =>
      have hds : fs_file pth c.core_fs = hdr ++ t := strip_prefix_Some hdr _ t hs
      rcases t with _ | ⟨b, t⟩
      · exact absurd (by rw [hds, List.append_nil]) Hne
      · show geo_point 1 (b :: t).length = 0
        unfold geo_point geo_mass
        rw [List.length_cons, Qpow_succ]
        grind
  · rfl

theorem file_geometric_prefix_needs_p_below_one (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : fs_file pth c.core_fs ≠ hdr) :
    (file_geometric_prefix hdr 1 argv envp fs0 pth s
      Qle_0_1 Rat.le_refl).cd_weight c = 0 := by
  show file_prefix_geo_weight hdr 1 argv envp fs0 pth s c = 0
  exact file_prefix_geo_weight_collapses_at_one_p hdr argv envp fs0 pth s c Hne

/- =========================================================================
   Byte lists over a fixed ALPHABET, and the geometric arithmetic over it
   ========================================================================= -/

/- THE ALPHABET-RESTRICTED FAMILY `file_geometric_prefix_over` below spreads
   the payload's bytes i.i.d. UNIFORMLY OVER A FIXED SUBSET `alpha` of the
   bytes rather than over all of them: a text-consuming program wants
   printable input, and under the 256-byte law almost every payload holds a
   control byte.  Everything the 256-byte families count and sum —
   `byte_lists`, `short_inputs`, `bytes_cyl`, `geo_mass` — is `all_bytes` or
   `1 / 256` applied to a shape that never depended on WHICH bytes they
   were.  So that shape is stated here ONCE over an alphabet, with
   hypotheses where the 256-byte enumeration had facts: the alphabet is
   duplicate-free (what `all_bytes_nodup` gave) and non-empty (what
   `all_bytes_length` gave, in the only way the arithmetic spends it: the
   per-byte ratio cancels against the count).  Completeness is NOT a
   hypothesis — an alphabet is not asked to be all the bytes — and turns
   into a PREDICATE on payloads, `alpha_only`, which the weight tests.

   The 256-byte objects are the instance at `alpha = all_bytes`, and that is
   PROVED rather than said (`alpha_lists_all_bytes`,
   `alpha_short_inputs_all_bytes`, `alpha_cyl_all_bytes`,
   `alpha_geo_mass_all_bytes`).  Nothing above this section changes: the
   existing statements are byte-identical, and the existing sums stay proved
   the way they were.  What is generalised is written beside them, and the
   instance lemmas are what tie the two. -/

/-- Membership in the alphabet, as a boolean, and "every byte of `t` is in
    the alphabet". -/
def alpha_memb (alpha : List (BitVec 8)) (b : BitVec 8) : Bool :=
  alpha.any (fun a => decide (a = b))

theorem alpha_memb_In (alpha : List (BitVec 8)) (b : BitVec 8) :
    alpha_memb alpha b = true ↔ b ∈ alpha := by
  unfold alpha_memb
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, Ha, Hab⟩
    rw [decide_eq_true_eq] at Hab
    rwa [← Hab]
  · intro Hb
    exact ⟨b, Hb, by rw [decide_eq_true_eq]⟩

def alpha_only (alpha t : List (BitVec 8)) : Bool :=
  t.all (alpha_memb alpha)

theorem alpha_only_In (alpha t : List (BitVec 8)) :
    alpha_only alpha t = true ↔ ∀ b, b ∈ t → b ∈ alpha := by
  unfold alpha_only
  rw [List.all_eq_true]
  exact ⟨fun H b Hb => (alpha_memb_In alpha b).mp (H b Hb),
    fun H b Hb => (alpha_memb_In alpha b).mpr (H b Hb)⟩

theorem alpha_only_app (alpha t1 t2 : List (BitVec 8)) :
    alpha_only alpha (t1 ++ t2) = (alpha_only alpha t1 && alpha_only alpha t2) := by
  unfold alpha_only
  exact List.all_append

/-- Every payload is over the full alphabet: the predicate is
    `all_bytes_complete` read as a boolean. -/
theorem alpha_only_all_bytes (t : List (BitVec 8)) : alpha_only all_bytes t = true := by
  rw [alpha_only_In]
  intro b _
  exact all_bytes_complete b

theorem all_bytes_ne : all_bytes ≠ [] := by
  intro H
  have h := congrArg List.length H
  rw [all_bytes_length] at h
  exact absurd h (by decide)

/-- The per-byte ratio: one over the alphabet's size.  It is the INVERSE of
    a `Qnat` rather than a `Qmake` with a `positive` denominator, so that
    the size is the list's own `length` and the cancellation below is
    `Rat.mul_inv_cancel` under "non-empty". -/
def alpha_ratio (alpha : List (BitVec 8)) : Rat := (Qnat alpha.length)⁻¹

theorem alpha_ratio_nonneg (alpha : List (BitVec 8)) : 0 ≤ alpha_ratio alpha := by
  unfold alpha_ratio
  rcases Nat.eq_zero_or_pos alpha.length with h | h
  · rw [h, Qnat_0, Rat.inv_zero]
    exact Rat.le_refl
  · refine Rat.le_of_lt (Rat.inv_pos.mpr ?_)
    unfold Qnat
    exact_mod_cast h

theorem Qnat_length_pos (alpha : List (BitVec 8)) (Hne : alpha ≠ []) :
    0 < Qnat alpha.length := by
  rcases alpha with _ | ⟨a, alpha⟩
  · exact absurd rfl Hne
  · rw [show (a :: alpha).length = alpha.length + 1 from rfl, Qnat_succ]
    have h : (0 : Rat) ≤ Qnat alpha.length := Qnat_nonneg _
    grind

theorem alpha_ratio_pos (alpha : List (BitVec 8)) (Hne : alpha ≠ []) :
    0 < alpha_ratio alpha := by
  unfold alpha_ratio
  exact Rat.inv_pos.mpr (Qnat_length_pos alpha Hne)

theorem alpha_ratio_cancel (alpha : List (BitVec 8)) (Hne : alpha ≠ []) :
    Qnat alpha.length * alpha_ratio alpha = 1 := by
  unfold alpha_ratio
  exact Rat.mul_inv_cancel _ (by
    intro h
    have hp := Qnat_length_pos alpha Hne
    rw [h] at hp
    exact absurd hp (by decide))

theorem alpha_ratio_all_bytes : alpha_ratio all_bytes = 1 / 256 := by
  unfold alpha_ratio
  rw [all_bytes_length, Qnat_256, Rat.div_def, Rat.one_mul]

/-- The mass of a payload cylinder and the weight of one payload, over the
    alphabet: powers of ONE ratio, `(1 - p_stop) * alpha_ratio`, exactly as
    `geo_mass` is powers of `(1 - p_stop) * (1 / 256)`. -/
def alpha_geo_mass (alpha : List (BitVec 8)) (p : Rat) (n : Nat) : Rat :=
  Qpow ((1 - p) * alpha_ratio alpha) n

def alpha_geo_point (alpha : List (BitVec 8)) (p : Rat) (n : Nat) : Rat :=
  p * alpha_geo_mass alpha p n

theorem alpha_geo_mass_closed_form (alpha : List (BitVec 8)) (p : Rat) (n : Nat) :
    alpha_geo_mass alpha p n =
      Qpow (1 - p) n * Qpow (alpha_ratio alpha) n :=
  Qpow_mult (1 - p) (alpha_ratio alpha) n

theorem alpha_geo_point_closed_form (alpha : List (BitVec 8)) (p : Rat) (n : Nat) :
    alpha_geo_point alpha p n =
      p * Qpow (1 - p) n * Qpow (alpha_ratio alpha) n := by
  unfold alpha_geo_point
  rw [alpha_geo_mass_closed_form]
  grind

theorem alpha_geo_ratio_nonneg (alpha : List (BitVec 8)) (p : Rat) (Hp1 : p ≤ 1) :
    0 ≤ (1 - p) * alpha_ratio alpha :=
  Rat.mul_nonneg (by grind) (alpha_ratio_nonneg alpha)

theorem alpha_geo_mass_nonneg (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hp1 : p ≤ 1) : 0 ≤ alpha_geo_mass alpha p n :=
  Qpow_nonneg _ n (alpha_geo_ratio_nonneg alpha p Hp1)

theorem alpha_geo_point_nonneg (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : 0 ≤ alpha_geo_point alpha p n :=
  Rat.mul_nonneg Hp0 (alpha_geo_mass_nonneg alpha p n Hp1)

theorem alpha_geo_point_le_mass (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hp1 : p ≤ 1) : alpha_geo_point alpha p n ≤ alpha_geo_mass alpha p n := by
  unfold alpha_geo_point
  have h := Rat.mul_le_mul_of_nonneg_right Hp1 (alpha_geo_mass_nonneg alpha p n Hp1)
  rwa [Rat.one_mul] at h

theorem alpha_geo_point_pos (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hp0 : 0 < p) (Hp1 : p < 1) (Hne : alpha ≠ []) :
    0 < alpha_geo_point alpha p n := by
  unfold alpha_geo_point alpha_geo_mass
  exact Rat.mul_pos Hp0 (Qpow_pos _ _ (Rat.mul_pos (by grind) (alpha_ratio_pos alpha Hne)))

/-- The instance at `all_bytes` is the 256-byte arithmetic. -/
theorem alpha_geo_mass_all_bytes (p : Rat) (n : Nat) :
    alpha_geo_mass all_bytes p n = geo_mass p n := by
  unfold alpha_geo_mass geo_mass
  exact Qpow_Qeq _ _ n (by rw [alpha_ratio_all_bytes])

theorem alpha_geo_point_all_bytes (p : Rat) (n : Nat) :
    alpha_geo_point all_bytes p n = geo_point p n := by
  unfold alpha_geo_point geo_point
  rw [alpha_geo_mass_all_bytes]

/- =========================================================================
   The enumerations over the alphabet
   ========================================================================= -/

/-- THE ENUMERATION of length-`n` lists over the alphabet: `byte_lists`
    with `alpha` in place of `all_bytes`. -/
def alpha_lists (alpha : List (BitVec 8)) : Nat → List (List (BitVec 8))
  | 0 => [[]]
  | n + 1 => alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))

theorem alpha_lists_all_bytes : ∀ n, alpha_lists all_bytes n = byte_lists n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show all_bytes.flatMap (fun b => (alpha_lists all_bytes n).map (fun l => b :: l)) =
      all_bytes.flatMap (fun b => (byte_lists n).map (fun l => b :: l))
    rw [ih]

theorem alpha_lists_length (alpha : List (BitVec 8)) (n : Nat) :
    (alpha_lists alpha n).length = alpha.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))).length
      = alpha.length ^ (n + 1)
    rw [length_flat_map_const (f := fun b => (alpha_lists alpha n).map (fun l => b :: l))
      (c := alpha.length ^ n) (Hc := fun b _ => by rw [List.length_map]; exact ih)]
    rw [Nat.pow_succ, Nat.mul_comm]

theorem alpha_lists_complete (alpha : List (BitVec 8)) :
    ∀ l : List (BitVec 8), alpha_only alpha l = true → l ∈ alpha_lists alpha l.length := by
  intro l
  induction l with
  | nil => intro _; exact List.mem_cons_self ..
  | cons b l ih =>
    intro Hl
    rw [alpha_only, List.all_cons, Bool.and_eq_true] at Hl
    obtain ⟨Hb, Hl⟩ := Hl
    show b :: l ∈ alpha.flatMap (fun b => (alpha_lists alpha l.length).map (fun l' => b :: l'))
    rw [List.mem_flatMap]
    exact ⟨b, (alpha_memb_In alpha b).mp Hb, List.mem_map.mpr ⟨l, ih Hl, rfl⟩⟩

theorem alpha_lists_In_length (alpha : List (BitVec 8)) :
    ∀ (n : Nat) (s : List (BitVec 8)), s ∈ alpha_lists alpha n → s.length = n := by
  intro n
  induction n with
  | zero =>
    intro s Hs
    rw [show alpha_lists alpha 0 = [[]] from rfl, List.mem_cons] at Hs
    rcases Hs with h | h
    · rw [h]; rfl
    · exact absurd h (List.not_mem_nil)
  | succ n ih =>
    intro s Hs
    rw [show alpha_lists alpha (n + 1) =
      alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l)) from rfl] at Hs
    obtain ⟨b, _, Hs⟩ := List.mem_flatMap.mp Hs
    obtain ⟨s', Hs', rfl⟩ := List.mem_map.mp Hs
    rw [List.length_cons, ih s' Hs']

theorem alpha_lists_In_alpha (alpha : List (BitVec 8)) :
    ∀ (n : Nat) (s : List (BitVec 8)), s ∈ alpha_lists alpha n → alpha_only alpha s = true := by
  intro n
  induction n with
  | zero =>
    intro s Hs
    rw [show alpha_lists alpha 0 = [[]] from rfl, List.mem_cons] at Hs
    rcases Hs with h | h
    · rw [h]; rfl
    · exact absurd h (List.not_mem_nil)
  | succ n ih =>
    intro s Hs
    rw [show alpha_lists alpha (n + 1) =
      alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l)) from rfl] at Hs
    obtain ⟨b, Hb, Hs⟩ := List.mem_flatMap.mp Hs
    obtain ⟨s', Hs', rfl⟩ := List.mem_map.mp Hs
    rw [alpha_only, List.all_cons, Bool.and_eq_true]
    exact ⟨(alpha_memb_In alpha b).mpr Hb, ih s' Hs'⟩

theorem alpha_lists_nodup (alpha : List (BitVec 8)) (Hnd : alpha.Nodup) :
    ∀ n, (alpha_lists alpha n).Nodup := by
  intro n
  induction n with
  | zero => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ n ih =>
    show (alpha.flatMap (fun b => (alpha_lists alpha n).map (fun l => b :: l))).Nodup
    refine NoDup_flat_map _ _ Hnd (fun b _ => ?_) (fun x y bs _ _ Hx Hy => ?_)
    · apply NoDup_map_inj (f := fun l => b :: l)
      · intro x y _ _ heq
        exact (List.cons.inj heq).2
      · exact ih
    · obtain ⟨lx, Hlx, rfl⟩ := List.mem_map.mp Hx
      obtain ⟨ly, Hly, Hxy⟩ := List.mem_map.mp Hy
      exact (List.cons.inj Hxy).1.symm

/-- A full length-`n` slice over the alphabet weighs `p (1 - p) ^ n`: the
    size `length alpha ^ n` and the ratio's `n`th power cancel, which is
    where "non-empty" is spent. -/
theorem Qnat_pow (m n : Nat) : Qnat (m ^ n) = Qpow (Qnat m) n := by
  induction n with
  | zero => rw [Nat.pow_zero, Qpow_0]; rfl
  | succ n ih => rw [Nat.pow_succ, Qnat_mult, ih, Qpow_succ]; grind

theorem alpha_slice_total (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hne : alpha ≠ []) :
    Qnat (alpha.length ^ n) * alpha_geo_point alpha p n = p * Qpow (1 - p) n := by
  have H1 : Qpow (Qnat alpha.length) n * Qpow (alpha_ratio alpha) n = 1 := by
    rw [← Qpow_mult]
    rw [Qpow_Qeq (Qnat alpha.length * alpha_ratio alpha) 1 n
      (alpha_ratio_cancel alpha Hne)]
    exact Qpow_1 n
  rw [Qnat_pow]
  unfold alpha_geo_point alpha_geo_mass
  rw [Qpow_mult]
  calc Qpow (Qnat alpha.length) n * (p * (Qpow (1 - p) n * Qpow (alpha_ratio alpha) n))
      = (Qpow (Qnat alpha.length) n * Qpow (alpha_ratio alpha) n) *
          (p * Qpow (1 - p) n) := by grind
    _ = 1 * (p * Qpow (1 - p) n) := by rw [H1]
    _ = p * Qpow (1 - p) n := by grind

theorem alpha_lists_sum (alpha : List (BitVec 8)) (p : Rat) (n : Nat)
    (Hne : alpha ≠ []) :
    qsum (fun s => alpha_geo_point alpha p s.length) (alpha_lists alpha n) =
      p * Qpow (1 - p) n :=
  calc qsum (fun s => alpha_geo_point alpha p s.length) (alpha_lists alpha n)
      = Qnat (alpha_lists alpha n).length * alpha_geo_point alpha p n :=
        qsum_const _ _ _ (fun s Hs => by rw [alpha_lists_In_length alpha n s Hs])
    _ = Qnat (alpha.length ^ n) * alpha_geo_point alpha p n := by rw [alpha_lists_length]
    _ = p * Qpow (1 - p) n := alpha_slice_total alpha p n Hne

/-- The length-bounded prefix family over the alphabet: `short_inputs` with
    `alpha_lists` in place of `byte_lists`. -/
def alpha_short_inputs (alpha : List (BitVec 8)) : Nat → List (List (BitVec 8))
  | 0 => []
  | k + 1 => alpha_lists alpha k ++ alpha_short_inputs alpha k

theorem alpha_short_inputs_all_bytes : ∀ k,
    alpha_short_inputs all_bytes k = short_inputs k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show alpha_lists all_bytes k ++ alpha_short_inputs all_bytes k =
      byte_lists k ++ short_inputs k
    rw [alpha_lists_all_bytes, ih]

theorem alpha_short_inputs_In_length (alpha : List (BitVec 8)) :
    ∀ (k : Nat) (s : List (BitVec 8)), s ∈ alpha_short_inputs alpha k → s.length < k := by
  intro k
  induction k with
  | zero => intro s Hs; exact absurd Hs (List.not_mem_nil)
  | succ k ih =>
    intro s Hs
    rw [show alpha_short_inputs alpha (k + 1) =
      alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl, List.mem_append] at Hs
    rcases Hs with Hs | Hs
    · have h := alpha_lists_In_length alpha k s Hs
      omega
    · have h := ih s Hs
      omega

theorem alpha_short_inputs_In_alpha (alpha : List (BitVec 8)) :
    ∀ (k : Nat) (s : List (BitVec 8)),
      s ∈ alpha_short_inputs alpha k → alpha_only alpha s = true := by
  intro k
  induction k with
  | zero => intro s Hs; exact absurd Hs (List.not_mem_nil)
  | succ k ih =>
    intro s Hs
    rw [show alpha_short_inputs alpha (k + 1) =
      alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl, List.mem_append] at Hs
    rcases Hs with Hs | Hs
    · exact alpha_lists_In_alpha alpha k s Hs
    · exact ih s Hs

theorem alpha_short_inputs_complete (alpha : List (BitVec 8)) :
    ∀ (k : Nat) (s : List (BitVec 8)),
      alpha_only alpha s = true → s.length < k → s ∈ alpha_short_inputs alpha k := by
  intro k
  induction k with
  | zero => intro s _ Hlen; omega
  | succ k ih =>
    intro s Ha Hlen
    rw [show alpha_short_inputs alpha (k + 1) =
      alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl, List.mem_append]
    by_cases heq : s.length = k
    · left
      rw [← heq]
      exact alpha_lists_complete alpha s Ha
    · right
      exact ih s Ha (by omega)

theorem alpha_short_inputs_nodup (alpha : List (BitVec 8)) (Hnd : alpha.Nodup) :
    ∀ k, (alpha_short_inputs alpha k).Nodup := by
  intro k
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    rw [show alpha_short_inputs alpha (k + 1) =
      alpha_lists alpha k ++ alpha_short_inputs alpha k from rfl, List.nodup_append]
    refine ⟨alpha_lists_nodup alpha Hnd k, ih, ?_⟩
    intro a Ha b Hb hab
    have h1 := alpha_lists_In_length alpha k a Ha
    have h2 := alpha_short_inputs_In_length alpha k b Hb
    rw [← hab, h1] at h2
    exact absurd h2 (Nat.lt_irrefl k)

theorem alpha_short_inputs_sum (alpha : List (BitVec 8)) (p : Rat) (k : Nat)
    (Hne : alpha ≠ []) :
    qsum (fun s => alpha_geo_point alpha p s.length) (alpha_short_inputs alpha k) =
      geo_prefix_sum p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show qsum (fun s => alpha_geo_point alpha p s.length)
        (alpha_lists alpha k ++ alpha_short_inputs alpha k) = geo_prefix_sum p (k + 1)
    rw [qsum_app, ih, alpha_lists_sum alpha p k Hne]
    rfl

/-- The cylinder enumeration over the alphabet: `bytes_cyl` with `alpha` in
    place of `all_bytes`. -/
def alpha_cyl (alpha bs : List (BitVec 8)) : Nat → List (List (BitVec 8))
  | 0 => [bs]
  | N + 1 => bs :: alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N)

theorem alpha_cyl_all_bytes : ∀ (N : Nat) (bs : List (BitVec 8)),
    alpha_cyl all_bytes bs N = bytes_cyl bs N := by
  intro N
  induction N with
  | zero => intro bs; rfl
  | succ N ih =>
    intro bs
    show bs :: all_bytes.flatMap (fun b => alpha_cyl all_bytes (bs ++ [b]) N) =
      bs :: all_bytes.flatMap (fun b => bytes_cyl (bs ++ [b]) N)
    rw [flatMap_congr_mem _ _ _ (fun b _ => ih (bs ++ [b]))]

theorem alpha_cyl_In (alpha : List (BitVec 8)) :
    ∀ (N : Nat) (bs ext : List (BitVec 8)),
      alpha_only alpha ext = true → ext.length ≤ N → bs ++ ext ∈ alpha_cyl alpha bs N := by
  intro N
  induction N with
  | zero =>
    intro bs ext Hext Hlen
    rcases ext with _ | ⟨b, ext⟩
    · rw [List.append_nil]
      exact List.mem_cons_self ..
    · exact absurd Hlen (by simp)
  | succ N ih =>
    intro bs ext Hext Hlen
    rcases ext with _ | ⟨b, ext⟩
    · rw [List.append_nil]
      exact List.mem_cons_self ..
    · rw [show alpha_cyl alpha bs (N + 1) =
        bs :: alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N) from rfl]
      refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap]
      rw [alpha_only, List.all_cons, Bool.and_eq_true] at Hext
      obtain ⟨Hb, Hext⟩ := Hext
      refine ⟨b, (alpha_memb_In alpha b).mp Hb, ?_⟩
      rw [show bs ++ b :: ext = (bs ++ [b]) ++ ext from by
        rw [List.append_assoc]; rfl]
      apply ih
      · exact Hext
      · rw [List.length_cons] at Hlen; omega

theorem alpha_cyl_sum_le (alpha : List (BitVec 8)) (p : Rat) (Hne : alpha ≠ [])
    (_Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    ∀ (N : Nat) (bs : List (BitVec 8)),
      qsum (fun s => alpha_geo_point alpha p s.length) (alpha_cyl alpha bs N) ≤
        alpha_geo_mass alpha p bs.length := by
  intro N
  induction N with
  | zero =>
    intro bs
    show qsum (fun s => alpha_geo_point alpha p s.length) [bs] ≤ alpha_geo_mass alpha p bs.length
    rw [qsum_cons, qsum_nil]
    have h := alpha_geo_point_le_mass alpha p bs.length Hp1
    grind
  | succ N ih =>
    intro bs
    show alpha_geo_point alpha p bs.length +
        qsum (fun s => alpha_geo_point alpha p s.length)
          (alpha.flatMap (fun b => alpha_cyl alpha (bs ++ [b]) N)) ≤
      alpha_geo_mass alpha p bs.length
    refine Rat.le_trans (b := alpha_geo_point alpha p bs.length +
      Qnat alpha.length * alpha_geo_mass alpha p (bs.length + 1)) ?_ ?_
    · refine Rat.add_le_add_left.mpr ?_
      refine Rat.le_trans (qsum_flat_map_const_le
        (fun s => alpha_geo_point alpha p s.length)
        (fun b => alpha_cyl alpha (bs ++ [b]) N) alpha
        (alpha_geo_mass alpha p (bs.length + 1)) ?_) Rat.le_refl
      intro b _
      refine Rat.le_trans (ih (bs ++ [b])) ?_
      rw [List.length_append]
      show alpha_geo_mass alpha p (bs.length + 1) ≤ alpha_geo_mass alpha p (bs.length + 1)
      exact Rat.le_refl
    · show p * Qpow ((1 - p) * alpha_ratio alpha) bs.length +
        Qnat alpha.length * Qpow ((1 - p) * alpha_ratio alpha) (bs.length + 1) ≤
        Qpow ((1 - p) * alpha_ratio alpha) bs.length
      rw [Qpow_succ]
      have hcancel : Qnat alpha.length * alpha_ratio alpha = 1 := alpha_ratio_cancel alpha Hne
      have h2 : Qnat alpha.length * ((1 - p) * alpha_ratio alpha *
          Qpow ((1 - p) * alpha_ratio alpha) bs.length) =
          (1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length := by
        calc Qnat alpha.length * ((1 - p) * alpha_ratio alpha *
              Qpow ((1 - p) * alpha_ratio alpha) bs.length)
            = (Qnat alpha.length * alpha_ratio alpha) * ((1 - p) *
                Qpow ((1 - p) * alpha_ratio alpha) bs.length) := by grind
          _ = 1 * ((1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length) := by rw [hcancel]
          _ = (1 - p) * Qpow ((1 - p) * alpha_ratio alpha) bs.length := by grind
      rw [h2]
      grind

/- =========================================================================
   Combinator: geometric file contents behind a fixed header, over a
   fixed ALPHABET
   ========================================================================= -/

/-- THE WEIGHT: `file_prefix_geo_weight` with one more test on the payload —
    every byte in the alphabet — and the alphabet's ratio in place of
    `1 / 256`.  A matching core whose file is `hdr ++ t` with `t` over the
    alphabet weighs `p * ((1 - p) * alpha_ratio) ^ length t`; a payload with
    any byte outside the alphabet weighs zero, as does a file that misses the
    header or a core off the environment. -/
def file_prefix_over_geo_weight (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) : Rat :=
  if c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  then match strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => if alpha_only alpha t then alpha_geo_point alpha p t.length else 0
    | none => 0
  else 0

theorem file_prefix_over_geo_weight_match (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t : List (BitVec 8)) (Ha : alpha_only alpha t = true) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t) = alpha_geo_point alpha p t.length := by
  unfold file_prefix_over_geo_weight file_prefix_core
  rw [fs_file_file_core, ite_eq_left rfl, strip_prefix_app]
  dsimp only []
  rw [Ha]
  rfl

/-- ZERO ON A PAYLOAD OUTSIDE THE ALPHABET, the rule this family adds. -/
theorem file_prefix_over_geo_weight_off_alphabet (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t : List (BitVec 8)) (Ha : alpha_only alpha t = false) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
      (file_prefix_core hdr argv envp fs0 pth s t) = 0 := by
  unfold file_prefix_over_geo_weight file_prefix_core
  rw [fs_file_file_core, ite_eq_left rfl, strip_prefix_app]
  dsimp only []
  rw [Ha]
  rfl

theorem file_prefix_over_geo_weight_mismatch (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hne : c ≠ file_core argv envp fs0 pth s (fs_file pth c.core_fs)) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  unfold file_prefix_over_geo_weight
  rw [ite_eq_right Hne]

theorem file_prefix_over_geo_weight_off_header (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hn : strip_prefix hdr (fs_file pth c.core_fs) = none) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  unfold file_prefix_over_geo_weight
  split
  · next _ => rw [Hn]
  · rfl

theorem file_prefix_over_geo_weight_off_header_zero (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hno : ∀ t, fs_file pth c.core_fs ≠ hdr ++ t) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  apply file_prefix_over_geo_weight_off_header
  exact strip_prefix_None_of_no_extension hdr _ Hno

theorem file_prefix_over_geo_weight_nonneg (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    0 ≤ file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c := by
  unfold file_prefix_over_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => exact Rat.le_refl
    | some t =>
      dsimp only []
      cases ha : alpha_only alpha t with
      | true => exact alpha_geo_point_nonneg alpha p t.length Hp0 Hp1
      | false => exact Rat.le_refl
  · exact Rat.le_refl

/-- The weight is at most the alphabet-geometric weight of the payload at
    EVERY payload, alphabet or not — the `<=` form of the block identity,
    which needs no hypothesis on the payloads enumerated. -/
theorem file_prefix_over_geo_weight_le_point (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s t : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
        (file_prefix_core hdr argv envp fs0 pth s t) ≤ alpha_geo_point alpha p t.length := by
  cases ha : alpha_only alpha t with
  | true =>
    rw [file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t ha]
    exact Rat.le_refl
  | false =>
    rw [file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t ha]
    exact alpha_geo_point_nonneg alpha p t.length Hp0 Hp1

/-- The distribution.  The alphabet's facts are constructor arguments, as
    the side conditions on `p_stop` are: nothing the constructor itself
    needs uses them — nonnegativity does not — but every certificate below
    does, `List.Nodup` for the witness families' duplicate-freedom and
    non-emptiness for the cancellation, and a distribution whose declared
    mass `1` could not be certified is not one this file wants to build. -/
def file_geometric_prefix_over (alpha : List (BitVec 8))
    (_Hnd : alpha.Nodup) (_Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution where
  cd_weight := file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
  cd_mass := 1
  cd_nonneg := file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1

/- =========================================================================
   The full alphabet: `file_geometric_prefix`, pointwise
   ========================================================================= -/

theorem file_prefix_over_geo_weight_all_bytes (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_prefix_over_geo_weight all_bytes hdr p argv envp fs0 pth s c =
      file_prefix_geo_weight hdr p argv envp fs0 pth s c := by
  unfold file_prefix_over_geo_weight file_prefix_geo_weight
  by_cases hc : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  · rw [ite_eq_left hc, ite_eq_left hc]
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => rfl
    | some t =>
      dsimp only []
      rw [alpha_only_all_bytes, alpha_geo_point_all_bytes]
      rfl
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem file_geometric_prefix_over_all_bytes_pointwise (Hnd : all_bytes.Nodup)
    (Hne : all_bytes ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore) :
    (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight c =
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight c :=
  file_prefix_over_geo_weight_all_bytes hdr p argv envp fs0 pth s c

theorem file_geometric_prefix_over_all_bytes_mass (Hnd : all_bytes.Nodup)
    (Hne : all_bytes ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    (file_geometric_prefix_over all_bytes Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_mass =
      (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass := rfl

/- =========================================================================
   The block identity, over the alphabet
   ========================================================================= -/

theorem qsum_file_prefix_over_block (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (B : List (List (BitVec 8)))
    (HB : ∀ t, t ∈ B → alpha_only alpha t = true) :
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) B) =
      qsum (fun t => alpha_geo_point alpha p t.length) B := by
  rw [qsum_map]
  apply qsum_ext
  intro t Ht
  exact file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t (HB t Ht)

theorem qsum_file_prefix_over_block_le (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (B : List (List (BitVec 8)))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) B) ≤
      qsum (fun t => alpha_geo_point alpha p t.length) B := by
  rw [qsum_map]
  apply qsum_mono
  intro t _
  exact file_prefix_over_geo_weight_le_point alpha hdr p argv envp fs0 pth s t Hp0 Hp1

/- =========================================================================
   The payload cylinder, and the enumeration that bounds it
   ========================================================================= -/

/-- The cylinder is `in_file_prefix_cylinder` unchanged: the fire set is
    described by a payload prefix, and a core in it whose payload leaves the
    alphabet weighs zero rather than being excluded.  The membership test
    carries the alphabet, for the filter. -/
def matches_file_prefix_over_env (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) : Bool :=
  matches_file_prefix_env hdr argv envp fs0 pth s c &&
    match strip_prefix hdr (fs_file pth c.core_fs) with
    | some t => alpha_only alpha t
    | none => false

theorem file_prefix_over_geo_weight_unmatched (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = false) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  unfold matches_file_prefix_over_env at H
  by_cases hm : matches_file_prefix_env hdr argv envp fs0 pth s c = false
  · rcases matches_file_prefix_env_false hdr argv envp fs0 pth s c hm with Hne | Hn
    · exact file_prefix_over_geo_weight_mismatch alpha hdr p argv envp fs0 pth s c Hne
    · exact file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c Hn
  · unfold file_prefix_over_geo_weight
    by_cases hc : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
    · rw [ite_eq_left hc]
      cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
      | none => rfl
      | some t =>
        dsimp only []
        have ha : alpha_only alpha t = false := by
          rcases hb : matches_file_prefix_env hdr argv envp fs0 pth s c with _ | _
          · exact absurd hb hm
          · rw [hb, hs] at H
            simpa using H
        rw [ha]
        rfl
    · rw [ite_eq_right hc]

theorem matches_file_prefix_over_env_true (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (H : matches_file_prefix_over_env alpha hdr argv envp fs0 pth s c = true) :
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ alpha_only alpha t = true := by
  unfold matches_file_prefix_over_env at H
  simp only [Bool.and_eq_true] at H
  obtain ⟨Henv, Ha⟩ := H
  obtain ⟨t, Ht⟩ := matches_file_prefix_env_true hdr argv envp fs0 pth s c Henv
  refine ⟨t, Ht, ?_⟩
  rw [Ht, fs_file_file_prefix_core, strip_prefix_app] at Ha
  exact Ha

/-- THE BOUND OVER CORES.  One step more than the 256-byte family: the list
    is first filtered to the cores that weigh anything (the rest weigh
    zero), and the survivors — payloads over the alphabet extending `bs` —
    are contained in `alpha_cyl` mapped through the template; the
    enumeration is then bounded by the `<=` block identity and
    `alpha_cyl_sum_le`.  No hypothesis on `bs` itself: a prefix that leaves
    the alphabet gives an empty filter and a bound of a positive number over
    zero. -/
theorem file_prefix_over_geo_weight_cylinder_bound (alpha hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hne : alpha ≠ []) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (bs : List (BitVec 8)) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_file_prefix_cylinder hdr argv envp fs0 pth s bs c) :
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) cs ≤
      alpha_geo_mass alpha p bs.length := by
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c Hc)]
  refine Rat.le_trans (qsum_core_incl_le
    (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) _
    (List.map (file_prefix_core hdr argv envp fs0 pth s)
      (alpha_cyl alpha bs (cores_file_prefix_depth hdr pth cs)))
    (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1)
    (List.Nodup.sublist List.filter_sublist Hnd) ?_) ?_
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨ext, Hext⟩ := Hcyl c Hin
    obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    have Hteq : t = bs ++ ext := by
      apply file_prefix_core_inj hdr argv envp fs0 pth s
      rw [← Ht, ← Hext]
    subst Hteq
    rw [alpha_only_app, Bool.and_eq_true] at Ha
    obtain ⟨_, Hae⟩ := Ha
    have Hd := cores_file_prefix_depth_ge hdr pth cs c (bs ++ ext) Hin
      (by rw [Hext, fs_file_file_prefix_core])
    rw [List.length_append] at Hd
    exact List.mem_map.mpr ⟨bs ++ ext, alpha_cyl_In alpha _ bs ext Hae (by omega), Ht.symm⟩
  · refine Rat.le_trans (qsum_file_prefix_over_block_le alpha hdr p argv envp fs0 pth s
      (alpha_cyl alpha bs (cores_file_prefix_depth hdr pth cs)) Hp0 Hp1) ?_
    exact alpha_cyl_sum_le alpha p Hne Hp0 Hp1 _ bs

/- =========================================================================
   The exports
   ========================================================================= -/

def file_geometric_prefix_over_cylinder_mass (alpha : List (BitVec 8)) (p : Rat)
    (bs : List (BitVec 8)) : Rat :=
  alpha_geo_mass alpha p bs.length

theorem file_geometric_prefix_over_cylinder_mass_closed_form (alpha : List (BitVec 8))
    (p : Rat) (bs : List (BitVec 8)) :
    file_geometric_prefix_over_cylinder_mass alpha p bs =
      Qpow (1 - p) bs.length * Qpow (alpha_ratio alpha) bs.length :=
  alpha_geo_mass_closed_form alpha p bs.length

theorem file_geometric_prefix_over_cylinder_mass_all_bytes (p : Rat)
    (bs : List (BitVec 8)) :
    file_geometric_prefix_over_cylinder_mass all_bytes p bs =
      file_geometric_prefix_cylinder_mass p bs :=
  alpha_geo_mass_all_bytes p bs.length

theorem file_geometric_prefix_over_bound (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f)) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤
      file_geometric_prefix_over_cylinder_mass alpha p bs := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
    alpha_geo_mass alpha p bs.length
  rw [core_sum_map_fin_core]
  exact file_prefix_over_geo_weight_cylinder_bound alpha hdr p argv envp fs0 pth s Hne
    Hp0 Hp1 bs (List.map fin_core l) Hndl (fun c Hc => by
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      exact Hcyl f Hf)

theorem file_geometric_prefix_over_bound_or_off_environment (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l →
      in_file_prefix_cylinder hdr argv envp fs0 pth s bs (fin_core f) ∨
        matches_file_prefix_over_env alpha hdr argv envp fs0 pth s (fin_core f) = false) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤
      file_geometric_prefix_over_cylinder_mass alpha p bs := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
    alpha_geo_mass alpha p bs.length
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c Hc)]
  apply file_prefix_over_geo_weight_cylinder_bound alpha hdr p argv envp fs0 pth s Hne Hp0 Hp1
  · exact List.Nodup.sublist List.filter_sublist Hndl
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    rcases Hor f Hf with h | h
    · exact h
    · rw [h] at Hm
      exact absurd Hm (by decide)

theorem file_geometric_prefix_over_mass_upper (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (l : List FinProcInput)
    (Hndl : (List.map fin_core l).Nodup) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤
      (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1).cd_mass := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤ 1
  refine Rat.le_trans (file_geometric_prefix_over_bound_or_off_environment alpha Hnd Hne
    hdr p argv envp fs0 pth s Hp0 Hp1 [] l Hndl ?_) ?_
  · intro f _
    by_cases hm : matches_file_prefix_over_env alpha hdr argv envp fs0 pth s
        (fin_core f) = true
    · left
      obtain ⟨t, Ht, _⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s
        (fin_core f) hm
      exact ⟨t, Ht⟩
    · right
      rcases hb : matches_file_prefix_over_env alpha hdr argv envp fs0 pth s (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm
  · show file_geometric_prefix_over_cylinder_mass alpha p [] ≤ 1
    exact Rat.le_refl

/- =========================================================================
   The counting lemma and the payload-length slice, over the alphabet
   ========================================================================= -/

theorem file_prefix_over_core_list_length_bound (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (n : Nat) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧
        t.length = n ∧ alpha_only alpha t = true) :
    cs.length ≤ alpha.length ^ n := by
  have Hle : cs.length ≤
      (List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_lists alpha n)).length := by
    apply nodup_subset_length
    · exact Hnd
    · intro c Hc
      obtain ⟨t, Ht, Hlen, Ha⟩ := Hall c Hc
      refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
      rw [← Hlen]
      exact alpha_lists_complete alpha t Ha
  rwa [List.length_map, alpha_lists_length] at Hle

theorem injective_core_list_in_file_prefix_over_cylinder_length_bound
    (alpha hdr : List (BitVec 8)) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧
        t.length = n ∧ alpha_only alpha t = true) :
    l.length ≤ alpha.length ^ n := by
  rw [← List.length_map (f := fin_core)]
  apply file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n
  · exact Hnd
  · intro c Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hc
    obtain ⟨t, Ht, Hlen, Ha⟩ := Hall f Hf
    exact ⟨t, by rw [← hfc, Ht], Hlen, Ha⟩

theorem injective_core_list_in_file_prefix_over_cylinder_length_bound_attained
    (alpha hdr : List (BitVec 8)) (Hnd : alpha.Nodup)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧
          t.length = n ∧ alpha_only alpha t = true) ∧
      l.length = alpha.length ^ n := by
  refine ⟨List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (alpha_lists alpha n), ?_, ?_, ?_⟩
  · rw [List.map_map]
    have hfun : (fin_core ∘ fun t => core_input
        (file_prefix_core hdr argv envp fs0 pth s t)) =
        (fun t => file_prefix_core hdr argv envp fs0 pth s t) := by
      funext t
      exact fin_core_core_input _
    rw [hfun]
    apply NoDup_map_inj
    · intro x y _ _ Heq
      exact file_prefix_core_inj _ _ _ _ _ _ _ _ Heq
    · exact alpha_lists_nodup alpha Hnd n
  · intro f Hf
    obtain ⟨t, Ht, rfl⟩ := List.mem_map.mp Hf
    exact ⟨t, fin_core_core_input _, alpha_lists_In_length alpha n t Ht,
      alpha_lists_In_alpha alpha n t Ht⟩
  · rw [List.length_map, alpha_lists_length]

/-- THE PAYLOAD-LENGTH SLICE, with no premise that the payloads are over the
    alphabet: the ones that are not weigh zero and are filtered away, and
    the survivors number at most `length alpha ^ n`. -/
theorem file_geometric_prefix_over_slice_bound (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤ p * Qpow (1 - p) n := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
    p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c Hc)]
  have Hslice : ∀ c, c ∈ List.filter (matches_file_prefix_over_env alpha hdr argv envp
      fs0 pth s) (List.map fin_core l) →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧
        t.length = n ∧ alpha_only alpha t = true := by
    intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Hlen⟩ := Hall f Hf
    obtain ⟨t', Ht', Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    have Hteq : t' = t := by
      apply file_prefix_core_inj hdr argv envp fs0 pth s
      rw [← Ht', ← hfc, Ht]
    subst t'
    exact ⟨t, Ht', Hlen, Ha⟩
  have hconst : qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (List.filter (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
        (List.map fin_core l)) =
      Qnat (List.filter (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
        (List.map fin_core l)).length * alpha_geo_point alpha p n :=
    qsum_const _ _ _ (fun c Hc => by
      obtain ⟨t, Ht, Hlen, Ha⟩ := Hslice c Hc
      rw [Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha, Hlen])
  rw [hconst, ← alpha_slice_total alpha p n Hne]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (alpha_geo_point_nonneg alpha p n Hp0 Hp1)
  apply Qnat_le
  exact file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n _
    (List.Nodup.sublist List.filter_sublist Hndl) Hslice

/-- THE WIDER SLICE STATEMENT for this family, in the whole-file shape:
    environment matched and file length `length hdr + n`, with no premise on
    the header or the alphabet. -/
theorem file_geometric_prefix_over_slice_bound_by_file_length (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = file_core argv envp fs0 pth s (fs_file pth f.fin_image_fs) ∧
        (fs_file pth f.fin_image_fs).length = hdr.length + n) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤ p * Qpow (1 - p) n := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
    p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c Hc)]
  have Hslice : ∀ c, c ∈ List.filter (matches_file_prefix_over_env alpha hdr argv envp
      fs0 pth s) (List.map fin_core l) →
      ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧
        t.length = n ∧ alpha_only alpha t = true := by
    intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    exact ⟨t, Ht, file_prefix_payload_length hdr argv envp fs0 pth s f t n
      (by rw [hfc, Ht]) (Hall f Hf).2, Ha⟩
  have hconst : qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
      (List.filter (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
        (List.map fin_core l)) =
      Qnat (List.filter (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s)
        (List.map fin_core l)).length * alpha_geo_point alpha p n :=
    qsum_const _ _ _ (fun c Hc => by
      obtain ⟨t, Ht, Hlen, Ha⟩ := Hslice c Hc
      rw [Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha, Hlen])
  rw [hconst, ← alpha_slice_total alpha p n Hne]
  refine Rat.mul_le_mul_of_nonneg_right ?_ (alpha_geo_point_nonneg alpha p n Hp0 Hp1)
  apply Qnat_le
  exact file_prefix_over_core_list_length_bound alpha hdr argv envp fs0 pth s n _
    (List.Nodup.sublist List.filter_sublist Hndl) Hslice

theorem file_geometric_prefix_over_slice_bound_attained (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) ∧
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l = p * Qpow (1 - p) n := by
  obtain ⟨l, Hndl, Hall, Hlen⟩ :=
    injective_core_list_in_file_prefix_over_cylinder_length_bound_attained
      alpha hdr Hnd argv envp fs0 pth s n
  refine ⟨l, Hndl, ?_, ?_⟩
  · intro f Hf
    obtain ⟨t, Ht, Hl, _⟩ := Hall f Hf
    exact ⟨t, Ht, Hl⟩
  · show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l =
      p * Qpow (1 - p) n
    rw [core_sum_map_fin_core]
    have hconst : qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
        (List.map fin_core l) =
        Qnat (List.map fin_core l).length * alpha_geo_point alpha p n :=
      qsum_const _ _ _ (fun c Hc => by
        obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
        obtain ⟨t, Ht, Hlen', Ha⟩ := Hall f Hf
        rw [Ht, file_prefix_over_geo_weight_match alpha hdr p argv envp fs0 pth s t Ha, Hlen'])
    rw [hconst, List.length_map, Hlen]
    exact alpha_slice_total alpha p n Hne

theorem file_geometric_prefix_over_slice_bound_sharp (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) (K : Rat)
    (Hbound : ∀ l : List FinProcInput, (List.map fin_core l).Nodup →
      (∀ f, f ∈ l →
        ∃ t, fin_core f = file_prefix_core hdr argv envp fs0 pth s t ∧ t.length = n) →
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤ K) :
    p * Qpow (1 - p) n ≤ K := by
  obtain ⟨l, Hndl, Hall, Hsum⟩ :=
    file_geometric_prefix_over_slice_bound_attained alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1 n
  rw [← Hsum]
  exact Hbound l Hndl Hall

/- =========================================================================
   The lower certificate for `file_geometric_prefix_over`
   ========================================================================= -/

def file_prefix_over_geo_lower_witness (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) : List FinProcInput :=
  List.map (fun t => core_input (file_prefix_core hdr argv envp fs0 pth s t))
    (alpha_short_inputs alpha k)

theorem map_fin_core_file_prefix_over_geo_lower_witness (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) :
    List.map fin_core (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k) =
      List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_short_inputs alpha k) := by
  rw [file_prefix_over_geo_lower_witness, List.map_map]
  apply List.map_congr_left
  intro t _
  exact fin_core_core_input _

theorem file_prefix_over_geo_lower_witness_nodup (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) :
    (List.map fin_core
      (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)).Nodup := by
  rw [map_fin_core_file_prefix_over_geo_lower_witness]
  apply NoDup_map_inj
  · intro x y _ _ Heq
    exact file_prefix_core_inj _ _ _ _ _ _ _ _ Heq
  · exact alpha_short_inputs_nodup alpha Hnd k

theorem qsum_file_prefix_over_short_inputs (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (k : Nat) (Hne : alpha ≠ []) :
    qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_short_inputs alpha k)) =
      geo_prefix_sum p k :=
  calc qsum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
        (List.map (file_prefix_core hdr argv envp fs0 pth s) (alpha_short_inputs alpha k))
      = qsum (fun t => alpha_geo_point alpha p t.length) (alpha_short_inputs alpha k) :=
        qsum_file_prefix_over_block alpha hdr p argv envp fs0 pth s _
          (fun t Ht => alpha_short_inputs_In_alpha alpha k t Ht)
    _ = geo_prefix_sum p k := alpha_short_inputs_sum alpha p k Hne

theorem file_geometric_prefix_over_mass_lower_witness (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    (List.map fin_core
      (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k)).Nodup ∧
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_weight
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k) =
        1 - Qpow (1 - p) k := by
  refine ⟨file_prefix_over_geo_lower_witness_nodup alpha Hnd hdr argv envp fs0 pth s k, ?_⟩
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) _ =
    1 - Qpow (1 - p) k
  rw [core_sum_map_fin_core, map_fin_core_file_prefix_over_geo_lower_witness,
    qsum_file_prefix_over_short_inputs alpha hdr p argv envp fs0 pth s k Hne,
    geo_prefix_sum_closed]

theorem file_geometric_prefix_over_mass_lower_prefix (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (k : Nat) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_weight l = 1 - Qpow (1 - p) k :=
  ⟨file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s k,
    file_geometric_prefix_over_mass_lower_witness alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1 k⟩

theorem file_geometric_prefix_over_mass_lower_certificate (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (eps : Rat)
    (Hpos : 0 < p) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_mass - eps ≤
        core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_weight l := by
  obtain ⟨k, Hk⟩ := geo_gap_small p eps Hpos Hp1 Heps
  obtain ⟨l, Hndl, Hsum⟩ :=
    file_geometric_prefix_over_mass_lower_prefix alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1 k
  refine ⟨l, Hndl, ?_⟩
  rw [Hsum]
  show (1 : Rat) - eps ≤ 1 - Qpow (1 - p) k
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hk)

/- =========================================================================... and this mass is a SUPREMUM and not a maximum
   ========================================================================= -/

theorem file_geometric_prefix_over_bound_by_max_length (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat)
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l ≤ 1 - Qpow (1 - p) (n + 1) := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
    1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s)
    (matches_file_prefix_over_env alpha hdr argv envp fs0 pth s) _
    (fun c Hc => file_prefix_over_geo_weight_unmatched alpha hdr p argv envp fs0 pth s c Hc)]
  refine Rat.le_trans (qsum_core_incl_le
    (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) _
    (List.map (file_prefix_core hdr argv envp fs0 pth s)
      (alpha_short_inputs alpha (n + 1)))
    (file_prefix_over_geo_weight_nonneg alpha hdr p argv envp fs0 pth s Hp0 Hp1)
    (List.Nodup.sublist List.filter_sublist Hndl) ?_) ?_
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    obtain ⟨t, Ht, Ha⟩ := matches_file_prefix_over_env_true alpha hdr argv envp fs0 pth s c Hm
    refine List.mem_map.mpr ⟨t, ?_, Ht.symm⟩
    apply alpha_short_inputs_complete alpha (n + 1) t Ha
    have hfs : fs_file pth c.core_fs = hdr ++ t := by
      rw [Ht]
      exact fs_file_file_prefix_core hdr argv envp fs0 pth s t
    have hfs2 : fs_file pth f.fin_image_fs = hdr ++ t := by
      have h := hfs
      rw [← hfc] at h
      exact h
    have hle := Hlen f Hf
    rw [hfs2, List.length_append] at hle
    show t.length < n + 1
    omega
  · rw [qsum_file_prefix_over_short_inputs alpha hdr p argv envp fs0 pth s (n + 1) Hne,
      geo_prefix_sum_closed]
    exact Rat.le_refl

theorem file_geometric_prefix_over_bound_by_max_length_attained (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (n : Nat) :
    (∀ f, f ∈ file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (n + 1) →
        (fs_file pth f.fin_image_fs).length ≤ hdr.length + n) ∧
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_weight
        (file_prefix_over_geo_lower_witness alpha hdr argv envp fs0 pth s (n + 1)) =
        1 - Qpow (1 - p) (n + 1) := by
  refine ⟨?_, (file_geometric_prefix_over_mass_lower_witness alpha Hnd Hne hdr p argv envp
    fs0 pth s Hp0 Hp1 (n + 1)).2⟩
  intro f Hf
  rw [file_prefix_over_geo_lower_witness] at Hf
  obtain ⟨t, Ht, rfl⟩ := List.mem_map.mp Hf
  have hfs : fs_file pth
      (core_input (file_prefix_core hdr argv envp fs0 pth s t)).fin_image_fs = hdr ++ t :=
    fs_file_file_prefix_core hdr argv envp fs0 pth s t
  rw [hfs, List.length_append]
  have := alpha_short_inputs_In_length alpha (n + 1) t Ht
  omega

theorem file_geometric_prefix_over_mass_not_attained (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup) :
    core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_weight l <
      (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_mass := by
  show core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l < 1
  generalize hN : list_max (List.map (fun f => (fs_file pth f.fin_image_fs).length) l) = N
  have h1 : core_sum (file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s) l ≤
      1 - Qpow (1 - p) (N + 1) :=
    file_geometric_prefix_over_bound_by_max_length alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1 N l Hndl
      (fun f Hf => by
        have hin : (fs_file pth f.fin_image_fs).length ∈
            List.map (fun g => (fs_file pth g.fin_image_fs).length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

theorem file_geometric_prefix_over_mass_supremum_not_maximum (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hlt : p < 1)
    (l : List FinProcInput) (Hndl : (List.map fin_core l).Nodup) :
    ¬ (core_sum (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_weight l =
        (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
          Hp0 Hp1).cd_mass) :=
  Rat.ne_of_lt (file_geometric_prefix_over_mass_not_attained alpha Hnd Hne hdr p argv envp
    fs0 pth s Hp0 Hp1 Hlt l Hndl)

/- =========================================================================
   Non-vacuity: the alphabet bites
   ========================================================================= -/

theorem file_prefix_over_geo_weight_off_environment_zero (alpha hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : c.core_argv ≠ argv) :
    file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0 := by
  apply file_prefix_over_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

theorem file_geometric_prefix_over_off_header_zero (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (c : FinCore)
    (Hno : ∀ t, fs_file pth c.core_fs ≠ hdr ++ t) :
    (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight c = 0 ∧
      (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_mass = 1 := by
  refine ⟨?_, rfl⟩
  show file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c = 0
  exact file_prefix_over_geo_weight_off_header_zero alpha hdr p argv envp fs0 pth s c Hno

/-- THE ALPHABET BITES, in general: a payload with a byte outside the
    alphabet weighs zero while the declared mass stays `1`. -/
theorem file_geometric_prefix_over_off_alphabet_zero (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (t : List (BitVec 8))
    (Ha : alpha_only alpha t = false) :
    (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight
        (file_prefix_core hdr argv envp fs0 pth s t) = 0 ∧
      (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
        Hp0 Hp1).cd_mass = 1 := by
  refine ⟨?_, rfl⟩
  show file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s
    (file_prefix_core hdr argv envp fs0 pth s t) = 0
  exact file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t Ha

/-- A one-byte alphabet, a payload in it and a payload outside it, all behind
    the one-byte example header. -/
def file_example_alpha : List (BitVec 8) := [BitVec.ofInt 8 65]

theorem file_example_alpha_nodup : file_example_alpha.Nodup :=
  List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩

theorem file_example_alpha_ne : file_example_alpha ≠ [] := by
  intro h
  cases h

def file_example_in_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [BitVec.ofInt 8 65]

def file_example_off_alpha_core : FinCore :=
  file_prefix_core file_example_hdr [] [] [] file_example_path [] [BitVec.ofInt 8 66]

/-- THE ALPHABET BITES, exhibited: the off-alphabet core — which the
    256-byte header family weighs POSITIVELY — weighs zero, the in-alphabet
    core weighs positively, and the mass is `1`. -/
theorem file_geometric_prefix_over_alphabet_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hpos : 0 < p) (Hlt : p < 1) :
    (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
      file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
      Hp0 Hp1).cd_weight file_example_off_alpha_core = 0 ∧
      0 < (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight file_example_in_alpha_core ∧
      (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_mass = 1 ∧
      0 < (file_geometric_prefix file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight file_example_off_alpha_core := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
      file_example_path [] file_example_off_alpha_core = 0
    apply file_prefix_over_geo_weight_off_alphabet
    show alpha_only file_example_alpha [BitVec.ofInt 8 66] = false
    decide
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
      file_example_path [] file_example_in_alpha_core
    unfold file_example_in_alpha_core
    rw [file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _
      (by decide : alpha_only file_example_alpha [BitVec.ofInt 8 65] = true)]
    exact alpha_geo_point_pos file_example_alpha p _ Hpos Hlt file_example_alpha_ne
  · rfl
  · show 0 < file_prefix_geo_weight file_example_hdr p [] [] [] file_example_path []
      file_example_off_alpha_core
    unfold file_example_off_alpha_core
    rw [file_prefix_geo_weight_match]
    exact geo_point_pos p _ Hpos Hlt

theorem file_geometric_prefix_over_bites (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hpos : 0 < p) (Hlt : p < 1) :
    0 < (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
      file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
      Hp0 Hp1).cd_weight file_example_in_alpha_core ∧
      (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p [] [] [] file_example_path []
        Hp0 Hp1).cd_weight geo_example_other = 0 := by
  refine ⟨(file_geometric_prefix_over_alphabet_bites p Hp0 Hp1 Hpos Hlt).2.1, ?_⟩
  show file_prefix_over_geo_weight file_example_alpha file_example_hdr p [] [] []
    file_example_path [] geo_example_other = 0
  apply file_prefix_over_geo_weight_off_environment_zero
  show geo_example_other.core_argv ≠ []
  unfold geo_example_other
  intro h
  cases h

/- =========================================================================
   Non-vacuity: the mass is reached at `p_stop = 1`, and `List.NoDup` is
   load-bearing
   ========================================================================= -/

def file_prefix_over_point_cd : CoreDistribution :=
  file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
    file_example_alpha_ne file_example_hdr 1 [] [] [] file_example_path []
    Qle_0_1 Rat.le_refl

theorem file_prefix_over_point_cd_weight_hdr :
    file_prefix_over_geo_weight file_example_alpha file_example_hdr 1 [] [] []
      file_example_path [] (fin_core file_hdr_input) = 1 := by
  rw [show fin_core file_hdr_input = file_example_hdr_core from fin_core_core_input _]
  show file_prefix_over_geo_weight file_example_alpha file_example_hdr 1 [] [] []
    file_example_path []
    (file_prefix_core file_example_hdr [] [] [] file_example_path [] []) = 1
  rw [file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _
    (by rfl : alpha_only file_example_alpha [] = true)]
  unfold alpha_geo_point alpha_geo_mass
  show 1 * Qpow ((1 - 1) * alpha_ratio file_example_alpha) 0 = 1
  rw [Qpow_0]
  grind

theorem file_prefix_over_point_cd_mass_attained :
    (List.map fin_core [file_hdr_input]).Nodup ∧
      core_sum file_prefix_over_point_cd.cd_weight [file_hdr_input] =
        file_prefix_over_point_cd.cd_mass := by
  refine ⟨?_, ?_⟩
  · rw [List.map_cons, List.map_nil, List.nodup_cons]
    exact ⟨List.not_mem_nil, List.nodup_nil⟩
  · show core_sum (file_prefix_over_geo_weight file_example_alpha file_example_hdr 1
      [] [] [] file_example_path []) [file_hdr_input] = 1
    rw [core_sum_map_fin_core]
    show file_prefix_over_geo_weight file_example_alpha file_example_hdr 1 [] [] []
      file_example_path [] (fin_core file_hdr_input) + 0 = 1
    rw [file_prefix_over_point_cd_weight_hdr]
    grind

theorem file_geometric_prefix_over_bound_needs_nodup :
    ¬ (List.map fin_core [file_hdr_input, file_hdr_input]).Nodup ∧
      (∀ f, f ∈ [file_hdr_input, file_hdr_input] →
        in_file_prefix_cylinder file_example_hdr [] [] [] file_example_path [] []
          (fin_core f)) ∧
      ¬ (core_sum file_prefix_over_point_cd.cd_weight [file_hdr_input, file_hdr_input] ≤
        file_geometric_prefix_over_cylinder_mass file_example_alpha 1 []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.mem_cons_self ..)
  · intro f Hf
    have hfc : f = file_hdr_input →
        fin_core f = file_prefix_core file_example_hdr [] [] [] file_example_path [] [] := by
      intro h
      rw [h]
      exact fin_core_core_input _
    rcases List.mem_cons.mp Hf with h | h
    · exact ⟨[], hfc h⟩
    · rcases List.mem_cons.mp h with h2 | h2
      · exact ⟨[], hfc h2⟩
      · exact absurd h2 (List.not_mem_nil)
  · intro Hle
    have hsum : core_sum file_prefix_over_point_cd.cd_weight
        [file_hdr_input, file_hdr_input] = 2 := by
      show file_prefix_over_geo_weight file_example_alpha file_example_hdr 1 [] [] []
        file_example_path [] (fin_core file_hdr_input) +
        (file_prefix_over_geo_weight file_example_alpha file_example_hdr 1 [] [] []
          file_example_path [] (fin_core file_hdr_input) + 0) = 2
      rw [file_prefix_over_point_cd_weight_hdr]
      grind
    have hm : file_geometric_prefix_over_cylinder_mass file_example_alpha 1
        ([] : List (BitVec 8)) = 1 := rfl
    rw [hsum, hm] at Hle
    exact absurd Hle (by grind)

/- =========================================================================
   The two degenerate endpoints, both pinned
   ========================================================================= -/

theorem file_prefix_over_geo_weight_zero_at_zero_p (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_prefix_over_geo_weight alpha hdr 0 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_over_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => rfl
    | some t =>
      dsimp only []
      cases ha : alpha_only alpha t with
      | true => unfold alpha_geo_point; grind
      | false => rfl
  · rfl

theorem file_geometric_prefix_over_mass_lower_needs_positive (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) :
    (∀ l : List FinProcInput,
      core_sum (file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1).cd_weight l = 0) ∧
      ¬ ((file_geometric_prefix_over alpha Hnd Hne hdr 0 argv envp fs0 pth s
        Rat.le_refl Qle_0_1).cd_mass - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show file_prefix_over_geo_weight alpha hdr 0 argv envp fs0 pth s c = 0
    exact file_prefix_over_geo_weight_zero_at_zero_p alpha hdr argv envp fs0 pth s c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

theorem file_prefix_over_geo_weight_collapses_at_one_p (alpha hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : fs_file pth c.core_fs ≠ hdr) :
    file_prefix_over_geo_weight alpha hdr 1 argv envp fs0 pth s c = 0 := by
  unfold file_prefix_over_geo_weight
  split
  · next _ =>
    cases hs : strip_prefix hdr (fs_file pth c.core_fs) with
    | none => rfl
    | some t =>
      dsimp only []
      cases ha : alpha_only alpha t with
      | false => rfl
      | true =>
        have hds : fs_file pth c.core_fs = hdr ++ t := strip_prefix_Some hdr _ t hs
        rcases t with _ | ⟨b, t⟩
        · exact absurd (by rw [hds, List.append_nil]) Hne
        · show alpha_geo_point alpha 1 (b :: t).length = 0
          unfold alpha_geo_point alpha_geo_mass
          rw [List.length_cons, Qpow_succ]
          grind
  · rfl

theorem file_geometric_prefix_over_needs_p_below_one (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8))
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne' : fs_file pth c.core_fs ≠ hdr) :
    (file_geometric_prefix_over alpha Hnd Hne hdr 1 argv envp fs0 pth s
      Qle_0_1 Rat.le_refl).cd_weight c = 0 := by
  show file_prefix_over_geo_weight alpha hdr 1 argv envp fs0 pth s c = 0
  exact file_prefix_over_geo_weight_collapses_at_one_p alpha hdr argv envp fs0 pth s c Hne'

/- =========================================================================
   Combinator: geometric file contents over a VARYING launch-time
   environment
   ========================================================================= -/

/-- THE TEMPLATE, with both varying coordinates plugged in: the core over a
    fixed argv, a fixed base file system and a fixed standard input,
    carrying environment `es` and file contents `d`.

    It is `file_core` with the environment moved from the fixed parameters
    to the varying ones, and it is DEFINED as `file_core` rather than
    written out again so that the two round trips this family needs are the
    ones `file_geometric` already proved: `fs_file_file_envp_core` is
    `fs_file_file_core`, and the injectivity in the contents that both the
    counting and the duplicate-freedom arguments spend is `file_core_inj`
    unchanged. -/
def file_envp_core (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (es : List (List (BitVec 8))) (d : List (BitVec 8)) : FinCore :=
  file_core argv es fs0 pth s d

theorem fs_file_file_envp_core (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (es : List (List (BitVec 8)))
    (d : List (BitVec 8)) :
    fs_file pth (file_envp_core argv fs0 pth s es d).core_fs = d :=
  fs_file_file_core argv es fs0 pth s d

theorem core_envp_file_envp_core (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (es : List (List (BitVec 8)))
    (d : List (BitVec 8)) :
    (file_envp_core argv fs0 pth s es d).core_envp = es := rfl

/-- THE WEIGHT.  Zero unless the core's argv, standard input and the rest of
    its file system are the fixed ones; otherwise the environment's weight
    times the geometric weight of its input file's length.

    It is `envp_geo_weight` WITH ITS STANDARD-INPUT FACTOR REPLACED, and
    that is the whole difference: `envp_point r q` on the environment
    coordinate is the same object, spread by the same two nested memoryless
    sources, and `geo_point p` is applied to
    `length (fs_file pth (core_fs c))` where the other family applies it to
    `length (core_stdin c)`.

    WHY BOTH COORDINATES AT ONCE, rather than mixing `file_geometric` with
    `stdin_envp_geometric` through `cd_mix2`: a mixture of the two would put
    weight on cores varying the file at the CANONICAL environment and on
    cores varying the environment at the CANONICAL file, and none at all on
    a core varying both.  A defect reachable only from a non-canonical
    environment AND a particular input file would still sit in a null set.
    This family is the product measure, so it does not. -/
def file_envp_geo_weight (p r q : Rat) (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore) : Rat :=
  if c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs)
  then envp_point r q c.core_envp * geo_point p (fs_file pth c.core_fs).length
  else 0

theorem file_envp_geo_weight_match (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (es : List (List (BitVec 8))) (d : List (BitVec 8)) :
    file_envp_geo_weight p r q argv fs0 pth s (file_envp_core argv fs0 pth s es d) =
      envp_point r q es * geo_point p d.length := by
  unfold file_envp_geo_weight file_envp_core
  rw [fs_file_file_core]
  split
  · next _ => rfl
  · next h => exact absurd rfl h

theorem file_envp_geo_weight_mismatch (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (Hne : c ≠ file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs)) :
    file_envp_geo_weight p r q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  rw [ite_eq_right Hne]

/-- THE FAMILY'S FORMULA, all six factors visible at once, stated for the
    reason `envp_geo_weight_closed_form` is: the specification is quoted in
    that shape and a reader should be able to check the definition against
    it without unfolding anything. -/
theorem file_envp_geo_weight_closed_form (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (es : List (List (BitVec 8))) (d : List (BitVec 8)) :
    file_envp_geo_weight p r q argv fs0 pth s (file_envp_core argv fs0 pth s es d) =
      r * Qpow (1 - r) es.length * entries_geo_product q es *
        (p * Qpow (1 - p) d.length * Qpow (1 / 256) d.length) := by
  rw [file_envp_geo_weight_match, envp_point_closed_form, geo_point_closed_form]

theorem file_envp_geo_weight_nonneg (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (c : FinCore) :
    0 ≤ file_envp_geo_weight p r q argv fs0 pth s c := by
  unfold file_envp_geo_weight
  split
  · next _ =>
    exact Rat.mul_nonneg (envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 _)
      (geo_point_nonneg p _ Hp0 Hp1)
  · exact Rat.le_refl

/-- The distribution.  Mass `1` is DECLARED, as everywhere in this file.
    The six side conditions are constructor arguments for the reason
    `stdin_envp_geometric`'s six are: `cd_nonneg` is a field.  None of the
    three STRICT inequalities is demanded, for the reason none is demanded
    there — nothing the constructor needs uses them, and the lower
    certificate that does asks for all three as hypotheses of its own
    statement. -/
def file_envp_geometric (p r q : Rat) (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution where
  cd_weight := file_envp_geo_weight p r q argv fs0 pth s
  cd_mass := 1
  cd_nonneg := file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1

/- =========================================================================
   The two coordinates, recombined
   ========================================================================= -/

/-- Every core over the fixed argv, base file system and standard input
    whose environment comes from `A` and whose file contents come from `B`.

    A core of this family is a PAIR and the weight is one factor per
    coordinate, so the enumeration is the product of the two coordinates'
    enumerations and its sum is the product of their sums
    (`qsum_file_envp_product`).  That identity is the only place the
    coordinates meet, and every bound below is assembled from an envp bound
    and a file-contents bound proved apart. -/
def file_envp_product (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (A : List (List (List (BitVec 8))))
    (B : List (List (BitVec 8))) : List FinCore :=
  A.flatMap (fun es => B.map (file_envp_core argv fs0 pth s es))

theorem In_file_envp_product (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (A : List (List (List (BitVec 8))))
    (B : List (List (BitVec 8))) (es : List (List (BitVec 8)))
    (d : List (BitVec 8)) (HA : es ∈ A) (HB : d ∈ B) :
    file_envp_core argv fs0 pth s es d ∈ file_envp_product argv fs0 pth s A B := by
  unfold file_envp_product
  exact List.mem_flatMap.mpr ⟨es, HA, List.mem_map.mpr ⟨d, HB, rfl⟩⟩

theorem qsum_file_envp_block (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (es : List (List (BitVec 8))) (B : List (List (BitVec 8))) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s)
        (List.map (file_envp_core argv fs0 pth s es) B) =
      qsum (fun d => geo_point p d.length) B * envp_point r q es := by
  rw [qsum_map]
  calc qsum (fun d => file_envp_geo_weight p r q argv fs0 pth s
        (file_envp_core argv fs0 pth s es d)) B
      = qsum (fun d => envp_point r q es * geo_point p d.length) B :=
        qsum_ext _ _ _ (fun d _ => file_envp_geo_weight_match p r q argv fs0 pth s es d)
    _ = envp_point r q es * qsum (fun d => geo_point p d.length) B :=
        qsum_scale (envp_point r q es) (fun d => geo_point p d.length) B
    _ = qsum (fun d => geo_point p d.length) B * envp_point r q es := by grind

theorem qsum_file_envp_product (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (A : List (List (List (BitVec 8)))) (B : List (List (BitVec 8))) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s)
        (file_envp_product argv fs0 pth s A B) =
      qsum (envp_point r q) A * qsum (fun d => geo_point p d.length) B := by
  unfold file_envp_product
  rw [qsum_flat_map]
  calc qsum (fun es => qsum (file_envp_geo_weight p r q argv fs0 pth s)
        (List.map (file_envp_core argv fs0 pth s es) B)) A
      = qsum (fun es => qsum (fun d => geo_point p d.length) B *
          envp_point r q es) A :=
        qsum_ext _ _ _ (fun es _ => qsum_file_envp_block p r q argv fs0 pth s es B)
    _ = qsum (fun d => geo_point p d.length) B * qsum (envp_point r q) A :=
        qsum_scale (qsum (fun d => geo_point p d.length) B) (envp_point r q) A
    _ = qsum (envp_point r q) A * qsum (fun d => geo_point p d.length) B := by grind

/-- The product of two duplicate-free enumerations repeats nothing: the
    blocks are duplicate-free because a core determines its file contents
    (`file_core_inj`), and two blocks are disjoint because a core determines
    its environment.  Only the lower certificate needs this — the bounds are
    proved against a containing list nobody has to show duplicate-free. -/
theorem NoDup_file_envp_product (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (A : List (List (List (BitVec 8))))
    (B : List (List (BitVec 8))) (HA : A.Nodup) (HB : B.Nodup) :
    (file_envp_product argv fs0 pth s A B).Nodup := by
  unfold file_envp_product
  refine NoDup_flat_map _ _ HA (fun es _ => ?_) (fun es1 es2 c _ _ H1 H2 => ?_)
  · apply NoDup_map_inj
    · intro x y _ _ Heq
      exact file_core_inj _ _ _ _ _ _ _ Heq
    · exact HB
  · obtain ⟨d1, Hd1, h1⟩ := List.mem_map.mp H1
    obtain ⟨d2, Hd2, h2⟩ := List.mem_map.mp H2
    have h : file_envp_core argv fs0 pth s es1 d1 =
        file_envp_core argv fs0 pth s es2 d2 := by rw [h1, h2]
    have := congrArg FinCore.core_envp h
    simpa [file_envp_core, file_core] using this

/- =========================================================================
   The cylinder bound over cores
   ========================================================================= -/

/-- The cores this bound is about: the fixed argv, base file system and
    standard input, an environment EXTENDING `es` and file contents
    EXTENDING `bs`.  Two existentials rather than a conjunction of four
    tests, for the reason `in_envp_stdin_cylinder` is two. -/
def in_file_envp_cylinder (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (es : List (List (BitVec 8))) (bs : List (BitVec 8))
    (c : FinCore) : Prop :=
  ∃ eext ext, c = file_envp_core argv fs0 pth s (es ++ eext) (bs ++ ext)

/-- The cylinder's mass: the product of what the two coordinates
    contribute, `envp_factor` on one and `geo_mass` on the other. -/
def file_envp_geometric_cylinder_mass (p r q : Rat) (es : List (List (BitVec 8)))
    (bs : List (BitVec 8)) : Rat :=
  envp_factor r q es * geo_mass p bs.length

theorem file_envp_geometric_cylinder_mass_closed_form (p r q : Rat)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) :
    file_envp_geometric_cylinder_mass p r q es bs =
      Qpow (1 - r) es.length * entries_geo_product q es *
        (Qpow (1 - p) bs.length * Qpow (1 / 256) bs.length) := by
  unfold file_envp_geometric_cylinder_mass
  rw [envp_factor_closed_form, geo_mass_closed_form]

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.

    THREE DEPTHS are read off the task's own list, exactly as the
    envp-varying family reads three: how many entries an environment has
    (`cores_envp_depth`), how long an entry is (`cores_entry_depth`) and
    how long the input file is (`cores_file_depth`, `file_geometric`'s, in
    the place `cores_stdin_depth` took there).  The product of the two
    coordinates' enumerations contains the list, its sum is the product of
    the two sums, and each factor has its bound already
    (`envp_enum_sum_le`, `bytes_cyl_sum_le`). -/
theorem file_envp_geo_weight_cylinder_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List (BitVec 8)))
    (bs : List (BitVec 8)) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_file_envp_cylinder argv fs0 pth s es bs c) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s) cs ≤
      file_envp_geometric_cylinder_mass p r q es bs := by
  refine Rat.le_trans (qsum_core_incl_le (file_envp_geo_weight p r q argv fs0 pth s) cs
    (file_envp_product argv fs0 pth s
      (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
      (bytes_cyl bs (cores_file_depth pth cs)))
    (file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨eext, ext, Heq⟩ := Hcyl c Hc
    have Henvp : (es ++ eext).length ≤ cores_envp_depth cs := by
      have h := cores_envp_depth_ge cs c Hc
      rw [Heq, core_envp_file_envp_core] at h
      exact h
    have Hfile : (bs ++ ext).length ≤ cores_file_depth pth cs := by
      have h := cores_file_depth_ge pth cs c Hc
      rw [Heq, fs_file_file_envp_core] at h
      exact h
    rw [List.length_append] at Henvp Hfile
    rw [Heq]
    refine In_file_envp_product argv fs0 pth s _ _ (es ++ eext) (bs ++ ext) ?_ ?_
    · apply envp_enum_complete
      · omega
      · intro e He
        exact cores_entry_depth_gt cs c e Hc (by
          rw [Heq]
          exact List.mem_append.mpr (Or.inr He))
    · apply bytes_cyl_In
      omega
  · rw [qsum_file_envp_product]
    unfold file_envp_geometric_cylinder_mass
    exact Qmult_le_compat_nonneg (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ _)
      (bytes_cyl_sum_le p Hp0 Hp1 _ bs)
      (qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x))
      (qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1))

/- =========================================================================
   The file-and-environment family's exports
   ========================================================================= -/

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in
    the cylinder over an environment prefix and a file-contents prefix,
    weighs at most that cylinder's mass.

    This is the statement the family exists for.  A fire set described by
    "the environment begins with these entries and the input file begins
    with these bytes" is charged a number that depends on BOTH, where
    `file_geometric_bound` would charge the file cylinder's whole mass at
    the canonical environment and nothing anywhere else, and
    `stdin_envp_geometric_bound` would charge nothing at all at any core
    whose file system is not the fixed one. -/
theorem file_envp_geometric_bound (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (es : List (List (BitVec 8))) (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_file_envp_cylinder argv fs0 pth s es bs (fin_core f)) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      file_envp_geometric_cylinder_mass p r q es bs := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  exact file_envp_geo_weight_cylinder_bound p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
    es bs (List.map fin_core l) Hnd (fun c Hc => by
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      exact Hcyl f Hf)

/-- The launch-time test as a boolean, so that `List.filter` can use it.  It
    is `matches_file_env` with the environment left free: this family fixes
    argv, standard input and the base file system, so the equation a core
    has to satisfy in order to weigh anything is the template with BOTH its
    envp and its file contents plugged in. -/
def matches_argv_file_fs (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) : Bool :=
  decide (c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs))

theorem matches_argv_file_fs_false (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (H : matches_argv_file_fs argv fs0 pth s c = false) :
    c ≠ file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) :=
  of_decide_eq_false H

theorem matches_argv_file_fs_true (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (H : matches_argv_file_fs argv fs0 pth s c = true) :
    c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) :=
  of_decide_eq_true H

/-- THE CYLINDER BOUND, SLACKENED THE ONLY WAY IT CAN BE, exactly as the
    other three families slacken theirs: each record is in the cylinder OR
    its core misses the fixed argv, standard input or base file system and
    therefore weighs nothing. -/
theorem file_envp_geometric_bound_or_off_environment (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (es : List (List (BitVec 8)))
    (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hor : ∀ f, f ∈ l →
      in_file_envp_cylinder argv fs0 pth s es bs (fin_core f) ∨
        matches_argv_file_fs argv fs0 pth s (fin_core f) = false) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      file_envp_geometric_cylinder_mass p r q es bs := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤ _
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_envp_geo_weight p r q argv fs0 pth s)
    (matches_argv_file_fs argv fs0 pth s) _
    (fun c Hc => file_envp_geo_weight_mismatch p r q argv fs0 pth s c
      (matches_argv_file_fs_false argv fs0 pth s c Hc))]
  apply file_envp_geo_weight_cylinder_bound p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
  · exact List.Nodup.sublist List.filter_sublist Hnd
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hin
    rcases Hor f Hf with h | h
    · exact h
    · rw [h] at Hm
      exact absurd Hm (by decide)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared
    mass `1`.  It is the disjunctive bound at the two EMPTY prefixes, and
    the whole content is that the disjunction is EXHAUSTIVE there.  Both
    cylinder masses at the empty prefix are `1`, one because `envp_factor`
    of no entries is and one because `Qpow` at exponent zero is. -/
theorem file_envp_geometric_mass_upper (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤
      (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤ 1
  refine Rat.le_trans (file_envp_geometric_bound_or_off_environment p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 [] [] l Hnd ?_) ?_
  · intro f _
    by_cases hm : matches_argv_file_fs argv fs0 pth s (fin_core f) = true
    · left
      exact ⟨(fin_core f).core_envp, fs_file pth (fin_core f).core_fs,
        matches_argv_file_fs_true argv fs0 pth s (fin_core f) hm⟩
    · right
      rcases hb : matches_argv_file_fs argv fs0 pth s (fin_core f) with _ | _
      · rfl
      · exact absurd hb hm
  · show file_envp_geometric_cylinder_mass p r q [] [] ≤ 1
    unfold file_envp_geometric_cylinder_mass geo_mass
    rw [envp_factor_nil]
    simp [Qpow_0]

/- =========================================================================
   Bounds that charge the environment nothing
   ========================================================================= -/

/-- A list whose cores match the fixed argv, standard input and base file
    system and whose file contents all come from a given enumeration `B`
    weighs at most what `B` weighs — the environment coordinate is charged
    `1`, its whole declared mass, and nothing about the environment is
    assumed.

    This is the shape both remaining bounds take, and it is
    `envp_geo_weight_stdin_family_bound` on the other coordinate.  A task
    that knows nothing about the environments in its fire set gets exactly
    the bound `file_geometric` would have given it. -/
theorem file_envp_geo_weight_file_family_bound (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (B : List (List (BitVec 8))) (SB : Rat)
    (cs : List FinCore) (HB : qsum (fun d => geo_point p d.length) B ≤ SB)
    (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs →
      c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) ∧
        fs_file pth c.core_fs ∈ B) :
    qsum (file_envp_geo_weight p r q argv fs0 pth s) cs ≤ SB := by
  refine Rat.le_trans (qsum_core_incl_le (file_envp_geo_weight p r q argv fs0 pth s) cs
    (file_envp_product argv fs0 pth s
      (envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)) B)
    (file_envp_geo_weight_nonneg p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨Hmatch, Hfile⟩ := Hall c Hc
    have Hins : c.core_envp ∈ envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs) := by
      apply envp_enum_complete
      · exact cores_envp_depth_ge cs c Hc
      · intro e He
        exact cores_entry_depth_gt cs c e Hc He
    have Hprod := In_file_envp_product argv fs0 pth s _ B (c.core_envp)
      (fs_file pth c.core_fs) Hins Hfile
    rw [Hmatch]
    exact Hprod
  · rw [qsum_file_envp_product]
    refine Rat.le_trans (Qmult_le_compat_nonneg
      (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 (cores_envp_depth cs) (cores_entry_depth cs) [])
      HB
      (qsum_nonneg _ _ (fun x _ => envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 x))
      (qsum_nonneg _ _ (fun x _ => geo_point_nonneg p x.length Hp0 Hp1))) ?_
    show envp_factor r q [] * SB ≤ SB
    rw [envp_factor_nil]
    grind

/-- THE LENGTH SLICE: a list drawn from one file-length slice weighs at most
    `p_stop * (1 - p_stop) ^ n`, with no `1/256` left in it and nothing
    charged for the environment.  It is `file_geometric_slice_bound`'s
    constant exactly, and the hypothesis does NOT fix the environment: the
    records may carry any envp at all.

    WHAT IS NOT CLAIMED, and the difference from `file_geometric` is worth
    naming rather than leaving to be inferred from an absent lemma: this
    constant is not pinned as ATTAINED, and no sharpness lemma accompanies
    it.  A slice at a fixed file length still holds one core per
    ENVIRONMENT, of which there are infinitely many carrying positive
    weight whenever `r < 1`, so the counting argument does not run and
    nothing weaker is passed off as it. -/
theorem file_envp_geometric_slice_bound (p r q : Rat) (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (n : Nat) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      fin_core f = file_envp_core argv fs0 pth s f.fin_envp (fs_file pth f.fin_image_fs) ∧
        (fs_file pth f.fin_image_fs).length = n) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤ p * Qpow (1 - p) n := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤ p * Qpow (1 - p) n
  rw [core_sum_map_fin_core]
  refine Rat.le_trans (file_envp_geo_weight_file_family_bound p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (byte_lists n) (p * Qpow (1 - p) n) (List.map fin_core l)
    ?_ Hnd ?_) ?_
  · rw [byte_lists_sum]
    exact Rat.le_refl
  · intro c Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hc
    obtain ⟨Henv, Hlen⟩ := Hall f Hf
    refine ⟨?_, ?_⟩
    · rw [← hfc]
      exact Henv
    · rw [← hfc]
      show fs_file pth f.fin_image_fs ∈ byte_lists n
      rw [← Hlen]
      exact byte_lists_complete _
  · exact Rat.le_refl

/-- A list confined to input files of length at most `n` weighs at most
    `1 - (1 - p_stop) ^ (n + 1)` — the partial sum at its own horizon, and
    again the environment is charged nothing.  It MISSES THE TAIL, and the
    tail is what `file_envp_geometric_mass_not_attained` below is made of.

    THE ENVIRONMENT'S SHARE OF THIS CONSTANT IS LOOSE for `r < 1`, and the
    reason is the one given at `stdin_envp_geometric_bound_by_max_length`:
    the bound charges that coordinate its whole declared `1`, and a finite
    list collects all of it only when the environment mass sits on
    finitely many environments, which happens exactly at `r = 1`.  So an
    attainment lemma here would be false rather than missing. -/
theorem file_envp_geometric_bound_by_max_length (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (n : Nat) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hlen : ∀ f, f ∈ l → (fs_file pth f.fin_image_fs).length ≤ n) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l ≤ 1 - Qpow (1 - p) (n + 1) := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤ 1 - Qpow (1 - p) (n + 1)
  rw [core_sum_map_fin_core]
  rw [qsum_filter (file_envp_geo_weight p r q argv fs0 pth s)
    (matches_argv_file_fs argv fs0 pth s) _
    (fun c Hc => file_envp_geo_weight_mismatch p r q argv fs0 pth s c
      (matches_argv_file_fs_false argv fs0 pth s c Hc))]
  refine Rat.le_trans (file_envp_geo_weight_file_family_bound p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 (short_inputs (n + 1)) (1 - Qpow (1 - p) (n + 1))
    (List.filter (matches_argv_file_fs argv fs0 pth s) (List.map fin_core l))
    ?_ (List.Nodup.sublist List.filter_sublist Hnd) ?_) ?_
  · rw [short_inputs_sum, geo_prefix_sum_closed]
    exact Rat.le_refl
  · intro c Hc
    obtain ⟨Hin, Hm⟩ := List.mem_filter.mp Hc
    obtain ⟨f, Hf, hfc⟩ := List.mem_map.mp Hin
    refine ⟨matches_argv_file_fs_true argv fs0 pth s c Hm, ?_⟩
    apply short_inputs_complete
    have hle := Hlen f Hf
    rw [← hfc]
    show (fs_file pth f.fin_image_fs).length < n + 1
    omega
  · exact Rat.le_refl

/- =========================================================================... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= -/

/-- For `p_stop < 1` NO admissible list weighs the declared mass.  The proof
    is `file_geometric_mass_not_attained`'s, unchanged: the list's own
    longest input file is a horizon, and beyond it sits a positive tail the
    list does not collect.

    Only `p_stop < 1` is asked for.  The environment coordinate needs no
    hypothesis at all, for the reason
    `stdin_envp_geometric_mass_not_attained` needs none: the shortfall is
    already there on the file axis, so degenerate `r` or `q_e` can only
    make it larger. -/
theorem file_envp_geometric_mass_not_attained (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (Hlt : p < 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum (file_envp_geometric p r q argv fs0 pth s
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l <
      (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass := by
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) l < 1
  generalize hN : list_max (List.map (fun f => (fs_file pth f.fin_image_fs).length) l) = N
  have h1 : core_sum (file_envp_geo_weight p r q argv fs0 pth s) l ≤
      1 - Qpow (1 - p) (N + 1) :=
    file_envp_geometric_bound_by_max_length p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1
      N l Hnd (fun f Hf => by
        have hin : (fs_file pth f.fin_image_fs).length ∈
            List.map (fun g => (fs_file pth g.fin_image_fs).length) l :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - p) (N + 1) := Qpow_pos _ _ (by grind)
  grind

/-- The same fact under the name a reader looks for. -/
theorem file_envp_geometric_mass_supremum_not_maximum (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (Hlt : p < 1) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (file_envp_geometric p r q argv fs0 pth s
          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l =
        (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass) :=
  Rat.ne_of_lt (file_envp_geometric_mass_not_attained p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hlt l Hnd)

/- =========================================================================
   The lower certificate for `file_envp_geometric`
   ========================================================================= -/

/-- THE WITNESS FAMILY: over the fixed argv, base file system and standard
    input, one record per (environment, file contents) pair drawn from the
    two prefix families.  `envps_upto` and `short_inputs` are the
    envp-varying family's own enumerations, unchanged; only the embedding
    into cores is this family's, and the product is duplicate-free because
    both coordinates are. -/
def file_envp_geo_lower_witness (argv : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (M L k : Nat) : List FinProcInput :=
  List.map core_input
    (file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k))

theorem map_fin_core_file_envp_geo_lower_witness (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (M L k : Nat) :
    List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k) =
      file_envp_product argv fs0 pth s (envps_upto L M) (short_inputs k) := by
  unfold file_envp_geo_lower_witness
  exact map_fin_core_core_input _

theorem file_envp_geo_lower_witness_nodup (argv : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (M L k : Nat) :
    (List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k)).Nodup := by
  rw [map_fin_core_file_envp_geo_lower_witness]
  exact NoDup_file_envp_product argv fs0 pth s _ _
    (envps_upto_nodup L M) (short_inputs_nodup k)

/-- THE WITNESS, at each triple of depths: an admissible list weighing
    exactly the product of the two coordinates' partial sums.  No hypothesis
    beyond the constructor's own is needed here; all three strictnesses
    enter one lemma later, where the depths have to be CHOSEN to meet a
    target. -/
theorem file_envp_geometric_mass_lower_witness (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (M L k : Nat) :
    (List.map fin_core (file_envp_geo_lower_witness argv fs0 pth s M L k)).Nodup ∧
      core_sum (file_envp_geometric p r q argv fs0 pth s
          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        (file_envp_geo_lower_witness argv fs0 pth s M L k) =
        envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k) := by
  refine ⟨file_envp_geo_lower_witness_nodup argv fs0 pth s M L k, ?_⟩
  show core_sum (file_envp_geo_weight p r q argv fs0 pth s) _ = _
  rw [core_sum_map_fin_core, map_fin_core_file_envp_geo_lower_witness,
    qsum_file_envp_product, qsum_envp_point_envps_upto, short_inputs_sum,
    geo_prefix_sum_closed]

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass minus that margin.  With
    `file_envp_geometric_mass_upper` above it, the declared `1` is the
    least upper bound of the admissible partial sums — approached but, by
    `file_envp_geometric_mass_not_attained`, never met.

    Each strictness buys exactly one depth and the order matters, exactly
    as at `stdin_envp_geometric_mass_lower_certificate`.
    `envp_stdin_depths_above` chooses the three depths and
    `envp_stdin_margin_at_depths` does the arithmetic; both are stated over
    `envp_prefix_sum` and two powers with no distribution in sight, so this
    family consumes them unchanged. -/
theorem file_envp_geometric_mass_lower_certificate (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (eps : Rat)
    (Hppos : 0 < p) (Hrpos : 0 < r) (Hqpos : 0 < q) (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (file_envp_geometric p r q argv fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_mass - eps ≤
        core_sum (file_envp_geometric p r q argv fs0 pth s
          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight l := by
  obtain ⟨M, L, k, _HM, _HL, Hsum, _Hk⟩ :=
    envp_stdin_depths_above p r q eps 0 0 Hppos Hp1 Hrpos Hr1 Hqpos Hq1 Heps
  refine ⟨file_envp_geo_lower_witness argv fs0 pth s M L k,
    file_envp_geo_lower_witness_nodup argv fs0 pth s M L k, ?_⟩
  rw [(file_envp_geometric_mass_lower_witness p r q argv fs0 pth s
    Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 M L k).2]
  show (1 : Rat) - eps ≤
    envp_prefix_sum r (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - p) k)
  exact envp_stdin_margin_at_depths p r q eps M L k Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 Hsum

/- =========================================================================
   Non-vacuity: the environment carries mass here too
   ========================================================================= -/

/-- `file_geo_weight`'s envp instance, stated because the bite below needs
    it.  It is the same `file_geo_weight_mismatch` the argv instance goes
    through. -/
theorem file_geo_weight_off_envp_zero (p : Rat) (argv envp : List (List (BitVec 8)))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8)) (c : FinCore)
    (Hne : c.core_envp ≠ envp) : file_geo_weight p argv envp fs0 pth s c = 0 := by
  apply file_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_envp Heq)

theorem file_envp_geo_weight_off_argv_zero (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : c.core_argv ≠ argv) :
    file_envp_geo_weight p r q argv fs0 pth s c = 0 := by
  apply file_envp_geo_weight_mismatch
  intro Heq
  exact Hne (congrArg FinCore.core_argv Heq)

/-- A core over a NON-CANONICAL launch-time environment carrying the input
    file: one entry, the single byte `A`, and the empty file at
    `file_example_path`.  As at `envp_example_named` it is not claimed
    valid; it is the point of `FinInput.FinCore` at which the two file
    families disagree. -/
def file_envp_example_named : FinCore :=
  file_envp_core [] [] file_example_path [] [[BitVec.ofInt 8 65]] []

/-- THE BITE THIS FAMILY EXISTS FOR, both halves on ONE core.
    `file_geometric` over the empty environment weighs
    `file_envp_example_named` exactly zero — its envp is not the fixed one —
    while `file_envp_geometric` weighs it strictly positively.

    Under a distribution built from `file_geometric` alone, a fire set
    living at cores like this one lies in a NULL set, so a
    `Measure.weight_bound_T` claim about it is satisfied vacuously.  Under
    this family it is not. -/
theorem file_envp_geometric_envp_bites (p r q : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hppos : 0 < p) (Hplt : p < 1) (Hrpos : 0 < r) (Hrlt : r < 1)
    (Hqpos : 0 < q) (Hqlt : q < 1) :
    (file_geometric p [] [] [] file_example_path [] Hp0 Hp1).cd_weight
        file_envp_example_named = 0 ∧
      0 < (file_envp_geometric p r q [] [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight file_envp_example_named := by
  refine ⟨?_, ?_⟩
  · show file_geo_weight p [] [] [] file_example_path [] file_envp_example_named = 0
    apply file_geo_weight_off_envp_zero
    unfold file_envp_example_named
    rw [core_envp_file_envp_core]
    intro h
    cases h
  · show 0 < file_envp_geo_weight p r q [] [] file_example_path []
      file_envp_example_named
    unfold file_envp_example_named
    rw [file_envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q [[BitVec.ofInt 8 65]] Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 0 Hppos Hplt)

/-- ... and the family is still not constant: a core whose argv misses the
    fixed one weighs exactly zero.  Both halves are needed for the reason
    `stdin_envp_geometric_bites` needs both. -/
theorem file_envp_geometric_bites (p r q : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hppos : 0 < p) (Hplt : p < 1) (Hrpos : 0 < r) (Hrlt : r < 1)
    (Hqpos : 0 < q) (Hqlt : q < 1) :
    0 < (file_envp_geometric p r q [] [] file_example_path []
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight file_example_core ∧
      (file_envp_geometric p r q [] [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight geo_example_other = 0 := by
  refine ⟨?_, ?_⟩
  · show 0 < file_envp_geo_weight p r q [] [] file_example_path [] file_example_core
    rw [show file_example_core =
      file_envp_core [] [] file_example_path [] [] ([] : List (BitVec 8)) from rfl,
      file_envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q [] Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 0 Hppos Hplt)
  · show file_envp_geo_weight p r q [] [] file_example_path [] geo_example_other = 0
    apply file_envp_geo_weight_off_argv_zero
    show geo_example_other.core_argv ≠ []
    unfold geo_example_other
    intro h
    cases h

/- =========================================================================
   Non-vacuity: `List.NoDup` is load-bearing here too
   ========================================================================= -/

/-- The member of the family at `p_stop = r = q_e = 1`: stop immediately on
    every axis.  It is the point mass on the core with no environment and an
    empty input file, it is admitted by the constructor, and it is what
    makes the refutation below closed arithmetic instead of open terms. -/
def file_envp_point_cd : CoreDistribution :=
  file_envp_geometric 1 1 1 [] [] file_example_path []
    Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl Qle_0_1 Rat.le_refl

theorem file_envp_point_cd_weight_empty :
    file_envp_geo_weight 1 1 1 [] [] file_example_path []
      (fin_core file_empty_input) = 1 := by
  rw [show fin_core file_empty_input = file_example_core from fin_core_core_input _]
  show file_envp_geo_weight 1 1 1 [] [] file_example_path []
    (file_envp_core [] [] file_example_path [] [] ([] : List (BitVec 8))) = 1
  rw [file_envp_geo_weight_match]
  change envp_point 1 1 [] * geo_point 1 0 = 1
  unfold envp_point geo_point geo_mass
  rw [envp_factor_nil, Qpow_0]
  grind

/-- THE `List.NoDup` HYPOTHESIS IS LOAD-BEARING for this family's cylinder
    bound, and this is `file_geometric_bound_needs_nodup` transposed: offer
    the same core twice — two records, so the list is duplicate-free as a
    list of RECORDS, and both lie in the cylinder over the two empty
    prefixes — and the sum is `2` against a cylinder mass of `1`. -/
theorem file_envp_geometric_bound_needs_nodup :
    ¬ (List.map fin_core [file_empty_input, file_empty_input]).Nodup ∧
      (∀ f, f ∈ [file_empty_input, file_empty_input] →
        in_file_envp_cylinder [] [] file_example_path [] [] [] (fin_core f)) ∧
      ¬ (core_sum file_envp_point_cd.cd_weight [file_empty_input, file_empty_input] ≤
        file_envp_geometric_cylinder_mass 1 1 1 [] []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Hnd
    rw [List.map_cons, List.map_cons, List.map_nil, List.nodup_cons] at Hnd
    exact Hnd.1 (List.mem_cons_self ..)
  · intro f Hf
    have hfc : f = file_empty_input →
        fin_core f = file_envp_core [] [] file_example_path [] [] [] := by
      intro h
      rw [h]
      exact fin_core_core_input _
    rcases List.mem_cons.mp Hf with h | h
    · exact ⟨[], [], hfc h⟩
    · rcases List.mem_cons.mp h with h2 | h2
      · exact ⟨[], [], hfc h2⟩
      · exact absurd h2 (List.not_mem_nil)
  · intro Hle
    have hsum : core_sum file_envp_point_cd.cd_weight
        [file_empty_input, file_empty_input] = 2 := by
      show file_envp_geo_weight 1 1 1 [] [] file_example_path []
        (fin_core file_empty_input) +
        (file_envp_geo_weight 1 1 1 [] [] file_example_path []
          (fin_core file_empty_input) + 0) = 2
      rw [file_envp_point_cd_weight_empty]
      grind
    have hm : file_envp_geometric_cylinder_mass 1 1 1 ([] : List (List (BitVec 8)))
        ([] : List (BitVec 8)) = 1 := by
      unfold file_envp_geometric_cylinder_mass geo_mass
      rw [envp_factor_nil]
      change (1 : Rat) * Qpow ((1 - 1) * (1 / 256)) 0 = 1
      rw [Qpow_0]
      grind
    rw [hsum, hm] at Hle
    exact absurd Hle (by grind)

/- =========================================================================
   Family 2: the SIX degenerate members, each pinned
   ========================================================================= -/

/- EVERY ENDPOINT THE CONSTRUCTOR ADMITS, which is one more than the
   envp-varying family pins, because this family's file coordinate
   degenerates at `p_stop = 1` the way its envp coordinate degenerates at
   `q_e = 0` — there the `p_stop` axis is standard input and its collapse is
   `stdin_geometric`'s already-documented one, here it is the input file,
   the coordinate this family exists for.

   At `p_stop = 0` and at `r = 0` the weight vanishes identically — every
   list weighs nothing while the declared mass stays `1`, so the lower
   certificate is false there and its hypotheses are not inherited caution.
   At `q_e = 0`, at `q_e = 1`, at `r = 1` and at `p_stop = 1` the weight
   does NOT vanish, and those four are the interesting ones: the first three
   kill a whole class of non-empty environments, so the family collapses
   back towards `file_geometric` and is as blind to the launch-time
   environment as the family it extends; at the fourth every core whose
   INPUT FILE is non-empty weighs zero, so it goes blind to the coordinate
   both file families were built for.  Those four are the failure modes worth
   pinning, because they are the ones that would go unnoticed: the
   distribution is still non-zero, still sums correctly, still declares mass
   `1` honestly, and still measures nothing about the axis in question. -/

theorem file_envp_geo_weight_zero_at_zero_p (r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_envp_geo_weight 0 r q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · next _ => unfold geo_point; grind
  · rfl

theorem file_envp_geo_weight_zero_at_zero_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_envp_geo_weight p 0 q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · next _ => unfold envp_point; grind
  · rfl

theorem file_envp_geo_weight_zero_at_zero_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : c.core_envp ≠ []) :
    file_envp_geo_weight p r 0 argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · next _ =>
    rcases h : c.core_envp with _ | ⟨e, es⟩
    · exact absurd h Hne
    · unfold envp_point envp_factor geo_point
      grind
  · rfl

theorem file_envp_geo_weight_collapses_at_one_p (r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (Hne : fs_file pth c.core_fs ≠ []) :
    file_envp_geo_weight 1 r q argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · next _ =>
    rcases h : fs_file pth c.core_fs with _ | ⟨b, d⟩
    · exact absurd h Hne
    · unfold geo_point geo_mass
      rw [List.length_cons, Qpow_succ]
      grind
  · rfl

/-- `r = 1` is stated as a COLLAPSE rather than as a blindness, which is the
    sharper form: at `r = 1` this family IS `file_geometric` over the EMPTY
    launch-time environment, weight for weight and at every core, including
    the ones both weigh zero.  `r < 1` is therefore genuinely asked for, by
    `envp_point_pos` and through it by `file_envp_geometric_envp_bites` —
    the very lemma that says this family improves on the one it extends. -/
theorem file_envp_geo_weight_collapses_at_one_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) :
    file_envp_geo_weight p 1 q argv fs0 pth s c =
      file_geo_weight p argv [] fs0 pth s c := by
  unfold file_envp_geo_weight file_geo_weight file_envp_core
  by_cases Hm : c = file_core argv c.core_envp fs0 pth s (fs_file pth c.core_fs)
  · by_cases He : c = file_core argv [] fs0 pth s (fs_file pth c.core_fs)
    · have Henv : c.core_envp = [] := by
        have h := congrArg FinCore.core_envp He
        simpa [file_core] using h
      rw [ite_eq_left Hm, ite_eq_left He, Henv]
      unfold envp_point envp_factor
      grind
    · rw [ite_eq_left Hm, ite_eq_right He]
      rcases h : c.core_envp with _ | ⟨e, es⟩
      · rw [h] at Hm
        exact absurd Hm He
      · unfold envp_point envp_factor
        grind
  · by_cases He : c = file_core argv [] fs0 pth s (fs_file pth c.core_fs)
    · exfalso
      apply Hm
      have Henv : c.core_envp = [] := by
        have h := congrArg FinCore.core_envp He
        simpa [file_core] using h
      rw [Henv]
      exact He
    · rw [ite_eq_right Hm, ite_eq_right He]

theorem file_envp_geometric_collapses_at_one_r (p q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (c : FinCore) :
    (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1).cd_weight c =
      (file_geometric p argv [] fs0 pth s Hp0 Hp1).cd_weight c :=
  file_envp_geo_weight_collapses_at_one_r p q argv fs0 pth s c

/-- ... and the three blindnesses, in the shape
    `stdin_envp_geometric_envp_needs_positive_q` states its own.  Both forms
    are exported everywhere both exist: a reader asking "what goes wrong at
    this parameter" wants the blindness, and a reader asking "what does the
    family become" wants the collapse. -/
theorem file_envp_geometric_envp_needs_r_below_one (p q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (c : FinCore) (Hne : c.core_envp ≠ []) :
    (file_envp_geometric p 1 q argv fs0 pth s Hp0 Hp1 Qle_0_1 Rat.le_refl Hq0 Hq1).cd_weight c = 0 := by
  rw [file_envp_geometric_collapses_at_one_r]
  show file_geo_weight p argv [] fs0 pth s c = 0
  exact file_geo_weight_off_envp_zero p argv [] fs0 pth s c Hne

theorem file_envp_geometric_envp_needs_positive_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (c : FinCore) (Hne : c.core_envp ≠ []) :
    (file_envp_geometric p r 0 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
      Rat.le_refl Qle_0_1).cd_weight c = 0 := by
  show file_envp_geo_weight p r 0 argv fs0 pth s c = 0
  exact file_envp_geo_weight_zero_at_zero_q p r argv fs0 pth s c Hne

/-- `q_e = 1` fails the way `envp_geo_weight_zero_at_one_q` fails for the
    family this one extends: `geo_point 1 m` is zero for every `m >= 1`, so
    an environment holding ANY non-empty entry weighs nothing while
    environments of empty entries keep their weight.  Since a real
    environment entry is a `NAME=value` string, the family is blind to every
    environment a program will actually see, and it has not gone quiet.

    The hypothesis names a non-empty ENTRY and not a non-empty ENVIRONMENT —
    `[[]]` weighs a positive amount at `q_e = 1` — so this is not
    `file_envp_geometric_envp_needs_positive_q` with `0` replaced by `1`. -/
theorem file_envp_geo_weight_zero_at_one_q (p r : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore) (e : List (BitVec 8))
    (Hin : e ∈ c.core_envp) (Hne : e ≠ []) :
    file_envp_geo_weight p r 1 argv fs0 pth s c = 0 := by
  unfold file_envp_geo_weight
  split
  · next _ =>
    unfold envp_point
    rw [envp_factor_zero_at_one_q r c.core_envp e Hin Hne]
    grind
  · rfl

theorem file_envp_geometric_envp_needs_q_below_one (p r : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (c : FinCore) (e : List (BitVec 8)) (Hin : e ∈ c.core_envp) (Hne : e ≠ []) :
    (file_envp_geometric p r 1 argv fs0 pth s Hp0 Hp1 Hr0 Hr1
      Qle_0_1 Rat.le_refl).cd_weight c = 0 := by
  show file_envp_geo_weight p r 1 argv fs0 pth s c = 0
  exact file_envp_geo_weight_zero_at_one_q p r argv fs0 pth s c e Hin Hne

/-- ... and the hypothesis cannot be weakened here either, at the same two
    environments and the same `1 / 8`. -/
theorem file_envp_geo_weight_at_one_q_needs_a_non_empty_entry :
    file_envp_geo_weight (1 / 2) (1 / 5) 1 [] [] file_example_path []
        file_envp_example_named = 0 ∧
      0 < file_envp_geo_weight (1 / 2) (1 / 5) 1 [] [] file_example_path []
        (file_envp_core [] [] file_example_path [] [[]] []) := by
  refine ⟨?_, ?_⟩
  · apply file_envp_geo_weight_zero_at_one_q _ _ _ _ _ _ _ [BitVec.ofInt 8 65]
    · unfold file_envp_example_named
      rw [core_envp_file_envp_core]
      exact List.mem_cons_self ..
    · intro h
      cases h
  · rw [file_envp_geo_weight_match]
    have h1 : envp_point (1 / 5) 1 [[]] = 1 / 5 * (1 - 1 / 5) := by
      unfold envp_point
      change (1 : Rat) / 5 * ((1 - 1 / 5) * geo_point 1 0 * envp_factor (1 / 5) 1 []) =
        1 / 5 * (1 - 1 / 5)
      rw [geo_point_at_zero, envp_factor_nil]
      grind
    rw [h1]
    change 0 < (1 / 5 * (1 - 1 / 5)) * geo_point (1 / 2) 0
    rw [geo_point_at_zero]
    exact Rat.mul_pos (Rat.mul_pos (Qpos_one_div 5 (by decide)) (by grind))
      (Qpos_one_div 2 (by decide))

theorem file_envp_geometric_needs_p_below_one (r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (c : FinCore) (Hne : fs_file pth c.core_fs ≠ []) :
    (file_envp_geometric 1 r q argv fs0 pth s Qle_0_1 Rat.le_refl Hr0 Hr1
      Hq0 Hq1).cd_weight c = 0 := by
  show file_envp_geo_weight 1 r q argv fs0 pth s c = 0
  exact file_envp_geo_weight_collapses_at_one_p r q argv fs0 pth s c Hne

/-- THE STRICTNESS AT `p_stop` IS LOAD-BEARING for the lower certificate,
    pinned the way this file pins every other hypothesis it asks for: at
    `p_stop = 0` EVERY admissible list weighs zero — not merely the witness
    family, which is why the first conjunct quantifies over all of them —
    and the declared mass is still `1`, so no list comes within `1 / 2` of
    it.  `file_envp_geometric_mass_upper` remains true here, and that
    asymmetry is the honest content of the pair: an upper bound survives
    degeneracy, a lower one does not. -/
theorem file_envp_geometric_mass_lower_needs_positive
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    (∀ l : List FinProcInput,
      core_sum (file_envp_geometric 0 r q argv fs0 pth s
        Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1).cd_weight l = 0) ∧
      ¬ ((file_envp_geometric 0 r q argv fs0 pth s
        Rat.le_refl Qle_0_1 Hr0 Hr1 Hq0 Hq1).cd_mass - 1 / 2 ≤ 0) := by
  refine ⟨?_, ?_⟩
  · intro l
    apply core_sum_zero_weight
    intro c
    show file_envp_geo_weight 0 r q argv fs0 pth s c = 0
    exact file_envp_geo_weight_zero_at_zero_p r q argv fs0 pth s c
  · show ¬ ((1 : Rat) - 1 / 2 ≤ 0)
    grind

/- =========================================================================
   The argv/path coupling: the one obligation a caller can get silently wrong
   ========================================================================= -/

/- BOTH FILE FAMILIES TAKE `argv` AND `pth` AS INDEPENDENT PARAMETERS, and a
   typical driver passes the varied file's path AS an argument.  So a task
   must pass the same path in both places, and nothing in the constructions
   makes it.  Pass two different ones and the distribution varies a file the
   program never opens: it still declares mass `1`, still satisfies both
   halves of the certificate pair, and still puts distinct positive weights
   on distinct file contents — while every core it weighs is one the program
   cannot tell apart from the others, which is exactly the all-or-nothing
   collapse these families exist to remove.

   This section closes that three ways, and none of them is a comment.
   `argv_names_path` NAMES the obligation.  `file_geometric_argv1` and its
   siblings make the mismatch UNREPRESENTABLE for the common shape, by
   deriving argv from the path rather than taking both.  And the blindness
   lemmas plus `file_geometric_needs_argv_to_name_the_path` PIN the collapse,
   so a misconfigured instance is visibly different from a well-configured
   one rather than merely differently intended.

   WHAT `argv_names_path` IS AND IS NOT.  It is the syntactic proxy: the
   path occurs somewhere in the fixed argv.  The real obligation is that the
   program OPENS the file at `pth`, which is a claim about the program.  So
   this is neither necessary nor sufficient for the real thing; it is the
   part a library can check, and it catches the one mistake a task author
   actually makes, which is passing two different paths. -/

def argv_names_path (argv : List (List (BitVec 8))) (pth : Fs.path) : Prop :=
  pth ∈ argv

/-- The argv of the common driver shape: a program name, then the input
    file's path.  `file_geometric_argv1` below is the constructor that takes
    this shape rather than an arbitrary argv, and it is offered ALONGSIDE
    the general constructor rather than replacing it because not every
    program takes its path at argv[1]. -/
def path_argv (prog : List (BitVec 8)) (pth : Fs.path) : List (List (BitVec 8)) :=
  [prog, pth]

theorem path_argv_names_path (prog : List (BitVec 8)) (pth : Fs.path) :
    argv_names_path (path_argv prog pth) pth :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- The two derived constructors.  `pth` is passed ONCE and reaches both
    slots, so the two cannot disagree: the misconfiguration is not a thing a
    caller of these can express. -/
def file_geometric_argv1 (p : Rat) (prog : List (BitVec 8))
    (envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) : CoreDistribution :=
  file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1

def file_envp_geometric_argv1 (p r q : Rat) (prog : List (BitVec 8))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) : CoreDistribution :=
  file_envp_geometric p r q (path_argv prog pth) fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1

/-- ... and they discharge the obligation by construction, which is the whole
    content of offering them: a task that uses one owes nothing. -/
theorem file_geometric_argv1_names_path (p : Rat) (prog : List (BitVec 8))
    (envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth ∧
      file_geometric_argv1 p prog envp fs0 pth s Hp0 Hp1 =
        file_geometric p (path_argv prog pth) envp fs0 pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

theorem file_envp_geometric_argv1_names_path (p r q : Rat) (prog : List (BitVec 8))
    (fs0 : Fs.Fs) (pth : Fs.path) (s : List (BitVec 8))
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    argv_names_path (path_argv prog pth) pth ∧
      file_envp_geometric_argv1 p r q prog fs0 pth s Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 =
        file_envp_geometric p r q (path_argv prog pth) fs0 pth s
          Hp0 Hp1 Hr0 Hr1 Hq0 Hq1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-- The header-conditioned family's coupled constructor, the same shape:
    `pth` is passed once and reaches both slots. -/
def file_geometric_prefix_argv1 (hdr : List (BitVec 8)) (p : Rat)
    (prog : List (BitVec 8)) (envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    CoreDistribution :=
  file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1

theorem file_geometric_prefix_argv1_names_path (hdr : List (BitVec 8)) (p : Rat)
    (prog : List (BitVec 8)) (envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth ∧
      file_geometric_prefix_argv1 hdr p prog envp fs0 pth s Hp0 Hp1 =
        file_geometric_prefix hdr p (path_argv prog pth) envp fs0 pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/-- The alphabet-restricted family's coupled constructor, the same shape. -/
def file_geometric_prefix_over_argv1 (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (prog : List (BitVec 8)) (envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    CoreDistribution :=
  file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp fs0
    pth s Hp0 Hp1

theorem file_geometric_prefix_over_argv1_names_path (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (prog : List (BitVec 8)) (envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) :
    argv_names_path (path_argv prog pth) pth ∧
      file_geometric_prefix_over_argv1 alpha Hnd Hne hdr p prog envp fs0 pth s
          Hp0 Hp1 =
        file_geometric_prefix_over alpha Hnd Hne hdr p (path_argv prog pth) envp
          fs0 pth s Hp0 Hp1 :=
  ⟨path_argv_names_path prog pth, rfl⟩

/- =========================================================================... and what goes wrong when the coupling is violated
   ========================================================================= -/

/-- `Fs.fs_set` TOUCHES ONE KEY AND NO OTHER, with no hypothesis on the file
    system — the companion of `fs_lookup_set`, and the fact the blindness
    below is made of.  The three-way case split is `fs_lookup_set`'s, read at
    a query key that is not the one being set: the inserted or replaced entry
    is skipped, and what is left is the original lookup. -/
theorem fs_lookup_set_other (fs : Fs.Fs) (pth : Fs.path) (d : List (BitVec 8))
    (pth' : Fs.path) (Hne : pth' ≠ pth) :
    Fs.fs_lookup (Fs.fs_set fs pth d) pth' = Fs.fs_lookup fs pth' := by
  induction fs with
  | nil =>
    show (if Fs.path_eqb pth' pth then some d else none) = none
    rw [ite_eq_right (fun h => Hne ((Fs.path_eqb_eq pth' pth).mp h))]
  | cons hd r ih =>
    obtain ⟨q, e⟩ := hd
    by_cases hlt : Fs.path_ltb pth q = true
    · have hs : Fs.fs_set ((q, e) :: r) pth d = (pth, d) :: (q, e) :: r := by
        simp [Fs.fs_set, hlt]
      rw [hs]
      show (if Fs.path_eqb pth' pth then some d
          else Fs.fs_lookup ((q, e) :: r) pth') = Fs.fs_lookup ((q, e) :: r) pth'
      rw [ite_eq_right (fun h => Hne ((Fs.path_eqb_eq pth' pth).mp h))]
    · by_cases heq : Fs.path_eqb pth q = true
      · have hs : Fs.fs_set ((q, e) :: r) pth d = (pth, d) :: r := by
          simp [Fs.fs_set, hlt, heq]
        have hq : pth = q := (Fs.path_eqb_eq pth q).mp heq
        rw [hs, hq]
        show (if Fs.path_eqb pth' q then some d else Fs.fs_lookup r pth') =
          (if Fs.path_eqb pth' q then some e else Fs.fs_lookup r pth')
        have hne' : ¬ (Fs.path_eqb pth' q = true) := fun h =>
          Hne (by rw [hq]; exact (Fs.path_eqb_eq pth' q).mp h)
        by_cases hq' : Fs.path_eqb pth' q = true
        · exact absurd hq' hne'
        · simp only [ite_eq_right hq']
      · have hs : Fs.fs_set ((q, e) :: r) pth d = (q, e) :: Fs.fs_set r pth d := by
          simp [Fs.fs_set, hlt, heq]
        rw [hs]
        show (if Fs.path_eqb pth' q then some e
            else Fs.fs_lookup (Fs.fs_set r pth d) pth') =
          (if Fs.path_eqb pth' q then some e else Fs.fs_lookup r pth')
        rw [ih]

theorem fs_file_set_other (fs0 : Fs.Fs) (pth : Fs.path) (d : List (BitVec 8))
    (pth' : Fs.path) (Hne : pth' ≠ pth) :
    fs_file pth' (Fs.fs_set fs0 pth d) = fs_file pth' fs0 := by
  unfold fs_file
  rw [fs_lookup_set_other fs0 pth d pth' Hne]

theorem fs_file_file_core_other (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (pth : Fs.path) (s d : List (BitVec 8)) (pth' : Fs.path) (Hne : pth' ≠ pth) :
    fs_file pth' (file_core argv envp fs0 pth s d).core_fs = fs_file pth' fs0 := by
  show fs_file pth' (Fs.fs_set fs0 pth d) = fs_file pth' fs0
  exact fs_file_set_other fs0 pth d pth' Hne

/-- A core the weight does not zero IS the template with its own coordinates
    plugged in — the `decide` read backwards, so that the blindness lemmas
    can talk about "every core this family weighs" and not about the
    membership test. -/
theorem file_geo_weight_positive_matches (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_geo_weight p argv envp fs0 pth s c) :
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  unfold file_geo_weight at Hpos
  by_cases h : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  · exact h
  · rw [ite_eq_right h] at Hpos
    exact absurd Hpos (by grind)

theorem file_envp_geo_weight_positive_matches (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_envp_geo_weight p r q argv fs0 pth s c) :
    c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs) := by
  unfold file_envp_geo_weight at Hpos
  by_cases h : c = file_envp_core argv fs0 pth s c.core_envp (fs_file pth c.core_fs)
  · exact h
  · rw [ite_eq_right h] at Hpos
    exact absurd Hpos (by grind)

/-- THE COLLAPSE, stated once per family: at EVERY path other than the one
    it varies, every core the family weighs holds exactly the base file
    system's contents.

    Read it against the obligation.  If `argv` names some `pth'` other than
    `pth`, then the file the program is told to open is the same in every
    weighted core, so every weighted core induces the same program behavior,
    so `Classifier.good_input` and `Classifier.agree` hold at all of them or
    at none — which is the all-or-nothing reject set and the `b ∈ {0, 1}`
    collapse, arrived at from the other direction.  The family is not broken
    at such a configuration; it is measuring a file nobody reads. -/
theorem file_geo_weight_blind_off_path (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (pth' : Fs.path) (c : FinCore)
    (Hne : pth' ≠ pth) (Hpos : 0 < file_geo_weight p argv envp fs0 pth s c) :
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  have Heq := file_geo_weight_positive_matches p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

theorem file_envp_geo_weight_blind_off_path (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (pth' : Fs.path) (c : FinCore)
    (Hne : pth' ≠ pth) (Hpos : 0 < file_envp_geo_weight p r q argv fs0 pth s c) :
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  have Heq := file_envp_geo_weight_positive_matches p r q argv fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv (c.core_envp) fs0 pth s (fs_file pth c.core_fs)
    pth' Hne

/-- ... and so ANY TWO weighted cores agree off `pth`, which is the form a
    reader wants: whatever the family varies, it is invisible at every other
    path. -/
theorem file_geometric_blind_off_path (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (pth' : Fs.path)
    (c1 c2 : FinCore)
    (Hne : pth' ≠ pth)
    (H1 : 0 < (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight c1)
    (H2 : 0 < (file_geometric p argv envp fs0 pth s Hp0 Hp1).cd_weight c2) :
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  show fs_file pth' c1.core_fs = fs_file pth' c2.core_fs
  rw [file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c1 Hne H1,
    file_geo_weight_blind_off_path p argv envp fs0 pth s pth' c2 Hne H2]

theorem file_envp_geometric_blind_off_path (p r q : Rat)
    (argv : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (pth' : Fs.path) (c1 c2 : FinCore)
    (Hne : pth' ≠ pth)
    (H1 : 0 < (file_envp_geometric p r q argv fs0 pth s
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight c1)
    (H2 : 0 < (file_envp_geometric p r q argv fs0 pth s
      Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight c2) :
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  show fs_file pth' c1.core_fs = fs_file pth' c2.core_fs
  rw [file_envp_geo_weight_blind_off_path p r q argv fs0 pth s pth' c1 Hne H1,
    file_envp_geo_weight_blind_off_path p r q argv fs0 pth s pth' c2 Hne H2]

/- =========================================================================
   The misconfigured instance, exhibited
   ========================================================================= -/

/-- A program name and a second path, both distinct from
    `file_example_path` and distinguished from it by LENGTH so that the
    inequalities below are three lines of `length` and not a fact about
    bytes.  As everywhere in this file these are points of `Fs.path`, not
    claims that anything is valid. -/
def file_example_prog : List (BitVec 8) :=
  [BitVec.ofInt 8 105, BitVec.ofInt 8 105, BitVec.ofInt 8 105]

def file_other_path : Fs.path := [BitVec.ofInt 8 105, BitVec.ofInt 8 105]

theorem file_other_path_ne : file_other_path ≠ file_example_path := by
  intro H
  have h := congrArg List.length H
  rw [show file_other_path.length = 2 from rfl,
    show file_example_path.length = 1 from rfl] at h
  exact absurd h (by decide)

/-- The misconfiguration: an argv that names `file_other_path` while the
    family varies `file_example_path`. -/
def file_misconfigured_argv : List (List (BitVec 8)) :=
  [file_example_prog, file_other_path]

theorem file_misconfigured_argv_not_names :
    ¬ argv_names_path file_misconfigured_argv file_example_path := by
  intro Hin
  unfold argv_names_path file_misconfigured_argv at Hin
  rcases List.mem_cons.mp Hin with h | h
  · have hl := congrArg List.length h
    rw [show file_example_prog.length = 3 from rfl,
      show file_example_path.length = 1 from rfl] at hl
    exact absurd hl (by decide)
  · rcases List.mem_cons.mp h with h2 | h2
    · exact file_other_path_ne h2.symm
    · exact absurd h2 (List.not_mem_nil)

/-- THE HAZARD, EXHIBITED, so that a misconfigured instance is visibly
    different from a well-configured one rather than merely differently
    intended.  Four conjuncts, and each is needed.

    The first says the configuration really is bad: the varied path occurs
    nowhere in the fixed argv, so `argv_names_path` fails.  The second and
    third say the distribution nevertheless looks entirely healthy — two
    cores with DIFFERENT file contents, both of positive weight; nothing
    about it is degenerate in any sense this file otherwise pins, and it
    declares mass `1` and satisfies both certificates exactly as a
    well-configured instance does.  The fourth is the collapse: at the path
    argv actually names, those two cores hold the same bytes, so a program
    reading its argument cannot tell them apart and the whole variation is
    invisible to it. -/
theorem file_geometric_needs_argv_to_name_the_path (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1)
    (Hpos : 0 < p) (Hlt : p < 1) :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric p file_misconfigured_argv [] [] file_example_path []
        Hp0 Hp1).cd_weight
        (file_core file_misconfigured_argv [] [] file_example_path [] []) ∧
      0 < (file_geometric p file_misconfigured_argv [] [] file_example_path []
        Hp0 Hp1).cd_weight
        (file_core file_misconfigured_argv [] [] file_example_path [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_core file_misconfigured_argv [] [] file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_core file_misconfigured_argv [] [] file_example_path []
            [BitVec.ofInt 8 65]).core_fs := by
  refine ⟨file_misconfigured_argv_not_names, ?_, ?_, ?_⟩
  · show 0 < file_geo_weight p file_misconfigured_argv [] [] file_example_path []
      (file_core file_misconfigured_argv [] [] file_example_path [] [])
    rw [file_geo_weight_match]
    exact geo_point_pos p 0 Hpos Hlt
  · show 0 < file_geo_weight p file_misconfigured_argv [] [] file_example_path []
      (file_core file_misconfigured_argv [] [] file_example_path [] [BitVec.ofInt 8 65])
    rw [file_geo_weight_match]
    exact geo_point_pos p 1 Hpos Hlt
  · rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] []
        file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne]

/-- The same hazard for the envp-varying file family, at the same
    misconfiguration and with the envp coordinate left where it is: two
    weighted cores over one environment, differing in the input file,
    agreeing at the path argv names. -/
theorem file_envp_geometric_needs_argv_to_name_the_path (p r q : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1)
    (Hpos : 0 < p) (Hlt : p < 1) (Hrpos : 0 < r) (Hrlt : r < 1)
    (Hqpos : 0 < q) (Hqlt : q < 1) :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_envp_geometric p r q file_misconfigured_argv [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        (file_envp_core file_misconfigured_argv [] file_example_path [] [] []) ∧
      0 < (file_envp_geometric p r q file_misconfigured_argv [] file_example_path []
        Hp0 Hp1 Hr0 Hr1 Hq0 Hq1).cd_weight
        (file_envp_core file_misconfigured_argv [] file_example_path [] []
          [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_envp_core file_misconfigured_argv [] file_example_path [] [] []).core_fs =
        fs_file file_other_path
          (file_envp_core file_misconfigured_argv [] file_example_path [] []
            [BitVec.ofInt 8 65]).core_fs := by
  refine ⟨file_misconfigured_argv_not_names, ?_, ?_, ?_⟩
  · show 0 < file_envp_geo_weight p r q file_misconfigured_argv [] file_example_path []
      (file_envp_core file_misconfigured_argv [] file_example_path [] [] [])
    rw [file_envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q [] Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 0 Hpos Hlt)
  · show 0 < file_envp_geo_weight p r q file_misconfigured_argv [] file_example_path []
      (file_envp_core file_misconfigured_argv [] file_example_path [] []
        [BitVec.ofInt 8 65])
    rw [file_envp_geo_weight_match]
    exact Rat.mul_pos (envp_point_pos r q [] Hrpos Hrlt Hqpos Hqlt)
      (geo_point_pos p 1 Hpos Hlt)
  · unfold file_envp_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] []
        file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne]

/- =========================================================================
   The same coupling, for the header-conditioned family
   ========================================================================= -/

/-- A core the weight does not zero is the whole-file template at its own
    contents — and, one step further, the SHIFTED template at some
    payload. -/
theorem file_prefix_geo_weight_positive_matches (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c) :
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  unfold file_prefix_geo_weight at Hpos
  by_cases h : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  · exact h
  · rw [ite_eq_right h] at Hpos
    exact absurd Hpos (by grind)

theorem file_prefix_geo_weight_positive_extends (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c) :
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t := by
  have Heq := file_prefix_geo_weight_positive_matches hdr p argv envp fs0 pth s c Hpos
  obtain ⟨t, Ht⟩ : ∃ t, strip_prefix hdr (fs_file pth c.core_fs) = some t := by
    rcases hs : strip_prefix hdr (fs_file pth c.core_fs) with _ | t
    · exfalso
      have h0 := file_prefix_geo_weight_off_header hdr p argv envp fs0 pth s c hs
      rw [h0] at Hpos
      exact absurd Hpos (by grind)
    · exact ⟨t, rfl⟩
  refine ⟨t, ?_⟩
  rw [Heq]
  show file_core argv envp fs0 pth s (fs_file pth c.core_fs) =
    file_prefix_core hdr argv envp fs0 pth s t
  rw [strip_prefix_Some hdr _ t Ht]
  rfl

theorem file_prefix_geo_weight_blind_off_path (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (pth' : Fs.path) (c : FinCore)
    (Hne : pth' ≠ pth) (Hpos : 0 < file_prefix_geo_weight hdr p argv envp fs0 pth s c) :
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  have Heq := file_prefix_geo_weight_positive_matches hdr p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

theorem file_geometric_prefix_blind_off_path (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (pth' : Fs.path)
    (c1 c2 : FinCore) (Hne : pth' ≠ pth)
    (H1 : 0 < (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight c1)
    (H2 : 0 < (file_geometric_prefix hdr p argv envp fs0 pth s Hp0 Hp1).cd_weight c2) :
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  show fs_file pth' c1.core_fs = fs_file pth' c2.core_fs
  rw [file_prefix_geo_weight_blind_off_path hdr p argv envp fs0 pth s pth' c1 Hne H1,
    file_prefix_geo_weight_blind_off_path hdr p argv envp fs0 pth s pth' c2 Hne H2]

/-- The misconfigured instance for this family, at the same
    misconfiguration and behind the one-byte example header: two weighted
    cores whose payloads differ, agreeing at the path argv names. -/
theorem file_geometric_prefix_needs_argv_to_name_the_path (p : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hpos : 0 < p) (Hlt : p < 1) :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric_prefix file_example_hdr p file_misconfigured_argv [] []
        file_example_path [] Hp0 Hp1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []) ∧
      0 < (file_geometric_prefix file_example_hdr p file_misconfigured_argv [] []
        file_example_path [] Hp0 Hp1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] [BitVec.ofInt 8 65]).core_fs := by
  refine ⟨file_misconfigured_argv_not_names, ?_, ?_, ?_⟩
  · show 0 < file_prefix_geo_weight file_example_hdr p file_misconfigured_argv [] []
      file_example_path [] (file_prefix_core file_example_hdr file_misconfigured_argv
        [] [] file_example_path [] [])
    rw [file_prefix_geo_weight_match]
    exact geo_point_pos p 0 Hpos Hlt
  · show 0 < file_prefix_geo_weight file_example_hdr p file_misconfigured_argv [] []
      file_example_path [] (file_prefix_core file_example_hdr file_misconfigured_argv
        [] [] file_example_path [] [BitVec.ofInt 8 65])
    rw [file_prefix_geo_weight_match]
    exact geo_point_pos p 1 Hpos Hlt
  · unfold file_prefix_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne]

/- =========================================================================
   The same coupling, for the alphabet-restricted family
   ========================================================================= -/

theorem file_prefix_over_geo_weight_positive_matches (alpha hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c) :
    c = file_core argv envp fs0 pth s (fs_file pth c.core_fs) := by
  unfold file_prefix_over_geo_weight at Hpos
  by_cases h : c = file_core argv envp fs0 pth s (fs_file pth c.core_fs)
  · exact h
  · rw [ite_eq_right h] at Hpos
    exact absurd Hpos (by grind)

theorem file_prefix_over_geo_weight_positive_extends (alpha hdr : List (BitVec 8))
    (p : Rat) (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (c : FinCore)
    (Hpos : 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c) :
    ∃ t, c = file_prefix_core hdr argv envp fs0 pth s t ∧ alpha_only alpha t = true := by
  have Heq := file_prefix_over_geo_weight_positive_matches alpha hdr p argv envp fs0 pth s c Hpos
  obtain ⟨t, Ht⟩ : ∃ t, strip_prefix hdr (fs_file pth c.core_fs) = some t := by
    rcases hs : strip_prefix hdr (fs_file pth c.core_fs) with _ | t
    · exfalso
      have h0 := file_prefix_over_geo_weight_off_header alpha hdr p argv envp fs0 pth s c hs
      rw [h0] at Hpos
      exact absurd Hpos (by grind)
    · exact ⟨t, rfl⟩
  have hc : c = file_prefix_core hdr argv envp fs0 pth s t := by
    rw [Heq]
    show file_core argv envp fs0 pth s (fs_file pth c.core_fs) =
      file_prefix_core hdr argv envp fs0 pth s t
    rw [strip_prefix_Some hdr _ t Ht]
    rfl
  have Ha : alpha_only alpha t = true := by
    cases ha : alpha_only alpha t with
    | true => rfl
    | false =>
      exfalso
      have h0 := file_prefix_over_geo_weight_off_alphabet alpha hdr p argv envp fs0 pth s t ha
      rw [hc, h0] at Hpos
      exact absurd Hpos (by grind)
  exact ⟨t, hc, Ha⟩

theorem file_prefix_over_geo_weight_blind_off_path (alpha hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (pth' : Fs.path) (c : FinCore) (Hne : pth' ≠ pth)
    (Hpos : 0 < file_prefix_over_geo_weight alpha hdr p argv envp fs0 pth s c) :
    fs_file pth' c.core_fs = fs_file pth' fs0 := by
  have Heq := file_prefix_over_geo_weight_positive_matches alpha hdr p argv envp fs0 pth s c Hpos
  rw [Heq]
  exact fs_file_file_core_other argv envp fs0 pth s (fs_file pth c.core_fs) pth' Hne

theorem file_geometric_prefix_over_blind_off_path (alpha : List (BitVec 8))
    (Hnd : alpha.Nodup) (Hne : alpha ≠ []) (hdr : List (BitVec 8)) (p : Rat)
    (argv envp : List (List (BitVec 8))) (fs0 : Fs.Fs) (pth : Fs.path)
    (s : List (BitVec 8)) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (pth' : Fs.path)
    (c1 c2 : FinCore) (Hne' : pth' ≠ pth)
    (H1 : 0 < (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1).cd_weight c1)
    (H2 : 0 < (file_geometric_prefix_over alpha Hnd Hne hdr p argv envp fs0 pth s
      Hp0 Hp1).cd_weight c2) :
    fs_file pth' c1.core_fs = fs_file pth' c2.core_fs := by
  show fs_file pth' c1.core_fs = fs_file pth' c2.core_fs
  rw [file_prefix_over_geo_weight_blind_off_path alpha hdr p argv envp fs0 pth s pth' c1
      Hne' H1,
    file_prefix_over_geo_weight_blind_off_path alpha hdr p argv envp fs0 pth s pth' c2
      Hne' H2]

/-- The misconfigured instance for this family, over the one-byte example
    alphabet: the payloads are the empty one and the alphabet's own byte. -/
theorem file_geometric_prefix_over_needs_argv_to_name_the_path (p : Rat)
    (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (Hpos : 0 < p) (Hlt : p < 1) :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p file_misconfigured_argv [] []
        file_example_path [] Hp0 Hp1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []) ∧
      0 < (file_geometric_prefix_over file_example_alpha file_example_alpha_nodup
        file_example_alpha_ne file_example_hdr p file_misconfigured_argv [] []
        file_example_path [] Hp0 Hp1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] [BitVec.ofInt 8 65]).core_fs := by
  refine ⟨file_misconfigured_argv_not_names, ?_, ?_, ?_⟩
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] [] file_example_path [] [])
    rw [file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _
      (by rfl : alpha_only file_example_alpha ([] : List (BitVec 8)) = true)]
    exact alpha_geo_point_pos file_example_alpha p _ Hpos Hlt file_example_alpha_ne
  · show 0 < file_prefix_over_geo_weight file_example_alpha file_example_hdr p
      file_misconfigured_argv [] [] file_example_path []
      (file_prefix_core file_example_hdr file_misconfigured_argv [] [] file_example_path []
        [BitVec.ofInt 8 65])
    rw [file_prefix_over_geo_weight_match _ _ _ _ _ _ _ _ _
      (by decide : alpha_only file_example_alpha [BitVec.ofInt 8 65] = true)]
    exact alpha_geo_point_pos file_example_alpha p _ Hpos Hlt file_example_alpha_ne
  · unfold file_prefix_core
    rw [fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne,
      fs_file_file_core_other file_misconfigured_argv [] [] file_example_path [] _
        file_other_path file_other_path_ne]

/- =========================================================================
   Combinator: the FULL-SUPPORT base family — every core carries mass
   ========================================================================= -/

/- Every family above weighs ZERO off one fixed template: `geo_weight` off
   its argv, envp and file system; `envp_geo_weight` off its argv and file
   system; the file families off their argv, envp and standard input and at
   every path but one.  The header's warning applies at each of those null
   sets — a fire set living there is charged nothing, and a
   `Measure.weight_bound_T` claim about it holds vacuously.  This family is
   the one under which NO core is in a null set: four independent factors,
   one per field of `FinInput.FinCore`, each strictly positive at every value
   of its coordinate when its rates are strictly inside `(0, 1)`
   (`full_support_base_positive`).

   The four factors are the memoryless sources this file already has, run
   over the fields the earlier families held fixed.  argv and envp are lists
   of byte strings, and both are spread by the entry-count / per-entry-byte
   source `envp_point` was built for; `strings_point` is that source under a
   field-neutral name, so that "the argv law" and "the envp law" are visibly
   the same object at different rates.  The file system is a list of
   (path, contents) PAIRS, and `fs_point` is the same entry-count shell
   around a pair of byte-geometric factors per entry, one for the path and
   one for the contents.  Standard input is `geo_point` as everywhere.
   Eight rates in all.

   WHAT IS NOT CLAIMED.  `fs_point` weighs EVERY list of pairs, sorted or
   not, duplicate keys or not, and those lists are never `Fs.valid_fs` and
   so never the file system of a real input.  This seam is decided rather
   than hidden, and it is decided the way every other family in this file
   decides validity: not at all.  `file_core`'s comment already says the
   library neither needs nor claims that the cores it weighs are valid, and
   this family is no different — the declared `1` is the mass of the LAW over
   all finite cores, and the mass reachable by valid images is strictly less
   than it. -/

/-- The argv law and the envp law are ONE source.  `strings_point r q` is
    `envp_point r q`, and `strings_factor` is `envp_factor`; the
    field-neutral names exist so that a statement about the argv coordinate
    does not read as a statement about the environment.  Every lemma about
    `envp_point` applies through `unfold`. -/
def strings_factor (r q : Rat) (xs : List (List (BitVec 8))) : Rat :=
  envp_factor r q xs

def strings_point (r q : Rat) (xs : List (List (BitVec 8))) : Rat :=
  envp_point r q xs

theorem strings_point_closed_form (r q : Rat) (xs : List (List (BitVec 8))) :
    strings_point r q xs = r * Qpow (1 - r) xs.length * entries_geo_product q xs :=
  envp_point_closed_form r q xs

theorem strings_point_nonneg (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) (xs : List (List (BitVec 8))) :
    0 ≤ strings_point r q xs :=
  envp_point_nonneg r q Hr0 Hr1 Hq0 Hq1 xs

theorem strings_point_pos (r q : Rat) (xs : List (List (BitVec 8)))
    (Hr0 : 0 < r) (Hr1 : r < 1) (Hq0 : 0 < q) (Hq1 : q < 1) :
    0 < strings_point r q xs :=
  envp_point_pos r q xs Hr0 Hr1 Hq0 Hq1

/-- The file-system law.  `fs_entries_product` is `entries_geo_product` with
    two byte-geometric factors per entry — the path's and the contents' —
    and `fs_factor` is `envp_factor`'s running product with the same pair
    inside: continuing past an entry costs `1 - u`, the entry costs its
    path's weight times its contents' weight.  `fs_point` is `u` times it,
    `u` being the weight of stopping.  As with `envp_point`, the
    three-factor form the family is specified with is `fs_point_closed_form`
    and is a LEMMA, not a rival definition. -/
def fs_entries_product (v w : Rat) : Fs.Fs → Rat
  | [] => 1
  | (pth, d) :: fs' => geo_point v pth.length * geo_point w d.length *
      fs_entries_product v w fs'

def fs_factor (u v w : Rat) : Fs.Fs → Rat
  | [] => 1
  | (pth, d) :: fs' => (1 - u) * geo_point v pth.length * geo_point w d.length *
      fs_factor u v w fs'

def fs_point (u v w : Rat) (fs : Fs.Fs) : Rat := u * fs_factor u v w fs

theorem fs_entries_product_nil (v w : Rat) : fs_entries_product v w [] = 1 := rfl

theorem fs_entries_product_cons (v w : Rat) (pth : Fs.path) (d : List (BitVec 8))
    (fs : Fs.Fs) :
    fs_entries_product v w ((pth, d) :: fs) =
      geo_point v pth.length * geo_point w d.length * fs_entries_product v w fs := rfl

theorem fs_factor_nil (u v w : Rat) : fs_factor u v w [] = 1 := rfl

theorem fs_factor_cons (u v w : Rat) (pth : Fs.path) (d : List (BitVec 8))
    (fs : Fs.Fs) :
    fs_factor u v w ((pth, d) :: fs) =
      (1 - u) * geo_point v pth.length * geo_point w d.length * fs_factor u v w fs := rfl

theorem fs_factor_closed_form (u v w : Rat) (fs : Fs.Fs) :
    fs_factor u v w fs = Qpow (1 - u) fs.length * fs_entries_product v w fs := by
  induction fs with
  | nil =>
    change (1 : Rat) = Qpow (1 - u) 0 * 1
    rw [Qpow_0]
    grind
  | cons hd fs ih =>
    obtain ⟨pth, d⟩ := hd
    change (1 - u) * geo_point v pth.length * geo_point w d.length *
        fs_factor u v w fs =
      Qpow (1 - u) ((pth, d) :: fs).length * fs_entries_product v w ((pth, d) :: fs)
    rw [List.length_cons, Qpow_succ, ih]
    change (1 - u) * geo_point v pth.length * geo_point w d.length *
        (Qpow (1 - u) fs.length * fs_entries_product v w fs) =
      ((1 - u) * Qpow (1 - u) fs.length) *
        (geo_point v pth.length * geo_point w d.length * fs_entries_product v w fs)
    grind

theorem fs_point_closed_form (u v w : Rat) (fs : Fs.Fs) :
    fs_point u v w fs = u * Qpow (1 - u) fs.length * fs_entries_product v w fs := by
  unfold fs_point
  rw [fs_factor_closed_form]
  grind

theorem fs_factor_app (u v w : Rat) (fs fs' : Fs.Fs) :
    fs_factor u v w (fs ++ fs') = fs_factor u v w fs * fs_factor u v w fs' := by
  induction fs with
  | nil =>
    rw [List.nil_append, fs_factor_nil]
    grind
  | cons hd fs ih =>
    obtain ⟨pth, d⟩ := hd
    change (1 - u) * geo_point v pth.length * geo_point w d.length *
        fs_factor u v w (fs ++ fs') =
      (1 - u) * geo_point v pth.length * geo_point w d.length * fs_factor u v w fs *
        fs_factor u v w fs'
    rw [ih]
    grind

theorem fs_factor_one (u v w : Rat) (pth : Fs.path) (d : List (BitVec 8)) :
    fs_factor u v w [(pth, d)] =
      (1 - u) * geo_point v pth.length * geo_point w d.length := by
  rw [fs_factor_cons, fs_factor_nil]
  grind

/-- Nonnegativity costs the five side conditions the three rates cost
    separately, exactly as `envp_factor_nonneg`'s cost its three. -/
theorem fs_factor_nonneg (u v w : Rat) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (fs : Fs.Fs) : 0 ≤ fs_factor u v w fs := by
  induction fs with
  | nil => exact Qle_0_1
  | cons hd fs ih =>
    obtain ⟨pth, d⟩ := hd
    rw [fs_factor_cons]
    refine Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by grind)
      (geo_point_nonneg v _ Hv0 Hv1)) (geo_point_nonneg w _ Hw0 Hw1)) ih

theorem fs_point_nonneg (u v w : Rat) (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v)
    (Hv1 : v ≤ 1) (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (fs : Fs.Fs) :
    0 ≤ fs_point u v w fs := by
  unfold fs_point
  exact Rat.mul_nonneg Hu0 (fs_factor_nonneg u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs)

/-- One file system weighs at most the mass of the file systems extending it
    (as lists), because `u <= 1` — `envp_point_le_factor` on this
    coordinate, and the base case of the same induction. -/
theorem fs_point_le_factor (u v w : Rat) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (fs : Fs.Fs) :
    fs_point u v w fs ≤ fs_factor u v w fs := by
  unfold fs_point
  have h := Rat.mul_le_mul_of_nonneg_right Hu1
    (fs_factor_nonneg u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs)
  rwa [Rat.one_mul] at h

/-- Strict positivity at every list of pairs, sorted or not: every factor of
    the running product is positive, so the product is.  `envp_point_pos`'s
    induction with two `geo_point_pos` per entry. -/
theorem fs_point_pos (u v w : Rat) (fs : Fs.Fs) (Hu0 : 0 < u) (Hu1 : u < 1)
    (Hv0 : 0 < v) (Hv1 : v < 1) (Hw0 : 0 < w) (Hw1 : w < 1) :
    0 < fs_point u v w fs := by
  unfold fs_point
  refine Rat.mul_pos Hu0 ?_
  induction fs with
  | nil => exact (by decide : (0 : Rat) < 1)
  | cons hd fs ih =>
    obtain ⟨pth, d⟩ := hd
    rw [fs_factor_cons]
    exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (by grind)
      (geo_point_pos v _ Hv0 Hv1)) (geo_point_pos w _ Hw0 Hw1)) ih

/-- THE WEIGHT: the product of the four coordinates' laws, with no template
    and no `decide` — there is no environment to match, because every
    environment is in the support.  `base_weight_mk` is the rewrite rule on
    a constructed core, and it is `eq` by computation rather than a `Qeq`
    through a decision, which is the whole difference from
    `geo_weight_match`. -/
def base_weight (ra qa re qe u v w ps : Rat) (c : FinCore) : Rat :=
  strings_point ra qa c.core_argv * strings_point re qe c.core_envp *
    fs_point u v w c.core_fs * geo_point ps c.core_stdin.length

theorem base_weight_mk (ra qa re qe u v w ps : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (s : List (BitVec 8)) :
    base_weight ra qa re qe u v w ps (FinCore.mkFinCore argv envp fs s) =
      strings_point ra qa argv * strings_point re qe envp *
        fs_point u v w fs * geo_point ps s.length := rfl

/-- THE FAMILY'S FORMULA with all eight rates visible, stated because the
    law is usually written in this shape and a reader should be able to
    check the definition against it without unfolding anything. -/
theorem base_weight_closed_form (ra qa re qe u v w ps : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (s : List (BitVec 8)) :
    base_weight ra qa re qe u v w ps (FinCore.mkFinCore argv envp fs s) =
      (ra * Qpow (1 - ra) argv.length * entries_geo_product qa argv) *
        (re * Qpow (1 - re) envp.length * entries_geo_product qe envp) *
        (u * Qpow (1 - u) fs.length * fs_entries_product v w fs) *
        (ps * Qpow (1 - ps) s.length * Qpow (1 / 256) s.length) := by
  rw [base_weight_mk, strings_point_closed_form, strings_point_closed_form,
    fs_point_closed_form, geo_point_closed_form]

theorem base_weight_nonneg (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) (c : FinCore) :
    0 ≤ base_weight ra qa re qe u v w ps c := by
  unfold base_weight
  exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
    (strings_point_nonneg ra qa Hra0 Hra1 Hqa0 Hqa1 _)
    (strings_point_nonneg re qe Hre0 Hre1 Hqe0 Hqe1 _))
    (fs_point_nonneg u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 _))
    (geo_point_nonneg ps _ Hps0 Hps1)

/-- The distribution.  Mass `1` is DECLARED, and the sixteen side conditions
    are constructor arguments for the reason `stdin_geometric`'s two are:
    `cd_nonneg` is a field.  None of the eight STRICT inequalities is
    demanded — nothing the constructor needs uses them, and the two lemmas
    that do (`full_support_base_positive`, the lower certificate) ask for
    them as hypotheses of their own statements, so a degenerate member (a
    rate at `0` or `1`) is a member in good standing, as everywhere in this
    file. -/
def full_support_base (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    CoreDistribution where
  cd_weight := base_weight ra qa re qe u v w ps
  cd_mass := 1
  cd_nonneg := base_weight_nonneg ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1

theorem full_support_base_mass_nonneg (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1) :
    0 ≤ (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_mass := by
  show (0 : Rat) ≤ 1
  decide

/- =========================================================================
   Full support: every core weighs something
   ========================================================================= -/

/-- THE FULL-SUPPORT LEMMA.  At any eight rates strictly inside `(0, 1)`,
    every core — every argv, every environment, every file system, every
    standard input, however long — weighs strictly more than zero.  Under
    this family no fire set sits in a null set, so a
    `Measure.weight_bound_T` claim is never vacuous.  Four positivity facts,
    one per coordinate, and the product of positives is positive. -/
theorem full_support_base_positive (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Hrapos : 0 < ra) (Hralt : ra < 1) (Hqapos : 0 < qa) (Hqalt : qa < 1)
    (Hrepos : 0 < re) (Hrelt : re < 1) (Hqepos : 0 < qe) (Hqelt : qe < 1)
    (Hupos : 0 < u) (Hult : u < 1) (Hvpos : 0 < v) (Hvlt : v < 1)
    (Hwpos : 0 < w) (Hwlt : w < 1) (Hpspos : 0 < ps) (Hpslt : ps < 1)
    (c : FinCore) :
    0 < (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight c := by
  show 0 < base_weight ra qa re qe u v w ps c
  unfold base_weight
  exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos
    (strings_point_pos ra qa _ Hrapos Hralt Hqapos Hqalt)
    (strings_point_pos re qe _ Hrepos Hrelt Hqepos Hqelt))
    (fs_point_pos u v w _ Hupos Hult Hvpos Hvlt Hwpos Hwlt))
    (geo_point_pos ps _ Hpspos Hpslt)

/-- The same fact on RECORDS, which is the form `Measure.DISTRIBUTION`'s `w`
    is consulted in: every record weighs something. -/
theorem full_support_base_lift_positive (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Hrapos : 0 < ra) (Hralt : ra < 1) (Hqapos : 0 < qa) (Hqalt : qa < 1)
    (Hrepos : 0 < re) (Hrelt : re < 1) (Hqepos : 0 < qe) (Hqelt : qe < 1)
    (Hupos : 0 < u) (Hult : u < 1) (Hvpos : 0 < v) (Hvlt : v < 1)
    (Hwpos : 0 < w) (Hwlt : w < 1) (Hpspos : 0 < ps) (Hpslt : ps < 1)
    (f : FinProcInput) :
    0 < cd_lift (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) f := by
  unfold cd_lift
  exact full_support_base_positive ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    Hrapos Hralt Hqapos Hqalt Hrepos Hrelt Hqepos Hqelt
    Hupos Hult Hvpos Hvlt Hwpos Hwlt Hpspos Hpslt _

/-- THE BITE, against every sibling at once: a core off every fixed template
    — its argv, envp, file system and standard input each one byte — weighs
    zero under each of the template families over the empty environment (the
    header families at the empty header, the alphabet one over the one-byte
    alphabet), and strictly positively here. -/
def full_support_example_core : FinCore :=
  FinCore.mkFinCore [[BitVec.ofInt 8 65]] [[BitVec.ofInt 8 65]]
    [([BitVec.ofInt 8 65], [BitVec.ofInt 8 65])] [BitVec.ofInt 8 65]

theorem full_support_base_bites (p r q : Rat) :
    geo_weight p [] [] [] full_support_example_core = 0 ∧
      envp_geo_weight p r q [] [] full_support_example_core = 0 ∧
      file_geo_weight p [] [] [] [BitVec.ofInt 8 65] [] full_support_example_core = 0 ∧
      file_envp_geo_weight p r q [] [] [BitVec.ofInt 8 65] [] full_support_example_core = 0 ∧
      file_prefix_geo_weight [] p [] [] [] [BitVec.ofInt 8 65] []
        full_support_example_core = 0 ∧
      file_prefix_over_geo_weight [BitVec.ofInt 8 65] [] p [] [] []
        [BitVec.ofInt 8 65] [] full_support_example_core = 0 ∧
      0 < base_weight (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2) (1 / 2)
        (1 / 2) full_support_example_core := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core])
  · apply envp_geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core])
  · apply file_geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core, file_core])
  · apply file_envp_geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core, file_envp_core, file_core])
  · apply file_prefix_geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core, file_core])
  · apply file_prefix_over_geo_weight_mismatch
    intro Heq
    exact absurd (congrArg FinCore.core_argv Heq) (by simp [full_support_example_core, file_core])
  · unfold full_support_example_core
    rw [base_weight_mk]
    have h2 : (0 : Rat) < 1 / 2 := Qpos_one_div 2 (by decide)
    have h2' : (1 : Rat) / 2 < 1 := Qdiv_nat_lt_one 1 2 (by decide) (by decide)
    exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos
      (strings_point_pos _ _ _ h2 h2' h2 h2')
      (strings_point_pos _ _ _ h2 h2' h2 h2'))
      (fs_point_pos _ _ _ _ h2 h2' h2 h2' h2 h2'))
      (geo_point_pos _ _ h2 h2')

/- =========================================================================
   The four coordinates, recombined
   ========================================================================= -/

/-- Every core whose argv comes from `Av`, envp from `Ae`, file system from
    `Af` and standard input from `B`.  Three `flat_map` layers over one
    `map`, and its sum is the product of the four coordinates' sums
    (`qsum_full_support_product`).  This identity is the only place the four
    coordinates meet; every bound below is assembled from four
    one-coordinate bounds proved apart. -/
def full_support_product (Av Ae : List (List (List (BitVec 8))))
    (Af : List Fs.Fs) (B : List (List (BitVec 8))) : List FinCore :=
  Av.flatMap (fun argv => Ae.flatMap (fun envp =>
    Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs))))

theorem In_full_support_product (Av Ae : List (List (List (BitVec 8))))
    (Af : List Fs.Fs) (B : List (List (BitVec 8)))
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (s : List (BitVec 8))
    (Ha : argv ∈ Av) (He : envp ∈ Ae) (Hf : fs ∈ Af) (Hs : s ∈ B) :
    FinCore.mkFinCore argv envp fs s ∈ full_support_product Av Ae Af B := by
  unfold full_support_product
  exact List.mem_flatMap.mpr ⟨argv, Ha, List.mem_flatMap.mpr ⟨envp, He,
    List.mem_flatMap.mpr ⟨fs, Hf, List.mem_map.mpr ⟨s, Hs, rfl⟩⟩⟩⟩

theorem qsum_base_stdin_block (ra qa re qe u v w ps : Rat)
    (argv envp : List (List (BitVec 8))) (fs : Fs.Fs) (B : List (List (BitVec 8))) :
    qsum (base_weight ra qa re qe u v w ps)
        (B.map (FinCore.mkFinCore argv envp fs)) =
      strings_point ra qa argv * strings_point re qe envp * fs_point u v w fs *
        qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_map]
  calc qsum (fun s => base_weight ra qa re qe u v w ps
        (FinCore.mkFinCore argv envp fs s)) B
      = qsum (fun s => (strings_point ra qa argv * strings_point re qe envp *
          fs_point u v w fs) * geo_point ps s.length) B :=
        qsum_ext _ _ _ (fun s _ => base_weight_mk ra qa re qe u v w ps argv envp fs s)
    _ = (strings_point ra qa argv * strings_point re qe envp * fs_point u v w fs) *
          qsum (fun s => geo_point ps s.length) B :=
        qsum_scale _ (fun s => geo_point ps s.length) B

theorem qsum_base_fs_block (ra qa re qe u v w ps : Rat)
    (argv envp : List (List (BitVec 8))) (Af : List Fs.Fs)
    (B : List (List (BitVec 8))) :
    qsum (base_weight ra qa re qe u v w ps)
        (Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs))) =
      strings_point ra qa argv * strings_point re qe envp *
        qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_flat_map]
  calc qsum (fun fs => qsum (base_weight ra qa re qe u v w ps)
        (B.map (FinCore.mkFinCore argv envp fs))) Af
      = qsum (fun fs => (strings_point ra qa argv * strings_point re qe envp *
            qsum (fun s => geo_point ps s.length) B) * fs_point u v w fs) Af :=
        qsum_ext _ _ _ (fun fs _ => by
          rw [qsum_base_stdin_block ra qa re qe u v w ps argv envp fs B]
          grind)
    _ = (strings_point ra qa argv * strings_point re qe envp *
          qsum (fun s => geo_point ps s.length) B) * qsum (fs_point u v w) Af :=
        qsum_scale _ (fs_point u v w) Af
    _ = strings_point ra qa argv * strings_point re qe envp *
          qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by grind

theorem qsum_base_envp_block (ra qa re qe u v w ps : Rat)
    (argv : List (List (BitVec 8))) (Ae : List (List (List (BitVec 8))))
    (Af : List Fs.Fs) (B : List (List (BitVec 8))) :
    qsum (base_weight ra qa re qe u v w ps)
        (Ae.flatMap (fun envp =>
          Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs)))) =
      strings_point ra qa argv * qsum (strings_point re qe) Ae *
        qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  rw [qsum_flat_map]
  calc qsum (fun envp => qsum (base_weight ra qa re qe u v w ps)
        (Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs)))) Ae
      = qsum (fun envp => (strings_point ra qa argv * qsum (fs_point u v w) Af *
            qsum (fun s => geo_point ps s.length) B) * strings_point re qe envp) Ae :=
        qsum_ext _ _ _ (fun envp _ => by
          rw [qsum_base_fs_block ra qa re qe u v w ps argv envp Af B]
          grind)
    _ = (strings_point ra qa argv * qsum (fs_point u v w) Af *
          qsum (fun s => geo_point ps s.length) B) * qsum (strings_point re qe) Ae :=
        qsum_scale _ (strings_point re qe) Ae
    _ = strings_point ra qa argv * qsum (strings_point re qe) Ae *
          qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by grind

theorem qsum_full_support_product (ra qa re qe u v w ps : Rat)
    (Av Ae : List (List (List (BitVec 8)))) (Af : List Fs.Fs)
    (B : List (List (BitVec 8))) :
    qsum (base_weight ra qa re qe u v w ps) (full_support_product Av Ae Af B) =
      qsum (strings_point ra qa) Av * qsum (strings_point re qe) Ae *
        qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by
  unfold full_support_product
  rw [qsum_flat_map]
  calc qsum (fun argv => qsum (base_weight ra qa re qe u v w ps)
        (Ae.flatMap (fun envp =>
          Af.flatMap (fun fs => B.map (FinCore.mkFinCore argv envp fs))))) Av
      = qsum (fun argv => (qsum (strings_point re qe) Ae * qsum (fs_point u v w) Af *
            qsum (fun s => geo_point ps s.length) B) * strings_point ra qa argv) Av :=
        qsum_ext _ _ _ (fun argv _ => by
          rw [qsum_base_envp_block ra qa re qe u v w ps argv Ae Af B]
          grind)
    _ = (qsum (strings_point re qe) Ae * qsum (fs_point u v w) Af *
          qsum (fun s => geo_point ps s.length) B) * qsum (strings_point ra qa) Av :=
        qsum_scale _ (strings_point ra qa) Av
    _ = qsum (strings_point ra qa) Av * qsum (strings_point re qe) Ae *
          qsum (fs_point u v w) Af * qsum (fun s => geo_point ps s.length) B := by grind

/-- The product of four duplicate-free enumerations repeats nothing: a core
    determines each of its four fields, so within a block the innermost map
    is injective and any two blocks at any layer are disjoint.  Only the
    lower certificate needs this. -/
theorem NoDup_full_support_product (Av Ae : List (List (List (BitVec 8))))
    (Af : List Fs.Fs) (B : List (List (BitVec 8)))
    (HA : Av.Nodup) (HE : Ae.Nodup) (HF : Af.Nodup) (HB : B.Nodup) :
    (full_support_product Av Ae Af B).Nodup := by
  unfold full_support_product
  refine NoDup_flat_map _ _ HA (fun argv _ => ?_) (fun argv1 argv2 c _ _ H1 H2 => ?_)
  · refine NoDup_flat_map _ _ HE (fun envp _ => ?_) (fun envp1 envp2 c _ _ H1 H2 => ?_)
    · refine NoDup_flat_map _ _ HF (fun fs _ => ?_) (fun fs1 fs2 c _ _ H1 H2 => ?_)
      · apply NoDup_map_inj
        · intro x y _ _ Heq
          exact congrArg FinCore.core_stdin Heq
        · exact HB
      · obtain ⟨s1, _, h1⟩ := List.mem_map.mp H1
        obtain ⟨s2, _, h2⟩ := List.mem_map.mp H2
        exact congrArg FinCore.core_fs (h1.trans h2.symm)
    · obtain ⟨fs1, _, H1⟩ := List.mem_flatMap.mp H1
      obtain ⟨s1, _, h1⟩ := List.mem_map.mp H1
      obtain ⟨fs2, _, H2⟩ := List.mem_flatMap.mp H2
      obtain ⟨s2, _, h2⟩ := List.mem_map.mp H2
      exact congrArg FinCore.core_envp (h1.trans h2.symm)
  · obtain ⟨envp1, _, H1⟩ := List.mem_flatMap.mp H1
    obtain ⟨fs1, _, H1⟩ := List.mem_flatMap.mp H1
    obtain ⟨s1, _, h1⟩ := List.mem_map.mp H1
    obtain ⟨envp2, _, H2⟩ := List.mem_flatMap.mp H2
    obtain ⟨fs2, _, H2⟩ := List.mem_flatMap.mp H2
    obtain ⟨s2, _, h2⟩ := List.mem_map.mp H2
    exact congrArg FinCore.core_argv (h1.trans h2.symm)

/-- THE ENGINE every bound below runs on: a duplicate-free list of cores each
    of whose four fields lies in a given enumeration weighs at most the
    product of four numbers bounding the four enumerations' sums.
    `qsum_core_incl_le` places the list inside the product enumeration,
    `qsum_full_support_product` evaluates that, and
    `Qmult_le_compat_nonneg` three times puts the four bounds together. -/
theorem base_weight_product_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Av Ae : List (List (List (BitVec 8)))) (Af : List Fs.Fs)
    (B : List (List (BitVec 8))) (SA SE SF SB : Rat) (cs : List FinCore)
    (HA : qsum (strings_point ra qa) Av ≤ SA)
    (HE : qsum (strings_point re qe) Ae ≤ SE)
    (HF : qsum (fs_point u v w) Af ≤ SF)
    (HB : qsum (fun s => geo_point ps s.length) B ≤ SB)
    (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs →
      c.core_argv ∈ Av ∧ c.core_envp ∈ Ae ∧ c.core_fs ∈ Af ∧ c.core_stdin ∈ B) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ SA * SE * SF * SB := by
  have HA0 : 0 ≤ qsum (strings_point ra qa) Av :=
    qsum_nonneg _ _ (fun x _ => strings_point_nonneg ra qa Hra0 Hra1 Hqa0 Hqa1 x)
  have HE0 : 0 ≤ qsum (strings_point re qe) Ae :=
    qsum_nonneg _ _ (fun x _ => strings_point_nonneg re qe Hre0 Hre1 Hqe0 Hqe1 x)
  have HF0 : 0 ≤ qsum (fs_point u v w) Af :=
    qsum_nonneg _ _ (fun x _ => fs_point_nonneg u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 x)
  have HB0 : 0 ≤ qsum (fun s => geo_point ps s.length) B :=
    qsum_nonneg _ _ (fun x _ => geo_point_nonneg ps x.length Hps0 Hps1)
  refine Rat.le_trans (qsum_core_incl_le (base_weight ra qa re qe u v w ps) cs
    (full_support_product Av Ae Af B)
    (base_weight_nonneg ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
      Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1) Hnd ?_) ?_
  · intro c Hc
    obtain ⟨Ha, He, Hf, Hs⟩ := Hall c Hc
    exact In_full_support_product Av Ae Af B c.core_argv c.core_envp c.core_fs
      c.core_stdin Ha He Hf Hs
  · rw [qsum_full_support_product]
    exact Qmult_le_compat_nonneg
      (Qmult_le_compat_nonneg (Qmult_le_compat_nonneg HA HE HA0 HE0) HF
        (Rat.mul_nonneg HA0 HE0) HF0)
      HB (Rat.mul_nonneg (Rat.mul_nonneg HA0 HE0) HF0) HB0

/- =========================================================================
   The file-system enumeration, and its cancellation
   ========================================================================= -/

/-- Every file system extending `fs0` (as a list) by at most `M` further
    entries, each with a path shorter than `Lp` and contents shorter than
    `Lc`.  It is `envp_enum` with a pair where that has an entry: two nested
    `short_inputs` enumerations per step, one for the path and one for the
    contents.  As with `envp_enum`, duplicate-freedom is never proved and
    never needed for the bounds. -/
def fs_enum (fs0 : Fs.Fs) : Nat → Nat → Nat → List Fs.Fs
  | 0, _, _ => [fs0]
  | M + 1, Lp, Lc =>
    fs0 :: (short_inputs Lp).flatMap (fun pth =>
      (short_inputs Lc).flatMap (fun d => fs_enum (fs0 ++ [(pth, d)]) M Lp Lc))

theorem fs_enum_complete (M Lp Lc : Nat) (fs0 rest : Fs.Fs)
    (Hlen : rest.length ≤ M)
    (Hent : ∀ e, e ∈ rest → (e.1).length < Lp ∧ (e.2).length < Lc) :
    fs0 ++ rest ∈ fs_enum fs0 M Lp Lc := by
  induction M generalizing fs0 rest with
  | zero =>
    rcases rest with _ | ⟨e, rest⟩
    · rw [List.append_nil]
      exact List.mem_cons_self ..
    · exact absurd Hlen (by simp)
  | succ M ih =>
    rcases rest with _ | ⟨⟨pth, d⟩, rest⟩
    · rw [List.append_nil]
      exact List.mem_cons_self ..
    · obtain ⟨Hp, Hd⟩ := Hent (pth, d) (List.mem_cons_self ..)
      refine List.mem_cons_of_mem _ ?_
      refine List.mem_flatMap.mpr ⟨pth, short_inputs_complete Lp pth Hp, ?_⟩
      refine List.mem_flatMap.mpr ⟨d, short_inputs_complete Lc d Hd, ?_⟩
      rw [show fs0 ++ (pth, d) :: rest = (fs0 ++ [(pth, d)]) ++ rest from by
        rw [List.append_assoc]; rfl]
      refine ih (fs0 ++ [(pth, d)]) rest ?_ ?_
      · simp only [List.length_cons] at Hlen
        omega
      · intro x Hx
        exact Hent x (List.mem_cons_of_mem _ Hx)

/-- ONE STEP OF THE FILE-SYSTEM CANCELLATION, exactly: the file systems one
    entry deeper than `fs0` carry `fs_factor fs0` times `(1 - u)` times what
    the path enumeration weighs times what the contents enumeration weighs —
    `qsum_envp_factor_step` with the second `short_inputs_sum` inside the
    first. -/
theorem qsum_fs_factor_step (u v w : Rat) (fs0 : Fs.Fs) (Lp Lc : Nat) :
    qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
        (short_inputs Lc)) (short_inputs Lp) =
      fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc) := by
  calc qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
        (short_inputs Lc)) (short_inputs Lp)
      = qsum (fun pth => (fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc)) *
          geo_point v pth.length) (short_inputs Lp) := by
        apply qsum_ext
        intro pth _
        calc qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)])) (short_inputs Lc)
            = qsum (fun d => (fs_factor u v w fs0 * (1 - u) * geo_point v pth.length) *
                geo_point w d.length) (short_inputs Lc) := by
              apply qsum_ext
              intro d _
              rw [fs_factor_app, fs_factor_one]
              grind
          _ = (fs_factor u v w fs0 * (1 - u) * geo_point v pth.length) *
                qsum (fun d => geo_point w d.length) (short_inputs Lc) :=
              qsum_scale _ _ _
          _ = (fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc)) *
                geo_point v pth.length := by
              rw [short_inputs_sum, geo_prefix_sum_closed]
              grind
    _ = (fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - w) Lc)) *
          qsum (fun pth => geo_point v pth.length) (short_inputs Lp) :=
        qsum_scale _ _ _
    _ = fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp) *
          (1 - Qpow (1 - w) Lc) := by
        rw [short_inputs_sum, geo_prefix_sum_closed]
        grind

/-- Three small facts about a rate in `[0, 1]` and its geometric tail,
    stated once because eight rates each need them below. -/
theorem one_minus_unit (q : Rat) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 ≤ 1 - q ∧ 1 - q ≤ 1 := by
  refine ⟨by grind, by grind⟩

theorem geo_tail_unit (q : Rat) (L : Nat) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 ≤ Qpow (1 - q) L ∧ Qpow (1 - q) L ≤ 1 := by
  obtain ⟨h0, h1⟩ := one_minus_unit q Hq0 Hq1
  exact ⟨Qpow_nonneg _ _ h0, Qpow_le_1 _ _ h0 h1⟩

theorem geo_head_unit (q : Rat) (L : Nat) (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    0 ≤ 1 - Qpow (1 - q) L ∧ 1 - Qpow (1 - q) L ≤ 1 := by
  obtain ⟨h0, h1⟩ := geo_tail_unit q L Hq0 Hq1
  exact one_minus_unit _ h0 h1

/-- THE CANCELLATION on the file-system coordinate: the whole enumeration
    weighs no more than the mass of the file systems extending `fs0`.
    `envp_enum_sum_le`'s induction; the step charges the continuations
    `(1 - u)` times two partial sums each under `1`, and the base case is
    `fs_point_le_factor`. -/
theorem fs_enum_sum_le (u v w : Rat) (_Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v)
    (Hv1 : v ≤ 1) (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) :
    ∀ (M Lp Lc : Nat) (fs0 : Fs.Fs),
      qsum (fs_point u v w) (fs_enum fs0 M Lp Lc) ≤ fs_factor u v w fs0 := by
  intro M
  induction M with
  | zero =>
    intro Lp Lc fs0
    show qsum (fs_point u v w) [fs0] ≤ fs_factor u v w fs0
    rw [qsum_cons, qsum_nil]
    have h := fs_point_le_factor u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs0
    grind
  | succ M ih =>
    intro Lp Lc fs0
    show qsum (fs_point u v w)
        (fs0 :: (short_inputs Lp).flatMap (fun pth => (short_inputs Lc).flatMap
          (fun d => fs_enum (fs0 ++ [(pth, d)]) M Lp Lc))) ≤ fs_factor u v w fs0
    rw [qsum_cons]
    refine Rat.le_trans (b := fs_point u v w fs0 +
      qsum (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
        (short_inputs Lc)) (short_inputs Lp)) ?_ ?_
    · refine Rat.add_le_add_left.mpr ?_
      exact Rat.le_trans (qsum_flat_map_le (fs_point u v w)
        (fun pth => (short_inputs Lc).flatMap
          (fun d => fs_enum (fs0 ++ [(pth, d)]) M Lp Lc))
        (fun pth => qsum (fun d => fs_factor u v w (fs0 ++ [(pth, d)]))
          (short_inputs Lc))
        (short_inputs Lp)
        (fun pth _ => qsum_flat_map_le (fs_point u v w)
          (fun d => fs_enum (fs0 ++ [(pth, d)]) M Lp Lc)
          (fun d => fs_factor u v w (fs0 ++ [(pth, d)])) (short_inputs Lc)
          (fun d _ => ih Lp Lc (fs0 ++ [(pth, d)])))) (Rat.le_refl)
    · rw [qsum_fs_factor_step]
      unfold fs_point
      have HF : 0 ≤ fs_factor u v w fs0 * (1 - u) :=
        Rat.mul_nonneg (fs_factor_nonneg u v w Hu1 Hv0 Hv1 Hw0 Hw1 fs0) (by grind)
      obtain ⟨HGv0, HGv1⟩ := geo_head_unit v Lp Hv0 Hv1
      obtain ⟨HGw0, HGw1⟩ := geo_head_unit w Lc Hw0 Hw1
      have hAB : (1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc) ≤ 1 := by
        have h := Qmult_le_compat_nonneg HGv1 HGw1 HGv0 HGw0
        simpa using h
      have h1 : fs_factor u v w fs0 * (1 - u) * ((1 - Qpow (1 - v) Lp) *
          (1 - Qpow (1 - w) Lc)) ≤ fs_factor u v w fs0 * (1 - u) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hAB HF
      have hmain : fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp) *
          (1 - Qpow (1 - w) Lc) ≤ fs_factor u v w fs0 * (1 - u) := by
        calc fs_factor u v w fs0 * (1 - u) * (1 - Qpow (1 - v) Lp) *
              (1 - Qpow (1 - w) Lc)
            = fs_factor u v w fs0 * (1 - u) * ((1 - Qpow (1 - v) Lp) *
                (1 - Qpow (1 - w) Lc)) := by grind
          _ ≤ fs_factor u v w fs0 * (1 - u) * 1 := h1
          _ = fs_factor u v w fs0 * (1 - u) := by grind
      have hsplit : u * fs_factor u v w fs0 + fs_factor u v w fs0 * (1 - u) =
          fs_factor u v w fs0 := by grind
      grind

/- =========================================================================
   The depths, read off the task's own list
   ========================================================================= -/

/-- Eight depths where the envp-varying family reads three: an entry count
    and an entry length for argv, the same two for envp
    (`cores_envp_depth`, `cores_entry_depth`), an entry count, a path length
    and a contents length for the file system, and the standard-input length
    (`cores_stdin_depth`).  Each exists because `Measure.weight_bound_T`'s
    lists are finite and for no other reason; the length depths are `+ 1` of
    a maximum because `short_inputs` enumerates STRICTLY shorter lists. -/
def cores_argv_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_argv.length))

def cores_argv_entry_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_argv.map (fun e => e.length)))) + 1

def cores_fs_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => c.core_fs.length))

def cores_fs_path_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_fs.map (fun e => e.1.length)))) + 1

def cores_fs_contents_depth (cs : List FinCore) : Nat :=
  list_max (cs.map (fun c => list_max (c.core_fs.map (fun e => e.2.length)))) + 1

theorem cores_argv_depth_ge (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_argv.length ≤ cores_argv_depth cs := by
  unfold cores_argv_depth
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)

theorem cores_fs_depth_ge (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_fs.length ≤ cores_fs_depth cs := by
  unfold cores_fs_depth
  exact list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)

/-- The three "strictly shorter than" depths share one proof: the entry is
    under its core's inner maximum, and that is under the outer maximum. -/
theorem cores_inner_max_gt (A : Type) (proj : FinCore → List A) (len : A → Nat)
    (cs : List FinCore) (c : FinCore) (e : A) (Hc : c ∈ cs) (He : e ∈ proj c) :
    len e < list_max (cs.map (fun c0 => list_max ((proj c0).map len))) + 1 := by
  have Hinner : len e ≤ list_max ((proj c).map len) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨e, He, rfl⟩)
  have Houter : list_max ((proj c).map len) ≤
      list_max (cs.map (fun c0 => list_max ((proj c0).map len))) :=
    list_max_ge _ _ (List.mem_map.mpr ⟨c, Hc, rfl⟩)
  omega

theorem cores_argv_entry_depth_gt (cs : List FinCore) (c : FinCore)
    (e : List (BitVec 8)) (Hc : c ∈ cs) (He : e ∈ c.core_argv) :
    e.length < cores_argv_entry_depth cs := by
  unfold cores_argv_entry_depth
  exact cores_inner_max_gt _ FinCore.core_argv (fun e => e.length) cs c e Hc He

theorem cores_fs_path_depth_gt (cs : List FinCore) (c : FinCore)
    (e : Fs.path × List (BitVec 8)) (Hc : c ∈ cs) (He : e ∈ c.core_fs) :
    e.1.length < cores_fs_path_depth cs := by
  unfold cores_fs_path_depth
  exact cores_inner_max_gt _ FinCore.core_fs (fun e => e.1.length) cs c e Hc He

theorem cores_fs_contents_depth_gt (cs : List FinCore) (c : FinCore)
    (e : Fs.path × List (BitVec 8)) (Hc : c ∈ cs) (He : e ∈ c.core_fs) :
    e.2.length < cores_fs_contents_depth cs := by
  unfold cores_fs_contents_depth
  exact cores_inner_max_gt _ FinCore.core_fs (fun e => e.2.length) cs c e Hc He

/-- The four UNCONSTRAINED enumerations at the depths a list dictates: one
    per coordinate, from the empty prefix, each containing that coordinate
    of every core of the list and each summing to at most `1`.  A marginal
    bound fixes one coordinate and cites these for the other three. -/
def argv_free (cs : List FinCore) : List (List (List (BitVec 8))) :=
  envp_enum [] (cores_argv_depth cs) (cores_argv_entry_depth cs)

def envp_free (cs : List FinCore) : List (List (List (BitVec 8))) :=
  envp_enum [] (cores_envp_depth cs) (cores_entry_depth cs)

def fs_free (cs : List FinCore) : List Fs.Fs :=
  fs_enum [] (cores_fs_depth cs) (cores_fs_path_depth cs) (cores_fs_contents_depth cs)

def stdin_free (cs : List FinCore) : List (List (BitVec 8)) :=
  bytes_cyl [] (cores_stdin_depth cs)

theorem argv_free_In (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_argv ∈ argv_free cs := by
  unfold argv_free
  exact envp_enum_complete _ _ [] c.core_argv (cores_argv_depth_ge cs c Hc)
    (fun e He => cores_argv_entry_depth_gt cs c e Hc He)

theorem envp_free_In (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_envp ∈ envp_free cs := by
  unfold envp_free
  exact envp_enum_complete _ _ [] c.core_envp (cores_envp_depth_ge cs c Hc)
    (fun e He => cores_entry_depth_gt cs c e Hc He)

theorem fs_free_In (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_fs ∈ fs_free cs := by
  unfold fs_free
  exact fs_enum_complete _ _ _ [] c.core_fs (cores_fs_depth_ge cs c Hc)
    (fun e He => ⟨cores_fs_path_depth_gt cs c e Hc He,
      cores_fs_contents_depth_gt cs c e Hc He⟩)

theorem stdin_free_In (cs : List FinCore) (c : FinCore) (Hc : c ∈ cs) :
    c.core_stdin ∈ stdin_free cs := by
  unfold stdin_free
  exact bytes_cyl_In (cores_stdin_depth cs) [] c.core_stdin
    (cores_stdin_depth_ge cs c Hc)

theorem argv_free_sum_le (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q)
    (Hq1 : q ≤ 1) (cs : List FinCore) : qsum (strings_point r q) (argv_free cs) ≤ 1 := by
  unfold argv_free strings_point
  refine Rat.le_trans (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ []) ?_
  rw [envp_factor_nil]
  exact Rat.le_refl

theorem envp_free_sum_le (r q : Rat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1) (Hq0 : 0 ≤ q)
    (Hq1 : q ≤ 1) (cs : List FinCore) : qsum (strings_point r q) (envp_free cs) ≤ 1 := by
  unfold envp_free strings_point
  refine Rat.le_trans (envp_enum_sum_le r q Hr0 Hr1 Hq0 Hq1 _ _ []) ?_
  rw [envp_factor_nil]
  exact Rat.le_refl

theorem fs_free_sum_le (u v w : Rat) (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v)
    (Hv1 : v ≤ 1) (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (cs : List FinCore) :
    qsum (fs_point u v w) (fs_free cs) ≤ 1 := by
  unfold fs_free
  refine Rat.le_trans (fs_enum_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 _ _ _ []) ?_
  rw [fs_factor_nil]
  exact Rat.le_refl

theorem stdin_free_sum_le (p : Rat) (Hp0 : 0 ≤ p) (Hp1 : p ≤ 1) (cs : List FinCore) :
    qsum (fun s => geo_point p s.length) (stdin_free cs) ≤ 1 := by
  unfold stdin_free
  refine Rat.le_trans (bytes_cyl_sum_le p Hp0 Hp1 _ []) ?_
  unfold geo_mass
  change Qpow ((1 - p) * (1 / 256)) 0 ≤ 1
  rw [Qpow_0]
  exact Rat.le_refl

/- =========================================================================
   The cylinder bound over cores, and the whole-space certificate
   ========================================================================= -/

/-- The cores this bound is about: argv extending `xs`, environment extending
    `es`, file system extending `fs0` AS A LIST, standard input extending
    `bs`.  Four existentials, for the reason `in_envp_stdin_cylinder` has
    two.  The file-system prefix is a LIST prefix — the first entries of the
    association list — which is the shape the enumeration wants; a task
    describing a fire set by ONE file's contents wants
    `full_support_base_file_bound` below instead. -/
def in_full_support_cylinder (xs es : List (List (BitVec 8))) (fs0 : Fs.Fs)
    (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ aext eext fext sext,
    c = FinCore.mkFinCore (xs ++ aext) (es ++ eext) (fs0 ++ fext) (bs ++ sext)

/-- The cylinder's mass: one continuation factor per coordinate. -/
def full_support_base_cylinder_mass (ra qa re qe u v w ps : Rat)
    (xs es : List (List (BitVec 8))) (fs0 : Fs.Fs) (bs : List (BitVec 8)) : Rat :=
  strings_factor ra qa xs * strings_factor re qe es * fs_factor u v w fs0 *
    geo_mass ps bs.length

theorem full_support_base_cylinder_mass_closed_form (ra qa re qe u v w ps : Rat)
    (xs es : List (List (BitVec 8))) (fs0 : Fs.Fs) (bs : List (BitVec 8)) :
    full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs =
      (Qpow (1 - ra) xs.length * entries_geo_product qa xs) *
        (Qpow (1 - re) es.length * entries_geo_product qe es) *
        (Qpow (1 - u) fs0.length * fs_entries_product v w fs0) *
        (Qpow (1 - ps) bs.length * Qpow (1 / 256) bs.length) := by
  unfold full_support_base_cylinder_mass strings_factor
  rw [envp_factor_closed_form, envp_factor_closed_form, fs_factor_closed_form,
    geo_mass_closed_form]

/-- THE BOUND OVER CORES: any duplicate-free list of cores lying in the
    cylinder weighs at most the cylinder's mass.  Eight depths are read off
    the list, the four enumerations at those depths contain it, and each
    enumeration is bounded by its own cancellation lemma. -/
theorem base_weight_cylinder_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs es : List (List (BitVec 8))) (fs0 : Fs.Fs) (bs : List (BitVec 8))
    (cs : List FinCore) (Hnd : cs.Nodup)
    (Hcyl : ∀ c, c ∈ cs → in_full_support_cylinder xs es fs0 bs c) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤
      full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs := by
  unfold full_support_base_cylinder_mass strings_factor
  refine base_weight_product_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (envp_enum xs (cores_argv_depth cs) (cores_argv_entry_depth cs))
    (envp_enum es (cores_envp_depth cs) (cores_entry_depth cs))
    (fs_enum fs0 (cores_fs_depth cs) (cores_fs_path_depth cs)
      (cores_fs_contents_depth cs))
    (bytes_cyl bs (cores_stdin_depth cs))
    (envp_factor ra qa xs) (envp_factor re qe es) (fs_factor u v w fs0)
    (geo_mass ps bs.length) cs ?_ ?_ ?_ ?_ Hnd ?_
  · unfold strings_point
    exact envp_enum_sum_le ra qa Hra0 Hra1 Hqa0 Hqa1 _ _ xs
  · unfold strings_point
    exact envp_enum_sum_le re qe Hre0 Hre1 Hqe0 Hqe1 _ _ es
  · exact fs_enum_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 _ _ _ fs0
  · exact bytes_cyl_sum_le ps Hps0 Hps1 _ bs
  · intro c Hc
    obtain ⟨aext, eext, fext, sext, Heq⟩ := Hcyl c Hc
    have Hargv : xs.length + aext.length ≤ cores_argv_depth cs := by
      have h := cores_argv_depth_ge cs c Hc
      rw [Heq] at h
      have h2 : (xs ++ aext).length ≤ cores_argv_depth cs := h
      rw [List.length_append] at h2
      exact h2
    have Henvp : es.length + eext.length ≤ cores_envp_depth cs := by
      have h := cores_envp_depth_ge cs c Hc
      rw [Heq] at h
      have h2 : (es ++ eext).length ≤ cores_envp_depth cs := h
      rw [List.length_append] at h2
      exact h2
    have Hfs : fs0.length + fext.length ≤ cores_fs_depth cs := by
      have h := cores_fs_depth_ge cs c Hc
      rw [Heq] at h
      have h2 : (fs0 ++ fext).length ≤ cores_fs_depth cs := h
      rw [List.length_append] at h2
      exact h2
    have Hstdin : bs.length + sext.length ≤ cores_stdin_depth cs := by
      have h := cores_stdin_depth_ge cs c Hc
      rw [Heq] at h
      have h2 : (bs ++ sext).length ≤ cores_stdin_depth cs := h
      rw [List.length_append] at h2
      exact h2
    rw [Heq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply envp_enum_complete
      · omega
      · intro e He
        exact cores_argv_entry_depth_gt cs c e Hc (by
          rw [Heq]; exact List.mem_append.mpr (Or.inr He))
    · apply envp_enum_complete
      · omega
      · intro e He
        exact cores_entry_depth_gt cs c e Hc (by
          rw [Heq]; exact List.mem_append.mpr (Or.inr He))
    · apply fs_enum_complete
      · omega
      · intro e He
        refine ⟨cores_fs_path_depth_gt cs c e Hc ?_, cores_fs_contents_depth_gt cs c e Hc ?_⟩
        · rw [Heq]; exact List.mem_append.mpr (Or.inr He)
        · rw [Heq]; exact List.mem_append.mpr (Or.inr He)
    · apply bytes_cyl_In
      omega

/-- Any duplicate-free list of cores at all weighs at most `1`: the cylinder
    bound at the four empty prefixes, where every continuation factor is
    `1`. -/
theorem base_weight_mass_le_1 (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (cs : List FinCore) (Hnd : cs.Nodup) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ 1 := by
  refine Rat.le_trans (base_weight_cylinder_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    [] [] [] [] cs Hnd ?_) ?_
  · intro c _
    exact ⟨c.core_argv, c.core_envp, c.core_fs, c.core_stdin, rfl⟩
  · unfold full_support_base_cylinder_mass strings_factor geo_mass
    change (1 : Rat) * (1 : Rat) * (1 : Rat) * Qpow ((1 - ps) * (1 / 256)) 0 ≤ 1
    rw [Qpow_0]
    grind

/-- THE EXPORT: a list of records with duplicate-free cores, all lying in the
    cylinder, weighs at most the cylinder's mass.  The hypothesis is the one
    `Measure.weight_bound_T` carries, and `core_sum_map_fin_core` is the only
    step between them. -/
theorem full_support_base_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs es : List (List (BitVec 8))) (fs0 : Fs.Fs) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l → in_full_support_cylinder xs es fs0 bs (fin_core f)) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      full_support_base_cylinder_mass ra qa re qe u v w ps xs es fs0 bs := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ _
  rw [core_sum_map_fin_core]
  exact base_weight_cylinder_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    xs es fs0 bs (List.map fin_core l) Hnd (fun c Hc => by
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      exact Hcyl f Hf)

/-- UPPER CERTIFICATE: every admissible list weighs at most the declared mass
    `1`.  There is no "off the environment" disjunct to widen by, because
    there is no environment to be off: every core is in the cylinder at the
    four empty prefixes. -/
theorem full_support_base_mass_upper (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_mass := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ 1
  rw [core_sum_map_fin_core]
  exact base_weight_mass_le_1 ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    _ Hnd

/- =========================================================================
   The marginal bounds: one coordinate constrained, three charged 1
   ========================================================================= -/

/-- Fixing ONE coordinate exactly and charging the other three their whole
    declared mass.  These are the bounds a task composes the base family
    with a structured family through: a fire set described by its argv alone
    is charged the argv's own weight, and nothing about the other
    coordinates is assumed.  Each is the engine with one singleton
    enumeration and three free ones. -/
theorem base_weight_argv_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List (BitVec 8))) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_argv = xs) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ strings_point ra qa xs := by
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    [xs] (envp_free cs) (fs_free cs) (stdin_free cs)
    (strings_point ra qa xs) 1 1 1 cs ?_ ?_ ?_ ?_ Hnd ?_) ?_
  · rw [qsum_cons, qsum_nil]
    grind
  · exact envp_free_sum_le re qe Hre0 Hre1 Hqe0 Hqe1 cs
  · exact fs_free_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 cs
  · exact stdin_free_sum_le ps Hps0 Hps1 cs
  · intro c Hc
    exact ⟨by rw [Hall c Hc]; exact List.mem_cons_self .., envp_free_In cs c Hc,
      fs_free_In cs c Hc, stdin_free_In cs c Hc⟩
  · show strings_point ra qa xs * 1 * 1 * 1 ≤ strings_point ra qa xs
    grind

theorem base_weight_envp_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (es : List (List (BitVec 8))) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_envp = es) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ strings_point re qe es := by
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (argv_free cs) [es] (fs_free cs) (stdin_free cs)
    1 (strings_point re qe es) 1 1 cs ?_ ?_ ?_ ?_ Hnd ?_) ?_
  · exact argv_free_sum_le ra qa Hra0 Hra1 Hqa0 Hqa1 cs
  · rw [qsum_cons, qsum_nil]
    grind
  · exact fs_free_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 cs
  · exact stdin_free_sum_le ps Hps0 Hps1 cs
  · intro c Hc
    exact ⟨argv_free_In cs c Hc, by rw [Hall c Hc]; exact List.mem_cons_self ..,
      fs_free_In cs c Hc, stdin_free_In cs c Hc⟩
  · show (1 : Rat) * strings_point re qe es * 1 * 1 ≤ strings_point re qe es
    grind

theorem base_weight_fs_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (fs0 : Fs.Fs) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_fs = fs0) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ fs_point u v w fs0 := by
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (argv_free cs) (envp_free cs) [fs0] (stdin_free cs)
    1 1 (fs_point u v w fs0) 1 cs ?_ ?_ ?_ ?_ Hnd ?_) ?_
  · exact argv_free_sum_le ra qa Hra0 Hra1 Hqa0 Hqa1 cs
  · exact envp_free_sum_le re qe Hre0 Hre1 Hqe0 Hqe1 cs
  · rw [qsum_cons, qsum_nil]
    grind
  · exact stdin_free_sum_le ps Hps0 Hps1 cs
  · intro c Hc
    exact ⟨argv_free_In cs c Hc, envp_free_In cs c Hc,
      by rw [Hall c Hc]; exact List.mem_cons_self .., stdin_free_In cs c Hc⟩
  · show (1 : Rat) * 1 * fs_point u v w fs0 * 1 ≤ fs_point u v w fs0
    grind

/-- The standard-input coordinate's two bounds, in the shapes the other
    families export them: a list drawn from one LENGTH slice weighs at most
    `ps * (1 - ps) ^ n`, and a list confined to standard inputs of length at
    most `n` weighs at most `1 - (1 - ps) ^ (n + 1)`.  Neither fixes any
    other coordinate.  The second MISSES THE TAIL, and the tail is what
    `full_support_base_mass_not_attained` is made of. -/
theorem base_weight_stdin_slice_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_stdin.length = n) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ ps * Qpow (1 - ps) n := by
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (argv_free cs) (envp_free cs) (fs_free cs) (byte_lists n)
    1 1 1 (ps * Qpow (1 - ps) n) cs ?_ ?_ ?_ ?_ Hnd ?_) ?_
  · exact argv_free_sum_le ra qa Hra0 Hra1 Hqa0 Hqa1 cs
  · exact envp_free_sum_le re qe Hre0 Hre1 Hqe0 Hqe1 cs
  · exact fs_free_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 cs
  · rw [byte_lists_sum]
    exact Rat.le_refl
  · intro c Hc
    refine ⟨argv_free_In cs c Hc, envp_free_In cs c Hc, fs_free_In cs c Hc, ?_⟩
    rw [← Hall c Hc]
    exact byte_lists_complete _
  · show (1 : Rat) * 1 * 1 * (ps * Qpow (1 - ps) n) ≤ ps * Qpow (1 - ps) n
    grind

theorem base_weight_bound_by_max_length (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_stdin.length ≤ n) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ 1 - Qpow (1 - ps) (n + 1) := by
  refine Rat.le_trans (base_weight_product_bound ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (argv_free cs) (envp_free cs) (fs_free cs) (short_inputs (n + 1))
    1 1 1 (1 - Qpow (1 - ps) (n + 1)) cs ?_ ?_ ?_ ?_ Hnd ?_) ?_
  · exact argv_free_sum_le ra qa Hra0 Hra1 Hqa0 Hqa1 cs
  · exact envp_free_sum_le re qe Hre0 Hre1 Hqe0 Hqe1 cs
  · exact fs_free_sum_le u v w Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 cs
  · rw [short_inputs_sum, geo_prefix_sum_closed]
    exact Rat.le_refl
  · intro c Hc
    refine ⟨argv_free_In cs c Hc, envp_free_In cs c Hc, fs_free_In cs c Hc, ?_⟩
    exact short_inputs_complete _ _ (by have := Hall c Hc; omega)
  · show (1 : Rat) * 1 * 1 * (1 - Qpow (1 - ps) (n + 1)) ≤ 1 - Qpow (1 - ps) (n + 1)
    grind

/- =========================================================================
   The file-contents marginal: one entry constrained, the rest free
   ========================================================================= -/

/-- The cores the composability bound prices: the file at `pth` — what
    `fs_file` reads, the first entry with that key, or nothing — EXTENDS
    `bs`.  Nothing else about the file system is fixed: not its entry count,
    not any other entry, not the position of the entry at `pth`. -/
def file_at_extends (pth : Fs.path) (bs : List (BitVec 8)) (c : FinCore) : Prop :=
  ∃ ext, fs_file pth c.core_fs = bs ++ ext

/-- THE INJECTION.  Strip the first `n` bytes off the contents of the first
    entry keyed `pth`, leave everything else alone.  On the cores
    `file_at_extends pth bs` describes, with `n = bs.length`, it is
    weight-preserving up to the one factor `geo_mass w bs.length`
    (`base_weight_strip`) and injective (`core_strip_inj`), and those two
    facts are the whole of the marginal bound. -/
def fs_strip (pth : Fs.path) (n : Nat) : Fs.Fs → Fs.Fs
  | [] => []
  | (q, d) :: r =>
    if Fs.path_eqb pth q then (q, d.drop n) :: r else (q, d) :: fs_strip pth n r

def core_strip (pth : Fs.path) (n : Nat) (c : FinCore) : FinCore :=
  FinCore.mkFinCore c.core_argv c.core_envp (fs_strip pth n c.core_fs) c.core_stdin

theorem skipn_length_app {A : Type} (l1 l2 : List A) :
    (l1 ++ l2).drop l1.length = l2 := by
  induction l1 with
  | nil => rfl
  | cons x l1 ih => exact ih

theorem Qpow_plus_exp (x : Rat) (m n : Nat) :
    Qpow x (m + n) = Qpow x m * Qpow x n := by
  induction m with
  | zero => rw [Nat.zero_add, Qpow_0]; grind
  | succ m ih => rw [Nat.succ_add, Qpow_succ, ih, Qpow_succ]; grind

/-- A byte string that extends `bs` weighs `geo_mass` of the prefix times the
    weight of what follows: the single identity the injection pays with. -/
theorem geo_point_app (p : Rat) (bs ext : List (BitVec 8)) :
    geo_point p (bs ++ ext).length = geo_mass p bs.length * geo_point p ext.length := by
  unfold geo_point geo_mass
  rw [List.length_append, Qpow_plus_exp]
  grind

theorem fs_strip_zero (pth : Fs.path) (fs : Fs.Fs) : fs_strip pth 0 fs = fs := by
  induction fs with
  | nil => rfl
  | cons hd fs ih =>
    obtain ⟨q, d⟩ := hd
    show (if Fs.path_eqb pth q then (q, d.drop 0) :: fs else (q, d) :: fs_strip pth 0 fs) =
      (q, d) :: fs
    by_cases h : Fs.path_eqb pth q = true
    · rw [ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ih]

theorem fs_strip_cons_same (pth : Fs.path) (n : Nat) (q : Fs.path) (d : List (BitVec 8))
    (fs : Fs.Fs) (h : Fs.path_eqb pth q = true) :
    fs_strip pth n ((q, d) :: fs) = (q, d.drop n) :: fs := by
  show (if Fs.path_eqb pth q then (q, d.drop n) :: fs else (q, d) :: fs_strip pth n fs) = _
  rw [ite_eq_left h]

theorem fs_strip_cons_other (pth : Fs.path) (n : Nat) (q : Fs.path) (d : List (BitVec 8))
    (fs : Fs.Fs) (h : ¬ Fs.path_eqb pth q = true) :
    fs_strip pth n ((q, d) :: fs) = (q, d) :: fs_strip pth n fs := by
  show (if Fs.path_eqb pth q then (q, d.drop n) :: fs else (q, d) :: fs_strip pth n fs) = _
  rw [ite_eq_right h]

theorem fs_lookup_of_fs_file_cons (pth : Fs.path) (fs : Fs.Fs) (b : BitVec 8)
    (l : List (BitVec 8)) (H : fs_file pth fs = b :: l) :
    Fs.fs_lookup fs pth = some (b :: l) := by
  unfold fs_file at H
  rcases hl : Fs.fs_lookup fs pth with _ | d
  · rw [hl] at H
    exact absurd H (by simp)
  · rw [hl] at H
    dsimp only [] at H
    rw [H]

theorem fs_factor_strip (u v w : Rat) (pth : Fs.path) (bs ext : List (BitVec 8))
    (fs : Fs.Fs) (Hlk : Fs.fs_lookup fs pth = some (bs ++ ext)) :
    fs_factor u v w fs =
      geo_mass w bs.length * fs_factor u v w (fs_strip pth bs.length fs) := by
  induction fs with
  | nil => exact absurd Hlk (by simp [Fs.fs_lookup])
  | cons hd fs ih =>
    obtain ⟨q, d⟩ := hd
    by_cases hq : Fs.path_eqb pth q = true
    · have hd_eq : d = bs ++ ext := by
        have h := Hlk
        show d = bs ++ ext
        rw [show Fs.fs_lookup ((q, d) :: fs) pth =
          (if Fs.path_eqb pth q then some d else Fs.fs_lookup fs pth) from rfl,
          ite_eq_left hq] at h
        exact Option.some.inj h
      subst hd_eq
      rw [fs_strip_cons_same pth bs.length q (bs ++ ext) fs hq]
      rw [fs_factor_cons, fs_factor_cons, skipn_length_app, geo_point_app]
      grind
    · have hlk' : Fs.fs_lookup fs pth = some (bs ++ ext) := by
        have h := Hlk
        rw [show Fs.fs_lookup ((q, d) :: fs) pth =
          (if Fs.path_eqb pth q then some d else Fs.fs_lookup fs pth) from rfl,
          ite_eq_right hq] at h
        exact h
      rw [fs_strip_cons_other pth bs.length q d fs hq]
      rw [fs_factor_cons, fs_factor_cons, ih hlk']
      grind

theorem fs_strip_inj (pth : Fs.path) (bs : List (BitVec 8)) :
    ∀ (fs1 fs2 : Fs.Fs) (ext1 ext2 : List (BitVec 8)),
      Fs.fs_lookup fs1 pth = some (bs ++ ext1) →
      Fs.fs_lookup fs2 pth = some (bs ++ ext2) →
      fs_strip pth bs.length fs1 = fs_strip pth bs.length fs2 → fs1 = fs2 := by
  intro fs1
  induction fs1 with
  | nil =>
    intro fs2 ext1 ext2 H1 _ _
    exact absurd H1 (by simp [Fs.fs_lookup])
  | cons hd1 fs1 ih =>
    obtain ⟨q1, d1⟩ := hd1
    intro fs2 ext1 ext2 H1 H2 Hs
    match fs2 with
    | [] => exact absurd H2 (by simp [Fs.fs_lookup])
    | (q2, d2) :: fs2 =>
      have H1' : (if Fs.path_eqb pth q1 then some d1 else Fs.fs_lookup fs1 pth) =
          some (bs ++ ext1) := H1
      have H2' : (if Fs.path_eqb pth q2 then some d2 else Fs.fs_lookup fs2 pth) =
          some (bs ++ ext2) := H2
      by_cases h1 : Fs.path_eqb pth q1 = true
      · by_cases h2 : Fs.path_eqb pth q2 = true
        · rw [ite_eq_left h1] at H1'
          rw [ite_eq_left h2] at H2'
          have e1 : d1 = bs ++ ext1 := Option.some.inj H1'
          have e2 : d2 = bs ++ ext2 := Option.some.inj H2'
          rw [fs_strip_cons_same pth bs.length q1 d1 fs1 h1,
            fs_strip_cons_same pth bs.length q2 d2 fs2 h2] at Hs
          obtain ⟨hp, hfs⟩ := List.cons.inj Hs
          obtain ⟨hq, hd⟩ := Prod.mk.injEq q1 (d1.drop bs.length) q2 (d2.drop bs.length) |>.mp hp
          rw [e1, e2, skipn_length_app, skipn_length_app] at hd
          rw [hq, e1, e2, hd, hfs]
        · rw [ite_eq_left h1] at H1'
          rw [ite_eq_right h2] at H2'
          rw [fs_strip_cons_same pth bs.length q1 d1 fs1 h1,
            fs_strip_cons_other pth bs.length q2 d2 fs2 h2] at Hs
          obtain ⟨hp, _⟩ := List.cons.inj Hs
          obtain ⟨hq, _⟩ := Prod.mk.injEq q1 (d1.drop bs.length) q2 d2 |>.mp hp
          rw [← hq] at h2
          exact absurd h1 h2
      · by_cases h2 : Fs.path_eqb pth q2 = true
        · rw [ite_eq_right h1] at H1'
          rw [ite_eq_left h2] at H2'
          rw [fs_strip_cons_other pth bs.length q1 d1 fs1 h1,
            fs_strip_cons_same pth bs.length q2 d2 fs2 h2] at Hs
          obtain ⟨hp, _⟩ := List.cons.inj Hs
          obtain ⟨hq, _⟩ := Prod.mk.injEq q1 d1 q2 (d2.drop bs.length) |>.mp hp
          rw [← hq] at h2
          exact absurd h2 h1
        · rw [ite_eq_right h1] at H1'
          rw [ite_eq_right h2] at H2'
          rw [fs_strip_cons_other pth bs.length q1 d1 fs1 h1,
            fs_strip_cons_other pth bs.length q2 d2 fs2 h2] at Hs
          obtain ⟨hp, hfs⟩ := List.cons.inj Hs
          obtain ⟨hq, hd⟩ := Prod.mk.injEq q1 d1 q2 d2 |>.mp hp
          have ih' := ih fs2 ext1 ext2 H1' H2' hfs
          rw [hq, hd, ih']

theorem base_weight_strip (ra qa re qe u v w ps : Rat) (pth : Fs.path)
    (bs : List (BitVec 8)) (c : FinCore) (Hext : file_at_extends pth bs c) :
    base_weight ra qa re qe u v w ps c =
      geo_mass w bs.length *
        base_weight ra qa re qe u v w ps (core_strip pth bs.length c) := by
  obtain ⟨ext, Hext'⟩ := Hext
  unfold base_weight core_strip
  rcases bs with _ | ⟨b, bs'⟩
  · show strings_point ra qa c.core_argv * strings_point re qe c.core_envp *
      fs_point u v w c.core_fs * geo_point ps c.core_stdin.length =
      geo_mass w ([] : List (BitVec 8)).length *
        (strings_point ra qa c.core_argv * strings_point re qe c.core_envp *
          fs_point u v w (fs_strip pth 0 c.core_fs) * geo_point ps c.core_stdin.length)
    rw [fs_strip_zero]
    change _ = geo_mass w 0 * _
    unfold geo_mass
    rw [Qpow_0]
    grind
  · have hlk : Fs.fs_lookup c.core_fs pth = some ((b :: bs') ++ ext) :=
      fs_lookup_of_fs_file_cons pth c.core_fs b (bs' ++ ext) (by simpa using Hext')
    unfold fs_point
    rw [fs_factor_strip u v w pth (b :: bs') ext c.core_fs hlk]
    dsimp only [core_strip]
    grind

theorem core_strip_inj (pth : Fs.path) (bs : List (BitVec 8)) (c1 c2 : FinCore)
    (H1 : file_at_extends pth bs c1) (H2 : file_at_extends pth bs c2)
    (Heq : core_strip pth bs.length c1 = core_strip pth bs.length c2) : c1 = c2 := by
  obtain ⟨ext1, H1'⟩ := H1
  obtain ⟨ext2, H2'⟩ := H2
  have Ha : c1.core_argv = c2.core_argv := by
    simpa [core_strip] using congrArg FinCore.core_argv Heq
  have He : c1.core_envp = c2.core_envp := by
    simpa [core_strip] using congrArg FinCore.core_envp Heq
  have Hf : fs_strip pth bs.length c1.core_fs = fs_strip pth bs.length c2.core_fs := by
    simpa [core_strip] using congrArg FinCore.core_fs Heq
  have Hs : c1.core_stdin = c2.core_stdin := by
    simpa [core_strip] using congrArg FinCore.core_stdin Heq
  rcases bs with _ | ⟨b, bs'⟩
  · change fs_strip pth 0 c1.core_fs = fs_strip pth 0 c2.core_fs at Hf
    rw [fs_strip_zero pth c1.core_fs, fs_strip_zero pth c2.core_fs] at Hf
    cases c1; cases c2
    simp_all
  · have Hfs : c1.core_fs = c2.core_fs :=
      fs_strip_inj pth (b :: bs') c1.core_fs c2.core_fs ext1 ext2
        (fs_lookup_of_fs_file_cons pth c1.core_fs b (bs' ++ ext1) (by simpa using H1'))
        (fs_lookup_of_fs_file_cons pth c2.core_fs b (bs' ++ ext2) (by simpa using H2'))
        Hf
    cases c1
    cases c2
    simp_all

theorem core_strip_argv (pth : Fs.path) (n : Nat) (c : FinCore) :
    (core_strip pth n c).core_argv = c.core_argv := rfl

theorem NoDup_map_core_strip (pth : Fs.path) (bs : List (BitVec 8))
    (cs : List FinCore) (Hall : ∀ c, c ∈ cs → file_at_extends pth bs c)
    (Hnd : cs.Nodup) : (cs.map (core_strip pth bs.length)).Nodup := by
  apply NoDup_map_inj
  · intro x y Hx Hy Heq
    exact core_strip_inj pth bs x y (Hall x Hx) (Hall y Hy) Heq
  · exact Hnd

theorem qsum_base_weight_strip (ra qa re qe u v w ps : Rat) (pth : Fs.path)
    (bs : List (BitVec 8)) (cs : List FinCore)
    (Hall : ∀ c, c ∈ cs → file_at_extends pth bs c) :
    qsum (base_weight ra qa re qe u v w ps) cs =
      geo_mass w bs.length *
        qsum (base_weight ra qa re qe u v w ps) (cs.map (core_strip pth bs.length)) := by
  rw [qsum_map]
  calc qsum (base_weight ra qa re qe u v w ps) cs
      = qsum (fun c => geo_mass w bs.length *
          base_weight ra qa re qe u v w ps (core_strip pth bs.length c)) cs :=
        qsum_ext _ _ _ (fun c Hc => base_weight_strip ra qa re qe u v w ps pth bs c
          (Hall c Hc))
    _ = geo_mass w bs.length *
          qsum (fun c => base_weight ra qa re qe u v w ps
            (core_strip pth bs.length c)) cs :=
        qsum_scale _ _ _

/-- THE FILE-CONTENTS MARGINAL: cores whose file at `pth` extends `bs` weigh
    at most `geo_mass w bs.length` — the prefix's cylinder mass on the
    contents coordinate, with the entry count, every other entry, the path's
    own bytes and the other three coordinates all charged `1`.  At `bs = []`
    the hypothesis is vacuous and the bound is the whole-space `1`. -/
theorem base_weight_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (pth : Fs.path) (bs : List (BitVec 8)) (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → file_at_extends pth bs c) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤ geo_mass w bs.length := by
  rw [qsum_base_weight_strip ra qa re qe u v w ps pth bs cs Hall]
  refine Rat.le_trans (Qmult_le_compat_nonneg (Rat.le_refl)
    (base_weight_mass_le_1 ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
      _ (NoDup_map_core_strip pth bs cs Hall Hnd))
    (geo_mass_nonneg w bs.length Hw1)
    (qsum_nonneg _ _ (fun x _ => base_weight_nonneg ra qa re qe u v w ps
      Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 x))) ?_
  show geo_mass w bs.length * 1 ≤ geo_mass w bs.length
  grind

/-- THE COMPOSABILITY BOUND: cores whose argv is `xs` and whose file at
    `pth` extends `bs` weigh at most
    `strings_point ra qa xs * geo_mass w bs.length`, the remaining
    coordinates' total being under `1`.  The injection pays the contents
    factor and preserves argv (`core_strip_argv`), so the stripped list is
    one `base_weight_argv_bound` applies to. -/
theorem base_weight_argv_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List (BitVec 8))) (pth : Fs.path) (bs : List (BitVec 8))
    (cs : List FinCore) (Hnd : cs.Nodup)
    (Hall : ∀ c, c ∈ cs → c.core_argv = xs ∧ file_at_extends pth bs c) :
    qsum (base_weight ra qa re qe u v w ps) cs ≤
      strings_point ra qa xs * geo_mass w bs.length := by
  rw [qsum_base_weight_strip ra qa re qe u v w ps pth bs cs
    (fun c Hc => (Hall c Hc).2)]
  refine Rat.le_trans (Qmult_le_compat_nonneg (Rat.le_refl)
    (base_weight_argv_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs _
      (NoDup_map_core_strip pth bs cs (fun c Hc => (Hall c Hc).2) Hnd)
      (fun c Hc => ?_))
    (geo_mass_nonneg w bs.length Hw1)
    (qsum_nonneg _ _ (fun x _ => base_weight_nonneg ra qa re qe u v w ps
      Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 x))) ?_
  · obtain ⟨c0, Hc0, rfl⟩ := List.mem_map.mp Hc
    rw [core_strip_argv]
    exact (Hall c0 Hc0).1
  · show geo_mass w bs.length * strings_point ra qa xs ≤
      strings_point ra qa xs * geo_mass w bs.length
    grind

/- =========================================================================
   The marginal exports, on records
   ========================================================================= -/

theorem full_support_base_argv_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List (BitVec 8))) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_argv = xs) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      strings_point ra qa xs := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ strings_point ra qa xs
  rw [core_sum_map_fin_core]
  refine base_weight_argv_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_envp_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (es : List (List (BitVec 8))) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_envp = es) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      strings_point re qe es := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ strings_point re qe es
  rw [core_sum_map_fin_core]
  refine base_weight_envp_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 es _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_fs_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (fs0 : Fs.Fs) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_image_fs = fs0) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      fs_point u v w fs0 := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ fs_point u v w fs0
  rw [core_sum_map_fin_core]
  refine base_weight_fs_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 fs0 _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_slice_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_stdin.length = n) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      ps * Qpow (1 - ps) n := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ ps * Qpow (1 - ps) n
  rw [core_sum_map_fin_core]
  refine base_weight_stdin_slice_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_bound_by_max_length (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (n : Nat) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_stdin.length ≤ n) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      1 - Qpow (1 - ps) (n + 1) := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ 1 - Qpow (1 - ps) (n + 1)
  rw [core_sum_map_fin_core]
  refine base_weight_bound_by_max_length ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 n _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (pth : Fs.path) (bs : List (BitVec 8)) (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → file_at_extends pth bs (fin_core f)) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      geo_mass w bs.length := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤ geo_mass w bs.length
  rw [core_sum_map_fin_core]
  exact base_weight_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 pth bs _
    Hnd (fun c Hc => by
      obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
      exact Hall f Hf)

/-- The composability bound at the `_argv1` driver shape: argv is `[prog; pth]`
    and the file at `pth` extends `bs`.  `path_argv` is the argv shape the
    file families' `_argv1` constructors build, so a task that already
    couples its argv to its path through it lands here directly. -/
theorem full_support_base_argv_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (xs : List (List (BitVec 8))) (pth : Fs.path) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l → f.fin_argv = xs ∧ file_at_extends pth bs (fin_core f)) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      strings_point ra qa xs * geo_mass w bs.length := by
  show core_sum (base_weight ra qa re qe u v w ps) l ≤
    strings_point ra qa xs * geo_mass w bs.length
  rw [core_sum_map_fin_core]
  refine base_weight_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 xs pth bs _ Hnd ?_
  intro c Hc
  obtain ⟨f, Hf, rfl⟩ := List.mem_map.mp Hc
  exact Hall f Hf

theorem full_support_base_path_argv_file_bound (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (prog : List (BitVec 8)) (pth : Fs.path) (bs : List (BitVec 8))
    (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup)
    (Hall : ∀ f, f ∈ l →
      f.fin_argv = path_argv prog pth ∧ file_at_extends pth bs (fin_core f)) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l ≤
      strings_point ra qa [prog, pth] * geo_mass w bs.length :=
  full_support_base_argv_file_bound ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
    Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    (path_argv prog pth) pth bs l Hnd Hall

/- =========================================================================... and this mass is a SUPREMUM and not a maximum either
   ========================================================================= -/

/-- For `ps < 1` NO admissible list weighs the declared mass.  The proof is
    `stdin_envp_geometric_mass_not_attained`'s unchanged: the list's own
    longest standard input is a horizon, and beyond it sits a positive tail
    the list does not collect.  Only `ps < 1` is asked for — the shortfall is
    already there on the standard-input axis, so the other seven rates may be
    as degenerate as they like. -/
theorem full_support_base_mass_not_attained (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Hlt : ps < 1) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l <
      (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
        Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_mass := by
  show core_sum (base_weight ra qa re qe u v w ps) l < 1
  generalize hN : list_max (l.map (fun f => f.fin_stdin.length)) = N
  have h1 : core_sum (base_weight ra qa re qe u v w ps) l ≤
      1 - Qpow (1 - ps) (N + 1) :=
    full_support_base_bound_by_max_length ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
      Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 N l Hnd
      (fun f Hf => by
        have hin : f.fin_stdin.length ∈ l.map (fun g => g.fin_stdin.length) :=
          List.mem_map.mpr ⟨f, Hf, rfl⟩
        have := list_max_ge _ _ hin
        omega)
  have hpos : 0 < Qpow (1 - ps) (N + 1) := Qpow_pos _ _ (by grind)
  grind

theorem full_support_base_mass_supremum_not_maximum (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Hlt : ps < 1) (l : List FinProcInput) (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l =
        (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_mass) :=
  Rat.ne_of_lt (full_support_base_mass_not_attained ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    Hlt l Hnd)


/- =========================================================================
   The file-system witness family
   ========================================================================= -/

/-- THE FILE-SYSTEM WITNESS FAMILY: every list of exactly `m` pairs whose
    paths are shorter than `Lp` and whose contents are shorter than `Lc`,
    and the union of those over `m < M`.  It is `envps_len` and `envps_upto`
    with a pair where they have an entry, and it is duplicate-free for the
    same reason (`fss_len_nodup`).  `fs_enum` is not reused, for the reason
    `envp_enum` is not: the certificate needs a duplicate-free list and the
    bounds' enumeration is not one. -/
def fss_len (Lp Lc : Nat) : Nat → List Fs.Fs
  | 0 => [[]]
  | m + 1 => (short_inputs Lp).flatMap (fun pth =>
      (short_inputs Lc).flatMap (fun d =>
        (fss_len Lp Lc m).map (fun fs => (pth, d) :: fs)))

theorem fss_len_zero (Lp Lc : Nat) : fss_len Lp Lc 0 = [[]] := rfl

theorem fss_len_succ (Lp Lc m : Nat) :
    fss_len Lp Lc (m + 1) = (short_inputs Lp).flatMap (fun pth =>
      (short_inputs Lc).flatMap (fun d =>
        (fss_len Lp Lc m).map (fun fs => (pth, d) :: fs))) := rfl

/-- Every file system of FEWER than `M` pairs, each path shorter than `Lp`
    and each contents shorter than `Lc`, as a list.  `envps_upto`'s
    construction, one coordinate deeper. -/
def fss_upto (Lp Lc : Nat) : Nat → List Fs.Fs
  | 0 => []
  | M + 1 => fss_len Lp Lc M ++ fss_upto Lp Lc M

theorem fss_upto_zero (Lp Lc : Nat) : fss_upto Lp Lc 0 = [] := rfl

theorem fss_upto_succ (Lp Lc M : Nat) :
    fss_upto Lp Lc (M + 1) = fss_len Lp Lc M ++ fss_upto Lp Lc M := rfl

theorem fss_len_In_length (Lp Lc : Nat) : ∀ (m : Nat) (fs : Fs.Fs),
    fs ∈ fss_len Lp Lc m → fs.length = m := by
  intro m
  induction m with
  | zero =>
    intro fs Hfs
    rw [fss_len_zero] at Hfs
    rcases List.mem_cons.mp Hfs with h | h
    · rw [h]; rfl
    · exact absurd h (List.not_mem_nil)
  | succ m ih =>
    intro fs Hfs
    rw [fss_len_succ] at Hfs
    obtain ⟨pth, _, Hin⟩ := List.mem_flatMap.mp Hfs
    obtain ⟨d, _, Hin2⟩ := List.mem_flatMap.mp Hin
    obtain ⟨fs', Hfs', rfl⟩ := List.mem_map.mp Hin2
    rw [List.length_cons, ih fs' Hfs']

/-- ... and it repeats nothing: distinct paths give disjoint blocks at the
    outer `flat_map`, distinct contents give disjoint blocks at the inner
    one, and within a block consing a fixed pair is injective.  The third
    condition is the `List.tl` injectivity fact, read off
    the cons instead — `(pth, d) :: fs = (pth', d') :: fs'` has equal
    heads. -/
theorem fss_len_nodup (Lp Lc : Nat) : ∀ m, (fss_len Lp Lc m).Nodup := by
  intro m
  induction m with
  | zero =>
    rw [fss_len_zero, List.nodup_cons]
    exact ⟨fun h => absurd h (List.not_mem_nil), List.nodup_nil⟩
  | succ m ih =>
    rw [fss_len_succ]
    refine NoDup_flat_map _ _ (short_inputs_nodup Lp) ?_ ?_
    · intro pth _
      refine NoDup_flat_map _ _ (short_inputs_nodup Lc) ?_ ?_
      · intro d _
        apply NoDup_map_inj
        · intro x y _ _ heq
          exact (List.cons.inj heq).2
        · exact ih
      · intro d1 d2 fs _ _ H1 H2
        obtain ⟨x1, _, h1⟩ := List.mem_map.mp H1
        obtain ⟨x2, _, h2⟩ := List.mem_map.mp H2
        exact congrArg Prod.snd (List.cons.inj (h1.trans h2.symm)).1
    · intro p1 p2 fs _ _ H1 H2
      obtain ⟨d1, _, H1⟩ := List.mem_flatMap.mp H1
      obtain ⟨x1, _, h1⟩ := List.mem_map.mp H1
      obtain ⟨d2, _, H2⟩ := List.mem_flatMap.mp H2
      obtain ⟨x2, _, h2⟩ := List.mem_map.mp H2
      exact congrArg Prod.fst (List.cons.inj (h1.trans h2.symm)).1

theorem fss_upto_In_length (Lp Lc : Nat) : ∀ (M : Nat) (fs : Fs.Fs),
    fs ∈ fss_upto Lp Lc M → fs.length < M := by
  intro M
  induction M with
  | zero => intro fs Hfs; cases Hfs
  | succ M ih =>
    intro fs Hfs
    rw [fss_upto_succ] at Hfs
    rcases List.mem_append.mp Hfs with h | h
    · rw [fss_len_In_length Lp Lc M fs h]; omega
    · have := ih fs h; omega

theorem fss_upto_nodup (Lp Lc : Nat) : ∀ M, (fss_upto Lp Lc M).Nodup := by
  intro M
  induction M with
  | zero => exact List.nodup_nil
  | succ M ih =>
    rw [fss_upto_succ, List.nodup_append]
    refine ⟨fss_len_nodup Lp Lc M, ih, ?_⟩
    intro fs Hin1 fs2 Hin2 h
    have h1 := fss_len_In_length Lp Lc M fs Hin1
    have h2 := fss_upto_In_length Lp Lc M fs2 Hin2
    rw [← h] at h2
    rw [h1] at h2
    omega

/-- ONE FULL ENTRY-COUNT SLICE of file systems weighs a power, as
    `qsum_entries_geo_product_envps_len` does for environments; the base is
    the PRODUCT of what the path enumeration and the contents enumeration
    collect, because each slot draws both. -/
theorem qsum_fs_entries_product_fss_len (v w : Rat) (Lp Lc m : Nat) :
    qsum (fs_entries_product v w) (fss_len Lp Lc m) =
      Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m := by
  induction m with
  | zero =>
    rw [fss_len_zero, qsum_cons, qsum_nil, fs_entries_product_nil, Qpow_0]
    grind
  | succ m ih =>
    rw [fss_len_succ, qsum_flat_map]
    rw [qsum_ext
      (fun pth => qsum (fs_entries_product v w)
        ((short_inputs Lc).flatMap (fun d =>
          (fss_len Lp Lc m).map (fun fs => (pth, d) :: fs))))
      (fun pth => (Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m *
        (1 - Qpow (1 - w) Lc)) * geo_point v pth.length) _ ?_]
    · rw [qsum_scale, short_inputs_sum, geo_prefix_sum_closed, Qpow_succ]
      grind
    · intro pth _
      rw [qsum_flat_map]
      rw [qsum_ext
        (fun d => qsum (fs_entries_product v w)
          ((fss_len Lp Lc m).map (fun fs => (pth, d) :: fs)))
        (fun d => (Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m *
          geo_point v pth.length) * geo_point w d.length) _ ?_]
      · rw [qsum_scale, short_inputs_sum, geo_prefix_sum_closed]
        grind
      · intro d _
        rw [qsum_map]
        rw [qsum_ext (fun fs => fs_entries_product v w ((pth, d) :: fs))
          (fun fs => (geo_point v pth.length * geo_point w d.length) *
            fs_entries_product v w fs) _ (fun fs _ => fs_entries_product_cons v w pth d fs)]
        rw [qsum_scale, ih]
        grind

theorem qsum_fs_point_fss_len (u v w : Rat) (Lp Lc m : Nat) :
    qsum (fs_point u v w) (fss_len Lp Lc m) =
      u * Qpow (1 - u) m * Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) m := by
  rw [qsum_ext (fs_point u v w)
    (fun fs => (u * Qpow (1 - u) m) * fs_entries_product v w fs) _
    (fun fs Hfs => by
      rw [fs_point_closed_form, fss_len_In_length Lp Lc m fs Hfs])]
  rw [qsum_scale, qsum_fs_entries_product_fss_len]

/-- The partial sum over entry counts is `envp_prefix_sum` at the product
    base — the same `Fixpoint`, because the file-system coordinate is the
    environment coordinate with a different slot total. -/
theorem qsum_fs_point_fss_upto (u v w : Rat) (Lp Lc M : Nat) :
    qsum (fs_point u v w) (fss_upto Lp Lc M) =
      envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M := by
  induction M with
  | zero => rw [fss_upto_zero, qsum_nil, envp_prefix_sum_zero]
  | succ M ih =>
    rw [fss_upto_succ, qsum_app, ih, qsum_fs_point_fss_len, envp_prefix_sum_succ]

/- =========================================================================
   The margin arithmetic, four factors deep
   ========================================================================= -/

/-- TWO FACTORS IN `[0, 1]` COMPOSE THEIR MARGINS: if each falls short of
    `1` by at most its margin, the product falls short by at most the sum.
    `Qmargins_three` is this at three factors with a different hypothesis
    shape; this form asks only that the two factors be in the unit
    interval, which is what lets it be applied to a running product
    without tracking which margins are under `1` — an entry-length margin
    `M * x` need not be.  The proof is one square: `x * y` exceeds
    `x + y - 1` by `(1 - x) * (1 - y)`. -/
theorem Qprod_margin (x y a b : Rat) (_Hx0 : 0 ≤ x) (Hx1 : x ≤ 1) (_Hy0 : 0 ≤ y)
    (Hy1 : y ≤ 1) (Ha : 1 - a ≤ x) (Hb : 1 - b ≤ y) :
    1 - (a + b) ≤ x * y := by
  have hsq : 0 ≤ (1 - x) * (1 - y) := Rat.mul_nonneg (by grind) (by grind)
  have h1 : x + y - 1 ≤ x * y := by grind
  have h2 : (1 - a) + (1 - b) - 1 ≤ x + y - 1 := by grind
  grind

/-- A product of two numbers in the unit interval is in the unit
    interval. -/
theorem Qmult_unit (x y : Rat) (Hx0 : 0 ≤ x) (Hx1 : x ≤ 1) (Hy0 : 0 ≤ y)
    (Hy1 : y ≤ 1) : 0 ≤ x * y ∧ x * y ≤ 1 := by
  refine ⟨Rat.mul_nonneg Hx0 Hy0, ?_⟩
  refine Rat.le_trans (Qmult_le_compat_nonneg (a := x) (b := 1) (c := y) (d := 1)
    Hx1 Hy1 Hx0 Hy0) ?_
  grind

/-- The partial sum is nonnegative term by term. -/
theorem envp_prefix_sum_nonneg (r G : Rat) (M : Nat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (HG0 : 0 ≤ G) : 0 ≤ envp_prefix_sum r G M := by
  induction M with
  | zero => rw [envp_prefix_sum_zero]; exact Rat.le_refl
  | succ M ih =>
    rw [envp_prefix_sum_succ]
    exact Qplus_nonneg _ _ (Rat.mul_nonneg
      (Rat.mul_nonneg Hr0 (Qpow_nonneg _ _ (by grind))) (Qpow_nonneg _ _ HG0)) ih

/-- The partial sum is under `1 - (1 - r) ^ M` because each slot collects
    at most `1`. -/
theorem envp_prefix_sum_le (r G : Rat) (M : Nat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (HG0 : 0 ≤ G) (HG1 : G ≤ 1) :
    envp_prefix_sum r G M ≤ 1 - Qpow (1 - r) M := by
  induction M with
  | zero =>
    rw [envp_prefix_sum_zero, Qpow_0]
    grind
  | succ M ih =>
    rw [envp_prefix_sum_succ, Qpow_succ]
    have hrP : 0 ≤ r * Qpow (1 - r) M :=
      Rat.mul_nonneg Hr0 (Qpow_nonneg _ _ (by grind))
    have hG1 : Qpow G M ≤ 1 := Qpow_le_1 _ _ HG0 HG1
    refine Rat.le_trans (b := r * Qpow (1 - r) M * 1 + (1 - Qpow (1 - r) M)) ?_ ?_
    · exact Qplus_le_compat (Rat.mul_le_mul_of_nonneg_left hG1 hrP) ih
    · grind

/-- The partial sum is in the unit interval. -/
theorem envp_prefix_sum_unit (r G : Rat) (M : Nat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (HG0 : 0 ≤ G) (HG1 : G ≤ 1) :
    0 ≤ envp_prefix_sum r G M ∧ envp_prefix_sum r G M ≤ 1 := by
  refine ⟨envp_prefix_sum_nonneg r G M Hr0 Hr1 HG0, ?_⟩
  refine Rat.le_trans (envp_prefix_sum_le r G M Hr0 Hr1 HG0 HG1) ?_
  exact (geo_head_unit r M Hr0 Hr1).2

/-- ONE STRING COORDINATE'S MARGIN: its partial sum at depths `(M, L)` is
    within `M * (1 - q) ^ L + (1 - r) ^ M` of `1` — the entry-length
    shortfall over `M` slots (`Qpow_one_minus_lower`) plus the entry-count
    tail, composed by `Qprod_margin` and put under the sum by
    `envp_prefix_sum_lower`.  No strict hypothesis appears; the strictness
    is spent choosing the depths. -/
theorem strings_prefix_margin (r q : Rat) (L M : Nat) (Hr0 : 0 ≤ r) (Hr1 : r ≤ 1)
    (Hq0 : 0 ≤ q) (Hq1 : q ≤ 1) :
    1 - (Qnat M * Qpow (1 - q) L + Qpow (1 - r) M) ≤
      envp_prefix_sum r (1 - Qpow (1 - q) L) M := by
  obtain ⟨Hx0, Hx1⟩ := geo_tail_unit q L Hq0 Hq1
  obtain ⟨HG0, HG1⟩ := geo_head_unit q L Hq0 Hq1
  obtain ⟨_Hb0, _Hb1⟩ := geo_tail_unit r M Hr0 Hr1
  obtain ⟨Hc0, Hc1⟩ := geo_head_unit r M Hr0 Hr1
  refine Rat.le_trans
    (b := Qpow (1 - Qpow (1 - q) L) M * (1 - Qpow (1 - r) M)) ?_ ?_
  · exact Qprod_margin _ _ _ _ (Qpow_nonneg _ _ HG0) (Qpow_le_1 _ _ HG0 HG1) Hc0 Hc1
      (Qpow_one_minus_lower _ M Hx0 Hx1) (Rat.le_refl)
  · exact envp_prefix_sum_lower r (1 - Qpow (1 - q) L) M Hr0 Hr1 HG0 HG1

/-- THE FILE-SYSTEM COORDINATE'S MARGIN: two entry-length shortfalls, one
    per half of the pair, and one entry-count tail. -/
theorem fs_prefix_margin (u v w : Rat) (Lp Lc M : Nat) (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1)
    (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1) (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) :
    1 - (Qnat M * Qpow (1 - v) Lp + Qnat M * Qpow (1 - w) Lc + Qpow (1 - u) M) ≤
      envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M := by
  obtain ⟨Hxv0, Hxv1⟩ := geo_tail_unit v Lp Hv0 Hv1
  obtain ⟨HGv0, HGv1⟩ := geo_head_unit v Lp Hv0 Hv1
  obtain ⟨Hxw0, Hxw1⟩ := geo_tail_unit w Lc Hw0 Hw1
  obtain ⟨HGw0, HGw1⟩ := geo_head_unit w Lc Hw0 Hw1
  obtain ⟨Hc0, Hc1⟩ := geo_head_unit u M Hu0 Hu1
  obtain ⟨HG0, HG1⟩ := Qmult_unit _ _ HGv0 HGv1 HGw0 HGw1
  refine Rat.le_trans
    (b := Qpow ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) M *
      (1 - Qpow (1 - u) M)) ?_ ?_
  · refine Qprod_margin _ _ _ _ (Qpow_nonneg _ _ HG0) (Qpow_le_1 _ _ HG0 HG1) Hc0 Hc1
      ?_ (Rat.le_refl)
    rw [Qpow_mult]
    exact Qprod_margin _ _ _ _ (Qpow_nonneg _ _ HGv0) (Qpow_le_1 _ _ HGv0 HGv1)
      (Qpow_nonneg _ _ HGw0) (Qpow_le_1 _ _ HGw0 HGw1)
      (Qpow_one_minus_lower (Qpow (1 - v) Lp) M Hxv0 Hxv1)
      (Qpow_one_minus_lower (Qpow (1 - w) Lc) M Hxw0 Hxw1)
  · exact envp_prefix_sum_lower u _ M Hu0 Hu1 HG0 HG1

/-- THE MARGIN ARITHMETIC OF THE CERTIFICATE, WITH THE EIGHT DEPTHS STILL
    FREE: if the eight tails together come in under `eps`, the witness's
    partial sum is within `eps` of `1`.  Four factors, each in the unit
    interval, each within its own margin; `Qprod_margin` three times.  No
    strict hypothesis appears. -/
theorem full_support_margin_at_depths (ra qa re qe u v w ps eps : Rat)
    (Ma La Me Le Mf Lp Lc k : Nat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Hsum : Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
      + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
      + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
      + Qpow (1 - ps) k ≤ eps) :
    1 - eps ≤ envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
        * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
        * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
        * (1 - Qpow (1 - ps) k) := by
  obtain ⟨HGa0, HGa1⟩ := geo_head_unit qa La Hqa0 Hqa1
  obtain ⟨HGe0, HGe1⟩ := geo_head_unit qe Le Hqe0 Hqe1
  obtain ⟨HGv0, HGv1⟩ := geo_head_unit v Lp Hv0 Hv1
  obtain ⟨HGw0, HGw1⟩ := geo_head_unit w Lc Hw0 Hw1
  obtain ⟨HGf0, HGf1⟩ := Qmult_unit _ _ HGv0 HGv1 HGw0 HGw1
  obtain ⟨HSa0, HSa1⟩ := envp_prefix_sum_unit ra _ Ma Hra0 Hra1 HGa0 HGa1
  obtain ⟨HSe0, HSe1⟩ := envp_prefix_sum_unit re _ Me Hre0 Hre1 HGe0 HGe1
  obtain ⟨HSf0, HSf1⟩ := envp_prefix_sum_unit u _ Mf Hu0 Hu1 HGf0 HGf1
  obtain ⟨HSs0, HSs1⟩ := geo_head_unit ps k Hps0 Hps1
  obtain ⟨HSae0, HSae1⟩ := Qmult_unit _ _ HSa0 HSa1 HSe0 HSe1
  obtain ⟨HSaef0, HSaef1⟩ := Qmult_unit _ _ HSae0 HSae1 HSf0 HSf1
  refine Rat.le_trans (b := 1 - (Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
      + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
      + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
      + Qpow (1 - ps) k)) ?_ ?_
  · rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact Rat.add_le_add_left.mpr (Rat.neg_le_neg Hsum)
  · refine Qprod_margin _ _ _ _ HSaef0 HSaef1 HSs0 HSs1 ?_ (Rat.le_refl)
    refine Qprod_margin _ _ _ _ HSae0 HSae1 HSf0 HSf1 ?_
      (fs_prefix_margin u v w Lp Lc Mf Hu0 Hu1 Hv0 Hv1 Hw0 Hw1)
    exact Qprod_margin _ _ _ _ HSa0 HSa1 HSe0 HSe1
      (strings_prefix_margin ra qa La Ma Hra0 Hra1 Hqa0 Hqa1)
      (strings_prefix_margin re qe Le Me Hre0 Hre1 Hqe0 Hqe1)

/-- ... AND THE DEPTHS THAT MEET IT.  Each strictness buys exactly one
    depth, eight in all, and each is asked for an eighth of the margin.
    An entry-count depth is `geo_gap_small` on its stop rate; an
    entry-length depth is chosen AFTER the entry count it has to cover
    (`entry_depth_for`), which is the `M + 1` division
    `envp_stdin_depths_above` does inline, named because it is done four
    times here.  No floors are taken: nothing but the margin has a say for
    a single family. -/
theorem entry_depth_for (q delta : Rat) (M : Nat) (Hq0 : 0 < q) (Hq1 : q ≤ 1)
    (Hd : 0 < delta) : ∃ L : Nat, Qnat M * Qpow (1 - q) L ≤ delta := by
  have HD : (0 : Rat) < Qnat M + 1 := by
    have := Qnat_nonneg M
    grind
  have HDpos : 0 < (Qnat M + 1)⁻¹ := Rat.inv_pos.mpr HD
  have Hbnd : 0 < delta * (Qnat M + 1)⁻¹ := Rat.mul_pos Hd HDpos
  obtain ⟨L, HL⟩ := geo_gap_small q (delta * (Qnat M + 1)⁻¹) Hq0 Hq1 Hbnd
  refine ⟨L, ?_⟩
  have hMle : Qnat M * (Qnat M + 1)⁻¹ ≤ 1 := by
    have hle : Qnat M ≤ Qnat M + 1 := by grind
    have hinv : 0 ≤ (Qnat M + 1)⁻¹ := Rat.le_of_lt HDpos
    refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hle hinv) ?_
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt HD)]
    exact Rat.le_refl
  refine Rat.le_trans (Rat.mul_le_mul_of_nonneg_left HL (Qnat_nonneg M)) ?_
  have hid : Qnat M * (delta * (Qnat M + 1)⁻¹) =
      (Qnat M * (Qnat M + 1)⁻¹) * delta := by grind
  rw [hid]
  have h := Rat.mul_le_mul_of_nonneg_right hMle (Rat.le_of_lt Hd)
  rwa [Rat.one_mul] at h

theorem full_support_depths_above (ra qa re qe u v w ps eps : Rat)
    (Hra0 : 0 < ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 < qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 < re) (Hre1 : re ≤ 1) (Hqe0 : 0 < qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 < u) (Hu1 : u ≤ 1) (Hv0 : 0 < v) (Hv1 : v ≤ 1)
    (Hw0 : 0 < w) (Hw1 : w ≤ 1) (Hps0 : 0 < ps) (Hps1 : ps ≤ 1)
    (Heps : 0 < eps) :
    ∃ Ma La Me Le Mf Lp Lc k : Nat,
      Qnat Ma * Qpow (1 - qa) La + Qpow (1 - ra) Ma
      + (Qnat Me * Qpow (1 - qe) Le + Qpow (1 - re) Me)
      + (Qnat Mf * Qpow (1 - v) Lp + Qnat Mf * Qpow (1 - w) Lc + Qpow (1 - u) Mf)
      + Qpow (1 - ps) k ≤ eps := by
  have h8 : (0 : Rat) < 1 / 8 := Qpos_one_div 8 (by decide)
  have heps8 : 0 < eps * (1 / 8) := Rat.mul_pos Heps h8
  obtain ⟨Ma, HMa⟩ := geo_gap_small ra (eps * (1 / 8)) Hra0 Hra1 heps8
  obtain ⟨La, HLa⟩ := entry_depth_for qa (eps * (1 / 8)) Ma Hqa0 Hqa1 heps8
  obtain ⟨Me, HMe⟩ := geo_gap_small re (eps * (1 / 8)) Hre0 Hre1 heps8
  obtain ⟨Le, HLe⟩ := entry_depth_for qe (eps * (1 / 8)) Me Hqe0 Hqe1 heps8
  obtain ⟨Mf, HMf⟩ := geo_gap_small u (eps * (1 / 8)) Hu0 Hu1 heps8
  obtain ⟨Lp, HLp⟩ := entry_depth_for v (eps * (1 / 8)) Mf Hv0 Hv1 heps8
  obtain ⟨Lc, HLc⟩ := entry_depth_for w (eps * (1 / 8)) Mf Hw0 Hw1 heps8
  obtain ⟨k, Hk⟩ := geo_gap_small ps (eps * (1 / 8)) Hps0 Hps1 heps8
  refine ⟨Ma, La, Me, Le, Mf, Lp, Lc, k, ?_⟩
  refine Rat.le_trans (b := eps * (1 / 8) + eps * (1 / 8)
      + (eps * (1 / 8) + eps * (1 / 8))
      + (eps * (1 / 8) + eps * (1 / 8) + eps * (1 / 8))
      + eps * (1 / 8)) ?_ ?_
  · exact Qplus_le_compat (Qplus_le_compat (Qplus_le_compat
      (Qplus_le_compat HLa HMa) (Qplus_le_compat HLe HMe))
      (Qplus_le_compat (Qplus_le_compat HLp HLc) HMf)) Hk
  · grind

/- =========================================================================
   The witness, and the certificate
   ========================================================================= -/

/-- THE WITNESS FAMILY: one record per quadruple drawn from the four
    prefix families.  It is a product, exactly as the bounds' enumeration
    is, and duplicate-free because all four coordinates are
    (`NoDup_full_support_product`).  Nothing in it is claimed valid. -/
def full_support_lower_witness (Ma La Me Le Mf Lp Lc k : Nat) : List FinProcInput :=
  List.map core_input
    (full_support_product (envps_upto La Ma) (envps_upto Le Me)
       (fss_upto Lp Lc Mf) (short_inputs k))

theorem map_fin_core_full_support_lower_witness (Ma La Me Le Mf Lp Lc k : Nat) :
    List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k) =
      full_support_product (envps_upto La Ma) (envps_upto Le Me)
        (fss_upto Lp Lc Mf) (short_inputs k) := by
  unfold full_support_lower_witness
  exact map_fin_core_core_input _

theorem full_support_lower_witness_nodup (Ma La Me Le Mf Lp Lc k : Nat) :
    (List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k)).Nodup := by
  rw [map_fin_core_full_support_lower_witness]
  exact NoDup_full_support_product _ _ _ _
    (envps_upto_nodup La Ma) (envps_upto_nodup Le Me)
    (fss_upto_nodup Lp Lc Mf) (short_inputs_nodup k)

/-- THE WITNESS, at each choice of the eight depths: an admissible list
    weighing exactly the product of the four coordinates' partial sums.
    Unconditional arithmetic, as `stdin_envp_geometric_mass_lower_witness`
    is. -/
theorem full_support_base_mass_lower_witness (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (Ma La Me Le Mf Lp Lc k : Nat) :
    (List.map fin_core (full_support_lower_witness Ma La Me Le Mf Lp Lc k)).Nodup ∧
      core_sum (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight
        (full_support_lower_witness Ma La Me Le Mf Lp Lc k) =
        envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
          * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
          * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
          * (1 - Qpow (1 - ps) k) := by
  refine ⟨full_support_lower_witness_nodup Ma La Me Le Mf Lp Lc k, ?_⟩
  show core_sum (base_weight ra qa re qe u v w ps)
      (full_support_lower_witness Ma La Me Le Mf Lp Lc k) = _
  rw [core_sum_map_fin_core, map_fin_core_full_support_lower_witness,
    qsum_full_support_product]
  unfold strings_point
  rw [qsum_envp_point_envps_upto, qsum_envp_point_envps_upto,
    qsum_fs_point_fss_upto, short_inputs_sum, geo_prefix_sum_closed]

/-- THE LOWER CERTIFICATE: for every margin `eps` there is an admissible
    list weighing at least the declared mass minus that margin.  With
    `full_support_base_mass_upper` above it, the declared `1` is the least
    upper bound of the admissible partial sums — approached but, by
    `full_support_base_mass_not_attained`, never met.

    ALL EIGHT STRICT INEQUALITIES ARE HYPOTHESES OF THIS LEMMA AND NOT
    TIGHTENINGS OF THE CONSTRUCTOR, for the reason
    `stdin_geometric_mass_lower_certificate` gives: everything above this
    lemma holds at every degenerate rate, and moving the hypotheses into
    the constructor would invalidate every degenerate member a consumer had
    already built.  A margin is asked for, eight natural numbers are
    produced, and the finite list they name is exhibited. -/
theorem full_support_base_mass_lower_certificate (ra qa re qe u v w ps : Rat)
    (Hra0 : 0 ≤ ra) (Hra1 : ra ≤ 1) (Hqa0 : 0 ≤ qa) (Hqa1 : qa ≤ 1)
    (Hre0 : 0 ≤ re) (Hre1 : re ≤ 1) (Hqe0 : 0 ≤ qe) (Hqe1 : qe ≤ 1)
    (Hu0 : 0 ≤ u) (Hu1 : u ≤ 1) (Hv0 : 0 ≤ v) (Hv1 : v ≤ 1)
    (Hw0 : 0 ≤ w) (Hw1 : w ≤ 1) (Hps0 : 0 ≤ ps) (Hps1 : ps ≤ 1)
    (eps : Rat)
    (Hrapos : 0 < ra) (Hqapos : 0 < qa) (Hrepos : 0 < re) (Hqepos : 0 < qe)
    (Hupos : 0 < u) (Hvpos : 0 < v) (Hwpos : 0 < w) (Hpspos : 0 < ps)
    (Heps : 0 < eps) :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      (full_support_base ra qa re qe u v w ps Hra0 Hra1 Hqa0 Hqa1
          Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_mass - eps ≤
        core_sum (full_support_base ra qa re qe u v w ps
            Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
            Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1).cd_weight l := by
  obtain ⟨Ma, La, Me, Le, Mf, Lp, Lc, k, Hsum⟩ :=
    full_support_depths_above ra qa re qe u v w ps eps
      Hrapos Hra1 Hqapos Hqa1 Hrepos Hre1 Hqepos Hqe1
      Hupos Hu1 Hvpos Hv1 Hwpos Hw1 Hpspos Hps1 Heps
  refine ⟨full_support_lower_witness Ma La Me Le Mf Lp Lc k,
    full_support_lower_witness_nodup Ma La Me Le Mf Lp Lc k, ?_⟩
  rw [(full_support_base_mass_lower_witness ra qa re qe u v w ps
    Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1 Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1
    Ma La Me Le Mf Lp Lc k).2]
  show (1 : Rat) - eps ≤
    envp_prefix_sum ra (1 - Qpow (1 - qa) La) Ma
      * envp_prefix_sum re (1 - Qpow (1 - qe) Le) Me
      * envp_prefix_sum u ((1 - Qpow (1 - v) Lp) * (1 - Qpow (1 - w) Lc)) Mf
      * (1 - Qpow (1 - ps) k)
  exact full_support_margin_at_depths ra qa re qe u v w ps eps
    Ma La Me Le Mf Lp Lc k Hra0 Hra1 Hqa0 Hqa1 Hre0 Hre1 Hqe0 Hqe1
    Hu0 Hu1 Hv0 Hv1 Hw0 Hw1 Hps0 Hps1 Hsum
end LinuxSem.EquivalenceDefinition.MeasureLib
