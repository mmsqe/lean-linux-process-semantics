/-
  * Examples.MeasureLibDemo.EnvpGeometric — the environment-varying
    geometric family, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  [MeasureLib]'s worked demonstration instantiates
  [MeasureLib.stdin_geometric], which holds argv, envp and the file
  system FIXED and varies standard input alone.  This file instantiates
  its two-coordinate companion [MeasureLib.stdin_envp_geometric], which
  varies the launch-time ENVIRONMENT as well, and carries it through to
  a [Measure.weight_bound_T].

  ** The three parameters, and why a task has three rather than one

  [p_stop] is the per-byte stop weight on standard input, as before.
  The environment coordinate needs two more, because an environment is
  a list of byte STRINGS and both the number of entries and the length
  of each has to be paid for: `r` is the weight of stopping after an
  entry (so `1 / 4` means a mean of four entries) and `q_e` is the
  per-byte stop weight WITHIN an entry.  [MeasureLib.envp_factor] is
  the running product of the two and [MeasureLib.envp_point] is `r`
  times it, which is what makes the two coordinates multiply in
  [MeasureLib.stdin_envp_geometric_cylinder_mass].

  The numbers here are `p_stop = 1 / 8`, `r = 1 / 4`, `q_e = 1 / 16`,
  and the environment prefix the fire set is charged against is ONE
  entry of ONE byte.  A realistic `NAME=value` entry is a dozen bytes
  and the ceiling is then a rational with a forty-digit denominator; a
  one-byte entry keeps the ceiling at `315 / 536870912`, which a reader
  can multiply out by hand from the four factors
  [envp_fire_ceiling] names.  Nothing in the argument depends on the
  length.

  ** What the cylinder is here

  Two existentials rather than one: a core is in the cylinder over
  `(es, bs)` when its environment EXTENDS `es` and its standard input
  EXTENDS `bs`, with argv and the file system fixed.  So the fire set
  below contains cores at every environment depth and every input
  length past the two prefixes, not merely the two records
  [envp_fire_list] exhibits — which is what makes the slack in
  [envp_fire_slack] large rather than a rounding.

  ** Non-vacuity

  [envp_fire_slack] pins that the two records really are inside the
  cylinder and weigh strictly less than the ceiling, so the bound is
  not attained; [envp_off_argv_weighs_nothing] pins the other side,
  that the family is not a constant — a core whose argv is not the
  fixed one weighs exactly zero.  Neither record is claimed VALID and
  neither is claimed rejected by any classifier.
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

namespace EnvpGeometric

/- =========================================================================
   The parameters, and the two side conditions each costs
   ========================================================================= -/

def envp_argv : List (List (BitVec 8)) :=
  [[BitVec.ofInt 8 119, BitVec.ofInt 8 99]]

def envp_fs : Fs.Fs := []

def envp_p : Rat := (1 : Rat) / 8

def envp_r : Rat := (1 : Rat) / 4

def envp_q : Rat := (1 : Rat) / 16

/-- Six `≤` facts, two per parameter.  They are named rather than
    inlined for the reason [MeasureLib.worked_share_named_nonneg] is:
    the constructor takes them as arguments, and a task author reading
    this wants to see what that costs — six lines, once. -/
theorem envp_p_nonneg : 0 ≤ envp_p := by unfold envp_p; grind

theorem envp_p_le_1 : envp_p ≤ 1 := by unfold envp_p; grind

theorem envp_r_nonneg : 0 ≤ envp_r := by unfold envp_r; grind

theorem envp_r_le_1 : envp_r ≤ 1 := by unfold envp_r; grind

theorem envp_q_nonneg : 0 ≤ envp_q := by unfold envp_q; grind

theorem envp_q_le_1 : envp_q ≤ 1 := by unfold envp_q; grind

/-- THE DISTRIBUTION.  Its declared mass is `1` by the constructor's own
    numeral, so `b * M` is `b` and the ceiling below can be quoted as a
    single number. -/
def envp_cd : CoreDistribution :=
  stdin_envp_geometric envp_p envp_r envp_q envp_argv envp_fs
    envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1

theorem envp_mass_is_one : envp_cd.cd_mass = 1 := rfl

/- =========================================================================
   The fire set: one environment prefix, one input prefix
   ========================================================================= -/

def envp_v : BitVec 8 := BitVec.ofInt 8 86

def envp_w : BitVec 8 := BitVec.ofInt 8 87

def envp_nul : BitVec 8 := BitVec.ofInt 8 0

def envp_a : BitVec 8 := BitVec.ofInt 8 65

/-- The two prefixes the fire set is charged against: an environment
    beginning with the one-byte entry `V`, and a standard input
    beginning with a NUL byte. -/
def envp_es : List (List (BitVec 8)) := [[envp_v]]

def envp_bs : List (BitVec 8) := [envp_nul]

/-- THE CEILING, as an exact rational, stated before it is used so that
    the number in the demonstrations is visibly what the cylinder mass
    IS and not a convenient rounding of it.  The four factors are the
    two the environment coordinate contributes — `1 - r = 3 / 4` for
    continuing past no entry at all, and `q_e (1 - q_e) / 256` for the
    one byte of the entry — and the two the input coordinate
    contributes, `(1 - p) / 256` for the NUL byte. -/
theorem envp_fire_ceiling :
    stdin_envp_geometric_cylinder_mass envp_p envp_r envp_q envp_es envp_bs =
      (315 : Rat) / 536870912 := by
  rw [stdin_envp_geometric_cylinder_mass_closed_form]
  unfold envp_p envp_r envp_q envp_es envp_bs envp_v envp_nul
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

/-- The same number through the family's own closed form, which is the
    shape a task prints: a power of `1 - r` for the entry count, the
    product of the per-entry weights, and the byte-geometric factor on
    standard input.  Stating both is what keeps the definitional form
    and the printed form from drifting. -/
theorem envp_fire_ceiling_closed_form :
    Qpow (1 - envp_r) envp_es.length * entries_geo_product envp_q envp_es *
        (Qpow (1 - envp_p) envp_bs.length * Qpow ((1 : Rat) / 256) envp_bs.length) =
      (315 : Rat) / 536870912 := by
  rw [← stdin_envp_geometric_cylinder_mass_closed_form]
  exact envp_fire_ceiling

/-- THE BOUND: every admissible list drawn from the cylinder weighs at
    most the ceiling.  One [MeasureLib.stdin_envp_geometric_bound] and
    the equality that names the number; the two existentials the
    cylinder asks for are discharged by the caller, at the fire set it
    actually has. -/
theorem envp_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) :
    core_sum envp_cd.cd_weight l ≤ (315 : Rat) / 536870912 := by
  rw [← envp_fire_ceiling]
  exact stdin_envp_geometric_bound envp_p envp_r envp_q envp_argv envp_fs
    envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1 envp_es envp_bs l Hnd Hcyl

/-- The OTHER bound the family exports, and the one a task with a
    length-indexed fire set uses instead: every admissible list whose
    members all have standard input of the SAME length `n` weighs at
    most `p (1 - p) ^ n`, with the environment charged nothing at all.
    Instantiated here at `n = 2`. -/
theorem envp_slice_bound_at_two (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      fin_core f = FinCore.mkFinCore envp_argv f.fin_envp envp_fs f.fin_stdin ∧
        f.fin_stdin.length = 2) :
    core_sum envp_cd.cd_weight l ≤ (49 : Rat) / 512 := by
  refine Rat.le_trans (stdin_envp_geometric_slice_bound envp_p envp_r envp_q
    envp_argv envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1 2 l Hnd Hslice) ?_
  show envp_p * Qpow (1 - envp_p) 2 ≤ (49 : Rat) / 512
  unfold envp_p
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def Envp_D : DISTRIBUTION where
  w := cd_lift envp_cd
  M := envp_cd.cd_mass
  w_nonneg := cd_lift_nonneg envp_cd
  M_nonneg := by
    show 0 ≤ envp_cd.cd_mass
    rw [envp_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind envp_cd

/-- The recipe, at any multiplier the ceiling fits under.  The
    classifier hypothesis is where the task's own analysis of its
    program enters, and it is the only place: everything else is the
    library's arithmetic. -/
theorem envp_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f))
    (Hb : (315 : Rat) / 536870912 ≤ b) :
    weight_bound_T C Envp_D.w Envp_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift envp_cd) l ≤ b * envp_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (envp_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [envp_mass_is_one, Rat.mul_one]
  exact Hb

/-- At a round multiplier a task would plausibly declare: a classifier
    whose reject set lies in this cylinder carries at most a
    thousandth of the mass. -/
theorem envp_weight_bound_T_thousandth (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) :
    weight_bound_T C Envp_D.w Envp_D.M ((1 : Rat) / 1000) := by
  refine envp_weight_bound_T_of C _ Hfire ?_
  grind

/-- At the tightest multiplier this route reaches. -/
theorem envp_weight_bound_T_ceiling (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs (fin_core f)) :
    weight_bound_T C Envp_D.w Envp_D.M ((315 : Rat) / 536870912) :=
  envp_weight_bound_T_of C _ Hfire Rat.le_refl

/- =========================================================================
   Non-vacuity: inside the cylinder, and off the fixed argv
   ========================================================================= -/

/-- Two cores of the cylinder: the one that stops at both prefixes, and
    one that extends BOTH coordinates — a second environment entry and a
    second input byte.  The pair is what makes the cylinder's two
    existentials visible as two independent degrees of freedom. -/
def envp_core_stop : FinCore :=
  FinCore.mkFinCore envp_argv [[envp_v]] envp_fs [envp_nul]

def envp_core_ext : FinCore :=
  FinCore.mkFinCore envp_argv [[envp_v], [envp_w]] envp_fs [envp_nul, envp_a]

def envp_fire_list : List FinProcInput :=
  List.map core_input [envp_core_stop, envp_core_ext]

theorem envp_core_stop_weight :
    envp_cd.cd_weight envp_core_stop = (315 : Rat) / 17179869184 := by
  show envp_geo_weight envp_p envp_r envp_q envp_argv envp_fs envp_core_stop = _
  unfold envp_core_stop
  rw [envp_geo_weight_closed_form]
  unfold envp_p envp_r envp_q envp_v envp_nul
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

theorem envp_core_ext_weight :
    envp_cd.cd_weight envp_core_ext = (99225 : Rat) / 9223372036854775808 := by
  show envp_geo_weight envp_p envp_r envp_q envp_argv envp_fs envp_core_ext = _
  unfold envp_core_ext
  rw [envp_geo_weight_closed_form]
  unfold envp_p envp_r envp_q envp_v envp_w envp_nul envp_a
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

/-- HOW MUCH OF THE CEILING IS REAL.  Four conjuncts.  The first two say
    the two cores really are in the cylinder, by naming the extensions —
    the empty pair for one, one entry and one byte for the other.  The
    third says the list is admissible, so [envp_fire_bound] applies to
    it.  The fourth is the strictness: the two records weigh strictly
    less than the ceiling, so this route carries slack.

    All of that slack is the cylinder's other members — every
    environment past `V` and every input past the NUL byte, at every
    depth, is charged for and absent from a two-element list.  What this
    does NOT say is that no smaller multiplier is provable; a task that
    sums its own cores exactly is entitled to a smaller one. -/
theorem envp_fire_slack :
    in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs envp_core_stop ∧
      in_envp_stdin_cylinder envp_argv envp_fs envp_es envp_bs envp_core_ext ∧
      (List.map fin_core envp_fire_list).Nodup ∧
      ¬ ((315 : Rat) / 536870912 ≤ core_sum envp_cd.cd_weight envp_fire_list) := by
  have hsum : core_sum envp_cd.cd_weight envp_fire_list =
      (315 : Rat) / 17179869184 + 99225 / 9223372036854775808 := by
    show envp_cd.cd_weight (fin_core (core_input envp_core_stop)) +
        (envp_cd.cd_weight (fin_core (core_input envp_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input, envp_core_stop_weight,
      envp_core_ext_weight]
    grind
  refine ⟨⟨[], [], rfl⟩, ⟨[[envp_w]], [envp_a], rfl⟩, ?_, ?_⟩
  · unfold envp_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have h2 := congrArg (fun c : FinCore => c.core_envp.length) h
      unfold envp_core_stop envp_core_ext at h2
      simp at h2
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind

/-- THE OTHER DIRECTION: the family is not the zero distribution and not
    a constant either.  The stopping core carries positive weight — the
    product of the two coordinates' stop weights — and a core whose argv
    is not the fixed one weighs exactly zero, which is
    [MeasureLib.envp_geo_weight_off_argv_zero] at a core this file
    names.  Without the first half every bound above would hold of a
    distribution that weighs nothing. -/
def envp_core_other_argv : FinCore :=
  FinCore.mkFinCore [[envp_a]] [[envp_v]] envp_fs [envp_nul]

theorem envp_off_argv_weighs_nothing :
    0 < envp_cd.cd_weight envp_core_stop ∧
      envp_cd.cd_weight envp_core_other_argv = 0 := by
  refine ⟨?_, ?_⟩
  · rw [envp_core_stop_weight]
    grind
  · show envp_geo_weight envp_p envp_r envp_q envp_argv envp_fs
      envp_core_other_argv = 0
    apply envp_geo_weight_off_argv_zero
    unfold envp_core_other_argv envp_argv
    intro h
    simp at h

/- =========================================================================
   The certificate pair, at concrete numbers
   ========================================================================= -/

/-- The whole-space upper certificate: no admissible list weighs more
    than the declared mass, fire set or not. -/
theorem envp_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum envp_cd.cd_weight l ≤ 1 :=
  stdin_envp_geometric_mass_upper envp_p envp_r envp_q envp_argv envp_fs
    envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1 l Hnd

/-- THE LOWER HALF, at a concrete margin.  All three of `p_stop`, `r`
    and `q_e` have to be POSITIVE for it: a zero on any of the three
    collapses the coordinate it governs, and the witness family the
    certificate builds would then weigh nothing.  The library pins each
    of those three degeneracies separately. -/
theorem envp_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum envp_cd.cd_weight l := by
  unfold envp_cd
  exact stdin_envp_geometric_mass_lower_certificate envp_p envp_r envp_q
    envp_argv envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1 (1 / 1000 : Rat)
    (by unfold envp_p; grind) (by unfold envp_r; grind)
    (by unfold envp_q; grind) (by grind)

/-- ... and no admissible list attains the mass, so the declared `1` is
    a supremum here too. -/
theorem envp_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum envp_cd.cd_weight l = 1) := by
  unfold envp_cd
  exact stdin_envp_geometric_mass_supremum_not_maximum envp_p envp_r envp_q
    envp_argv envp_fs envp_p_nonneg envp_p_le_1 envp_r_nonneg envp_r_le_1
    envp_q_nonneg envp_q_le_1 (by unfold envp_p; grind) l Hnd

end EnvpGeometric

end LinuxSem.Examples.MeasureLibDemo
