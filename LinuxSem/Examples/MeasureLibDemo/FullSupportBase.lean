/-
  * Examples.MeasureLibDemo.FullSupportBase — the full-support base family,
    worked at rate one half

  DEMO FILE (not part of the trusted specification, and not installed).
  Every other file in this directory instantiates a family that weighs
  ZERO off one fixed template.  This one instantiates
  [MeasureLib.full_support_base], under which every core — every argv,
  every environment, every file system, every standard input — weighs
  strictly more than zero, and carries it through to a
  [Measure.weight_bound_T] on a fire set described by an argv and the
  contents of one file, both alone and inside the mixture a task
  actually ships.

  ** The eight rates, and why they are all one half

  A typical base component is a product over the four coordinates, with
  every byte string weighing `(1 / 2) * (1 / 512) ^ length` and every
  list weighing `(1 / 2) ^ (count + 1)` times its entries' product.
  That is the family at all eight rates equal to `1 / 2`: [base_string_law]
  and [base_list_law] below are those two laws, proved against the
  library's own [geo_point] and entry-count shell so that the numbers a
  task prints are visibly the numbers the library weighs by.

  ** The fire set, and its bound

  The fire set is "argv is `[prog; pth]` and the file at `pth` begins
  with a NUL byte", which is the shape a task describes a
  content-triggered defect in.  It fixes ONE coordinate exactly and
  constrains ONE ENTRY of another while everything else — the
  environment, standard input, every other file, the entry count of the
  file system — stays free, so no cylinder bound covers it.
  [MeasureLib.full_support_base_argv_file_bound] does, at exactly the
  argv's own weight times the byte cylinder's mass on the contents
  coordinate.  Here that is `1 / 1125899906842624`, which is `2 ^ -50`:
  forty-one halvings for the two-entry argv and nine for the one-byte
  prefix.

  ** Inside the shipping mixture

  A task does not ship the base family alone; it ships
  `cd_mix2 (cd_scale s structured) (cd_scale (1 - s) base)` with the
  base's share small.  [base_mixture_fire_bound] prices the same fire
  set under that mixture at a share of `6 / 100`, with
  [MeasureLib.file_geometric] as the structured component: each
  component is charged through its own bound and the two are added by
  [MeasureLib.cd_mix2_bound].  The base component's charge is the
  smaller term by a wide margin, which is what "the base component is
  there for support, not for mass" means as a number.

  ** Non-vacuity, and the seam

  [base_fire_slack] pins that two cores really are in the fire set and
  weigh strictly less than the ceiling, so the bound is not attained;
  [base_every_core_positive] is full support itself, and
  [base_unsorted_fs_weighs] pins the seam: a core whose file system is
  NOT sorted — and so never [Fs.valid_fs] — still carries weight.  That
  is by design (see the family's header in [MeasureLib]); it is stated
  so nobody mistakes the declared mass for the mass reachable by valid
  images.  Nothing exhibited here is claimed valid and nothing is
  claimed rejected by any classifier.
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

namespace FullSupportBase

/- =========================================================================
   The rates, and the side conditions they cost
   ========================================================================= -/

/-- One rate for all eight slots.  Two `≤` facts and two `<` facts, named
    once: the constructor takes the first pair eight times over, and the
    positivity lemma the second pair. -/
def base_half : Rat := (1 : Rat) / 2

theorem base_half_nonneg : 0 ≤ base_half := by unfold base_half; grind

theorem base_half_le_1 : base_half ≤ 1 := by unfold base_half; grind

theorem base_half_pos : 0 < base_half := by unfold base_half; grind

theorem base_half_lt_1 : base_half < 1 := by unfold base_half; grind

/-- THE DISTRIBUTION, declared mass `1`. -/
def base_cd : CoreDistribution :=
  full_support_base base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1

theorem base_mass_is_one : base_cd.cd_mass = 1 := rfl

/- =========================================================================
   The two laws, as the library weighs them
   ========================================================================= -/

/-- Every byte string weighs `(1 / 2) * (1 / 512) ^ length`: the per-byte
    factor `(1 - 1 / 2) * (1 / 256)` is `1 / 512`. -/
theorem base_string_law (s : List (BitVec 8)) :
    geo_point base_half s.length = (1 : Rat) / 2 * Qpow ((1 : Rat) / 512) s.length := by
  unfold geo_point geo_mass base_half
  rw [Qpow_Qeq ((1 - 1 / 2) * (1 / 256)) (1 / 512) s.length (by grind)]

/-- Every list of `k` entries pays `(1 / 2) ^ (k + 1)` for its count. -/
theorem base_list_law (k : Nat) :
    base_half * Qpow (1 - base_half) k = Qpow ((1 : Rat) / 2) (k + 1) := by
  rw [Qpow_succ]
  unfold base_half
  rw [Qpow_Qeq (1 - 1 / 2) (1 / 2) k (by grind)]

/- =========================================================================
   Full support: every core weighs something
   ========================================================================= -/

theorem base_every_core_positive (c : FinCore) : 0 < base_cd.cd_weight c :=
  full_support_base_positive base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_pos base_half_lt_1 base_half_pos base_half_lt_1
    base_half_pos base_half_lt_1 base_half_pos base_half_lt_1
    base_half_pos base_half_lt_1 base_half_pos base_half_lt_1
    base_half_pos base_half_lt_1 base_half_pos base_half_lt_1
    c

/-- The seam, pinned.  This file system lists its two keys in the wrong
    order, so [Fs.fs_sorted] rejects it and it is never [Fs.valid_fs];
    the family weighs it anyway.  The declared mass `1` is the mass of
    the LAW, and the mass reachable by valid images is less. -/
def base_unsorted_fs : Fs.Fs :=
  [([BitVec.ofInt 8 98], []), ([BitVec.ofInt 8 97], [BitVec.ofInt 8 65])]

def base_unsorted_core : FinCore :=
  FinCore.mkFinCore [] [] base_unsorted_fs []

theorem base_unsorted_fs_weighs :
    Fs.fs_sorted base_unsorted_fs = false ∧
      0 < base_cd.cd_weight base_unsorted_core := by
  refine ⟨?_, base_every_core_positive _⟩
  unfold base_unsorted_fs
  decide

/- =========================================================================
   The fire set: an argv, and the head of one file
   ========================================================================= -/

def base_prog : List (BitVec 8) := [BitVec.ofInt 8 119, BitVec.ofInt 8 99]

def base_pth : Fs.path := [BitVec.ofInt 8 47, BitVec.ofInt 8 116]

def base_argv : List (List (BitVec 8)) := path_argv base_prog base_pth

def base_nul : BitVec 8 := BitVec.ofInt 8 0

def base_a : BitVec 8 := BitVec.ofInt 8 65

def base_bs : List (BitVec 8) := [base_nul]

/-- THE CEILING, as an exact rational: the argv's weight — a stop after
    two entries, and two two-byte strings — times the mass of the
    one-byte contents cylinder. -/
theorem base_fire_ceiling :
    strings_point base_half base_half base_argv * geo_mass base_half base_bs.length =
      (1 : Rat) / 1125899906842624 := by
  unfold base_argv base_prog base_pth base_bs base_half path_argv
  simp only [strings_point, envp_point, envp_factor, geo_point, geo_mass,
    Qpow_succ, Qpow_0, List.length_cons, List.length_nil]
  grind

/-- THE BOUND: every admissible list whose records have the fixed argv
    and a file at [base_pth] beginning with NUL weighs at most the
    ceiling.  One [MeasureLib.full_support_base_argv_file_bound] and the
    equality that names the number. -/
theorem base_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l →
      f.fin_argv = base_argv ∧ file_at_extends base_pth base_bs (fin_core f)) :
    core_sum base_cd.cd_weight l ≤ (1 : Rat) / 1125899906842624 := by
  rw [← base_fire_ceiling]
  exact full_support_base_argv_file_bound base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_argv base_pth base_bs l Hnd Hfire

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def Base_D : DISTRIBUTION where
  w := cd_lift base_cd
  M := base_cd.cd_mass
  w_nonneg := cd_lift_nonneg base_cd
  M_nonneg := by
    show 0 ≤ base_cd.cd_mass
    rw [base_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind base_cd

theorem base_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      f.fin_argv = base_argv ∧ file_at_extends base_pth base_bs (fin_core f))
    (Hb : (1 : Rat) / 1125899906842624 ≤ b) :
    weight_bound_T C Base_D.w Base_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift base_cd) l ≤ b * base_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (base_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [base_mass_is_one, Rat.mul_one]
  exact Hb

theorem base_weight_bound_T_ceiling (C : Image)
    (Hfire : ∀ f, rejects C f →
      f.fin_argv = base_argv ∧ file_at_extends base_pth base_bs (fin_core f)) :
    weight_bound_T C Base_D.w Base_D.M ((1 : Rat) / 1125899906842624) :=
  base_weight_bound_T_of C _ Hfire Rat.le_refl

/- =========================================================================
   Non-vacuity: inside the fire set, and strictly under the ceiling
   ========================================================================= -/

/-- Two cores of the fire set: the one with nothing but the argv and the
    one-byte file, and one that fills every free coordinate — an
    environment entry, a second file listed BEFORE the named one, a
    longer file at the path, a standard input.  The pair is what makes
    the free coordinates visible as degrees of freedom the bound
    charges for. -/
def base_core_stop : FinCore :=
  FinCore.mkFinCore base_argv [] [(base_pth, [base_nul])] []

def base_core_ext : FinCore :=
  FinCore.mkFinCore base_argv [[base_a]]
    [([base_a], [base_a]), (base_pth, [base_nul, base_a])] [base_a]

def base_fire_list : List FinProcInput :=
  List.map core_input [base_core_stop, base_core_ext]

theorem base_core_stop_weight :
    base_cd.cd_weight base_core_stop = (1 : Rat) / 2 ^ 74 := by
  show base_weight base_half base_half base_half base_half base_half base_half
      base_half base_half base_core_stop = _
  unfold base_core_stop base_argv base_prog base_pth base_nul base_half path_argv
  rw [base_weight_mk]
  simp only [strings_point, envp_point, envp_factor, fs_point, fs_factor,
    geo_point, geo_mass, Qpow_succ, Qpow_0, List.length_cons, List.length_nil]
  grind

theorem base_core_ext_weight :
    base_cd.cd_weight base_core_ext = (1 : Rat) / 2 ^ 124 := by
  show base_weight base_half base_half base_half base_half base_half base_half
      base_half base_half base_core_ext = _
  unfold base_core_ext base_argv base_prog base_pth base_nul base_a base_half
    path_argv
  rw [base_weight_mk]
  simp only [strings_point, envp_point, envp_factor, fs_point, fs_factor,
    geo_point, geo_mass, Qpow_succ, Qpow_0, List.length_cons, List.length_nil]
  grind

theorem base_core_stop_ne_ext : base_core_stop ≠ base_core_ext := by
  intro h
  have h2 := congrArg (fun c : FinCore => c.core_envp.length) h
  unfold base_core_stop base_core_ext at h2
  simp at h2

theorem base_fire_slack :
    ((core_input base_core_stop).fin_argv = base_argv ∧
        file_at_extends base_pth base_bs base_core_stop) ∧
      ((core_input base_core_ext).fin_argv = base_argv ∧
        file_at_extends base_pth base_bs base_core_ext) ∧
      (List.map fin_core base_fire_list).Nodup ∧
      (0 < core_sum base_cd.cd_weight base_fire_list) ∧
      ¬ ((1 : Rat) / 1125899906842624 ≤ core_sum base_cd.cd_weight base_fire_list) := by
  have hsum : core_sum base_cd.cd_weight base_fire_list =
      (1 : Rat) / 2 ^ 74 + 1 / 2 ^ 124 := by
    show base_cd.cd_weight (fin_core (core_input base_core_stop)) +
        (base_cd.cd_weight (fin_core (core_input base_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input, base_core_stop_weight,
      base_core_ext_weight]
    grind
  refine ⟨⟨rfl, ⟨[], rfl⟩⟩, ⟨rfl, ⟨[base_a], rfl⟩⟩, ?_, ?_, ?_⟩
  · unfold base_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact base_core_stop_ne_ext h
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind
  · rw [hsum]
    grind

/- =========================================================================
   The certificate pair, at concrete numbers
   ========================================================================= -/

theorem base_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum base_cd.cd_weight l ≤ 1 :=
  full_support_base_mass_upper base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    l Hnd

theorem base_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum base_cd.cd_weight l = 1) :=
  full_support_base_mass_supremum_not_maximum base_half base_half base_half
    base_half base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_lt_1 l Hnd

/-- THE LOWER HALF, at a concrete margin.  All eight rates have to be
    POSITIVE for it: a zero on any of them collapses the coordinate it
    governs, and the witness family the certificate builds would then
    weigh nothing there. -/
theorem base_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum base_cd.cd_weight l :=
  full_support_base_mass_lower_certificate base_half base_half base_half base_half
    base_half base_half base_half base_half
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    base_half_nonneg base_half_le_1 base_half_nonneg base_half_le_1
    (1 / 1000 : Rat)
    base_half_pos base_half_pos base_half_pos base_half_pos
    base_half_pos base_half_pos base_half_pos base_half_pos
    (by grind)

/- =========================================================================
   Inside the shipping mixture, at a share of 6 in 100
   ========================================================================= -/

/-- The structured component: the input file's contents at [base_pth],
    byte-geometric at `1 / 8`, over the fixed argv, an empty environment,
    an otherwise empty file system and empty standard input —
    [MeasureLib.file_geometric_argv1], so the argv and the path cannot
    disagree. -/
def base_structured_p : Rat := (1 : Rat) / 8

theorem base_structured_p_nonneg : 0 ≤ base_structured_p := by
  unfold base_structured_p; grind

theorem base_structured_p_le_1 : base_structured_p ≤ 1 := by
  unfold base_structured_p; grind

def base_structured : CoreDistribution :=
  file_geometric_argv1 base_structured_p base_prog [] [] base_pth []
    base_structured_p_nonneg base_structured_p_le_1

/-- The two shares: the base component gets `6 / 100`. -/
def base_share : Rat := (6 : Rat) / 100

def structured_share : Rat := (94 : Rat) / 100

theorem base_share_nonneg : 0 ≤ base_share := by unfold base_share; grind

theorem structured_share_nonneg : 0 ≤ structured_share := by
  unfold structured_share; grind

def base_mixture : CoreDistribution :=
  cd_mix2 (cd_scale structured_share structured_share_nonneg base_structured)
    (cd_scale base_share base_share_nonneg base_cd)

theorem base_mixture_mass_is_one : base_mixture.cd_mass = 1 := by
  rw [base_mixture, cd_mix2_mass, cd_scale_mass, cd_scale_mass, base_mass_is_one]
  show structured_share * base_structured.cd_mass + base_share * 1 = 1
  show structured_share * 1 + base_share * 1 = 1
  unfold structured_share base_share
  grind

/-- The structured component's own fire set — the file's contents extend
    the NUL byte over ITS fixed template — is inside the base family's:
    the template's argv is the fixed one and the file it varies is the
    file at [base_pth]. -/
theorem base_structured_fire_in_base_fire (c : FinCore)
    (Hc : in_file_cylinder base_argv [] [] base_pth [] base_bs c) :
    c.core_argv = base_argv ∧ file_at_extends base_pth base_bs c := by
  obtain ⟨ext, rfl⟩ := Hc
  refine ⟨rfl, ?_⟩
  exact ⟨ext, fs_file_file_core base_argv [] [] base_pth [] (base_bs ++ ext)⟩

/-- THE MIXTURE BOUND on the structured component's fire set: the
    structured component is charged its contents cylinder, the base
    component its argv-and-file marginal, each scaled by its share and
    added.  The number is `94 / 100` of `7 / 2048` plus `6 / 100` of
    `2 ^ -50`, reduced. -/
theorem base_mixture_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l →
      in_file_cylinder base_argv [] [] base_pth [] base_bs (fin_core f)) :
    core_sum base_mixture.cd_weight l ≤
      (36173932553831 : Rat) / 11258999068426240 := by
  have hstruct : core_sum
      (cd_scale structured_share structured_share_nonneg base_structured).cd_weight l ≤
      structured_share * ((7 : Rat) / 2048) := by
    refine cd_scale_bound _ _ _ _ _ ?_
    show core_sum base_structured.cd_weight l ≤ (7 : Rat) / 2048
    refine Rat.le_trans (file_geometric_bound base_structured_p base_argv [] []
      base_pth [] base_structured_p_nonneg base_structured_p_le_1 base_bs
      l Hnd Hfire) ?_
    show file_geometric_cylinder_mass base_structured_p base_bs ≤ (7 : Rat) / 2048
    unfold file_geometric_cylinder_mass geo_mass base_structured_p
    show Qpow ((1 - 1 / 8) * (1 / 256)) 1 ≤ (7 : Rat) / 2048
    rw [Qpow_succ, Qpow_0]
    grind
  have hbase : core_sum
      (cd_scale base_share base_share_nonneg base_cd).cd_weight l ≤
      base_share * ((1 : Rat) / 1125899906842624) := by
    refine cd_scale_bound _ _ _ _ _ ?_
    show core_sum base_cd.cd_weight l ≤ (1 : Rat) / 1125899906842624
    exact base_fire_bound l Hnd (fun f Hf =>
      base_structured_fire_in_base_fire (fin_core f) (Hfire f Hf))
  refine Rat.le_trans (cd_mix2_bound _ _ l _ _ hstruct hbase) ?_
  unfold structured_share base_share
  grind

end FullSupportBase

end LinuxSem.Examples.MeasureLibDemo
