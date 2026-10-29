/-
  * Examples.MeasureLibDemo.Calibrated — the calibrated mixture, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  [MeasureLib.calibrated_mixture] is the composition the library was
  requested for: fifteen sixteenths of the mass on standard input over
  ONE fixed launch-time environment, and a sixteenth spread over
  environments as well, at `r = 1 / 5` entries and `q_e = 1 / 33` bytes
  per entry.  It is [MeasureLib.cd_scale] twice and
  [MeasureLib.cd_mix2] once and no new combinator, which is the point
  of it having a name.  This file instantiates it at one stop weight
  and carries it to a [Measure.weight_bound_T].

  ** Why the ceiling comes out as the cylinder's own mass

  The fire set below lies in the fixed environment: every core in it
  has the canonical environment exactly, and a standard input extending
  one NUL byte.  Both components then charge it the same number — the
  stdin-only component through its cylinder, the envp-varying component
  through its cylinder over the EMPTY environment prefix, whose
  environment factor is `1`.  The two are then scaled by shares that
  sum to `1`, so the mixture's ceiling is the cylinder mass itself,
  `7 / 2048`.

  That is worth writing down rather than deriving in the reader's head,
  because it is the property a task actually wants from a calibrated
  mixture: mixing in an environment-varying component costs NOTHING on
  fire sets that do not vary the environment.  A fire set that does
  vary it pays, and pays through the second component's environment
  factor.

  ** What the mixture does buy, and where

  [calib_envp_component_carries_mass] is the bite:
  [MeasureLib.calibrated_mixture_envp_bites] instantiated here, showing
  a core with a non-empty environment that the stdin-only component
  weighs at ZERO and the mixture weighs positively.  Without that, the
  sixteenth would be decoration — the whole reason to mix is that the
  envp-varying component reaches cores the other one cannot see.

  Nothing exhibited here is claimed VALID and nothing is claimed
  rejected by any classifier.
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

namespace Calibrated

/- =========================================================================
   The one parameter a task picks, and the canonical environment
   ========================================================================= -/

/-- The stop weight is the ONLY thing [MeasureLib.calibrated_mixture]
    leaves open: the two shares and the environment coordinate's two
    parameters are the calibration and are fixed by the library.  A task
    configuration picks `p_stop` per binary by format class. -/
def calib_p : Rat := (1 : Rat) / 8

theorem calib_p_nonneg : 0 ≤ calib_p := by unfold calib_p; grind

theorem calib_p_le_1 : calib_p ≤ 1 := by unfold calib_p; grind

/-- The task's canonical launch-time environment.  It is what the
    stdin-only component FIXES; the envp-varying component takes the
    same argv and file system and no environment at all, which is the
    whole difference between the two. -/
def calib_argv : List (List (BitVec 8)) :=
  [[BitVec.ofInt 8 119, BitVec.ofInt 8 99]]

def calib_envp : List (List (BitVec 8)) := []

def calib_fs : Fs.Fs := []

def calib_cd : CoreDistribution :=
  calibrated_mixture calib_p calib_argv calib_envp calib_fs
    calib_p_nonneg calib_p_le_1

/-- The declared mass is `1`, and it is the two shares adding up rather
    than a numeral written here: `15 / 16` of one component's declared
    `1` plus `1 / 16` of the other's.  Change one share without the
    other and this stops holding. -/
theorem calib_mass_is_one : calib_cd.cd_mass = 1 :=
  calibrated_mixture_mass_is_one calib_p calib_argv calib_envp calib_fs
    calib_p_nonneg calib_p_le_1

/- =========================================================================
   The fire set: the canonical environment, standard input from a NUL
   ========================================================================= -/

def calib_nul : BitVec 8 := BitVec.ofInt 8 0

def calib_a : BitVec 8 := BitVec.ofInt 8 65

def calib_bs : List (BitVec 8) := [calib_nul]

/-- THE CEILING, as the two component ceilings scaled and added, stated
    as an equality before it is used so that the number in the
    demonstrations is visibly what the composition yields.  The second
    component is charged its cylinder over the EMPTY environment prefix —
    the fire set fixes an environment rather than a prefix of one, and
    the empty prefix is the one every environment extends. -/
theorem calib_fire_ceiling :
    calibrated_co_lambda * stdin_geometric_cylinder_mass calib_p calib_bs +
        calibrated_lambda * stdin_envp_geometric_cylinder_mass calib_p
          calibrated_r calibrated_q [] calib_bs =
      (7 : Rat) / 2048 := by
  unfold stdin_geometric_cylinder_mass stdin_envp_geometric_cylinder_mass
    geo_mass envp_factor calib_p calib_bs calib_nul calibrated_co_lambda
    calibrated_lambda
  simp only [Qpow_succ, Qpow_0, List.length_cons, List.length_nil]
  grind

/-- THE BOUND.  One [MeasureLib.cd_mix2_bound], one
    [MeasureLib.cd_scale_bound] per component, and one library cylinder
    bound under each — the same four-step shape [MeasureLib]'s worked
    demonstration uses, at a mixture whose components are both geometric
    rather than one finite and one geometric.

    The two side conditions are where the fire set is spent.  For the
    stdin-only component: a fire core is the canonical environment
    followed by an extension of `[0]`.  For the envp-varying component:
    the same core, read as an environment extending the empty prefix and
    a standard input extending `[0]` — so the environment existential is
    discharged with the canonical environment itself. -/
theorem calib_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hfire : ∀ f, f ∈ l →
      ∃ ext, fin_core f = FinCore.mkFinCore calib_argv calib_envp calib_fs
        (calib_bs ++ ext)) :
    core_sum calib_cd.cd_weight l ≤ (7 : Rat) / 2048 := by
  have hstruct :
      core_sum (cd_scale calibrated_co_lambda calibrated_co_lambda_nonneg
        (stdin_geometric calib_p calib_argv calib_envp calib_fs calib_p_nonneg
          calib_p_le_1)).cd_weight l ≤
        calibrated_co_lambda * stdin_geometric_cylinder_mass calib_p calib_bs :=
    cd_scale_bound _ _ _ _ _ (stdin_geometric_bound calib_p calib_argv
      calib_envp calib_fs calib_p_nonneg calib_p_le_1 calib_bs l Hnd
      (fun f Hf => Hfire f Hf))
  have henvp :
      core_sum (cd_scale calibrated_lambda calibrated_lambda_nonneg
        (stdin_envp_geometric calib_p calibrated_r calibrated_q calib_argv
          calib_fs calib_p_nonneg calib_p_le_1 calibrated_r_nonneg
          calibrated_r_le_1 calibrated_q_nonneg calibrated_q_le_1)).cd_weight l ≤
        calibrated_lambda * stdin_envp_geometric_cylinder_mass calib_p
          calibrated_r calibrated_q [] calib_bs :=
    cd_scale_bound _ _ _ _ _ (stdin_envp_geometric_bound calib_p calibrated_r
      calibrated_q calib_argv calib_fs calib_p_nonneg calib_p_le_1
      calibrated_r_nonneg calibrated_r_le_1 calibrated_q_nonneg
      calibrated_q_le_1 [] calib_bs l Hnd (fun f Hf => by
        obtain ⟨ext, Hext⟩ := Hfire f Hf
        exact ⟨calib_envp, ext, Hext⟩))
  rw [← calib_fire_ceiling]
  exact cd_mix2_bound _ _ l _ _ hstruct henvp

/-- The whole-space certificate for the mixture itself, which is the
    bound a task gets with no description of its fire set at all. -/
theorem calib_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum calib_cd.cd_weight l ≤ 1 :=
  calibrated_mixture_mass_upper calib_p calib_argv calib_envp calib_fs
    calib_p_nonneg calib_p_le_1 l Hnd

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def Calib_D : DISTRIBUTION where
  w := cd_lift calib_cd
  M := calib_cd.cd_mass
  w_nonneg := cd_lift_nonneg calib_cd
  M_nonneg := by
    show 0 ≤ calib_cd.cd_mass
    rw [calib_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind calib_cd

theorem calib_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      ∃ ext, fin_core f = FinCore.mkFinCore calib_argv calib_envp calib_fs
        (calib_bs ++ ext))
    (Hb : (7 : Rat) / 2048 ≤ b) :
    weight_bound_T C Calib_D.w Calib_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift calib_cd) l ≤ b * calib_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (calib_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [calib_mass_is_one, Rat.mul_one]
  exact Hb

theorem calib_weight_bound_T_hundredth (C : Image)
    (Hfire : ∀ f, rejects C f →
      ∃ ext, fin_core f = FinCore.mkFinCore calib_argv calib_envp calib_fs
        (calib_bs ++ ext)) :
    weight_bound_T C Calib_D.w Calib_D.M ((1 : Rat) / 100) := by
  refine calib_weight_bound_T_of C _ Hfire ?_
  grind

/- =========================================================================
   Non-vacuity: the sixteenth is not decoration, and the mass is real
   ========================================================================= -/

/-- WHAT THE MIXTURE BUYS.  A core with a non-empty environment: the
    stdin-only component weighs it at exactly zero, and the mixture
    weighs it positively.  So the sixteenth reaches cores the
    fifteen-sixteenths cannot see, which is the whole reason to mix
    rather than to declare the stdin-only family alone. -/
theorem calib_envp_component_carries_mass :
    (stdin_geometric calib_p [] [] [] calib_p_nonneg calib_p_le_1).cd_weight
        envp_example_named = 0 ∧
      0 < (calibrated_mixture calib_p [] [] [] calib_p_nonneg
        calib_p_le_1).cd_weight envp_example_named :=
  calibrated_mixture_envp_bites calib_p calib_p_nonneg calib_p_le_1
    (by unfold calib_p; grind) (by unfold calib_p; grind)

/-- THE LOWER HALF, at a concrete margin: some admissible list weighs
    within a thousandth of the declared `1`.  This is the one certificate
    in the library that does NOT compose from its components' — both
    components' masses are suprema that no list attains, so the mixture
    needs one list good for both at once, at depths chosen to cover the
    fixed environment as well as the margin. -/
theorem calib_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum calib_cd.cd_weight l :=
  calibrated_mixture_mass_lower_certificate calib_p calib_argv calib_envp
    calib_fs calib_p_nonneg calib_p_le_1 (1 / 1000 : Rat)
    (by unfold calib_p; grind) (by grind)

/-- Two cores of the fire set, and the slack.  The cylinder holds every
    standard input beginning with a NUL byte, at every length; a
    two-element list weighs strictly less than the ceiling that charges
    for all of them. -/
def calib_core_stop : FinCore :=
  FinCore.mkFinCore calib_argv calib_envp calib_fs [calib_nul]

def calib_core_ext : FinCore :=
  FinCore.mkFinCore calib_argv calib_envp calib_fs [calib_nul, calib_a]

def calib_fire_list : List FinProcInput :=
  List.map core_input [calib_core_stop, calib_core_ext]

/-- The stopping core's mixture weight: `15 / 16` of the stdin-only
    family's `geo_point p 1`, plus `1 / 16` of the envp-varying family's
    `envp_point r q [] * geo_point p 1` — the empty environment's point
    being the stop weight `r = 1 / 5` itself. -/
theorem calib_core_stop_weight :
    calib_cd.cd_weight calib_core_stop = (133 : Rat) / 327680 := by
  show calibrated_co_lambda * geo_weight calib_p calib_argv calib_envp calib_fs
      calib_core_stop +
      calibrated_lambda * envp_geo_weight calib_p calibrated_r calibrated_q
        calib_argv calib_fs calib_core_stop = _
  unfold calib_core_stop
  rw [geo_weight_match, envp_geo_weight_match]
  show calibrated_co_lambda * geo_point calib_p 1 +
      calibrated_lambda * (envp_point calibrated_r calibrated_q [] * geo_point calib_p 1) = _
  unfold calibrated_co_lambda calibrated_lambda calibrated_r calibrated_q
    envp_point envp_factor geo_point geo_mass calib_p
  simp only [Qpow_succ, Qpow_0]
  grind

/-- The extending core's: the same two factors at `geo_point p 2`. -/
theorem calib_core_ext_weight :
    calib_cd.cd_weight calib_core_ext = (931 : Rat) / 671088640 := by
  show calibrated_co_lambda * geo_weight calib_p calib_argv calib_envp calib_fs
      calib_core_ext +
      calibrated_lambda * envp_geo_weight calib_p calibrated_r calibrated_q
        calib_argv calib_fs calib_core_ext = _
  unfold calib_core_ext
  rw [geo_weight_match, envp_geo_weight_match]
  show calibrated_co_lambda * geo_point calib_p 2 +
      calibrated_lambda * (envp_point calibrated_r calibrated_q [] * geo_point calib_p 2) = _
  unfold calibrated_co_lambda calibrated_lambda calibrated_r calibrated_q
    envp_point envp_factor geo_point geo_mass calib_p
  simp only [Qpow_succ, Qpow_0]
  grind

theorem calib_core_stop_ne_ext : calib_core_stop ≠ calib_core_ext := by
  intro h
  have h2 := congrArg (fun c : FinCore => c.core_stdin.length) h
  unfold calib_core_stop calib_core_ext at h2
  simp at h2

theorem calib_fire_slack :
    (List.map fin_core calib_fire_list).Nodup ∧
      (∀ f, f ∈ calib_fire_list →
        ∃ ext, fin_core f = FinCore.mkFinCore calib_argv calib_envp calib_fs
          (calib_bs ++ ext)) ∧
      ¬ ((7 : Rat) / 2048 ≤ core_sum calib_cd.cd_weight calib_fire_list) := by
  have hsum : core_sum calib_cd.cd_weight calib_fire_list =
      (133 : Rat) / 327680 + 931 / 671088640 := by
    show calib_cd.cd_weight (fin_core (core_input calib_core_stop)) +
        (calib_cd.cd_weight (fin_core (core_input calib_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input, calib_core_stop_weight,
      calib_core_ext_weight]
    grind
  refine ⟨?_, ?_, ?_⟩
  · unfold calib_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact calib_core_stop_ne_ext h
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · intro f Hf
    unfold calib_fire_list at Hf
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at Hf
    rcases Hf with rfl | rfl
    · exact ⟨[], rfl⟩
    · exact ⟨[calib_a], rfl⟩
  · rw [hsum]
    grind

end Calibrated

end LinuxSem.Examples.MeasureLibDemo
