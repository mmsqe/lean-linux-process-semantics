/-
  * Examples.MeasureLibDemo.FileEnvpGeometric — the file-and-environment
    geometric family, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  Two families so far vary ONE coordinate: `stdin_geometric` the standard
  input, `file_geometric` the contents of one file, `stdin_envp_geometric`
  the launch-time environment beside the standard input.
  [MeasureLib.file_envp_geometric] varies the ENVIRONMENT and the FILE
  CONTENTS at once, over a fixed argv, standard input and base file
  system, and this file instantiates it at the same numbers its
  standard-input twin uses.

  ** Why the product and not a mixture

  A mixture of `file_geometric` and `stdin_envp_geometric` through
  [MeasureLib.cd_mix2] would put weight on cores varying the file at the
  CANONICAL environment and on cores varying the environment at the
  CANONICAL file, and none at all on a core varying both — so a defect
  reachable only from a non-canonical environment AND a particular input
  file would still sit in a null set.  This family is the product
  measure, so it does not, and that is the combinatorial difference the
  file demonstrates rather than any difference in the arithmetic: the
  ceiling is [MeasureLib.envp_geo_weight]'s number, `315 / 536870912`,
  the very one [Examples.MeasureLibDemo.EnvpGeometric] prints.

  ** The argv/path coupling, discharged by construction

  [MeasureLib.file_envp_geometric_argv1] takes the path ONCE and
  [file_envp_demo_argv_names_path] is the receipt.
  [file_envp_demo_misconfiguration_is_invisible] is the library's pin,
  instantiated at this file's three parameters.

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

namespace FileEnvpGeometric

/- =========================================================================
   The task's fixed data, and the three parameters
   ========================================================================= -/

def file_envp_demo_prog : List (BitVec 8) :=
  [BitVec.ofInt 8 119, BitVec.ofInt 8 99]

def file_envp_demo_path : Fs.path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 105, BitVec.ofInt 8 110]

def file_envp_demo_fs0 : Fs.Fs := []

def file_envp_demo_stdin : List (BitVec 8) := []

def file_envp_demo_p : Rat := (1 : Rat) / 8

def file_envp_demo_r : Rat := (1 : Rat) / 4

def file_envp_demo_q : Rat := (1 : Rat) / 16

theorem file_envp_demo_p_nonneg : 0 ≤ file_envp_demo_p := by
  unfold file_envp_demo_p; grind

theorem file_envp_demo_p_le_1 : file_envp_demo_p ≤ 1 := by
  unfold file_envp_demo_p; grind

theorem file_envp_demo_r_nonneg : 0 ≤ file_envp_demo_r := by
  unfold file_envp_demo_r; grind

theorem file_envp_demo_r_le_1 : file_envp_demo_r ≤ 1 := by
  unfold file_envp_demo_r; grind

theorem file_envp_demo_q_nonneg : 0 ≤ file_envp_demo_q := by
  unfold file_envp_demo_q; grind

theorem file_envp_demo_q_le_1 : file_envp_demo_q ≤ 1 := by
  unfold file_envp_demo_q; grind

def file_envp_demo_argv : List (List (BitVec 8)) :=
  path_argv file_envp_demo_prog file_envp_demo_path

/-- THE DISTRIBUTION, through the coupled constructor. -/
def file_envp_demo_cd : CoreDistribution :=
  file_envp_geometric_argv1 file_envp_demo_p file_envp_demo_r
    file_envp_demo_q file_envp_demo_prog file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin
    file_envp_demo_p_nonneg file_envp_demo_p_le_1
    file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1

theorem file_envp_demo_mass_is_one : file_envp_demo_cd.cd_mass = 1 := rfl

theorem file_envp_demo_argv_names_path :
    argv_names_path file_envp_demo_argv file_envp_demo_path ∧
      file_envp_demo_cd = file_envp_geometric file_envp_demo_p
        file_envp_demo_r file_envp_demo_q file_envp_demo_argv
        file_envp_demo_fs0 file_envp_demo_path file_envp_demo_stdin
        file_envp_demo_p_nonneg file_envp_demo_p_le_1
        file_envp_demo_r_nonneg file_envp_demo_r_le_1
        file_envp_demo_q_nonneg file_envp_demo_q_le_1 :=
  file_envp_geometric_argv1_names_path file_envp_demo_p file_envp_demo_r
    file_envp_demo_q file_envp_demo_prog file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1

/- =========================================================================
   The fire set: one environment prefix, one file prefix
   ========================================================================= -/

def file_envp_demo_v : BitVec 8 := BitVec.ofInt 8 86

def file_envp_demo_w : BitVec 8 := BitVec.ofInt 8 87

def file_envp_demo_nul : BitVec 8 := BitVec.ofInt 8 0

def file_envp_demo_a : BitVec 8 := BitVec.ofInt 8 65

def file_envp_demo_es : List (List (BitVec 8)) := [[file_envp_demo_v]]

def file_envp_demo_bs : List (BitVec 8) := [file_envp_demo_nul]

/-- THE CEILING, exactly as in the standard-input twin and for the same
    four factors: `1 - r` for continuing past no entry, the one-byte
    entry's own weight, and the byte-geometric factor on the varied
    coordinate. -/
theorem file_envp_demo_fire_ceiling :
    file_envp_geometric_cylinder_mass file_envp_demo_p file_envp_demo_r
        file_envp_demo_q file_envp_demo_es file_envp_demo_bs =
      (315 : Rat) / 536870912 := by
  rw [file_envp_geometric_cylinder_mass_closed_form]
  unfold file_envp_demo_p file_envp_demo_r file_envp_demo_q file_envp_demo_es
    file_envp_demo_bs file_envp_demo_v file_envp_demo_nul
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

theorem file_envp_demo_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
        file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
        file_envp_demo_bs (fin_core f)) :
    core_sum file_envp_demo_cd.cd_weight l ≤ (315 : Rat) / 536870912 := by
  rw [← file_envp_demo_fire_ceiling]
  exact file_envp_geometric_bound file_envp_demo_p file_envp_demo_r
    file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1 file_envp_demo_es
    file_envp_demo_bs l Hnd Hcyl

/-- The length slice, charging the environment nothing, at `n = 2`. -/
theorem file_envp_demo_slice_bound_at_two (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      fin_core f = file_envp_core file_envp_demo_argv file_envp_demo_fs0
          file_envp_demo_path file_envp_demo_stdin f.fin_envp
          (fs_file file_envp_demo_path f.fin_image_fs) ∧
        (fs_file file_envp_demo_path f.fin_image_fs).length = 2) :
    core_sum file_envp_demo_cd.cd_weight l ≤ (49 : Rat) / 512 := by
  refine Rat.le_trans (file_envp_geometric_slice_bound file_envp_demo_p
    file_envp_demo_r file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1 2 l Hnd Hslice) ?_
  show file_envp_demo_p * Qpow (1 - file_envp_demo_p) 2 ≤ (49 : Rat) / 512
  unfold file_envp_demo_p
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def FileEnvp_D : DISTRIBUTION where
  w := cd_lift file_envp_demo_cd
  M := file_envp_demo_cd.cd_mass
  w_nonneg := cd_lift_nonneg file_envp_demo_cd
  M_nonneg := by
    show 0 ≤ file_envp_demo_cd.cd_mass
    rw [file_envp_demo_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind file_envp_demo_cd

theorem file_envp_demo_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
        file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
        file_envp_demo_bs (fin_core f))
    (Hb : (315 : Rat) / 536870912 ≤ b) :
    weight_bound_T C FileEnvp_D.w FileEnvp_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift file_envp_demo_cd) l ≤
    b * file_envp_demo_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (file_envp_demo_fire_bound l Hnd
    (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [file_envp_demo_mass_is_one, Rat.mul_one]
  exact Hb

theorem file_envp_demo_weight_bound_T_thousandth (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
        file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
        file_envp_demo_bs (fin_core f)) :
    weight_bound_T C FileEnvp_D.w FileEnvp_D.M ((1 : Rat) / 1000) := by
  refine file_envp_demo_weight_bound_T_of C _ Hfire ?_
  grind

/- =========================================================================
   Non-vacuity
   ========================================================================= -/

/-- Two cores of the cylinder, extending it in BOTH coordinates at once:
    the one that stops at both prefixes, and the one carrying a second
    environment entry and a second file byte. -/
def file_envp_demo_core_stop : FinCore :=
  file_envp_core file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
    file_envp_demo_stdin [[file_envp_demo_v]] [file_envp_demo_nul]

def file_envp_demo_core_ext : FinCore :=
  file_envp_core file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
    file_envp_demo_stdin [[file_envp_demo_v], [file_envp_demo_w]]
    [file_envp_demo_nul, file_envp_demo_a]

def file_envp_demo_fire_list : List FinProcInput :=
  List.map core_input
    [file_envp_demo_core_stop, file_envp_demo_core_ext]

theorem file_envp_demo_core_stop_weight :
    file_envp_demo_cd.cd_weight file_envp_demo_core_stop =
      (315 : Rat) / 17179869184 := by
  show file_envp_geo_weight file_envp_demo_p file_envp_demo_r file_envp_demo_q
      file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
      file_envp_demo_stdin file_envp_demo_core_stop = _
  unfold file_envp_demo_core_stop
  rw [file_envp_geo_weight_closed_form]
  unfold file_envp_demo_p file_envp_demo_r file_envp_demo_q file_envp_demo_v
    file_envp_demo_nul
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

theorem file_envp_demo_core_ext_weight :
    file_envp_demo_cd.cd_weight file_envp_demo_core_ext =
      (99225 : Rat) / 9223372036854775808 := by
  show file_envp_geo_weight file_envp_demo_p file_envp_demo_r file_envp_demo_q
      file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
      file_envp_demo_stdin file_envp_demo_core_ext = _
  unfold file_envp_demo_core_ext
  rw [file_envp_geo_weight_closed_form]
  unfold file_envp_demo_p file_envp_demo_r file_envp_demo_q file_envp_demo_v
    file_envp_demo_w file_envp_demo_nul file_envp_demo_a
  simp only [entries_geo_product, geo_point, geo_mass, Qpow_succ, Qpow_0,
    List.length_cons, List.length_nil]
  grind

theorem file_envp_demo_fire_slack :
    in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
        file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
        file_envp_demo_bs file_envp_demo_core_stop ∧
      in_file_envp_cylinder file_envp_demo_argv file_envp_demo_fs0
        file_envp_demo_path file_envp_demo_stdin file_envp_demo_es
        file_envp_demo_bs file_envp_demo_core_ext ∧
      (List.map fin_core file_envp_demo_fire_list).Nodup ∧
      ¬ ((315 : Rat) / 536870912 ≤
        core_sum file_envp_demo_cd.cd_weight file_envp_demo_fire_list) := by
  have hsum : core_sum file_envp_demo_cd.cd_weight file_envp_demo_fire_list =
      (315 : Rat) / 17179869184 + 99225 / 9223372036854775808 := by
    show file_envp_demo_cd.cd_weight (fin_core (core_input file_envp_demo_core_stop)) +
        (file_envp_demo_cd.cd_weight (fin_core (core_input file_envp_demo_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input, file_envp_demo_core_stop_weight,
      file_envp_demo_core_ext_weight]
    grind
  refine ⟨⟨[], [], rfl⟩, ⟨[[file_envp_demo_w]], [file_envp_demo_a], rfl⟩, ?_, ?_⟩
  · unfold file_envp_demo_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have h2 := congrArg (fun c : FinCore => c.core_envp.length) h
      unfold file_envp_demo_core_stop file_envp_demo_core_ext file_envp_core
        file_core at h2
      simp at h2
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind

/-- The environment really carries mass here too: a core whose argv is
    not the fixed one weighs exactly zero, so the family is not a
    constant. -/
def file_envp_demo_core_other_argv : FinCore :=
  FinCore.mkFinCore [[file_envp_demo_a]] [[file_envp_demo_v]]
    (Fs.fs_set file_envp_demo_fs0 file_envp_demo_path [file_envp_demo_nul])
    file_envp_demo_stdin

theorem file_envp_demo_off_argv_weighs_nothing :
    file_envp_demo_cd.cd_weight file_envp_demo_core_other_argv = 0 := by
  show file_envp_geo_weight file_envp_demo_p file_envp_demo_r file_envp_demo_q
      file_envp_demo_argv file_envp_demo_fs0 file_envp_demo_path
      file_envp_demo_stdin file_envp_demo_core_other_argv = 0
  apply file_envp_geo_weight_off_argv_zero
  unfold file_envp_demo_core_other_argv file_envp_demo_argv path_argv
  intro h
  simp at h

/-- THE LOWER HALF of the certificate pair, at a concrete margin. -/
theorem file_envp_demo_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum file_envp_demo_cd.cd_weight l := by
  unfold file_envp_demo_cd
  exact file_envp_geometric_mass_lower_certificate file_envp_demo_p
    file_envp_demo_r file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1 (1 / 1000 : Rat)
    (by unfold file_envp_demo_p; grind) (by unfold file_envp_demo_r; grind)
    (by unfold file_envp_demo_q; grind) (by grind)

/-- THE MISCONFIGURATION, at this file's three parameters. -/
theorem file_envp_demo_misconfiguration_is_invisible :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_envp_geometric file_envp_demo_p file_envp_demo_r
        file_envp_demo_q file_misconfigured_argv []
        file_example_path [] file_envp_demo_p_nonneg file_envp_demo_p_le_1
        file_envp_demo_r_nonneg file_envp_demo_r_le_1
        file_envp_demo_q_nonneg file_envp_demo_q_le_1).cd_weight
        (file_envp_core file_misconfigured_argv [] file_example_path []
          [] []) ∧
      0 < (file_envp_geometric file_envp_demo_p file_envp_demo_r
        file_envp_demo_q file_misconfigured_argv []
        file_example_path [] file_envp_demo_p_nonneg file_envp_demo_p_le_1
        file_envp_demo_r_nonneg file_envp_demo_r_le_1
        file_envp_demo_q_nonneg file_envp_demo_q_le_1).cd_weight
        (file_envp_core file_misconfigured_argv [] file_example_path []
          [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_envp_core file_misconfigured_argv [] file_example_path []
            [] []).core_fs =
        fs_file file_other_path
          (file_envp_core file_misconfigured_argv []
            file_example_path [] [] [BitVec.ofInt 8 65]).core_fs :=
  file_envp_geometric_needs_argv_to_name_the_path file_envp_demo_p
    file_envp_demo_r file_envp_demo_q file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1
    (by unfold file_envp_demo_p; grind) (by unfold file_envp_demo_p; grind)
    (by unfold file_envp_demo_r; grind) (by unfold file_envp_demo_r; grind)
    (by unfold file_envp_demo_q; grind) (by unfold file_envp_demo_q; grind)

/-- The whole-space upper certificate, and the mass as a supremum: the
    two halves that make the declared `1` a two-sided claim here too. -/
theorem file_envp_demo_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum file_envp_demo_cd.cd_weight l ≤ 1 :=
  file_envp_geometric_mass_upper file_envp_demo_p file_envp_demo_r
    file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1 l Hnd

theorem file_envp_demo_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum file_envp_demo_cd.cd_weight l = 1) := by
  unfold file_envp_demo_cd
  exact file_envp_geometric_mass_supremum_not_maximum file_envp_demo_p
    file_envp_demo_r file_envp_demo_q file_envp_demo_argv file_envp_demo_fs0
    file_envp_demo_path file_envp_demo_stdin file_envp_demo_p_nonneg
    file_envp_demo_p_le_1 file_envp_demo_r_nonneg file_envp_demo_r_le_1
    file_envp_demo_q_nonneg file_envp_demo_q_le_1
    (by unfold file_envp_demo_p; grind) l Hnd

end FileEnvpGeometric

end LinuxSem.Examples.MeasureLibDemo
