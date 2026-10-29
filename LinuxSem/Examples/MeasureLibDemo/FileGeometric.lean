/-
  * Examples.MeasureLibDemo.FileGeometric — the file-varying geometric
    family, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  [MeasureLib.stdin_geometric] varies STANDARD INPUT over a fixed
  launch-time environment.  [MeasureLib.file_geometric] varies the
  CONTENTS OF ONE FILE instead, at a path the task names, over a fixed
  argv, environment, standard input and base file system.  This file
  instantiates it and carries it through to a
  [Measure.weight_bound_T].

  ** Why a task reaches for this one rather than the standard-input one

  A program that takes its input as a path argument reads nothing from
  standard input, so a distribution that varies standard input puts all
  its mass on a coordinate the program never looks at, and every
  classifier either rejects all of it or none of it.  The file family
  varies the coordinate the program actually reads.  What it costs is
  one obligation that has no counterpart in the standard-input family,
  and this file pays it the way the library recommends.

  ** The argv/path coupling, discharged by construction

  [MeasureLib.file_geometric] takes argv and the path as INDEPENDENT
  parameters, and passing two different paths yields a distribution
  that is healthy by every certificate and varies a file the program
  never opens.  [MeasureLib.file_geometric_argv1] is the derived
  constructor for the shape a driver actually has — a program name and
  the input path at argv[1] — and it takes the path ONCE, so the
  mismatch is not expressible.  This file uses it, and
  [file_demo_argv_names_path] is the receipt.

  [file_demo_misconfiguration_is_invisible] is the other half: the
  library's pin of what a mismatched instance looks like, instantiated
  at this file's stop weight.  A reader can see there that the
  misconfigured instance passes both certificates and still collapses.

  ** The file system, and what [MeasureLib.fs_file] reads

  A core carries a whole [Fs.Fs], and the family varies one path of it
  over a fixed base: [MeasureLib.file_core] is [Fs.fs_set] of the
  contents into the base, and [MeasureLib.fs_file] is the readback,
  total by returning `[]` at an absent path.  [MeasureLib.file_core_inj]
  — the injectivity of that embedding — is what the duplicate-freedom
  argument below spends, and it is the reason two cores differing only
  in the file's contents are distinct cores rather than the same one.

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

namespace FileGeometric

/- =========================================================================
   The task's fixed data: a program, the path it is given, and the base
   ========================================================================= -/

/-- The program's own name, and the path it is invoked on: `"wc"` and
    `"/in"`.  Both are byte lists because argv entries and [Fs.path] are
    the same type here. -/
def file_demo_prog : List (BitVec 8) := [BitVec.ofInt 8 119, BitVec.ofInt 8 99]

def file_demo_path : Fs.path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 105, BitVec.ofInt 8 110]

/-- Everything the family holds fixed: no environment, an empty base file
    system, and an empty standard input.  The standard input being empty
    is the point rather than a default — this family's programs read
    their input from the path, so leaving standard input with any
    content at all would put weight on a coordinate nothing reads. -/
def file_demo_envp : List (List (BitVec 8)) := []

def file_demo_fs0 : Fs.Fs := []

def file_demo_stdin : List (BitVec 8) := []

def file_demo_p : Rat := (1 : Rat) / 8

theorem file_demo_p_nonneg : 0 ≤ file_demo_p := by unfold file_demo_p; grind

theorem file_demo_p_le_1 : file_demo_p ≤ 1 := by unfold file_demo_p; grind

/-- THE DISTRIBUTION, through the coupled constructor.  [file_demo_path]
    appears once in this term and reaches both the argv it is built into
    and the path whose contents are varied. -/
def file_demo_cd : CoreDistribution :=
  file_geometric_argv1 file_demo_p file_demo_prog file_demo_envp
    file_demo_fs0 file_demo_path file_demo_stdin
    file_demo_p_nonneg file_demo_p_le_1

def file_demo_argv : List (List (BitVec 8)) :=
  path_argv file_demo_prog file_demo_path

theorem file_demo_mass_is_one : file_demo_cd.cd_mass = 1 := rfl

/-- THE RECEIPT for the coupling: the argv this distribution was built
    with really does name the path whose contents it varies, and the
    coupled constructor really is the general one at that argv.  Both
    conjuncts come from the library; neither is argued here. -/
theorem file_demo_argv_names_path :
    argv_names_path file_demo_argv file_demo_path ∧
      file_demo_cd = file_geometric file_demo_p file_demo_argv file_demo_envp
        file_demo_fs0 file_demo_path file_demo_stdin
        file_demo_p_nonneg file_demo_p_le_1 :=
  file_geometric_argv1_names_path file_demo_p file_demo_prog file_demo_envp
    file_demo_fs0 file_demo_path file_demo_stdin file_demo_p_nonneg
    file_demo_p_le_1

/- =========================================================================
   The fire set: the input file begins with a NUL byte
   ========================================================================= -/

def file_demo_nul : BitVec 8 := BitVec.ofInt 8 0

def file_demo_a : BitVec 8 := BitVec.ofInt 8 65

/-- The prefix the fire set is charged against: one NUL byte at the head
    of the input file.  A task whose program fails on binary input
    describes its fire set exactly this way. -/
def file_demo_bs : List (BitVec 8) := [file_demo_nul]

/-- THE CEILING: the mass of the cylinder over that one byte.  It is the
    same [MeasureLib.geo_mass] the standard-input family charges, at the
    same stop weight — the two coordinates are weighted identically, and
    only the coordinate differs. -/
theorem file_demo_fire_ceiling :
    file_geometric_cylinder_mass file_demo_p file_demo_bs = (7 : Rat) / 2048 := by
  unfold file_geometric_cylinder_mass geo_mass file_demo_p file_demo_bs
  show Qpow ((1 - 1 / 8) * (1 / 256)) 1 = (7 : Rat) / 2048
  rw [Qpow_succ, Qpow_0]
  grind

/-- THE BOUND: every admissible list drawn from the cylinder weighs at
    most the ceiling.  One [MeasureLib.file_geometric_bound]; the
    existential the cylinder asks for is discharged by the caller, at
    the fire set it actually has. -/
theorem file_demo_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
        file_demo_path file_demo_stdin file_demo_bs (fin_core f)) :
    core_sum file_demo_cd.cd_weight l ≤ (7 : Rat) / 2048 := by
  rw [← file_demo_fire_ceiling]
  exact file_geometric_bound file_demo_p file_demo_argv file_demo_envp
    file_demo_fs0 file_demo_path file_demo_stdin file_demo_p_nonneg
    file_demo_p_le_1 file_demo_bs l Hnd Hcyl

/-- The length slice, which is the other bound the family exports: every
    admissible list whose members' input files all have the SAME length
    weighs at most `p (1 - p) ^ n`, with the 256 alternatives per byte
    charged nothing.  Instantiated at `n = 1`. -/
theorem file_demo_slice_bound_at_one (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      fin_core f = file_core file_demo_argv file_demo_envp file_demo_fs0
          file_demo_path file_demo_stdin
          (fs_file file_demo_path f.fin_image_fs) ∧
        (fs_file file_demo_path f.fin_image_fs).length = 1) :
    core_sum file_demo_cd.cd_weight l ≤ (7 : Rat) / 64 := by
  refine Rat.le_trans (file_geometric_slice_bound file_demo_p file_demo_argv
    file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
    file_demo_p_nonneg file_demo_p_le_1 1 l Hnd Hslice) ?_
  show file_demo_p * Qpow (1 - file_demo_p) 1 ≤ (7 : Rat) / 64
  unfold file_demo_p
  rw [Qpow_succ, Qpow_0]
  grind

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def File_D : DISTRIBUTION where
  w := cd_lift file_demo_cd
  M := file_demo_cd.cd_mass
  w_nonneg := cd_lift_nonneg file_demo_cd
  M_nonneg := by
    show 0 ≤ file_demo_cd.cd_mass
    rw [file_demo_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind file_demo_cd

theorem file_demo_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
        file_demo_path file_demo_stdin file_demo_bs (fin_core f))
    (Hb : (7 : Rat) / 2048 ≤ b) :
    weight_bound_T C File_D.w File_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift file_demo_cd) l ≤ b * file_demo_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (file_demo_fire_bound l Hnd (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [file_demo_mass_is_one, Rat.mul_one]
  exact Hb

/-- At a round multiplier a task would declare: a classifier that fires
    only on binary input files carries at most a hundredth of the mass. -/
theorem file_demo_weight_bound_T_hundredth (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
        file_demo_path file_demo_stdin file_demo_bs (fin_core f)) :
    weight_bound_T C File_D.w File_D.M ((1 : Rat) / 100) := by
  refine file_demo_weight_bound_T_of C _ Hfire ?_
  grind

/- =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= -/

/-- Two cores of the cylinder: the file that stops at the NUL byte, and
    the file that carries one byte more. -/
def file_demo_core_stop : FinCore :=
  file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
    file_demo_stdin [file_demo_nul]

def file_demo_core_ext : FinCore :=
  file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
    file_demo_stdin [file_demo_nul, file_demo_a]

def file_demo_fire_list : List FinProcInput :=
  List.map core_input [file_demo_core_stop, file_demo_core_ext]

theorem file_demo_core_stop_weight :
    file_demo_cd.cd_weight file_demo_core_stop = (7 : Rat) / 16384 := by
  show file_geo_weight file_demo_p file_demo_argv file_demo_envp file_demo_fs0
      file_demo_path file_demo_stdin
      (file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
        file_demo_stdin [file_demo_nul]) = _
  rw [file_geo_weight_match]
  show geo_point file_demo_p 1 = (7 : Rat) / 16384
  unfold geo_point geo_mass file_demo_p
  rw [Qpow_succ, Qpow_0]
  grind

theorem file_demo_core_ext_weight :
    file_demo_cd.cd_weight file_demo_core_ext = (49 : Rat) / 33554432 := by
  show file_geo_weight file_demo_p file_demo_argv file_demo_envp file_demo_fs0
      file_demo_path file_demo_stdin
      (file_core file_demo_argv file_demo_envp file_demo_fs0 file_demo_path
        file_demo_stdin [file_demo_nul, file_demo_a]) = _
  rw [file_geo_weight_match]
  show geo_point file_demo_p 2 = (49 : Rat) / 33554432
  unfold geo_point geo_mass file_demo_p
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

theorem file_demo_core_stop_ne_ext : file_demo_core_stop ≠ file_demo_core_ext := by
  intro h
  have h2 := congrArg (fun c : FinCore => (fs_file file_demo_path c.core_fs).length) h
  unfold file_demo_core_stop file_demo_core_ext at h2
  rw [fs_file_file_core, fs_file_file_core] at h2
  simp at h2

/-- HOW MUCH OF THE CEILING IS REAL.  The two cores are in the cylinder,
    the list is admissible — and duplicate-freedom is where
    [MeasureLib.file_core_inj] is spent: two cores differing only in the
    varied file's contents are distinct because the embedding into the
    file system is injective, which is a lemma and not an observation.
    The last conjunct is the strictness. -/
theorem file_demo_fire_slack :
    in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
        file_demo_path file_demo_stdin file_demo_bs file_demo_core_stop ∧
      in_file_cylinder file_demo_argv file_demo_envp file_demo_fs0
        file_demo_path file_demo_stdin file_demo_bs file_demo_core_ext ∧
      (List.map fin_core file_demo_fire_list).Nodup ∧
      ¬ ((7 : Rat) / 2048 ≤ core_sum file_demo_cd.cd_weight file_demo_fire_list) := by
  have hsum : core_sum file_demo_cd.cd_weight file_demo_fire_list =
      (7 : Rat) / 16384 + 49 / 33554432 := by
    show file_demo_cd.cd_weight (fin_core (core_input file_demo_core_stop)) +
        (file_demo_cd.cd_weight (fin_core (core_input file_demo_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input, file_demo_core_stop_weight,
      file_demo_core_ext_weight]
    grind
  refine ⟨⟨[], rfl⟩, ⟨[file_demo_a], rfl⟩, ?_, ?_⟩
  · unfold file_demo_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact file_demo_core_stop_ne_ext h
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind

/-- THE LOWER HALF of the certificate pair, at a concrete margin: some
    admissible list weighs within a thousandth of the declared mass.  A
    task prints this beside the upper bound to show that the `1` it
    declared is not an overstatement of what the weight actually
    carries. -/
theorem file_demo_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum file_demo_cd.cd_weight l := by
  unfold file_demo_cd
  exact file_geometric_mass_lower_certificate file_demo_p file_demo_argv
    file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
    file_demo_p_nonneg file_demo_p_le_1 (1 / 1000 : Rat)
    (by unfold file_demo_p; grind) (by grind)

/-- ... and it is a SUPREMUM and not a maximum: no admissible list
    whatever attains the declared mass, at this stop weight.  The two
    together are the honest reading of a declared `1` — approached, never
    reached. -/
theorem file_demo_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum file_demo_cd.cd_weight l = 1) := by
  unfold file_demo_cd
  exact file_geometric_mass_supremum_not_maximum file_demo_p file_demo_argv
    file_demo_envp file_demo_fs0 file_demo_path file_demo_stdin
    file_demo_p_nonneg file_demo_p_le_1
    (by unfold file_demo_p; grind) l Hnd

/-- THE MISCONFIGURATION, at this file's stop weight: the library's pin
    that an instance whose argv does not name the path is invisible to
    the program it is built for.  It declares mass `1`, puts positive
    weight on two distinct file contents, and those two cores hold the
    SAME bytes at the path argv actually names.  This is what
    [file_demo_argv_names_path] buys, made concrete. -/
theorem file_demo_misconfiguration_is_invisible :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric file_demo_p file_misconfigured_argv [] []
        file_example_path [] file_demo_p_nonneg file_demo_p_le_1).cd_weight
        (file_core file_misconfigured_argv [] [] file_example_path [] []) ∧
      0 < (file_geometric file_demo_p file_misconfigured_argv [] []
        file_example_path [] file_demo_p_nonneg file_demo_p_le_1).cd_weight
        (file_core file_misconfigured_argv [] [] file_example_path []
          [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_core file_misconfigured_argv [] [] file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_core file_misconfigured_argv [] [] file_example_path []
            [BitVec.ofInt 8 65]).core_fs :=
  file_geometric_needs_argv_to_name_the_path file_demo_p file_demo_p_nonneg
    file_demo_p_le_1 (by unfold file_demo_p; grind) (by unfold file_demo_p; grind)

/-- The whole-space upper certificate for the same distribution: the
    bound a task gets with no description of its fire set at all. -/
theorem file_demo_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum file_demo_cd.cd_weight l ≤ 1 :=
  file_geometric_mass_upper file_demo_p file_demo_argv file_demo_envp
    file_demo_fs0 file_demo_path file_demo_stdin file_demo_p_nonneg
    file_demo_p_le_1 l Hnd

end FileGeometric

end LinuxSem.Examples.MeasureLibDemo
