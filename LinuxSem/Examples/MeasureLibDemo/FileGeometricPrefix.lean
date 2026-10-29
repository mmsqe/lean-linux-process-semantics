/-
  * Examples.MeasureLibDemo.FileGeometricPrefix — the header-conditioned
    file family, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  [MeasureLib.file_geometric] varies the CONTENTS OF ONE FILE over a
  fixed environment, every byte uniform.
  [MeasureLib.file_geometric_prefix] fixes the first bytes of that file
  to a HEADER the task names and spreads the geometric source over what
  follows.  This file instantiates it at a seven-byte header and carries
  it through to a [Measure.weight_bound_T], beside the whole-file
  family's own demo.

  ** Why a task reaches for this one rather than the whole-file one

  A driver that parses a header before it hands the rest of the file to
  the library under test rejects almost every file the whole-file family
  weighs: the header's bytes are uniform there too, so only the sliver
  of files whose random header happens to parse reaches the library, and
  a bound over the whole-file family prices the driver's reject path.
  [file_demo_prefix_header_dilution] below is that statement as
  arithmetic: the very same core — the header followed by nothing —
  weighs the stop weight under this family and the stop weight times a
  seventh power of a tiny number under the whole-file family.

  ** The header, and what is fixed

  The header is the shape a length-prefixed driver reads: a two-byte
  little-endian length word saying "one", the one configuration byte it
  announces, and a four-byte all-zero flags word.  Nothing here depends
  on that reading; it is seven bytes the family holds fixed.

  ** The argv/path coupling, discharged by construction

  As for the whole-file family, the path is passed ONCE through
  [MeasureLib.file_geometric_prefix_argv1], and
  [file_demo_prefix_argv_names_path] is the receipt.

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

namespace FileGeometricPrefix

/- =========================================================================
   The task's fixed data: a program, the path it is given, the base, and
   the header
   ========================================================================= -/

/-- The program's own name and the path it is invoked on: `"wc"` and
    `"/in"`, as in the whole-file demo. -/
def file_demo_prefix_prog : List (BitVec 8) :=
  [BitVec.ofInt 8 119, BitVec.ofInt 8 99]

def file_demo_prefix_path : Fs.path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 105, BitVec.ofInt 8 110]

def file_demo_prefix_envp : List (List (BitVec 8)) := []

def file_demo_prefix_fs0 : Fs.Fs := []

def file_demo_prefix_stdin : List (BitVec 8) := []

/-- THE HEADER: seven bytes.  `01 00` is a little-endian length word of
    one, `2a` the one configuration byte, `00 00 00 00` the flags. -/
def file_demo_hdr : List (BitVec 8) :=
  [BitVec.ofInt 8 1, BitVec.ofInt 8 0, BitVec.ofInt 8 42,
   BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0, BitVec.ofInt 8 0]

theorem file_demo_hdr_length : file_demo_hdr.length = 7 := rfl

/-- The stop weight: one in two hundred fifty-seven, chosen so that
    `1 - p` is `256 / 257` and the per-byte factor `(1 - p) / 256` is
    exactly `1 / 257` — every number below is a power of `257`. -/
def file_demo_prefix_p : Rat := (1 : Rat) / 257

theorem file_demo_prefix_p_nonneg : 0 ≤ file_demo_prefix_p := by
  unfold file_demo_prefix_p; grind

theorem file_demo_prefix_p_le_1 : file_demo_prefix_p ≤ 1 := by
  unfold file_demo_prefix_p; grind

/-- THE DISTRIBUTION, through the coupled constructor. -/
def file_demo_prefix_cd : CoreDistribution :=
  file_geometric_prefix_argv1 file_demo_hdr file_demo_prefix_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1

def file_demo_prefix_argv : List (List (BitVec 8)) :=
  path_argv file_demo_prefix_prog file_demo_prefix_path

theorem file_demo_prefix_mass_is_one : file_demo_prefix_cd.cd_mass = 1 := rfl

theorem file_demo_prefix_argv_names_path :
    argv_names_path file_demo_prefix_argv file_demo_prefix_path ∧
      file_demo_prefix_cd = file_geometric_prefix file_demo_hdr
        file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
        file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
        file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 :=
  file_geometric_prefix_argv1_names_path file_demo_hdr file_demo_prefix_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_p_nonneg
    file_demo_prefix_p_le_1

/- =========================================================================
   The fire set: after the header, the payload begins with a NUL byte
   ========================================================================= -/

def file_demo_prefix_nul : BitVec 8 := BitVec.ofInt 8 0

def file_demo_prefix_a : BitVec 8 := BitVec.ofInt 8 65

/-- The PAYLOAD prefix the fire set is charged against: one NUL byte
    right after the header. -/
def file_demo_prefix_bs : List (BitVec 8) := [file_demo_prefix_nul]

/-- THE CEILING: the mass of the payload cylinder over that one byte.
    It is `(1 - p) / 256` at this stop weight, which is one in two
    hundred fifty-seven — and it does NOT pay for the header. -/
theorem file_demo_prefix_fire_ceiling :
    file_geometric_prefix_cylinder_mass file_demo_prefix_p file_demo_prefix_bs =
      (1 : Rat) / 257 := by
  unfold file_geometric_prefix_cylinder_mass file_geometric_cylinder_mass
    geo_mass file_demo_prefix_p file_demo_prefix_bs file_demo_prefix_nul
  change Qpow ((1 - (1 : Rat) / 257) * (1 / 256)) 1 = (1 : Rat) / 257
  rw [Qpow_succ, Qpow_0]
  grind

theorem file_demo_prefix_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_bs (fin_core f)) :
    core_sum file_demo_prefix_cd.cd_weight l ≤ (1 : Rat) / 257 := by
  rw [← file_demo_prefix_fire_ceiling]
  exact file_geometric_prefix_bound file_demo_hdr file_demo_prefix_p
    file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_p_nonneg
    file_demo_prefix_p_le_1 file_demo_prefix_bs l Hnd Hcyl

/-- The payload-length slice at `n = 1`: `p (1 - p)`, with the 256
    alternatives per payload byte charged nothing and the header charged
    nothing. -/
theorem file_demo_prefix_slice_bound_at_one (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core file_demo_hdr file_demo_prefix_argv
          file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
          file_demo_prefix_stdin t ∧ t.length = 1) :
    core_sum file_demo_prefix_cd.cd_weight l ≤ (256 : Rat) / 66049 := by
  refine Rat.le_trans (file_geometric_prefix_slice_bound file_demo_hdr
    file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 1 l Hnd Hslice) ?_
  show file_demo_prefix_p * Qpow (1 - file_demo_prefix_p) 1 ≤ (256 : Rat) / 66049
  unfold file_demo_prefix_p
  rw [Qpow_succ, Qpow_0]
  grind

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def FilePrefix_D : DISTRIBUTION where
  w := cd_lift file_demo_prefix_cd
  M := file_demo_prefix_cd.cd_mass
  w_nonneg := cd_lift_nonneg file_demo_prefix_cd
  M_nonneg := by
    show 0 ≤ file_demo_prefix_cd.cd_mass
    rw [file_demo_prefix_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind file_demo_prefix_cd

theorem file_demo_prefix_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_bs (fin_core f))
    (Hb : (1 : Rat) / 257 ≤ b) :
    weight_bound_T C FilePrefix_D.w FilePrefix_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift file_demo_prefix_cd) l ≤
    b * file_demo_prefix_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (file_demo_prefix_fire_bound l Hnd
    (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [file_demo_prefix_mass_is_one, Rat.mul_one]
  exact Hb

/-- At a round multiplier a task would declare: a classifier that fires
    only on payloads beginning with a NUL byte carries at most a
    hundredth of the mass. -/
theorem file_demo_prefix_weight_bound_T_hundredth (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_bs (fin_core f)) :
    weight_bound_T C FilePrefix_D.w FilePrefix_D.M ((1 : Rat) / 100) := by
  refine file_demo_prefix_weight_bound_T_of C _ Hfire ?_
  grind

/- =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= -/

/-- Two cores of the cylinder: the payload that stops at the NUL byte,
    and the payload that carries one byte more. -/
def file_demo_prefix_core_stop : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul]

def file_demo_prefix_core_ext : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul, file_demo_prefix_a]

def file_demo_prefix_fire_list : List FinProcInput :=
  List.map core_input [file_demo_prefix_core_stop, file_demo_prefix_core_ext]

theorem file_demo_prefix_core_stop_weight :
    file_demo_prefix_cd.cd_weight file_demo_prefix_core_stop = (1 : Rat) / 66049 := by
  show file_prefix_geo_weight file_demo_hdr file_demo_prefix_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_core_stop = _
  unfold file_demo_prefix_core_stop
  rw [file_prefix_geo_weight_match]
  show geo_point file_demo_prefix_p 1 = (1 : Rat) / 66049
  unfold geo_point geo_mass file_demo_prefix_p
  rw [Qpow_succ, Qpow_0]
  grind

theorem file_demo_prefix_core_ext_weight :
    file_demo_prefix_cd.cd_weight file_demo_prefix_core_ext =
      (1 : Rat) / 16974593 := by
  show file_prefix_geo_weight file_demo_hdr file_demo_prefix_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_core_ext = _
  unfold file_demo_prefix_core_ext
  rw [file_prefix_geo_weight_match]
  show geo_point file_demo_prefix_p 2 = (1 : Rat) / 16974593
  unfold geo_point geo_mass file_demo_prefix_p
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

theorem file_demo_prefix_core_stop_ne_ext :
    file_demo_prefix_core_stop ≠ file_demo_prefix_core_ext := by
  intro h
  have h2 := file_prefix_core_inj file_demo_hdr file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin [file_demo_prefix_nul]
    [file_demo_prefix_nul, file_demo_prefix_a] h
  simp at h2

/-- HOW MUCH OF THE CEILING IS REAL: both cores are in the cylinder, the
    list is admissible — [MeasureLib.file_prefix_core_inj] is what makes
    two payloads two cores — and the sum is strictly under the ceiling. -/
theorem file_demo_prefix_fire_slack :
    in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_bs file_demo_prefix_core_stop ∧
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_bs file_demo_prefix_core_ext ∧
      (List.map fin_core file_demo_prefix_fire_list).Nodup ∧
      ¬ ((1 : Rat) / 257 ≤
        core_sum file_demo_prefix_cd.cd_weight file_demo_prefix_fire_list) := by
  have hsum : core_sum file_demo_prefix_cd.cd_weight file_demo_prefix_fire_list =
      (1 : Rat) / 66049 + 1 / 16974593 := by
    show file_demo_prefix_cd.cd_weight
        (fin_core (core_input file_demo_prefix_core_stop)) +
        (file_demo_prefix_cd.cd_weight
          (fin_core (core_input file_demo_prefix_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input,
      file_demo_prefix_core_stop_weight, file_demo_prefix_core_ext_weight]
    grind
  refine ⟨⟨[], rfl⟩, ⟨[file_demo_prefix_a], rfl⟩, ?_, ?_⟩
  · unfold file_demo_prefix_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact file_demo_prefix_core_stop_ne_ext h
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind

/-- THE LOWER HALF of the certificate pair, at a concrete margin. -/
theorem file_demo_prefix_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum file_demo_prefix_cd.cd_weight l := by
  unfold file_demo_prefix_cd
  exact file_geometric_prefix_mass_lower_certificate file_demo_hdr
    file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1 (1 / 1000 : Rat)
    (by unfold file_demo_prefix_p; grind) (by grind)

/-- ... and it is a SUPREMUM and not a maximum. -/
theorem file_demo_prefix_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum file_demo_prefix_cd.cd_weight l = 1) := by
  unfold file_demo_prefix_cd
  exact file_geometric_prefix_mass_supremum_not_maximum file_demo_hdr
    file_demo_prefix_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1
    (by unfold file_demo_prefix_p; grind) l Hnd

/-- The whole-space upper certificate for the same distribution. -/
theorem file_demo_prefix_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum file_demo_prefix_cd.cd_weight l ≤ 1 :=
  file_geometric_prefix_mass_upper file_demo_hdr file_demo_prefix_p
    file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_p_nonneg
    file_demo_prefix_p_le_1 l Hnd

/- =========================================================================
   The header bites, numerically
   ========================================================================= -/

/-- The core whose file is EXACTLY the header (empty payload), the core
    whose file is the header with its first byte changed, and the
    whole-file family at the same parameters, for comparison. -/
def file_demo_prefix_core_hdr : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin []

/-- The corrupted header is DERIVED from the header — its first byte
    replaced, the rest taken from [file_demo_hdr] by [List.tail] — so
    that editing the header cannot leave the pin below green while it
    stops meaning "the header with its first byte changed".
    [file_demo_badhdr_is_the_header_with_its_first_byte_changed] is the
    receipt: same tail, different list. -/
def file_demo_badhdr : List (BitVec 8) :=
  BitVec.ofInt 8 2 :: file_demo_hdr.tail

theorem file_demo_badhdr_is_the_header_with_its_first_byte_changed :
    file_demo_badhdr.tail = file_demo_hdr.tail ∧
      Fs.path_eqb file_demo_badhdr file_demo_hdr = false := by
  refine ⟨rfl, ?_⟩
  unfold file_demo_badhdr file_demo_hdr
  decide

/-- The corrupted header is never the header followed by anything: the
    two have the same length and different first bytes. -/
theorem file_demo_badhdr_no_extension (t : List (BitVec 8)) :
    file_demo_badhdr ≠ file_demo_hdr ++ t := by
  intro h
  have hl := congrArg List.length h
  have ht : t = [] := by
    unfold file_demo_badhdr file_demo_hdr at hl
    simp at hl
    omega
  subst ht
  rw [List.append_nil] at h
  unfold file_demo_badhdr file_demo_hdr at h
  simp at h

def file_demo_prefix_core_badhdr : FinCore :=
  file_core file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_badhdr

def file_demo_wholefile_cd : CoreDistribution :=
  file_geometric file_demo_prefix_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_prefix_p_nonneg file_demo_prefix_p_le_1

/-- THE HEADER BITES: the exact-header core weighs the stop weight, the
    corrupted-header core weighs zero, and the declared mass is `1`. -/
theorem file_demo_prefix_header_bites :
    file_demo_prefix_cd.cd_weight file_demo_prefix_core_hdr = (1 : Rat) / 257 ∧
      file_demo_prefix_cd.cd_weight file_demo_prefix_core_badhdr = 0 ∧
      file_demo_prefix_cd.cd_mass = 1 := by
  have hhdr : file_demo_prefix_cd.cd_weight file_demo_prefix_core_hdr =
      (1 : Rat) / 257 := by
    show file_prefix_geo_weight file_demo_hdr file_demo_prefix_p
        file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
        file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_core_hdr = _
    unfold file_demo_prefix_core_hdr
    rw [file_prefix_geo_weight_match]
    show geo_point file_demo_prefix_p 0 = (1 : Rat) / 257
    unfold geo_point geo_mass file_demo_prefix_p
    rw [Qpow_0]
    grind
  have hbad : file_demo_prefix_cd.cd_weight file_demo_prefix_core_badhdr = 0 := by
    show file_prefix_geo_weight file_demo_hdr file_demo_prefix_p
        file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
        file_demo_prefix_path file_demo_prefix_stdin
        file_demo_prefix_core_badhdr = 0
    apply file_prefix_geo_weight_off_header_zero
    intro t h
    rw [show fs_file file_demo_prefix_path
        file_demo_prefix_core_badhdr.core_fs = file_demo_badhdr from
      fs_file_file_core file_demo_prefix_argv file_demo_prefix_envp
        file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
        file_demo_badhdr] at h
    exact file_demo_badhdr_no_extension t h
  exact ⟨hhdr, hbad, rfl⟩

/-- THE HEADER DILUTION, as arithmetic: the same exact-header core weighs
    `p` here and `p * ((1 - p) / 256) ^ 7` under the whole-file family —
    a seventh power of one in two hundred fifty-seven smaller.  That
    factor is what a bound over the whole-file family would have to pay
    for the header before it says anything about the payload. -/
theorem file_demo_prefix_header_dilution :
    file_demo_wholefile_cd.cd_weight file_demo_prefix_core_hdr =
        (1 : Rat) / 257 * Qpow ((1 : Rat) / 257) 7 ∧
      file_demo_prefix_cd.cd_weight file_demo_prefix_core_hdr = (1 : Rat) / 257 := by
  refine ⟨?_, (file_demo_prefix_header_bites).1⟩
  show file_geo_weight file_demo_prefix_p file_demo_prefix_argv
      file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
      file_demo_prefix_stdin file_demo_prefix_core_hdr = _
  unfold file_demo_prefix_core_hdr file_prefix_core file_demo_hdr
  rw [file_geo_weight_match]
  show geo_point file_demo_prefix_p 7 = (1 : Rat) / 257 * Qpow ((1 : Rat) / 257) 7
  unfold geo_point geo_mass file_demo_prefix_p
  rw [Qpow_Qeq ((1 - 1 / 257) * (1 / 256)) (1 / 257) 7 (by grind)]

/- =========================================================================
   The empty header, numerically
   ========================================================================= -/

def file_demo_nilhdr_cd : CoreDistribution :=
  file_geometric_prefix [] file_demo_prefix_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_prefix_p_nonneg file_demo_prefix_p_le_1

def file_demo_prefix_core_one : FinCore :=
  file_core file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin [file_demo_prefix_nul]

/-- THE `k = 0` COLLAPSE, at two concrete cores and as a number: the
    empty-header family and the whole-file family agree at the one-byte
    file, where both weigh `p (1 - p) / 256`, and at the seven-byte
    header file.  The general statement is
    [MeasureLib.file_geometric_prefix_nil_pointwise], instantiated in
    the last conjunct. -/
theorem file_demo_prefix_nil_collapse :
    file_demo_nilhdr_cd.cd_weight file_demo_prefix_core_one = (1 : Rat) / 66049 ∧
      file_demo_wholefile_cd.cd_weight file_demo_prefix_core_one =
        (1 : Rat) / 66049 ∧
      file_demo_nilhdr_cd.cd_weight file_demo_prefix_core_hdr =
        file_demo_wholefile_cd.cd_weight file_demo_prefix_core_hdr ∧
      (∀ c, file_demo_nilhdr_cd.cd_weight c =
        file_demo_wholefile_cd.cd_weight c) := by
  have hone : ∀ (D : CoreDistribution),
      (D = file_demo_nilhdr_cd ∨ D = file_demo_wholefile_cd) →
      D.cd_weight file_demo_prefix_core_one = (1 : Rat) / 66049 := by
    intro D hD
    have hw : D.cd_weight file_demo_prefix_core_one =
        geo_point file_demo_prefix_p 1 := by
      rcases hD with rfl | rfl
      · change file_prefix_geo_weight [] file_demo_prefix_p
          file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
          file_demo_prefix_path file_demo_prefix_stdin
          (file_prefix_core [] file_demo_prefix_argv file_demo_prefix_envp
            file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
            [file_demo_prefix_nul]) = geo_point file_demo_prefix_p 1
        rw [file_prefix_geo_weight_match]
        rfl
      · show file_geo_weight file_demo_prefix_p file_demo_prefix_argv
          file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
          file_demo_prefix_stdin
          (file_core file_demo_prefix_argv file_demo_prefix_envp
            file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
            [file_demo_prefix_nul]) = _
        rw [file_geo_weight_match]
        rfl
    rw [hw]
    unfold geo_point geo_mass file_demo_prefix_p
    rw [Qpow_succ, Qpow_0]
    grind
  refine ⟨hone _ (Or.inl rfl), hone _ (Or.inr rfl), ?_, ?_⟩
  · show file_prefix_geo_weight [] file_demo_prefix_p file_demo_prefix_argv
      file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
      file_demo_prefix_stdin file_demo_prefix_core_hdr =
      file_geo_weight file_demo_prefix_p file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_prefix_core_hdr
    rw [file_prefix_geo_weight_nil]
  · intro c
    exact file_geometric_prefix_nil_pointwise file_demo_prefix_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_prefix_p_nonneg
      file_demo_prefix_p_le_1 c

/-- THE MISCONFIGURATION, at this file's stop weight: the library's pin
    that an instance whose argv does not name the path is invisible to
    the program it is built for, for this family. -/
theorem file_demo_prefix_misconfiguration_is_invisible :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric_prefix file_example_hdr file_demo_prefix_p
        file_misconfigured_argv [] [] file_example_path []
        file_demo_prefix_p_nonneg file_demo_prefix_p_le_1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []) ∧
      0 < (file_geometric_prefix file_example_hdr file_demo_prefix_p
        file_misconfigured_argv [] [] file_example_path []
        file_demo_prefix_p_nonneg file_demo_prefix_p_le_1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] [BitVec.ofInt 8 65]).core_fs :=
  file_geometric_prefix_needs_argv_to_name_the_path file_demo_prefix_p
    file_demo_prefix_p_nonneg file_demo_prefix_p_le_1
    (by unfold file_demo_prefix_p; grind)
    (by unfold file_demo_prefix_p; grind)

end FileGeometricPrefix

end LinuxSem.Examples.MeasureLibDemo
