/-
  * Examples.MeasureLibDemo.FileGeometricPrefixOver — the
    header-conditioned file family over PRINTABLE ASCII, worked

  DEMO FILE (not part of the trusted specification, and not installed).
  [MeasureLib.file_geometric_prefix] fixes the first bytes of the input
  file to a header and spreads the geometric source over what follows,
  every payload byte uniform over all the bytes.
  [MeasureLib.file_geometric_prefix_over] spreads the payload's bytes
  over a fixed ALPHABET instead.  This file instantiates it at the
  printable ASCII bytes, behind the same seven-byte header the all-bytes
  demo uses, and carries it through to a [Measure.weight_bound_T].

  ** Why a task reaches for this one rather than the all-bytes one

  A text-consuming program parses printable input.  Under the all-bytes
  law almost every payload of any length holds a control byte, so a fire
  set described by printable text sits under every threshold for a reason
  that has nothing to do with the library: it is a small fraction of a
  space the program mostly rejects.  Over the printable alphabet the
  payload space IS the text the program reads.

  ** The alphabet, and what is derived from what

  [printable_ascii] is the bytes from the space to the tilde, built as
  `BitVec.ofInt` over [List.seq] from a lower bound and a count, so that
  its size, duplicate-freedom and non-emptiness are arguments about
  [List.seq] and not a literal.  The stop weight, the fire set's first
  byte, the in-alphabet and off-alphabet payloads below are all derived
  from those two numbers or reused from the all-bytes demo; nothing here
  is a literal copy of something defined elsewhere.

  ** The full alphabet

  [file_demo_over_all_bytes_collapse] checks, by computation at a
  concrete core, that the family at [all_bytes] is the all-bytes header
  family: the general lemma is
  [MeasureLib.file_geometric_prefix_over_all_bytes_pointwise].

  Nothing exhibited here is claimed VALID and nothing is claimed
  rejected by any classifier.
-/
import LinuxSem.EquivalenceDefinition.MeasureLib
import LinuxSem.Examples.MeasureLibDemo.FileGeometricPrefix

set_option autoImplicit false

open LinuxSem.Riscv

namespace LinuxSem.Examples.MeasureLibDemo

open LinuxSem.LinuxProcessSem
open LinuxSem.EquivalenceDefinition.FinInput
open LinuxSem.EquivalenceDefinition.Measure
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.MeasureLib
open LinuxSem.LinuxProcessSem.MemImageType
open FileGeometricPrefix

namespace FileGeometricPrefixOver

/- =========================================================================
   The alphabet: printable ASCII
   ========================================================================= -/

/-- The space is the first printable byte and there are ninety-five of
    them, up to the tilde.  Everything below is built from these. -/
def printable_lo : Nat := 32

def printable_count : Nat := 95

def printable_ascii : List (BitVec 8) :=
  List.map (fun n => BitVec.ofInt 8 (Int.ofNat n))
    (List.range' printable_lo printable_count)

theorem printable_ascii_length : printable_ascii.length = printable_count := by
  unfold printable_ascii
  rw [List.length_map, List.length_range']

/-- THE RECEIPT for "space to tilde": the alphabet's first byte is the
    space (hex 20) and its last is the tilde (hex 7e).  Both closed
    computations, so that the lower bound and the count above are pinned
    to the range the prose names rather than trusted. -/
theorem printable_ascii_runs_from_space_to_tilde :
    printable_ascii.headD (BitVec.ofInt 8 0) = BitVec.ofInt 8 32 ∧
      printable_ascii.getLastD (BitVec.ofInt 8 0) = BitVec.ofInt 8 126 := by
  refine ⟨?_, ?_⟩
  · unfold printable_ascii printable_lo printable_count
    decide
  · unfold printable_ascii printable_lo printable_count
    decide

/-- Duplicate-free, by the argument [MeasureLib.all_bytes_nodup] makes for
    the whole range: below the modulus the round trip through `toNat` is
    the identity, so the map is injective on the sequence. -/
theorem printable_ascii_nodup : printable_ascii.Nodup := by
  unfold printable_ascii
  apply NoDup_map_inj
  · intro x y hx hy heq
    rw [List.mem_range'] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    unfold printable_count at hi hj
    have h2 : BitVec.ofNat 8 (printable_lo + 1 * i) =
        BitVec.ofNat 8 (printable_lo + 1 * j) := by
      rw [← BitVec.ofInt_natCast 8 (printable_lo + 1 * i),
        ← BitVec.ofInt_natCast 8 (printable_lo + 1 * j)]
      exact heq
    unfold printable_lo at h2
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 32 + 1 * i < 2 ^ 8),
      Nat.mod_eq_of_lt (by omega : 32 + 1 * j < 2 ^ 8)] at h3
    omega
  · exact List.nodup_range'

theorem printable_ascii_ne : printable_ascii ≠ [] := by
  intro H
  have h := congrArg List.length H
  rw [printable_ascii_length] at h
  exact absurd h (by decide)

/-- The stop weight: one over one more than the alphabet's size, so that
    `1 - p` is the alphabet's size over that, and the per-byte factor
    `(1 - p) * alpha_ratio` is again one over one more than the size —
    every number below is a power of that one denominator. -/
def file_demo_over_p : Rat := (1 : Rat) / (printable_count + 1)

theorem file_demo_over_p_nonneg : 0 ≤ file_demo_over_p := by
  unfold file_demo_over_p printable_count; grind

theorem file_demo_over_p_le_1 : file_demo_over_p ≤ 1 := by
  unfold file_demo_over_p printable_count; grind

/-- The space byte and the letter `A`, derived from the lower bound. -/
def file_demo_over_space : BitVec 8 := BitVec.ofInt 8 (Int.ofNat printable_lo)

def file_demo_over_a : BitVec 8 :=
  BitVec.ofInt 8 (Int.ofNat (printable_lo + 33))

theorem file_demo_over_space_in_alpha :
    alpha_memb printable_ascii file_demo_over_space = true := by
  unfold alpha_memb printable_ascii printable_lo printable_count
    file_demo_over_space
  decide

theorem file_demo_over_a_in_alpha :
    alpha_memb printable_ascii file_demo_over_a = true := by
  unfold alpha_memb printable_ascii printable_lo printable_count
    file_demo_over_a
  decide

/-- ... and the NUL byte the all-bytes demo fires on is a CONTROL byte,
    outside the alphabet. -/
theorem file_demo_prefix_nul_off_alpha :
    alpha_memb printable_ascii file_demo_prefix_nul = false := by
  unfold alpha_memb printable_ascii printable_lo printable_count
    file_demo_prefix_nul
  decide

/- =========================================================================
   The distribution: the same header, program, path and base as the
   all-bytes demo
   ========================================================================= -/

def file_demo_over_cd : CoreDistribution :=
  file_geometric_prefix_over_argv1 printable_ascii printable_ascii_nodup
    printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin
    file_demo_over_p_nonneg file_demo_over_p_le_1

theorem file_demo_over_mass_is_one : file_demo_over_cd.cd_mass = 1 := rfl

theorem file_demo_over_argv_names_path :
    argv_names_path file_demo_prefix_argv file_demo_prefix_path ∧
      file_demo_over_cd = file_geometric_prefix_over printable_ascii
        printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
        file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
        file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
        file_demo_over_p_le_1 :=
  file_geometric_prefix_over_argv1_names_path printable_ascii
    printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_prog file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
    file_demo_over_p_le_1

/- =========================================================================
   The fire set: after the header, the payload begins with a space
   ========================================================================= -/

def file_demo_over_bs : List (BitVec 8) := [file_demo_over_space]

/-- THE CEILING: `(1 - p) * alpha_ratio` at one payload byte, which is one
    ninety-sixth at this stop weight. -/
theorem file_demo_over_fire_ceiling :
    file_geometric_prefix_over_cylinder_mass printable_ascii file_demo_over_p
        file_demo_over_bs = (1 : Rat) / 96 := by
  unfold file_geometric_prefix_over_cylinder_mass alpha_geo_mass alpha_ratio
    file_demo_over_p file_demo_over_bs printable_ascii printable_lo
    printable_count
  rw [List.length_map, List.length_range']
  unfold Qnat
  rw [show [file_demo_over_space].length = 1 from rfl]
  rw [Qpow_succ, Qpow_0]
  grind

theorem file_demo_over_fire_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hcyl : ∀ f, f ∈ l →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_over_bs (fin_core f)) :
    core_sum file_demo_over_cd.cd_weight l ≤ (1 : Rat) / 96 := by
  rw [← file_demo_over_fire_ceiling]
  exact file_geometric_prefix_over_bound printable_ascii printable_ascii_nodup
    printable_ascii_ne file_demo_hdr file_demo_over_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_over_p_nonneg file_demo_over_p_le_1
    file_demo_over_bs l Hnd Hcyl

/-- The payload-length slice at `n = 1`: `p (1 - p)`, with the
    ninety-five alternatives per payload byte charged nothing. -/
theorem file_demo_over_slice_bound_at_one (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      ∃ t, fin_core f = file_prefix_core file_demo_hdr file_demo_prefix_argv
          file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
          file_demo_prefix_stdin t ∧ t.length = 1) :
    core_sum file_demo_over_cd.cd_weight l ≤ (95 : Rat) / 9216 := by
  refine Rat.le_trans (file_geometric_prefix_over_slice_bound printable_ascii
    printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
    file_demo_over_p_le_1 1 l Hnd Hslice) ?_
  show file_demo_over_p * Qpow (1 - file_demo_over_p) 1 ≤ (95 : Rat) / 9216
  unfold file_demo_over_p printable_count
  rw [Qpow_succ, Qpow_0]
  grind

/-- The same slice in the file-length shape, with no premise on the header
    or the alphabet. -/
theorem file_demo_over_slice_bound_by_file_length_at_one (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup)
    (Hslice : ∀ f, f ∈ l →
      fin_core f = file_core file_demo_prefix_argv file_demo_prefix_envp
          file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
          (fs_file file_demo_prefix_path f.fin_image_fs) ∧
        (fs_file file_demo_prefix_path f.fin_image_fs).length =
          file_demo_hdr.length + 1) :
    core_sum file_demo_over_cd.cd_weight l ≤ (95 : Rat) / 9216 := by
  refine Rat.le_trans (file_geometric_prefix_over_slice_bound_by_file_length
    printable_ascii printable_ascii_nodup printable_ascii_ne file_demo_hdr
    file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_over_p_nonneg file_demo_over_p_le_1 1 l Hnd Hslice) ?_
  show file_demo_over_p * Qpow (1 - file_demo_over_p) 1 ≤ (95 : Rat) / 9216
  unfold file_demo_over_p printable_count
  rw [Qpow_succ, Qpow_0]
  grind

/- =========================================================================
   The module, and [Measure.weight_bound_T]
   ========================================================================= -/

def FilePrefixOver_D : DISTRIBUTION where
  w := cd_lift file_demo_over_cd
  M := file_demo_over_cd.cd_mass
  w_nonneg := cd_lift_nonneg file_demo_over_cd
  M_nonneg := by
    show 0 ≤ file_demo_over_cd.cd_mass
    rw [file_demo_over_mass_is_one]
    exact Qle_0_1
  w_core_blind := cd_lift_core_blind file_demo_over_cd

theorem file_demo_over_weight_bound_T_of (C : Image) (b : Rat)
    (Hfire : ∀ f, rejects C f →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_over_bs (fin_core f))
    (Hb : (1 : Rat) / 96 ≤ b) :
    weight_bound_T C FilePrefixOver_D.w FilePrefixOver_D.M b := by
  intro l Hnd Hrej
  show sum_weights (cd_lift file_demo_over_cd) l ≤
    b * file_demo_over_cd.cd_mass
  rw [← core_sum_cd_lift]
  refine Rat.le_trans (file_demo_over_fire_bound l Hnd
    (fun f Hf => Hfire f (Hrej f Hf))) ?_
  rw [file_demo_over_mass_is_one, Rat.mul_one]
  exact Hb

/-- At a round multiplier a task would declare: a classifier that fires
    only on payloads beginning with a space carries at most a fiftieth of
    the mass. -/
theorem file_demo_over_weight_bound_T_fiftieth (C : Image)
    (Hfire : ∀ f, rejects C f →
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_over_bs (fin_core f)) :
    weight_bound_T C FilePrefixOver_D.w FilePrefixOver_D.M ((1 : Rat) / 50) := by
  refine file_demo_over_weight_bound_T_of C _ Hfire ?_
  grind

/- =========================================================================
   Non-vacuity: inside the cylinder, and the mass is a supremum
   ========================================================================= -/

def file_demo_over_core_stop : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space]

def file_demo_over_core_ext : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space, file_demo_over_a]

def file_demo_over_fire_list : List FinProcInput :=
  List.map core_input [file_demo_over_core_stop, file_demo_over_core_ext]

theorem file_demo_over_core_stop_weight :
    file_demo_over_cd.cd_weight file_demo_over_core_stop = (1 : Rat) / 9216 := by
  show file_prefix_over_geo_weight printable_ascii file_demo_hdr
      file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
      file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
      file_demo_over_core_stop = _
  unfold file_demo_over_core_stop
  rw [file_prefix_over_geo_weight_match printable_ascii file_demo_hdr
    file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space] (by
      unfold alpha_only
      simp [file_demo_over_space_in_alpha])]
  show alpha_geo_point printable_ascii file_demo_over_p 1 = (1 : Rat) / 9216
  unfold alpha_geo_point alpha_geo_mass alpha_ratio file_demo_over_p
    printable_ascii printable_lo printable_count
  rw [List.length_map, List.length_range']
  unfold Qnat
  rw [Qpow_succ, Qpow_0]
  grind

theorem file_demo_over_core_ext_weight :
    file_demo_over_cd.cd_weight file_demo_over_core_ext = (1 : Rat) / 884736 := by
  show file_prefix_over_geo_weight printable_ascii file_demo_hdr
      file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
      file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
      file_demo_over_core_ext = _
  unfold file_demo_over_core_ext
  rw [file_prefix_over_geo_weight_match printable_ascii file_demo_hdr
    file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_over_space, file_demo_over_a] (by
      unfold alpha_only
      simp [file_demo_over_space_in_alpha, file_demo_over_a_in_alpha])]
  show alpha_geo_point printable_ascii file_demo_over_p 2 = (1 : Rat) / 884736
  unfold alpha_geo_point alpha_geo_mass alpha_ratio file_demo_over_p
    printable_ascii printable_lo printable_count
  rw [List.length_map, List.length_range']
  unfold Qnat
  rw [Qpow_succ, Qpow_succ, Qpow_0]
  grind

theorem file_demo_over_core_stop_ne_ext :
    file_demo_over_core_stop ≠ file_demo_over_core_ext := by
  intro h
  have h2 := file_prefix_core_inj file_demo_hdr file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin [file_demo_over_space]
    [file_demo_over_space, file_demo_over_a] h
  simp at h2

theorem file_demo_over_fire_slack :
    in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_over_bs file_demo_over_core_stop ∧
      in_file_prefix_cylinder file_demo_hdr file_demo_prefix_argv
        file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
        file_demo_prefix_stdin file_demo_over_bs file_demo_over_core_ext ∧
      (List.map fin_core file_demo_over_fire_list).Nodup ∧
      ¬ ((1 : Rat) / 96 ≤
        core_sum file_demo_over_cd.cd_weight file_demo_over_fire_list) := by
  have hsum : core_sum file_demo_over_cd.cd_weight file_demo_over_fire_list =
      (1 : Rat) / 9216 + 1 / 884736 := by
    show file_demo_over_cd.cd_weight
        (fin_core (core_input file_demo_over_core_stop)) +
        (file_demo_over_cd.cd_weight
          (fin_core (core_input file_demo_over_core_ext)) + 0) = _
    rw [fin_core_core_input, fin_core_core_input,
      file_demo_over_core_stop_weight, file_demo_over_core_ext_weight]
    grind
  refine ⟨⟨[], rfl⟩, ⟨[file_demo_over_a], rfl⟩, ?_, ?_⟩
  · unfold file_demo_over_fire_list
    rw [map_fin_core_core_input]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact file_demo_over_core_stop_ne_ext h
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
      intro h
      simp at h
  · rw [hsum]
    grind

theorem file_demo_over_mass_lower_at_a_thousandth :
    ∃ l : List FinProcInput, (List.map fin_core l).Nodup ∧
      1 - (1 : Rat) / 1000 ≤ core_sum file_demo_over_cd.cd_weight l := by
  unfold file_demo_over_cd
  exact file_geometric_prefix_over_mass_lower_certificate printable_ascii
    printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
    file_demo_over_p_le_1 (1 / 1000 : Rat)
    (by unfold file_demo_over_p printable_count; grind) (by grind)

theorem file_demo_over_mass_not_attained (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    ¬ (core_sum file_demo_over_cd.cd_weight l = 1) := by
  unfold file_demo_over_cd
  exact file_geometric_prefix_over_mass_supremum_not_maximum printable_ascii
    printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
    file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
    file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
    file_demo_over_p_le_1
    (by unfold file_demo_over_p printable_count; grind) l Hnd

theorem file_demo_over_whole_space_bound (l : List FinProcInput)
    (Hnd : (List.map fin_core l).Nodup) :
    core_sum file_demo_over_cd.cd_weight l ≤ 1 :=
  file_geometric_prefix_over_mass_upper printable_ascii printable_ascii_nodup
    printable_ascii_ne file_demo_hdr file_demo_over_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_over_p_nonneg file_demo_over_p_le_1 l Hnd

/- =========================================================================
   The alphabet bites, numerically
   ========================================================================= -/

/-- A one-byte printable payload, and a one-byte CONTROL payload — the NUL
    byte the all-bytes demo fires on. -/
def file_demo_over_core_printable : FinCore := file_demo_over_core_stop

def file_demo_over_core_control : FinCore :=
  file_prefix_core file_demo_hdr file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    [file_demo_prefix_nul]

/-- The all-bytes header family at this file's stop weight, for
    comparison. -/
def file_demo_over_allbytes_ref_cd : CoreDistribution :=
  file_geometric_prefix file_demo_hdr file_demo_over_p file_demo_prefix_argv
    file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
    file_demo_prefix_stdin file_demo_over_p_nonneg file_demo_over_p_le_1

theorem file_demo_prefix_nul_off_alpha_only :
    alpha_only printable_ascii [file_demo_prefix_nul] = false := by
  unfold alpha_only
  simp [file_demo_prefix_nul_off_alpha]

/-- THE ALPHABET BITES: the printable payload weighs `p * (1 - p) / 95`,
    which is one over the square of ninety-six; the control payload
    weighs zero here and positively under the all-bytes header family;
    the mass is `1`. -/
theorem file_demo_over_alphabet_bites :
    file_demo_over_cd.cd_weight file_demo_over_core_printable =
        (1 : Rat) / 9216 ∧
      file_demo_over_cd.cd_weight file_demo_over_core_control = 0 ∧
      file_demo_over_cd.cd_mass = 1 ∧
      0 < file_demo_over_allbytes_ref_cd.cd_weight file_demo_over_core_control := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · exact file_demo_over_core_stop_weight
  · show file_prefix_over_geo_weight printable_ascii file_demo_hdr
        file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
        file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
        file_demo_over_core_control = 0
    unfold file_demo_over_core_control
    exact (file_geometric_prefix_over_off_alphabet_zero printable_ascii
      printable_ascii_nodup printable_ascii_ne file_demo_hdr file_demo_over_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_over_p_nonneg
      file_demo_over_p_le_1 [file_demo_prefix_nul]
      file_demo_prefix_nul_off_alpha_only).1
  · show 0 < file_prefix_geo_weight file_demo_hdr file_demo_over_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_over_core_control
    unfold file_demo_over_core_control
    rw [file_prefix_geo_weight_match]
    show 0 < geo_point file_demo_over_p 1
    unfold geo_point geo_mass file_demo_over_p printable_count
    rw [Qpow_succ, Qpow_0]
    grind

/- =========================================================================
   The full alphabet, numerically
   ========================================================================= -/

def file_demo_over_allbytes_cd : CoreDistribution :=
  file_geometric_prefix_over all_bytes all_bytes_nodup all_bytes_ne
    file_demo_hdr file_demo_over_p file_demo_prefix_argv file_demo_prefix_envp
    file_demo_prefix_fs0 file_demo_prefix_path file_demo_prefix_stdin
    file_demo_over_p_nonneg file_demo_over_p_le_1

/-- THE `alpha = all_bytes` COLLAPSE, at a concrete core and in general:
    the family over the full alphabet agrees with the all-bytes header
    family at the control payload, as a number, and at every core. -/
theorem file_demo_over_all_bytes_collapse :
    file_demo_over_allbytes_cd.cd_weight file_demo_over_core_control =
        file_demo_over_allbytes_ref_cd.cd_weight file_demo_over_core_control ∧
      (∀ c, file_demo_over_allbytes_cd.cd_weight c =
        file_demo_over_allbytes_ref_cd.cd_weight c) := by
  refine ⟨?_, ?_⟩
  · show file_prefix_over_geo_weight all_bytes file_demo_hdr file_demo_over_p
        file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
        file_demo_prefix_path file_demo_prefix_stdin file_demo_over_core_control =
      file_prefix_geo_weight file_demo_hdr file_demo_over_p
        file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
        file_demo_prefix_path file_demo_prefix_stdin file_demo_over_core_control
    exact file_prefix_over_geo_weight_all_bytes file_demo_hdr file_demo_over_p
      file_demo_prefix_argv file_demo_prefix_envp file_demo_prefix_fs0
      file_demo_prefix_path file_demo_prefix_stdin file_demo_over_core_control
  · intro c
    exact file_geometric_prefix_over_all_bytes_pointwise all_bytes_nodup
      all_bytes_ne file_demo_hdr file_demo_over_p file_demo_prefix_argv
      file_demo_prefix_envp file_demo_prefix_fs0 file_demo_prefix_path
      file_demo_prefix_stdin file_demo_over_p_nonneg file_demo_over_p_le_1 c

/-- THE MISCONFIGURATION, at this file's stop weight, for this family. -/
theorem file_demo_over_misconfiguration_is_invisible :
    ¬ argv_names_path file_misconfigured_argv file_example_path ∧
      0 < (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr
        file_demo_over_p file_misconfigured_argv [] [] file_example_path []
        file_demo_over_p_nonneg file_demo_over_p_le_1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] []) ∧
      0 < (file_geometric_prefix_over file_example_alpha
        file_example_alpha_nodup file_example_alpha_ne file_example_hdr
        file_demo_over_p file_misconfigured_argv [] [] file_example_path []
        file_demo_over_p_nonneg file_demo_over_p_le_1).cd_weight
        (file_prefix_core file_example_hdr file_misconfigured_argv [] []
          file_example_path [] [BitVec.ofInt 8 65]) ∧
      fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] []).core_fs =
        fs_file file_other_path
          (file_prefix_core file_example_hdr file_misconfigured_argv [] []
            file_example_path [] [BitVec.ofInt 8 65]).core_fs :=
  file_geometric_prefix_over_needs_argv_to_name_the_path file_demo_over_p
    file_demo_over_p_nonneg file_demo_over_p_le_1
    (by unfold file_demo_over_p printable_count; grind)
    (by unfold file_demo_over_p printable_count; grind)

end FileGeometricPrefixOver

end LinuxSem.Examples.MeasureLibDemo
