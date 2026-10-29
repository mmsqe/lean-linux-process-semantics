/-
  * Examples.RwxFlagNs.Proof — equivalence for rwx-flag-ns, top-level glue

  PROOF-SIDE FILE (not part of the trusted specification).  Discharges
  `strong_universal_T`: observable trace equivalence between the source
  image (Source) and the target image (Target) for all valid stack
  pointers and every valid process input (one `State.ProcInput` record:
  argv, envp, file system, stdin).

  Both binaries store 5 into a writable global byte, load it back and exit
  with it — no output, exit 5, on every input — so the two `to_wexit`
  derivations agree on `([], 5)` and are glued with
  `CatSim.cat_omni_strong_equiv_te`.

  The point of the example is the SOURCE's layout: a single RWX LOAD
  segment (linked without `-z separate-code`; see `source/rwx.lds`), so
  every source fetch goes through the overlay-aware w+x fetch and the
  source derivation is carried by `Common.WxExec`'s frame invariant — see
  `RwxFlagNsSource.lean`.  The target is an ordinary lld-linked binary,
  proved with the standard static-fetch machinery.
-/
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.EquivalenceDefinition.OmniEquivalence
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.ExitSim
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Examples.RwxFlagNs.RwxFlagNsDefs
import LinuxSem.Examples.RwxFlagNs.RwxFlagNsSource
import LinuxSem.Examples.RwxFlagNs.RwxFlagNsTarget
import LinuxSem.Examples.RwxFlagNs.SourceMemImage
import LinuxSem.Examples.RwxFlagNs.TargetMemImage

/- `autoImplicit` is off: in a STATEMENT a bare identifier would otherwise
   become an implicitly bound variable, i.e. a weakened claim rather than a
   compile error. -/
set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.ExitSim
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.OmniEquivalence

namespace LinuxSem.Examples.RwxFlagNs

/-- The two images, as the `Equivalence` functor sees them: each
  snapshot's loaded segments, entry PC and program headers. -/
def source_image : Image :=
  mkImage SourceMemImage.Source.loaded_segments SourceMemImage.SourceMemImage_init_pc
    SourceMemImage.Source.phdrs

def target_image : Image :=
  mkImage TargetMemImage.Target.loaded_segments TargetMemImage.TargetMemImage_init_pc
    TargetMemImage.Target.phdrs

theorem omni_strong_universal :
    omni_strong_universal_T source_image target_image := by
  intro en_source en_target inp Hens Hent Hvalid
  -- the input declares Sv48 (`Run.valid_input` pins it), so the entry
  -- predicate is the literal Sv48 one (`Run.valid_entry_sv48`)
  have Hsv48 := valid_input_va_size inp Hvalid
  rw [valid_entry_sv48 _ _ _ Hsv48] at Hens
  rw [valid_entry_sv48 _ _ _ Hsv48] at Hent
  obtain ⟨Hva, Hve, -, -, -, -, -, -, -, -, -⟩ := Hvalid
  obtain ⟨Hspr, -, -, -⟩ := Hens
  obtain ⟨Hspa, -, -, -⟩ := Hent
  obtain ⟨Hr_lo, Hr_hi, -⟩ := Hspr
  obtain ⟨Ha_lo, Ha_hi, -⟩ := Hspa
  refine cat_omni_strong_equiv_te source_segs SourceMemImage.SourceMemImage_init_pc source_phdrs
    en_source.en_sp en_source.en_brk en_source.en_mmap_base en_source.en_draw
    target_segs TargetMemImage.TargetMemImage_init_pc target_phdrs
    en_target.en_sp en_target.en_brk en_target.en_mmap_base en_target.en_draw
    [] (BitVec.ofInt 64 5) inp ?_ ?_ ?_
  · -- the source steps through the RWX segment; 18 instructions, exit 5
    rw [source_init_pc_val]
    exact RwxFlagNsSource.source_wexit inp.in_argv inp.in_envp Hva Hve en_source.en_sp
      en_source.en_draw Hr_lo Hr_hi inp.in_uid inp.in_hwcap
  · -- the target's six instructions, same answer
    rw [target_init_pc_val]
    exact RwxFlagNsTarget.target_wexit inp.in_argv inp.in_envp en_target.en_sp
      en_target.en_draw Ha_lo Ha_hi inp.in_uid inp.in_hwcap
  · -- Neither binary writes anything, so there is no buffer to bound.
    intro b hb
    simp at hb

/-- The legacy statement, through the compat iff; this is the theorem
    `Checker.v` pins to `Equivalence.SPEC`. -/
theorem strong_universal : strong_universal_T source_image target_image :=
  (strong_universal_iff source_image target_image).mpr omni_strong_universal

end LinuxSem.Examples.RwxFlagNs
