/-
  * Examples.PatchClassifyDemo.Sealed — the demo ascribed to the
    submission surface

  DEMO FILE (not part of the trusted specification), and the only file
  in this directory whose content is its TYPE.  Nothing is proved
  here: every definition below is a bare alias for a theorem `Images`
  or `Obligations` already proved, and the file's whole job is to make
  the kernel check that those theorems are the ones
  `EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY` asks
  for.

  ** Why an ascription, rather than a list of theorem names

  `PatchClassifySpec`'s header gives the reason and it is worth
  restating at the point where it bites: a submission's proofs are
  ASCRIBED to the structure, so a proof of a different statement —
  about a different image, under a weakened predicate, with a bound
  about some other classifier — fails to typecheck here rather than
  passing quietly.  A directory of theorems with the right names
  establishes nothing; the same directory accepted by a
  `SPEC_PATCH_CLASSIFY` value establishes that the six images really
  do satisfy the surface.

  That is the difference this file makes to the demo, and it is the
  reason the aliases below are bare.  If any of them had to be
  restated — an adapter, a proof block, an `apply` that reshuffled
  quantifiers — the restatement would be the thing to audit, and the
  theorems in `Obligations` would no longer be the theorems the
  surface demands.  They are not restated.  Each definition is one
  identifier, and the ascription is what checks it.

  ** `Equivalence.IMAGE_WF` for all six, first

  The six well-formedness ascriptions come first because without them
  the five obligations are consistent with the demo having proved
  nothing at all.  Every obligation quantifies over valid
  `Run.ExecEntry`s, and an image with none satisfies all of them
  vacuously: `Classifier.decides_vacuous_no_entries` says such an
  image DECIDES EVERY property, contradictory ones included, and
  `Classifier.accepts_vacuous_no_entries` says it accepts every input,
  which empties `Classifier.rejects` and makes
  `Measure.weight_bound_T` hold at every multiplier for every weight.
  A file that pinned the five statements and the two numbers while
  skipping the well-formedness would have pinned exactly that: five
  theorems and two numerals, all seven free.

  `PatchClassifySpec`'s header names the two CLASSIFIER images as the
  pair easiest to forget and worst to omit, since they are the ones
  the vacuity lemmas above are about; `C1wf` and `C2wf` are therefore
  not optional decoration on the four an equivalence checker would
  already ascribe.  The eighteen lemmas they are built from are proved
  in `Images`, beside the segments they are about, so that an edit
  breaking one fails in the file the edit is in.

  ** What the ascription does NOT establish

  It does not make the demo interesting; it makes it CHECKED.  Both
  classifiers fire on every valid finite input and both bounds are the
  trivial multiplier — the honest answers for this pair of originals,
  argued in `Obligations`' header and in the demo's README, which also
  names the refinement that would make the numbers say more.  The
  ascription is indifferent to that: it would accept a sharper
  instance and it accepts this one, and a reader who wants to know how
  much the demo says should read the bites at the end of `Obligations`
  rather than this file.

  In particular, `b1` and `b2` below being `1` is not a claim that `1`
  is the least provable multiplier.  `Obligations`'
  `demo_b_zero_refutable` and `demo_b_half_refutable` show two smaller
  values are refutable, which is what makes the multiplier load-bearing
  rather than decorative, and they leave every `b` strictly between
  `144495 / 262144` and `1` open.

  `Print Assumptions`.  Every result in this directory is proved
  outright — no escape hatches, no extra postulates — so the kernel's
  assumption set is empty to begin with, and there is nothing for a
  per-file audit to print; `scripts/check.sh` runs that audit tree-wide
  instead.
-/
import LinuxSem.Examples.PatchClassifyDemo.Images
import LinuxSem.Examples.PatchClassifyDemo.Distribution
import LinuxSem.Examples.PatchClassifyDemo.Obligations
import LinuxSem.EquivalenceDefinition.PatchClassifySpec

/- `autoImplicit` is off for this file: a bare structure-field name would
   otherwise silently become an implicitly bound variable, which in a
   STATEMENT is a weakened claim rather than a compile error. -/
set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.EquivalenceDefinition.Equivalence
open LinuxSem.EquivalenceDefinition.MustExit
open LinuxSem.EquivalenceDefinition.Classifier
open LinuxSem.EquivalenceDefinition.Measure
open LinuxSem.EquivalenceDefinition.PatchClassifySpec

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Sealed

open Images
open Distribution
open Obligations

/- =========================================================================
   `Equivalence.IMAGE_WF` for all six images
   ========================================================================= -/

/-! Three aliases each, in the order `Equivalence.IMAGE_WF` declares
    them.  `brk_satisfiable` is the one whose failure would sink the
    example silently — it is what inhabits the entry space, and hence
    what makes `Run.valid_entry` satisfiable at all — and the other two
    close the vacuity routes that run through the error escape. -/

theorem O1wf : IMAGE_WF O1m :=
  ⟨O1_entry_fetchable, O1_phdrs_readable, O1_brk_satisfiable⟩

theorem O2wf : IMAGE_WF O2m :=
  ⟨O2_entry_fetchable, O2_phdrs_readable, O2_brk_satisfiable⟩

theorem P1wf : IMAGE_WF P1m :=
  ⟨P1_entry_fetchable, P1_phdrs_readable, P1_brk_satisfiable⟩

theorem P2wf : IMAGE_WF P2m :=
  ⟨P2_entry_fetchable, P2_phdrs_readable, P2_brk_satisfiable⟩

/-- The two the header says are easiest to forget. -/
theorem C1wf : IMAGE_WF C1m :=
  ⟨C1_entry_fetchable, C1_phdrs_readable, C1_brk_satisfiable⟩

theorem C2wf : IMAGE_WF C2m :=
  ⟨C2_entry_fetchable, C2_phdrs_readable, C2_brk_satisfiable⟩

/- =========================================================================
   The submission surface, sealed
   ========================================================================= -/

/-- The five obligations and the two bounds, at the argument order
    `PatchClassifySpec.SPEC_PATCH_CLASSIFY` declares — `O1m P1m O2m P2m C1m
    C2m`, the two originals interleaved with their patches, then the two
    classifiers, then the distribution.

    Every field is ONE identifier from `Obligations`, deliberately: if any
    of them had to be restated — an adapter, a proof block, an `apply` that
    reshuffled quantifiers — the restatement would be the thing to audit,
    and `Obligations`' theorems would no longer be the theorems the surface
    demands.  They are not restated; the ascription is what checks them.

    `DemoDist` enters as trusted metadata and not as a claim: its two
    obligations are about the weight function (nonnegativity, and
    `Measure.DISTRIBUTION`'s `w_core_blind`), both discharged in
    `Distribution` from `MeasureLib`'s lifting lemmas, and neither is
    something a submission would have to establish. -/
def DemoSealed : SPEC_PATCH_CLASSIFY O1m P1m O2m P2m C1m C2m DemoDist where
  strong_universal := P1_P2_strong_universal
  classifies_diff := C1_classifies_patch_diff
  classifies_good := C2_classifies_good_inputs
  b1 := 1
  b2 := 1
  bound_diff := C1_weight_bound
  bound_good := C2_weight_bound

/- =========================================================================
   The error-free flavor, which the demo also satisfies
   ========================================================================= -/

/-- `PatchClassifySpec.SPEC_PATCH_CLASSIFY_ERROR_FREE` is the surface a
    task OPTS IN to: it replaces the patch obligation with
    `Equivalence.strong_universal_error_free_T`, which additionally demands
    that neither patched binary ever reaches the error transition.  Its
    header explains why that is a separate module type rather than an
    extension — the stronger reading is unprovable for any binary that can
    legitimately crash, so no task should get it by default.

    These two patches cannot crash: they execute three instructions and
    exit, at every valid entry on every input, which is what
    `Obligations.P1_P2_strong_universal_error_free` says.  So the demo
    satisfies the stronger surface too, and the ascription below is the
    evidence.  The other five declarations are the same identifiers as
    above, deliberately: the classifiers are asked the same questions in
    both flavors and the measure layer never sees the difference. -/
def DemoSealedErrorFree :
    SPEC_PATCH_CLASSIFY_ERROR_FREE O1m P1m O2m P2m C1m C2m DemoDist where
  strong_universal_error_free := P1_P2_strong_universal_error_free
  classifies_diff := C1_classifies_patch_diff
  classifies_good := C2_classifies_good_inputs
  b1 := 1
  b2 := 1
  bound_diff := C1_weight_bound
  bound_good := C2_weight_bound

/- =========================================================================
   Reading the two bounds
   ========================================================================= -/

/-! `PatchClassifySpec`'s header is explicit that a consuming checker
    PRINTS `b1` and `b2` and does not compare them against an expected
    value, because a `Q` equality is propositional.  Under Lean's `Rat`
    the two coincide, so the two `rfl`s below are the whole of that
    discipline — they say the printed multiplier reads as one, and nothing
    more. -/
theorem demo_b1_reads_as_one : DemoSealed.b1 = 1 := rfl

theorem demo_b2_reads_as_one : DemoSealed.b2 = 1 := rfl

/-- And the printed bound is an UPPER bound rather than a measurement,
    which is `Measure.weight_bound_mono`: a proof at `b` is a proof at
    every larger `b'`.  Instantiated here so that the honest reading of the
    demo's numbers — "the fire set weighs at most this much" — is exhibited
    rather than asserted. -/
theorem demo_bound_diff_at_two :
    weight_bound_T C1_image DemoDist.w DemoDist.M 2 :=
  weight_bound_mono C1_image DemoDist.w DemoDist.M 1 2
    (by rw [Distribution.demo_M_is_one]; grind) (by grind) DemoSealed.bound_diff

end Sealed

end LinuxSem.Examples.PatchClassifyDemo
