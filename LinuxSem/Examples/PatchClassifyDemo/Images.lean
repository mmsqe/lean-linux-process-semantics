/-
  * Examples.PatchClassifyDemo.Images — the six images of the worked
    patch-classifier example

  DEMO FILE (not part of the trusted specification).  This directory
  carries ONE complete instance of
  [EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY]: six
  images, the five obligations that surface asks about them, and a
  distribution to measure the classifiers' fire sets against.  Without
  such an instance, nothing would show that the statements the surface
  makes can be met.

  ** Why the images are hand-built

  Every other example under `Examples/` snapshots a real compiled
  binary: `elf-snapshot` emits a `MemImage` module whose segment bytes
  are thousands of characters of hex.  That is
  the right shape for an example about a real program and the wrong
  shape for this one, which exists to be READ — the point being made
  is about the six-image SURFACE and not about any particular binary,
  and a reader who cannot see what the programs do cannot check that
  the verdicts proved of them are the right verdicts.

  So the six images here are written out as literal segments, in the
  style of the fixtures in `Checks.Examples` (`Checks.Examples.exit0_segment`
  and its neighbours), and each is three instructions long.  There are
  only two distinct programs:

  - EXIT-0: `addi a7, x0, 93; addi a0, x0, 0; ecall` — the exit
    syscall with status 0.
  - EXIT-1: the same with `addi a0, x0, 1` — status 1.

  and the six images are those two programs under six names:

  | image | program | role                                          |
  |-------|---------|-----------------------------------------------|
  | `O1m` | exit 1  | the first original — the defect: wrong status  |
  | `O2m` | exit 0  | the second original                           |
  | `P1m` | exit 0  | the patch of `O1m` — the defect repaired      |
  | `P2m` | exit 0  | the patch of `O2m` — nothing to repair        |
  | `C1m` | exit 1  | the patch-difference classifier               |
  | `C2m` | exit 1  | the good-input classifier                     |

  Both classifiers fire on every input, and that is HONEST rather than
  degenerate-for-convenience: `O1m` and `P1m` differ on every input
  (one exits 1, the other 0), so the patch-difference classifier must
  fire everywhere; and the two originals differ on every input for the
  same reason, so no input is good and the good-input classifier must
  fire everywhere too.  The demo's README says what this example
  therefore does NOT exercise.

  ** Six names, two programs, six separate obligations

  `O2m`, `P1m` and `P2m` have the same code, as do `C1m` and `C2m`:
  there are two segment lists below, and the six modules' three fields
  are defined from them.  Every obligation stated downstream is
  nonetheless stated of the module it is about, and each image owes
  its own `Equivalence.IMAGE_WF` triple, proved separately below —
  `PatchClassifySpec`'s header is explicit that the two classifier
  images' well-formedness is the pair easiest to forget and worst to
  omit.

  That separation is DISCIPLINE, and the type system does not enforce
  it.  Conversion sees straight through the definitions, so a lemma
  about `O1m` really does close a goal about `C1m` — they name the same
  segment list, the same entry and the same phdr record, and
  `Definition` is transparent.  Nothing here is unsound because of
  that (each obligation is stated and proved on its own), but a reader
  should not take the six names for six checked things: if the two
  classifiers were ever given different code, an obligation quietly
  discharged from the wrong image would start being a claim about a
  program nobody proved it of.  State each one from the facts about its
  own image.

  They are MODULES (`MemImage`) rather than bare `MemImageType.Image`
  records because that is what
  `PatchClassifySpec.SPEC_PATCH_CLASSIFY` takes; the `Image` record for
  each is defined here too, exactly as the module type builds it
  (`mkImage` on the module's three fields), so that the statements in
  `Verdicts` are literally the statements the ascription will need.

  ** The layout: two segments, and why the second one is there

  Each image has a 12-byte executable segment at 0x10000, which is
  also its entry point, and a 336-byte readable segment at 0x11000
  holding the program header table.

  The second segment exists for `Equivalence.image_phdrs_readable`.
  An image's `MemImageType.PhdrInfo` is the one image datum with no
  other tie to its segments — `Run.init_machine_state` splices
  `ph_addr` into the initial stack whatever it says — so the
  well-formedness check asks that the advertised range
  `[ph_addr, ph_addr + ph_num * ph_ent)` really lie inside a readable
  loaded segment.  A one-segment image would fail that check, and the
  failure would be silent in the sense that matters: every obligation
  downstream would still be provable, about an image whose libc could
  not find its own program headers.

  The table's bytes are zeros.  Nothing in this development parses a
  program header table — the model publishes its ADDRESS in the auxv
  and reads no byte of it — so the only property the demo needs of
  those 336 bytes is that they are there and readable, which is what
  `image_phdrs_readable` checks and `phdrs_readable` below proves.
  Read as ELF, 336 zero bytes are six PT_NULL entries: a table a
  loader would accept and a libc would find nothing in.

  ** The encodings, and how they are checked

  Little-endian, one 32-bit instruction per four bytes:

  | offset | segment bytes | word       | instruction     |
  |--------|---------------|------------|-----------------|
  | +0     | `9308d005`    | 0x05d00893 | addi a7, x0, 93 |
  | +4     | `13050000`    | 0x00000513 | addi a0, x0, 0  |
  | +4     | `13051000`    | 0x00100513 | addi a0, x0, 1  |
  | +8     | `73000000`    | 0x00000073 | ecall           |

  (the two +4 rows are the exit-0 and exit-1 programs respectively).
  The first two words are I-type: `imm(12) rs1(5) 000 rd(5) 0010011`,
  with a7 = x17 and a0 = x10.  93 is the exit syscall number
  (`Checks.Examples.exit_sysno`, which also admits 94, exit_group).

  None of that is asserted: the three `decodes` examples below run
  THIS development's decoder on each word and pin the mnemonic, the
  two register numbers and the immediate, so an encoding typed wrong
  fails here rather than turning into a different program that happens
  to exit.  `ecall` is checked against `RiscvSemantics.is_ecall`
  instead of the decoder, because that is the test
  `RiscvSemantics.step` actually applies — ECALL is intercepted before
  decode.

  Each image is a `MemImage` STRUCTURE VALUE (`MemImageType` carries the
  same three fields), so `O1m.loaded_segments` is a projection and the
  sealing file's `IMAGE_WF O1m` is an ordinary structure ascription.
-/
import LinuxSem.EquivalenceDefinition.Equivalence
import LinuxSem.Riscv.DecodeC

/- `autoImplicit` is off for this file: a bare structure-field name would
   otherwise silently become an implicitly bound variable, which in a
   STATEMENT is a weakened claim rather than a compile error. -/
set_option autoImplicit false

/- `maxRecDepth`: `image_phdrs_readable` walks the 336 table bytes through
   the hex reader, a recursion 336 deep — deeper than the default limit,
   though nowhere near a proof obligation's worth of work. -/
set_option maxRecDepth 4096

/- PERF: `image_phdrs_readable` is the expensive thing in this file.  It
   walks the 336 phdr table bytes through the hex reader, and that reader
   is quadratic in the table (`hex_byte_at` converts the whole
   672-character string to a list per byte), so ONE computation costs
   ~25 s of kernel reduction.

   There are, however, only TWO distinct computations to do: the six
   images have two segment lists between them (this file's header), and
   the two differ in their twelve code bytes and in nothing the phdr read
   consults — same bases, same sizes, same phdr record.  So the two
   `phdrs_readable_exit*` lemmas in the `IMAGE_WF` section below are
   computed once each, and the six `*_phdrs_readable` ascriptions that
   `IMAGE_WF` demands are proved by TRANSPORT from the one for their
   image's list.  Six computations made this file 2m34s of `lean` time;
   two make it 51s.

  The SIX statements remain six, one per image, because the ascription
  in the demo's sealing file is these six lemmas.  Only the computation
  is shared.  `decide`
   (without `+kernel`) does not finish within the default heartbeat
   budget here. -/

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.EquivalenceDefinition.Equivalence

namespace LinuxSem.Examples.PatchClassifyDemo

namespace Images

/- =========================================================================
   The two programs
   ========================================================================= -/

/-- `addi a7, x0, 93; addi a0, x0, 0; ecall` — exit(0). -/
def exit0_code_segment : Segment :=
  { seg_base := 0x10000
    seg_size := 12
    seg_perms := "r-x"
    seg_bytes := ["9308d0051305000073000000"] }

/-- `addi a7, x0, 93; addi a0, x0, 1; ecall` — exit(1). -/
def exit1_code_segment : Segment :=
  { seg_base := 0x10000
    seg_size := 12
    seg_perms := "r-x"
    seg_bytes := ["9308d0051305100073000000"] }

/-- The entry point: the first instruction of either program. -/
def demo_init_pc : Nat := 0x10000

/- =========================================================================
   The program header table
   ========================================================================= -/

/-- Six all-zero ELF64 program headers — 6 * 56 = 336 bytes.  See this
    file's header for why the demo carries a table at all and why its
    contents are irrelevant.

  The 672 characters are spelled out literally, so that a reader can
  count them against `seg_size`. -/
def demo_phdr_bytes : String :=
  "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

def demo_phdr_segment : Segment :=
  { seg_base := 0x11000
    seg_size := 336
    seg_perms := "r--"
    seg_bytes := [demo_phdr_bytes] }

/-- Where the table sits, as the auxv advertises it: 6 entries of 56
  bytes at 0x11000 — `ph_ent` and `ph_num` as
    `Checks.Cases.Prelude.demo_phdrs` has them, and an address inside
    the segment above.

    NOT named `demo_phdrs`, deliberately, though the `demo_` prefix
    would match its neighbours here.  That name belongs to
    `Checks.Cases.Prelude.demo_phdrs` and it is a DIFFERENT record
  (0x10040, for a fixture whose segments this demo does not share);
  were both modules imported into `Verdicts`, a bare `demo_phdrs`
  would resolve to whichever of the two was imported last — silently,
  and while the two disagree, which is exactly the failure
  `Checks.Examples` warns about where it names its exit-dispatch lemmas
  apart from their `Common.ExitSim` counterparts.  One name, one
  record. -/
def patchclassify_phdrs : PhdrInfo := ⟨0x11000, 56, 6⟩

/- =========================================================================
   The encodings, run through this development's decoder
   ========================================================================= -/

/-- `addi a7, x0, 93`: an ALU-add immediate into x17 from x0. -/
theorem addi_a7_93_decodes :
    (match decodeAny (BitVec.ofInt 32 0x05d00893) with
     | some (Instr.opImm .ADD rd rs1 imm, 4) =>
         (rd.toNat, rs1.toNat, imm.toNat) = (17, 0, 93)
     | _ => False) := by
  -- The decoder is run first (that is the check), then the pattern match
  -- is discharged by `rfl`.
  have h : decodeAny (BitVec.ofInt 32 0x05d00893)
      = some (Instr.opImm .ADD (17 : reg) (0 : reg) (93 : BitVec 12), 4) := by
    decide
  rw [h]
  rfl

/-- `addi a0, x0, 0`. -/
theorem addi_a0_0_decodes :
    (match decodeAny (BitVec.ofInt 32 0x00000513) with
     | some (Instr.opImm .ADD rd rs1 imm, 4) =>
         (rd.toNat, rs1.toNat, imm.toNat) = (10, 0, 0)
     | _ => False) := by
  have h : decodeAny (BitVec.ofInt 32 0x00000513)
      = some (Instr.opImm .ADD (10 : reg) (0 : reg) (0 : BitVec 12), 4) := by
    decide
  rw [h]
  rfl

/-- `addi a0, x0, 1` — the one word that separates the two programs. -/
theorem addi_a0_1_decodes :
    (match decodeAny (BitVec.ofInt 32 0x00100513) with
     | some (Instr.opImm .ADD rd rs1 imm, 4) =>
         (rd.toNat, rs1.toNat, imm.toNat) = (10, 0, 1)
     | _ => False) := by
  have h : decodeAny (BitVec.ofInt 32 0x00100513)
      = some (Instr.opImm .ADD (10 : reg) (0 : reg) (1 : BitVec 12), 4) := by
    decide
  rw [h]
  rfl

/-- The third word is the syscall boundary `RiscvSemantics.step` tests
    for before it decodes anything. -/
theorem ecall_is_ecall : is_ecall (BitVec.ofInt 32 0x00000073) = true := by
  decide

/- =========================================================================
   The six images
   ========================================================================= -/

/-- The two segment lists.  Each image below defines its own
    `loaded_segments` field from one of them, so that a later change to
    one image's code is an edit to one module rather than to a shared
    constant — but the two names are transparent, and conversion
    identifies the fields that share a list.  See this file's header on
    what that does and does not buy. -/
def exit0_image_segments : List Segment :=
  [exit0_code_segment, demo_phdr_segment]

def exit1_image_segments : List Segment :=
  [exit1_code_segment, demo_phdr_segment]

/-- `O1` — the first original, and the defect the exercise is about: it
    reports failure on every input. -/
def O1m : MemImage where
  loaded_segments := exit1_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/-- `O2` — the second original, which is already right. -/
def O2m : MemImage where
  loaded_segments := exit0_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/-- `P1` — the patch of `O1`: the status word is now 0. -/
def P1m : MemImage where
  loaded_segments := exit0_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/-- `P2` — the patch of `O2`, which had nothing to repair. -/
def P2m : MemImage where
  loaded_segments := exit0_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/-- `C1` — the patch-difference classifier.  It fires on every input,
    which is the right answer here: `O1` and `P1` disagree everywhere. -/
def C1m : MemImage where
  loaded_segments := exit1_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/-- `C2` — the good-input classifier.  It fires on every input, which is
    the right answer here: the two originals are equivalent nowhere. -/
def C2m : MemImage where
  loaded_segments := exit1_image_segments
  init_pc := demo_init_pc
  phdrs := patchclassify_phdrs

/- =========================================================================
   The same six as `MemImageType.Image` records
   ========================================================================= -/

/-- Built exactly as `PatchClassifySpec.SPEC_PATCH_CLASSIFY` builds them,
    so that a theorem proved about `O1_image` is, after unfolding this
    definition and nothing else, the theorem the ascription demands. -/
def O1_image : Image := mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs
def O2_image : Image := mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs
def P1_image : Image := mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs
def P2_image : Image := mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs
def C1_image : Image := mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs
def C2_image : Image := mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs

/- =========================================================================
   `Equivalence.IMAGE_WF` for all six
   ========================================================================= -/

/-! The three anti-vacuity checks, per image, in the exact form
    `Equivalence.IMAGE_WF` states them, so that the ascription in the
    demo's sealing file is these lemmas and not restatements of them.

    They are proved HERE, beside the images, rather than in that file,
    because they are facts about the images: an edit to a segment that
    broke one of them should fail in the file the edit is in.  Twelve of
    the eighteen are one `by decide` each — the images are 348 bytes.  The
    six `*_phdrs_readable` ones are the exception: their computation walks
    the 336-byte table and costs ~25 s apiece, so it is done twice (once
    per distinct segment list, `phdrs_readable_exit0` and
    `phdrs_readable_exit1` immediately below) and the six ascriptions are
    transports across the image definitions.  Every statement is still
    stated of the image it is about.  See the `PERF` note at the head of
    this file.

    The two computed lemmas come first, before any ascription, so that a
    reader meets the two computations before the six checks that borrow
    them.

    `brk_satisfiable` is the one whose failure would sink the example
    silently.  It says a valid program break exists for these segments,
    hence that `Run.valid_entry` is satisfiable at all; without it every
    obligation the demo proves would hold under a premise nothing can
    meet.  The other two rule out the vacuities that run through the
    error escape: an entry point that cannot be fetched, and a phdr
    table that is not there. -/

/-- The phdr read of `exit0_image_segments`: ONE of the two computations
    this file's `PERF` note is about, and the source of `O2`, `P1` and
    `P2`'s `*_phdrs_readable` below.  Stated over the segment list rather
    than over an image, because that is exactly the shareable half: the
    three images built from this list all have `patchclassify_phdrs` as
    their `phdrs`, so the image-level facts differ from this one by
    unfolding and nothing else. -/
theorem phdrs_readable_exit0 :
    image_phdrs_readable exit0_image_segments patchclassify_phdrs = true := by
  decide +kernel

/-- The phdr read of `exit1_image_segments`: the other computation, and
    the source of `O1`, `C1` and `C2`'s `*_phdrs_readable` below.  It is a
    separate check and not a `simpa` from its sibling, deliberately: the
  two lists are genuinely different data, and nothing in this tree
    derives one's readability from the other's. -/
theorem phdrs_readable_exit1 :
    image_phdrs_readable exit1_image_segments patchclassify_phdrs = true := by
  decide +kernel

theorem O1_entry_fetchable :
    image_entry_fetchable O1m.loaded_segments O1m.init_pc = true := by decide
/-- `O1`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit1` — `O1m`'s segments are `exit1_image_segments` by
    definition, and its `phdrs` is `patchclassify_phdrs`, so this is a
    transport across those two definitions and not a second walk of the
    336 bytes.  The same shared computation also serves `C1` and `C2`
    below.  (The statement is still `O1`'s own: unfold `O1m` and it is
    literally `phdrs_readable_exit1`'s conclusion.) -/
theorem O1_phdrs_readable :
    image_phdrs_readable O1m.loaded_segments O1m.phdrs = true := by
  exact phdrs_readable_exit1
theorem O1_brk_satisfiable :
    image_brk_satisfiable O1m.loaded_segments = true := by decide

theorem O2_entry_fetchable :
    image_entry_fetchable O2m.loaded_segments O2m.init_pc = true := by decide
/-- `O2`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit0` (`O2m`'s segments are `exit0_image_segments` and
    its `phdrs` is `patchclassify_phdrs`); the same computation serves `P1`
    and `P2`. -/
theorem O2_phdrs_readable :
    image_phdrs_readable O2m.loaded_segments O2m.phdrs = true := by
  exact phdrs_readable_exit0
theorem O2_brk_satisfiable :
    image_brk_satisfiable O2m.loaded_segments = true := by decide

theorem P1_entry_fetchable :
    image_entry_fetchable P1m.loaded_segments P1m.init_pc = true := by decide
/-- `P1`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit0` — transported across `P1m`'s three fields, which
    name `exit0_image_segments` and `patchclassify_phdrs`. -/
theorem P1_phdrs_readable :
    image_phdrs_readable P1m.loaded_segments P1m.phdrs = true := by
  exact phdrs_readable_exit0
theorem P1_brk_satisfiable :
    image_brk_satisfiable P1m.loaded_segments = true := by decide

theorem P2_entry_fetchable :
    image_entry_fetchable P2m.loaded_segments P2m.init_pc = true := by decide
/-- `P2`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit0`. -/
theorem P2_phdrs_readable :
    image_phdrs_readable P2m.loaded_segments P2m.phdrs = true := by
  exact phdrs_readable_exit0
theorem P2_brk_satisfiable :
    image_brk_satisfiable P2m.loaded_segments = true := by decide

theorem C1_entry_fetchable :
    image_entry_fetchable C1m.loaded_segments C1m.init_pc = true := by decide
/-- `C1`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit1`.  This is the one the file's header calls
    easiest to forget: a classifier image owes its own ascription even
    though its fields are `O1m`'s. -/
theorem C1_phdrs_readable :
    image_phdrs_readable C1m.loaded_segments C1m.phdrs = true := by
  exact phdrs_readable_exit1
theorem C1_brk_satisfiable :
    image_brk_satisfiable C1m.loaded_segments = true := by decide

theorem C2_entry_fetchable :
    image_entry_fetchable C2m.loaded_segments C2m.init_pc = true := by decide
/-- `C2`'s check, DERIVED FROM THE SHARED COMPUTATION
    `phdrs_readable_exit1` — the last of the three that share it. -/
theorem C2_phdrs_readable :
    image_phdrs_readable C2m.loaded_segments C2m.phdrs = true := by
  exact phdrs_readable_exit1
theorem C2_brk_satisfiable :
    image_brk_satisfiable C2m.loaded_segments = true := by decide

/-! The check bites on these images rather than holding of everything:
    dropping the phdr segment breaks `image_phdrs_readable`, and jumping
    a byte past the entry breaks `image_entry_fetchable`.  Both are
    stated over the demo's own segment lists, so they say something about
    THIS example and not only about the definitions
    (`Equivalence.image_phdrs_readable_nil` already covers the empty
    image). -/

theorem phdrs_readable_needs_the_table :
    image_phdrs_readable [exit0_code_segment] patchclassify_phdrs = false := by
  decide

theorem entry_fetchable_needs_a_mapped_entry :
    image_entry_fetchable exit0_image_segments (demo_init_pc + 12) = false := by
  decide

end Images

end LinuxSem.Examples.PatchClassifyDemo
