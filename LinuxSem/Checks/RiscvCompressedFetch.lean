/-
  * LinuxProcessSem.Checks.RiscvCompressedFetch — RVC length-correct fetch checks

  Regression checks for the halfword-granular instruction fetch
  ([fetch_half]/[fetch_tail], used by [step] when the four-byte
  [fetch_word] fast path fails).  The case these pin: a compressed
  (2-byte) instruction in the LAST two bytes of an executable segment,
  which a fetch that always read four bytes would fault on.  It is
  fetched from exactly the two bytes it occupies.

  The fixtures use minimally-sized executable segments so the boundary
  is exact: a 2-byte segment can back a compressed instruction but
  never a four-byte read, which is precisely the case [fetch_word]
  could not handle.

  Conventions.  `Z` is `Int`, `N` is `Nat`, `bv n` is
  `BitVec n` and `Z_to_bv n z` is `BitVec.ofInt n z`.  `bv_unsigned` has
  no separate abbreviation: the unsigned value of a `word` is its
  `.toNat` field, and the tuples the checks below compare are `Nat` pairs
  (the same numbers a `Z` spelling would cast).  The
  `Example name : ...` checks are `theorem`s with the same names here.

  (closed computations).  The convention is `by decide`.
  That is what closes every goal whose type has a `DecidableEq`
  instance (`Option`/`List`/`Bool`/`Nat`/`Int`/`BitVec`).  The goals
  stated as an equality of `machine_result machine_state` values cannot
  use it: `machine_state` has function-typed fields (`ms_mem`,
  `ms_rom`), so it has no `DecidableEq` and neither does
  `machine_result machine_state`.  There the same computation is done by
  the kernel and the goal is closed by `rfl`, which is exactly what
  `reflexivity` after such a computation establishes.

  (constructors).  Lean puts the constructors of
  `machine_result` in the inductive's namespace
  (`machine_result.MachineFault`), so a statement mentions them as
  `.MachineFault` / `.MachineUnmodeled`; inside a `match` the bare names
  resolve from the scrutinee's type.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC

/- `st0` keeps its `segs` parameter (the fixture
   list the state is built for) even though the state does not read it;
   Lean's `linter.unusedVariables` warns on
   that, so it is switched off for the file rather than renaming the
   argument away from the signature. -/
set_option linter.unusedVariables false

namespace LinuxSem.Checks.RiscvCompressedFetch

open LinuxSem.Riscv (word reg byte decodeAny bvmap_empty)
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- A 2-byte executable segment holding [c.li a0, 5] (= 0x4515, bytes
    15 45 little-endian).  There is no room for a four-byte read. -/
def cli_segment : Segment where
  seg_base := 0x100
  seg_size := 2
  seg_perms := "r-x"
  seg_bytes := ["1545"]

def cli_segments : List Segment := [cli_segment]

/-- A 2-byte executable segment holding only the LOW half of a 32-bit
    [addi x0,x0,0] (0x00000013, low half 0x0013, bytes 13 00).  The low
    two bits are 0b11, so this parcel announces a 32-bit instruction
    whose second parcel is not mapped. -/
def trunc32_segment : Segment where
  seg_base := 0x100
  seg_size := 2
  seg_perms := "r-x"
  seg_bytes := ["1300"]

def trunc32_segments : List Segment := [trunc32_segment]

/-- A 4-byte executable segment whose first parcel is [c.li a0, 5] and
    whose SECOND parcel is nonzero (ff ff).  Both fetches are defined
    here; they differ in the (decoder-dead) upper 16 bits. -/
def cli_pad_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["1545ffff"]

def cli_pad_segments : List Segment := [cli_pad_segment]

/-- A 4-byte executable segment holding the full 32-bit [addi x0,x0,0]. -/
def addi_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["13000000"]

def addi_segments : List Segment := [addi_segment]

def st0 (segs : List Segment) (pc : word) : machine_state where
  ms_regs := bvmap_empty
  ms_fregs := bvmap_empty
  ms_pc_val := pc
  ms_svc_pending := none
  ms_resv := none
  ms_fcsr := BitVec.ofInt 32 0
  ms_mem := fun _ => none
  ms_rom := fun _ => none

/- ================================================================= -/
/- THE FIX: a compressed instruction in the last 2 bytes of a segment -/
/- ================================================================= -/

/-- The four-byte fast path cannot read this instruction — only two
    bytes are mapped. -/
theorem cli_fetch_word_fails :
    fetch_word cli_segments (BitVec.ofInt 64 0x100) = none := by decide

/-- The length-correct fetch reads exactly the two-byte parcel. -/
theorem cli_fetch_tail_ok :
    fetch_tail cli_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x4515) := by decide

/-- And so [step] runs it: a0 := 5, pc += 2. -/
theorem cli_step_runs :
    (match step cli_segments (st0 cli_segments (BitVec.ofInt 64 0x100)) with
     | .MachineOk ms' =>
         ((ms_pc ms').toNat, (ms_gpr ms' 0).toNat)
     | _ => (0, 0)) = (0x102, 5) := by decide

/- ================================================================= -/
/- A 32-bit instruction still requires all four bytes                -/
/- ================================================================= -/

/-- A 32-bit encoding whose second parcel is unmapped is a genuine
    fault: [fetch_tail] returns [none] and [step] is [MachineFault].
    (Contrast the compressed case above — the length-correct fetch does
    NOT weaken the fault for truly-missing bytes.) -/
theorem trunc32_fetch_tail_fails :
    fetch_tail trunc32_segments (BitVec.ofInt 64 0x100) = none := by decide

theorem trunc32_step_illegal :
    step trunc32_segments (st0 trunc32_segments (BitVec.ofInt 64 0x100))
      = .MachineFault := by rfl

/- ================================================================= -/
/- Agreement where both fetches are defined: the word fetch matches    -/
/- the two-halfword fetch, on representative fixtures.                  -/
/- ================================================================= -/

/-- For a compressed instruction with four mapped bytes, [fetch_word]
    and [fetch_tail] differ only in the upper 16 bits (FFFF vs 0000)
    that the decoder never reads — [decode_any] agrees, so the two
    fetches drive the same step. -/
theorem cli_pad_fetch_word :
    fetch_word cli_pad_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0xFFFF4515) := by decide

theorem cli_pad_fetch_tail :
    fetch_tail cli_pad_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x00004515) := by decide

theorem cli_pad_decode_agrees :
    decodeAny (BitVec.ofInt 32 0xFFFF4515)
      = decodeAny (BitVec.ofInt 32 0x00004515) := by decide

/-- ([bool_decide] rather than a raw equality: the decoded [bv] fields
    reduce to equal values but not syntactically-equal proof terms —
    see the note in [Riscv/Decode].) -/
theorem cli_pad_decodes_to_cli :
    decide (decodeAny (BitVec.ofInt 32 0x00004515)
      = some (.opImm .ADD (BitVec.ofInt 5 10) (BitVec.ofInt 5 0)
              (BitVec.ofInt 12 5), (2 : Int))) = true := by decide

/-- For a full 32-bit instruction with four mapped bytes, the two
    fetches are literally equal. -/
theorem addi_fetch_word_eq_tail :
    fetch_word addi_segments (BitVec.ofInt 64 0x100)
      = fetch_tail addi_segments (BitVec.ofInt 64 0x100) := by decide

/- ================================================================= -/
/- Alignment: the halfword fetch still gates on pc mod 2             -/
/- ================================================================= -/

/-- A misaligned PC faults through the fallback too — [fetch_tail]
    keeps the IALIGN=16 gate, so an odd PC is [None] and [step] is
    [MachineFault] even though the compressed instruction is mapped. -/
theorem cli_misaligned_fetch_tail_none :
    fetch_tail cli_segments (BitVec.ofInt 64 0x101) = none := by decide

theorem cli_misaligned_step_illegal :
    step cli_segments (st0 cli_segments (BitVec.ofInt 64 0x101))
      = .MachineFault := by rfl

/- ================================================================= -/
/- WHY the fetch failed: the model declining vs. the process crashing -/
/- ================================================================= -/

/- The fetch layer declines some reads for reasons no MMU would
   enforce, and [step] must NOT report those as crashes — see
   [RiscvSemantics.fetch_failure].  These fixtures pin the two
   sides of that split on the same instruction bytes, so only the
   segment's permissions and hex distinguish them. -/

/-- A w+x segment holding a perfectly good [addi x0,x0,0].  Real
    hardware executes this page, and so does the model: the static
    [fetch_word] (immutable-code gate, [x /\ ~w]) refuses it, but
    [step] falls through to the overlay-aware [fetch_word_ov], which
    reads the writable overlay first and the segment image underneath —
    the same view data loads use.  (A fetch that refused w+x outright,
    reporting [MachineUnmodeled], would make an RWX-linked source image
    error on its first fetch and satisfy [Run.all_traces_error]
    vacuously.) -/
def wx_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "rwx"
  seg_bytes := ["13000000"]

def wx_segments : List Segment := [wx_segment]

theorem wx_fetch_word_fails :
    fetch_word wx_segments (BitVec.ofInt 64 0x100) = none := by decide

/-- The static projection [fetch_word_wx] (what a w+x image's generated
    fetch lemmas are stated over) and the overlay-aware fetch on an
    empty overlay agree on the image bytes. -/
theorem wx_fetch_word_wx_ok :
    fetch_word_wx wx_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x13) := by decide

theorem wx_fetch_word_ov_ok :
    fetch_word_ov wx_segments (fun _ => none) (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 32 0x13) := by decide

theorem wx_step_runs :
    (match step wx_segments (st0 wx_segments (BitVec.ofInt 64 0x100)) with
     | .MachineOk ms' => (ms_pc ms').toNat
     | _ => 0) = 0x104 := by decide

/-- And the overlay SHADOWS the image: with a store's bytes sitting
    over the fetched address (here rewriting [addi x0,x0,0] into the
    compressed [c.li a0, 5], 0x4515), the next fetch at that address
    executes the NEW bytes — self-modifying code in a w+x segment is
    modeled faithfully rather than proved against stale code. -/
theorem wx_overlay_shadows_fetch :
    (match step wx_segments
        { ms_regs := bvmap_empty, ms_fregs := bvmap_empty
          ms_pc_val := BitVec.ofInt 64 0x100
          ms_svc_pending := none
          ms_resv := none, ms_fcsr := BitVec.ofInt 32 0
          ms_mem := write_to_mem (fun _ => none) (BitVec.ofInt 64 0x100)
                      [BitVec.ofInt 8 0x15, BitVec.ofInt 8 0x45]
          ms_rom := fun _ => none } with
     | .MachineOk ms' =>
         ((ms_pc ms').toNat, (ms_gpr ms' 0).toNat)
     | _ => (0, 0)) = (0x102, 5) := by decide

/-- The same bytes in a segment mapped WITHOUT 'x' is a genuine NX
    fault: a real kernel kills the process. -/
def nx_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "rw-"
  seg_bytes := ["13000000"]

def nx_segments : List Segment := [nx_segment]

theorem nx_step_fault :
    step nx_segments (st0 nx_segments (BitVec.ofInt 64 0x100))
      = .MachineFault := by rfl

/-- An executable, non-writable segment whose snapshot hex is not
    decodable — [hex_nybble] rejects 'A'-'F', so an uppercase image
    silently reads as unmapped (see the [hex_byte_at] guard).  That is a
    defect of the SNAPSHOT, not of the program, so it is unmodeled too:
    a bad image must never be able to launder a target through the
    escape. -/
def badhex_segment : Segment where
  seg_base := 0x100
  seg_size := 4
  seg_perms := "r-x"
  seg_bytes := ["1300A000"]

def badhex_segments : List Segment := [badhex_segment]

theorem badhex_fetch_tail_fails :
    fetch_tail badhex_segments (BitVec.ofInt 64 0x100) = none := by decide

theorem badhex_step_unmodeled :
    step badhex_segments (st0 badhex_segments (BitVec.ofInt 64 0x100))
      = .MachineUnmodeled := by rfl

/-- Fetch is per-PARCEL, and each parcel may come from either KIND of
    executable segment: here the pc's first parcel sits in an ordinary
    r-x segment and the UPPER parcel of the 32-bit encoding falls in a
    w+x segment.  [fetch_tail_any] reads parcel 0 from the static image
    and parcel 1 through the overlay view, and the instruction runs —
    matching hardware, where permissions are per page and an
    instruction may straddle a boundary.  Compare
    [trunc32_step_illegal], the identical shape with the upper parcel
    genuinely unmapped, which stays [MachineFault]. -/
def split_wx_segments : List Segment :=
  [ { seg_base := 0x100, seg_size := 2,
      seg_perms := "r-x", seg_bytes := ["1300"] }
  , { seg_base := 0x102, seg_size := 2,
      seg_perms := "rwx", seg_bytes := ["0000"] } ]

theorem split_wx_first_parcel_ok :
    fetch_half split_wx_segments (BitVec.ofInt 64 0x100)
      = some (BitVec.ofInt 16 0x0013) := by decide

theorem split_wx_step_runs :
    (match step split_wx_segments (st0 split_wx_segments (BitVec.ofInt 64 0x100)) with
     | .MachineOk ms' => (ms_pc ms').toNat
     | _ => 0) = 0x104 := by decide

/-- A pc outside every segment stays a fault: a wild jump is a crash. -/
theorem unmapped_step_fault :
    step [] (st0 [] (BitVec.ofInt 64 0x100)) = .MachineFault := by rfl

end LinuxSem.Checks.RiscvCompressedFetch
