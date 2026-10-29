/-
  * LinuxProcessSem.RiscvSemantics — user-mode RISC-V step over Linux virtual memory


  TRUST BOUNDARY: this file is part of the trusted specification.

  Uses the RV64GC ISA semantics of `Riscv/`
  (LinuxSem.Riscv): registers and addresses are
  [word = bv 64], memory bytes are [byte = bv 8], register indices
  are [reg = bv 5].

  This file does two things:

  (a) ISA WRAPPING.  It wraps the ISA decoder/executor into a
      total-or-illegal step function over this project's
      [machine_state]: fetch the instruction from the STATIC segment
      image, check for ECALL (intercepted before decode so the syscall
      model can take over), otherwise decode with [DecodeC.decode_any]
      (32-bit or compressed), build the instruction's EFFECT TREE
      with [Sem.exec] and interpret it ([interp_eff]); a failing
      interpretation is the illegal transition.

      - COMPRESSED instructions (RV64GC) are decoded and executed, and
        instruction fetch is LENGTH-CORRECT: [fetch_tail] reads the
        first 16-bit parcel and only reads the second when that parcel
        marks a 32-bit instruction, so a 2-byte instruction in the
        last 2 mapped bytes of a segment (or just before a
        non-executable page) fetches from exactly those two bytes
        instead of spuriously faulting.  A four-byte [fetch_word] fast
        path handles the common case; it is sound under the segments'
        non-overlap invariant (see the [fetch_tail] note).
      - LR/SC reservations are MODELED ([ms_resv]).
      - F/D and the fcsr Zicsr accesses are MODELED: the machine
        state carries the FP register file ([ms_fregs]) and fcsr
        ([ms_fcsr]) and threads both through [Sem.core], so IEEE
        arithmetic and its accrued exception flags are ordinary
        state transitions here rather than a modeling boundary.

  (b) VIRTUAL MEMORY.  What the program can read, write and execute is
      not a hardware fact — it is the address space Linux sets up for a
      user process, honouring the per-segment ELF page permissions
      (r/w/x):
      - the loaded segments as a read-only backing ([ms_rom]), gated
        on 'r' so a load from a PROT_NONE page faults ([memory_read]);
      - a writable overlay for everything the process stores
        ([ms_mem]), with stores outside the WRITABLE view made
        illegal (the SIGSEGV analogue, [store_ok]) — a store must
        land on memory the process actually has mapped, not merely
        miss the read-only segments;
      - instruction fetch gated on 'x', so jumping into a
        non-executable segment faults instead of running its bytes as
        code (the NX guarantee).  Fetch reads the view a real machine
        executes: for an IMMUTABLE executable segment (x and not w —
        stores into it are illegal, [store_ok]) it reads the static
        segment image directly ([code_read]/[fetch_word]); for a
        WRITABLE executable segment (w+x, as GNU ld's default
        [-z noseparate-code] produces by merging .text with the
        writable sections) it reads the writable overlay first and
        falls back to the static image
        ([code_read_ov]/[fetch_word_ov]), exactly as data loads do —
        so a store into a w+x segment is observed by the next fetch
        at that address, and an ordinary w+x binary (one that never
        stores over its own code) executes its image bytes faithfully;
      - the READ vs. WRITABLE views ([ms_read_byte] vs.
        [ms_writable_byte]) that the syscall specs use for buffer
        checks (the copy_to_user/EFAULT split).
      Segment data stays in the [N]-based [MemImageType.Segment];
      all range
      arithmetic against segments happens in [Z] over [bv_unsigned].

  ECALL detection:
  RISC-V ECALL encoding = 0x00000073.  When detected, we record the
  syscall number from register a7 (x17) in [ms_svc_pending]; the
  trace semantics (Run.v) dispatches it on the next step.  Linux
  riscv64 ABI: syscall number in a7, args in a0–a5 (x10–x15).

  representation..
  - `PrimString.string` / `Uint63` appear only for the generated
    hex-chunk decoding helpers.  Here hex chunks are `String`s and
    characters are `Char` (whose `toNat` is the Unicode code point, the
    value `Uint63.to_Z` returned), so the helpers range over `String`.
    `PrimString.get`/`Uint63` index arithmetic becomes `String.length`
    plus a total, `Option`-returning index (`String.toList[i]?`); the
    bounds guard is kept exactly (see `hex_byte_at`).
  - `Z` is `Int`, `N` is `Nat`, `bv n` is `BitVec n`, `bv_extract lo len`
    is `bits lo len`, `bv_concat` is `BitVec.append`, `Z_to_bv n z` is
    `BitVec.ofInt n z`.  Record field projections are `.field`.
  - A `Global Strategy 100` at the end of the file only tuned lazy
    reduction, which has no Lean counterpart.  The DEFINITIONS it named
    are all present below.
-/
import LinuxSem.Riscv.Sem
import LinuxSem.Riscv.DecodeC
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType

namespace LinuxSem.LinuxProcessSem.RiscvSemantics

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem.MemImageType

/-! ** Machine state

    [machine_state] holds the general-purpose registers (as a
    [bvmap 5 word], the SAME representation [Sem.core] uses, so [step]
    threads the register file through the ISA layer with no conversion;
    missing keys read as 0 and register x0 is forced to 0 by the
    read/write wrappers per the RISC-V spec), the program counter, a
    pending-ecall slot, the LR/SC reservation, writable memory, and
    read-only memory.

    Register convention (Linux riscv64 syscall ABI):
    - x17 (a7): syscall number
    - x10–x15 (a0–a5): syscall arguments
    - x10 (a0): return value -/
structure machine_state where
  /-- General-purpose registers. -/
  ms_regs        : BvMap word
  /-- Floating-point registers. -/
  ms_fregs       : BvMap word
  /-- Program counter. -/
  ms_pc_val      : word
  /-- Pending syscall number (set by ECALL). -/
  ms_svc_pending : Option word
  /-- LR/SC reservation. -/
  ms_resv        : Option word
  /-- The stored fcsr (fflags + frm). -/
  ms_fcsr        : BitVec 32
  /-- The writable overlay. -/
  ms_mem         : word → Option byte
  /-- The read-only static segment image. -/
  ms_rom         : word → Option byte

def ms_pc (st : machine_state) : word := st.ms_pc_val

def ms_sp (st : machine_state) : word := reg_get st.ms_regs 2

/-- [ms_gpr st i] returns the i-th syscall argument register (a0–a5).
    Maps argument index to physical register: arg i → x(10+i). -/
def ms_gpr (st : machine_state) (i : Nat) : word :=
  reg_get st.ms_regs (BitVec.ofInt 5 (10 + (i : Int)))

/-- Read physical register by number (x0 reads as 0). -/
def ms_reg (st : machine_state) (r : reg) : word :=
  if bv_eqb r 0 then (0 : word) else reg_get st.ms_regs r

/-- Update a physical register. x0 writes are silently discarded. -/
def set_reg (st : machine_state) (r : reg) (v : word) : machine_state :=
  if bv_eqb r 0 then st else { st with ms_regs := bvmapSet r v st.ms_regs }

/-- Set a0 (= x10), the syscall return register. -/
def set_gpr0 (ms : machine_state) (ret : word) : machine_state :=
  set_reg ms 10 ret

/-- Write [data] byte-by-byte into [mem] starting at [addr]. -/
def write_to_mem (mem : word → Option byte) (addr : word) (data : List byte) :
    word → Option byte :=
  match data with
  | [] => mem
  | b :: rest =>
    write_to_mem (fun a => if bv_eqb a addr then some b else mem a)
                 (addr + 1) rest

/-- Set a0 to [ret] and write [data] into memory at [buf_addr] — the
    post-state of a syscall that returns a value and fills a caller buffer. -/
def set_gpr0_write_buf (ms : machine_state) (ret : word)
    (buf_addr : word) (data : List byte) : machine_state :=
  let ms' := set_reg ms 10 ret
  { ms' with ms_mem := write_to_mem ms'.ms_mem buf_addr data }

/-! ** Machine step result

    A single machine step either succeeds ([MachineOk]) or does not, and
    the two ways of not succeeding are kept APART, because they mean
    opposite things about this development:

    - [MachineFault] — the PROGRAM did something fatal and the model says
      so FAITHFULLY: a misaligned pc, a jump to an address that is
      unmapped or mapped without 'x', a load from an unmapped address, a
      store to an address the process has not mapped writable — into a
      read-only segment, or into nothing at all (the SIGSEGV
      analogue) — or an
      [ebreak] (the SIGTRAP analogue), or an encoding the ISA defines
      to be illegal in every implementation — the SIGILL analogue, which
      arrives on two routes: an undecodable word
      [DecodeC.is_defined_illegal] flags (the all-zero parcel), and a
      decodable instruction [Sem.exec] answers with [Sem.EDefinedIllegal]
      (a write to a read-only CSR; see [Sem.csr_write_illegal]).  Linux
      turns the hart's illegal-instruction exception into SIGILL with
      [ILL_ILLOPC] in [do_trap_insn_illegal]
      (arch/riscv/kernel/traps.c, v6.18.46), so a real
      Linux process dies here too.  A source binary is allowed to fault;
      the model has modeled it.

    - [MachineUnmodeled] — the MODEL gave up: a word this development's
      decoder does not decode (unless the ISA defines it illegal — see
      above), an ISA-level [EIllegal] boundary node, or a fetch
      [code_read] declined for a modeling
      reason rather than a hardware one (a w+x segment, or snapshot hex
      the decoder cannot read — see [fetch_failure]).  Nothing is
      claimed about what the real process would do.  A source binary
      reaching this makes its equivalence statement suspect (see
      [Run.reaches_unmodeled] and the [modeled] clause of
      [Equivalence.strong_equiv]), which is exactly why the
      classification is fail-closed: anything that might be a gap in the
      decoder, in the ISA semantics, or in the memory image counts
      as [MachineUnmodeled], and only failures a real process would also
      suffer count as [MachineFault].

    Both drive the same explicit error transition in [Run.sstep]; the
    distinction is carried alongside it, not instead of it.  The machine
    itself is deterministic — all non-determinism in the semantics lives
    in the syscall model. -/
inductive machine_result (A : Type) where
  | MachineOk (result : A)
  | MachineFault
  | MachineUnmodeled

/-! ** Unified memory read helpers

    [ms_read_byte] checks writable memory first, then falls back to
    read-only memory. -/

def ms_read_byte (ms : machine_state) (addr : word) : Option byte :=
  match ms.ms_mem addr with
  | some b => some b
  | none   => ms.ms_rom addr

def ms_read_bytes_aux (ms : machine_state) (addr : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match ms_read_byte ms addr with
    | some b =>
      match ms_read_bytes_aux ms (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

def ms_read_bytes (ms : machine_state) (addr len : word) : Option (List byte) :=
  ms_read_bytes_aux ms addr (word_to_nat len)

def ms_read_u64 (ms : machine_state) (addr : word) : Option word :=
  match ms_read_bytes ms addr (BitVec.ofInt 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

def word_to_le_bytes (n : Nat) (v : word) : List byte :=
  Z_to_le_bytes n (v.toNat : Int)

/-! ** Hex decode helpers

    Segment bytes are stored as a hex string (lowercase, no spaces).
    These functions decode a contiguous range of bytes from a hex
    string without materialising the whole segment.  Offsets are [N]
    (they index into the [N]-based [Segment] snapshot data).

     the encoding works on `PrimString.string` and `char63`
    (a `Uint63`); here hex chunks are `String` and `Char`, and the
    offset arithmetic is `Nat`. -/

/-- The value of one hex digit, or 16 for a non-digit (accepted range:
    `'0'..'9'` and `'a'..'f'`, lowercase only). -/
def hex_nybble (c : Char) : Nat :=
  if decide (48 ≤ c.toNat ∧ c.toNat ≤ 57) then c.toNat - 48
  else if decide (97 ≤ c.toNat ∧ c.toNat ≤ 102) then c.toNat - 87
  else 16

/-- Decode the byte at byte offset `i` (i.e. the two hex digits
    `2i`, `2i+1`) of the hex string `s`.

     the guard tests `2i+1 < s.len` (the `Uint63` guard
    `ltb ci1 s_len || eqb ci1 (s_len - 1)` is subsumed by `ci1 < s_len`
    for every real offset: the second disjunct is `ci1 = s_len - 1`,
    which is already `< s_len`), then reads the two characters with
    `PrimString.get`.  Lean's `String.get` is partial, so the two
    characters are read through the total `String.toList[i]?`; the
    bounds guard makes the `none` arms unreachable, exactly as
    the guard above does. -/
def hex_byte_at (s : String) (i : Nat) : Option byte :=
  let ci  := 2 * i
  let ci1 := 2 * i + 1
  if ci1 < s.length then
    match s.toList[ci]?, s.toList[ci1]? with
    | some hi, some lo =>
      let h := hex_nybble hi
      let l := hex_nybble lo
      if h < 16 && l < 16 then some (BitVec.ofInt 8 ((h * 16 + l : Nat) : Int))
      else none
    | _, _ => none
  else none

def hex_read_bytes (s : String) (off : Nat) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    match hex_byte_at s off with
    | none => none
    | some b =>
      match hex_read_bytes s (off + 1) n' with
      | none => none
      | some rest => some (b :: rest)

/-- Read through the bounded primitive strings that represent one logical ELF
    segment.  Chunk boundaries have no memory-semantic meaning: a load or
    instruction fetch may cross one exactly as it crosses any other byte in
    the segment. -/
def segment_byte_at (chunks : List String) (off : Nat) : Option byte :=
  match chunks with
  | [] => none
  | chunk :: rest =>
      let chunk_bytes := chunk.length / 2
      if off < chunk_bytes
      then hex_byte_at chunk off
      else segment_byte_at rest (off - chunk_bytes)

def segment_read_bytes (bytes : List String) (off : Nat) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
      match segment_byte_at bytes off with
      | none => none
      | some b =>
          match segment_read_bytes bytes (off + 1) n' with
          | none => none
          | some rest => some (b :: rest)

/-! ** Memory read

    Linear scan over [loaded_segments] looking for a segment whose
    address range covers [addr .. addr + n - 1].  The range check is in
    [Z] over unsigned values (segments are [N]-based snapshot data and
    never wrap). -/
def find_segment (segs : List Segment) (addr : Int) (n : Int) : Option Segment :=
  match segs with
  | [] => none
  | seg :: rest =>
    let base : Int := (seg.seg_base : Int)
    let top  : Int := base + (seg.seg_size : Int)
    if base ≤ addr && addr + n ≤ top
    then some seg
    else find_segment rest addr n

/-- Read [n] bytes at [addr] from segment [seg], each byte taken from
    the writable overlay [m] when present and from the segment's static
    image otherwise — the per-segment analogue of [ov_read_bytes],
    used by [code_read_ov] to fetch from a WRITABLE executable (w+x)
    segment.  Fail on any byte that neither view supplies. -/
def seg_ov_read_bytes (m : word → Option byte) (seg : Segment)
    (addr : word) (n : Nat) : Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    let cur :=
      match m addr with
      | some b => some b
      | none => segment_byte_at seg.seg_bytes
                  (addr.toNat - seg.seg_base)
    match cur with
    | some b =>
      match seg_ov_read_bytes m seg (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-! ** Store-target permission check

    Does [addr .. addr + n) avoid every NON-writable loaded segment?
    Machine stores whose target overlaps a segment mapped without 'w'
    (.text, .rodata) are ILLEGAL instructions — the explicit error
    transition, matching the SIGSEGV a real MMU delivers.  (Fetch
    reading the static segment image ([code_read]) is sound for exactly
    these segments: a non-writable executable segment is immutable.
    Fetch from a WRITABLE executable segment reads through the overlay
    instead ([code_read_ov]), so a store into a w+x segment — legal,
    the segment is writable — is observed by later fetches.) -/
def range_avoids_ro_segs (segs : List Segment) (addr n : Int) : Bool :=
  segs.all (fun seg =>
    seg_writable seg ||
      !(decide ((seg.seg_base : Int) < addr + n) &&
        decide (addr < (seg.seg_base : Int) + (seg.seg_size : Int))))

section WithMemImage

variable (mi_loaded_segments : List Segment)

/-- DATA read: return [addr .. addr+n) only if it lies in a single
    READABLE segment.  A load whose target segment lacks the 'r' flag
    (a PROT_NONE / write-only page) reads as unmapped — the SIGSEGV
    analogue — exactly as a store outside the writable view is
    illegal (see [store_ok]).  Used for machine loads and,
    via [Run.init_machine_state]'s [ms_rom], for syscall source
    buffers. -/
def memory_read (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (addr.toNat : Int) (n : Int) with
  | some seg =>
    if seg_readable seg then
      let off := addr.toNat - seg.seg_base
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- INSTRUCTION read: like [memory_read] but gated on the EXECUTABLE
    ('x') flag rather than 'r'.  Instruction fetch ([fetch_word]) reads
    through this, so a jump into a non-executable segment (.rodata,
    .data, or an anonymous data mapping) fetches [none] and faults
    ([MachineFault]) instead of executing the bytes as code — the
    NX / W^X guarantee a real kernel installs.  Kept separate from
    [memory_read] because reading data from an executable page and
    executing bytes from a readable-only page are governed by different
    ELF flags.

    This function covers only IMMUTABLE executable segments (x and not
    w): it reads the STATIC segment image, not the writable overlay
    ([ms_mem]), which is sound exactly because stores into non-writable
    segments are illegal ([store_ok]).  A WRITABLE executable segment
    (w+x) is handled by [code_read_ov] below, which reads through the
    overlay the way data loads do; [step] dispatches between the two.
    The two gates are complementary ([x /\ ~w] here, [x /\ w] there),
    so on any given segment exactly one of them can succeed. -/
def code_read (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (addr.toNat : Int) (n : Int) with
  | some seg =>
    if seg_executable seg && !seg_writable seg then
      let off := addr.toNat - seg.seg_base
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

/-- INSTRUCTION read from a WRITABLE executable (w+x) segment: the
    complementary gate to [code_read] ([x /\ w] rather than [x /\ ~w]).
    A w+x segment's bytes are mutable — stores into it are legal — so
    fetch must read the same view data loads do: the writable overlay
    [m] first, falling back to the static segment image
    ([seg_ov_read_bytes]).  A store over an instruction in a w+x
    segment is therefore observed by the next fetch of that address,
    exactly as on real hardware (self-modifying code is MODELED, not
    refused — though the proof layer only follows programs whose code
    range the overlay never touches; see the frame lemmas in
    Common/WxExec.v).

    [code_read_wx] is the STATIC projection of the same read — the
    segment image alone, same [x /\ w] gate, no overlay parameter.  It
    is what the generated per-example fetch lemmas are stated over for
    a w+x image (a pure function of the snapshot, so a closed computation
    can check it); [code_read_ov] coincides with it whenever the overlay
    misses the fetched range. -/
def code_read_wx (addr : word) (n : Nat) : Option (List byte) :=
  match find_segment mi_loaded_segments (addr.toNat : Int) (n : Int) with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      let off := addr.toNat - seg.seg_base
      segment_read_bytes seg.seg_bytes off n
    else none
  | none => none

def code_read_ov (m : word → Option byte) (addr : word) (n : Nat) :
    Option (List byte) :=
  match find_segment mi_loaded_segments (addr.toNat : Int) (n : Int) with
  | some seg =>
    if seg_executable seg && seg_writable seg then
      seg_ov_read_bytes m seg addr n
    else none
  | none => none

/-! ** Why a fetch failed: the MODEL declining vs. the PROCESS crashing

    The combined fetch ([code_read] for immutable code, [code_read_ov]
    for w+x code) declines for several different reasons, and they do
    not mean the same thing about this development:

    1. the byte lies outside every loaded segment — a wild jump into
       unmapped memory, which a real process suffers as SIGSEGV;
    2. the byte lies in a segment mapped without 'x' (.rodata, .data) —
       the NX fault a real kernel delivers;
    3. the byte lies in a fetchable segment but neither the overlay nor
       the [seg_bytes] hex supplies it (a malformed or truncated
       snapshot, e.g. uppercase hex, which [hex_nybble] rejects) — a
       limitation of the snapshot, not of the process.

    Cases 1 and 2 are [MachineFault]; case 3 is the MODEL giving up and
    must be [MachineUnmodeled].  Getting this wrong is not
    cosmetic: calling case 3 a crash would let a source binary that
    runs perfectly on real hardware prove [Run.all_traces_error], take
    [Equivalence.equiv]'s escape and free the target unanalyzed, while
    [Equivalence.modeled] — which deliberately tolerates faults —
    certified the run as covered.  That is exactly the vacuity the
    [modeled] clause exists to rule out.  (A w+x segment is not a
    reason: it is fetched through the overlay and simply executes.)

    So the classification is stated on the FAULT side, per byte, and
    everything else is the model's own limit — which keeps it fail-closed
    under a decline this note has not enumerated (a fetch whose bytes
    straddle two abutting executable segments, say: [find_segment] wants
    ONE segment to cover the whole read, and real hardware does not).
    [fetch_byte_traps a] is true exactly when a real MMU would trap on
    fetching the single byte [a]: it is unmapped (case 1) or its page
    lacks 'x' (case 2).

    [fetch_failure] applies it per NEEDED BYTE rather than per pc: a
    32-bit instruction whose first parcel is fetchable and whose second
    parcel is genuinely unmapped is a fault (pinned by
    [Checks/RiscvCompressedFetch.trunc32_step_illegal]) even though the
    pc itself sits in a perfectly good segment. -/
def fetch_byte_traps (a : word) : Bool :=
  match find_segment mi_loaded_segments (a.toNat : Int) 1 with
  | none => true                        -- case 1: unmapped — a real fault
  | some seg => !seg_executable seg     -- case 2: no 'x' — a real NX fault

/-! ** Writable memory view

    The byte at [addr] as the KERNEL may write it: defined on exactly
    the addresses the process has writable-mapped — the writable
    overlay merged over segments carrying the 'w' permission
    (.data/.bss).  Addresses only in non-writable segments
    (.text/.rodata) and unmapped addresses read [none].  Threaded into
    each syscall as [SyscallInput.in_wmem] (the copy_to_user EFAULT
    analogue); compare [ms_read_byte], the READ view used for source
    buffers. -/
def wview (m : word → Option byte) (addr : word) : Option byte :=
  match m addr with
  | some b => some b
  | none =>
      match find_segment mi_loaded_segments (addr.toNat : Int) 1 with
      | some seg =>
          if seg_writable seg
          then segment_byte_at seg.seg_bytes (addr.toNat - seg.seg_base)
          else none
      | none => none

def ms_writable_byte (ms : machine_state) (addr : word) : Option byte :=
  wview mi_loaded_segments ms.ms_mem addr

/-! ** The store bound

    A byte the PROCESS may store to, and the SAME view the kernel
    writes through ([ms_writable_byte] above, threaded into each
    syscall as the copy_to_user/EFAULT gate).  A store outside it is
    the SIGSEGV a real MMU delivers.

    This has to be checked, and checking only the read-only segments is
    not enough, because the overlay [m] is a TOTAL function: writing
    through it CREATES a mapping wherever it lands.  Without a bound, a
    store to any address off a read-only segment succeeds — below the
    stack, in the gap above the image, anywhere — and the process can
    then read the value back.  Real Linux faults there.

    The consequence is not just infidelity in the small.  [init_sp] and
    the initial break are quantified INDEPENDENTLY for the two binaries
    (ASLR; [Run.valid_sp], [Run.valid_brk], and see the note at
    [Equivalence.strong_universal_T]).  Unbounded stack or heap growth
    therefore collides with something at an address that depends on
    those choices, so a program whose recursion or allocation is driven
    by its input diverges from itself between two admissible
    quantifications — and [strong_universal] is then arguably false
    even for a reference against itself.  Real Linux faults at an
    ASLR-INDEPENDENT point instead: the RLIMIT_STACK window, which
    [Run.init_machine_state] already zero-maps as
    [init_sp - stack_max_size, init_sp).

    So the ledger this needs already exists, and is exactly [wview]:
    the initial stack block and its zero window, every brk/mmap grant
    ([Run.apply_zeros]) minus everything [munmap] took back
    ([Run.apply_unmaps]), and the writable segments (.data/.bss).
    Nothing new is tracked; the store is simply held to the same notion
    of writable memory the syscalls already use.

    LOADS need no such bound — [ov_read_bytes] already fails on any
    byte that is neither in the overlay nor in a readable segment.
    Without [store_ok] the two would be asymmetric. -/
def store_ok (m : word → Option byte) (a : word) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
      match wview mi_loaded_segments m a with
      | some _ => store_ok m (a + 1) n'
      | none => false

/-! ** Instruction fetch

    Read 4 bytes from [addr] out of an IMMUTABLE executable segment
    ([code_read]'s [x /\ ~w] gate: the static image is the truth there,
    and a jump into a non-executable segment faults instead of running
    its bytes as code), and assemble them little-endian into a 32-bit
    word.  The w+x counterpart is [fetch_word_ov] below.

    Fetch also returns [none] on a MISALIGNED [addr]: RV64 with the C
    extension has IALIGN=16, so fetching at pc mod 2 <> 0 is an
    instruction-address-misaligned trap — the process observably
    crashes, same as a bad fetch.  (With compressed instructions
    modeled, pc ≡ 2 (mod 4) is a legal fetch address.)  [Sem]
    never produces a misaligned pc from a jump — jal/branch
    immediates are even and jalr clears bit 0 per the spec — so this
    gate covers the one PC source no jump path constrains, a
    misaligned [init_pc] taken verbatim from the ELF [e_entry]. -/
def fetch_word (addr : word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else
  match code_read mi_loaded_segments addr 4 with
  | some (b0 :: b1 :: b2 :: b3 :: []) => some (le4 b3 b2 b1 b0)
  | _ => none

/-- Word fetch from a WRITABLE executable (w+x) segment, through the
    overlay-first view ([code_read_ov]); same alignment gate as
    [fetch_word].  Because the two gates are complementary, at most one
    of [fetch_word]/[fetch_word_ov] can succeed at any address; [step]
    tries [fetch_word] first, so the immutable-code fast path is
    unchanged by the existence of this one. -/
def fetch_word_ov (m : word → Option byte) (addr : word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else
  match code_read_ov mi_loaded_segments m addr 4 with
  | some (b0 :: b1 :: b2 :: b3 :: []) => some (le4 b3 b2 b1 b0)
  | _ => none

/-- The STATIC projection of [fetch_word_ov]: the w+x segment's image
    bytes alone ([code_read_wx]).  A pure function of the snapshot, so
    the generated per-example fetch lemmas for a w+x image are stated
    over it and closed by evaluation; [fetch_word_ov] rewrites to it
    whenever the overlay misses the fetched range (Common/WxExec.v). -/
def fetch_word_wx (addr : word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else
  match code_read_wx mi_loaded_segments addr 4 with
  | some (b0 :: b1 :: b2 :: b3 :: []) => some (le4 b3 b2 b1 b0)
  | _ => none

/-! ** Halfword-granular instruction fetch (RVC-correct)

    RISC-V determines an instruction's length from the low bits of its
    FIRST 16-bit parcel: [instr[1:0] <> 0b11] is a 2-byte compressed
    instruction, [instr[1:0] = 0b11] a (here) 4-byte one.  A fetch must
    therefore read ONLY the parcels the instruction actually occupies —
    a compressed instruction in the last two bytes of an executable
    segment (or immediately before a non-executable page) must fetch
    from just those two bytes, never a spurious four-byte read that
    faults on bytes the instruction does not use.

    [fetch_half] reads one aligned 16-bit parcel through [code_read]
    (same 'x' ∧ ¬'w' gate as [fetch_word]).  [fetch_tail] is the
    length-correct fetch: read parcel 0; if it is compressed, that is
    the whole instruction (zero-extended into the 32-bit word the
    decoder consumes — [decode_any] reads only [bits 0 16] for a
    compressed encoding, and the low two bits <> 0b11 keep it clear of
    the ECALL test); if it is a 32-bit instruction, read parcel 1 and
    concatenate.

    [step] uses [fetch_word] as a fast path and falls back to
    [fetch_tail] only when the four-byte read fails — exactly the
    boundary case above.  Reading four bytes when only two are needed is
    harmless under the model's snapshot invariant that loaded segments
    do not overlap (enforced when the memory image is built): the extra
    parcel is either within the same executable segment (readable, so
    the fast path succeeds and the decoder ignores it for a compressed
    instruction) or outside it (so the four-byte read fails and the
    fallback runs).  With overlapping segments the two reads could
    resolve to different segments, so the fast path is NOT a generic
    no-op; the agreement is pinned on representative fixtures in
    [Checks/RiscvCompressedFetch.v] rather than asserted for arbitrary
    segment lists. -/
def fetch_half (addr : word) : Option (BitVec 16) :=
  match code_read mi_loaded_segments addr 2 with
  | some (b0 :: b1 :: []) => some (le2 b1 b0)
  | _ => none

def fetch_tail (addr : word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else
  match fetch_half mi_loaded_segments addr with
  | none => none
  | some h0 =>
    if (bits 0 2 h0).toNat == 3 then
      -- 32-bit instruction: read the upper parcel too.
      match fetch_half mi_loaded_segments (addr + 2) with
      | some h1 => some (h1.append h0)
      | none => none
    else
      -- compressed: two bytes suffice; the upper parcel is decoder-dead.
      some ((0 : BitVec 16).append h0)

/-- The w+x halfword fetch, and the COMBINED (either-kind-of-segment)
    halfword and length-correct fetches.  [fetch_half_any] reads a
    16-bit parcel from whichever executable segment holds it — the
    static image for immutable code, the overlay-first view for w+x
    code (the two gates are complementary, so the ordering is
    dispatch, not preference).  [fetch_tail_any] is [fetch_tail]'s
    length-correct algorithm over [fetch_half_any], so each parcel of
    an instruction may independently come from either kind of segment
    (matching hardware, where segment permissions are per page and an
    instruction may straddle a boundary). -/
def fetch_half_ov (m : word → Option byte) (addr : word) : Option (BitVec 16) :=
  match code_read_ov mi_loaded_segments m addr 2 with
  | some (b0 :: b1 :: []) => some (le2 b1 b0)
  | _ => none

def fetch_half_any (m : word → Option byte) (addr : word) : Option (BitVec 16) :=
  match fetch_half mi_loaded_segments addr with
  | some h => some h
  | none => fetch_half_ov mi_loaded_segments m addr

def fetch_tail_any (m : word → Option byte) (addr : word) : Option (BitVec 32) :=
  if addr.toNat % 2 ≠ 0 then none
  else
  match fetch_half_any mi_loaded_segments m addr with
  | none => none
  | some h0 =>
    if (bits 0 2 h0).toNat == 3 then
      match fetch_half_any mi_loaded_segments m (addr + 2) with
      | some h1 => some (h1.append h0)
      | none => none
    else
      some ((0 : BitVec 16).append h0)

/-! ** ECALL instruction detector

    RISC-V ECALL encoding is exactly 0x00000073.  (A compressed
    instruction can never alias this test: the low 2 bits of 0x73 are
    11, the uncompressed marker.) -/
def is_ecall (w : BitVec 32) : Bool :=
  bv_eqb w (BitVec.ofInt 32 0x73)

/-! ** ISA-semantics integration

    [Sem.exec] maps a decoded instruction and the core state
    ([Sem.core]: integer and FP registers, pc, fcsr, LR/SC
    reservation) to a finite first-order EFFECT TREE whose nodes are
    the operations the semantics does not interpret itself.  This
    section supplies the interpreter: [ELoad]s read through the
    writable overlay with segment fallback and fail on any unmapped
    byte; [EStore]s fail on any range with a byte outside the
    writable view ([store_ok] — the SIGSEGV analogue); the boundary
    nodes [EIllegal]/[EDefinedIllegal]/[EEcall]/[EEbreak] all map to
    failure (ebreak is
    fatal here, and ECALL is intercepted BEFORE decode by [step], so
    [EEcall] is unreachable anyway), split between [MachineFault] and
    [MachineUnmodeled] as described at [interp_eff].  A failed interpretation propagates
    unchanged through [step].

    The machine's register files [ms_regs]/[ms_fregs] are
    [bvmap 5 word]s — the SAME representation as [Sem.core]'s
    [c_regs]/[c_fregs] — so [step] passes them into [exec] and
    projects them back verbatim, with no conversion in either
    direction; [ms_fcsr] is likewise [Sem.core]'s [c_fcsr]
    unchanged. -/

/-- Byte counts for the [ELoad]/[EStore] widths (which are in BITS:
    8/16/32/64).  Total by construction; other widths never occur. -/
def width_bytes (n : Nat) : Nat :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

def width_bytesZ (n : Nat) : Int :=
  match n with
  | 8 => 1 | 16 => 2 | 32 => 4 | 64 => 8
  | _ => 0

/-- *** Overlay-then-segments memory read

    Read [n] bytes starting at [addr]: each byte comes from the
    writable overlay if present, else from the loaded segments; fail
    on any miss. -/
def ov_read_bytes (m : word → Option byte) (addr : word) (n : Nat) :
    Option (List byte) :=
  match n with
  | 0 => some []
  | n' + 1 =>
    let cur :=
      match m addr with
      | some b => some b
      | none => match memory_read mi_loaded_segments addr 1 with
                | some (b :: _) => some b
                | _ => none
    match cur with
    | some b =>
      match ov_read_bytes m (addr + 1) n' with
      | some rest => some (b :: rest)
      | none => none
    | none => none

/-- *** Memory accesses reported by the tree interpreter

    A successful instruction reports every data-memory range it accessed.
    The report is separate from [machine_state]: it is an observation of one
    step, not architectural state.  A caller can therefore inspect accesses
    without adding an observation field to every machine-state literal in the
    development.  A range is reported only after its load or store permission
    check succeeds.  The complete list is returned with the successful
    instruction, so a consumer can validate all ranges atomically before
    accepting the transition. -/
abbrev memory_access := word × Nat

structure access_report (A : Type) where
  access_value : A
  accessed_ranges : List memory_access

/-- The constructor name `mkAccessReport`. -/
def mkAccessReport {A : Type} (v : A) (rs : List memory_access) : access_report A :=
  ⟨v, rs⟩

def drop_access_report {A : Type} (r : machine_result (access_report A)) :
    machine_result A :=
  match r with
  | .MachineOk report => .MachineOk report.access_value
  | .MachineFault => .MachineFault
  | .MachineUnmodeled => .MachineUnmodeled

/-- *** The tree interpreter

    Structural recursion over the effect tree; the writable overlay
    is threaded through.  [ELoad n a k]'s continuation receives the
    [width_bytes n] loaded bytes assembled little-endian ([n] is the
    access width in bits); [EStore n a v k] writes the [width_bytes n]
    little-endian bytes of [v] into the overlay, but only once every
    byte of the range is known writable ([store_ok]).  The boundary
    nodes are all terminal
    failures, but of the two DIFFERENT kinds (see [machine_result]):

    - [EEbreak] is a [MachineFault] — a real process takes SIGTRAP and
      dies, so the model is faithful here;
    - [EFault] is a [MachineFault] — the ISA itself defines the
      execution to trap (today: a misaligned lr/sc/amo, the SIGBUS
      analogue; see [Sem.amo_aligned]), so this is the process
      crashing, not the model declining;
    - a failed [ELoad] (unmapped byte) and a failed [EStore] (any byte
      of the range outside the writable view — a non-writable segment,
      or memory that was never mapped at all; see [store_ok]) are
      [MachineFault]s too: the SIGSEGV analogue;
    - [EIllegal] is [MachineUnmodeled] — the ISA semantics declined to
      give this instruction a meaning (an unknown CSR address, or a
      reserved FP rounding mode).  [EEcall] is unreachable (ECALL is
      intercepted before decode in [step]) and is classified
      [MachineUnmodeled] with the rest of the boundary;
    - [EDefinedIllegal] is a [MachineFault] — the ARCHITECTURE, not this
      model, defines the instruction to raise an illegal-instruction
      exception (today: a write to a read-only CSR address, which is what
      GNU as's [unimp] and hence every fired -fsanitize-trap check is),
      so the process takes SIGILL and dies.  This is the same split
      [EFault]/[EIllegal] draw, one level up: see [Sem.csr_write_illegal]
      for why the address alone settles it.

     this is the one place where the proof relies on Lean's
    eliminator feature.  The recursion is on `k (...)` — a value returned
    by the continuation field — which a guard checker accepts; Lean's
    kernel-generated recursor
    for `eff` quantifies the induction hypothesis over the whole
    continuation (`(a : BitVec n) → motive (k a)`), so the same
    recursion is accepted here with the SAME type and the SAME
    semantics: no fuel, no partiality, no unsafe. -/
def interp_eff_accesses (mi_loaded_segments : List Segment) (t : eff)
    (m : word → Option byte) :
    machine_result (access_report (core × (word → Option byte))) :=
  match t with
  | .eDone c => .MachineOk (mkAccessReport (c, m) [])
  | .eEbreak _ | .eFault _ | .eDefinedIllegal _ => .MachineFault
  | .eIllegal _ | .eEcall _ => .MachineUnmodeled
  | .eLoad n a k =>
      match ov_read_bytes mi_loaded_segments m a (width_bytes n) with
      | some bs =>
        match interp_eff_accesses mi_loaded_segments
                (k (bits 0 n (le_bytes_to_word bs))) m with
        | .MachineOk report =>
          .MachineOk
            (mkAccessReport report.access_value
               ((a, width_bytes n) :: report.accessed_ranges))
        | .MachineFault => .MachineFault
        | .MachineUnmodeled => .MachineUnmodeled
      | none => .MachineFault
  | .eStore n a v k =>
      if store_ok mi_loaded_segments m a (width_bytes n)
      then
        match interp_eff_accesses mi_loaded_segments k
                (write_to_mem m a
                   (Z_to_le_bytes (width_bytes n) (v.toNat : Int))) with
        | .MachineOk report =>
          .MachineOk
            (mkAccessReport report.access_value
               ((a, width_bytes n) :: report.accessed_ranges))
        | .MachineFault => .MachineFault
        | .MachineUnmodeled => .MachineUnmodeled
      else .MachineFault

/-- There is one trusted interpreter.  Callers that do not need access
    observations project them away from its result. -/
def interp_eff (t : eff) (m : word → Option byte) :
    machine_result (core × (word → Option byte)) :=
  drop_access_report (interp_eff_accesses mi_loaded_segments t m)

/-- Erasing an access report recovers the authoritative architectural
    interpreter exactly.  This is the bridge used by the existing symbolic
    proof library: access accounting adds an observation, never a second ISA
    semantics. -/
theorem drop_interp_eff_accesses (t : eff) (m : word → Option byte) :
    drop_access_report (interp_eff_accesses mi_loaded_segments t m)
      = interp_eff mi_loaded_segments t m :=
  rfl

/-- ** Decode-and-execute a fetched instruction word

    Given the 32-bit word [w] the fetch produced (a full 32-bit
    encoding, or a compressed 16-bit encoding zero-extended into the low
    parcel — see [fetch_tail]):

    1. Check if the word is [ecall] (Linux riscv64 syscall boundary).
       If yes: record [ms_reg st 17] (a7) as the pending syscall number.
    2. Otherwise: decode ([DecodeC.decode_any], 32-bit or compressed),
       build the effect tree ([Sem.exec]) and interpret it
       ([interp_eff]).  The core is built from the machine state with
       both register maps and fcsr passed through UNCHANGED
       ([ms_regs]/[ms_fregs] and [c_regs]/[c_fregs] share the [bvmap]
       representation) and projected back the same way.
    3. On decode failure: [MachineUnmodeled], fail closed — an
       undecodable word may be a genuinely illegal encoding, but it
       may equally be a hole in THIS decoder, and the two are not in
       general distinguishable from here.  The one exception is a word
       the architecture pins as illegal in every implementation:
       [DecodeC.is_defined_illegal] (today, exactly the all-zero low
       parcel), where real hardware is guaranteed to trap and Linux
       delivers SIGILL — the process dies there too, so that word is a
       [MachineFault], per the classification rule on
       [machine_result].  A DECODABLE instruction can be defined-illegal
       too, and that decision belongs to [Sem.exec] rather than here: it
       answers [Sem.EDefinedIllegal], which [interp_eff] faults on.  On
       interpretation failure:
       whichever of [MachineFault]/[MachineUnmodeled] [interp_eff]
       reports.  Either way the trace semantics turns it into the
       explicit error transition; only [MachineUnmodeled] additionally
       marks the configuration as one the model failed to cover. -/
def decode_exec_accesses (st : machine_state) (w : BitVec 32) :
    machine_result (access_report machine_state) :=
  if is_ecall w then
    .MachineOk (mkAccessReport
      { st with ms_svc_pending := some (ms_reg st 17) } [])
  else
    match decodeAny w with
    | none =>
      if isDefinedIllegal w then .MachineFault else .MachineUnmodeled
    | some (i, isz) =>
      match interp_eff_accesses mi_loaded_segments
              (exec (BitVec.ofInt 64 isz) i
                { c_regs := st.ms_regs
                  c_fregs := st.ms_fregs
                  c_pc := st.ms_pc_val
                  c_fcsr := st.ms_fcsr
                  c_resv := st.ms_resv })
              st.ms_mem with
      | .MachineFault => .MachineFault
      | .MachineUnmodeled => .MachineUnmodeled
      | .MachineOk report =>
        let c := report.access_value.1
        let m' := report.access_value.2
        .MachineOk (mkAccessReport
          { ms_regs := c.c_regs
            ms_fregs := c.c_fregs
            ms_pc_val := c.c_pc
            ms_svc_pending := none
            ms_resv := c.c_resv
            ms_fcsr := c.c_fcsr
            ms_mem := m'
            ms_rom := st.ms_rom }
          report.accessed_ranges)

def decode_exec (st : machine_state) (w : BitVec 32) :
    machine_result machine_state :=
  drop_access_report (decode_exec_accesses mi_loaded_segments st w)

/- ** Step function

    Fetch the instruction at [ms_pc st] and hand its word to
    [decode_exec].  The fetch takes the fast path first: a single
    four-byte [fetch_word] from immutable code.  If that fails it tries
    the four-byte w+x fetch [fetch_word_ov] (the complementary gate:
    exactly one of the two can apply to any address).  If that fails
    too — the interesting cases being a compressed instruction whose
    second parcel lies outside the fetchable segment, a boundary a
    four-byte read cannot cross, or an instruction straddling two
    abutting executable segments — it retries with the length-correct
    combined halfword fetch [fetch_tail_any] (see the [fetch_tail] note
    for why the fast path is sound under the non-overlap snapshot
    invariant).

    A failed fetch is classified by WHY it failed, via [fetch_failure]:
    a misaligned PC, or a needed byte that is unmapped or
    non-executable, is a [MachineFault] — a wild jump is a crash, NOT a
    clean exit, and it is a crash the real
    process suffers too, so it is modeled.  A needed byte the fetch
    declined for the MODEL's own reasons (snapshot hex the decoder
    cannot read, or a read straddling abutting segments that
    [find_segment] declines) is a [MachineUnmodeled] instead. -/

/-- Classify a fetch at [addr] that every fetch path declined.  A
    misaligned pc is a genuine instruction-address-misaligned trap.
    Otherwise inspect exactly the bytes the instruction needs — parcel 0
    always, and parcel 1 only when parcel 0 was readable and announced a
    32-bit encoding, which is the only remaining way [fetch_tail_any]
    can fail — and report [MachineFault] if any of them would trap on
    real hardware.  If none would, the decline was this model's own
    ([MachineUnmodeled]). -/
def fetch_failure (m : word → Option byte) (addr : word) :
    machine_result machine_state :=
  if addr.toNat % 2 ≠ 0 then .MachineFault
  else
    let traps :=
      (fetch_byte_traps mi_loaded_segments addr
         || fetch_byte_traps mi_loaded_segments (addr + 1)
         || match fetch_half_any mi_loaded_segments m addr with
            | none => false           -- parcel 0 is mapped and executable
            | some _ =>               -- ...so the failure is in parcel 1
              (fetch_byte_traps mi_loaded_segments (addr + 2)
                 || fetch_byte_traps mi_loaded_segments (addr + 3)))
    if traps then .MachineFault else .MachineUnmodeled

def step_accesses (st : machine_state) :
    machine_result (access_report machine_state) :=
  match fetch_word mi_loaded_segments (ms_pc st) with
  | some w => decode_exec_accesses mi_loaded_segments st w
  | none =>
    match fetch_word_ov mi_loaded_segments st.ms_mem (ms_pc st) with
    | some w => decode_exec_accesses mi_loaded_segments st w
    | none =>
      match fetch_tail_any mi_loaded_segments st.ms_mem (ms_pc st) with
      | some w => decode_exec_accesses mi_loaded_segments st w
      | none =>
        match fetch_failure mi_loaded_segments st.ms_mem (ms_pc st) with
        | .MachineOk st' => .MachineOk (mkAccessReport st' [])
        | .MachineFault => .MachineFault
        | .MachineUnmodeled => .MachineUnmodeled

def step (st : machine_state) : machine_result machine_state :=
  drop_access_report (step_accesses mi_loaded_segments st)

theorem drop_decode_exec_accesses (st : machine_state) (w : BitVec 32) :
    drop_access_report (decode_exec_accesses mi_loaded_segments st w)
      = decode_exec mi_loaded_segments st w :=
  rfl

theorem drop_step_accesses (st : machine_state) :
    drop_access_report (step_accesses mi_loaded_segments st)
      = step mi_loaded_segments st :=
  rfl

end WithMemImage

/-! ## Sanity checks

    There is no closed computation to re-use for this file, so these are
    added here: a small two-segment image, byte and
    word reads through the read view, the writable view and the store
    bound, the fetch paths (32-bit, compressed, NX/unmapped
    classification), an `exec` of a tiny instruction sequence, and a
    hand-built effect tree through the interpreter. -/

section Sanity

/-- `addi x1, x0, 5` (0x00500093) at 0x1000, then `ecall` (0x00000073). -/
private def codeSeg : Segment := ⟨0x1000, 8, "r-x", ["9300500073000000"]⟩

/-- Read/write data, eight bytes, little-endian 0xDEADBEEF at 0x2000. -/
private def dataSeg : Segment := ⟨0x2000, 8, "rw-", ["efbeadde00000000"]⟩

/-- A w+x segment: store-then-fetch (self-modifying code) is legal there. -/
private def wxSeg : Segment := ⟨0x4000, 8, "rwx", ["9300500000000000"]⟩

/-- One compressed instruction (`c.li x1, 5`, 0x4095) in exactly two
    mapped bytes — the length-correct fetch boundary case. -/
private def cSeg : Segment := ⟨0x3000, 2, "r-x", ["9540"]⟩

/-- A non-executable data segment: fetching from it is an NX fault. -/
private def nxSeg : Segment := ⟨0x5000, 4, "rw-", ["00000000"]⟩

private def segs : List Segment := [codeSeg, dataSeg, wxSeg, cSeg, nxSeg]

/-- The image the checks run against: a `MemImage` is the interface a
    generated snapshot module provides (`Run.init_machine_state` threads
    its `loaded_segments` into `interp_eff`/`step` and its `init_pc` into
    the initial pc). -/
private def img : MemImage :=
  { loaded_segments := segs, init_pc := 0x1000, phdrs := ⟨0x1040, 56, 2⟩ }

/-- An empty machine state (no registers, no memory). -/
private def emptyMS : machine_state :=
  { ms_regs := bvmap_empty
    ms_fregs := bvmap_empty
    ms_pc_val := 0
    ms_svc_pending := none
    ms_resv := none
    ms_fcsr := 0
    ms_mem := fun _ => none
    ms_rom := fun _ => none }

/-- A read-only view onto a segment list, as `Run.init_machine_state`
    wires `ms_rom` from the image. -/
private def romOf (sg : List Segment) : word → Option byte :=
  fun a =>
    match memory_read sg a 1 with
    | some (b :: _) => some b
    | _ => none

/-- Did the step fault (the SIGSEGV/SIGILL/SIGTRAP side)?  Polymorphic
    so it applies to the machine-state and the core×memory results
    alike; `machine_state` has function fields, so `DecidableEq` on it
    does not exist and the classification is tested this way. -/
private def isFault {α : Type} : machine_result α → Bool
  | .MachineFault => true
  | _ => false

/-- Did the model decline (the fail-closed side)? -/
private def isUnmodeled {α : Type} : machine_result α → Bool
  | .MachineUnmodeled => true
  | _ => false

/-- x0 is hardwired: reads 0, writes discarded. -/
example : ms_reg (set_reg emptyMS 0 42) 0 = 0 := by decide

example : ms_reg (set_reg emptyMS 1 42) 1 = 42 := by decide

/-- Syscall argument i lives in x(10+i); `ms_sp` is x2. -/
example : ms_gpr (set_reg emptyMS 12 9) 2 = 9 := by decide

example : ms_sp (set_reg emptyMS 2 0x8000) = 0x8000 := by decide

/-- The byte at the entry point. -/
example : memory_read segs (0x1000 : word) 1 = some [0x93] := by decide

/-- The whole `addi` encoding, little-endian. -/
example : memory_read segs (0x1000 : word) 4
    = some [0x93, 0x00, 0x50, 0x00] := by decide

/-- NX: `.rodata`-style bytes are not fetchable. -/
example : code_read segs (0x2000 : word) 4 = none := by decide

/-- The 32-bit fast path assembles the word. -/
example : fetch_word segs (0x1000 : word) = some 0x00500093 := by decide

/-- ...and through the image interface: the entry point fetches its first
    instruction. -/
example : fetch_word img.loaded_segments (BitVec.ofNat 64 img.init_pc)
    = some 0x00500093 := by decide

/-- The `ecall` word at 0x1004. -/
example : fetch_word segs (0x1004 : word) = some 0x00000073 := by decide

/-- Misaligned pc (odd address): no fetch. -/
example : fetch_word segs (0x1001 : word) = none := by decide

/-- A compressed instruction in a two-byte segment: the four-byte read
    fails, the length-correct fetch succeeds. -/
example : fetch_word segs (0x3000 : word) = none := by decide

example : fetch_tail segs (0x3000 : word) = some 0x00004095 := by decide

/-- ...and it decodes and executes as `c.li x1, 5` (2 bytes). -/
example : (match step segs { emptyMS with ms_pc_val := 0x3000 } with
           | .MachineOk st' => (ms_reg st' 1, ms_pc st')
           | _ => ((0 : word), (0 : word))) = ((5 : word), (0x3002 : word)) := by
  decide

/-- A load through the READ view: the little-endian word at 0x2000. -/
example : ms_read_u64 { emptyMS with ms_rom := romOf segs } (0x2000 : word)
    = some 0x00000000deadbeef := by decide

/-- The writable view reads a writable segment... -/
example : wview segs (fun _ => none) (0x2001 : word) = some 0xbe := by decide

/-- ...but not a read-only one. -/
example : wview segs (fun _ => none) (0x1000 : word) = none := by decide

/-- The overlay shadows the segment image. -/
example : wview segs (fun a => if a == (0x2001 : word) then some 0x41 else none)
    (0x2001 : word) = some 0x41 := by decide

/-- The store bound: eight writable bytes are fine, nine run off the end. -/
example : store_ok segs (fun _ => none) (0x2000 : word) 8 = true := by decide

example : store_ok segs (fun _ => none) (0x2000 : word) 9 = false := by decide

example : store_ok segs (fun _ => none) (0x1000 : word) 1 = false := by decide

/-- ECALL detection (`0x73`), and the compressed marker keeping a
    compressed `c.li` clear of it. -/
example : is_ecall 0x00000073 = true := by decide

example : is_ecall 0x00500093 = false := by decide

example : is_ecall 0x00004095 = false := by decide

/-- The fetch-failure classification: unmapped is a hardware trap, a
    non-executable page is an NX trap, and a fetchable-but-unreadable
    byte is the model's own limit. -/
example : fetch_byte_traps segs (0x9000 : word) = true := by decide

example : fetch_byte_traps segs (0x5000 : word) = true := by decide

example : fetch_byte_traps segs (0x1000 : word) = false := by decide

/-- A step over `addi x1, x0, 5`: x1 = 5, pc advances by 4. -/
example : (match step segs { emptyMS with ms_pc_val := 0x1000 } with
           | .MachineOk st' => (ms_reg st' 1, ms_pc st')
           | _ => ((0 : word), (0 : word))) = ((5 : word), (0x1004 : word)) := by
  decide

/-- The next step is ECALL: the syscall number (a7 = x17 = 0 here) is
    parked in `ms_svc_pending`, and the machine step itself does NOT
    advance the pc (the trace semantics does, when it dispatches the
    syscall; see the [decode_exec_accesses] step 1). -/
example : (match step segs { emptyMS with ms_pc_val := 0x1004 } with
           | .MachineOk st' => (st'.ms_svc_pending, ms_pc st')
           | _ => (none, (0 : word))) = (some 0, (0x1004 : word)) := by
  decide

/-- A jump into unmapped memory is a fault, not a silent stop. -/
example : isFault (step segs { emptyMS with ms_pc_val := 0x9000 }) = true := by
  decide

/-- ...and so is a misaligned pc. -/
example : isFault (step segs { emptyMS with ms_pc_val := 0x1001 }) = true := by
  decide

/-- `ebreak` is a fault (SIGTRAP), reached through the interpreter. -/
example : isFault (interp_eff segs (.eEbreak
    { c_regs := bvmap_empty, c_fregs := bvmap_empty, c_pc := 0
      c_fcsr := 0, c_resv := none }) (fun _ => none)) = true := by
  decide

/-- A hand-built effect tree: load the byte at 0x2000 into the pc slot,
    and check the reported access range. -/
example : (match interp_eff_accesses segs
             (.eLoad 8 (0x2000 : word) (fun v => .eDone
               { c_regs := bvmap_empty, c_fregs := bvmap_empty
                 c_pc := zext 64 v, c_fcsr := 0, c_resv := none }))
             (fun _ => none) with
           | .MachineOk report =>
             (report.access_value.1.c_pc, report.accessed_ranges)
           | _ => ((0 : word), [])) = ((0xef : word), [((0x2000 : word), 1)]) := by
  decide

/-- A store through the interpreter lands in the overlay and is observed
    by the writable view (and by a later load). -/
example : (match interp_eff_accesses segs
             (.eStore 8 (0x2001 : word) (0x41 : byte) (.eDone
               { c_regs := bvmap_empty, c_fregs := bvmap_empty, c_pc := 0
                 c_fcsr := 0, c_resv := none }))
             (fun _ => none) with
           | .MachineOk report => wview segs report.access_value.2 (0x2001 : word)
           | _ => none) = some 0x41 := by
  decide

/-- An ISA-level `EIllegal` boundary node is the MODEL declining, not the
    process crashing (see the `interp_eff_accesses` classification). -/
example : isUnmodeled (interp_eff segs
    (.eIllegal { c_regs := bvmap_empty, c_fregs := bvmap_empty, c_pc := 0
                 c_fcsr := 0, c_resv := none }) (fun _ => none)) = true := by
  decide

/-- A store into a read-only segment is illegal (the SIGSEGV analogue),
    before any byte is written. -/
example : isFault (interp_eff segs
    (.eStore 8 (0x1000 : word) (0x00 : byte) (.eDone
      { c_regs := bvmap_empty, c_fregs := bvmap_empty, c_pc := 0
        c_fcsr := 0, c_resv := none }))
    (fun _ => none)) = true := by
  decide

/-- An undecodable-but-defined-illegal word (the all-zero parcel) is a
    hardware SIGILL. -/
example : isFault (decode_exec segs emptyMS 0x00000000) = true := by decide

/-- A word this decoder does not model is fail-closed `MachineUnmodeled`. -/
example : isUnmodeled (decode_exec segs emptyMS 0xffffffff) = true := by decide

/-- ECALL is intercepted before decode: a7 is parked, nothing retires. -/
example : (match decode_exec segs emptyMS 0x00000073 with
           | .MachineOk st => st.ms_svc_pending
           | _ => none) = some 0 := by decide

/-- `width_bytes` on the four widths the ISA issues, and `range_avoids_ro_segs`
    on the image. -/
example : (width_bytes 8, width_bytes 16, width_bytes 32, width_bytes 64)
    = (1, 2, 4, 8) := by decide

example : range_avoids_ro_segs segs 0x2000 8 = true := by decide

example : range_avoids_ro_segs segs 0x1000 1 = false := by decide

example : width_bytesZ 32 = 4 := by decide

/-- The w+x path: `fetch_word`'s `x /\ ~w` gate declines a writable
    executable segment, `fetch_word_ov`'s `x /\ w` gate accepts it, and
    the static projection `fetch_word_wx` agrees when the overlay
    misses. -/
example : fetch_word segs (0x4000 : word) = none := by decide

example : fetch_word_ov segs (fun _ => none) (0x4000 : word)
    = some 0x00500093 := by decide

example : fetch_word_wx segs (0x4000 : word) = some 0x00500093 := by decide

/-- ...and a step there executes the segment's bytes. -/
example : (match step segs { emptyMS with ms_pc_val := 0x4000 } with
           | .MachineOk st' => (ms_reg st' 1, ms_pc st')
           | _ => ((0 : word), (0 : word))) = ((5 : word), (0x4004 : word)) := by
  decide

/-- SELF-MODIFYING CODE is modeled: a store into the w+x segment is
    observed by the next fetch at that address (overlay first). -/
example : fetch_word_ov segs
    (fun a => if a == (0x4000 : word) then some 0x13 else none)
    (0x4000 : word) = some 0x00500013 := by decide

/-- Hex decoding: lowercase digits only, `N` offsets into a chunk list. -/
example : hex_nybble 'f' = 15 := by decide

example : hex_nybble '0' = 0 := by decide

example : hex_nybble 'A' = 16 := by decide

example : hex_byte_at "93" 0 = some 0x93 := by decide

example : hex_byte_at "93" 1 = none := by decide

example : hex_read_bytes "deadbeef" 0 2 = some [0xde, 0xad] := by decide

/-- Chunk boundaries carry no memory-semantic meaning. -/
example : segment_byte_at ["93", "0050"] 2 = some 0x50 := by decide

example : segment_read_bytes ["93", "0050"] 0 3
    = some [0x93, 0x00, 0x50] := by decide

/-- ...but a read past the chunk list fails rather than wrapping. -/
example : segment_read_bytes ["93", "0050"] 0 4 = none := by decide

example : word_to_le_bytes 4 0xdeadbeef = [0xef, 0xbe, 0xad, 0xde] := by decide

/-- The syscall post-state helper: a0 = ret, and the buffer bytes land in
    the writable overlay at the caller's address. -/
example : ms_reg (set_gpr0_write_buf emptyMS 7 (0x2001 : word) [0x41, 0x42]) 10
    = 7 := by decide

example : ms_writable_byte segs
    (set_gpr0_write_buf emptyMS 7 (0x2001 : word) [0x41, 0x42])
    (0x2002 : word) = some 0x42 := by decide

end Sanity

end LinuxSem.LinuxProcessSem.RiscvSemantics
