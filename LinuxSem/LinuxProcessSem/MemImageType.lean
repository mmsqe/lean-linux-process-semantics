/-
  * MemImageType — shared types for memory image snapshots

  TRUST BOUNDARY: this file is part of the trusted specification.

  Defines the `Segment` record used by all generated MemImage files and by
  `RiscvSemantics.lean` for memory reads.  Factored out so that multiple
  MemImage instantiations (source binary + target binary) can share the
  same type without circular dependencies.
-/
import LinuxSem.LinuxProcessSem.BvBase

namespace LinuxSem.LinuxProcessSem.MemImageType

/-- One LOAD segment of a compiled binary, as snapshotted from the ELF file.

    `seg_base`/`seg_size` are the segment's run-time extent;
    `seg_perms` is the ELF program-header flag rendering (`"rwx"`, with `'-'`
    for an unset bit); `seg_bytes` holds the segment's bytes as lowercase
    hex chunks without spaces. -/
structure Segment where
  /-- Run-time base address of the segment. -/
  seg_base  : Nat
  /-- Size of the segment in bytes. -/
  seg_size  : Nat
  /-- ELF permission rendering, e.g. `"r-x"` or `"rw-"`. -/
  seg_perms : String
  /-- The segment contents: hex chunks, lowercase, no spaces. -/
  seg_bytes : List String
  deriving DecidableEq, Repr

/-! ** `PhdrInfo` — where the binary's PROGRAM HEADER TABLE lands in memory

    The kernel does not only map the LOAD segments at `execve`: it also
    tells the new process where its own program header table is, through
    the auxiliary vector (`StackLayout.auxv_entries`) —

    - AT_PHDR  (`ph_addr`): the RUN-TIME address of the phdr table.  The
      kernel reports the address the table got by virtue of lying inside
      a mapped LOAD segment: for the segment whose file extent covers
      `e_phoff`, `p_vaddr + (e_phoff - p_offset)` (fs/binfmt_elf.c, the
      `phdr_addr` computation in `load_elf_binary`).  Static
      non-PIE riscv64 binaries put the table in the first LOAD segment,
      which starts at file offset 0, so this is just `e_phoff` above the
      image base.
    - AT_PHENT (`ph_ent`): `e_phentsize`, 56 for every ELF64 file.
    - AT_PHNUM (`ph_num`): `e_phnum`.

    WHY THE MODEL NEEDS IT.  A statically linked libc reads its own
    program headers to find the segments the kernel does not describe
    any other way — above all PT_TLS, the initialization image for
    THREAD-LOCAL STORAGE.  musl's `__init_tls` walks
    `AT_PHDR..AT_PHDR + AT_PHNUM * AT_PHENT` looking for it, sizes the
    thread block from its `p_memsz`/`p_align`, copies `p_filesz` bytes
    of initialized TLS data out of it, and only then sets the thread
    pointer `tp`.  With no AT_PHDR (or AT_PHNUM = 0) that walk finds
    nothing, and every `_Thread_local` access in the program reads and
    writes a block that was never laid out for it.  The phdr table is
    therefore process-startup data exactly like `init_pc`, and belongs
    to the image for the same reason.

    Note this is DERIVED data: the bytes of the table are already in the
    image (they lie inside the first LOAD segment, which the loader
    snapshots from file offset 0).  `PhdrInfo` only records where they
    ended up, which the model cannot recompute without an ELF parser.
    `elf-snapshot` emits it, and checks the recorded range
    really is covered by a snapshotted readable segment; because that
    check is Python, and outside the trust boundary, the same
  containment is re-checked inside  for both images of every
    example by `Equivalence.image_phdrs_readable` in `Checker.v`.
    Nothing else in the model relates `phdrs` to `loaded_segments`:
    `Run.init_machine_state` publishes `ph_addr` whatever it says. -/

/-- The location of the binary's program header table, as the kernel
    publishes it in the auxiliary vector. -/
structure PhdrInfo where
  /-- AT_PHDR  — run-time address of the phdr table -/
  ph_addr : Nat
  /-- AT_PHENT — e_phentsize (56 on ELF64) -/
  ph_ent  : Nat
  /-- AT_PHNUM — e_phnum -/
  ph_num  : Nat
  deriving DecidableEq, Repr

/-- Does the permission string carry the flag character `c`?  `seg_perms`
    comes from the ELF program-header flags rendered as "rwx" (with '-'
    for an unset bit): 'r' at index 0, 'w' at index 1, 'x' at index 2.
    The three flag letters are distinct and appear nowhere else in the
    string, so scanning the whole string for `c` identifies the flag
    regardless of the exact rendering, staying robust to formatting.

  Lean's `String` is a wrapper around `List Char`, so the same scan is written as a
  helper on that list; this is a representation-only change. -/
def string_has (c : Char) (s : String) : Bool :=
  go s.toList
where
  /-- Scan a character list for `c`. -/
  go : List Char → Bool
    | [] => false
    | c' :: r => if c' == c then true else go r

/-! The three page permissions the model enforces, each derived from the
    ELF segment's `seg_perms`.  Together they make the loaded image obey
    the same protections a real kernel installs at `execve`. -/

/-- Reads (machine loads, and syscall SOURCE buffers) may only touch
    readable pages.  A PROT_NONE / write-only region is not readable —
    reading it is the SIGSEGV analogue. -/
def seg_readable (seg : Segment) : Bool := string_has 'r' (seg.seg_perms)

/-- Drives two trusted checks — machine stores into a non-writable segment
    are illegal (RiscvSemantics.lean), and syscall OUTPUT buffers must be
    writable-mapped (LinuxProcessSem). -/
def seg_writable (seg : Segment) : Bool := string_has 'w' (seg.seg_perms)

/-- Instruction fetch may only read executable pages (the NX / W^X
    guarantee).  Jumping into a non-executable segment (.rodata, .data)
    faults rather than executing its bytes as code. -/
def seg_executable (seg : Segment) : Bool := string_has 'x' (seg.seg_perms)

/-! ** `MemImage` — the data a single compiled binary contributes to the model.

    A memory image is exactly the ELF-derived data `Run.run` consumes: the
    loaded code/data segments, the initial program counter, and the
    program-header-table location the kernel publishes in the auxv
    (`PhdrInfo`).  Nothing
    else in the image comes from the binary — the initial register file is
    fixed by the process model (`Run.init_machine_state`): the stack pointer
    is quantified over the ASLR window (`Run.valid_sp`) and every other
    register, `a0` included, starts at 0 on Linux entry (argc/argv live on
    the stack, not in registers).  Both the source binary and the target
    binary are packaged as `MemImage` modules, and the `Equivalence` functor
    in `Equivalence.lean` is parameterized over two of them.

    Generated per-binary by `elf-snapshot --module-name`. -/

/-- The image interface: the three data a generated snapshot module
    provides.

  Lean has no module types, so the interface is represented as a structure with
  exactly those three fields; a generated snapshot module corresponds to a definition
  of this type. -/
structure MemImage where
  /-- The loaded code/data segments. -/
  loaded_segments : List Segment
  /-- The initial program counter. -/
  init_pc : Nat
  /-- Where the program header table lands in memory. -/
  phdrs : PhdrInfo
  deriving DecidableEq, Repr

/-- The same three data as a RECORD, so that `Run.run` and the theorem
    statements in `Equivalence.lean` take one image argument rather than
    three parallel ones.  A `MemImage` module is packaged into it by
    `Equivalence.SPEC`; the module type stays the interface the
    generated snapshot files implement. -/
structure Image where
  /-- The loaded code/data segments. -/
  img_segments : List Segment
  /-- The initial program counter. -/
  img_init_pc  : Nat
  /-- Where the program header table lands in memory. -/
  img_phdrs    : PhdrInfo
  deriving DecidableEq, Repr

/-! ## Sanity checks

    -/

section Sanity

/-- `"r-x"` — the renderings the helpers are specified over. -/
private def roSeg : Segment := ⟨0x1000, 0x200, "r-x", ["7f454c46"]⟩

/-- A writable, non-executable data segment. -/
private def rwSeg : Segment := ⟨0x2000, 0x100, "rw-", ["00000001"]⟩

/-- A PROT_NONE segment. -/
private def noneSeg : Segment := ⟨0x3000, 0x100, "---", []⟩

example : seg_readable roSeg = true := by decide

example : seg_writable roSeg = false := by decide

example : seg_executable roSeg = true := by decide

example : seg_readable rwSeg = true := by decide

example : seg_writable rwSeg = true := by decide

example : seg_executable rwSeg = false := by decide

example : seg_readable noneSeg = false := by decide

example : seg_writable noneSeg = false := by decide

example : seg_executable noneSeg = false := by decide

/-- Scanning finds a flag anywhere in the string (the robustness property
    the doc comment claims), not just at a fixed index. -/
example : string_has 'x' "rwx" = true := by decide

example : string_has 'w' "rwx" = true := by decide

example : string_has 'r' "rwx" = true := by decide

example : string_has 'x' "rw-" = false := by decide

example : string_has 'r' "" = false := by decide

example : string_has 'z' "rwx" = false := by decide

/-- The permission flags are independent: flipping one bit of the
    rendering changes exactly the corresponding predicate. -/
example : seg_readable ⟨0, 1, "rwx", []⟩ && seg_writable ⟨0, 1, "rwx", []⟩
    && seg_executable ⟨0, 1, "rwx", []⟩ = true := by decide

/-- A small image: two segments, entry point 0x1000, phdr table in the
    first segment. -/
private def smallImage : Image :=
  { img_segments := [roSeg, rwSeg]
    img_init_pc  := 0x1000
    img_phdrs    := ⟨0x1000 + 0x40, 56, 2⟩ }

/-- The phdr table the image records really is covered by the snapshotted
    segment it claims to lie in — the containment check the `PhdrInfo`
    comment above says `elf-snapshot` and `Equivalence.image_phdrs_readable`
    enforce. -/
example : smallImage.img_phdrs.ph_addr
      + smallImage.img_phdrs.ph_num * smallImage.img_phdrs.ph_ent
    ≤ roSeg.seg_base + roSeg.seg_size := by decide

/-- Looking a segment up by base address on the small image (ordinary
    `List` lookup over the derived `DecidableEq`). -/
example : (smallImage.img_segments.find? (fun s => s.seg_base == 0x2000))
    = some rwSeg := by decide

example : (smallImage.img_segments.find? (fun s => s.seg_base == 0x9000))
    = none := by decide

/-- Every segment of the image is readable — what a loader hands to
    `RiscvSemantics` for a load. -/
example : smallImage.img_segments.all seg_readable = true := by decide

/-- `DecidableEq` on `Segment` compares the hex chunks too, not just the
    address range. -/
example : (⟨0x1000, 0x200, "r-x", ["7f454c46"]⟩ : Segment) = roSeg := by decide

example : (⟨0x1000, 0x200, "r-x", ["7f454c47"]⟩ : Segment) ≠ roSeg := by decide

/-- `PhdrInfo` carries the ELF64 `e_phentsize` we expect. -/
example : smallImage.img_phdrs.ph_ent = 56 := by decide

end Sanity

end LinuxSem.LinuxProcessSem.MemImageType
