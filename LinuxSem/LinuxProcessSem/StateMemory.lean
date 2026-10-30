/-
  * LinuxProcessSem.StateMemory — reading user memory, part 2

  What lives here, in order:

  - the length bound on the longest readable prefix (`readable_bytes_length_le`);
  - `path_max` and the pathname reader (`cstr_access_len_aux`,
    `cstr_result`, `read_cstr_aux`, `read_cstr`) — the three outcomes
    Linux distinguishes (`-ENAMETOOLONG` vs `-EFAULT` vs the string);
  - the little-endian word reader (`read_u64`) and the iovec-array
    decoder (`read_iovecs_aux`, `read_iovecs`);
  - the transfer cap (`MAX_RW_COUNT`, `rw_count_clamp`, `IOV_MAX`);
  - `access_okb`, the riscv64 `access_ok` transcription, and
    `copy_bytes_map`, the `access_ok`-then-copy pair;
  - the iovec import path (`iov_import`, `iov_entry`,
    `read_iovec_entry`, `copy_iovecs_aux`, `copy_iovecs_accesses`,
    `iovs_access_okb`, `cap_iovecs_aux`, `cap_iovecs`, `import_iovecs`,
    `import_iovecs_accesses`);
  - the copy-in ledger and the scatter/gather consumers
    (`iov_prefix_accesses`, `scatter_iovecs`, `gather_iovecs`,
    `gather_prefix`, `iovs_total`, `writev_gathered`).

  This chunk is a LEAF: nothing else in `State.lean` uses it, and its only
  dependencies are already-landed modules — `State.lean` (chunk B1a: the
  `read_bytes_*`/`readable_bytes_*` readers; chunk B1b: `TASK_SIZE`) and
  `BvBase.lean` (`word_to_nat`, `word_to_nat_bounded`, `len_word`,
  `le_bytes_to_word`).

  TRUST BOUNDARY: this file is part of the trusted specification.

  - `Z.min` is `min` on `Int`, so the two proofs that used
    `Z_to_bv_unsigned; bv_wrap_small` go through
    `toNat_ofInt_eq_self` below (`BitVec.toNat_ofInt` +
    `Int.emod_eq_of_lt`), the same fact stated once.
  - `rw_count_clamp`/`MAX_RW_COUNT`/`IOV_MAX` stay in `Int` because
    they are compared against unsigned lengths without
    wrapping.
-/
import LinuxSem.LinuxProcessSem.State

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/-! ## Length bound on the readable prefix -/

/-- The readable prefix never exceeds the requested count. -/
theorem readable_bytes_length_le (mp : word → Option byte) (a len : word) :
    (readable_bytes mp a len).length ≤ word_to_nat len := by
  rw [readable_bytes_eq]
  exact readable_bytes_aux_length_le mp (word_to_nat len) a

/-! ## Reading a NUL-terminated pathname -/

/-- Linux PATH_MAX: a pathname's content may be at most 4095 bytes, i.e.
    4096 counting the NUL — `path_max` is the bound Linux's `getname()`
    enforces, and it counts the terminator, so a 4095-byte path plus its
    NUL fits and a 4096-byte one does not. -/
def path_max : Nat := 4096

/-- Pathname bytes counted as read: through the first NUL, the first
    unreadable byte, or `path_max`.  This is the count the model records,
    and it is SHORTER than what `getname()` issues —
    `strncpy_from_user` loads whole words, so it runs past the NUL to the
    end of that word (lib/strncpy_from_user.c, `do_strncpy_from_user`;
    byte-identical v6.10 through v6.16 — the FILE is not, so the window
    belongs to the function).  The answer is unaffected: that loop is
    clamped below TASK_SIZE and falls back to a byte loop when a word
    load faults, so no verdict moves.  Only the recorded read set is
    short. -/
def cstr_access_len_aux (mp : word → Option byte) (a : word) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      match mp a with
      | none => 1
      | some b =>
          if bv_eqb b (BitVec.ofInt 8 0) then 1
          else cstr_access_len_aux mp (a + 1) fuel + 1

/-- Reading a pathname out of user memory has three outcomes, and Linux
    distinguishes all three: the string, `-ENAMETOOLONG` (no NUL within
    PATH_MAX), and `-EFAULT` (an unmapped byte before the NUL).  Both
    failures are ordinary kernel returns, NOT modeling gaps — keeping
    them apart is what lets `Open.openat_spec` answer an errno instead
    of declining to interpret the call. -/
inductive cstr_result where
  /-- NUL-terminated within PATH_MAX -/
  | CstrOk (p : List byte)
  /-- no NUL within PATH_MAX → `-ENAMETOOLONG` -/
  | CstrTooLong
  /-- unmapped byte before the NUL → `-EFAULT` -/
  | CstrFault
  deriving DecidableEq, Repr

def read_cstr_aux (mp : word → Option byte) (a : word) : Nat → cstr_result
  | 0 => .CstrTooLong             -- no NUL within the length bound
  | k + 1 =>
      match mp a with
      | none => .CstrFault        -- unmapped byte before the NUL
      | some b =>
          if bv_eqb b (BitVec.ofInt 8 0) then .CstrOk []
          else match read_cstr_aux mp (a + 1) k with
               | .CstrOk r => .CstrOk (b :: r)
               | r => r          -- propagate the failure verbatim

def read_cstr (mp : word → Option byte) (a : word) : cstr_result :=
  read_cstr_aux mp a path_max

/-- Read one little-endian 64-bit word at `a` (`BvBase.le_bytes_to_word`
    decodes index 0 as least significant), or `none` if any of the 8
    bytes is unmapped — for reading 8-byte fields of in-memory kernel
    structures (the iovec array of readv/writev). -/
def read_u64 (mp : word → Option byte) (a : word) : Option word :=
  match read_bytes_map mp a (BitVec.ofInt 64 8) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

/-- Read `cnt` `struct iovec` entries starting at `a` — on LP64 each is
    16 bytes: `iov_base` then `iov_len`, both 8-byte little-endian words
    — or `none` if any byte of the array is unmapped.

    This is the layout decode ALONE: no length or address validation.
    Both specs import through `copy_iovecs_aux` below, which walks the
    same layout and additionally answers `ImpFault`/`ImpInval`, so
    nothing in the model calls this.  Its consumer is a caller of the
    extracted checker, which must decide which guest ranges to capture
    BEFORE it knows whether the import succeeds — a validating decoder
    would hand it nothing for exactly the traces the model then needs
    memory for.  It is an explicit extraction root for that reason
    (Checks/Extraction.v).  The entry point that turns a word count into
    `k` is `read_iovecs`, stated below `IOV_MAX` because it bounds the
    count by it. -/
def read_iovecs_aux (mp : word → Option byte) (a : word) :
    Nat → Option (List (word × word))
  | 0 => some []
  | k + 1 =>
      match read_u64 mp a, read_u64 mp (a + 8) with
      | some base, some len =>
          match read_iovecs_aux mp (a + 16) k with
          | some r => some ((base, len) :: r)
          | none => none
      | _, _ => none

/-! ## Transfer caps -/

/-- Linux caps the aggregate transfer described by an iovec array at
    `MAX_RW_COUNT = 0x7ffff000` (include/linux/fs.h, `MAX_RW_COUNT` =
    `INT_MAX & PAGE_MASK`, v6.18.46).  Keep the cap here, next to the
    structural helpers which consume it, so readv's trusted spec and
    executable checker cannot drift apart.

    `INT_MAX & PAGE_MASK` is a HOST property: Linux computes this from
    the page size the running kernel booted with, so the literal below is
    the 4 KiB-page value, and a 16 KiB or 64 KiB host clamps lower
    (0x7fffc000, 0x7fff0000) than this constant names.  4 KiB-page hosts
    are therefore the honest scope of the constant, and that is a scope
    of the model rather than a bug to fix here: making it configurable
    would put a host property into a model constant. -/
def MAX_RW_COUNT : Int := 0x7ffff000

/-- The SCALAR form of the same clamp: a plain read or write is capped at
    `MAX_RW_COUNT` before the transfer —
    `if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;` in `vfs_read`
    (fs/read_write.c:566-567) and `vfs_write` (:680-681), both at
    v6.18.46 — after `access_ok` and `rw_verify_area` and ahead of the
    `->read`/`->write` dispatch, so the caller of an over-clamp count
    sees a SHORT transfer, not an error.  Computed in `Int`; the result is
    at most `MAX_RW_COUNT`, far under 2^64, so a use site may re-enter
    `word` with `BitVec.ofInt` without wrapping.

    EVERY SCALAR TRANSFER ARM CONSUMES IT, on both directions: on the read
    side `Fs.ReadWrite.read_spec`'s channel, file, socket and pipe arms,
    and `pread64_spec`; on the write side every arm, where
    `Uaccess.write_source` is the clamped source prefix, including
    `pwrite64_spec`, which reads its source through `write_source` like
    the rest. -/
def rw_count_clamp (count : word) : Int :=
  min (count.toNat : Int) MAX_RW_COUNT

theorem rw_count_clamp_small (count : word)
    (h : (count.toNat : Int) ≤ MAX_RW_COUNT) :
    rw_count_clamp count = (count.toNat : Int) := by
  unfold rw_count_clamp
  exact Int.min_eq_left h

theorem rw_count_clamp_range (count : word) :
    0 ≤ rw_count_clamp count ∧ rw_count_clamp count ≤ MAX_RW_COUNT := by
  unfold rw_count_clamp
  refine ⟨?_, Int.min_le_right _ _⟩
  rw [Int.le_min]
  exact ⟨Int.natCast_nonneg _, by unfold MAX_RW_COUNT; decide⟩

/-- `BitVec.ofInt n z` round-trips through `toNat` for a non-negative `z`
    below the modulus.  This is here
    `Z_to_bv_unsigned` + `bv_wrap_small` pair, stated once. -/
theorem toNat_ofInt_eq_self {n : Nat} {z : Int}
    (h0 : 0 ≤ z) (h1 : z < ((2 ^ n : Nat) : Int)) :
    ((BitVec.ofInt n z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-- The clamped count re-entered as a `word`.  `MAX_RW_COUNT` is far under
    2^64, so the round trip is the identity and a spec may name the
    clamped transfer as a `word` without a wrapping side condition. -/
theorem rw_count_clamp_word (count : word) :
    ((BitVec.ofInt 64 (rw_count_clamp count)).toNat : Int) = rw_count_clamp count := by
  have h := rw_count_clamp_range count
  refine toNat_ofInt_eq_self h.1 ?_
  have hlt : MAX_RW_COUNT < ((2 ^ 64 : Nat) : Int) := by
    unfold MAX_RW_COUNT; decide
  omega

/-- Linux UIO_MAXIOV: the largest iovec count a single readv/writev may
    pass; anything larger fails with `-EINVAL` (lib/iov_iter.c
    `iovec_from_user`, testing `nr_segs > UIO_MAXIOV`; the constant is
    `UIO_MAXIOV = 1024` in include/uapi/linux/uio.h; both v6.18.46).
    Lives beside `MAX_RW_COUNT` because `import_iovecs` below tests
    both. -/
def IOV_MAX : Int := 1024

/-- Decode the iovec array a `readv`/`writev` of count `cnt` passes,
    stopping after `IOV_MAX` entries.

    The bound is there because `nat` extracts to a unary Peano numeral:
    the unbounded `word_to_nat cnt` materializes `cnt` successors before
    the first descriptor is read, so a large `cnt` overflows the extracted
    checker's stack even when the very first entry is unmapped.
    `word_to_nat_bounded` keeps the comparison in `Int` and never builds
    more than `IOV_MAX` of them.

    Stopping there loses nothing the kernel could produce, so this is
    faithful rather than an approximation.  A count above `IOV_MAX` is
    `-EINVAL` from `iovec_from_user` (lib/iov_iter.c, v6.18.46) BEFORE
    `copy_iovec_from_user` touches a descriptor, and the one path that
    skips that test — the `nr_segs == 1` short-circuit described at
    `import_iovecs` — imports a single entry.  No call the kernel admits
    imports more than `IOV_MAX` descriptors.  `read_iovecs_unguarded`
    proves the bound is invisible at and below it. -/
def read_iovecs (mp : word → Option byte) (a cnt : word) :
    Option (List (word × word)) :=
  read_iovecs_aux mp a (word_to_nat_bounded cnt IOV_MAX.toNat)

theorem read_iovecs_unguarded (mp : word → Option byte) (a cnt : word)
    (hle : (cnt.toNat : Int) ≤ IOV_MAX) :
    read_iovecs mp a cnt = read_iovecs_aux mp a (word_to_nat cnt) := by
  have hle' : word_to_nat cnt ≤ IOV_MAX.toNat := by
    have h1024 : IOV_MAX.toNat = 1024 := rfl
    unfold word_to_nat
    omega
  unfold read_iovecs
  rw [word_to_nat_bounded_eq_min, Nat.min_eq_left hle']

/-! ## The user/kernel protection boundary -/

/-- riscv64 `access_ok`, transcribed.  Linux's `__access_ok` is

        (size <= TASK_SIZE_MAX) && (addr <= TASK_SIZE_MAX - size)

    (include/asm-generic/access_ok.h, `__access_ok`, at v6.18.46 /
    1f99e9ab748f), and on riscv64 at that commit `TASK_SIZE_MAX` is the
    header's own `#ifndef TASK_SIZE_MAX` fallback to `TASK_SIZE` — see
    that constant above for the derivation and the Sv48 premise it
    rests on.  `access_okb` below is that comparison with `TASK_SIZE`
    substituted: two comparisons and no page-table walk, so an unmapped
    range ending at or below 2^47 passes and a mapped one ending past it
    fails.  Written as a SUBTRACTION, as the kernel writes it, so the
    sum `base + len` is never formed and a range that wraps 2^64 is
    refused rather than folded back inside.

    Every user-range verdict in the model goes through this one
    definition: `import_iovecs` applies it to the descriptor array and
    to each destination, and `Uaccess.access_ok_zero` and the scalar arms
    apply it to their buffers.  There is no second spelling of the limit
    to keep in step with it.

    WHAT `__access_ok` HAS THAT THIS DOES NOT, in two halves.  The first
    is the pointer-masking wrapper.  With `CONFIG_RISCV_ISA_SUPM`
    (arch/riscv/Kconfig: `bool`, `depends on 64BIT`, `default y`) riscv64
    defines its own `access_ok` as `__access_ok(untagged_addr(addr),
    size)` (arch/riscv/include/asm/uaccess.h, `access_ok`).  This
    predicate does not untag.  That costs nothing here, because the
    untagging is the IDENTITY for every process this model can describe.
    Every citation below is at v6.18.46 unless it names another tag.

    - `untagged_addr` masks `PMLEN` bits.  Under `CONFIG_MMU` — the
      configuration modeled here — `__untagged_addr_remote`
      (arch/riscv/include/asm/uaccess.h) is the ARITHMETIC, sign-extending
      shift `(long)(addr << pmlen) >> pmlen`; the logical
      `(addr << pmlen) >> pmlen` is the `!CONFIG_MMU` branch.  Both are the
      identity at `pmlen = 0`, and the function returns `addr` outright
      when SUPM is absent.
    - `PMLEN` is zero on every `execve`: `activate_mm`
      (arch/riscv/include/asm/mmu_context.h) assigns
      `next->context.pmlen = 0` unconditionally, and `flush_thread`
      (arch/riscv/kernel/process.c) resets the hardware `ENVCFG_PMM` to
      `ENVCFG_PMM_PMLEN_0` alongside it.  THIS is the premise the
      argument rests on.
    - A nonzero `pmlen` is set only by `set_tagged_addr_ctrl`
      (arch/riscv/kernel/process.c, the `mm->context.pmlen = pmlen`
      store), which has TWO callers, not one:
      `prctl(PR_SET_TAGGED_ADDR_CTRL, ...)` (kernel/sys.c, the
      `PR_SET_TAGGED_ADDR_CTRL` arm of `SYSCALL_DEFINE5(prctl)`), and
      PTRACE_SETREGSET with `NT_RISCV_TAGGED_ADDR_CTRL`
      (arch/riscv/kernel/ptrace.c, `tagged_addr_ctrl_set`; both arrived
      in v6.13 in one series, commits 2e1743085887 and 78844482a1c9, so
      there was never a release in which prctl was the only route).
      A TRACER can therefore enable masking for a tracee that never calls
      prctl.  Documentation/arch/riscv/uabi.rst: "Pointer masking is
      disabled by default.  To enable it, userspace must call
      PR_SET_TAGGED_ADDR_CTRL".  No Kconfig default sets it and the
      `abi.tagged_addr_disabled` sysctl only ever FORBIDS enabling.
    - `pmlen` lives in `mm->context`, NOT in `thread_struct`, so it IS
      inherited across fork and clone (`dup_mm`'s `memcpy` of the whole
      `mm_struct` in kernel/fork.c, and `CLONE_VM` sharing the `mm`
      outright in `copy_mm`); riscv's `init_new_context` resets
      `context.id` and the `MM_CONTEXT_LOCK_PMLEN` bit but never `pmlen`.
      Inheritance does not weaken anything here, because the `execve`
      reset above runs on the binary this model starts from.

    Neither route is reachable in this model, but the two are ruled out at different
    granularities. `ptrace` is syscall 117 on riscv64
    (include/uapi/asm-generic/unistd.h; riscv64 uses the generic table) and is
    outside `Specs.modeled_sysnos` — as is `execve` — so it falls through the
    dispatcher to `Monad.unmodeled`, fail closed, before any tagged pointer can reach
    this predicate. `prctl` is 167 and IS in `Specs.modeled_sysnos`: it answers
    `PR_CAPBSET_READ` and nothing else, so what is declined is the OPTION rather than
    the number, and `PR_SET_TAGGED_ADDR_CTRL` (55) is declined inside
    `Kernel.Sys.prctl_spec` instead of at the dispatcher.
    **`Checks/ProcessCreation.lean` HAS LANDED** (51 of 71 declarations proved), so
    the tripwires exist here: the exclusions above are discharged by
    `Checks.ProcessCreation.prctl_option_unmodeled`,
    `prctl_tagged_addr_ctrl_unmodeled` and `ptrace_unmodeled`, and
    `prctl_modeled_options_are` pins the closed option list itself. The twenty
    declarations that file still defers are the clone-resolution and `wait4`/`setsid`
    group — NOT these — so nothing in this paragraph is a hypothesis any more. No
    lemma tying it to `prctl_spec`): an edit teaching `prctl` a second option does
    not fail any pin here. `clone` (220) and `clone3` (435) ARE in
    `Specs.modeled_sysnos`, but only for a flag word that shares no address space, so
    on that assumption no process this model admits an outcome for can write
    another's `mm->context`. (riscv64 has no `fork` syscall of its own: `fork` IS
    `clone(SIGCHLD)`, which this model answers.)

    THE TRACER IS AN ASSUMPTION, not a consequence: no process outside
    this one attaches to it.  That is a closed-world assumption about
    the ENVIRONMENT, which no artifact in this repository checks.  It does
    not follow from the limits on 220, since a tracer is an independently
    started process; modeling `clone` parent-side does not weaken it,
    but it does add a second population to it, because a child this
    model never steps could attach to its own parent.  Under that
    assumption, every execution the model admits an outcome for has
    `pmlen = 0`.

    That settles the tagging half.  The other half is a BUILD
    CONFIGURATION: `__access_ok` returns true for every range, before it
    reaches the comparison this predicate transcribes, under
    `CONFIG_ALTERNATE_USER_ADDRESS_SPACE` or with `CONFIG_MMU` off.  On
    such a build `access_okb` still declines ranges the kernel accepts,
    which is exactly an under-approximation.

    The two are NOT alike, and only one of them is a choice.  riscv
    cannot select `CONFIG_ALTERNATE_USER_ADDRESS_SPACE`: it is defined in
    arch/Kconfig with no prompt and is selected only by parisc, s390,
    `SPARC64` and m68k's `CPU_HAS_ADDRESS_SPACES` (arch/Kconfig at
    v6.18.46), none of them this architecture.  `CONFIG_MMU` IS a choice, and
    riscv64 can be built without it — arch/riscv/Kconfig's `config MMU`
    is a prompted bool defaulting to y with no `depends on`, and
    arch/riscv/configs/nommu_virt_defconfig is a shipped RV64 build that
    turns it off.  So this model is scoped to the MMU half by decision,
    not by impossibility, and a nommu riscv64 kernel is a real
    configuration in which `access_okb` is an under-approximation.

    The claim is scoped rather than hedged on purpose: build for nommu
    and this is the sentence that breaks.

    This is a fail-closed gap in the ordinary way, not a known
    limitation. -/
def access_okb (base : word) (len : Int) : Bool :=
  decide (len ≤ TASK_SIZE) && decide ((base.toNat : Int) ≤ TASK_SIZE - len)

/-- `copy_to_user`/`copy_from_user` IS `access_ok` AND THEN THE COPY
    (include/linux/uaccess.h's `_inline_copy_to_user` and
    `_inline_copy_from_user` at v6.18.46 each test `access_ok` over the
    whole range and only then call the raw copy), and this pairs the two
    halves.
    `read_bytes_map` is the copy alone: it advances with WRAPPING `bv`
    addition, so a range whose base sits in the last bytes of the address
    space walks off the top and back in at 0, and where `mp` backs both
    halves it answers `some` — a range fully "readable" that Linux
    refuses outright.  `access_okb` sums in `Int` and so refuses it.

    A spec modeling a `copy_to_user` or a `copy_from_user` should reach
    for this and not for the bare walk.  `Net.Socket.socketpair_dest_writable`,
    `Kernel.Signal.write_oset`, `EventPoll.copy_from_user_ok` and
    `Fs.Pipe.pipe2_spec` each spell the same pair by hand,
    `access_okb` and then `read_bytes_map`; moving them onto this
    definition is the follow-up, so that the range question has one
    spelling.  A spec that reaches for the bare walk alone is claiming
    the range question is asked somewhere else, and owes the argument
    in place.

    THE LENGTH IS AN `Int` BECAUSE `access_okb`'s IS.

    A structural repair — an `IMAGE_WF` conjunct
    bounding every loaded segment — would remove the wrapping
    walks at the source.  The range test stays either way: it is what
    turns a refused range into -EFAULT rather than into an unmapped
    walk's `none`. -/
def copy_bytes_map (mp : word → Option byte) (a : word) (len : Int) :
    Option (List byte) :=
  if access_okb a len then read_bytes_map mp a (BitVec.ofInt 64 len) else none

/-- The half the walk alone cannot see: a range `access_okb` refuses is
    `none` here however the memory map answers.  This is the property
    every caller's decline rests on, so it is stated once rather than
    re-derived per arm. -/
theorem copy_bytes_map_refused (mp : word → Option byte) (a : word) (len : Int)
    (h : access_okb a len = false) : copy_bytes_map mp a len = none := by
  simp [copy_bytes_map, h]

/-- ...and the other direction, which is what keeps the guard from being
    a blanket refusal: on a range `access_okb` accepts, this is exactly
    the walk it always was. -/
theorem copy_bytes_map_accepted (mp : word → Option byte) (a : word) (len : Int)
    (h : access_okb a len = true) :
    copy_bytes_map mp a len = read_bytes_map mp a (BitVec.ofInt 64 len) := by
  simp [copy_bytes_map, h]

/-! ## Importing an iovec array -/

/-- The three outcomes of importing an iovec array (lib/iov_iter.c
    `__import_iovec`, v6.18.46): the imported entries, a `-EFAULT` from an
    unreadable descriptor or a failed `access_ok`, or a `-EINVAL` from a
    count over `IOV_MAX` or a length that is negative as `ssize_t`. -/
inductive iov_import where
  | ImpOk (iovs : List (word × word))
  | ImpFault
  | ImpInval
  deriving DecidableEq, Repr

/-- One `struct iovec` (LP64: 8-byte little-endian `iov_base` then
    `iov_len`) as `copy_iovec_from_user` fetches it: BOTH fields are
    loaded — `iov_len`, then `iov_base`, each an `unsafe_get_user` with
    its own fixup — and only then is the sign of `iov_len` tested.  So a
    field that cannot be read is `-EFAULT` whatever the length says, and
    a length that is negative as `ssize_t` is `-EINVAL` only once both
    fields have been read. -/
inductive iov_entry where
  | IovEntry (base len : word)
  | IovFault
  | IovInval
  deriving DecidableEq, Repr

def read_iovec_entry (mp : word → Option byte) (a : word) : iov_entry :=
  match read_u64 mp a, read_u64 mp (a + 8) with
  | some base, some len =>
      if (2 ^ 63 : Int) ≤ (len.toNat : Int) then .IovInval else .IovEntry base len
  | _, _ => .IovFault

/-- `copy_iovec_from_user` (lib/iov_iter.c, v6.18.46): ONE interleaved
    pass in index order — per entry both fields, then
    `if (len < 0) return -EINVAL` — so the FIRST error in INDEX ORDER
    decides the call.

    The interleaving is v6.4 and later.  Up to v6.3 the function did a
    bulk `copy_from_user` of the whole array followed by a separate
    length loop, so `-EFAULT` beat `-EINVAL` regardless of index; commit
    487c20b016dc ("iov: improve copy_iovec_from_user() code generation",
    Linus Torvalds, first in v6.4-rc1) changed it, with the errno
    precedence an unremarked side effect of what was sold as a codegen
    change. -/
def copy_iovecs_aux (mp : word → Option byte) (a : word) :
    Nat → iov_import
  | 0 => .ImpOk []
  | k + 1 =>
      match read_iovec_entry mp a with
      | .IovFault => .ImpFault
      | .IovInval => .ImpInval
      | .IovEntry base len =>
          match copy_iovecs_aux mp (a + 16) k with
          | .ImpOk r => .ImpOk ((base, len) :: r)
          | r => r

/-- The bytes of the descriptor at `a` that `copy_iovec_from_user` has
    read when it moves on or returns (lib/iov_iter.c:1272-1273,
    v6.18.46).  It loads `iov_len`, at `a + 8`, before `iov_base`, at
    `a`, and a fault on either load jumps to `uaccess_end` at once:
    - `iov_len` unreadable: nothing;
    - `iov_len` read, `iov_base` unreadable: the 8 bytes at `a + 8`;
    - both read: the whole 16 bytes, whatever the sign test of
      `iov_len` then answers.
    A field that straddles a page boundary and faults records nothing,
    the convention that `Kernel.Signal.rt_sigprocmask_spec`'s note names
    and costs. -/
def iovec_entry_accesses (mp : word → Option byte) (a : word) :
    List (word × Nat) :=
  match read_u64 mp (a + 8) with
  | none => []
  | some _ => if (read_u64 mp a).isSome then [(a, 16)] else [(a + 8, 8)]

/-- The copy-in ledger of `copy_iovecs_aux`: `iovec_entry_accesses` of
    each descriptor it reaches.  The walk stops on the same first
    unreadable field or negative length, so an errno path records only
    what the kernel read before it answered. -/
def copy_iovecs_accesses (mp : word → Option byte) (a : word) :
    Nat → List (word × Nat)
  | 0 => []
  | k + 1 =>
      iovec_entry_accesses mp a ++
      match read_iovec_entry mp a with
      | .IovEntry _ _ => copy_iovecs_accesses mp (a + 16) k
      | _ => []

/-- `__import_iovec`'s per-segment `access_ok(iov_base, len)` on the
    UNCAPPED length (lib/iov_iter.c, v6.18.46), applied to a zero-length
    entry as well as to any other. -/
def iovs_access_okb (iovs : List (word × word)) : Bool :=
  iovs.all fun bl => access_okb bl.1 (bl.2.toNat : Int)

/-- Truncate an iovec sequence at `MAX_RW_COUNT`, exactly as
    `__import_iovec`'s loop does with `len > MAX_RW_COUNT - total_len`
    (lib/iov_iter.c, v6.18.46).  Entries after the cap remain present with
    length zero: the kernel imports and address-checks the whole array
    before I/O, even though no bytes from those entries can be
    transferred. -/
def cap_iovecs_aux : List (word × word) → Int → List (word × word)
  | [], _ => []
  | (base, len) :: rest, left =>
      let n := min left (len.toNat : Int)
      (base, BitVec.ofInt 64 n) :: cap_iovecs_aux rest (left - n)

def cap_iovecs (iovs : List (word × word)) : List (word × word) :=
  cap_iovecs_aux iovs MAX_RW_COUNT

/-- The iovec import path (lib/iov_iter.c, v6.18.46): `import_iovec` is a
    one-line wrapper that passes `in_compat_syscall()` to
    `__import_iovec`, which does the work, for readv and writev alike.
    The entries come back UNCAPPED — the kernel clamps inside
    `__import_iovec`'s loop, the model afterwards, in the consumers
    (`ReadWrite.readv_imported`, `ReadWrite.writev_spec`'s gather),
    after the per-entry `access_ok` the loop applies to the uncapped
    length has been decided.
    (`Net.Socket.sendmsg_spec` imports with `copy_iovecs_aux` and
    so lacks the per-segment `access_ok` this function adds.)

    - A count of exactly ONE takes a DIFFERENT function with the OPPOSITE
      cap/`access_ok` order: `__import_iovec_ubuf` copies the single
      descriptor (`copy_iovec_from_user` with `nr_segs = 1`, so the same
      `read_iovec_entry` order) and hands it to `import_ubuf`, which caps
      to `MAX_RW_COUNT` FIRST and only then applies `access_ok` to the
      CAPPED length.  The `nr_segs == 1` short-circuit is the first
      statement of `__import_iovec`, ahead of its call to
      `iovec_from_user`, hence ahead of that function's `UIO_MAXIOV` test
      and of its heap allocation.  So `readv(fd, iov, 1)` never reports
      `-EINVAL` for a count over `IOV_MAX` — 1 is not over it — and,
      because the count reaches `__import_iovec` through an `unsigned`
      parameter, a raw count of `2^32 + 1` truncates to 1 and takes this
      path too.

    - For every other count the array is copied first
      (`copy_iovecs_aux`, index-ordered `-EFAULT`/`-EINVAL`) and only
      then walked a SECOND time for `access_ok` on the UNCAPPED length —
      `__import_iovec`'s per-segment loop tests `access_ok` before it
      applies that same loop's `MAX_RW_COUNT` clamp.  The two passes are
      why an `-EINVAL` at ANY index beats an `access_ok` `-EFAULT` at
      any index, while an unreadable descriptor and a negative length
      race in index order.

    `copy_iovec_from_user` opens with `user_access_begin` over
    `nr_segs` descriptors, an `access_ok` on the descriptor array
    itself; that is the `access_okb a ...` test on each branch. -/
def import_iovecs (mp : word → Option byte) (a n : word) : iov_import :=
  if bv_eqb n 1 then
    if !access_okb a 16 then .ImpFault
    else match read_iovec_entry mp a with
         | .IovFault => .ImpFault
         | .IovInval => .ImpInval
         | .IovEntry base len =>
             if !access_okb base (min (len.toNat : Int) MAX_RW_COUNT)
             then .ImpFault
             else .ImpOk [(base, len)]
  else if bv_eqb n 0 then .ImpOk []
  else if IOV_MAX < (n.toNat : Int) then .ImpInval
  else if !access_okb a (16 * (n.toNat : Int)) then .ImpFault
  else match copy_iovecs_aux mp a (word_to_nat n) with
       | .ImpOk iovs =>
           if iovs_access_okb iovs then .ImpOk iovs else .ImpFault
       | r => r

def import_iovecs_accesses (mp : word → Option byte) (a n : word) :
    List (word × Nat) :=
  if bv_eqb n 1 then
    if !access_okb a 16 then [] else iovec_entry_accesses mp a
  else if bv_eqb n 0 then []
  else if IOV_MAX < (n.toNat : Int) then []
  else if !access_okb a (16 * (n.toNat : Int)) then []
  else copy_iovecs_accesses mp a (word_to_nat n)

/-- The copy-in ledger for the prefix of an iovec sequence a transfer of
    `left` bytes actually touched.  `word_to_nat_bounded` rather than
    `Nat.min (word_to_nat len) left` for the reason given at its
    definition: a capped `iov_len` reaches `MAX_RW_COUNT`, and the
    `Nat.min` spelling materializes that as a unary numeral before it
    compares, on a call that may have delivered one byte. -/
def iov_prefix_accesses : List (word × word) → Nat → List (word × Nat)
  | _, 0 => []
  | [], _ => []
  | (base, len) :: rest, left =>
      let n := word_to_nat_bounded len left
      if n == 0 then iov_prefix_accesses rest left
      else (base, n) :: iov_prefix_accesses rest (left - n)

/-- Scatter `bs` across destination iovecs in order.  Every nonempty piece
    must be writable in `mp`; zero-length entries are skipped and produce
    no vacuous effect write.  `none` means either that `bs` exceeds the
    aggregate capacity or that some byte which would be delivered is not
    writable. -/
def scatter_iovecs (mp : word → Option byte) (iovs : List (word × word))
    (bs : List byte) : Option (List (word × List byte)) :=
  match bs with
  | [] => some []
  | _ :: _ =>
      match iovs with
      | [] => none
      | (base, len) :: rest =>
          let n := word_to_nat_bounded len bs.length
          let here := bs.take n
          let later := bs.drop n
          match here with
          | [] => scatter_iovecs mp rest later
          | _ :: _ =>
              match read_bytes_map mp base (len_word here),
                    scatter_iovecs mp rest later with
              | some _, some writes => some ((base, here) :: writes)
              | _, _ => none

theorem scatter_iovecs_concat :
    ∀ (mp : word → Option byte) (iovs : List (word × word)) (bs : List byte)
      (writes : List (word × List byte)),
      scatter_iovecs mp iovs bs = some writes →
      (writes.map Prod.snd).flatten = bs := by
  intro mp iovs
  induction iovs with
  | nil =>
    intro bs writes H
    cases bs with
    | nil =>
      simp only [scatter_iovecs, Option.some.injEq] at H
      subst H
      rfl
    | cons b bs' =>
      rw [show scatter_iovecs mp [] (b :: bs') = none from rfl] at H
      simp at H
  | cons hd rest ih =>
    obtain ⟨base, len⟩ := hd
    intro bs writes H
    cases bs with
    | nil =>
      simp only [scatter_iovecs, Option.some.injEq] at H
      subst H
      rfl
    | cons b bs' =>
      simp only [scatter_iovecs] at H
      split at H
      · rename_i hhere
        have hn : word_to_nat_bounded len (b :: bs').length = 0 := by
          rcases List.take_eq_nil_iff.mp hhere with h | h
          · exact h
          · simp at h
        rw [hn, List.drop_zero] at H
        exact ih (b :: bs') writes H
      · rename_i hhead hhere
        split at H
        · rename_i ok hread
          simp only [Option.some.injEq] at H
          subst H
          simp only [List.map_cons, List.flatten_cons]
          rw [ih _ _ hread]
          exact List.take_append_drop _ _
        · simp at H

/-- An empty delivery performs no writes, independently of the vector. -/
theorem scatter_iovecs_nil (mp : word → Option byte) (iovs : List (word × word)) :
    scatter_iovecs mp iovs [] = some [] := by
  cases iovs with
  | nil => rfl
  | cons hd tl => obtain ⟨b, l⟩ := hd; rfl

/-- Whether a one-byte scatter succeeds depends only on the destination
    vector and its writability, not on the value of the byte. -/
theorem scatter_iovecs_singleton_some (mp : word → Option byte) :
    ∀ (iovs : List (word × word)) (b : byte)
      (writes : List (word × List byte)) (b' : byte),
      scatter_iovecs mp iovs [b] = some writes →
      ∃ writes', scatter_iovecs mp iovs [b'] = some writes' := by
  intro iovs
  induction iovs with
  | nil =>
    intro b writes b' H
    rw [show scatter_iovecs mp [] [b] = none from rfl] at H
    simp at H
  | cons hd rest ih =>
    obtain ⟨base, len⟩ := hd
    intro b writes b' H
    simp only [scatter_iovecs] at H ⊢
    rw [show ([b] : List byte).length = 1 from rfl] at H
    rw [show ([b'] : List byte).length = 1 from rfl]
    have hnle : word_to_nat_bounded len 1 ≤ 1 := by
      rw [word_to_nat_bounded_eq_min]; exact Nat.min_le_right _ _
    rcases hcase : word_to_nat_bounded len 1 with _ | k
    · simp only [hcase] at H ⊢
      exact ih b writes b' H
    · have hk : k = 0 := by omega
      subst hk
      simp only [hcase] at H ⊢
      simp [scatter_iovecs_nil] at H ⊢
      rw [show len_word ([b'] : List byte) = len_word [b] from rfl]
      cases hr : read_bytes_map mp base (len_word [b]) with
      | none => rw [hr] at H; simp at H
      | some v => exact ⟨[(base, [b'])], rfl⟩

/-- Gather the source bytes of each iovec in order into one flat byte
    string (`none` if any source byte is unreadable) — exactly the
    buffer an equivalent single `write` would write. -/
def gather_iovecs (mp : word → Option byte) : List (word × word) → Option (List byte)
  | [] => some []
  | (base, len) :: r =>
      match read_bytes_map mp base len with
      | none => none
      | some bs =>
          match gather_iovecs mp r with
          | some rest => some (bs ++ rest)
          | none => none

/-- The GATHERABLE PREFIX of an iovec sequence: the bytes a real
    kernel's writev moves before faulting.  Linux consumes the iovecs
    in order, copy_from_user-ing each source buffer as it goes, so a
    fault inside an iovec delivers that iovec's readable prefix and
    stops — the flattened analogue of `readable_bytes`.  Equals the
    full flattening exactly when every source byte is readable (i.e.
    when `gather_iovecs` succeeds); zero-length iovecs are skipped
    without touching their base pointer, as on Linux.  The
    completeness test compares lengths in `Int` over the unsigned value
    (no wrapping). -/
def gather_prefix (mp : word → Option byte) : List (word × word) → List byte
  | [] => []
  | (base, len) :: r =>
      let bs := readable_bytes mp base len
      if (bs.length : Int) = (len.toNat : Int) then bs ++ gather_prefix mp r else bs

/-- Total byte count an iovec list requests (writev's EFAULT gate:
    a delivery of zero bytes is an error only when something was
    actually requested).  Summed in `Int` over unsigned lengths, so the
    total cannot wrap. -/
def iovs_total : List (word × word) → Int
  | [] => 0
  | (_, len) :: r => (len.toNat : Int) + iovs_total r

theorem iovs_total_nonneg (iovs : List (word × word)) : 0 ≤ iovs_total iovs := by
  induction iovs with
  | nil => simp [iovs_total]
  | cons hd rest ih =>
    obtain ⟨base, len⟩ := hd
    simp only [iovs_total]
    have := Int.natCast_nonneg len.toNat
    omega

/-- `min` distributes over the budget the way `cap_iovecs_aux` spends
    it: `min c a + min b (c - min c a) = min (a + b) c` for `0 ≤ b`,
    `0 ≤ c`.  This is the arithmetic core of `iovs_total_cap_aux`. -/
private theorem cap_min_add (a b c : Int) (hb : 0 ≤ b) :
    0 ≤ c → min c a + min b (c - min c a) = min (a + b) c := by
  intro hc
  by_cases h1 : c ≤ a
  · rw [Int.min_eq_left h1, Int.min_eq_right (by omega : c ≤ a + b)]
    rw [show c - c = (0 : Int) by omega, Int.min_eq_right (by omega : (0 : Int) ≤ b)]
    omega
  · rw [Int.min_eq_right (by omega : a ≤ c)]
    by_cases h2 : c - a ≤ b
    · rw [Int.min_eq_right h2, Int.min_eq_right (by omega : c ≤ a + b)]
      omega
    · rw [Int.min_eq_left (by omega : b ≤ c - a), Int.min_eq_left (by omega : a + b ≤ c)]

/-- `cap_iovecs` IS the kernel's aggregate clamp, and this is the only
    statement of that in the tree: capping a vector leaves an aggregate of
    exactly `min` of the original aggregate and `MAX_RW_COUNT`.  Stated
    here rather than beside `cap_iovecs` because `iovs_total` is defined
    below it.

    The generalized form quantifies over the budget `left` still unspent,
    which is what the induction needs; the top-level `iovs_total_cap`
    instantiates it at `MAX_RW_COUNT`. -/
theorem iovs_total_cap_aux :
    ∀ (iovs : List (word × word)) (left : Int), 0 ≤ left →
      iovs_total (cap_iovecs_aux iovs left) = min (iovs_total iovs) left := by
  intro iovs
  induction iovs with
  | nil => intro left hleft; simp [iovs_total, cap_iovecs_aux, Int.min_eq_left hleft]
  | cons hd rest ih =>
    obtain ⟨base, len⟩ := hd
    intro left hleft
    simp only [iovs_total, cap_iovecs_aux]
    have hL : 0 ≤ (len.toNat : Int) := Int.natCast_nonneg _
    have hLlt : (len.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by
      have := len.isLt; omega
    have hn0 : 0 ≤ min left (len.toNat : Int) := Int.le_min.mpr ⟨hleft, hL⟩
    have hnlt : min left (len.toNat : Int) < ((2 ^ 64 : Nat) : Int) :=
      Int.lt_of_le_of_lt (Int.min_le_right _ _) hLlt
    have hsub : 0 ≤ left - min left (len.toNat : Int) := by
      have := Int.min_le_left left (len.toNat : Int); omega
    rw [toNat_ofInt_eq_self hn0 hnlt, ih (left - min left (len.toNat : Int)) hsub]
    exact cap_min_add _ _ _ (iovs_total_nonneg rest) hleft

theorem iovs_total_cap (iovs : List (word × word)) :
    iovs_total (cap_iovecs iovs) = min (iovs_total iovs) MAX_RW_COUNT := by
  unfold cap_iovecs
  exact iovs_total_cap_aux iovs MAX_RW_COUNT (by unfold MAX_RW_COUNT; decide)

/-- The bytes a writev moves, and the -EFAULT gate in front of them,
    each stated ONCE for the whole tree.  `__import_iovec` applies the
    aggregate `MAX_RW_COUNT` clamp inside its per-segment loop for BOTH
    directions, so the write side must gather over `cap_iovecs` exactly
    as the read side scatters over it.  Every writev body — the
    relational spec, the acceptor and the progress witness, each with
    one channel arm and one file arm — goes through these two, so there
    is no per-arm clamp left to forget on one side and remember on the
    other. -/
def writev_gathered (mp : word → Option byte)
    (iovs0 : List (word × word)) : List byte :=
  gather_prefix mp (cap_iovecs iovs0)

/-! ## Sanity checks

  -/

/-- A tiny memory image: the bytes of `bs` at addresses `0`, `1`, … and
    nothing anywhere else.  Test scaffolding for the checks below; no
    part of the model refers to it. -/
def sanityMem (bs : List byte) : word → Option byte := fun a => bs[a.toNat]?

/-- `read_cstr` stops at the NUL and does not include it. -/
example : read_cstr (sanityMem [104, 105, 0, 0]) 0 = .CstrOk [104, 105] := by decide

/-- An unmapped byte before the NUL is `-EFAULT`, not `-ENAMETOOLONG`. -/
example : read_cstr (sanityMem [104, 105]) 0 = .CstrFault := by decide

/-- No NUL within the fuel is `-ENAMETOOLONG`. -/
example : read_cstr_aux (sanityMem [1, 2, 3]) 0 3 = .CstrTooLong := by decide

/-- The recorded read count includes the NUL and stops there. -/
example : cstr_access_len_aux (sanityMem [1, 2, 0, 9]) 0 10 = 3 := by decide

/-- `read_u64` is little-endian: index 0 is the least significant byte. -/
example :
    read_u64 (sanityMem [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]) 0
      = some (0x0102030405060708 : word) := by decide

/-- ...and a short mapping is `none`, not a partial word. -/
example : read_u64 (sanityMem [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02]) 0 = none := by
  decide

/-- `TASK_SIZE` is 2^47 (Sv48); a range ending exactly at it is accepted
    and one byte past it is not. -/
example : access_okb 0 0x800000000000 = true := by decide
example : access_okb 0 0x800000000001 = false := by decide
example : access_okb 0x800000000000 0 = true := by decide
example : access_okb 0x800000000001 0 = false := by decide
example : access_okb 0x7fffffffffff 1 = true := by decide
example : access_okb 0x7fffffffffff 2 = false := by decide

/-- `copy_bytes_map` refuses what `access_okb` refuses, even where the
    memory map would happily answer. -/
example : copy_bytes_map (sanityMem [1, 2, 3]) 0 0x800000000001 = none := by decide

/-- The aggregate clamp leaves an under-cap iovec sequence alone and
    truncates an over-cap one. -/
example : cap_iovecs [(0, 8), (100, 16)] = [(0, 8), (100, 16)] := by decide
example : iovs_total [(0, 8), (100, 16)] = 24 := by decide

/-- The clamp truncates an over-cap entry and leaves the following ones
    present with length zero. -/
example : iovs_total (cap_iovecs [(0, 0x7ffff064), (8, 8)]) = 0x7ffff000 := by decide

/-- `import_iovecs`: a zero count imports nothing, a count over `IOV_MAX`
    is `-EINVAL` before any descriptor is read, and an unmapped descriptor
    array is `-EFAULT`. -/
example : import_iovecs (sanityMem []) 0 0 = .ImpOk [] := by decide
example : import_iovecs (sanityMem []) 0 1025 = .ImpInval := by decide
example : import_iovecs (sanityMem []) 0 2 = .ImpFault := by decide

/-- `read_iovecs` decodes `(base, len)` pairs from the array. -/
example :
    read_iovecs (sanityMem [0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0]) 0 1
      = some [(0, 16)] := by decide

/-- `scatter_iovecs` on an empty delivery writes nothing; on a mapped
    destination it reports the piece it would write. -/
example : scatter_iovecs (sanityMem [0, 0, 0, 0]) [] [] = some [] := by decide
example : scatter_iovecs (sanityMem [0, 0, 0, 0]) [(0, 2)] [7, 8] = some [(0, [7, 8])] := by
  decide

end LinuxSem.LinuxProcessSem

