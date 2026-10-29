/-
  * LinuxProcessSem.Sys.Fs.Stat — readlinkat (78), newfstatat (79), fstat (80)

  This file answers to Linux `fs/stat.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

      From LinuxSem.LinuxProcessSem Require Import BvBase Fs State Monad.
      From LinuxSem.LinuxProcessSem.Sys Require Export Syscall Uapi.

  Here `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
  so a spec's type is `SysSpec SyscallEffect`,
  and `getModelSpec`/`inputSpec` are `get_model`/`input`.
  `StateMemory` supplies `read_cstr`, `cstr_access_len_aux`, `path_max`
  and `access_okb`; `StateLedger` supplies `m_fs`, `m_statpins` and
  `with_statpin`; `StateFd` supplies `fd_lookup`; `Fs` supplies
  `fs_lookup`, `path` and `path_eqb`; `Sys.Uapi` supplies the whole
  `struct stat` layer (`STAT_SIZE`, the `ST_*_OFF` offsets,
  `stat_buf_wf`, `stat_size_ok`, `stat_stable_eqb`, the `S_IF*` mask and
  `stat_ifmt`, `dot_path`, `devnull_path`, `urandom_path`,
  `stat_devnull_ok`, `stat_urandom_ok`, `AT_FDCWD32`,
  `AT_SYMLINK_NOFOLLOW`); `Sys.Syscall` supplies `ret_only`, `err_ret`
  and `record_copyins`.  `Sys.Uaccess` is deliberately NOT imported: no
  arm of this file reaches a user buffer through it, and nothing here
  needs its qualified names.

  `x <- c;; k` has no Lean counterpart, so it is `bind c (fun x => k)` here. The same
  state update, one unfolding further out.

  `choose` takes a `Prop`;

  file is NINE DEFINITIONS and
  their prose: it contains no lemma, and no `decide` goal.  All nine
  are ported, in order.  The `example`s at the end are PORT CHECKS, and
  the one helper lemma (`newfstatat_spec_unmodeled_of_core`) is a port
  scaffold rather than a restatement.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Stat

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

/- =========================================================================
   readlinkat (78)
   ========================================================================= -/

/-- `readlinkat dirfd path buf bufsiz`: the modeled file system has NO
    symlinks (`Fs.lean`: paths are uninterpreted names, no symlink objects),
    so no path a program can name resolves to one — and readlink(2) on
    anything that is not a symlink is -EINVAL.

    The DIRFD is the one argument that is checked, and only AT_FDCWD is
    modeled: `do_readlinkat` resolves the dirfd through `fdget_raw`
    inside path resolution, so `readlinkat(999, "f", buf, 64)` is -EBADF
    on Linux — asserting -EINVAL there would
    REJECT a conforming trace, which is worse than declining.  Any other
    dirfd therefore is `unmodeled`, fail closed, exactly as openat's does.
    `dirfd` arrives already truncated to 32 bits (see `Syscall.fd32`), so
    `readlinkat(2^32 - 100, ...)` names the working directory as Linux
    does.

    Everything under AT_FDCWD is the deterministic -EINVAL.  No other
    argument is validated.  ORDERING CHOICE: the kernel resolves the
    path BEFORE touching the output buffer, so the path-based -EINVAL
    wins over any buffer problem — the buffer is deliberately NOT
    checked against `in_wmem` (a successful readlinkat never happens, so
    no byte is ever delivered).

    APPROXIMATION (deliberate).  Under AT_FDCWD the path itself
    is still not interpreted, so a missing path (-ENOENT on Linux) and a bad
    path pointer (-EFAULT) are both coarsened to -EINVAL, and the `int bufsiz`
    gate Linux applies BEFORE path resolution (`bufsiz <= 0` is -EINVAL) is
    subsumed rather than modeled.  Those are FALSE REJECTIONS of conforming
    traces, not fail-closed gaps: no modeled binary consumes readlinkat's
    result, and interpreting the path here would duplicate openat's path-errno
    machinery. -/
def readlinkat_spec (dirfd : word) : SysSpec SyscallEffect :=
  if !(bv_eqb dirfd AT_FDCWD32) then unmodeled   -- unmodeled dirfd: fail closed
  else err_ret EINVAL

/- =========================================================================
   newfstatat (79)
   ========================================================================= -/

/-- The flag WORDS `newfstatat_spec` interprets: 0 (plain `stat`) and
    AT_SYMLINK_NOFOLLOW (`lstat`).  Those are the only two riscv64 musl
    ever puts on syscall 79.  Following that through musl takes three
    steps, none of them obvious from the file names: riscv64 has no
    `__NR_fstatat`, but src/internal/syscall.h defines `SYS_fstatat` to
    be `SYS_newfstatat` when the latter exists, so the `#ifdef
    SYS_fstatat` arm of src/stat/fstatat.c IS compiled; that arm takes
    the `statx` path only when the kernel `struct kstat`'s timestamps
    are narrower than `time_t`, and on riscv64 both are 64 bits, so
    `__fstatat` falls through to `fstatat_kstat`; and `fstatat_kstat`
    has no `SYS_stat`/`SYS_lstat` to prefer, so it issues syscall 79
    with whatever flag it was given.  `stat()` gives it 0 and `lstat()`
    AT_SYMLINK_NOFOLLOW (src/stat/stat.c, src/stat/lstat.c).  `fstat()`
    does NOT arrive here: it calls `__fstatat(fd, "", st, AT_EMPTY_PATH)`
    (src/stat/fstat.c), and `fstatat_kstat` spends exactly that shape on
    `fstat` (80) before it would reach 79.

    The two modeled flag words are also indistinguishable IN the model:
    the interpreted file system has no symlink objects (`Fs.lean`), so
    following one is never different from not following one.

    Everything else — AT_EMPTY_PATH, AT_NO_AUTOMOUNT, the
    AT_STATX_SYNC_TYPE bits, and every word Linux answers -EINVAL for —
    is unmodeled and DECLINED, not answered.  Declining costs precision
    and nothing else: see the ORDER paragraph at `newfstatat_spec`. -/
def modeled_statat_flags (flag : word) : Bool :=
  let fl := flag.toNat
  (fl : Int) == 0 || (fl : Int) == AT_SYMLINK_NOFOLLOW

/-- `newfstatat dirfd path statbuf flag` — `stat`/`lstat` as modern libc
    issues them.  KERNEL SCOPE for everything below: Linux v6.10-v6.15,
    fs/stat.c, `SYSCALL_DEFINE4(newfstatat)` / `cp_new_stat`, and
    fs/namei.c, `getname_flags` / `filename_lookup` / `path_init`.
    `SYSCALL_DEFINE4(newfstatat)` and `cp_new_stat` are byte-identical
    across that range; `vfs_fstatat` and `vfs_statx` are not, and the
    part that moved is the reason AT_EMPTY_PATH is declined below.

    THE SUCCESS ARM IS NOT MODELED, AND CANNOT BE FROM WHAT `Fs` CARRIES.
    A successful call writes 128 bytes of `struct stat` (riscv64 has no
    `asm/stat.h` of its own, so it uses the asm-generic layout,
    include/uapi/asm-generic/stat.h): st_dev at 0, st_ino at 8, st_mode
    at 16, st_nlink at 20, st_uid at 24, st_gid at 28, st_rdev at 32,
    st_size at 48, st_blksize at 56, st_blocks at 64, and three
    timestamps with their nanosecond halves from 72 to 120.  All 128
    bytes are written: `cp_new_stat` zeroes its stack copy through
    `INIT_STRUCT_STAT_PADDING` (which riscv64 leaves at the generic
    `memset`, as only x86 overrides it) and hands the whole thing to
    `copy_to_user` in one call, so the padding is delivered too.

    The interpreted file system is a map from path to CONTENTS (`Fs.lean`)
    and carries none of that — no file type, no permission bits, no
    owner, no inode, no device, no link count, no timestamps.  Of the
    128 bytes only st_size follows from what `Fs` holds — and the
    S_IFMT type bits follow only from the premise named below, not from
    `Fs` at all.  A spec that answered the call would be inventing the
    rest, so every path that RESOLVES is `unmodeled`: fail closed.

    THE MACHINERY IS NOT WHAT IS MISSING — `fstat_file_spec` BELOW HAS
    IT.  That arm answers the same 128 bytes for a DESCRIPTOR: it pins
    the padding `cp_new_stat` clears, derives `st_size` under the
    kernel's own S_IFREG test rather than asserting the type, and
    chooses the members `Fs` cannot supply once per file and holds them
    fixed.  None of that needs a path.

    WHAT IS MISSING HERE IS THE RESOLUTION.  This spec reaches its file
    through `fs_lookup` on an uninterpreted pathname, and the same flat
    namespace that makes it answer -ENOENT for "f/x" and ".." is what a
    success arm would have to resolve first — and that is a change to
    `Fs` rather than to this spec.  The premise that every path names a
    regular file is the second half:
    `Open.openat_spec` admits a name the model has no type for, and a
    path-based stat meets that on its most ordinary input rather than
    behind a descriptor whose file the model has already been reading
    and writing.  Per-file metadata closes neither.

    WHAT IS MODELED is the failing side, which is exactly the part of
    the call that writes nothing: `SYSCALL_DEFINE4(newfstatat)` reaches
    `cp_new_stat` only once `vfs_fstatat` has returned 0, so on every
    arm below the kernel leaves `statbuf` untouched.  That is why this
    spec does not take the `statbuf` pointer at all — its arity is the
    statement that no modeled arm can deliver a byte, and hence that
    none can fault on the destination either.  (A bad `statbuf` with an
    absent file really is -ENOENT on Linux: the -EFAULT of a bad
    `statbuf` is `copy_to_user`'s, raised after the stat has already
    succeeded, and it is the LAST thing that can go wrong.)

    ORDER.  Chronologically the kernel copies the pathname in first
    (`vfs_fstatat` calls `getname_flags` before `vfs_statx`), but a
    failure there is only STASHED as an `ERR_PTR`; `vfs_statx` tests the
    flags before it hands that stashed value to `filename_lookup`, which
    is what finally returns it.  So the priority of the errno the caller
    actually sees is: the flag word first (`flags & ~(AT_SYMLINK_NOFOLLOW
    | AT_NO_AUTOMOUNT | AT_EMPTY_PATH | AT_STATX_SYNC_TYPE)` is -EINVAL),
    then the pathname, then the dirfd (`path_init` raises -EBADF only for
    a relative walk), then the file, then -EFAULT on `statbuf`.  This
    spec follows that priority exactly, with DECLINING substituted for
    the -EINVAL: a flag word the model has not interpreted is one it
    cannot judge the call from.

    Declining rather than asserting -EINVAL costs precision in one
    shape and nothing else: `newfstatat(AT_FDCWD, <a 4096-byte path>,
    buf, AT_NO_AUTOMOUNT)` is -ENAMETOOLONG on Linux, and here it is
    declined.  Asserting -EINVAL instead would be a confident wrong
    answer on every flag word Linux ACCEPTS.  The flag arrives already
    truncated to 32 bits (`Syscall.flag32`), so the high half of the
    register is not part of the comparison.

    Under a modeled flag word the pathname fetch comes first, with all
    three of `getname_flags`'s answers — -ENAMETOOLONG for no NUL within
    PATH_MAX, -EFAULT for an unmapped byte, and the string otherwise —
    and the empty pathname is its -ENOENT (`getname_flags` returns that
    unless LOOKUP_EMPTY is set, and no modeled flag word sets it at
    either end of the window: v6.10-v6.12 route through
    `getname_statx_lookup_flags`, which sets LOOKUP_EMPTY only for
    AT_EMPTY_PATH, and from v6.13 `vfs_fstatat` calls
    `getname_maybe_null`, which for a non-AT_EMPTY_PATH flag word is
    plain `getname` — that is, `getname_flags` with no flags at all; the
    successor `statx_lookup_flags` dropped the LOOKUP_EMPTY arm
    entirely).  All three preempt the dirfd, so they are answered before it
    is looked at, exactly as `Open.openat_spec` does.

    Then the dirfd: only AT_FDCWD is modeled, and any other is
    `unmodeled` — asserting an errno for a directory the model cannot
    name would reject a conforming trace.  `dirfd` arrives already
    truncated to 32 bits (see `Syscall.fd32`), so
    `newfstatat(2^32 - 100, ...)` names the working directory as Linux
    does.

    Then the path.  "." is a path the model resolves to a directory
    (`Uapi.dot_path`), and a directory's metadata is as absent from `Fs`
    as a file's, so it is declined too.  ".." is NOT declined here, and
    that is a divergence rather than a choice: this spec lets it fall
    through to `fs_lookup` and so answers a deterministic -ENOENT, an
    errno Linux never gives for "..", while `Open.openat_spec` and
    `Open.faccessat_spec` both resolve it (`Open.path_is_dirref`).  The
    same model therefore says two things about "..", one function call
    apart.  Any other path the
    file system does not hold is the real -ENOENT; any path it does hold
    would succeed on Linux, and is declined.

    APPROXIMATION 1 (deliberate, and the same shape as
    `Open.openat_spec`'s path-resolution arms).  The -ENOENT is asserted
    with no alternative, whereas Linux can fail the call before
    resolution with `getname_flags`'s own -ENOMEM.  This NARROWS the
    spec, so it admits nothing unsound; the cost is that a source and a
    target which diverge only under allocation failure are not
    distinguished.

    APPROXIMATION 2 (deliberate, inherited from `Fs`'s flat namespace,
    not introduced here).  Paths are uninterpreted byte strings with no
    directory structure, so "f/x" where "f" is a regular file is simply
    a key the map does not hold, and answers -ENOENT where Linux answers
    -ENOTDIR.  `Open.openat_spec` does not have this property on the
    same paths: it declines a pathname with a separator instead of
    answering off the map.  This spec answers, so the divergence is
    this spec's alone.
    It is a fact about `Fs`, and fixing it means giving `Fs` directories.

    THE COPY-IN LEDGER.  The pathname fetch is a real
    `strncpy_from_user` of user memory, so it is recorded as one, with
    the same `record_copyins` wrapper and the same range
    `Open.openat_spec` uses: `cstr_access_len_aux (in_mem i) pathp
    path_max`, the bytes through the first NUL, the first unreadable
    byte, or PATH_MAX.  The wrapper sits OUTSIDE the flag test, so every
    arm the spec ANSWERS carries the ledger — the `CstrFault` one
    included, where `cstr_access_len_aux` counts the faulting byte
    itself (a `none` byte is 1, `State.lean`): the kernel attempted that
    byte, and an immediate -EFAULT is a fetch that happened, not one
    that did not.  The declining arms cost nothing, because
    `Syscall.record_copyins_unmodeled` carries `unmodeled` through the
    wrapper untouched — so wrapping the uninterpreted flag word does not
    disturb the ORDER argument above.

    This is not bookkeeping.  `State.syscall_effect_accesses` is
    `eff_copyins` followed by the write ranges, and `Run.lean`'s
    `sstep_syscall` charges exactly that list against the process's
    backing budget.  An empty ledger here would charge NOTHING for a
    page the model holds lazily and the machine overlay (`Run.lean`'s
    `in_mem`) answers from anyway — an under-charge, which is the
    direction that grants an allocation the kernel refuses.  The ledger
    is short by up to 7 bytes, because `strncpy_from_user` reads a word
    at a time, and this spec inherits that bound rather than restating it.

    SHARED WITH `Open.openat_spec`, AND DELIBERATELY LEFT INLINE.  The
    three steps between the flag word and the path — `read_cstr`'s three
    answers, the empty pathname's -ENOENT, and the AT_FDCWD gate — are
    the same sequence `Open.openat_spec` runs, wrapped in the same
    ledger, and those two specs are its only copies (mirrored once more
    by `Open.check_openat` and `Stat.check_newfstatat`, whose soundness
    and completeness lemmas discharge by destructing `read_cstr`
    directly).  They are kept side by side rather than hoisted into a
    shared combinator: what repeats is five lines of already shared
    primitives (`read_cstr`, `Fs.path_eqb`, `Uapi.AT_FDCWD32`,
    `err_ret`) under one already shared wrapper
    (`Syscall.record_copyins`), and hoisting them would have to thread a
    continuation through both checkers, where the arm-for-arm mirroring
    is what keeps those four lemmas short.  The price is that
    APPROXIMATION 1, and any later correction to this precedence or to
    the recorded range, must be made in both places.  `readlinkat_spec`
    above is the third call site waiting to happen — it asserts -EINVAL
    without interpreting its pathname at all, and fixing it means
    reusing this machinery — so that is the point at which
    extracting a shared helper pays for itself. -/
def newfstatat_core_spec (dirfd pathp flag : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    bind getModelSpec fun m =>
      /- a flag word the model does not interpret: decline, never assert -/
      if !(modeled_statat_flags flag) then unmodeled
      else
        /- `getname_flags()`: all three of its answers are real errnos, and
           all three preempt the dirfd. -/
        match read_cstr i.in_mem pathp with
        | .CstrTooLong => err_ret ENAMETOOLONG  -- no NUL within PATH_MAX
        | .CstrFault => err_ret EFAULT  -- unmapped byte in the path string
        | .CstrOk p =>
            if path_eqb p [] then err_ret ENOENT
              -- empty pathname: AT_EMPTY_PATH is not modeled
            else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
              -- unmodeled dirfd: fail closed
            else if path_eqb p dot_path then unmodeled
              -- the working directory: no metadata in `Fs`
            else
              match fs_lookup (m_fs m) p with
              | none => err_ret ENOENT
                -- file absent: real -ENOENT, not a modeling gap
              | some _ => unmodeled
                -- resolves: 128 bytes `Fs` cannot supply

/-- The pathname fetch, recorded.  In Linux v6.18.46 `vfs_fstatat`
    (fs/stat.c) fetches the pathname in the initializer of its `name`
    local, before it calls `vfs_statx` at all.  Its callee is
    `getname_maybe_null` (include/linux/fs.h); no flag word this spec
    answers sets AT_EMPTY_PATH, so that is plain `getname` — which is
    `getname_flags` with no flags at all (fs/namei.c) — and
    `getname_flags`'s `strncpy_from_user` is the byte fetch itself.
    Every outcome the core spec answers is downstream of that fetch, so
    the range belongs to all of them; see THE COPY-IN LEDGER above.  The
    ORDER paragraph above answers a different question — which errno the
    caller finally sees, where the flag word still wins. -/
def newfstatat_spec (dirfd pathp flag : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (newfstatat_core_spec dirfd pathp flag)

/- =========================================================================
   fstat (80)
   ========================================================================= -/

/-! `fstat fd statbuf` — `newfstatat`'s descriptor-only sibling, and the
    number riscv64 musl really reaches for `fstat()`.  Syscall 79 is
    modeled above, by `newfstatat_spec`; nothing below leans on it.
    KERNEL SCOPE:
    Linux v6.10-v6.15, fs/stat.c, `SYSCALL_DEFINE2(newfstat)`,
    `cp_new_stat` and `vfs_fstat`.  The first two are byte-identical
    across that range and its stable branches; `vfs_fstat` is not, and
    where it moved is recorded below.

    riscv64 has no `__NR_fstat` of its own, but WHERE it inherits 80
    changed inside the window, so the citation is two.  Through v6.10 it
    is the generic table's
    `__SC_3264(__NR3264_fstat, sys_fstat64, sys_newfstat)`
    (include/uapi/asm-generic/unistd.h), resolving to `sys_newfstat`
    because `__BITS_PER_LONG` is 64.  From v6.11 riscv generates its
    table instead, and the entry is `80 64 fstat sys_newfstat` in
    scripts/syscall.tbl.  The `64` on that line is one of the ABI tokens
    scripts/Makefile.asm-headers contributes (`syscall_abis_64 +=
    common,64`); arch/riscv/kernel/Makefile.syscalls appends only
    `riscv`, `rlimit` and `memfd_secret` to the same variable, so it is
    not where the `64` comes from.  Either way the definition is
    reached because riscv64 defines `__ARCH_WANT_NEW_STAT`, which is the
    only guard on it — the `__ARCH_WANT_STAT64` one nearby covers
    `newfstatat`, not this.

    THE SPEC IS THE ORDER, AND THE ORDER IS TWO STEPS:

      SYSCALL_DEFINE2(newfstat, unsigned int, fd, struct stat __user *, statbuf)
        error = vfs_fstat(fd, &stat);        <- -EBADF here, WRITING NOTHING
        if (!error) error = cp_new_stat(&stat, statbuf);

    Everything this spec answers is the first line, and everything it
    declines is the second.  `vfs_fstat` resolves the descriptor before
    it looks at anything else and returns -EBADF when the process does
    not hold it, so a call that names a closed fd AND a bad `statbuf` is
    -EBADF and never -EFAULT: `cp_new_stat`, which is where a bad
    `statbuf` would be noticed, has not run.  That is the whole of the
    -EBADF arm, and on it the pointer is never read and never written.

    `vfs_fstat` is REWRITTEN TWICE inside the version window and the
    -EBADF survives all three spellings, which is why the arm can be
    asserted over the whole of it: v6.10-v6.11 take `fdget_raw` and test
    `!f.file`, v6.12 keeps `fdget_raw` and tests `!fd_file(f)`, and
    v6.13 onward is `CLASS(fd_raw, f)(fd)` with `fd_empty(f)`.  The
    guard class expands to the same `fdget_raw`, and its `EMPTY_FD` is
    returned exactly where the older code left `.file` NULL.  Neither
    rewrite was backported, so a stable branch carries its series' form.

    THE DESCRIPTOR IS 32 BITS, and the truncation is the syscall
    wrapper's rather than the hardware's: `fd` is declared `unsigned
    int`, `__SC_LONG` widens it to a `long` on the way in, and
    `__SC_CAST` discards the high half at the call
    (arch/riscv/include/asm/syscall_wrapper.h, include/linux/syscalls.h).
    `Syscall.fd32` is that cast.  Two consequences it is worth being
    able to read off this spec: a register of all ones is fd -1 and
    -EBADF, and a register of 2^32 is fd ZERO — a live descriptor, not a
    rejected one — so the truncation can turn a nonsense argument into a
    call this spec declines rather than answers.

    THE SUCCESS ARM IS MODELED, FOR THE FOUR FILE KINDS AND FOR THE TWO
    DEVICE KINDS AND NO OTHER, and it is `fstat_file_spec` below (and
    its device twin `fstat_chrdev_spec`) rather than part of this
    definition: `vfs_fstat`'s -EBADF is what THIS spec answers, and
    everything a success delivers is `cp_new_stat`'s.  The split follows
    the kernel's two lines, and it is why this spec takes `statbuf` —
    the pointer really is read on the arms that succeed.

    WHAT THE ARM COSTS AND WHAT IT BUYS is argued on
    `fstat_file_spec`.  In one line: `st_size` is derived under the
    kernel's own S_IFREG condition, the twenty bytes of padding are
    pinned to zero, and the other members are chosen once per file and
    then held fixed, so a second `fstat` of one file cannot report a
    different inode.

    THE SHAPE A REAL PROGRAM SPENDS ON IT is musl's `__map_file`
    (src/time/__map_file.c, called from src/time/__tz.c), which opens a
    TZif file, fstats it for `st_size` alone, and maps exactly that many
    bytes.  It is worth naming because it is CHECKABLE FROM THIS TREE
    that the shape leaves the modeled surface on the FAR side of the
    fstat, whoever issues it: the map is file-backed MAP_SHARED, where
    all three of `Mmap.mmap_modeled_b`, `Mmap.mmap_noaccess_b` and
    `Mmap.mmap_fixed_noaccess_b` require MAP_PRIVATE|MAP_ANONYMOUS, and
    `Mmap.mmap_spec`'s file-backed branch declines every
    MAP_ANONYMOUS-clear call before a shape is matched at all.  Its
    open — O_RDONLY|O_CLOEXEC|O_NONBLOCK — is ADMITTED
    (`Open.open_ignored_flags` strips O_NONBLOCK alongside O_CLOEXEC and
    O_LARGEFILE), so the near side carries no decline.  The fstat itself
    is answered; the mmap after it is not, which is why this
    arm buys no additional COVERED RUN on that path and is not defended
    on those grounds.

    That this is the ONLY `fstat` a `dropbear -i` session issues is an
    OUT-OF-TREE MEASUREMENT and is not a checked fact: a qemu-riscv64
    -strace of a static riscv64-musl `dropbear -i`,
    404 syscalls through KEX, auth and exit, whose log is not committed
    here.  It corroborates the paragraph above rather than carrying it —
    re-measure before relying on it.

    THE -EBADF IS ASSERTED WITH NO ALTERNATIVE, and that is exactness
    rather than an approximation: `vfs_fstat` resolves the descriptor
    before anything else can fail, so a call naming a closed fd AND a bad
    `statbuf` is -EBADF and never -EFAULT.  `cp_new_stat` has not run.
    The errnos reachable past an OPEN descriptor are `fstat_file_spec`'s
    subject. -/

/-- THE SUCCESS ARM, for a descriptor on a file the interpreted file
    system holds.  It is the second line of the two above:

      if (!error) error = cp_new_stat(&stat, statbuf);

    and everything below is `cp_new_stat` (fs/stat.c, Linux v6.18.46,
    commit 1f99e9ab748f) rather than `vfs_fstat`.

    WHAT THE MODEL DETERMINES, and it is less than half the struct:

    - THE WIDTH AND THE PADDING.  `cp_new_stat` clears its whole stack
      copy through `INIT_STRUCT_STAT_PADDING` — the generic `memset` on
      riscv64, only x86 overriding it — assigns the members, and hands
      all 128 bytes to ONE `copy_to_user`.  So `__pad1`, `__pad2`,
      `__unused4` and `__unused5` are delivered as ZERO, and the write
      is exactly `Uapi.STAT_SIZE` bytes wide at `statbuf`.  This is the
      part of the answer the model knows exactly, and it is what makes a
      poisoned, short or invented buffer rejectable
      (`Uapi.stat_buf_wf`).
    - `st_size`, AND ONLY IF THE KERNEL SAYS THE FILE IS REGULAR.
      `generic_fillattr` (fs/stat.c) copies `inode->i_size`, which for a
      regular file is the file's length, and the model's length is the
      byte list `Fs` carries for the path this descriptor names.  The
      IMPLICATION is the whole of the claim
      (`Uapi.stat_size_ok`): the model does NOT know the file is
      regular, and a path it resolves can be one that Linux calls a
      character device, where the true answer is S_IFCHR with `st_size`
      0 against a nonempty byte list.  Asserting S_IFREG, or asserting the length outright,
      would REJECT that conforming trace.  Under the implication the
      model says nothing about it and still says something sharp about
      every file that really is regular — which is the same premise
      `ReadWrite.read_spec` already commits to on the same descriptor,
      and no wider.

    WHAT IT DOES NOT DETERMINE, and how it answers anyway.  The device,
    the inode, the mode's type and permission bits, the link count, the
    owning ids, `st_rdev`, the block size, the block count and the three
    timestamp pairs have no source in `Fs`, which is a map from path to
    CONTENTS.  Each is a `choose` — an environment value, not a zero.
    Zero-filling them would be a confident wrong answer of exactly the
    kind design priority 1 (README.md) forbids.

    FOUR MEMBERS ARE LEFT OUT OF THE PIN and are therefore re-chosen at
    every call: `st_blocks` and the three timestamp pairs.  That is
    over-admission — the model accepts a run in which two stats of one
    untouched file report time running backwards, which Linux does not
    produce — and it is kept because holding them fixed would reject the
    ordinary stat/write/stat trace instead.

    THE CHOICE IS PINNED, per file, in `State.procst_statpins`, and that
    is what makes it a check rather than a shrug.  Chosen afresh at each
    call these members would admit a trace in which two `fstat`s of one
    unchanged file report different inodes, which no Linux machine
    produces — the objection `State.procst_utsname` answers for the UTS
    name and `Sys.Kernel.Sched.Syscalls.sched_getaffinity_spec` answers
    by declining.  So the first stat of a file records the 128 bytes it
    delivered, and every later stat of the same file must repeat its
    STABLE members (`Uapi.stat_stable_eqb`): the device, inode, mode,
    link count, ids, `st_rdev` and block size.  `st_size`, `st_blocks`
    and the timestamps are deliberately NOT held against the pin,
    because a write moves all three.

    A PIN THAT IS NOT `Uapi.stat_buf_wf` IS DECLINED, and that branch is
    unreachable: the only writer is the branch below, which has just
    checked the predicate.  It is written rather than argued away
    because receptiveness (`Checks.Progress`) is a statement about every
    `Model`, including ones no run can build, and an unsatisfiable
    `choose` is the one way to write a non-receptive spec (Monad.lean).

    THE ORDER IS THE KERNEL'S.  `vfs_fstat` resolves the descriptor
    before `cp_new_stat` runs, so -EBADF preempts everything here; then
    `copy_to_user`'s `access_ok` gate refuses the 128-byte range with
    -EFAULT before a byte moves; then the range is either wholly
    writable, which is the modeled path, or partially so, which is
    `unmodeled` — a `copy_to_user` that commits a prefix and then faults
    leaves a half-written struct this model has no vocabulary for, the
    shape `Kernel.Sys.uname_spec` and `Time.gettimeofday_spec` decline
    for the same reason.  Asking `access_ok` BEFORE the walk is
    load-bearing rather than cosmetic, for the wrapping reason
    `Kernel.Sys.uname_spec` states.

    A PATH `Fs` NO LONGER HOLDS IS DECLINED.  `unlinkat` (35) removes a
    key while a descriptor on it stays open, and Linux answers such an
    `fstat` with the inode's surviving metadata and `st_nlink` 0.  The
    model has no contents to size and no link count to drop, so it
    declines — which is also what keeps `st_nlink` among the members the
    pin holds fixed. -/
def fstat_file_spec (p : path) (statbuf : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    bind getModelSpec fun m =>
      match fs_lookup (m_fs m) p with
      | none => unmodeled
        -- unlinked under an open fd: no contents to size
      | some data =>
          if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
          else
            match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
            | none => unmodeled
              -- a partial `copy_to_user` then -EFAULT
            | some _ =>
                match statpin_lookup (m_statpins m) p with
                | some b0 =>
                    if !(stat_buf_wf b0) then unmodeled
                      -- no branch writes such a pin
                    else
                      bind (choose (fun bs : List byte =>
                              stat_buf_wf bs = true ∧
                              stat_size_ok data.length bs = true ∧
                              stat_stable_eqb bs b0 = true)) fun bs =>
                        pure (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] [])
                | none =>
                    bind (choose (fun bs : List byte =>
                            stat_buf_wf bs = true ∧
                            stat_size_ok data.length bs = true)) fun bs =>
                      seqSpec (modifySpec (with_statpin p bs))
                        (pure (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []))

/-- THE SUCCESS ARM FOR A CHARACTER DEVICE THE MODEL KNOWS, in two
    instances: /dev/null (`fstat_devnull_spec`, under `Uapi.devnull_path`
    and `Uapi.stat_devnull_ok`) and /dev/urandom (`fstat_urandom_spec`,
    under `Uapi.urandom_path` and `Uapi.stat_urandom_ok`).  It is
    `fstat_file_spec`'s shape with the file's one implication replaced
    by the device's assertions: the model KNOWS which device this
    descriptor is — that is the assumption the openat arm states — so
    `st_mode`'s type, `st_rdev`, `st_size` and `st_blocks` are pinned
    outright, and the members the kernel does not decide are chosen
    once and held in `State.procst_statpins` under the device's path,
    exactly as a file's are under its key.  `p` is that path and `ok`
    the device's assertions; nothing below reads either for anything
    but the pin's key and the delivery's test.

    THE PIN IS CHECKED AGAINST BOTH PREDICATES before it is used, where
    the file arm checks `stat_buf_wf` alone.  The file arm patches
    `st_size` into whatever pin it holds, and `st_size` is outside the
    stable members, so any well-formed pin admits a delivery; here the
    asserted members are INSIDE the stable region (`st_mode` and
    `st_rdev`) or asserted constant (`st_size`, `st_blocks`), so a pin
    that failed `stat_devnull_ok` would leave the `choose` below with no
    satisfying buffer — a non-receptive spec, the one shape Monad.lean
    forbids.  Declining such a pin keeps the arm receptive on every
    `Model`; the branch is unreachable, since the only writer is the
    branch below, which has just checked both predicates.

    No `fs_lookup`: the device is not a key, and `unlinkat` cannot reach
    it (the separator decline stands for it), so there is no
    unlinked-under-an-open-fd case to decline.  The rest — -EBADF before
    anything, `access_ok`'s -EFAULT, the partial `copy_to_user`
    decline, the errnos past an open descriptor — is `fstat_file_spec`'s
    argument unchanged. -/
def fstat_chrdev_spec (p : path) (ok : List byte → Bool)
    (statbuf : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    bind getModelSpec fun m =>
      if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
      else
        match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
        | none => unmodeled
          -- a partial `copy_to_user` then -EFAULT
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0 && ok b0) then unmodeled
                  -- no branch writes such a pin: see above
                else
                  bind (choose (fun bs : List byte =>
                          stat_buf_wf bs = true ∧
                          ok bs = true ∧
                          stat_stable_eqb bs b0 = true)) fun bs =>
                    pure (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] [])
            | none =>
                bind (choose (fun bs : List byte =>
                        stat_buf_wf bs = true ∧
                        ok bs = true)) fun bs =>
                  seqSpec (modifySpec (with_statpin p bs))
                    (pure (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []))

/-- The null device: S_IFCHR, `st_rdev` 1:3, zero size and blocks. -/
def fstat_devnull_spec (statbuf : word) : SysSpec SyscallEffect :=
  fstat_chrdev_spec devnull_path stat_devnull_ok statbuf

/-- The random device: S_IFCHR, `st_rdev` 1:9, zero size and blocks
    (`Uapi.stat_urandom_ok`), on the assumption
    `Open.openat_urandom_spec` states — the image's /dev/urandom is the
    random device, major 1 minor 9.  `cp_new_stat` (fs/stat.c,
    v6.18.46) reads the same inode members it reads for /dev/null; the
    zero `st_size` and `st_blocks` rest on the same premise about a
    node nothing ever resized. -/
def fstat_urandom_spec (statbuf : word) : SysSpec SyscallEffect :=
  fstat_chrdev_spec urandom_path stat_urandom_ok statbuf

/-- THE MATCH BELOW IS TOTAL ON `FdEntry` ON PURPOSE, with no wildcard.
    A new constructor is a new kind of file, and whoever adds it must
    decide what `fstat` says about it; the non-exhaustive-match error is
    the only thing that makes them.

    THE FOUR FILE KINDS SHARE ONE ANSWER because they share one inode:
    `FdFile`, `FdFileW`, `FdFileA` and `FdFileRW` differ in how the
    descriptor was opened and in nothing `cp_new_stat` reads.  Neither
    `f_mode` nor `f_flags` is a member of `struct stat`, so HOW A
    DESCRIPTOR WAS OPENED is not something a stat can report; and the
    model's own difference between them — which of `ReadWrite`'s arms
    will serve the descriptor — is not a member either.  Two of them are
    worth naming, and for one reason: `FdFileA`'s writes land at the
    file's end, and `FdFileRW`'s single shared `f_pos` means a read
    moves the offset the next write lands at, so in both the `st_size`
    moves under the descriptor exactly as `FdFileW`'s does.  That is
    what the ONE implication below is: the size obligation is a function
    of the CURRENT contents rather than of the descriptor, which is why
    the same one serves all four.

    /dev/null ANSWERS TOO, through `fstat_devnull_spec`: the model minted
    that descriptor knowing it is the null device, so the type bits and
    the device number are asserted where the file arm can only imply.
    /dev/urandom answers the same way through `fstat_urandom_spec`.

    THE FOUR OTHER KINDS STILL DECLINE, and they are not equally far
    from an answer:

      - `FdChannel` — the type bits alone are undecidable.  A channel is
        the model's one name for a pipe, a socket and a terminal (see
        `FdChannel`'s own note), so S_IFIFO, S_IFSOCK and S_IFCHR are
        all live and nothing in the model chooses between them.  A
        `choose` over the type would not fix it: the pin makes two stats
        agree with each other, not with the kernel, and there is nothing
        here for the size obligation to bite on.
      - `FdDir` — S_IFDIR is the one type bit the model does know, and it
        buys nothing: a directory's `st_size` and `st_blocks` are the
        filesystem's own bookkeeping, not a function of anything `Fs`
        holds, so the arm would carry no obligation at all.
      - `FdSocket` — the BEST-DETERMINED of the four.  `sock_alloc`
        (net/socket.c, v6.18.46) sets `i_mode = S_IFSOCK | S_IRWXUGO` —
        a CONSTANT — and `i_uid`/`i_gid` from
        `current_fsuid`/`current_fsgid`, which `State.Creds` argues
        coincide with euid/egid here.  `sockfs_inode_ops` carries no
        `.getattr`, so `vfs_getattr_nosec` fills the rest with
        `generic_fillattr` out of pseudo-filesystem constants:
        `inode_init_always` (fs/inode.c) leaves `i_nlink` 1, `i_rdev` 0,
        `i_size` 0 and `i_blocks` 0, and `i_blkbits` is
        `pseudo_fs_fill_super`'s PAGE_SHIFT (fs/libfs.c).  What is out of
        reach is `st_ino` (`get_next_ino`), `st_dev` (the sockfs
        superblock's anonymous device, from `set_anon_super`) and the
        three timestamps.  Those are the members the machinery above
        exists for, so this arm is a matter of WRITING IT rather than
        of the model lacking a mechanism; it is left declined here
        because the fields it would pin are kernel constants that want
        their own citations, not because it cannot be done.
      - `FdPipe` — S_IFIFO is known and the rest is not, and a pipe's
        `st_size`/`st_blocks` are not even the queue's length, so
        nothing plays the role `Fs`'s contents play above.

    WHAT IS NOT REACHABLE PAST THE ARMS ASSERTED.  On an open descriptor
    Linux can still fail — `vfs_getattr` runs `security_inode_getattr`,
    which an LSM may refuse, and a filesystem's own `.getattr` may return
    an error.  This model has no security module, so an LSM refusal is
    not an outcome it can represent; that is a premise on the
    environment rather than a claim about Linux, and it is the one thing
    the success arm adds to what the -EBADF arm already assumed.
    `cp_new_stat`'s five -EOVERFLOW tests cannot fire on riscv64: four
    are false because every destination member is at least as wide as
    its `kstat` source, and the `MAX_NON_LFS` one is inside
    `#if BITS_PER_LONG == 32`. -/
def fstat_spec (fd statbuf : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    match fd_lookup (m_fds m) fd with
    | none => err_ret EBADF
      -- `vfs_fstat`'s own answer, before `statbuf` is touched
    | some (FdEntry.FdChannel _) => unmodeled
      -- pipe, socket or terminal: even the type bits are undecided
    | some (FdEntry.FdFile p _) => fstat_file_spec p statbuf
    | some (FdEntry.FdFileW p _) => fstat_file_spec p statbuf
      -- the same inode, opened for writing
    | some (FdEntry.FdFileA p _) => fstat_file_spec p statbuf
      -- and again in append mode
    | some (FdEntry.FdFileRW p _) => fstat_file_spec p statbuf
      -- and again opened O_RDWR.  Same inode, and the
      -- read-write kind's SINGLE SHARED `f_pos` means a
      -- read moves the offset the next write lands at, so
      -- its `st_size` moves under it exactly as
      -- `FdFileW`'s does -- the size obligation is a
      -- function of the CURRENT contents, not of the
      -- descriptor (`cp_new_stat`/`generic_fillattr`,
      -- fs/stat.c, v6.18.46, 1f99e9ab748f)
    | some FdEntry.FdDir => unmodeled
      -- S_IFDIR is known; a directory's size and blocks are not
    | some (FdEntry.FdSocket _) => unmodeled
      -- mode/uid/gid are known; ino, dev and the timestamps are not
    | some (FdEntry.FdPipe _ _) => unmodeled
      -- S_IFIFO is known; a pipe's `st_size`/`st_blocks` are
      -- not even the queue's length, so nothing plays the
      -- role the file contents play above
    | some (FdEntry.FdDevNull _ _) => fstat_devnull_spec statbuf
      -- the null device: S_IFCHR, `st_rdev` 1:3, `st_size`
      -- and `st_blocks` 0 asserted (`Uapi.stat_devnull_ok`),
      -- the rest pinned once under `Uapi.devnull_path`
    | some FdEntry.FdUrandom => fstat_urandom_spec statbuf
      -- the random device: S_IFCHR, `st_rdev` 1:9
      -- (`Uapi.stat_urandom_ok`), the rest pinned once
      -- under `Uapi.urandom_path`

/-- THE COPY-IN WRAPPER CARRIES `unmodeled` THROUGH UNTOUCHED, which is
    why the declining arms cost no ledger entry and why the ORDER
    argument on `newfstatat_core_spec` survives the wrapper
    (`Syscall.record_copyins_unmodeled`).  This is port scaffolding for
    the checks below, not a restatement. -/
private theorem newfstatat_spec_unmodeled_of_core (dirfd pathp flag : word)
    (i : SyscallInput) (m : Model)
    (h : newfstatat_core_spec dirfd pathp flag i m .unmodeled) :
    newfstatat_spec dirfd pathp flag i m .unmodeled := by
  unfold newfstatat_spec
  exact bind_unmodeled2 inputSpec _ i m i m [] rfl (record_copyins_unmodeled h)

/-! ## Sanity checks

  It is the nine definitions above and their prose. The checks below are PORT CHECKS,
  and they pin the answers that prose argues for against a concrete model:

    - the 128-byte `struct stat` envelope and the two members the model
      settles — the derived `st_size` and the `S_IFMT` type bits — which
      is exactly what `fstat_file_spec`'s `choose` constrains;
    - `fstat` of a missing descriptor is -EBADF, decided by the fd
      lookup before `statbuf` is touched;
    - `fstat` of a regular file DELIVERS THE PINNED BUFFER, unchanged;
    - `newfstatat`'s answered arms: an absent path is -ENOENT (carried by
      the copy-in ledger of the pathname fetch), an empty pathname is
      -ENOENT too, and a faulting byte is -EFAULT;
    - `newfstatat`'s declining arms, including the one that never
      interprets the pathname at all;
    - `readlinkat`'s two arms, and the 32-bit truncation its dirfd test
      rests on.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so the checks state the spec's OUTCOME
    rather than comparing entries: the outcome carries the returned word
    and the whole `SyscallEffect`, which is what a caller observes.  The
    `Bool`-valued helpers of `Uapi` (`stat_buf_wf`, `stat_ifmt`,
    `stat_size_ok`, `modeled_statat_flags`) are `by decide`.

  The envelope checks below run `decide`
    over `stat_buf_wf`, `stat_field_le` and `stat_set_size` on a literal
    128-element byte list, and the kernel's default recursion depth
    (1000) is not enough for those ground reductions.  The option below
    raises the fuel; it is not a proof principle, and every term it is
    spent on is closed. -/

set_option maxRecDepth 8000

/-- A 128-byte `struct stat` with the shape `cp_new_stat` delivers: every
    padding byte zero, and `st_mode`'s type bits S_IFREG at offset 16
    (0x8000 little-endian).  Bytes 48..55, the `st_size` field, are left
    zero here and are written by `stat_set_size` in `demoStatBuf`. -/
private def demoStatBase : List byte :=
  List.replicate 16 (0 : byte) ++ ([0x00, 0x80, 0x00, 0x00] : List byte)
    ++ List.replicate 28 (0 : byte) ++ List.replicate 80 (0 : byte)

/-- The same buffer with `st_size` derived from a five-byte file: `fstat`
    of `f` must deliver exactly this, since the model settles the width,
    the padding, the type bits and the size, and the rest is the
    environment's. -/
private def demoStatBuf : List byte := stat_set_size 5 demoStatBase

/-! ### The `struct stat` envelope -/

/-- 128 bytes, and `stat_buf_wf` admits it. -/
example : demoStatBuf.length = 128 := by decide
example : stat_buf_wf demoStatBuf = true := by decide

/-- It names the REGULAR FILE type, which is what makes
    `stat_size_ok`'s implication apply to it. -/
example : stat_ifmt demoStatBuf = S_IFREG := by decide
example : stat_is_reg demoStatBuf = true := by decide

/-- THE DERIVED `st_size`: offset 48 carries the five bytes the file
    holds, `stat_size_ok` accepts that length and rejects any other. -/
example : stat_field_le ST_SIZE_OFF 8 demoStatBuf = 5 := by decide
example : stat_size_ok 5 demoStatBuf = true := by decide
example : stat_size_ok 6 demoStatBuf = false := by decide

/-- The padding really is zero, and a buffer that poisons `__pad1` is NOT
    well formed — that is the part of the answer `cp_new_stat` settles
    without consulting the inode, and what makes a poisoned or invented
    buffer rejectable. -/
example : stat_field_le ST_PAD1_OFF 8 demoStatBuf = 0 := by decide
example :
    stat_buf_wf (demoStatBuf.take 40 ++ [0x01] ++ demoStatBuf.drop 41) = false := by
  decide

/-- The two flags `newfstatat` interprets are 0 (`stat`) and
    AT_SYMLINK_NOFOLLOW (`lstat`); AT_EACCESS is a word Linux accepts on
    this syscall and that the model has no arm for. -/
example : modeled_statat_flags 0 = true := by decide
example : modeled_statat_flags (BitVec.ofInt 64 AT_SYMLINK_NOFOLLOW) = true := by
  decide
example : modeled_statat_flags 1 = false := by decide
example : modeled_statat_flags (BitVec.ofInt 64 AT_EACCESS) = false := by decide

/-- THE TRUNCATION IS THE DISPATCHER'S (`Syscall.flag32`), not this
    function's: 2^32 is not the flag word 0, and `flag32 2^32` is. -/
example : modeled_statat_flags (BitVec.ofInt 64 4294967296) = false := by decide
example : modeled_statat_flags (flag32 (BitVec.ofInt 64 4294967296)) = true := by
  decide

/-! ### The fixture the spec checks run on -/

/-- A tiny fd table for the checks: 0 a regular file `f`, 1 a directory,
    2 `/dev/null`, 3 a channel. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdFile [(0x66 : byte)] 0),
    (1, FdEntry.FdDir),
    (2, FdEntry.FdDevNull true false),
    (3, FdEntry.FdChannel 7) ]

/-- The file system: one regular file, `f`, holding the five bytes
    `demoStatBuf`'s `st_size` was derived from. -/
private def demoFs : List (path × List byte) :=
  [ ([(0x66 : byte)], [1, 2, 3, 4, 5]) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    EOF on stdin, no stat pins yet, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof demoFs none none none

/-- The same model with `f`'s `struct stat` already pinned, which is the
    branch that must repeat the pinned bytes rather than choose again.
    `fstat_file_spec`'s `none` arm is the only writer, so the checks
    install the pin by hand exactly as that arm would. -/
private def pinnedModel : Model :=
  with_statpin [(0x66 : byte)] demoStatBuf demoModel

/-- The model with an EMPTY file system: every pathname is absent. -/
private def emptyModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The fully writable overlay the `fstat` checks deliver into. -/
private def demoWmem : word → Option byte := fun _ => some 0

/-- `AT_EACCESS` (0x200) as the 64-bit flag word a caller passes:
    a word Linux ACCEPTS on `newfstatat` and that the model has no arm
    for, so it is the shape the fail-closed arm must cover. -/
private def atEaccessWord : word := BitVec.ofInt 64 AT_EACCESS

/-- A syscall input for `fstat` (80), with a writable range at the
    `statbuf` the checks use, so `access_okb` accepts the 128-byte
    destination and `read_bytes_map` walks all of it. -/
private def demoInputW : SyscallInput :=
  { in_sysno := 80, in_args := [0, 0x1000], in_mem := sanityMem [0x66, 0],
    in_wmem := demoWmem }

/-- A syscall input for `newfstatat` (79) whose memory holds the
    pathname `f` at address 0 followed by its NUL, and nothing else. -/
private def demoInputN : SyscallInput :=
  { in_sysno := 79, in_args := [], in_mem := sanityMem [0x66, 0],
    in_wmem := fun _ => none }

/-- The same, with the pathname `.` — the working directory, which
    `newfstatat_spec` declines rather than answer. -/
private def dotInputN : SyscallInput :=
  { in_sysno := 79, in_args := [], in_mem := sanityMem [0x2e, 0],
    in_wmem := fun _ => none }

/-- The same, with the pathname `f/x` — a key the flat namespace does not
    hold, so it answers -ENOENT where Linux answers -ENOTDIR
    (APPROXIMATION 2 on `newfstatat_core_spec`). -/
private def nestedInputN : SyscallInput :=
  { in_sysno := 79, in_args := [], in_mem := sanityMem [0x66, 0x2f, 0x78, 0],
    in_wmem := fun _ => none }

/-- The same, with an EMPTY pathname: its first byte is the NUL. -/
private def emptyPathInputN : SyscallInput :=
  { in_sysno := 79, in_args := [], in_mem := sanityMem [0],
    in_wmem := fun _ => none }

/-- The same, with NO memory at all: the first byte faults. -/
private def faultInputN : SyscallInput :=
  { in_sysno := 79, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- The pathname fetch the ledger records: through the first NUL, which
    for `f` is two bytes (the byte and its terminator). -/
example : cstr_access_len_aux demoInputN.in_mem 0 path_max = 2 := by decide

/-! ### `readlinkat`'s arms -/

/-- UNDER AT_FDCWD THE ANSWER IS THE DETERMINISTIC -EINVAL: the model has
    no symlink objects, and readlink(2) of a non-symlink is -EINVAL.  No
    byte is delivered and the model is untouched. -/
example :
    readlinkat_spec AT_FDCWD32 demoInputN demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := rfl

/-- The same word written out as its low 32 bits: `2^32 - 100` IS the
    working directory's descriptor, which is the truncation the header
    claims. -/
example :
    readlinkat_spec (BitVec.ofInt 64 4294967196) demoInputN demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := rfl

/-- ANY OTHER DIRFD IS DECLINED, not answered: asserting an errno for a
    directory the model cannot name would reject a conforming trace
    (`readlinkat(999, "f", buf, 64)` is -EBADF on Linux). -/
example : readlinkat_spec 999 demoInputN demoModel .unmodeled := rfl

/-- THE TRUNCATION IS LOAD-BEARING, in the direction that looks wrong:
    the dirfd reaches the spec already narrowed by `Syscall.fd32`, so the
    SIGN-EXTENDED `AT_FDCWD` (all ones above bit 31) is NOT the working
    directory's word and is declined, while its low 32 bits are.  A
    dispatcher that forgot the narrowing would answer -EINVAL to a call
    the kernel resolves. -/
example : readlinkat_spec AT_FDCWD demoInputN demoModel .unmodeled := rfl

/-! ### `fstat`'s arms -/

/-- A MISSING FD IS -EBADF, and the fd lookup is what decides: `statbuf`
    is never read, never written, and no other test runs — so a closed fd
    with a bad `statbuf` is -EBADF and never -EFAULT. -/
example :
    fstat_spec 9 0x1000 demoInputW demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [fstat_spec, getModelSpec, bind_getModel, hlook, err_ret,
    ret_only, pure]

/-- A CHANNEL FD IS DECLINED: a pipe, a socket and a terminal share the
    one constructor, so even `st_mode`'s type bits are undecided. -/
example : fstat_spec 3 0x1000 demoInputW demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [fstat_spec, getModelSpec, bind_getModel, hlook, unmodeled]

/-- A DIRECTORY FD IS DECLINED: S_IFDIR is the one type bit the model
    knows, and a directory's size and blocks are the filesystem's own
    bookkeeping. -/
example : fstat_spec 1 0x1000 demoInputW demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [fstat_spec, getModelSpec, bind_getModel, hlook, unmodeled]

/-- A FILE DESCRIPTOR ON A PATH `Fs` NO LONGER HOLDS IS DECLINED:
    `unlinkat` can remove the key under an open descriptor, and the model
    then has no contents to size. -/
example : fstat_spec 0 0x1000 demoInputW emptyModel .unmodeled := by
  have hlook : fd_lookup (m_fds emptyModel) 0 =
      some (FdEntry.FdFile [(0x66 : byte)] 0) := by
    simp [m_fds, emptyModel, mkModel, demoFds, fd_lookup]
  have hnone : fs_lookup (m_fs emptyModel) [(0x66 : byte)] = none := by
    simp [m_fs, emptyModel, mkModel, fs_lookup]
  simp only [fstat_spec, getModelSpec, bind_getModel, hlook]
  unfold fstat_file_spec
  refine bind_unmodeled2 inputSpec _ demoInputW emptyModel demoInputW emptyModel
    [] rfl ?_
  simp only [getModelSpec, bind_getModel, hnone, unmodeled]

/-- THE PIN IS REPEATED, and the delivered bytes are the PINNED ones: the
    second `fstat` of an unchanged file reports the same 128-byte
    `struct stat`, `st_size` included, because the pin decides every
    member the model does not.  The `choose` set is a singleton here. -/
example :
    fstat_spec 0 0x1000 demoInputW pinnedModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [(0x1000, demoStatBuf)] [])
        pinnedModel []) := by
  have hlook : fd_lookup (m_fds pinnedModel) 0 =
      some (FdEntry.FdFile [(0x66 : byte)] 0) := by
    simp [m_fds, pinnedModel, with_statpin, demoModel, mkModel, demoFds,
      fd_lookup]
  have hfs : fs_lookup (m_fs pinnedModel) [(0x66 : byte)] = some [1, 2, 3, 4, 5] := by
    decide
  have hpin : statpin_lookup (m_statpins pinnedModel) [(0x66 : byte)] =
      some demoStatBuf := by
    decide
  have hwf : stat_buf_wf demoStatBuf = true := by decide
  have hsize : stat_size_ok 5 demoStatBuf = true := by decide
  have hstable : stat_stable_eqb demoStatBuf demoStatBuf = true := by decide
  have hok : access_okb 0x1000 STAT_SIZE = true := by decide
  have hread : read_bytes_map demoWmem 0x1000 (BitVec.ofInt 64 STAT_SIZE) =
      some (List.replicate 128 (0 : byte)) := by decide
  simp only [fstat_spec, getModelSpec, bind_getModel, hlook]
  unfold fstat_file_spec
  refine bind_ok inputSpec _ demoInputW pinnedModel demoInputW pinnedModel []
    _ pinnedModel [] rfl ?_
  simp only [getModelSpec, bind_getModel, hfs, hok, hread, hpin, hwf,
    Bool.not_true, Bool.false_eq_true, ite_false, demoInputW]
  refine bind_ok _ _ demoInputW pinnedModel demoStatBuf pinnedModel [] _
    pinnedModel [] ?_ rfl
  exact choose_ok _ demoStatBuf _ _ ⟨hwf, hsize, hstable⟩

/-! ### `newfstatat`'s arms

    Each answered arm is proved in two steps — the core spec's outcome,
    then the copy-in wrapper around it — because the pathname fetch is
    the only part of the call that touches user memory, and the ledger is
    the statement that it happened.  Every fact the arms turn on is a
    GROUND computation (`read_cstr` of a concrete memory, `path_eqb` of
    two concrete paths, `modeled_statat_flags` of a concrete word), so
    the proofs reduce the definitions in place rather than carrying
    hypotheses about them: a numeral elaborated in a hypothesis and the
    same numeral inside a spec's body are not always the same term to
    `simp`'s matcher, and letting the goal's own terms reduce sidesteps
    that entirely. -/

/-- AN ABSENT PATH IS -ENOENT, wrapped in the ledger of the fetch that
    looked for it: the flag word is modeled, the pathname resolves, and
    the map does not hold the key.  This is the real -ENOENT rather than
    a modeling gap (APPROXIMATION 1 narrows it and nothing more). -/
example :
    newfstatat_spec AT_FDCWD32 0 0 demoInputN emptyModel
      (.ok (with_copyins [(0, 2)] (mkEffect (errno_ret ENOENT) [] []))
        emptyModel []) := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 demoInputN emptyModel
      (.ok (mkEffect (errno_ret ENOENT) [] []) emptyModel []) := by
    simp only [newfstatat_core_spec]
    refine bind_ok inputSpec _ demoInputN emptyModel demoInputN emptyModel []
      _ emptyModel [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, sanityMem, path_eqb, bv_eqb, dot_path,
      fs_lookup, mkModel, m_fs, demoInputN, emptyModel, err_ret, ret_only,
      pure]
  simp only [newfstatat_spec, record_copyins]
  refine bind_ok inputSpec _ demoInputN emptyModel demoInputN emptyModel []
    _ emptyModel [] rfl ?_
  refine bind_ok _ _ demoInputN emptyModel
    (mkEffect (errno_ret ENOENT) [] []) emptyModel [] _ emptyModel []
    hcore ?_
  exact pure_ok _ _ _

/-- AN EMPTY PATHNAME IS -ENOENT: `getname_flags` answers that whenever
    LOOKUP_EMPTY is clear, and no modeled flag word sets AT_EMPTY_PATH —
    and it is answered BEFORE the dirfd is looked at. -/
example :
    newfstatat_spec AT_FDCWD32 0 0 emptyPathInputN emptyModel
      (.ok (with_copyins [(0, 1)] (mkEffect (errno_ret ENOENT) [] []))
        emptyModel []) := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 emptyPathInputN emptyModel
      (.ok (mkEffect (errno_ret ENOENT) [] []) emptyModel []) := by
    simp only [newfstatat_core_spec]
    refine bind_ok inputSpec _ emptyPathInputN emptyModel emptyPathInputN
      emptyModel [] _ emptyModel [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, sanityMem, path_eqb, bv_eqb, mkModel,
      emptyPathInputN, emptyModel, err_ret, ret_only, pure]
  simp only [newfstatat_spec, record_copyins]
  refine bind_ok inputSpec _ emptyPathInputN emptyModel emptyPathInputN
    emptyModel [] _ emptyModel [] rfl ?_
  refine bind_ok _ _ emptyPathInputN emptyModel
    (mkEffect (errno_ret ENOENT) [] []) emptyModel [] _ emptyModel []
    hcore ?_
  exact pure_ok _ _ _

/-- A FAULTING BYTE IS -EFAULT, and the faulting byte is COUNTED in the
    ledger: the kernel attempted that byte, so the fetch happened. -/
example :
    newfstatat_spec AT_FDCWD32 0 0 faultInputN emptyModel
      (.ok (with_copyins [(0, 1)] (mkEffect (errno_ret EFAULT) [] []))
        emptyModel []) := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 faultInputN emptyModel
      (.ok (mkEffect (errno_ret EFAULT) [] []) emptyModel []) := by
    simp only [newfstatat_core_spec]
    refine bind_ok inputSpec _ faultInputN emptyModel faultInputN emptyModel
      [] _ emptyModel [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, faultInputN, err_ret, ret_only, pure]
  simp only [newfstatat_spec, record_copyins]
  refine bind_ok inputSpec _ faultInputN emptyModel faultInputN emptyModel []
    _ emptyModel [] rfl ?_
  refine bind_ok _ _ faultInputN emptyModel
    (mkEffect (errno_ret EFAULT) [] []) emptyModel [] _ emptyModel []
    hcore ?_
  exact pure_ok _ _ _

/-- `f`/`x` IS -ENOENT HERE AND -ENOTDIR ON LINUX.  This is
    APPROXIMATION 2 (the flat namespace) answering rather than
    declining, and it is recorded as a check so that a change to `Fs`
    that introduces directories breaks it visibly. -/
example :
    newfstatat_spec AT_FDCWD32 0 0 nestedInputN emptyModel
      (.ok (with_copyins [(0, 4)] (mkEffect (errno_ret ENOENT) [] []))
        emptyModel []) := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 nestedInputN emptyModel
      (.ok (mkEffect (errno_ret ENOENT) [] []) emptyModel []) := by
    simp only [newfstatat_core_spec]
    refine bind_ok inputSpec _ nestedInputN emptyModel nestedInputN emptyModel
      [] _ emptyModel [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, sanityMem, path_eqb, bv_eqb, dot_path,
      fs_lookup, mkModel, m_fs, nestedInputN, emptyModel, err_ret,
      ret_only, pure]
  simp only [newfstatat_spec, record_copyins]
  refine bind_ok inputSpec _ nestedInputN emptyModel nestedInputN emptyModel
    [] _ emptyModel [] rfl ?_
  refine bind_ok _ _ nestedInputN emptyModel
    (mkEffect (errno_ret ENOENT) [] []) emptyModel [] _ emptyModel []
    hcore ?_
  exact pure_ok _ _ _

/-- …while a path the file system DOES hold is DECLINED: it would succeed
    on Linux, and 128 bytes of it cannot be supplied from `Fs`. -/
example : newfstatat_spec AT_FDCWD32 0 0 demoInputN demoModel .unmodeled := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 demoInputN demoModel .unmodeled := by
    simp only [newfstatat_core_spec]
    refine bind_unmodeled2 inputSpec _ demoInputN demoModel demoInputN
      demoModel [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, sanityMem, path_eqb, bv_eqb, dot_path,
      fs_lookup, mkModel, m_fs, demoInputN, demoModel, demoFs, unmodeled]
  exact newfstatat_spec_unmodeled_of_core _ _ _ _ _ hcore

/-- THE WORKING DIRECTORY IS DECLINED TOO: `.` is a path the model
    resolves to a directory (`Uapi.dot_path`), and a directory's metadata
    is as absent from `Fs` as a file's. -/
example : newfstatat_spec AT_FDCWD32 0 0 dotInputN demoModel .unmodeled := by
  have hcore : newfstatat_core_spec AT_FDCWD32 0 0 dotInputN demoModel .unmodeled := by
    simp only [newfstatat_core_spec]
    refine bind_unmodeled2 inputSpec _ dotInputN demoModel dotInputN demoModel
      [] rfl ?_
    simp [getModelSpec, bind_getModel, modeled_statat_flags, read_cstr,
      read_cstr_aux, path_max, sanityMem, path_eqb, bv_eqb, dot_path,
      mkModel, dotInputN, demoModel, unmodeled]
  exact newfstatat_spec_unmodeled_of_core _ _ _ _ _ hcore

/-- A FLAG WORD THE MODEL DOES NOT INTERPRET IS DECLINED WITHOUT THE
    PATHNAME BEING LOOKED AT — AT_EACCESS (0x200) here, a word Linux
    accepts on this syscall and that the model has no arm for.  Declining
    beats guessing an errno for it, and the copy-in wrapper carries the
    `unmodeled` through. -/
example :
    newfstatat_spec AT_FDCWD32 0 atEaccessWord demoInputN demoModel .unmodeled := by
  have hflags : modeled_statat_flags atEaccessWord = false := by decide
  have hcore : newfstatat_core_spec AT_FDCWD32 0 atEaccessWord demoInputN
      demoModel .unmodeled := by
    simp only [newfstatat_core_spec]
    refine bind_unmodeled2 inputSpec _ demoInputN demoModel demoInputN
      demoModel [] rfl ?_
    simp [getModelSpec, bind_getModel, hflags, demoInputN, demoModel,
      unmodeled]
  exact newfstatat_spec_unmodeled_of_core _ _ _ _ _ hcore

/-- THE ERRNO WORDS REALLY ARE THE KERNEL'S, and the success return of
    the file arm really is a zero word: what the checks above read off
    the outcome is the same value a program sees in `a0`. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret ENOENT = BitVec.ofInt 64 (-2) := by decide
example : errno_ret EFAULT = BitVec.ofInt 64 (-14) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : errno_ret ENAMETOOLONG = BitVec.ofInt 64 (-36) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end LinuxSem.LinuxProcessSem.Sys.Fs.Stat
