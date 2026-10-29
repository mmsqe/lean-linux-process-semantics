/-
  * LinuxProcessSem.Sys.Syscall — the syscall calling convention

  Every other file under `Sys/` answers to one kernel SOURCE file;
  this one answers to a kernel HEADER, `include/linux/syscalls.h`, and
  holds what the specs share rather than any one syscall's behaviour.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  here that is `SysSpec SyscallEffect` from `MonadInstances`.

  `Sys/Uapi.lean` currently carries
  its own `abi_low32`/`fd32` because this file had not landed yet; the two
  now coexist in different namespaces.  Nothing here depends on `Uapi`,
  and the Uapi copies should be deleted in favour of these.
-/
import LinuxSem.LinuxProcessSem.MonadInstances

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Syscall

/-! ## The two primitive shapes of a spec -/

/-- Return `r` with no memory writes. -/
def ret_only (r : word) : SysSpec SyscallEffect := pure (mkEffect r [] [])

/-- Fail with errno `e` (a0 = -e). -/
def err_ret (e : Int) : SysSpec SyscallEffect := ret_only (errno_ret e)

/-! ## Recording copy-from-user ranges -/

/-- Attach the copy-from-user ranges at the point where the syscall has
    actually performed them.  Keeping this in the effect distinguishes two
    paths that return the same errno before and after a user-memory read. -/
def record_copyins (reads : List (word × Nat))
    (spec : SysSpec SyscallEffect) : SysSpec SyscallEffect :=
  bind spec fun eff => pure (with_copyins (reads ++ eff.eff_copyins) eff)

theorem record_copyins_ok {reads : List (word × Nat)}
    {spec : SysSpec SyscallEffect} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : spec i m (.ok eff m' evs)) :
    record_copyins reads spec i m
      (.ok (with_copyins (reads ++ eff.eff_copyins) eff) m' evs) :=
  ⟨eff, m', evs, [], H, rfl, by simp⟩

theorem record_copyins_ok_empty {reads : List (word × Nat)}
    {spec : SysSpec SyscallEffect} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (Hempty : eff.eff_copyins = [])
    (H : spec i m (.ok eff m' evs)) :
    record_copyins reads spec i m (.ok (with_copyins reads eff) m' evs) := by
  simpa [Hempty] using record_copyins_ok (reads := reads) H

theorem record_copyins_unmodeled {reads : List (word × Nat)}
    {spec : SysSpec SyscallEffect} {i : SyscallInput} {m : Model}
    (H : spec i m .unmodeled) :
    record_copyins reads spec i m .unmodeled :=
  Or.inl H

/-- The same transformation, lifted to a whole outcome (so it can be used to
    state `record_copyins_outcome` without knowing which branch fired). -/
def outcome_copyins (reads : List (word × Nat))
    (o : Outcome SyscallEffect Model event) : Outcome SyscallEffect Model event :=
  match o with
  | .ok eff m evs => .ok (with_copyins (reads ++ eff.eff_copyins) eff) m evs
  | .unmodeled => .unmodeled

theorem record_copyins_outcome {reads : List (word × Nat)}
    {spec : SysSpec SyscallEffect} {i : SyscallInput} {m : Model}
    {o : Outcome SyscallEffect Model event}
    (H : spec i m o) :
    record_copyins reads spec i m (outcome_copyins reads o) := by
  cases o with
  | ok eff m' evs => exact record_copyins_ok H
  | unmodeled => exact record_copyins_unmodeled H

/-! ## Failure injection -/

/-- An errno drawn from a syscall's realistic injectable set.  Failure
    injection is constrained PER SYSCALL: a failure branch may return
    only errnos the call can produce on a real kernel (per its man
    page), never an arbitrary value in 1..4095 — e.g. mmap can never
    fail with -EBADF.  Each syscall with an injectable failure carries
    its own small list below. -/
def errno_from (es : List Int) : SysSpec Int :=
  choose (fun e => e ∈ es)

/-! ## Word tests and the ABI narrowing

    These are the conversions the C prototypes in `include/linux/syscalls.h`
    perform on the 64-bit argument registers.  They are applied at the ABI
    boundary — once, in the dispatcher (`Sys.SyscallTable.spec_table`) —
    so every per-syscall spec receives an argument that is already narrowed.
-/

/-- Word-against-zero test, used all over the dispatcher. -/
def w_is0 (w : word) : Bool := bv_eqb w (BitVec.ofInt 64 0)

/-- A positive count is not zero — the fact every arm that has to tell a
    real transfer from an empty one reaches for. -/
theorem w_is0_pos (w : word) (H : 0 < w.toNat) : w_is0 w = false := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at H
    simp at H
  unfold w_is0
  rw [show BitVec.ofInt 64 0 = (0 : word) from by decide]
  exact beq_eq_false_iff_ne.mpr hne

/-- …and the converse, which is the direction an ARM reads it in: past
    a `w_is0` gate the length is positive, and a spec that goes on to
    record a range derived from it is recording real bytes. -/
theorem w_is0_false_pos (w : word) (H : w_is0 w = false) : 0 < w.toNat := by
  unfold w_is0 at H
  rw [show BitVec.ofInt 64 0 = (0 : word) from by decide] at H
  have hne : w ≠ 0 := beq_eq_false_iff_ne.mp H
  rcases Nat.eq_zero_or_pos w.toNat with h0 | hpos
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
  · exact hpos

/-- The low 32 bits of a register, zero-extended back into a `word` —
    the C conversion an `int` / `unsigned int` syscall parameter
    performs on the 64-bit register it is passed.

    NAME: deliberately NOT `low32`.  `Riscv.Sem.low32` already denotes
    the ISA's narrowing (`bv_extract 0 32 : word -> bv 32`, the low half
    as a 32-bit value), and files such as `Common/FileSim.v` import both
    this module and `Riscv.Sem`; one token for two different types would
    be a reading hazard in exactly the files an auditor must read.  The
    two agree up to the zero-extension this one performs:
    `abi_low32 w = zext 64 (Riscv.Sem.low32 w)`.  It is spelled out here
    rather than defined that way so the syscall layer does not depend on
    the ISA layer.

  this tree spells the same value as `BitVec.ofNat 64 (w.toNat % 2 ^ 32)` so the
  proofs use `Nat.mod_eq_of_lt` rather than an `Int`/`Nat` cast lemma. The result is
  identical (`Nat.mod_eq_of_lt` on the cast, and `Z_to_bv n k = BitVec.ofNat n k` for
  `k: Nat`). -/
def abi_low32 (w : word) : word := BitVec.ofNat 64 (w.toNat % 2 ^ 32)

/-- THE FILE DESCRIPTOR ARGUMENT IS 32 BITS.  An fd reaches the kernel
    in a full 64-bit register, but every syscall entry point declares it
    `unsigned int` / `int`, so the high half is DISCARDED before the fd
    table is ever consulted (fs/read_write.c, fs/open.c, fs/file.c,
    fs/fcntl.c):

      read/write   `SYSCALL_DEFINE3(read, unsigned int, fd, ...)`
      close        `SYSCALL_DEFINE1(close, unsigned int, fd)`
      lseek        `SYSCALL_DEFINE3(lseek, unsigned int, fd, ...)`
      readv/writev declared `unsigned long, fd`, but resolved through
                   `fdget_pos(unsigned int fd)` — truncated all the same
      openat       `SYSCALL_DEFINE4(openat, int, dfd, ...)`
      ioctl        `SYSCALL_DEFINE3(ioctl, unsigned int, fd, ...)`
      fcntl        `SYSCALL_DEFINE3(fcntl, unsigned int, fd, ...)`
      readlinkat   `SYSCALL_DEFINE4(readlinkat, int, dfd, ...)`
      dup          `SYSCALL_DEFINE1(dup, unsigned int, fildes)`
      dup3         `SYSCALL_DEFINE3(dup3, unsigned int, oldfd,
                   unsigned int, newfd, int, flags)` — BOTH fds

    So `write(2^32 + 1, buf, n)` really writes to STDOUT, and
    `close(2^32)` really closes stdin — matching a bare 64-bit compare
    against the fd table would instead have reported -EBADF, admitting a
    behavior no kernel produces and missing the one it does.

    `fd32` is that conversion.  ZERO-extension (rather than sign-) is
    faithful here even though `int` fds are signed: the model's fd table
    only ever holds fds <= 4096 (`State.alloc_fd`), so a low half at or
    above 2^31 — a negative `int` — matches no entry either way and is
    -EBADF, exactly as on Linux.

    The truncation is applied ONCE, in `syscall_spec` (and mirrored in
    `Checks/ExecutableSpecs.check_syscall` and
    `Checks/Progress.syscall_spec_witness`), at the ABI boundary where
    the kernel performs it; each per-syscall spec below therefore
    receives an fd that is already 32-bit. -/
def fd32 (fd : word) : word := abi_low32 fd

/-- `fd32` is the identity on every fd the model can hold or hand out
    (all of them below 2^32), which is what proofs about concrete fds
    need to see through the dispatcher's truncation. -/
theorem fd32_id (fd : word) (H : fd.toNat < 2 ^ 32) : fd32 fd = fd := by
  unfold fd32 abi_low32
  rw [Nat.mod_eq_of_lt H]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fd.isLt]

/-- The bound the per-binary proofs already carry for the fds they hold
    (below 2^31, so an fd is never an error-encoded return — see
    `Checks/Checks.Sys.Prelude.errno_ret_in_fd`) is more than enough. -/
theorem fd32_lt31 (fd : word) (H : fd.toNat < 2 ^ 31) : fd32 fd = fd :=
  fd32_id fd (by omega)

/-- lseek's origin selector is `unsigned int` too
    (`SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset,
    unsigned int, whence)`, fs/read_write.c), so the kernel compares
    only the low half against SEEK_SET/SEEK_CUR/SEEK_END:
    `lseek(fd, 0, 2^32 | SEEK_END)` really seeks to end-of-file.
    Matching the full register would demand -EINVAL — a return no
    kernel produces. -/
def whence32 (whence : word) : word := abi_low32 whence

/-- ioctl's request is `unsigned int` as well
    (`SYSCALL_DEFINE3(ioctl, unsigned int, fd, unsigned int, cmd,
    unsigned long, arg)`, fs/ioctl.c), and so is fcntl's command
    (`SYSCALL_DEFINE3(fcntl, unsigned int, fd, unsigned int, cmd,
    unsigned long, arg)`, fs/fcntl.c) and flock's operation
    (`SYSCALL_DEFINE2(flock, unsigned int, fd, unsigned int, cmd)`,
    fs/locks.c, Linux v6.18.46, commit 1f99e9ab748f).  All three share
    this conversion; the `arg` beside the first two is `unsigned long`
    and is NOT truncated.

    For flock the narrowing is not cosmetic, because its command word is
    tested BITWISE rather than by equality: `cmd & LOCK_MAND` and
    `cmd & ~LOCK_NB` both read a 32-bit value, so a caller that leaves
    bit 37 set gets Linux's answer for the low half rather than the
    -EINVAL a full-register test would invent. -/
def cmd32 (cmd : word) : word := abi_low32 cmd

/-- `clockid_t` is an `int` — `typedef int __kernel_clockid_t`
    (include/uapi/asm-generic/posix_types.h), reaching the syscall as
    `typedef __kernel_clockid_t clockid_t` (include/linux/types.h) —
    and `SYSCALL_DEFINE2`'s `__SC_CAST` casts the register to it
    (`SYSCALL_DEFINE2(clock_gettime, const clockid_t, which_clock,
    struct __kernel_timespec __user *, tp)`,
    kernel/time/posix-timers.c; the body is identical at v6.10-v6.15).
    So the kernel compares only the low half of the register.  Same
    treatment as `fd32`/`whence32`/`cmd32`; zero-extension is faithful
    because every id the model interprets is a small positive constant,
    and a low half at or above 2^31 — a negative `clockid_t` — matches
    no modeled id either way and declines.  What is being declined there
    is wider than it looks: `clockid_to_kclock`
    (kernel/time/posix-timers.c, v6.10-v6.15) sends a negative id to
    the dynamic-posix-clock (clockfd) handler ONLY when
    `(id & CLOCKFD_MASK) == CLOCKFD` — both constants in
    include/linux/posix-timers_types.h — i.e. `id & 7 == 3`; every OTHER
    negative id goes to `clock_posix_cpu`, the per-process and
    per-thread CPU clocks, several of which SUCCEED and write a
    timespec — `clock_gettime(-6, tp)` is `MAKE_PROCESS_CPUCLOCK(0,
    CPUCLOCK_SCHED)` and returns 0 on Linux.  So the negative half of
    the id space is mostly a live clock family the model does not
    cover, not a uniformly failing one, and declining it is fail-closed
    rather than agreement with an `-EINVAL`.  Applied ONCE, in
    `Sys.SyscallTable.spec_table`, at the ABI boundary where the kernel
    performs it; `clock_gettime_spec` receives an already-truncated
    id. -/
def clockid32 (clkid : word) : word := abi_low32 clkid

/-- `setsockopt`'s `level` and `optlen`, `getsockopt`'s `level` and
    `shutdown`'s `how` are each a plain `int` in their `SYSCALL_DEFINE`
    (net/socket.c), so only the low 32 bits reach the kernel's own
    tests, exactly as for `fd`.  The tests those four arguments feed
    are all EQUALITY or SIGN tests against small constants, and this
    model states them over `bv_unsigned` of the low half: "negative as
    an `int`" is "at least 2^31", and "one of 0/1/2" is membership in
    the low half.  Truncating rather than comparing the whole register
    is the SAME correction `whence32` records — a caller that leaves
    garbage in the high half of `a4` gets Linux's answer, not an
    -EINVAL no kernel produces. -/
def int32 (w : word) : word := abi_low32 w

/-- A credential id argument is 32 BITS.  Every credential entry point
    declares its arguments `uid_t` / `gid_t`
    (`SYSCALL_DEFINE1(setuid, uid_t, uid)` and its siblings,
    kernel/sys.c), so the high half of the 64-bit register is discarded
    before the kernel looks at the value — the reason `setuid(2^32)`
    sets the uid to 0 rather than failing.  Applied ONCE, in the
    dispatcher, exactly like `fd32`: the specs take ids already
    narrowed, so no arm can compare a 64-bit register against
    `Uapi.ID_MINUS_ONE` by accident. -/
def uid32 (u : word) : word := abi_low32 u

/-- A syscall flag word declared `int` rather than `unsigned` — dup3's
    (`SYSCALL_DEFINE3(dup3, unsigned int, oldfd, unsigned int, newfd,
    int, flags)`, fs/file.c), unlinkat's
    (`SYSCALL_DEFINE3(unlinkat, int, dfd, const char __user *, pathname,
    int, flag)`, fs/namei.c) and most of the older *at() calls',
    newfstatat's included (`SYSCALL_DEFINE4(newfstatat, int, dfd,
    const char __user *, filename, struct stat __user *, statbuf,
    int, flag)`, fs/stat.c) — so the kernel never sees its high half,
    and the high half is discarded before any bit of it is tested: for
    unlinkat, before the `flag & ~AT_REMOVEDIR` test.

    This is a convention of the older syscalls, not a rule, and not one
    dup3 introduced: setxattr (5), lsetxattr (6), fsetxattr (7),
    eventfd2 (19) and epoll_create1 (20) all precede dup3 (24) with an
    `int` flags word, while the newer additions declare theirs unsigned
    — statx takes `unsigned`, and renameat2, fchmodat2, open_tree,
    move_mount, statmount and listmount take `unsigned int`.  The
    truncation is what matters here and it is identical either way.

    This one is applied in BOTH places, unlike `fd32`/`whence32`/`cmd32`,
    which are only ever applied at the dispatcher.  `Sys.SyscallTable`
    narrows at the arm for `newfstatat` and `timerfd_create`, whose flag
    words are read by nothing else; `Fs.File.dup3_flags_ok` and
    `Sys.Fs.Namei`'s flag tests apply it themselves instead.  For dup3
    that is because it is the only thing separating the model from a
    full-width flag test there — see that definition. -/
def flag32 (flag : word) : word := abi_low32 flag

/-- Linux's `int` parameter `n`, as the kernel reads it.  The register
    is 64 bits wide but `SYSCALL_DEFINE6(pselect6, int, n, ...)` casts it
    to `int` before any comparison, so the high half is discarded and the
    low half is read as two's complement (see `fd32` for the same rule on
    file descriptors). -/
def nfds32 (n : word) : word := abi_low32 n

/-- ppoll's `nfds` is `unsigned int`
    (`SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned int,
    nfds, ...)`, fs/select.c), so the same 32-bit truncation applies and
    the result is read UNSIGNED.  Kept apart from `nfds32` above rather
    than shared with it: the two words are narrowed identically and read
    OPPOSITELY, and `do_sys_poll`'s first test — `nfds` against
    `rlimit(RLIMIT_NOFILE)` — is an unsigned comparison, so a register
    whose low half has bit 31 set is a huge count and not a negative
    one. -/
def unfds32 (nfds : word) : word := abi_low32 nfds

def nfds_signed (n32 : word) : Int :=
  let v : Int := (n32.toNat : Int)
  if v < 2 ^ 31 then v else v - 2 ^ 32

/-- `socket`, `bind`, `listen`, `accept4` all take `int` arguments, and
    their range checks are SIGNED (`family < 0`, `protocol < 0`,
    `addrlen < 0`).  `abi_low32` gives the unsigned low 32 bits; this
    reads the same bits as a signed `int`.

    THE LOW HALF IS COMPARED AS A `Nat` BEFORE IT IS READ AS AN `Int`,
    and that shape is load-bearing rather than cosmetic.  Written the
    other way round — `let u : Int := ((abi_low32 w).toNat : Int); if u <
    2 ^ 31 then u else u - 2 ^ 32`, which is the same function — the
    guard is `Int.decLt` on an `Int.ofNat` of a `BitVec.toNat`, and its
    `whnf` does not terminate under a unifier: the wall `Checks/Cases`'
    `sint32` note measures.  A `Nat` comparison reduces, so this spelling
    can still be unfolded by `simp`/`rw`/`rfl` wherever a checker is
    evaluated.  (`nfds_signed` above keeps the old shape: nothing
    reduces it at a symbolic argument.) -/
def sint32 (w : word) : Int :=
  let n : Nat := (abi_low32 w).toNat
  if n < 2 ^ 31 then (n : Int) else (n : Int) - 2 ^ 32

/-- rt_sigprocmask's `how` is `int`
    (`SYSCALL_DEFINE4(rt_sigprocmask, int, how, sigset_t __user *, nset,
    sigset_t __user *, oset, size_t, sigsetsize)`, kernel/signal.c), so
    `sigprocmask`'s `switch (how)` compares only the low half against
    SIG_BLOCK, SIG_UNBLOCK and SIG_SETMASK.  Its `sigsetsize` is
    `size_t` and is deliberately NOT narrowed here: it is compared
    full-width, so a register whose low half is 8 is still the wrong
    size. -/
def how32 (how : word) : word := abi_low32 how

/-- wait4's `upid` is a `pid_t`, which is an `int`
    (`SYSCALL_DEFINE4(wait4, pid_t, upid, int __user *, stat_addr, int,
    options, struct rusage __user *, ru)`, kernel/exit.c), so the kernel
    compares only the low half of the register — exactly as `fd32` and
    `whence32` describe for their own arguments.  Applied ONCE, in the
    dispatcher's arm. -/
def pid32 (upid : word) : word := abi_low32 upid

/-- wait4's `options` is an `int` in the same prototype, and the
    kernel's validation is a bitwise test on it, so the high half is
    discarded before any bit is read. -/
def waitopts32 (options : word) : word := abi_low32 options

/-- pipe2's flag word is an `int`
    (`SYSCALL_DEFINE2(pipe2, int __user *, fildes, int, flags)`,
    fs/pipe.c), so only its low 32 bits reach the mask test. -/
def pipe_flags32 (flags : word) : word := abi_low32 flags

/-! ## Sanity checks on the computable helpers

  these pin the two things a transcription slip would break — the ABI narrowing of a
  negative `int32` argument, and the errno return encoding. -/

/-- The narrowing keeps the low 32 bits of an all-ones register. -/
example : abi_low32 (BitVec.ofInt 64 (-1)) = 4294967295 := by decide

/-- `write(2^32 + 1, ...)` really names fd 1: the high half is gone. -/
example : fd32 (BitVec.ofInt 64 4294967297) = 1 := by decide

/-- `-1` as an `int` argument is still `-1` once read back signed. -/
example : sint32 (BitVec.ofInt 64 (-1)) = -1 := by decide

/-- So is `-100` (AT_FDCWD), whose low half is `0xffffff9c`. -/
example : sint32 (BitVec.ofInt 64 (-100)) = -100 := by decide

/-- A small non-negative `int` is unchanged. -/
example : sint32 5 = 5 := by decide

/-- The signed `nfds` read is the same two's-complement reading as
    `sint32`, and, unlike `unfds32`, a bit-31-set low half is negative. -/
example : nfds_signed (unfds32 (BitVec.ofInt 64 (-1))) = -1 := by decide

example : nfds_signed 16 = 16 := by decide

/-- The sign boundary: a low half with bit 31 set reads as `-2^31`. -/
example : sint32 (BitVec.ofInt 64 2147483648) = -2147483648 := by decide

example : nfds_signed (unfds32 (BitVec.ofInt 64 2147483648)) = -2147483648 := by
  decide

/-- …while the UNSIGNED reader of the same register keeps it huge — the
    reason `unfds32` is kept apart from `nfds32`. -/
example : (unfds32 (BitVec.ofInt 64 2147483648)).toNat = 2147483648 := by
  decide

/-- The errno return encoding: `-EBADF` in two's complement. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide

example : errno_ret EBADF = 18446744073709551607 := by decide

/-- `err_ret` really returns that word and writes no memory. -/
example : ret_only (errno_ret ENOENT) = pure (mkEffect (errno_ret ENOENT) [] []) := rfl

/-- The zero test itself. -/
example : w_is0 (BitVec.ofInt 64 0) = true := by decide

example : w_is0 1 = false := by decide

end LinuxSem.LinuxProcessSem.Sys.Syscall
