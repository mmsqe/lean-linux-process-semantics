/-
  * LinuxProcessSem.Sys.Uapi — the constants the userspace ABI fixes

  Every other file under `Sys/` answers to one kernel SOURCE file; this
  one answers to a kernel HEADER, `include/uapi/`, and holds what the
  specs share rather than any one syscall's behaviour.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions every
  spec here follows.

  **`Sys/Syscall.lean` defines both** (`abi_low32`, `fd32`).  The local
  `abi_low32` below is now a transparent alias to the `Sys.Syscall` one (the
  two are definitionally equal), so this file no longer restates the
  truncation; `fd32` stays a local definition built on that alias, exactly as
  `Sys.Syscall.fd32` is built on the `Sys.Syscall` copy.

  `stat_set_size_size_ok`
  uses `bytes_le_to_Z_of_le_bytes` from `BvBase.lean`.  That general lemma
  now IS in `BvBase.lean` (proved there from the `Nat` byte recursion);
  this file still proves the one instance it needs —
  `bytes_le_to_Nat_Z_to_le_bytes`, in the `struct stat` section below,
  over the `Nat`-valued round trip, because that is the form the local
  proof consumes.  See the note there.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.Sys.Syscall

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem.Fs

namespace LinuxSem.LinuxProcessSem.Sys.Uapi

/-! ## `Z.lor` and `Z.land` over `Int`

    Lean's core `Int` library has no bitwise and/or (only complement and
  the two shifts), while the original uses `Z.lor` and `Z.land` on
    the non-negative ABI words below.  Both are defined through `Nat`,
    which agrees with the `Z` versions whenever the operands are
    non-negative — and every use site here is either a literal constant
    or a value read out of delivered bytes, so they always are. -/

/--  `Z.lor` (bitwise or), through `Nat`. -/
def z_lor (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)

/--  `Z.land` (bitwise and), through `Nat`. -/
def z_land (a b : Int) : Int := ((a.toNat &&& b.toNat : Nat) : Int)

/-! ## `Z.ldiff` over `Int`

    `Z.ldiff a b` is the bitwise difference `a land lnot b` — `a` with
  every bit of `b` cleared.  It is the third of the `Z` bit operations
  used on the ABI words here, next to `Z.lor` and `Z.land` above; Lean's
  core `Int` library has none of them (only complement and the two
  shifts), so, like those two, it is defined through `Nat`, which agrees
  with the `Z` version whenever the operands are non-negative.  They
  always are wherever it is used: a `word` read unsigned (`toNat`,
  `abi_low32`, `flag32`, `cmd32`) or a literal ABI constant such as
  `O_CLOEXEC`.

    On such operands "clear the bits of `b` from `a`" is integer
  subtraction of their intersection, so the body is `a - (a &&& b)`
  rather than a spelled-out complement: the complement would have to be
  taken at a fixed width (`2^64 - 1 - b`), and `a - z_land a b` needs no
  width to be chosen at all, being exact as long as both arguments are
  non-negative. -/

/--  `Z.ldiff` (bitwise "`a` and not `b`"), through `Nat`, as
    `a - (a &&& b)`; exact on the non-negative ABI operands. -/
def z_ldiff (a b : Int) : Int := a - z_land a b

/-! ## File-open flags and the path/file-descriptor ABI words -/

def O_WRONLY : Int := 1
/-- `O_RDWR` has TWO readers, and they arrive at it from opposite ends.

    It is the access mode `Open.rdwr_open_word` admits, minting a
    `State.FdFileRW`; and, separately, it is the WHOLE of a socket's
    `f_flags`.  net/socket.c `sock_alloc_file` builds the file with
    `alloc_file_pseudo(..., O_RDWR | (flags & O_NONBLOCK), &socket_file_ops)`,
    so a socket created without SOCK_NONBLOCK has exactly this word and
    nothing else — no O_LARGEFILE, which the open SYSCALL ENTRY POINTS
    add with `force_o_largefile()` and which nothing on the socket
    creation path does.  `Fcntl.socket_f_flags` is that derivation, and
    it is a fact about how a SOCKET is created rather than about the
    constant, so the open arms below cannot disturb it. -/
def O_RDWR : Int := 2
def O_CREAT : Int := 64
def O_EXCL : Int := 128
def O_TRUNC : Int := 512
def O_CLOEXEC : Int := 524288
/-- musl's syscall layer ORs O_LARGEFILE into EVERY open it issues
    (src/internal/syscall.h); it is meaningless on a 64-bit ABI, so it
    is accepted and ignored like O_CLOEXEC. -/
def O_LARGEFILE : Int := 32768

/-- O_NONBLOCK: 2048.  riscv64 takes the asm-generic ABI
    (include/uapi/asm-generic/fcntl.h), where the value is unchanged
    from v4.9 through v6.17 and O_NDELAY is an alias of it throughout.
    riscv supplies no asm/fcntl.h of its own to override it — checked at
    v5.10 and v6.17, and only meaningful from v4.15, which is where
    arch/riscv first exists.  Accepted and IGNORED like O_CLOEXEC and
    O_LARGEFILE, but for a reason that is a property of this model's
    FILE SYSTEM rather than of the flag, so it is spelled out here and
    has to be re-checked whenever that file system grows.
    `Open.open_ignored_flags` is the mask that carries it.

    WHAT THE KERNEL DOES WITH IT.  It reaches `f_flags` and stays there.
    Plain openat masks its flag word with VALID_OPEN_FLAGS
    (`build_open_how`, fs/open.c) and openat2 rejects anything outside
    that set instead (`build_open_flags`); O_NONBLOCK is in the set
    either way.  From v5.6, where openat2 split those two, the only bits
    `build_open_flags` strips are O_CLOEXEC and, on the older branches,
    the kernel-internal FMODE_NONOTIFY.  That is scoped to v5.6 and
    later on purpose: at v5.4 `build_open_flags` also does
    `flags &= VALID_OPEN_FLAGS` itself, and its O_PATH arm does
    `flags &= O_DIRECTORY | O_NOFOLLOW | O_PATH`, which DOES drop
    O_NONBLOCK; v4.9 has no VALID_OPEN_FLAGS at all.  Then
    `do_dentry_open` clears O_CREAT, O_EXCL, O_NOCTTY and O_TRUNC from
    `f_flags` once the file's `->open` has run, and O_NONBLOCK is not in
    that list, so the description really does record it.  That clearing
    line is identical at v4.9, v5.10, v6.1, v6.6 and v6.17, and on
    stable 6.6.y and 6.1.y.

    WHY RECORDING IT COSTS THIS MODEL NOTHING.  Three ways a program
    could tell, all closed:

    - READ THE FLAG WORD BACK, which means fcntl(F_GETFL).  fcntl (25)
      is modeled and F_GETFL IS one of the commands it answers — but
      only on the fd kind whose flag word the model can derive, which is
      `State.FdSocket` (`Fcntl.getfl_f_flags`).  `Open.openat_spec` never
      mints one: the fd this bullet is about is an `FdFile`, `FdFileW`,
      `FdFileA`, `FdFileRW`, `FdDir`, `FdDevNull` or `FdUrandom`, and F_GETFL
      declines on every one of them FOR THE
      REASON THIS BULLET IS ABOUT — the ignored bit is part of the answer, so the
      read fails closed inside the spec rather than at the dispatch.
      The two facts moved together on purpose: `Fcntl.getfl_f_flags`
      enumerates its fd kinds, so recording O_NONBLOCK on an `FdEntry`
      is what would let the file kinds be answered, and it is the same
      change that would retire this bullet.

    - THE OPEN ITSELF ANSWERS -EAGAIN.  `do_dentry_open` calls
      `break_lease` with the UNSTRIPPED `f_flags`, before the clearing
      line above, and `__break_lease` (fs/locks.c) answers -EWOULDBLOCK
      — which is EAGAIN — when `mode & O_NONBLOCK`.  Unreachable here
      rather than merely unlikely: `break_lease` (include/linux/filelock.h)
      returns 0 outright unless the inode already carries a lease, a
      lease is taken with fcntl(F_SETLEASE), one of the commands
      `Fcntl.fcntl_spec` declines, and the model runs ONE process, so
      nothing else can hold one either.  Checked at v4.9, v5.10, v6.1,
      v6.6 and v6.17: the call precedes the clearing line and passes
      `f_flags` at all five, and the `list_empty` bail sits directly
      above the O_NONBLOCK test in `__break_lease`.  The inode helper
      is spelled `locks_inode` up to v6.1 and `file_inode` from v6.6.

    - A TRANSFER ANSWERS -EAGAIN, which needs an object that could have
      blocked.  Every path `Open.openat_spec` resolves here is a regular
      file in the interpreted file system or one of the two directory
      references "." and ".." (`Fs.Open.path_is_dirref`) — never a pipe,
      a socket, a terminal or any other character device.  On a regular
      file every -EAGAIN in `generic_file_read_iter` and
      `filemap_get_pages` (mm/filemap.c) is conditioned on IOCB_NOWAIT,
      IOCB_NOIO or, from v6.17, IOCB_WAITQ; those bits come only from
      RWF_NOWAIT via `kiocb_set_rw_flags`, which is defined in
      include/linux/fs.h — fs/read_write.c holds its call site and no
      definition — and which read(2) and write(2) never pass; and
      `iocb_flags` (include/linux/fs.h) maps only O_APPEND, O_DIRECT,
      O_DSYNC and __O_SYNC, not O_NONBLOCK.  That mapping has held from
      v4.19 through v6.17, mainline and stable alike.

      ONE EXCEPTION, ON BRANCHES BEFORE v5.15.  There a regular-file
      read(2)/write(2) COULD answer -EAGAIN from `f_flags` alone, nowhere
      near mm/filemap.c: `rw_verify_area` (fs/read_write.c) called
      `locks_mandatory_area` (then in fs/locks.c), which reads
      `filp->f_flags & O_NONBLOCK` directly and lets `posix_lock_inode`
      return -EAGAIN without FL_SLEEP.  It needed
      CONFIG_MANDATORY_FILE_LOCKING and an -o mand mount.  Mandatory
      locking was removed at v5.15: fs/locks.c defines `locks_mandatory_area`
      at v4.9, v4.19, v5.4, v5.10 and v5.14, and not at v5.15, v6.1, v6.17
      or v6.18.46.  So the paragraph above is a claim about
      v5.15 and later, not about every branch this file names elsewhere.

    THAT IS CONDITIONAL ON THE FILE SYSTEM KEEPING THAT SHAPE.  Should
    `Open.openat_spec` ever resolve a path to a FIFO, a socket or a
    character device, O_NONBLOCK stops being ignorable — on a FIFO it
    decides whether the open itself blocks or answers -ENXIO — and
    belongs back OUT of `Open.open_ignored_flags`, not widened further.
    The same trigger governs O_NOCTTY's argument in
    `Open.modeled_open_flags`: 9p's `dotl_oflag_map` forwards BOTH flags
    to the server, so a file system growing past regular files and "."
    puts the two back in question together. -/
def O_NONBLOCK : Int := 2048

/-- O_DIRECTORY: 0200000.  riscv64 takes the asm-generic ABI
    (include/uapi/asm-generic/fcntl.h, Linux v6.18.46) and supplies no
    asm/fcntl.h of its own to override the value.

    THE ONE OPEN FLAG THIS MODEL INTERPRETS BEYOND THE ACCESS MODE, and
    it cannot be ignored the way `Open.open_ignored_flags`'s three bits
    are: it changes which answers the call gives.  The bit does not stay
    in `f_flags` to be read back later.  `build_open_flags` (fs/open.c)
    turns it into the LOOKUP_DIRECTORY bit of the lookup flags, and
    `do_open` (fs/namei.c) then answers -ENOTDIR for a resolved dentry
    that `d_can_lookup` (include/linux/dcache.h) refuses.

    WHERE THAT TEST SITS is what makes the errno independent of what the
    name turned out to be: inside `do_open` (fs/namei.c), after the
    O_CREAT block and before `may_open` (fs/namei.c), which is itself
    before `vfs_open` (fs/open.c).  So a FIFO whose open would otherwise
    block for a peer, a device node whose file operations would run, and
    a plain file all answer -ENOTDIR without either of the two later
    steps being reached.  Linux v6.18.46. -/
def O_DIRECTORY : Int := 65536

/-! ## The ABI words whose low half the dispatcher reads -/

/-- The low 32 bits of a register, zero-extended back into a `word` —
    the C conversion an `int` / `unsigned int` syscall parameter
    performs on the 64-bit register it is passed.

  This is `LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32`, as a transparent
  alias: the `Sys.Syscall` body is `BitVec.ofNat 64 (w.toNat % 2 ^ 32)`, which
  is definitionally the `ofInt`/`Nat` form this file used to spell out. -/
abbrev abi_low32 (w : word) : word := LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32 w

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

  `Sys/Syscall.lean` now has the same definition, and this copy can be replaced by
  it. -/
def fd32 (fd : word) : word := abi_low32 fd

def AT_FDCWD : word := BitVec.ofInt 64 (-100)   -- -100 in two's complement

/-- AT_FDCWD as it reaches openat's dirfd test, i.e. after the `int dfd`
    truncation the dispatcher applies (`Syscall.fd32`): the low 32 bits of -100.
    A program passes AT_FDCWD in a register sign-extended to 64 bits
    (`AT_FDCWD` itself), and the kernel then compares only the low half,
    so `openat(2^32 - 100, ...)` names the working directory too. -/
def AT_FDCWD32 : word := fd32 AT_FDCWD

/-- `(uid_t)-1`, after the `Syscall.uid32` narrowing.  No process can
    hold it — `make_kuid` maps it to `INVALID_UID`
    (include/linux/uidgid.h) and `Run.valid_id` excludes it — so
    `setuid` and `setgid` reject it with -EINVAL, and `setresuid` and
    `setresgid` read it as "leave this id alone". -/
def ID_MINUS_ONE : word := BitVec.ofInt 64 4294967295

/-- AT_SYMLINK_NOFOLLOW, the flag that turns `stat` into `lstat`
    (include/uapi/linux/fcntl.h). -/
def AT_SYMLINK_NOFOLLOW : Int := 256

/-- AT_EACCESS (0x200), the flag that asks `faccessat2` to answer with
    the EFFECTIVE ids rather than the real ones
    (include/uapi/linux/fcntl.h).  It is read once, by
    `access_need_override_creds`, which returns false outright when it
    is set and so skips the `access_override_creds` that copies uid/gid
    over fsuid/fsgid (fs/open.c).  Under F_OK the choice is
    unobservable, which is what lets `Fs.Open.faccessat2_spec` answer
    with it set; `Fs.Open.faccessat2_spec` carries the argument. -/
def AT_EACCESS : Int := 512

/-- AT_EMPTY_PATH (0x1000), the flag that makes `getname_flags` accept
    an empty pathname and resolve the dirfd itself
    (include/uapi/linux/fcntl.h).  `do_faccessat` turns it into
    LOOKUP_EMPTY (fs/open.c).  It is one of the three flags
    `faccessat2` accepts, so it is not an -EINVAL, and
    `Fs.Open.modeled_access_flags` declines it rather than guessing. -/
def AT_EMPTY_PATH : Int := 4096

/-- `S_IRWXO` (0o7): the mask `do_faccessat` validates its `mode`
    against, and the reason the R_OK/W_OK/X_OK values are the low three
    bits.  Linux passes `mode` STRAIGHT THROUGH as a permission mask —
    `inode_permission(..., mode | MAY_ACCESS)` — which works only
    because R_OK, W_OK and X_OK have the same numeric values as
    MAY_READ, MAY_WRITE and MAY_EXEC (4/2/1, include/linux/fs.h).  A
    `mode` with any bit outside this mask is a deterministic -EINVAL,
    decided by the FIRST statement of `do_faccessat`, before the flag
    word, before the creds and before the pathname is fetched — see
    `Fs.Open.faccessat_spec` (Linux include/uapi/linux/stat.h; the value
    is unchanged across every branch this file names). -/
def S_IRWXO : Int := 7

/-- "." (the working directory), one of the two paths that name a
    directory without a lookup.  The other is `Fs.Namei.dotdot_path`;
    `Fs.Open.path_is_dirref` is the pair, and its comment says why they
    get the same answers.  The interpreted fs has no directory
    structure, so no path OTHER than those two resolves to a directory.

    It sits here rather than with a syscall because more than one spec
    resolves it: `openat` opens it as a directory fd, `newfstatat`
    declines it for want of metadata, and no file under `Sys/` imports
    another. -/
def dot_path : path := [BitVec.ofInt 8 46]

/-- "/dev/null", the one DEVICE path the model answers.  It sits here
    for the reason `dot_path` does: `Fs.Open.openat_devnull_spec` opens
    it, `Fs.Stat.fstat_devnull_spec` keys the descriptor's stat pin
    under it, and no file under `Sys/` imports the other.  The
    assumption the name rests on — the image's /dev/null is the null
    device, character major 1 minor 3 — is stated once, at the openat
    arm. -/
def devnull_path : path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 100, BitVec.ofInt 8 101, BitVec.ofInt 8 118,
   BitVec.ofInt 8 47, BitVec.ofInt 8 110, BitVec.ofInt 8 117, BitVec.ofInt 8 108,
   BitVec.ofInt 8 108]

/-- "/dev/urandom", the second device path the model answers, here for
    the reason `devnull_path` is: `Fs.Open.openat_urandom_spec` opens
    it and `Fs.Stat.fstat_urandom_spec` keys the descriptor's stat pin
    under it.  The assumption the name rests on — the image's
    /dev/urandom is the random device, character major 1 minor 9 — is
    stated once, at the openat arm. -/
def urandom_path : path :=
  [BitVec.ofInt 8 47, BitVec.ofInt 8 100, BitVec.ofInt 8 101, BitVec.ofInt 8 118,
   BitVec.ofInt 8 47, BitVec.ofInt 8 117, BitVec.ofInt 8 114, BitVec.ofInt 8 97,
   BitVec.ofInt 8 110, BitVec.ofInt 8 100, BitVec.ofInt 8 111, BitVec.ofInt 8 109]

/-! ## Sockets: constants, argument decoding, and the trace channel -/

/-- Address families and socket types.  riscv64 has no `asm/socket.h` and
    no `asm/errno.h` of its own — arch/riscv/include/uapi/asm/Kbuild
    generates only unistd_32.h and unistd_64.h — so every constant here
    is the asm-generic one, at v6.12. -/
def AF_UNSPEC : Int := 0
def AF_INET : Int := 2
def NPROTO : Int := 46    -- = AF_MAX, include/linux/socket.h

def SOCK_STREAM : Int := 1
def SOCK_DGRAM : Int := 2
def SOCK_RAW : Int := 3
def SOCK_SEQPACKET : Int := 5
def SOCK_DCCP : Int := 6
def SOCK_PACKET : Int := 10
def SOCK_MAX : Int := 11  -- = SOCK_PACKET + 1, include/linux/net.h

/-- `SOCK_TYPE_MASK` is 0xf: the low four bits of `type` are the socket
    type and the rest are flags (include/linux/net.h). -/
def SOCK_TYPE_MASK : Int := 15

/-- `SOCK_CLOEXEC` and `SOCK_NONBLOCK` are ARCH-DEPENDENT in general —
    include/linux/net.h defines them only `#ifndef ARCH_HAS_SOCKET_TYPES`,
    and mips/parisc/sparc/alpha override them.  riscv64 does not, and has
    no `asm/fcntl.h` either, so both fall through to the asm-generic
    O_ flags: `SOCK_CLOEXEC = O_CLOEXEC = 02000000` and
    `SOCK_NONBLOCK = O_NONBLOCK = 04000`. -/
def SOCK_CLOEXEC : Int := 524288   -- 0o2000000
def SOCK_NONBLOCK : Int := 2048    -- 0o4000

/-- `IPPROTO_MAX` is the TRAILING ENUMERATOR of the `IPPROTO_*` enum in
    include/uapi/linux/in.h, not a round number: the last named member is
    `IPPROTO_MPTCP = 262`, so `IPPROTO_MAX` is 263.  It was 256 only up
    to v5.5; `IPPROTO_MPTCP` arrived in v5.6 and the value has been 263
    from v5.6 through v6.12.  Getting this wrong makes protocols 256-262
    answer -EINVAL where Linux answers -EPROTONOSUPPORT. -/
def IPPROTO_IP : Int := 0
def IPPROTO_TCP : Int := 6
def IPPROTO_SCTP : Int := 132
def IPPROTO_MPTCP : Int := 262
def IPPROTO_MAX : Int := 263

/-- The three address lengths the socket calls test, in the order the
    kernel applies them:

    - `SOCKADDR_STORAGE_SIZE`, the largest address `move_addr_to_kernel`
      will copy (include/uapi/linux/socket.h);
    - `SA_FAMILY_SIZE`, `sizeof (sa_family_t)` — an `unsigned short` —
      which is `__inet_stream_connect`'s
      `addr_len < sizeof(uaddr->sa_family)` and so precedes its state
      switch;
    - `SOCKADDR_IN_SIZE`, `sizeof (struct sockaddr_in)`, the smallest
      `inet_bind_sk` accepts (include/uapi/linux/in.h) and the one
      `tcp_v4_connect` applies AFTER that switch.

    The middle one is connect's alone: bind reaches `inet_bind_sk`
    directly and never tests it.  A 4-byte address passes it and is then
    refused by the third. -/
def SOCKADDR_STORAGE_SIZE : Int := 128
def SA_FAMILY_SIZE : Int := 2
def SOCKADDR_IN_SIZE : Int := 16

/-- The three option LEVELS an AF_INET/SOCK_STREAM socket has a handler
    for, and `shutdown`'s three directions.

    `SOL_SOCKET` is the odd one out: it is not an `IPPROTO_*` value but
    a constant of its own, from include/uapi/asm-generic/socket.h, which
    riscv64 uses unchanged.  The other two are `IPPROTO_IP` and
    `IPPROTO_TCP` above — SOL_IP and SOL_TCP are the SAME NUMBERS (0 and
    6) under other names (include/uapi/linux/in.h), so they are not
    defined again here; `Net.Socket.sock_level_known` names them as the
    levels.

    `SHUT_RD`/`SHUT_WR`/`SHUT_RDWR` are the members of the unnumbered
    `enum sock_shutdown_cmd` in include/linux/net.h, declared in that
    order with no initialisers, hence 0/1/2 (unchanged v6.1 through
    v6.19).  They are NOT the `RCV_SHUTDOWN`/`SEND_SHUTDOWN` bits of
    include/net/sock.h (1/2/3, with `SHUTDOWN_MASK = 3`) — `inet_shutdown`
    converts between the two with a `how++`, and mistaking one set for
    the other is exactly how a model gets `shutdown`'s validation
    backwards. -/
def SOL_SOCKET : Int := 1
def SHUT_RD : Int := 0
def SHUT_WR : Int := 1
def SHUT_RDWR : Int := 2

def SEEK_SET : Int := 0
def SEEK_CUR : Int := 1
def SEEK_END : Int := 2

/-- The largest whence the kernel accepts at all: SEEK_HOLE.
    `ksys_lseek` tests `whence <= SEEK_MAX` AFTER resolving the fd and
    BEFORE `vfs_llseek`, so the -EINVAL for a whence past it precedes
    every per-file-kind answer — including a pipe's -ESPIPE. -/
def SEEK_MAX : Int := 4

/-- mmap prot/flags ABI constants (asm-generic, as on riscv64:
    include/uapi/asm-generic/mman-common.h, Linux v6.12). -/
def PROT_READ : Int := 1
def PROT_WRITE : Int := 2
def PROT_NONE : Int := 0
/-- mprotect's two stack-extension modifiers (include/uapi/asm-generic/
    mman-common.h).  They are not permissions: `do_mprotect_pkey` masks
    them out of `prot` before anything else looks at it, and only their
    conjunction is an argument error (see `Mprotect.mprotect_grows_conflict_b`). -/
def PROT_GROWSDOWN : Int := 0x01000000
def PROT_GROWSUP : Int := 0x02000000
def MAP_PRIVATE : Int := 2
def MAP_FIXED : Int := 16              -- 0x10
def MAP_ANONYMOUS : Int := 32          -- 0x20
def MAP_HUGETLB : Int := 262144        -- 0x40000

/-- MAP_FIXED_NOREPLACE, from the same arch-generic header riscv64
    inherits: `#define MAP_FIXED_NOREPLACE 0x100000`
    (include/uapi/asm-generic/mman-common.h:31, Linux v6.18.46).  It
    asks for placement at `addr` exactly, as MAP_FIXED does, but for a
    refusal rather than a replacement when any page of the range is
    already mapped; `do_mmap` (mm/mmap.c:361-362 and :410-412, Linux
    v6.18.46) is where both halves are decided, and
    `Mmap.mmap_noreplace_flags_b` carries the reading. -/
def MAP_FIXED_NOREPLACE : Int := 1048576   -- 0x100000

/-- mremap ABI flag bits (asm-generic, as on riscv64):
    `#define MREMAP_MAYMOVE 1` (include/uapi/linux/mman.h:9, v6.12).  The
    value is architecture-independent — riscv64 has no
    arch/riscv/include/uapi/asm/mman.h of its own, and neither
    include/uapi/asm-generic/mman.h nor mman-common.h redefines any
    MREMAP_ bit, so this uapi header is the sole definition. -/
def MREMAP_MAYMOVE : Int := 1

/-- madvise advice values (asm-generic, as on riscv64):
    `#define MADV_DONTNEED 4` (include/uapi/asm-generic/mman-common.h:49,
    Linux v6.18.46).  Architecture-independent for the same reason the
    MREMAP_ bits are: riscv64 carries no uapi mman.h of its own, and the
    arch-generic mman.h defines no MADV_ value, so mman-common.h is the
    sole definition.  `Mm.Madvise.madvise_dontneed_b` is the one reader. -/
def MADV_DONTNEED : Int := 4

/-- getrandom flag bits (include/uapi/linux/random.h). -/
def GRND_NONBLOCK : Int := 1
def GRND_RANDOM : Int := 2

/-- The ioctl requests that only a terminal implements.

    TIOCGWINSZ is the one a musl-linked binary reaches on its own:
    `__fdopen`, `__stdout_write` and `isatty` probe the terminal window
    size to pick stdio's buffering mode.  The rest are what a program
    that expects to own a pty asks for — `tcgetattr` and
    `tcsetattr(TCSANOW)`, the other half of the window-size pair, the
    controlling-terminal pair `TIOCSCTTY`/`TIOCNOTTY`, and the two
    requests musl's `openpty` issues on /dev/ptmx.  Every one of them is
    on the path a Dropbear SSH server takes to hand a session a
    terminal.

    Values are the asm-generic ones, which riscv64 uses unchanged: riscv
    has no arch/riscv/include/uapi/asm/ioctls.h, and
    include/uapi/asm-generic/Kbuild lists ioctls.h as mandatory, so the
    port gets the generic header verbatim.  It is byte-identical for all
    eight across Linux v5.10-v6.14
    (include/uapi/asm-generic/ioctls.h). -/
def TCGETS : word := BitVec.ofInt 64 21505       -- 0x5401
def TCSETS : word := BitVec.ofInt 64 21506       -- 0x5402
def TIOCSCTTY : word := BitVec.ofInt 64 21518    -- 0x540E
def TIOCGWINSZ : word := BitVec.ofInt 64 21523   -- 0x5413
def TIOCSWINSZ : word := BitVec.ofInt 64 21524   -- 0x5414
def TIOCNOTTY : word := BitVec.ofInt 64 21538    -- 0x5422
def TIOCGPTN : word := BitVec.ofInt 64 2147767344   -- 0x80045430
def TIOCSPTLCK : word := BitVec.ofInt 64 1074025521 -- 0x40045431

/-- The fcntl commands, from `include/uapi/asm-generic/fcntl.h` — riscv64
    supplies no arch override, so these are its values.  `F_GETLK` and
    friends are the 64-bit spellings (5/6/7).  The 12/13/14 numbering is
    guarded by `#if __BITS_PER_LONG == 32 || defined(__KERNEL__)`, so a
    64-bit kernel does define those names — but `do_fcntl` has no arm for
    them and they fall to its `default: break`, returning the -EINVAL its
    `long err` was initialised to.  Declining them is therefore the same
    answer `Fcntl.fcntl_spec` gives every unrecognized command. -/
def F_GETFD : word := BitVec.ofInt 64 1
def F_SETFD : word := BitVec.ofInt 64 2
def F_GETFL : word := BitVec.ofInt 64 3
def F_SETFL : word := BitVec.ofInt 64 4

/-- The `flock` operations, from that same header
    (`include/uapi/asm-generic/fcntl.h`, Linux v6.18.46, commit
    1f99e9ab748f).  They are a MIXED word rather than an enumeration:
    LOCK_NB is a modifier OR'd into one of the other three, which is why
    `Fs.Locks.flock_base` strips it before comparing.

    LOCK_MAND is here because the kernel still READS it, not because
    anything sets it.  Mandatory flocks were removed, and what replaced
    them is not a rejection: `SYSCALL_DEFINE2(flock)` (fs/locks.c) opens
    with `if (cmd & LOCK_MAND) ... return 0;`, so the bit turns the whole
    call into a no-op that succeeds — ahead of the operation check, ahead
    of the descriptor lookup, and so ahead of every errno flock has.  A
    model that only knew the three operations would answer -EINVAL there,
    which is the confident wrong answer this constant exists to prevent.

    The header keeps LOCK_READ, LOCK_WRITE and LOCK_RW beside it; they
    are not named here because nothing in fs/locks.c reads them at
    v6.18.46 — they reach `flock_translate_cmd`'s `switch` as ordinary
    unrecognized words and are -EINVAL, which is what the general rule
    already gives.  LOCK_MAND is the one whose bit is tested. -/
def LOCK_SH : Int := 1
def LOCK_EX : Int := 2
def LOCK_NB : Int := 4
def LOCK_UN : Int := 8
def LOCK_MAND : Int := 32

/-- The file STATUS flag bits `setfl` (fs/fcntl.c) reads, from that same
    header.  `Fcntl.setfl_acted_on` is their union and carries the
    argument for why each one is in it — in particular why FASYNC, which
    `SETFL_MASK` omits, belongs there all the same.  O_NONBLOCK (04000)
    is one of them; it is defined above, with the open flags that ignore
    it, because it is one bit of one ABI and so one constant. -/
/- O_APPEND is read by TWO things, like O_DIRECT below:
    `Fcntl.setfl_acted_on`, for which it is a status bit F_SETFL really
    changes, and `Open.append_create_flags`, the open shape that mints a
    `State.FdFileA`.  The two readings are coupled rather than
    independent — the append open is the one admitted shape whose
    residue meets `setfl_acted_on`, and `Fcntl.setfl_noop_on`'s
    `FdFileA` arm is what keeps that sound. -/
def O_APPEND : Int := 1024       -- 02000
def FASYNC : Int := 8192         -- 020000
/-- O_DIRECT is read by TWO things: `Fcntl.setfl_acted_on`, for which it
    is a status bit F_SETFL really changes, and
    `Fs.Pipe.pipe2_flags_mask`, which names it among the bits pipe2
    ACCEPTS -- what separates a real -EINVAL from a decline. -/
def O_DIRECT : Int := 16384      -- 040000
def O_NOATIME : Int := 262144    -- 01000000

/-- `RLIMIT_CORE`, the maximum size of a core dump (Linux v6.10-v6.15,
    include/uapi/asm-generic/resource.h, byte-identical at all six tags). -/
def RLIMIT_CORE : Int := 4

/-- The POSIX clock ids the model interprets
    (include/uapi/linux/time.h, Linux v6.10-v6.15 and v6.18.46; the id
    block is byte-identical across all of them).  A clock id gets a name
    here when some spec TESTS it, not when it exists: the ids nothing
    tests are deliberately left unnamed, because a constant only a
    comment reads is dead weight.
    `Kernel.Time.PosixTimers.clock_gettime_spec` names the ids it
    declines in prose rather than as constants.

    The first three are `clock_gettime`'s.  The last three are
    `Fs.Timerfd.timerfd_create_spec`'s, and they are named for the
    OPPOSITE reason: that spec's whole content is a five-way membership
    test written out of Linux's own, so each id it admits has to be
    stateable.  The two families OVERLAP but neither contains the other
    — `timerfd_create` takes `CLOCK_BOOTTIME` and the two alarm clocks
    that `clock_gettime` declines, and declines
    `CLOCK_PROCESS_CPUTIME_ID`, which `clock_gettime` answers.  Do not
    read either list as "the clocks the model supports". -/
def CLOCK_REALTIME : Int := 0
def CLOCK_MONOTONIC : Int := 1
def CLOCK_PROCESS_CPUTIME_ID : Int := 2
def CLOCK_MONOTONIC_RAW : Int := 4
def CLOCK_REALTIME_COARSE : Int := 5
def CLOCK_MONOTONIC_COARSE : Int := 6
def CLOCK_BOOTTIME : Int := 7
def CLOCK_REALTIME_ALARM : Int := 8
def CLOCK_BOOTTIME_ALARM : Int := 9

/-- `TFD_CREATE_FLAGS`, the only flag bits `timerfd_create` accepts.

    include/linux/timerfd.h (Linux v6.18.46) defines
    `TFD_SHARED_FCNTL_FLAGS (TFD_CLOEXEC | TFD_NONBLOCK)` and then
    `TFD_CREATE_FLAGS TFD_SHARED_FCNTL_FLAGS` -- the create mask IS the
    shared-fcntl mask, so one constant serves.  The two members are
    `O_CLOEXEC` and `O_NONBLOCK` themselves, which fs/timerfd.c asserts
    at build time rather than assuming: `SYSCALL_DEFINE2(timerfd_create)`
    opens with `BUILD_BUG_ON(TFD_CLOEXEC != O_CLOEXEC)` and
    `BUILD_BUG_ON(TFD_NONBLOCK != O_NONBLOCK)`.  Spelling the value as
    `Z.lor O_CLOEXEC O_NONBLOCK` rather than as 526336 is therefore not a
    convenience: it is the kernel's own definition, and the two
    `BUILD_BUG_ON`s are what license reusing the `O_` constants for it.

    `TFD_TIMER_ABSTIME` and `TFD_TIMER_CANCEL_ON_SET` belong to
    `TFD_SETTIME_FLAGS` and are NOT accepted here -- passing either to
    `timerfd_create` is -EINVAL.  They go unnamed because
    `timerfd_settime` has no arm. -/
def TFD_CREATE_FLAGS : Int := z_lor O_CLOEXEC O_NONBLOCK

/-- `EFD_SEMAPHORE`, the one flag bit `eventfd2` accepts that no other
    anon-inode create call does.

    include/uapi/linux/eventfd.h (Linux v6.18.46) defines it as
    `(1 << 0)` beside `EFD_CLOEXEC O_CLOEXEC` and
    `EFD_NONBLOCK O_NONBLOCK`; fs/eventfd.c's `do_eventfd` asserts all
    three at build time rather than assuming them, opening with
    `BUILD_BUG_ON(EFD_CLOEXEC != O_CLOEXEC)`,
    `BUILD_BUG_ON(EFD_NONBLOCK != O_NONBLOCK)` and
    `BUILD_BUG_ON(EFD_SEMAPHORE != (1 << 0))`.

    The three `EFD_` names were not always in the same header: at v6.1
    and earlier all three sit in include/linux/eventfd.h, and the uapi
    header carrying them is there from at least v6.6.  The VALUES are
    identical across that move, so nothing here turns on which header a
    reader opens -- but the path in a citation does, which is why the
    move is stated rather than left for the next reader to rediscover. -/
def EFD_SEMAPHORE : Int := 1

/-- `EFD_FLAGS_SET`, the only flag bits `eventfd2` accepts.

    include/linux/eventfd.h (Linux v6.18.46) defines
    `EFD_SHARED_FCNTL_FLAGS (O_CLOEXEC | O_NONBLOCK)` and then
    `EFD_FLAGS_SET (EFD_SHARED_FCNTL_FLAGS | EFD_SEMAPHORE)`, so the
    create mask is the shared-fcntl mask WIDENED BY ONE BIT -- which is
    what separates it from `TFD_CREATE_FLAGS`, where the create mask IS
    the shared-fcntl mask and nothing more.

    THAT ONE BIT IS THE WHOLE DIFFERENCE between the two masks, and it
    is why they are two constants rather than one shared name.  Bit 0 is
    `EFD_SEMAPHORE` to `eventfd2` and is `TFD_TIMER_ABSTIME` --
    `timerfd_settime`'s flag, not `timerfd_create`'s -- to
    `timerfd_create`, which refuses it.  So `eventfd2(0, 1)` hands back
    a descriptor and `timerfd_create(CLOCK_MONOTONIC, 1)` is -EINVAL,
    and a model that spelled one gate with the other's mask would be
    wrong on exactly one input each way. -/
def EFD_FLAGS_SET : Int := z_lor (z_lor O_CLOEXEC O_NONBLOCK) EFD_SEMAPHORE

/-- The range `ktime_t` represents, in nanoseconds.

    Linux carries kernel time as `ktime_t`, a signed 64-bit nanosecond
    count — `typedef s64 ktime_t` in include/linux/types.h (not ktime.h,
    whose surrounding helpers do change across the range: v6.14 adds
    `us_to_ktime`).  The typedef itself is unchanged at v6.10-v6.15.  So
    2^63 nanoseconds — about 292 years — is the first value it cannot
    hold.

    Every time spec below the header layer needs this bound, for a
    different quantity: `Kernel.Time.PosixTimers` as the ceiling on a
    recorded `CLOCK_MONOTONIC` reading, and `Kernel.Time.Hrtimer` as the
    ceiling on where a sleep may carry that reading.  It is here rather
    than with either of them because it is a fact about the type, not
    about a syscall. -/
def CLOCK_NS_ENVELOPE : Int := 2 ^ 63

/-- The largest value `ktime_t` holds:
    `#define KTIME_MAX ((s64)~((u64)1 << 63))` (include/linux/time64.h at
    v6.18.46, which is where both constants are defined —
    include/linux/ktime.h uses them without redefining them), i.e.
    2^63 - 1, one nanosecond below `CLOCK_NS_ENVELOPE`.

    It is the value `ktime_add_safe` (kernel/time/hrtimer.c) SATURATES
    to, which is the one place the two constants must not be confused.
    That function's saturation arm reads `res = ktime_set(KTIME_SEC_MAX,
    0)`, and its comment says it is using "the maximum timeout which we
    can return to user space in a timespec" — but `ktime_set`
    (include/linux/ktime.h) opens with
    `if (unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;`, and the
    test is `>=`, so passing exactly `KTIME_SEC_MAX` takes that early
    return.  The saturation value is therefore `KTIME_MAX`, NOT
    `KTIME_SEC_MAX * 10^9` — the code does not do what its own comment
    describes, and the difference is the 854775807 ns between them.
    `Kernel.Time.Hrtimer.nanosleep_clock` needs the value the code
    produces.  Both functions read as quoted at v6.18.46. -/
def KTIME_MAX : Int := 2 ^ 63 - 1

/-- The largest whole second `ktime_t` can hold:
    `#define KTIME_SEC_MAX (KTIME_MAX / NSEC_PER_SEC)` over
    `#define KTIME_MAX ((s64)~((u64)1 << 63))` (include/linux/time64.h;
    the whole constant block is byte-identical at v6.10-v6.15), i.e.
    (2^63 - 1) / 10^9 = 9223372036.

    Two readers need it, for different reasons:
    `Time.gettimeofday_spec` as the ceiling on a wall-clock
    reading, and `timespec_ktime` just below as the point where
    `ktime_set` stops converting a request and starts clamping. -/
def KTIME_SEC_MAX : Int := 9223372036

/-- Two little-endian 8-byte fields, read OUT of the bytes the kernel
    wrote.

    THE NAMES ARE STRUCT-NEUTRAL because three structs have this shape
    on riscv64.  `struct __kernel_timespec` { `__kernel_time64_t
    tv_sec`; `long long tv_nsec` } and `struct __kernel_old_timeval`
    { `__kernel_long_t tv_sec`; `__kernel_long_t tv_usec` }
    (include/uapi/linux/time_types.h, byte-identical at v6.10-v6.15)
    are both 16 bytes of two 8-byte fields, differing only in the UNIT
    of the second one — nanoseconds against microseconds.  So the
    decoders are shared and only the per-struct predicates
    (`Kernel.Time.PosixTimers.timespec_ok_b`,
    `Time.timeval_ok_b`,
    `Kernel.Time.Hrtimer.timespec_valid_b`) differ.

    Reading the bytes, rather than encoding a chosen count into them,
    is deliberate: the bytes in the destination buffer are what the
    kernel actually produced, so
    every condition over them is stated about them directly.  The
    alternative — choose a count, encode it, and have the acceptor
    decode it back — would need the encode/decode round-trip as a proof
    obligation to say the same thing. -/
def tv_sec_of (bs : List byte) : Int :=
  bytes_le_to_Z (bs.take 8)
def tv_frac_of (bs : List byte) : Int :=
  bytes_le_to_Z (bs.drop 8)

/-- A whole `struct __kernel_timespec` as a nanosecond count.  Computed
    in `Int`, NOT in `word`: a wrapping sum would let an absurd `tv_sec`
    land back under the envelope and read as a small, admissible
    time. -/
def timespec_ns (bs : List byte) : Int :=
  tv_sec_of bs * 1000000000 + tv_frac_of bs

/-- The same `struct __kernel_timespec` as the `ktime_t` the kernel
    converts it to, which is NOT the same number.

    `timespec64_to_ktime` is `ktime_set(ts.tv_sec, ts.tv_nsec)`
    (include/linux/ktime.h at v6.18.46, where both functions are
    defined), and `ktime_set` opens with

      `if (unlikely(secs >= KTIME_SEC_MAX)) return KTIME_MAX;`

    so the conversion STOPS at `KTIME_SEC_MAX` and hands back
    `KTIME_MAX` rather than a product.  The two disagree over the whole
    band `[KTIME_SEC_MAX, 2^63)` of seconds a `timespec64` can carry
    past `timespec64_valid`, and they disagree AT the boundary too, in
    both directions: `KTIME_SEC_MAX` seconds converts to `KTIME_MAX`
    and not to `KTIME_SEC_MAX * 10^9`, which is 854775807 ns lower.

    `tv_sec` is read unsigned here for `timespec_ns`'s reason, and the
    one caller (`Kernel.Time.Hrtimer.nanosleep_clock`) has already
    applied `timespec64_valid`, which refuses a `tv_sec` at or past
    2^63 — so the band this function saturates over is exactly the band
    that predicate lets through. -/
def timespec_ktime (bs : List byte) : Int :=
  if tv_sec_of bs < KTIME_SEC_MAX then timespec_ns bs else KTIME_MAX

/-- The same total with `tv_sec` read as the SIGNED 64-bit field it
    actually is (`__kernel_time64_t` is `long long`).  `timespec_ns`
    reads it unsigned, which is what the two arms that report a TIME
    want — a negative second is not a time, and reading it unsigned
    turns it into a number far past their envelope, which is exactly
    the rejection they need.  `CLOCK_PROCESS_CPUTIME_ID` does not
    report a time, and a negative `tv_sec` is a shape it really emits,
    so `Kernel.Time.PosixTimers.cputime_ok_b` needs the signed reading.
    Computed in `Int` for `timespec_ns`'s reason: a wrapping sum would
    let an absurd `tv_sec` land back in range. -/
def timespec_ns_signed (bs : List byte) : Int :=
  (if tv_sec_of bs < 2 ^ 63 then tv_sec_of bs
    else tv_sec_of bs - 2 ^ 64) * 1000000000 + tv_frac_of bs

/-- `AT_REMOVEDIR` (0x200): the only flag `unlinkat` accepts.  Any other
    bit is a deterministic -EINVAL, decided before the pathname is
    fetched and before the dirfd is looked at — see `Fs.Namei.unlinkat_spec`
    (Linux include/uapi/linux/fcntl.h; the value is unchanged v6.10
    through v6.15, though the file was reorganised in v6.12). -/
def AT_REMOVEDIR : Int := 512

/-- The longest single path COMPONENT every Linux filesystem in reach
    accepts (Linux include/uapi/linux/limits.h).  `fs/namei.c` itself has
    NO such check — the bound belongs to the filesystem, raised by
    `dir->i_op->lookup` (`simple_lookup` in fs/libfs.c on tmpfs and
    `ext4_lookup` in fs/ext4/namei.c on ext4, both -ENAMETOOLONG at 255;
    that guard is the FIRST statement of each function and is unchanged
    v6.10 through v6.16, though the bodies around it are not — ext4's
    changed at v6.11 and libfs's at v6.13, and ext4 reaches 255 through
    its own `EXT4_NAME_LEN` rather than through `NAME_MAX`).  So the
    model, which represents no filesystem type, declines a longer name
    rather than picking one filesystem's answer. -/
def NAME_MAX : Nat := 255

/-- One second in nanoseconds (include/vdso/time64.h `NSEC_PER_SEC`),
    the bound `timespec64_valid` holds `tv_nsec` under. -/
def NSEC_PER_SEC : Int := 1000000000

/-- `sizeof(sigset_t)` as the KERNEL declares it: `_NSIG` is 64, so the
    mask is 8 bytes.  `set_user_sigmask` rejects any other
    `sigsetsize` with -EINVAL.  Note this is the kernel's sigset, not
    glibc's 128-byte one. -/
def kernel_sigset_bytes : Int := 8

/-- `rt_sigprocmask`'s `how`, from include/uapi/asm-generic/signal-defs.h.
    riscv defines no `uapi/asm/signal.h` of its own, so the asm-generic
    values are the ones the riscv64 ABI uses.  Byte-identical across
    v6.1 - v6.17. -/
def SIG_BLOCK : Int := 0
def SIG_UNBLOCK : Int := 1
def SIG_SETMASK : Int := 2

/-- `sizeof(sigset_t)`, the size `rt_sigprocmask` demands in its fourth
    argument and the number of bytes it copies.

    Eight, and derived rather than asserted: include/uapi/asm-generic/
    signal.h has `_NSIG 64`, `_NSIG_BPW __BITS_PER_LONG` and
    `typedef struct { unsigned long sig[_NSIG / _NSIG_BPW]; } sigset_t`,
    and riscv64's `__BITS_PER_LONG` is `__SIZEOF_POINTER__ * 8`
    (arch/riscv/include/uapi/asm/bitsperlong.h), i.e. 64, so `sigset_t`
    is one 64-bit word.  Both headers are byte-identical across v6.1 - v6.17.

    The same eight bytes as `kernel_sigset_bytes` above, which
    `set_user_sigmask`'s check on pselect6's sigmask argument names;
    the two are separate definitions, one for each spec that names the
    constant.

    NOT musl's userspace `sigset_t`, which is 128 bytes
    (include/signal.h). -/
def NSIG_BYTES : Int := 8

/-- `sigaltstack`'s three flag values, from include/uapi/linux/signal.h
    (Linux v6.18.46, commit 1f99e9ab748f).  riscv defines no
    `uapi/asm/signal.h` of its own, so these asm-generic values are the
    ones the riscv64 ABI uses.

    SS_AUTODISARM is the whole of `SS_FLAG_BITS` — that header defines
    `SS_FLAG_BITS` AS `SS_AUTODISARM`, so the two are one constant and
    are not spelled twice here.  It is what `do_sigaltstack`
    (kernel/signal.c) masks off its `ss_flags` before comparing the rest
    against SS_DISABLE, SS_ONSTACK and 0, and what `on_sig_stack`
    (include/linux/sched/signal.h) tests to answer "not on the stack"
    without looking at the stack pointer. -/
def SS_ONSTACK : Int := 1
def SS_DISABLE : Int := 2
def SS_AUTODISARM : Int := 0x80000000     -- = SS_FLAG_BITS

/-- `sizeof(stack_t)` on riscv64: `ss_sp`(8) at 0, `ss_flags`(4, an
    `int`) at 8, four bytes of padding, `ss_size`(8, a
    `__kernel_size_t`) at 16 — 24 bytes.  The struct is the asm-generic
    one (include/uapi/asm-generic/signal.h, the `struct sigaltstack` definition), which riscv does not override.
    `SYSCALL_DEFINE2(sigaltstack)` (kernel/signal.c) copies exactly
    `sizeof(stack_t)` out of `uss` in ONE `copy_from_user`, so
    readability is all-or-nothing across the whole 24 — the padding
    included, even though nothing reads it. -/
def SIGALTSTACK_BYTES : Int := 24
def SS_SP_OFF : Int := 0
def SS_FLAGS_OFF : Int := 8
def SS_SIZE_OFF : Int := 16

/-- The smallest alternate stack `sigaltstack` accepts:
    `SYSCALL_DEFINE2(sigaltstack)` passes MINSIGSTKSZ as
    `do_sigaltstack`'s `min_ss_size`, and riscv takes the asm-generic
    value 2048 (include/uapi/asm-generic/signal.h, guarded by
    `#if !defined MINSIGSTKSZ`; riscv supplies no `uapi/asm/signal.h` to
    define one first).  Anything smaller is -ENOMEM.  It is not the only
    lower bound the kernel applies — see `Kernel.Signal.sigaltstack_spec`
    for `sigaltstack_size_valid`, which is the other one and is why that
    spec's success arm carries a premise. -/
def MINSIGSTKSZ : Int := 2048

/-- The two signals a mask may never contain, as the bits they occupy in
    a `sigset_t`: `sigmask(sig)` is `1 << (sig - 1)`
    (include/linux/signal.h), SIGKILL is 9 and SIGSTOP is 19
    (include/uapi/asm-generic/signal.h), so the pair is bit 8 | bit 18 =
    0x40100.  `rt_sigprocmask` clears exactly these from the set it is
    handed, with
    `sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))`
    (kernel/signal.c, `SYSCALL_DEFINE4(rt_sigprocmask)`, Linux v6.18.46,
    commit 1f99e9ab748f), and answers 0: blocking either is silently
    ignored, NOT -EINVAL.  That is the opposite of `rt_sigaction`, where
    `sig_kernel_only` is an error — see `Kernel.Signal.sig_kernel_only`,
    which tests the same two signals for the other syscall's sake.

    THE STRIP IS THE WRAPPER'S, NOT `sigprocmask`'s.  The comment above
    `sigprocmask` in the same file says so in as many words: "Unlike the
    user-mode sys_sigprocmask(), the kernel interface happily blocks
    'unblockable' signals like SIGKILL and friends."  So a claim that
    every path clearing these bits runs through one function is FALSE;
    what is true is the enumeration in `Run.valid_sigmask`. -/
def sig_kernel_only_mask : Int := 262400

/-- SIGABRT, and the bit it occupies in a `sigset_t`.  6
    (include/uapi/asm-generic/signal.h), so `sigmask(SIGABRT)` is
    `1 << 5` = 32 (include/linux/signal.h, the same `sigmask` macro
    `sig_kernel_only_mask` is built from).  Its default disposition is
    SIG_CORE -- terminate the process and dump core
    (kernel/signal.c's `sig_kernel_coredump` over SIG_KERNEL_COREDUMP_MASK,
    Linux v6.18.46, commit 1f99e9ab748f) -- and the core dump itself is
    outside anything this model observes: `do_coredump` writes a file the
    process cannot see and `do_group_exit` ends the process either way.
    What reaches the trace is the DEATH and the signal number, which is
    what a waiting parent reads through WIFSIGNALED/WTERMSIG and a shell
    renders as 134. -/
def SIGABRT : Int := 6
def sigabrt_mask : Int := 32

/-- `WNOHANG`, the one wait4 option this model accepts
    (include/uapi/linux/wait.h, whose `W*` macro block is byte-identical
    in mainline from v3.10 — the oldest tag that still fetches — through
    v7.2; that header is where every `W*` macro lives, and
    include/linux/wait.h is wait-queue types and defines none of them).
    The FILE moved twice in that span, both times outside the block: an
    SPDX line at v4.14 and `P_PIDFD` at v5.4.  The other option bits
    Linux accepts — WUNTRACED, WCONTINUED, __WNOTHREAD, __WCLONE,
    __WALL — are not named here because no arm reads them: they select
    which children are eligible and which state changes are reportable,
    questions about children this model does not have.  Anything but
    WNOHANG declines; see `Kernel.Exit.wait4_spec`. -/
def WNOHANG : Int := 1
/-- MSG_CMSG_COMPAT (include/linux/socket.h).  Its VALUE depends on the
    kernel's configuration: `0x80000000` under CONFIG_COMPAT and `0`
    without it, and the two give different answers for the same call —
    see `Net.Socket.recvmsg_spec`. -/
def MSG_CMSG_COMPAT : Int := 2147483648   -- 0x80000000

/-- `NR_OPEN_DEFAULT`, the number of descriptor slots embedded in a
    `struct files_struct` (include/linux/fdtable.h,
    `#define NR_OPEN_DEFAULT BITS_PER_LONG`, Linux v6.18.46, commit
    1f99e9ab748f) — 64 on the LP64 target this model compiles for, and 32
    on a 32-bit one, which is the one leg of the argument below that is
    arch-dependent.

    WHY A SPEC READS IT.  It is a FLOOR on the live descriptor table:
    every `struct fdtable` a task can reach has `max_fds >=
    NR_OPEN_DEFAULT`.  There are three producers and no shrinker (all
    fs/file.c) — `init_files` is a static initializer at exactly this
    value; `dup_fd` starts the new table at the embedded `fdtab` and
    calls `alloc_fdtable` only under `while (open_files >
    new_fdt->max_fds)`; and `alloc_fdtable` returns a table no smaller
    than it was asked for.  Both writes of `max_fds` happen before the
    table is published with `rcu_assign_pointer`, and nothing writes it
    in place.  `sane_fdtable_size` cannot ask for less either: every
    return is `NR_OPEN_DEFAULT` or `ALIGN(last + 1, BITS_PER_LONG)`.

    The consequence `Fs.File.dup3_spec` uses: `expand_files(files, nr)`
    opens with `if (nr < fdt->max_fds) return 0;`, so for `nr <
    NR_OPEN_DEFAULT` it returns 0 having allocated nothing — neither the
    -EMFILE of `nr >= sysctl_nr_open` nor the -ENOMEM of a failed
    `kvmalloc` is reachable.  The bound is a comment rather than an
    assertion on the kernel's side (`alloc_fdtable` documents its
    `slots_wanted > BITS_PER_LONG` precondition and does not check it),
    so it is the two call sites that hold it up.

    Its two readers use the floor for different things:
    `Fs.File.dup3_spec` for `expand_files`, and
    `Fs.Select.pselect_nfds_max` for `core_sys_select`'s clamp to
    `max_fds`.

    It says nothing about whether an operation SUCCEEDS: RLIMIT_NOFILE is
    a separate and earlier gate in every caller, which is why
    `dup3_spec` tests the limit before it reaches this. -/
def NR_OPEN_DEFAULT : Int := 64

/-- `NGROUPS_MAX`, the ceiling on a process's supplementary group list
    (include/uapi/linux/limits.h, `#define NGROUPS_MAX 65536`; the value
    has stood since before v2.6.12, the oldest commit in the tree).  The
    kernel enforces it where the list is WRITTEN — `setgroups` answers
    -EINVAL for a `gidsetsize` above it (kernel/groups.c,
    `SYSCALL_DEFINE2(setgroups)`) — so no `struct group_info` a process
    can hold is longer.  `Kernel.Groups.getgroups_spec` reads it as the
    bound that makes its own answer one an `int` return can carry. -/
def NGROUPS_MAX : Int := 65536

/-- The scheduling policies `sched_setscheduler` takes, and the flag bit
    it lets a caller OR into them (include/uapi/linux/sched.h, Linux
    v6.18.46, commit 1f99e9ab748f).  4 is absent from the block on
    purpose — the header reserves it for an unimplemented SCHED_ISO and
    defines no name for it — so the six numbers below are not an
    interval and a membership test cannot be written as a range.

    `SCHED_EXT` is named for the opposite reason to the other five: no
    arm ANSWERS it.  `Kernel.Sched.Syscalls.sched_setscheduler_spec`
    declines it, and the constant exists so the decline can say which
    number it is declining.  See that spec for why: whether
    kernel/sched/sched.h's `valid_policy` admits 7 at all turns on
    CONFIG_SCHED_CLASS_EXT, and the model does not fix that config. -/
def SCHED_NORMAL : Int := 0
def SCHED_FIFO : Int := 1
def SCHED_RR : Int := 2
def SCHED_BATCH : Int := 3
def SCHED_IDLE : Int := 5
def SCHED_DEADLINE : Int := 6
def SCHED_EXT : Int := 7

/-- The legacy "revert to SCHED_NORMAL on fork" bit, ORed into the
    policy word rather than passed separately
    (include/uapi/linux/sched.h).  `_sched_setscheduler`
    (kernel/sched/syscalls.c) strips it into
    `attr.sched_flags |= SCHED_FLAG_RESET_ON_FORK` before
    `__sched_setscheduler` reads the policy, which is why it has to be
    masked off a policy word before that word is compared against the
    six names above. -/
def SCHED_RESET_ON_FORK : Int := 0x40000000

/-- The first priority `__sched_setscheduler` refuses: it answers
    -EINVAL for `attr->sched_priority > MAX_RT_PRIO-1`, so 1..99 are the
    RT priorities and 0 is the only one a non-RT policy accepts
    (include/linux/sched/prio.h, `#define MAX_RT_PRIO 100`; the
    comparison is in kernel/sched/syscalls.c,
    `__sched_setscheduler`).  It is not a uapi constant — the number a
    program is told to use is `sched_get_priority_max(SCHED_FIFO)`,
    which computes it — but the comparison the model transcribes is
    against this. -/
def MAX_RT_PRIO : Int := 100

/-- `CLONE_VM`, the bit that makes a new task share the caller's address
    space (include/uapi/linux/sched.h, Linux v6.18.46, commit
    1f99e9ab748f).

    Named here for ONE reader, and it is not in `Sys/`: it is the bit
    `Kernel.Futex.Syscalls`'s empty-waiter-set argument depends on
    nobody ever granting, and `Checks/Cases/Kernel/Futex/Syscalls.lean`
    turns that dependency into a checked fact over both clone gates
    ([clone_fork_gate_grants_no_shared_mm] and
    [clone3_fork_gate_grants_no_shared_mm]), so widening a gate fails
    that build rather than only a reader's expectation.
    `Kernel.Fork` names the
    flag in prose throughout and needs no constant, because its gates
    are equalities on whole words rather than mask tests. -/
def CLONE_VM : Int := 256

/-- The `futex` operation words this model answers, and the two bits
    that decorate them (include/uapi/linux/futex.h, Linux v6.18.46,
    commit 1f99e9ab748f).

    `SYSCALL_DEFINE6(futex)` (kernel/futex/syscalls.c) does not switch on
    `op` itself: `do_futex` splits it into a COMMAND, `op &
    FUTEX_CMD_MASK`, and the two flag bits the mask removes,
    `FUTEX_PRIVATE_FLAG` and `FUTEX_CLOCK_REALTIME`.  The mask is
    `~(FUTEX_PRIVATE_FLAG | FUTEX_CLOCK_REALTIME)`, so every OTHER bit
    of `op` is part of the command and reaches the switch's `default:
    return -ENOSYS;`.

    `FUTEX_PRIVATE_FLAG` is not decoration.  `futex_to_flags`
    (kernel/futex/futex.h) sets `FLAGS_SHARED` exactly when the bit is
    CLEAR, and that flag decides which key `get_futex_key`
    (kernel/futex/core.c) builds — the private path keys on
    `(current->mm, address)` and returns before it looks at a page at
    all, the shared path resolves the page and can key on an inode two
    processes share.  So the bit changes WHO can be waiting on the word,
    which is the whole of what `Kernel.Futex.Syscalls.futex_spec` needs
    to decide, and the two words below are the private ones. -/
def FUTEX_WAIT : Int := 0
def FUTEX_WAKE : Int := 1
def FUTEX_PRIVATE_FLAG : Int := 128
def FUTEX_WAIT_PRIVATE : Int := z_lor FUTEX_WAIT FUTEX_PRIVATE_FLAG
def FUTEX_WAKE_PRIVATE : Int := z_lor FUTEX_WAKE FUTEX_PRIVATE_FLAG

/-- The width of a futex word, in bytes.

    `futex_size` (kernel/futex/futex.h) is `1 << (flags &
    FLAGS_SIZE_MASK)`, and `futex_to_flags` hands the legacy `futex`
    entry point `FLAGS_SIZE_32` unconditionally — the size bits come
    only from the `futex2` flag word, which reaches the kernel through
    `futex_waitv` / `futex_wake` / `futex_wait`, the numbers 449, 454
    and 455, none of which has an arm here.  `futex_flags_valid` refuses
    anything but `FLAGS_SIZE_32` anyway ("Only 32bit futexes are
    implemented -- for now").  So 4 is the width for every call this
    spec can see, and it is the width of BOTH things `get_futex_key`
    uses it for: the alignment the address must have, and the length
    `access_ok` is given. -/
def FUTEX_WORD_SIZE : Int := 4

/-- `__NEW_UTS_LEN`, the length of a `struct new_utsname` field WITHOUT
    its terminator (include/uapi/linux/utsname.h,
    `#define __NEW_UTS_LEN 64`, Linux v6.18.46, commit 1f99e9ab748f).
    Every one of the struct's six members is declared
    `char field[__NEW_UTS_LEN + 1]`, so the field a `uname` (160) copies
    out is 65 bytes wide and the string in it is at most 64 characters.
    `Kernel.Sys.uname_spec` reads it as the field stride; the +1 is what
    guarantees a terminator inside the field, which is the one thing that
    spec asserts about the four members it does not pin. -/
def NEW_UTS_LEN : Int := 64

/-- `sizeof(struct new_utsname)`: six 65-byte `char` arrays, so 390 bytes
    with no padding anywhere — a struct of `char` arrays has alignment 1
    (include/uapi/linux/utsname.h, `struct new_utsname`, Linux v6.18.46,
    commit 1f99e9ab748f).  This is the width of the SINGLE
    `copy_to_user(name, &tmp, sizeof(tmp))` in
    `SYSCALL_DEFINE1(newuname)` (kernel/sys.c), which is why
    `Kernel.Sys.uname_spec` gates one range of exactly this size rather
    than six.

    The member order is fixed by the same declaration and the spec
    depends on it: `sysname`, `nodename`, `release`, `version`,
    `machine`, `domainname`, at offsets 0, 65, 130, 195, 260 and 325. -/
def NEW_UTSNAME_SIZE : Int := 390

/-- `PR_CAPBSET_READ`, the one `prctl` option this model answers
    (include/uapi/linux/prctl.h, Linux v6.18.46, commit 1f99e9ab748f).
    It is NOT handled in kernel/sys.c's own `switch`: the LSM hook
    `security_task_prctl` runs first, and capability's implementation of
    it -- `cap_task_prctl` (security/commoncap.c) -- answers this option
    and returns before the syscall body's `switch` is reached.  See
    `Kernel.Sys.prctl_spec`, which is where the whole argument lives. -/
def PR_CAPBSET_READ : Int := 23

/-- `CAP_LAST_CAP`, the highest capability number the kernel recognises:
    `CAP_CHECKPOINT_RESTORE`, 40 (include/uapi/linux/capability.h, Linux
    v6.18.46, commit 1f99e9ab748f).  `cap_valid`, defined in the same
    header as `((x) >= 0 && (x) <= CAP_LAST_CAP)`, is what
    `cap_task_prctl` tests `PR_CAPBSET_READ`'s `arg2` against, and it is
    the ONLY thing separating the option's answer from -EINVAL.

    A VERSION FACT, and the narrowest claim in `Kernel.Sys.prctl_spec`:
    40 has been the last capability since v5.9 added
    `CAP_CHECKPOINT_RESTORE`, and a kernel that adds a 41st moves the
    -EINVAL boundary this model pins.  That is the same standing pin
    every other constant here carries, stated because the boundary is
    what programs SEARCH FOR -- libcap's `cap_max_bits` binary-searches
    it -- so it is read by real code rather than merely available. -/
def CAP_LAST_CAP : Int := 40

/-! ## `struct stat`, as fstat (80) and newfstatat (79) copy it out -/

/-- `sizeof(struct stat)` on riscv64.  riscv64 has no `asm/stat.h` of
    its own, so it takes the generic 64-bit layout
    (include/uapi/asm-generic/stat.h, Linux v6.18.46, commit
    1f99e9ab748f), whose members and offsets are

      unsigned long  st_dev         0
      unsigned long  st_ino         8
      unsigned int   st_mode       16
      unsigned int   st_nlink      20
      unsigned int   st_uid        24
      unsigned int   st_gid        28
      unsigned long  st_rdev       32
      unsigned long  __pad1        40
      long           st_size       48
      int            st_blksize    56
      int            __pad2        60
      long           st_blocks     64
      long           st_atime      72
      unsigned long  st_atime_nsec 80
      long           st_mtime      88
      unsigned long  st_mtime_nsec 96
      long           st_ctime     104
      unsigned long  st_ctime_nsec 112
      unsigned int   __unused4    120
      unsigned int   __unused5    124

    ALL 128 BYTES ARE DELIVERED, padding included.  `cp_new_stat`
    (fs/stat.c) zeroes its stack copy through `INIT_STRUCT_STAT_PADDING`
    — which riscv64 leaves at the generic `memset`, only x86 overriding
    it — fills the members above, and hands the whole struct to a single
    `copy_to_user`. -/
def STAT_SIZE : Int := 128

/-- Member offsets this file's predicates read.  Named rather than
    written inline because three of them are read twice, and because a
    layout error is the one mistake a reader cannot see in a numeral. -/
def ST_MODE_OFF : Nat := 16
def ST_RDEV_OFF : Nat := 32
def ST_PAD1_OFF : Nat := 40
def ST_SIZE_OFF : Nat := 48
def ST_BLKSIZE_OFF : Nat := 56
def ST_PAD2_OFF : Nat := 60
def ST_BLOCKS_OFF : Nat := 64
def ST_UNUSED45_OFF : Nat := 120

/-- One little-endian member of a delivered `struct stat`, as the
    unsigned value of its `n` bytes at `off`.  riscv64 is
    little-endian, and every member above is a plain integer, so a
    member is exactly this.  A short buffer reads as the value of what
    bytes are there — the length is checked separately, by
    `stat_buf_wf`. -/
def stat_field_le (off n : Nat) (bs : List byte) : Int :=
  bytes_le_to_Z ((bs.drop off).take n)

/-- `S_IFMT` and the seven file types it selects
    (include/uapi/linux/stat.h, Linux v6.18.46, commit 1f99e9ab748f).
    `S_IFMT` is the mask; the seven values below are every type the mask
    can hold, and an inode always has exactly one of them —
    `inode_init_always` (fs/inode.c) is reached only through an
    allocation that a filesystem then gives a type, and every
    `init_special_inode`/`d_instantiate` path sets one. -/
def S_IFMT : Int := 61440    -- 0170000
def S_IFSOCK : Int := 49152  -- 0140000
def S_IFLNK : Int := 40960   -- 0120000
def S_IFREG : Int := 32768   -- 0100000
def S_IFBLK : Int := 24576   -- 0060000
def S_IFDIR : Int := 16384   -- 0040000
def S_IFCHR : Int := 8192    -- 0020000
def S_IFIFO : Int := 4096    -- 0010000

/-- The `S_IFMT` bits of a delivered `struct stat`'s `st_mode`. -/
def stat_ifmt (bs : List byte) : Int :=
  z_land (stat_field_le ST_MODE_OFF 4 bs) S_IFMT

/-- Whether the kernel called the object a REGULAR FILE.  This is a
    question ABOUT THE ANSWER, not a claim by the model: the model does
    not know a path's type, and `Fs.Stat.fstat_spec` uses this only to
    decide whether its `st_size` obligation applies. -/
def stat_is_reg (bs : List byte) : Bool :=
  stat_ifmt bs == S_IFREG

/-- Whether `st_mode` names one of the seven types at all.  An
    all-zero `st_mode` is not one of them, which is what makes an
    all-zero `struct stat` — the shape a kernel that wrote nothing but
    claimed to have written would produce — inadmissible. -/
def stat_ifmt_valid (bs : List byte) : Bool :=
  let t := stat_ifmt bs
  (t == S_IFSOCK || t == S_IFLNK || t == S_IFREG || t == S_IFBLK
   || t == S_IFDIR || t == S_IFCHR || t == S_IFIFO)

/-- THE ENVELOPE EVERY DELIVERED `struct stat` MUST FALL IN, and it is
    everything `cp_new_stat` settles without consulting the inode:

    - the width is exactly `STAT_SIZE`, the single `copy_to_user`'s;
    - `__pad1`, `__pad2` and `__unused4`/`__unused5` are ZERO, because
      `INIT_STRUCT_STAT_PADDING` cleared the whole struct and no member
      assignment covers those bytes.  This is the part of the answer the
      model knows EXACTLY rather than nondeterministically, and it is
      what makes a poisoned or invented buffer rejectable;
    - `st_mode` names one of the seven file types.

    Nothing else is claimed here.  Which type it is, the permission
    bits, the ids, the inode, the device, the link count, the block
    size, the block count and the three timestamps are the environment's
    (see `Fs.Stat.fstat_spec`). -/
def stat_buf_wf (bs : List byte) : Bool :=
  (bs.length == 128
   && stat_ifmt_valid bs
   && stat_field_le ST_PAD1_OFF 8 bs == 0
   && stat_field_le ST_PAD2_OFF 4 bs == 0
   && stat_field_le ST_UNUSED45_OFF 8 bs == 0)

/-- THE ONE MEMBER THE MODEL DERIVES, and it is derived CONDITIONALLY.

    For a regular file `st_size` is the file's length: `generic_fillattr`
    (fs/stat.c) copies `inode->i_size` into `stat->size` and
    `cp_new_stat` copies that to `tmp.st_size`, and for a regular file
    `i_size` is the number of bytes the file holds — which, for a path
    this model resolves, is the length of the byte list `Fs` carries.
    THAT PREMISE IS THE ONE `ReadWrite.read_spec` ALREADY MAKES, and no
    more: it is a claim about regular files, and the implication below
    is how it is stated without extending it.

    The implication is what keeps the arm from FALSELY REJECTING.
    A path the model
    resolves can be one Linux calls a character device, where the true answer
    is S_IFCHR with `st_size` 0 while the model's byte list is not
    empty.  Asserting S_IFREG, or asserting the length unconditionally,
    rejects that conforming trace.  Under the implication the model
    simply says nothing about it, and still says something sharp about
    every file that really is regular.

    THE COMPARISON WRAPS AT 2^64, because `stat_field_le` reads eight
    bytes and a `list byte`'s length is an unbounded `Nat`.  A file that
    long is not constructible here — every write is bounded by
    `State.max_rw_count` and the initial image is a run input — so the
    wrap is unreachable rather than an approximation; it is written this
    way so the predicate is TOTAL, which is what
    `Checks.Witness.Fs.Stat`'s witness needs on the pinned branch.

  `implb b c` is Lean's `!b || c`. -/
def stat_size_ok (n : Nat) (bs : List byte) : Bool :=
  !(stat_is_reg bs) ||
    (stat_field_le ST_SIZE_OFF 8 bs == (BitVec.ofInt 64 (n : Int)).toNat)

/-- THE MEMBERS A `struct stat` OF /dev/null CARRIES FROM THE
    KERNEL, asserted outright rather than under an implication: the
    device is known to be a device, which is what the regular-file arm
    cannot say of a key.  `cp_new_stat` (fs/stat.c, Linux v6.18.46)
    copies what `generic_fillattr` read off the inode: `st_mode`'s type
    bits are S_IFCHR because `init_special_inode` (fs/inode.c) set them
    when the node was made; `st_rdev` is `new_encode_dev` of
    `MKDEV(1, 3)` (include/linux/kdev_t.h) — `(3 & 0xff) | (1 << 8)` —
    which is `DEVNULL_RDEV`; `st_size` is `i_size`, 0 on a device
    inode nothing ever wrote through (`write_null` returns without
    touching the inode, drivers/char/mem.c), and `st_blocks` is
    `i_blocks`, 0 for the same reason.  The two zeros are a consequence
    of the environment premise rather than a kernel invariant: a node
    made by mknod or devtmpfs and never resized carries them, and a
    crafted inode could carry another.

    NOT asserted here, and chosen once per descriptor by
    `Fs.Stat.fstat_devnull_spec`'s pin like every other member: the
    permission bits and the owner, which are the image's node's
    (devtmpfs takes 0666 and root from `mem_devnode`, drivers/char/mem.c,
    but a container runtime makes its own node), the link count, the
    device and inode numbers, the block size and the timestamps. -/
def DEVNULL_RDEV : Int := 259

/-- The members a `struct stat` of ANY of the model's character
    devices carries from the kernel, parameterised by the device
    number: `stat_devnull_ok` and `stat_urandom_ok` are its two
    instances, and the argument above is the argument for both. -/
def stat_chrdev_ok (rdev : Int) (bs : List byte) : Bool :=
  (stat_ifmt bs == S_IFCHR
   && stat_field_le ST_RDEV_OFF 8 bs == rdev
   && stat_field_le ST_SIZE_OFF 8 bs == 0
   && stat_field_le ST_BLOCKS_OFF 8 bs == 0)

def stat_devnull_ok (bs : List byte) : Bool := stat_chrdev_ok DEVNULL_RDEV bs

/-- /dev/urandom's `st_rdev`: `new_encode_dev` of `MKDEV(1, 9)`
    (include/linux/kdev_t.h, v6.18.46) — `(9 & 0xff) | (1 << 8)`.  The
    zero `st_size` and `st_blocks` rest on the same environment
    premise the null device's do — a node made by mknod or devtmpfs
    and never resized; `random_write_iter` mixes into the pool and
    touches no inode member (drivers/char/random.c). -/
def URANDOM_RDEV : Int := 265

def stat_urandom_ok (bs : List byte) : Bool := stat_chrdev_ok URANDOM_RDEV bs

/-- Byte-list equality, for comparing a delivered `struct stat` against
    a pin.  `Fs.path_eqb` is the same function over the same type; a
    second name is used because these bytes are not a path, and
    `Checks.Sys.Prelude.listN_eqb` is not visible from a spec file. -/
def stat_bytes_eqb : List byte → List byte → Bool
  | [], [] => true
  | a :: r1, b :: r2 => bv_eqb a b && stat_bytes_eqb r1 r2
  | _, _ => false

theorem stat_bytes_eqb_eq : ∀ (l1 l2 : List byte), stat_bytes_eqb l1 l2 = true ↔ l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2
    cases l2 with
    | nil => simp [stat_bytes_eqb]
    | cons b r2 => simp [stat_bytes_eqb]
  | cons a r1 ih =>
    intro l2
    cases l2 with
    | nil => simp [stat_bytes_eqb]
    | cons b r2 =>
      simp only [stat_bytes_eqb, Bool.and_eq_true, bv_eqb_eq, ih]
      constructor
      · rintro ⟨rfl, rfl⟩
        rfl
      · intro h
        exact List.cons.inj h

theorem stat_bytes_eqb_refl : ∀ l : List byte, stat_bytes_eqb l l = true := by
  intro l
  exact (stat_bytes_eqb_eq l l).mpr rfl

/-- THE MEMBERS THAT MAY NOT CHANGE UNDER A RUN, so that two `fstat`s of
    one file cannot disagree about which file it is.  Bytes 0..47 —
    `st_dev`, `st_ino`, `st_mode`, `st_nlink`, `st_uid`, `st_gid`,
    `st_rdev` and `__pad1` — and bytes 56..63, `st_blksize` and
    `__pad2`.

    WHY THESE AND NOT THE REST.  Each of the eight is settled by the
    inode or by its superblock, and no syscall in
    `Sys.SyscallTable.spec_table` moves one: there is no `chmod`/`fchmod`
    arm for the permission bits, no `chown` arm for the ids, no
    `link`/`linkat` arm for the link count, and a type, an inode number,
    a device and a block size do not change at all while the inode
    lives.  `unlinkat` (35) IS modeled and DOES drop `st_nlink`, but it
    also removes the key, and `Fs.Stat.fstat_spec` declines a descriptor
    whose path `Fs` no longer holds, so no `fstat` observes the drop.

    WHAT IS DELIBERATELY LEFT FREE: `st_size` (which `write` and
    `ftruncate` move, and which `stat_size_ok` constrains instead),
    `st_blocks` (which moves with it, and is the filesystem's own
    allocation rather than a function of the length — a sparse file has
    fewer), and the three timestamp pairs (which every read and write
    moves).  Requiring any of those to repeat would reject a conforming
    trace.  The three besides `st_size` are then unconstrained ACROSS
    calls, which admits a run Linux would not produce.  That is a
    known over-approximation. -/
def stat_stable_eqb (b1 b2 : List byte) : Bool :=
  (stat_bytes_eqb (b1.take ST_PAD1_OFF) (b2.take ST_PAD1_OFF)
   && stat_bytes_eqb ((b1.drop ST_PAD1_OFF).take 8) ((b2.drop ST_PAD1_OFF).take 8)
   && stat_bytes_eqb ((b1.drop ST_BLKSIZE_OFF).take 8) ((b2.drop ST_BLKSIZE_OFF).take 8))

theorem stat_stable_eqb_refl : ∀ b : List byte, stat_stable_eqb b b = true := by
  intro b
  simp [stat_stable_eqb, stat_bytes_eqb_refl]

/-- TWO SLICES OF A DELIVERED `struct stat` READ THE SAME out of two
    buffers that agree on the region they fall in: wholly inside the
    first 48 bytes, or wholly at or past 56.  Those two regions are
    exactly what `stat_stable_eqb` compares and where every member
    `stat_buf_wf` looks at lives, so these two carry both predicates
    across a change confined to bytes 48..55. -/

theorem stat_slice_head {off k : Nat} {x y : List byte}
    (hb : off + k ≤ 48) (heq : x.take 48 = y.take 48) :
    (x.drop off).take k = (y.drop off).take k := by
  have h : ∀ z : List byte, (z.drop off).take k = ((z.take 48).drop off).take k := by
    intro z
    rw [List.take_drop, List.take_drop]
    have h1 : z.take (off + k) = (z.take 48).take (off + k) := by
      rw [List.take_take, Nat.min_eq_left hb]
    rw [h1]
  rw [h x, h y, heq]

theorem stat_slice_tail {off k : Nat} {x y : List byte}
    (hb : 56 ≤ off) (heq : x.drop 56 = y.drop 56) :
    (x.drop off).take k = (y.drop off).take k := by
  have h : ∀ z : List byte, z.drop off = (z.drop 56).drop (off - 56) := by
    intro z
    rw [List.drop_drop, show 56 + (off - 56) = off by omega]
  rw [h x, h y, heq]

theorem stat_field_le_head {off k : Nat} {x y : List byte}
    (hb : off + k ≤ 48) (heq : x.take 48 = y.take 48) :
    stat_field_le off k x = stat_field_le off k y := by
  unfold stat_field_le
  rw [stat_slice_head hb heq]

theorem stat_field_le_tail {off k : Nat} {x y : List byte}
    (hb : 56 ≤ off) (heq : x.drop 56 = y.drop 56) :
    stat_field_le off k x = stat_field_le off k y := by
  unfold stat_field_le
  rw [stat_slice_tail hb heq]

/-- THE SAME `struct stat` WITH A DIFFERENT `st_size`.  A file that is
    statted twice with a write in between must answer with the same
    device, inode, mode, link count, ids and block size and a NEW
    length, and this is one buffer that does: it exists so
    `Checks.Witness.Fs.Stat` can name an admissible answer on the pinned
    branch of `Fs.Stat.fstat_spec` without inventing the members the pin
    fixes.  It is not itself a claim about Linux — the spec CHOOSES from
    a set this is one member of, and the timestamps and `st_blocks` it
    copies over unchanged are exactly the members a real kernel would
    have moved. -/
def stat_set_size (n : Nat) (bs : List byte) : List byte :=
  bs.take 48 ++ Z_to_le_bytes 8 (n : Int) ++ bs.drop 56

theorem stat_set_size_head (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    (stat_set_size n bs).take 48 = bs.take 48 := by
  unfold stat_set_size
  rw [List.append_assoc]
  rw [List.take_left' (by rw [List.length_take, Nat.min_eq_left hlen])]

theorem stat_set_size_tail (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    (stat_set_size n bs).drop 56 = bs.drop 56 := by
  unfold stat_set_size
  rw [List.drop_append]
  have h1 : (bs.take 48 ++ Z_to_le_bytes 8 (n : Int)).length = 56 := by
    simp [List.length_take, length_Z_to_le_bytes, Nat.min_eq_left hlen]
  rw [h1, show 56 - 56 = 0 by omega, List.drop_zero]
  rw [List.drop_append, List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
  rw [List.length_take, Nat.min_eq_left hlen]
  rw [show 56 - 48 = 8 by omega, List.drop_of_length_le (by simp [length_Z_to_le_bytes])]
  simp

theorem stat_set_size_field (n : Nat) (bs : List byte) (hlen : 48 ≤ bs.length) :
    ((stat_set_size n bs).drop 48).take 8 = Z_to_le_bytes 8 (n : Int) := by
  unfold stat_set_size
  rw [List.drop_append]
  have h1 : (bs.take 48 ++ Z_to_le_bytes 8 (n : Int)).length = 56 := by
    simp [List.length_take, length_Z_to_le_bytes, Nat.min_eq_left hlen]
  rw [h1, show 48 - 56 = 0 by omega, List.drop_zero]
  rw [List.drop_append, List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
  rw [List.length_take, Nat.min_eq_left hlen]
  rw [show 48 - 48 = 0 by omega, List.drop_zero, List.nil_append]
  rw [List.take_left' (l₁ := Z_to_le_bytes 8 (n : Int)) (by simp [length_Z_to_le_bytes])]

theorem stat_set_size_length (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    (stat_set_size n bs).length = 128 := by
  unfold stat_set_size
  rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      <- hlen, length_Z_to_le_bytes]
  omega

theorem stat_set_size_wf (n : Nat) (bs : List byte) (H : stat_buf_wf bs = true) :
    stat_buf_wf (stat_set_size n bs) = true := by
  have hlen : bs.length = 128 := by
    by_cases h : bs.length = 128
    · exact h
    · have hb : (bs.length == 128) = false := by simp [h]
      have h' := H
      unfold stat_buf_wf at h'
      simp only [hb, Bool.false_and] at h'
      exact absurd h' (by decide)
  have hhead := stat_set_size_head n bs (by omega)
  have htail := stat_set_size_tail n bs (by omega)
  have hifmt : stat_ifmt (stat_set_size n bs) = stat_ifmt bs := by
    unfold stat_ifmt
    rw [stat_field_le_head (off := ST_MODE_OFF) (k := 4) (by decide) hhead]
  have hp1 : stat_field_le ST_PAD1_OFF 8 (stat_set_size n bs)
      = stat_field_le ST_PAD1_OFF 8 bs :=
    stat_field_le_head (off := ST_PAD1_OFF) (k := 8) (by decide) hhead
  have hp2 : stat_field_le ST_PAD2_OFF 4 (stat_set_size n bs)
      = stat_field_le ST_PAD2_OFF 4 bs :=
    stat_field_le_tail (off := ST_PAD2_OFF) (k := 4) (by decide) htail
  have hp3 : stat_field_le ST_UNUSED45_OFF 8 (stat_set_size n bs)
      = stat_field_le ST_UNUSED45_OFF 8 bs :=
    stat_field_le_tail (off := ST_UNUSED45_OFF) (k := 8) (by decide) htail
  have goal_eq : stat_buf_wf (stat_set_size n bs) = stat_buf_wf bs := by
    unfold stat_buf_wf stat_ifmt_valid
    rw [stat_set_size_length n bs hlen, hlen, hifmt, hp1, hp2, hp3]
  rw [goal_eq]
  exact H

theorem stat_set_size_stable (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    stat_stable_eqb (stat_set_size n bs) bs = true := by
  have hhead := stat_set_size_head n bs (by omega)
  have htail := stat_set_size_tail n bs (by omega)
  have h40 : (stat_set_size n bs).take 40 = bs.take 40 := by
    have h := stat_slice_head (off := 0) (k := 40)
      (x := stat_set_size n bs) (y := bs) (by decide) hhead
    simpa using h
  have h4048 : ((stat_set_size n bs).drop 40).take 8 = (bs.drop 40).take 8 :=
    stat_slice_head (off := 40) (k := 8) (x := stat_set_size n bs) (y := bs)
      (by decide) hhead
  have h56 : ((stat_set_size n bs).drop 56).take 8 = (bs.drop 56).take 8 :=
    stat_slice_tail (off := 56) (k := 8) (x := stat_set_size n bs) (y := bs)
      (by decide) htail
  unfold stat_stable_eqb
  rw [ST_PAD1_OFF, ST_BLKSIZE_OFF, h40, h4048, h56]
  simp [stat_bytes_eqb_refl]

/-! ### The byte round trip that `stat_set_size_size_ok` needs

  proof ends with `bytes_le_to_Z_of_le_bytes`, which `BvBase.lean` proves from the
  `Nat` byte recursion, and the `Nat` round trip it rests on
  (`bytes_le_to_Nat_Z_to_le_bytes`) is public there too, so this file cites it
  rather than restating it.  The two `Nat` limb lemmas below (`mod_mul_256_of`,
  `mod_mul_256`) are the modular arithmetic a byte step normalises with. -/

/-- One limb of the modulus arithmetic below. -/
theorem mod_mul_256_of (q r M : Nat) (hr : r < 256) (hM : 0 < M) :
    (256 * q + r) % (256 * M) = 256 * (q % M) + r := by
  have hqM : q % M < M := Nat.mod_lt _ hM
  have hrM : r < 256 * M := by omega
  rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt (by omega)]

theorem mod_mul_256 (x M : Nat) (hM : 0 < M) :
    x % (256 * M) = 256 * ((x / 256) % M) + x % 256 := by
  have h := mod_mul_256_of (x / 256) (x % 256) M (Nat.mod_lt _ (by decide)) hM
  rwa [Nat.div_add_mod] at h

-- `Z_to_le_bytes`'s shift and low-byte read are the canonical
-- `BvBase.int_shiftRight_8_natCast` and `BvBase.toNat_ofInt_8_nat`; the
-- round trip below rewrites with them rather than restating them.

theorem stat_set_size_size_ok (n : Nat) (bs : List byte) (hlen : bs.length = 128) :
    stat_size_ok n (stat_set_size n bs) = true := by
  have hfield : stat_field_le ST_SIZE_OFF 8 (stat_set_size n bs)
      = bytes_le_to_Z (Z_to_le_bytes 8 (n : Int)) := by
    unfold stat_field_le
    rw [ST_SIZE_OFF, stat_set_size_field n bs (by omega)]
  have htrunc : (BitVec.ofInt 64 (n : Int)).toNat = n % 2 ^ 64 := by
    rw [BitVec.toNat_ofInt, Int.toNat_emod (Int.natCast_nonneg n) (by decide)]
    simp
  unfold stat_size_ok
  rw [hfield, htrunc]
  cases hreg : stat_is_reg (stat_set_size n bs) with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    unfold bytes_le_to_Z
    rw [bytes_le_to_Nat_Z_to_le_bytes]
    rw [show 8 * 8 = 64 from rfl]
    exact beq_self_eq_true _

theorem stat_buf_wf_length (bs : List byte) (H : stat_buf_wf bs = true) :
    bs.length = 128 := by
  by_cases h : bs.length = 128
  · exact h
  · have hb : (bs.length == 128) = false := by simp [h]
    have h' := H
    unfold stat_buf_wf at h'
    simp only [hb, Bool.false_and] at h'
    exact absurd h' (by decide)

/-! ## Sanity checks

    reflexivity` goals. An offset or a little-endian read is exactly the kind of
    mistake that typechecks, so both are pinned on literal bytes below. -/

section

-- `decide` on a 128-element list exceeds the default reduction-depth
-- budget; the checks themselves are small, so only the budget moves, and
-- only for this section.
set_option maxRecDepth 10000

/-! ### The two's-complement ABI words -/

/-- `AT_FDCWD` is -100, and its 32-bit image is 2^32 - 100. -/
example : AT_FDCWD.toInt = -100 := by decide
example : AT_FDCWD32.toNat = 4294967196 := by decide
/-- `fd32` ZERO-extends: only the low half of the register survives. -/
example : fd32 (BitVec.ofInt 64 (2 ^ 32 + 5)) = 5 := by decide
example : fd32 (BitVec.ofInt 64 (-1)) = 4294967295 := by decide
/-- `(uid_t)-1` after the `uid32` narrowing. -/
example : ID_MINUS_ONE.toNat = 4294967295 := by decide
example : fd32 ID_MINUS_ONE = ID_MINUS_ONE := by decide

/-! ### Open, socket, clock and ioctl constants -/

example : O_WRONLY = 1 := by decide
example : O_RDWR = 2 := by decide
example : O_CREAT = 64 := by decide
example : O_EXCL = 128 := by decide
example : O_TRUNC = 512 := by decide
example : O_CLOEXEC = 524288 := by decide
example : O_LARGEFILE = 32768 := by decide
example : O_NONBLOCK = 2048 := by decide
example : O_DIRECTORY = 65536 := by decide
example : O_APPEND = 1024 := by decide
example : FASYNC = 8192 := by decide
example : O_DIRECT = 16384 := by decide
example : O_NOATIME = 262144 := by decide
/-- `TFD_CREATE_FLAGS` is `O_CLOEXEC | O_NONBLOCK`, and `EFD_FLAGS_SET` is
    that mask WIDENED BY ONE BIT — the difference the file's comment turns on. -/
example : TFD_CREATE_FLAGS = 526336 := by decide
example : EFD_FLAGS_SET = 526337 := by decide
example : EFD_FLAGS_SET = TFD_CREATE_FLAGS + EFD_SEMAPHORE := by decide
example : SOCK_CLOEXEC = O_CLOEXEC := by decide
example : SOCK_NONBLOCK = O_NONBLOCK := by decide
example : AF_INET = 2 := by decide
example : NPROTO = 46 := by decide
example : SOCK_STREAM = 1 := by decide
example : SOCK_MAX = 11 := by decide
example : SOCK_TYPE_MASK = 15 := by decide
example : IPPROTO_MAX = 263 := by decide
example : SOCKADDR_STORAGE_SIZE = 128 := by decide
example : SA_FAMILY_SIZE = 2 := by decide
example : SOCKADDR_IN_SIZE = 16 := by decide
example : SHUT_RDWR = 2 := by decide
example : SEEK_MAX = 4 := by decide
example : MAP_FIXED_NOREPLACE = 1048576 := by decide
example : MREMAP_MAYMOVE = 1 := by decide
example : MADV_DONTNEED = 4 := by decide
example : LOCK_MAND = 32 := by decide
example : RLIMIT_CORE = 4 := by decide
example : CLOCK_MONOTONIC = 1 := by decide
example : CLOCK_BOOTTIME = 7 := by decide
example : SS_ONSTACK = 1 := by decide
example : SS_DISABLE = 2 := by decide
example : SS_AUTODISARM = 0x80000000 := by decide
example : SCHED_RESET_ON_FORK = 0x40000000 := by decide
example : MAX_RT_PRIO = 100 := by decide
example : CLONE_VM = 256 := by decide
example : FUTEX_PRIVATE_FLAG = 128 := by decide
example : FUTEX_WAIT_PRIVATE = 128 := by decide
example : FUTEX_WAKE_PRIVATE = 129 := by decide
example : FUTEX_WORD_SIZE = 4 := by decide
example : NEW_UTS_LEN = 64 := by decide
example : NEW_UTSNAME_SIZE = 390 := by decide
example : PR_CAPBSET_READ = 23 := by decide
example : CAP_LAST_CAP = 40 := by decide
example : NAME_MAX = 255 := by decide
example : NSEC_PER_SEC = 1000000000 := by decide
example : kernel_sigset_bytes = 8 := by decide
example : NSIG_BYTES = 8 := by decide
example : kernel_sigset_bytes = NSIG_BYTES := by decide
example : SIG_BLOCK = 0 := by decide
example : SIG_SETMASK = 2 := by decide
example : MINSIGSTKSZ = 2048 := by decide
example : WNOHANG = 1 := by decide
example : MSG_CMSG_COMPAT = 0x80000000 := by decide
example : NR_OPEN_DEFAULT = 64 := by decide
example : NGROUPS_MAX = 65536 := by decide

/-- The two `ktime_t` bounds and the range they bound: `KTIME_MAX` is one
    nanosecond below `CLOCK_NS_ENVELOPE`, and `KTIME_SEC_MAX` is
    `(2^63 - 1) / 10^9` — NOT the largest whole second under the
    envelope, which is the very confusion `timespec_ktime` transcribes. -/
example : CLOCK_NS_ENVELOPE = 2 ^ 63 := by decide
example : KTIME_MAX = 2 ^ 63 - 1 := by decide
example : KTIME_MAX = CLOCK_NS_ENVELOPE - 1 := by decide
example : KTIME_SEC_MAX = (2 ^ 63 - 1) / 1000000000 := by decide
example : KTIME_SEC_MAX = 9223372036 := by decide

/-- The eight ioctl request words, as `word`s, carry their asm-generic values. -/
example : TCGETS.toNat = 21505 := by decide
example : TCSETS.toNat = 21506 := by decide
example : TIOCSCTTY.toNat = 21518 := by decide
example : TIOCGWINSZ.toNat = 21523 := by decide
example : TIOCSWINSZ.toNat = 21524 := by decide
example : TIOCNOTTY.toNat = 21538 := by decide
example : TIOCGPTN.toNat = 2147767344 := by decide
example : TIOCSPTLCK.toNat = 1074025521 := by decide
example : F_GETFD.toNat = 1 := by decide
example : F_SETFL.toNat = 4 := by decide

/-- The three fixed paths, byte by byte. -/
example : dot_path.map BitVec.toNat = [46] := by decide
example : devnull_path.map BitVec.toNat = [47, 100, 101, 118, 47, 110, 117, 108, 108] := by decide
example : urandom_path.map BitVec.toNat
    = [47, 100, 101, 118, 47, 117, 114, 97, 110, 100, 111, 109] := by decide
example : devnull_path.length = 9 := by decide
example : urandom_path.length = 12 := by decide

/-! ### `struct stat`: the layout -/

/-- Every offset in the delivered layout, and the width they add up to. -/
example : STAT_SIZE = 128 := by decide
example : ST_MODE_OFF = 16 := by decide
example : ST_RDEV_OFF = 32 := by decide
example : ST_PAD1_OFF = 40 := by decide
example : ST_SIZE_OFF = 48 := by decide
example : ST_BLKSIZE_OFF = 56 := by decide
example : ST_PAD2_OFF = 60 := by decide
example : ST_BLOCKS_OFF = 64 := by decide
example : ST_UNUSED45_OFF = 120 := by decide
example : ST_MODE_OFF + 4 = 20 := by decide
example : ST_UNUSED45_OFF + 8 = STAT_SIZE := by decide

/-- The file-type mask: every `S_IF*` value is inside `S_IFMT`, and the
    seven are distinct. -/
example : S_IFMT = 0o170000 := by decide
example : S_IFSOCK = 0o140000 := by decide
example : S_IFLNK = 0o120000 := by decide
example : S_IFREG = 0o100000 := by decide
example : S_IFBLK = 0o060000 := by decide
example : S_IFDIR = 0o040000 := by decide
example : S_IFCHR = 0o020000 := by decide
example : S_IFIFO = 0o010000 := by decide
example : z_lor (z_lor S_IFSOCK S_IFLNK) (z_lor S_IFREG S_IFBLK)
    = 0o160000 := by decide
example : z_land S_IFREG S_IFMT = S_IFREG := by decide
example : z_land S_IFCHR S_IFMT = S_IFCHR := by decide
/-- The two character devices' `new_encode_dev` images: major 1, minor 3
    and 9. -/
example : DEVNULL_RDEV = (1 : Int) * 256 + 3 := by decide
example : URANDOM_RDEV = (1 : Int) * 256 + 9 := by decide

/-! ### A concrete `struct stat`, decoded field by field -/

/-- A concrete delivered `struct stat`: a regular file, mode `0100644`,
    device 0, size 5, block size 4096, 8 blocks, timestamps and padding
    zero.  Written as literal bytes rather than through `Z_to_le_bytes`,
    so that the checks below do not lean on the encoder they validate.

    `private`, like the two fixtures below: they are test data, not part
    of the module's interface. -/
private def statExample : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0]                   -- 0   st_dev
  ++ [1, 0, 0, 0, 0, 0, 0, 0]                -- 8   st_ino = 1
  ++ [0xa4, 0x81, 0, 0]                      -- 16  st_mode = 0100644
  ++ [1, 0, 0, 0]                            -- 20  st_nlink = 1
  ++ [0, 0, 0, 0]                            -- 24  st_uid
  ++ [0, 0, 0, 0]                            -- 28  st_gid
  ++ [0, 0, 0, 0, 0, 0, 0, 0]                -- 32  st_rdev
  ++ [0, 0, 0, 0, 0, 0, 0, 0]                -- 40  __pad1
  ++ [5, 0, 0, 0, 0, 0, 0, 0]                -- 48  st_size = 5
  ++ [0, 0x10, 0, 0]                         -- 56  st_blksize = 4096
  ++ [0, 0, 0, 0]                            -- 60  __pad2
  ++ [8, 0, 0, 0, 0, 0, 0, 0]                -- 64  st_blocks = 8
  ++ List.replicate 56 0                     -- 72  the three timestamps

/-- A concrete `struct stat` of a character device: mode `020666`,
    `st_rdev` 259 (major 1, minor 3), size 0, blocks 0 — the shape
    `stat_devnull_ok` admits. -/
private def devnullStatExample : List byte :=
  List.replicate 16 0                        -- 0   st_dev, st_ino
  ++ [0xb6, 0x21, 0, 0]                      -- 16  st_mode = 020666
  ++ List.replicate 12 0                     -- 20  st_nlink, st_uid, st_gid
  ++ [3, 1, 0, 0, 0, 0, 0, 0]                -- 32  st_rdev = 259
  ++ List.replicate 88 0                     -- 40  the rest

example : statExample.length = 128 := by decide
example : devnullStatExample.length = 128 := by decide
example : stat_buf_wf statExample = true := by decide
example : stat_buf_wf devnullStatExample = true := by decide
example : ¬ (stat_buf_wf (List.replicate 128 0) = true) := by decide

/-- Little-endian field reads at the named offsets. -/
example : stat_field_le ST_MODE_OFF 4 statExample = 33188 := by decide
example : stat_field_le ST_SIZE_OFF 8 statExample = 5 := by decide
example : stat_field_le ST_BLKSIZE_OFF 8 statExample = 4096 := by decide
example : stat_field_le ST_BLOCKS_OFF 8 statExample = 8 := by decide
example : stat_field_le ST_PAD1_OFF 8 statExample = 0 := by decide
example : stat_field_le ST_RDEV_OFF 8 devnullStatExample = 259 := by decide
example : stat_field_le ST_SIZE_OFF 8 devnullStatExample = 0 := by decide
example : stat_field_le ST_BLOCKS_OFF 8 devnullStatExample = 0 := by decide

/-- The type predicates read `st_mode`'s mask bits, not the whole word. -/
example : stat_ifmt statExample = S_IFREG := by decide
example : stat_ifmt devnullStatExample = S_IFCHR := by decide
example : stat_is_reg statExample = true := by decide
example : stat_is_reg devnullStatExample = false := by decide
example : stat_ifmt_valid statExample = true := by decide
example : stat_ifmt_valid (List.replicate 128 0) = false := by decide

/-- `st_size` is claimed only of a regular file, and `st_rdev`/`st_size`/
    `st_blocks` of a character device. -/
example : stat_size_ok 5 statExample = true := by decide
example : stat_size_ok 6 statExample = false := by decide
example : stat_size_ok 6 devnullStatExample = true := by decide
example : stat_devnull_ok devnullStatExample = true := by decide
example : stat_urandom_ok devnullStatExample = false := by decide

/-- Byte equality, and the stable-region comparison. -/
example : stat_bytes_eqb statExample statExample = true := by decide
example : stat_bytes_eqb statExample devnullStatExample = false := by decide
example : stat_stable_eqb statExample statExample = true := by decide
/-- Bytes 48..55 are `st_size`; changing only them keeps the stable
    region — and the envelope — intact, which is what `stat_set_size` is
    for. -/
example : stat_stable_eqb (stat_set_size 9 statExample) statExample = true := by decide
example : stat_buf_wf (stat_set_size 9 statExample) = true := by decide
example : stat_size_ok 9 (stat_set_size 9 statExample) = true := by decide
example : (stat_set_size 9 statExample).length = 128 := by decide
example : stat_field_le ST_SIZE_OFF 8 (stat_set_size 9 statExample) = 9 := by decide
example : stat_field_le ST_PAD1_OFF 8 (stat_set_size 9 statExample) = 0 := by decide
example : stat_field_le ST_BLKSIZE_OFF 8 (stat_set_size 9 statExample) = 4096 := by decide
example : stat_is_reg (stat_set_size 9 statExample) = true := by decide
/-- The one member a `stat_set_size` of a 128-byte buffer does NOT move. -/
example : stat_set_size 9 statExample = stat_set_size 9 (stat_set_size 5 statExample) := by decide

/-! ### `struct __kernel_timespec`: two little-endian eight-byte fields -/

/-- `tv_sec` = 3, `tv_nsec` = 500000000. -/
private def tsExample : List byte := [3, 0, 0, 0, 0, 0, 0, 0, 0, 0x65, 0xcd, 0x1d, 0, 0, 0, 0]

example : tv_sec_of tsExample = 3 := by decide
example : tv_frac_of tsExample = 500000000 := by decide
example : timespec_ns tsExample = 3500000000 := by decide
example : timespec_ns tsExample = tv_sec_of tsExample * 1000000000 + tv_frac_of tsExample := by decide
/-- Below `KTIME_SEC_MAX` the two totals agree. -/
example : timespec_ktime tsExample = timespec_ns tsExample := by decide
/-- At `KTIME_SEC_MAX` the conversion clamps to `KTIME_MAX` instead of
    multiplying, which is the whole point of `timespec_ktime`. -/
example : tv_sec_of (Z_to_le_bytes 8 KTIME_SEC_MAX ++ List.replicate 8 0) = KTIME_SEC_MAX := by decide
example : timespec_ktime (Z_to_le_bytes 8 KTIME_SEC_MAX ++ List.replicate 8 0) = KTIME_MAX := by decide
example : timespec_ns (Z_to_le_bytes 8 KTIME_SEC_MAX ++ List.replicate 8 0)
    = KTIME_SEC_MAX * 1000000000 := by decide
/-- -1 second reads as a huge unsigned second in `timespec_ns`, and as
    -1 in `timespec_ns_signed`. -/
example : tv_sec_of (List.replicate 8 0xff ++ List.replicate 8 0) = 2 ^ 64 - 1 := by decide
example : timespec_ns_signed (List.replicate 8 0xff ++ List.replicate 8 0) = -1000000000 := by decide
example : timespec_ns_signed tsExample = timespec_ns tsExample := by decide

end




