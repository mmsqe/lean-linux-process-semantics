/-
  * LinuxProcessSem.Sys.Fs.Locks — flock (32)

  This file answers to Linux `fs/locks.c`: it holds what the kernel
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
  and `getModelSpec` is `get_model`.  `Fs` supplies `path` and
  `path_eqb`; `StateLedger` supplies `m_fds`/`mkModel`; `StateFd` supplies
  `fd_lookup`; `Sys.Syscall` supplies `ret_only`/`err_ret`; `Sys.Uapi`
  supplies the five `LOCK_*` operations and `z_land`.  `Sys.Uaccess` is
  deliberately NOT imported: `flock` reads no user buffer, so no copy-in
  is ever recorded.  (Both `Sys.Uapi` and `Sys.Syscall` carry a local
  `abi_low32`/`fd32`; neither is used here, so the two names are only
  shadowed, not confused.)

  `x <- c;; k` has no Lean
  counterpart, so it is `bind c (fun x => k)` here; the one `get_model`
  step in `flock_spec` is written that way.  `ret_only` and `err_ret` are
  `Sys/Syscall.lean`'s, and `unmodeled` is `Monad.lean`'s.

  `Z.ldiff a b` is `a land lnot b`; Lean
  core has no `Int` bitwise and-not, so `Sys/Uapi.lean` ports it next to
  `z_lor`/`z_land`, and the `z_ldiff` below is a transparent alias to
  that one, kept where its one caller reads it — the same treatment
  `Sys/Fs/Pipe.lean` gives the same primitive.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Locks

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

/-- `cmd & LOCK_MAND` — the FIRST test `SYSCALL_DEFINE2(flock)`
    (fs/locks.c, Linux v6.18.46, commit 1f99e9ab748f) performs, and the
    only one that answers before the descriptor is looked up at all.

    Mandatory flocks were removed from the kernel, and what replaced
    them is a SUCCESSFUL NO-OP rather than a rejection: the syscall
    logs `pr_warn_once` and returns 0.  So `flock(-1, LOCK_MAND)` is 0,
    not -EBADF, and `flock(fd, LOCK_MAND)` is 0 whatever the fd names
    and whatever locks are held.  Nothing is recorded because nothing
    happens — no `struct file_lock` is built and `flock_translate_cmd`
    is never reached.

    The bit is tested, not the whole word, so LOCK_MAND OR'd with any
    other operation is still this arm: `LOCK_MAND|LOCK_EX` takes no
    lock. -/
def flock_mand_b (cmd : word) : Bool :=
  !(z_land (cmd.toNat : Int) LOCK_MAND == 0)

/-! ## `Z.ldiff` over `Int`

  `flock_base` is the one place in this file that needs 
    `Z.ldiff a b = a land lnot b`.  `Sys/Uapi.lean` now defines it
    (`Uapi.z_ldiff`, body `a - (a &&& b)`), so the helper below is a
    transparent alias to that one rather than a second spelling. -/

/--  `Z.ldiff` — the bitwise difference `a land lnot b` — is
    `Uapi.z_ldiff`, the canonical definition, as a transparent alias.

    The body there is `a - (a &&& b)`, which agrees with
    `a land lnot b` on the operands this file has: `a` is a `word` read
    unsigned (`cmd.toNat`) and `b` is `LOCK_NB`, 4, so both lie below
    `2^64`, and a value below `2^64` occupies no bit above 63.  On such
    bounded operands the `Nat`-mask form this file used to spell
    (`a &&& (2^64 - 1 - b)`) and `a - (a &&& b)` are the same value:
    either way exactly the bits of `b` are cleared from `a`.  Truncating
    either argument would be visible; both are bounded. -/
abbrev z_ldiff (a b : Int) : Int := LinuxSem.LinuxProcessSem.Sys.Uapi.z_ldiff a b

/-- `cmd & ~LOCK_NB` — the word `flock_translate_cmd` switches on.

    LOCK_NB is a MODIFIER, stripped before the operation is recognized,
    which is why an unrecognized operation and a recognized one differ
    only in these bits.  `cmd` arrives already narrowed to 32 bits (see
    `Syscall.cmd32`), so this is the kernel's own `unsigned int`
    arithmetic. -/
def flock_base (cmd : word) : Int :=
  z_ldiff (cmd.toNat : Int) LOCK_NB

/-- The three operations `flock_translate_cmd` (fs/locks.c) maps to a
    lock type; every other word falls off the end of its `switch` and is
    -EINVAL, RETURNED BEFORE THE DESCRIPTOR IS RESOLVED.  That ordering
    is behavior: `flock(-1, 0)` is -EINVAL and not -EBADF. -/
def flock_cmd_ok_b (cmd : word) : Bool :=
  let b := flock_base cmd
  (b == LOCK_SH || b == LOCK_EX || b == LOCK_UN)

/-- Is this the UNLOCK operation?  Separated from the other two because
    it is the one the model can answer unconditionally — see
    `flock_spec`. -/
def flock_unlock_b (cmd : word) : Bool := flock_base cmd == LOCK_UN

/-- How many descriptors in the table name the path `p`.

    THIS IS THE WHOLE OF THE MODEL'S LOCK STATE, and it is a count of
    OPENERS rather than a record of locks.  The argument in `flock_spec`
    turns on there being at most one `struct file` on the inode, not on
    which locks it holds, so no lock has to be recorded to make it.

    Every `FdEntry` constructor is named rather than wildcarded, for
    the reason `State.pipe_end_live` gives for the same shape: a later
    constructor able to name a file in `m_fs` must stop the build here
    instead of being counted as "not an opener" by falling through a
    catch-all.  The four that are skipped are skipped on a fact about
    what they are, not on convenience — a channel, a pipe end, a socket
    and a directory reference each live on an inode that is not a key of
    `Fs.Fs` at all, which is argued at `flock_spec`. -/
def path_openers : List (word × FdEntry) → Fs.path → Nat
  | [], _ => 0
  | (_, FdEntry.FdFile q _) :: r, p =>
      (if Fs.path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdEntry.FdFileW q _) :: r, p =>
      (if Fs.path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdEntry.FdFileA q _) :: r, p =>
      (if Fs.path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdEntry.FdFileRW q _) :: r, p =>
      (if Fs.path_eqb q p then 1 else 0) + path_openers r p
  | (_, FdEntry.FdChannel _) :: r, p => path_openers r p
  | (_, FdEntry.FdDir) :: r, p => path_openers r p
  | (_, FdEntry.FdSocket _) :: r, p => path_openers r p
  | (_, FdEntry.FdPipe _ _) :: r, p => path_openers r p
  -- a device node is not a key of `Fs.Fs`
  | (_, FdEntry.FdDevNull _ _) :: r, p => path_openers r p
  -- nor is this one
  | (_, FdEntry.FdUrandom) :: r, p => path_openers r p

/-- Exactly one descriptor names `p`.  Applied to a path just resolved
    out of the table, so the count is at least one and this says "no
    OTHER descriptor names it". -/
def flock_sole_opener (fds : List (word × FdEntry)) (p : Fs.path) : Bool :=
  path_openers fds p == 1

/-- `flock fd cmd`: take, convert or release a whole-file advisory lock.

    THE ORDER IS THE KERNEL'S, and here it decides two answers rather
    than one.  `SYSCALL_DEFINE2(flock)` (fs/locks.c, Linux v6.18.46,
    commit 1f99e9ab748f) does, in this order: the LOCK_MAND test, the
    `flock_translate_cmd` of `cmd & ~LOCK_NB`, the descriptor lookup
    and its `fd_empty` test, the `f_mode` test, the LSM hook, and only
    then the lock itself.  So

      flock(-1, LOCK_MAND)  is 0        — no fd is consulted
      flock(-1, 0)          is -EINVAL  — the operation loses to no fd
      flock(-1, LOCK_EX)    is -EBADF

    and a model that resolved the descriptor first would answer -EBADF
    to all three.

    WHAT IS ANSWERED, AND WHY EACH ANSWER IS CERTAIN.

    - LOCK_MAND (any word with bit 0x20 set): 0.  Unconditional; see
      `flock_mand_b`.

    - an operation `flock_translate_cmd` does not recognize: -EINVAL.
      Unconditional, and decided before the fd.

    - a descriptor that is not open: -EBADF.  `fd_empty(f)` is the only
      thing between the operation check and the lock.

    - LOCK_UN on any open descriptor: 0.  UNCONDITIONAL, and this is
      the one arm that needs no premise about who else holds a lock.
      Walk it: `flock_translate_cmd` gives F_UNLCK, so the `f_mode`
      test — `type != F_UNLCK && !(f_mode & (FMODE_READ|FMODE_WRITE))`
      — is skipped, and `locks_lock_file_wait` reaches
      `flock_lock_inode` (fs/locks.c).  There `locks_get_lock_context`
      returning NULL is `return (flc_flags & FL_EXISTS) ? -ENOENT : 0`
      for an unlock, and FL_EXISTS is a fcntl-side flag that
      `flock_make_lock` never sets; with a context, the first loop
      drops whatever this `struct file` held and `lock_is_unlock` then
      takes `goto out` with `error` still 0.  Neither branch reads the
      list of locks OTHER files hold, so an unlock cannot -EAGAIN and
      cannot block.  Releasing a lock that was never taken is 0 too.

    - LOCK_SH or LOCK_EX (with or without LOCK_NB) on an `FdFile` or
      `FdFileW` whose path NO OTHER DESCRIPTOR NAMES: 0.  This is the
      arm the premise below is spent on.

    WHY THE SOLE-OPENER GATE IS THE RIGHT ONE, and not a conservative
    flourish.  An FLOCK lock's owner is the `struct file`, not the
    process: `flock_make_lock` sets `flc_owner = filp`, and
    `flock_locks_conflict` returns false outright when
    `caller_flc->flc_file == sys_flc->flc_file`.  So one open file
    description can lock, relock, upgrade and downgrade freely and
    never conflict with itself, and a SECOND `openat` of the same name
    in the SAME PROCESS produces a second `struct file` that DOES
    conflict.  That is not a corner: it is the ordinary way a program
    deadlocks against itself, and it is reachable here with two modeled
    syscalls.

      fd1 = openat(AT_FDCWD, "f", ...);  flock(fd1, LOCK_EX);      /* 0 */
      fd2 = openat(AT_FDCWD, "f", ...);  flock(fd2, LOCK_EX|LOCK_NB);
                                                        /* -EAGAIN */

    A model that answered 0 to the second call would be wrong in
    the sense of design priority 1 (README.md), and the state that would let it
    answer -EAGAIN instead is a per-open-file-description lock table
    the model does not have — and could not key correctly if it did,
    since `File.dup_spec` copies an `FdEntry` and the copy is the SAME
    `struct file`, which does not conflict, while a reopen is a
    different one, which does.  Two identical `FdFile p off` entries do
    not say which happened.  So the second call DECLINES, and the first
    is answered only while it is provably alone.  The gate costs the
    duplicated-descriptor case (a `dup` of the locked fd declines even
    though Linux would answer 0); that is coverage, not soundness.

    WHY THE OTHER FOUR FD KINDS DECLINE, each for its own reason rather
    than by a shared shrug:

    - `FdPipe`: BOTH ENDS OF ONE PIPE SHARE AN INODE and are two
      `struct file`s, so `pipe2` alone builds the conflicting pair the
      gate above exists to refuse — and `State.FdPipe`'s id would make
      the gate expressible, so this decline is a coverage choice with a
      known shape rather than a missing fact.
    - `FdChannel`: the object is not in the model.  The model already
      assumes a channel is a PIPE (`Sync.fsync_spec`'s -EINVAL and
      `ReadWrite.lseek_spec`'s -ESPIPE both spend that assumption), and
      that assumption does not say whether two channels are two ends of
      one pipe or two different pipes — which is exactly the question
      an inode-scoped lock asks.
    - `FdDir`: "." and ".." are both `FdDir` and the constructor
      carries nothing, so two directory references cannot be told
      apart; two `openat(".")` descriptors are two `struct file`s on
      one inode.
    - `FdSocket`: sockfs gives every socket its own inode, so the
      conflicting pair is not constructible — but the answer would then
      be 0 by an argument about `sock_alloc` rather than about
      fs/locks.c, and no caller wants it.  Declined for want of a
      reason to admit it, not for want of one to refuse it.

    WHY A PATH IS THE RIGHT KEY FOR THE FILE KINDS.  Conflicts are
    per-INODE, and `Fs.Fs` is a flat path-to-bytes map with no inode
    notion, so the two coincide only under assumptions the model
    already makes everywhere: distinct keys are distinct files (a hard
    link would break it, and no modeled syscall makes one — `linkat`
    has no arm), and a key is a regular file in the working directory
    (`Open.openat_spec`'s separator gate is what keeps every key a plain
    name).  The constructors `path_openers` skips — `FdChannel`, `FdDir`,
    `FdSocket` and `FdPipe` — rest on the same map: a pipefs, sockfs or
    directory inode is not a key of `Fs.Fs`, so no descriptor of those
    kinds can share an inode with an `FdFile`.

    WHAT THE GRANT ASSUMES ABOUT THE WORLD, stated as an assumption
    rather than derived: no process outside the model holds a
    conflicting flock on the inode.  This is the premise
    `Sys/Uapi.lean`'s O_NONBLOCK note already asserts for leases — "the
    model runs ONE process, so nothing else can hold one either" — and
    it is load-bearing here in a way it is not there, because a lease
    also needs an fcntl the model declines while a flock needs only
    another process that opened the same name.  Modeling `clone`
    parent-side widens the population it quantifies over: a child this
    model never steps inherits the fd table, and locks taken through an
    INHERITED descriptor are the same `struct file` and still do not
    conflict, but a child that opens the name again is a second one
    that does.

    THE FILESYSTEM BOUND, which is real and is the same one
    `Sync.fsync_spec` names for `.fsync`.  Everything above assumes
    `f_op->flock` is NULL, so that `locks_lock_file_wait` — the local,
    inode-scoped path — is what runs.  It holds for the filesystems a
    run can plausibly sit on: neither `ext4_file_operations`
    (fs/ext4/file.c) nor `shmem_file_operations` (mm/shmem.c) nor
    `ext4_dir_operations` (fs/ext4/dir.c) nor `simple_dir_operations`
    (fs/libfs.c) declares one, and neither do `pipeanon_fops`
    (fs/pipe.c), `socket_file_ops` (net/socket.c), `tty_fops`
    (drivers/tty/tty_io.c) or `null_fops` (drivers/char/mem.c).  A
    network filesystem that DOES declare one — NFS is the standing
    example — answers from its own lock manager, and a run whose
    working directory sits on such a mount is outside this spec.  Same
    shape as fsync's procfs/sysfs bound: named, not fixed.

    OUT OF SCOPE, and unreachable rather than approximated:

    - -ENOMEM from `locks_alloc_lock` or `locks_get_lock_context`.  The
      model has no allocation-failure state, so no execution reaches
      it.  This spec commits to its answers absolutely rather than
      offering an `Syscall.errno_from` alternative, which is the
      position `Fcntl.fcntl_spec` and `Ioctl.ioctl_spec` take for the
      same class.
    - the LSM hook `security_file_lock`, which runs after the `f_mode`
      test and can fail the call under an enforcing module.  Same
      position again, and for the same reason: the model describes a
      kernel with no LSM registering these hooks.
    - the -EBADF an O_PATH descriptor gets from
      `type != F_UNLCK && !(f_mode & (FMODE_READ|FMODE_WRITE))`.
      `Open.openat_spec` models three flag words and O_PATH is not
      among them, so no such descriptor exists here.  Note the arm is
      -EBADF, not -EINVAL: an fd that IS open can still be refused by
      it, which is why it is named rather than folded into the lookup.
    - blocking.  A LOCK_SH or LOCK_EX without LOCK_NB that conflicts
      sleeps in `wait_event_interruptible` (fs/locks.c,
      `flock_lock_inode_wait`) until the holder releases or a signal
      arrives.  Every shape that can conflict declines above, so the
      model never has to represent a syscall that does not return, and
      the -EINTR that path can produce is unreachable with it. -/
def flock_spec (fd cmd : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if flock_mand_b cmd then ret_only (BitVec.ofInt 64 0)
      -- the removed mandatory-lock request: a no-op that succeeds,
      -- decided before the fd is looked at
    else if !(flock_cmd_ok_b cmd) then err_ret EINVAL
      -- `flock_translate_cmd` fell off its switch — still before the fd
    else
      match fd_lookup (m_fds m) fd with
      | none => err_ret EBADF  -- fd not open
      | some e =>
          if flock_unlock_b cmd then ret_only (BitVec.ofInt 64 0)
            -- an unlock reads no other file's locks: unconditionally 0
          else
            match e with
            | FdEntry.FdFile p _ =>
                if flock_sole_opener (m_fds m) p
                then ret_only (BitVec.ofInt 64 0)  -- provably uncontended
                else unmodeled  -- a second opener could hold it
            | FdEntry.FdFileW p _ =>
                if flock_sole_opener (m_fds m) p
                then ret_only (BitVec.ofInt 64 0)
                else unmodeled
            | FdEntry.FdFileA p _ =>
                -- the same regular file opened in append mode.  O_APPEND is
                -- a property of the open file description that decides where
                -- a WRITE lands; `flock` locks the inode and reads no
                -- `f_flags` at all, so the sole-opener argument transfers
                -- unchanged
                if flock_sole_opener (m_fds m) p
                then ret_only (BitVec.ofInt 64 0)
                else unmodeled
            | FdEntry.FdFileRW p _ =>
                -- the same regular file opened O_RDWR.  `sys_flock` resolves
                -- its descriptor through `fdget` and reads no `f_mode` and
                -- no `f_flags` on any path to `flock_lock_inode_wait`: the
                -- lock is on the INODE, and which directions the
                -- description may transfer is not one of its inputs
                -- (fs/locks.c, Linux v6.18.46).  So the access mode cannot
                -- change the count, and the sole-opener argument transfers
                -- unchanged from the three arms above.
                --
                -- COUNTING IT IS THE SOUNDNESS-RELEVANT HALF: skipping it
                -- in `path_openers` would leave `flock_sole_opener` true
                -- while a SECOND read-write descriptor held the same path,
                -- and the model would answer 0 for a lock the kernel makes
                -- conflict — an unsound accept rather than a gap.
                if flock_sole_opener (m_fds m) p
                then ret_only (BitVec.ofInt 64 0)
                else unmodeled
            | FdEntry.FdChannel _ => unmodeled
              -- the object is not in the model
            | FdEntry.FdDir => unmodeled
              -- two dirrefs are indistinguishable
            | FdEntry.FdSocket _ => unmodeled
              -- no caller, and a different argument
            | FdEntry.FdPipe _ _ => unmodeled
              -- both ends share one inode
            | FdEntry.FdDevNull _ _ => unmodeled
              -- FAIL-CLOSED: every open of /dev/null is a `struct file`
              -- on ONE inode, so two descriptors of this kind conflict
              -- exactly as two `FdFile`s on one path do, and the
              -- sole-opener gate would need an `FdDevNull` count the way
              -- `path_openers` counts a path.  Derivable, not written.
            | FdEntry.FdUrandom => unmodeled
              -- FAIL-CLOSED, for the /dev/null reason: one inode, so
              -- an `FdUrandom` count would be needed.  Not written.

/-! ## Sanity checks

  It is four small predicates, two table functions and the spec, with the prose
  above. The checks below are PORT CHECKS.

    The first group pins the word arithmetic at the three places a
    transcription slip would show: the LOCK_MAND test (a BIT, not the
    whole word), the `~LOCK_NB` strip, and the operation switch that
    strips it.  The second group pins the two table functions.  The third
    group pins the ARMS of `flock_spec` IN THE KERNEL'S ORDER, which is
    what the header argues for: a bad operation is -EINVAL even when the
    fd is missing, LOCK_MAND is 0 even when the fd is missing, a missing
    fd is -EBADF, an unlock is 0 unconditionally, and a file whose path
    has a SECOND opener declines rather than answering 0.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so the spec checks state the spec's
    OUTCOME rather than comparing entries: the outcome carries the
    returned word and the whole `SyscallEffect`, which is what a caller
    observes. -/

/-! ### The word tests -/

/-- The LOCK_MAND test is a BIT test: 0x20 alone is the arm, any other
    operation is not, and LOCK_MAND OR'd with another operation still
    is. -/
example : flock_mand_b 32 = true := by decide
example : flock_mand_b 34 = true := by decide
example : flock_mand_b 2 = false := by decide
example : flock_mand_b 0 = false := by decide

/-- `flock_base` strips LOCK_NB and nothing else. -/
example : flock_base 2 = 2 := by decide
example : flock_base 6 = 2 := by decide
example : flock_base 12 = 8 := by decide
example : flock_base 0 = 0 := by decide

/-- The operation switch: LOCK_SH, LOCK_EX and LOCK_UN pass, each with or
    without LOCK_NB; everything else — 0, a lone LOCK_NB, LOCK_MAND
    itself — falls off the end of the switch. -/
example : flock_cmd_ok_b 1 = true := by decide
example : flock_cmd_ok_b 2 = true := by decide
example : flock_cmd_ok_b 8 = true := by decide
example : flock_cmd_ok_b 5 = true := by decide
example : flock_cmd_ok_b 6 = true := by decide
example : flock_cmd_ok_b 12 = true := by decide
example : flock_cmd_ok_b 0 = false := by decide
example : flock_cmd_ok_b 4 = false := by decide
example : flock_cmd_ok_b 32 = false := by decide

/-- Only LOCK_UN (= 8) is the unlock, with or without the modifier. -/
example : flock_unlock_b 8 = true := by decide
example : flock_unlock_b 12 = true := by decide
example : flock_unlock_b 2 = false := by decide
example : flock_unlock_b 6 = false := by decide

/-- `Z.ldiff` clears the bits of its second argument — which is what
    makes LOCK_NB disappear from `flock_base` and nothing else. -/
example : z_ldiff 5 3 = 4 := by decide
example : z_ldiff 0 5 = 0 := by decide
example : z_ldiff 4 4 = 0 := by decide
example : z_ldiff 6 4 = 2 := by decide

/-! ### The fixture -/

/-- The path `out` for the table checks. -/
private def outPath : Fs.path := [0x6f, 0x75, 0x74]

/-- The path `dup` for the table checks. -/
private def dupPath : Fs.path := [0x64, 0x75, 0x70]

/-- A tiny fd table for the checks: 0 a channel, 1 a regular file
    (`out`), 2 a directory, 3 a pipe end, and 4 and 5 two regular files
    naming the SAME path (`dup`). -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile outPath 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdFile dupPath 0),
    (5, FdEntry.FdFileW dupPath 5) ]

/-- `path_openers` counts the four file constructors by path and skips
    every other kind of entry — the whole of the model's lock state. -/
example : path_openers demoFds outPath = 1 := by decide
example : path_openers demoFds dupPath = 2 := by decide
example : path_openers demoFds [] = 0 := by decide
example : path_openers [] dupPath = 0 := by decide

/-- …which is what the sole-opener gate asks: `out` is named once, `dup`
    twice. -/
example : flock_sole_opener demoFds outPath = true := by decide
example : flock_sole_opener demoFds dupPath = false := by decide

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A syscall input for `flock` (32).  The spec reads none of it; it is
    here because a `SysSpec` is a relation on an input as well as a
    model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 32, in_args := [1, 2], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-! ### The arms, in the kernel's order

    Every definition these checks unfold — the spec, the fixture, the
    word tests, and the `Uapi` operations they compare against — is
    registered `local simp` here, so each check is a single `simp` with
    no argument list.  Registered lemmas, unlike arguments passed per
    call, do not make the unused-simp-argument linter fire on the arms
    that never reach them (the LOCK_MAND arm never reaches the fd
    lookup, and the -EINVAL arm never reaches the unlock test).  The
    registrations are `local`: they end with this file and do not leak
    into `Specs.lean`.

    `bv_eqb` is in the list because `Fs.path_eqb` is spelled through it:
    `path_eqb [0x6f, …] [0x6f, …]` reduces to a conjunction of `bv_eqb`
    tests, so the byte comparisons have to reduce for the opener count to
    compute at all. -/

attribute [local simp]
  flock_spec getModelSpec bind_getModel fd_lookup demoFds demoModel
  m_fds mkModel flock_mand_b flock_cmd_ok_b flock_unlock_b flock_base
  flock_sole_opener path_openers Fs.path_eqb bv_eqb z_ldiff Uapi.z_ldiff z_land
  outPath dupPath
  LOCK_SH LOCK_EX LOCK_NB LOCK_UN LOCK_MAND err_ret ret_only pure
  unmodeled

/-- THE SUCCESS ARM RETURNS 0 AND AN EMPTY EFFECT: LOCK_EX on a regular
    file that no other descriptor names leaves the model untouched,
    writes no memory, zeroes and unmaps nothing, copies nothing, records
    no copy-ins and emits no event. -/
example :
    flock_spec 1 2 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- …and LOCK_EX|LOCK_NB is the same arm: the modifier changes no
    answer. -/
example :
    flock_spec 1 6 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- A BAD OPERATION IS -EINVAL.  This one is `flock(-1, 0)`'s answer:
    the operation falls off `flock_translate_cmd`'s switch, which is
    tested BEFORE the descriptor, so the fd is never consulted. -/
example :
    flock_spec 9 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp

/-- …and the same word on an fd that IS open is -EINVAL too: the
    descriptor cannot rescue an unrecognized operation. -/
example :
    flock_spec 1 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp

/-- LOCK_MAND IS A SUCCESSFUL NO-OP on an open fd … -/
example :
    flock_spec 1 32 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- … and on `flock(-1, LOCK_MAND)`, which returns 0 rather than -EBADF
    because the bit is tested before the descriptor is looked up. -/
example :
    flock_spec 9 32 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- A MISSING FD IS -EBADF, and it is the fd lookup that decides: no
    object is examined at all. -/
example :
    flock_spec 9 2 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  simp

/-- AN UNLOCK IS 0 UNCONDITIONALLY — even on `dup`, the path with a
    second opener, which is the one shape the LOCK_SH/LOCK_EX arms
    refuse: no other file's locks are read. -/
example :
    flock_spec 4 8 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- …with the modifier or without it. -/
example :
    flock_spec 4 12 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp

/-- A SECOND OPENER IS REFUSED, not answered 0: fd 4's path `dup` is
    also named by fd 5, so the model cannot tell whether a conflicting
    `struct file` holds the lock — the fail-closed answer. -/
example : flock_spec 4 2 demoInput demoModel .unmodeled := by
  simp

/-- …and the count sees EVERY file constructor, not just `FdFile`: fd 5
    is an `FdFileW` on the same path, so it is an opener too, and the
    arm above declines because of it.  This is the `path_openers` half
    the `FdFileRW` comment in `flock_spec` calls soundness-relevant. -/
example : flock_spec 5 2 demoInput demoModel .unmodeled := by
  simp

/-- The four non-file kinds decline for their own reasons: a channel, a
    directory and a pipe end each name an object that is not a key of
    `Fs.Fs`, so the opener count the gate needs cannot be taken. -/
example : flock_spec 0 2 demoInput demoModel .unmodeled := by
  simp

example : flock_spec 2 2 demoInput demoModel .unmodeled := by
  simp

example : flock_spec 3 2 demoInput demoModel .unmodeled := by
  simp

/-- The two errnos really are the kernel's numbers in the return word,
    and the success return really is a zero word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end LinuxSem.LinuxProcessSem.Sys.Fs.Locks
