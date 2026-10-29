/-
  * LinuxProcessSem.Sys.Fs.Select — pselect6 (72) and ppoll (73)


  This file answers to Linux `fs/select.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines the
  syscall.  `Specs.v` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  THE MONAD.  A spec's type is `SysSpec SyscallEffect`, fixed at the
  concrete `Model`/`SyscallInput`/`event` by `MonadInstances`.  The
  sequencing `x <- c ;; k` is `bind c (fun x => k)`, which is how the two
  chains in `pselect6_spec` and `ppoll_spec` are written (`input` →
  `inputSpec`, `get_model` → `getModelSpec`).

  NOTATION.  `Z` is `Int`, `bv n` is `BitVec n`; `bv_unsigned w` is
  `(w.toNat : Int)`, `bv_signed w` is `w.toInt`, `Z_to_bv n z` is
  `BitVec.ofInt n z`, `Z.eqb a b` is `a == b`, `Z.ltb`/`Z.leb` are
  `decide (· < ·)`/`decide (· ≤ ·)`, `Z.to_nat` is `Int.toNat`, and
  `Z.lor`/`Z.land` are `Sys.Uapi`'s `z_lor`/`z_land` (Lean core has no
  `Int` bitwise operations).  `FdEntry`'s constructors keep their names,
  so every `match` below reads against the prose line for line.

  THREE PRIMITIVES THIS TREE DOES NOT CARRY.
  `Z.testbit`, `Z.ones` and `BvBase.word_le2` are used below and exist
  in neither Lean core (v4.31.0 has no `Int.testbit`/`Nat.testbit`) nor
  `BvBase.lean` (which carries `word_le8` and not `word_le2`/`word_le4`).
  They are restated at the top of this file, each with the argument that
  the restatement is the same function.  This is the only structural
  addition in the file; nothing else is added, removed or reordered.

  NO REUSED LEMMAS.  The reference is definitions and
  prose: it carries no `Lemma` and no closed-goal check.  The checks at
  the bottom are therefore PORT CHECKS, and they pin the computable
  things the prose argues for — the fd-set bit encoding and the scan
  mask, the empty-set/zero-timeout arm, -EBADF, the -EINVAL and the
  declines of each nfds band, and ppoll's `revents` write-back.

  WHICH KERNEL THIS IS A MODEL OF.

  Cited by function name rather than by line number.  The window given
  for each function is ITS OWN, and deliberately so: one byte-identity
  sentence covering a LIST is false as soon as any single member moves.

    v6.1 - v6.18.46
      fs/select.c            `SYSCALL_DEFINE6(pselect6, ...)`,
                             `do_pselect`, `poll_select_finish`,
                             `poll_select_set_timeout`, `max_select_fd`,
                             `get_fd_set`, `set_fd_set`, `FDS_BYTES`,
                             `POLLIN_SET`, `POLLOUT_SET`, `POLLEX_SET`,
                             and, for ppoll (73),
                             `SYSCALL_DEFINE5(ppoll, ...)`,
                             `do_sys_poll`, `do_poll`, `do_pollfd`,
                             `POLL_STACK_ALLOC`, `N_STACK_PPS`,
                             `struct poll_list`, `demangle_poll`,
                             `mangle_poll` -- NOT READ FROM A CHECKOUT.
                             The ppoll half's window is NOT a
                             byte-identity claim like the ones below
                             it: it names the functions the claims
                             come from at the pinned version and
                             nothing more.  The pselect6 half's
                             windows were checked against a tree
      include/linux/poll.h   `vfs_poll`, `DEFAULT_POLLMASK`,
                             `SELECT_STACK_ALLOC`
      include/linux/time64.h `timespec64_valid`
      kernel/time/time.c     `timespec64_add_safe`, `get_timespec64`,
                             `put_timespec64` -- declared in
                             include/linux/time.h, NOT time32.h, whose
                             only timespec accessors are the
                             `get_old_timespec32` pair
      include/linux/hrtimer.h `hrtimer_set_expires_range_ns`, a static
                             inline defined there; kernel/time/hrtimer.c
                             only calls it
      kernel/time/sleep_timeout.c
                             `schedule_hrtimeout_range_clock` -- it lived
                             in kernel/time/hrtimer.c until v6.13 and is
                             ABSENT from that file at the pinned commit,
                             so the citation names where it is now; the
                             two branches this rests on are unchanged
                             across the move
    v6.1 - v6.15, then v6.16 - v6.18.46
      fs/select.c            `core_sys_select` -- TWO texts, not one.
                             v6.16 adds `unlikely()` to the `n < 0` test
                             and nothing else changes through the pinned
                             commit; nothing observable either way
    v6.13 - v6.18.46
      fs/select.c            `do_select`
    v6.6 - v6.18.46
      include/linux/fdtable.h `NR_OPEN_DEFAULT`
      kernel/signal.c        `set_user_sigmask`
    v6.14 - v6.18.46
      fs/select.c            `get_sigset_argpack`
      fs/file.c              `expand_files`

  THE UPPER END OF EVERY WINDOW IS READ FROM THE PINNED COMMIT ITSELF
  rather than from a mainline tag near it: stable v6.18.46, commit
  1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, which is this repository's
  kernel of record.  Five of the eight files are byte-identical AS
  WHOLE FILES between v6.17 and that commit -- fs/select.c,
  include/linux/poll.h, include/linux/time64.h,
  include/linux/fdtable.h and kernel/time/sleep_timeout.c -- so every
  function cited from them carries across with nothing to argue.  The
  other three do change between those refs, and each change lands
  outside what is cited here:

    kernel/time/time.c   `settimeofday` and its compat twin tighten
                         `new_ts.tv_nsec > USEC_PER_SEC` to `>=`,
                         `jiffies_64_to_clock_t` gains `notrace`, and
                         an `EXPORT_SYMBOL_GPL(timespec64_add_safe)`
                         line appears after the function.  All three
                         cited BODIES are byte-identical; only the
                         kerneldoc `Return:` line above
                         `timespec64_add_safe` and that export moved.
    include/linux/hrtimer.h
                         `hrtimer_cb_get_time` stops being a static
                         inline and becomes an out-of-line call, and
                         its three callers are rewired to it.
                         `hrtimer_set_expires_range_ns` is not one of
                         them and is untouched.
    kernel/signal.c      three hunks, all in `zap_other_threads` and
                         `__lock_task_sighand` (a
                         `task_clear_jobctl_pending` call and an
                         `smp_acquire__after_ctrl_dep()` barrier).
                         `set_user_sigmask` is untouched.
    fs/file.c            one hunk, in `replace_fd`: `do_dup2`'s result
                         is now checked rather than returned directly.
                         `expand_files` is untouched.

  THE v6.14 WINDOW IS NARROW BECAUSE BOTH FUNCTIONS IN IT MOVED.
  `get_sigset_argpack` has THREE texts across that range -- v6.1 -
  v6.11, v6.12 - v6.13, and v6.14 onward, which differs from v6.12's by
  one line: the fault path calls `user_read_access_end()` where it
  called `user_access_end()` -- kernel commit 344af27715dd,
  "select: Fix unbalanced user_access_end()".  `expand_files` has three
  as well, and its v6.14 change is a REORDER rather than a hint: the
  `nr >= sysctl_nr_open` test that yields -EMFILE moves from BEFORE the
  `resize_in_progress` wait to AFTER it.  That leaves the `dup3`
  ordering argument in `Sys/Fs/File.lean` intact, since that argument
  turns on when `expand_files`' RESULT IS READ relative to the `oldfd`
  check and not on the order of tests inside it -- but it is a semantic
  move, and a byte-identity claim spanning it would be false.

  The narrowest SIMULTANEOUS byte-identity window, where every function
  above holds at once, is still v6.14 - v6.15, and `core_sys_select` is
  the only function that closes it: every other one runs from its own
  lower bound to the pinned commit unbroken.  The SEMANTIC window is
  the whole v6.1 - v6.18.46 range: every remaining difference is a
  compiler hint (`noinline_for_stack`, `unlikely`, `READ_ONCE`), an
  accessor rename (`f.file` to `fd_file(f)`), a file move, the
  extraction of `select_poll_one`, or the `expand_files` reorder --
  which pselect6 cannot observe, since the model declines every `n`
  above 64 and allocates no descriptor.

  STABLE BRANCHES, AND THREE OF THEM ARE EXCLUDED.  `do_pselect`,
  `poll_select_finish`, `poll_select_set_timeout` and `max_select_fd`
  are byte-identical at every release tag above AND at the heads of
  linux-6.10.y through linux-6.18.y, read at 6.10.14, 6.11.11,
  6.12.105, 6.13.12, 6.14.11, 6.15.11, 6.16.12, 6.17.13 and 6.18.48.
  `core_sys_select` is byte-identical to ITS OWN window's text on every
  one of those branches rather than to a single text -- linux-6.10.y
  through linux-6.15.y carry the v6.1 one, linux-6.16.y through
  linux-6.18.y the v6.16 one, which is the pinned commit's -- so it is
  a split, not an exclusion.  `get_sigset_argpack` IS an exclusion, and
  every divergence runs the same way -- the branch carries a
  LATER text than its own mainline tag, because both changes to this
  function were backported.  linux-6.11.y carries the v6.12 text (the
  `masked_user_access_begin()` branch); linux-6.12.y and linux-6.13.y
  carry the v6.14 text (that branch AND the `user_read_access_end()`
  fault-path fix).  linux-6.10.y, linux-6.14.y, linux-6.15.y,
  linux-6.16.y, linux-6.17.y and linux-6.18.y agree with their tags.

  WHICH VALIDATOR, checked rather than assumed.  `poll_select_set_timeout`
  calls `timespec64_valid`, the NON-strict one; `timespec64_valid_strict`,
  which additionally bounds `tv_sec` by `KTIME_SEC_MAX`, does not appear
  in fs/select.c at any ref in the window.  So a huge `tv_sec` is ACCEPTED
  here and saturated by `timespec64_add_safe`, not rejected -- the
  opposite of what a reader who carried the rule across from a sibling
  syscall would write.  `timespec64_valid` rejects `tv_sec < 0` and
  `(unsigned long)tv_nsec >= NSEC_PER_SEC`; the cast is load-bearing and
  is why `pselect_timeout` tests `bv_unsigned nsec` rather than a signed
  reading.

  WHERE THE ORDERING COMES FROM.  Every ordering claim below is read off
  the bodies of `SYSCALL_DEFINE6(pselect6, ...)`, `do_pselect` and
  `core_sys_select`.  No man page documents error-check ordering for any
  syscall -- ERRORS sections are alphabetical by errno name, which is
  house style and not precedence -- so nothing here is taken from
  select.2, and an enumeration of what a call refuses is not a claim
  about what it checks first.

  On riscv64, `select` does not exist as a syscall number: glibc and
  musl both compile `select` and `pselect` to `pselect6`, number 72.
  There is no `poll` and no `epoll_wait` either -- `ppoll` (73) and the
  `epoll` family are the only other multiplexing entry points.  `ppoll`
  is modeled, at the bottom of this file, on the same readiness
  argument and with the same declines.  The epoll family is, on its
  REJECTING half only:
  `Fs.EventPoll` declines `epoll_create1`'s success arm, so no
  descriptor is ever an epoll instance and neither `epoll_ctl` nor
  `epoll_pwait` reaches the readiness machinery.  The reason is the
  mirror image of this file's -- `file_can_poll` rejects with -EPERM
  exactly the descriptors whose `DEFAULT_POLLMASK` lets
  `bits_all_pollable` answer, so epoll gets the half whose readiness
  this model cannot observe.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Select

/-! ## Three primitives this tree does not carry

    See the note in the header.  Each is the same function on the domain
    this file applies it to; the argument is on each docstring. -/

/-- `Z.testbit z k` — bit `k` of `z` — spelled through the
    shift-and-mask that defines it.

    NEITHER `Int.testbit` NOR `Nat.testbit` EXISTS in Lean core at this
    toolchain (v4.31.0), so the primitive is restated rather than
    imported, exactly as `Sys/Uapi.lean` restates `Z.lor`/`Z.land` over
    `Nat`.  Every `z` this file tests is a `bv_unsigned` — the `Int`
    reading of a 64-bit word — hence NON-NEGATIVE, which is the whole
    domain on which `Z.testbit` agrees with the low bit of `z >>> k`.
    On a negative `z` the two differ (`Z.testbit` reads the infinite
    two's-complement sign extension, this answers 0), and nothing in
    this file passes one: the only callers are `popcount_aux`,
    `bits_all_open` and `bits_all_pollable`, whose `z` is either
    `bv_unsigned v` or a `Z.lor` of three of them. -/
def z_testbit (z : Int) (k : Nat) : Bool := ((z.toNat >>> k) &&& 1) == 1

/-- `Z.ones n`: the low `n` bits set, `2 ^ n - 1`, and 0 at or
    below zero (`Int.toNat` of a non-positive is 0, and `2 ^ 0 - 1 = 0`
    is `Z.ones`'s own answer there).

    It reaches the bitmap only through `fd_set_scanned`, which masks the
    partial last word — `~(~0UL << (n & (BITS_PER_LONG-1)))` in
    `max_select_fd` is `Z.ones n` for every `n` in the modeled band. -/
def z_ones (n : Int) : Int := 2 ^ n.toNat - 1

/-- The 2 little-endian bytes of a word's low quarter — a `short` as the
    kernel's `put_user` stores it.  `ppoll`'s `revents` is the one field
    any modeled syscall writes at this width.

    `BvBase.lean` carries `word_le8` and not `word_le2`/`word_le4`, so it
    is restated
    here rather than added to another module's file.  It is
    definitionally the first two bytes of `word_le8`. -/
def word_le2 (v : word) : List byte := [bits 0 8 v, bits 8 8 v]

/-! ## The modeled band, and the fd-set encoding -/

/-- The largest `n` whose answer is a function of the MODELED state, and
    it is `Uapi.NR_OPEN_DEFAULT` rather than a number that happens to
    equal it.

    `core_sys_select` clamps `n` to `fdt->max_fds` before it sizes the
    bitmaps, and `max_fds` is a property of the fd TABLE's allocation
    history, not of which descriptors are open.  The model tracks open
    descriptors (`m_fds`) and not the table that holds them, so above
    that floor it cannot say how many bytes the kernel reads and writes
    back.  At or below it the clamp provably never bites -- which is the
    floor argument `Uapi.NR_OPEN_DEFAULT` carries, used here for the
    clamp where `Fs.File.dup3_spec` uses it for `expand_files`.

    Being `BITS_PER_LONG` it is also exactly one `long` of bitmap, which
    is why the modeled band needs no multi-word bitmap walk at all. -/
def pselect_nfds_max : Int := NR_OPEN_DEFAULT

/-- `FDS_BYTES(n)` for the modeled band.  `FDS_BYTES` rounds up to whole
    `long`s, so every `n` in `[1, 64]` costs exactly one 8-byte word and
    `n = 0` costs none -- and at `n = 0` neither `get_fd_set` nor
    `set_fd_set` touches the pointer at all, however wild it is. -/
def pselect_touches_sets (n : Int) : Bool := !(n == 0)

/-- One requested descriptor set, as the kernel imports it: the bitmap
    word at `p`, or all-zero when `p` is NULL (`get_fd_set` memsets its
    kernel copy instead of reading) or when `n` is 0 (a zero-length
    `copy_from_user` always succeeds).  `none` is the unreadable
    pointer that `get_fd_set` answers -EFAULT for. -/
def read_fd_set (mp : word → Option byte) (p : word) (n : Int) :
    Option word :=
  if !(pselect_touches_sets n) then some (BitVec.ofInt 64 0)
  else if w_is0 p then some (BitVec.ofInt 64 0)
  else read_u64 mp p

/-- The bits of a requested set that `do_select` actually scans.
    `max_select_fd` masks the partial last word with
    `~(~0UL << (n & (BITS_PER_LONG-1)))`, and `do_select` breaks out of
    its inner loop at `i >= n`, so a bit at or above `n` is invisible
    to the -EBADF test, to the scan, and to the returned count -- and it
    is CLEARED in the write-back, because the result words start zeroed
    and are assigned wholesale. -/
def fd_set_scanned (v : word) (n : Int) : word :=
  v &&& BitVec.ofInt 64 (z_ones n)

/-- The bytes `set_fd_set` copies back for one set: none when the set
    was not requested, one little-endian word otherwise. -/
def fd_set_writeback (p : word) (n : Int) (v : word) :
    List (word × List byte) :=
  if !(pselect_touches_sets n) then []
  else if w_is0 p then []
  else [(p, word_le8 v)]

/-- `do_select`'s return value is the TOTAL number of bits it set across
    the three result masks, not the number of ready descriptors: a
    descriptor ready for both reading and writing increments `retval`
    twice. -/
def popcount_aux (z : Int) : Nat → Int
  | 0 => 0
  | k + 1 => (if z_testbit z k then 1 else 0) + popcount_aux z k

def popcount64 (v : word) : Int := popcount_aux (v.toNat : Int) 64

/-- Every descriptor named by a set bit of `v` below position `k` is
    OPEN.  This is `max_select_fd`'s `set & ~*open_fds` test, which runs
    over the union of the three requested sets BEFORE any descriptor is
    polled -- so one closed descriptor makes the whole call -EBADF
    whatever the others would have answered. -/
def bits_all_open (fds : List (word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k + 1 =>
      (if z_testbit z k
       then match fd_lookup fds (BitVec.ofInt 64 k) with
            /- KIND-BLIND ON PURPOSE, unlike `bits_all_pollable` below.
               This asks only whether the descriptor is OPEN, which is
               what -EBADF turns on, and a new `FdEntry` constructor is
               open like any other.  Enumerating here would turn a
               future constructor into a compile error for no reason. -/
            | some _ => true
            | none => false
       else true)
      && bits_all_open fds z k

/-- Every descriptor named by a set bit of `v` below `k` has the
    CONSTANT poll mask.

    `vfs_poll` returns `DEFAULT_POLLMASK` for any file whose
    `f_op->poll` is NULL.  No DIRECTORY `file_operations` in the tree
    defines one -- `simple_dir_operations` and
    `simple_offset_dir_operations` (fs/libfs.c), `kernfs_dir_fops`,
    `proc_dir_operations` and `proc_sys_dir_file_operations` all lack
    it -- and neither do the
    REGULAR-FILE `file_operations` of the ordinary on-disk and in-memory
    filesystems, which take the `generic_file_*`
    operations.

    THAT DOES NOT EXTEND TO `S_IFREG` IN GENERAL, and the difference is
    worth stating.  At
    the pinned commit there are 227 `.poll` entries inside
    `struct file_operations` initializers -- counted by walking each
    initializer from its opening brace to its closing `};`, which is why
    the number is far below a bare grep for `.poll`: most such members
    belong to `v4l2_file_operations` or `proto_ops` and are not
    `file_operations` at all.  procfs installs `.poll = proc_reg_poll` on EVERY
    regular file it creates (fs/proc/inode.c), and sysctl, kernfs (so
    sysfs and cgroupfs), debugfs, tracefs, securityfs, POSIX message
    queues, ocfs2 dlmfs and FUSE all install one on `S_IFREG` inodes.
    Several answer masks that `DEFAULT_POLLMASK` would get wrong:
    `mounts_poll` (fs/proc_namespace.c) is `EPOLLIN|EPOLLRDNORM` and
    never sets `EPOLLOUT` on any path, and `fuse_file_poll`'s mask is
    whatever the userspace daemon returns.

    So what `bits_all_pollable` rests on is NOT a fact about which
    file_operations define `->poll`.  It is an ENVIRONMENT OBLIGATION,
    stated here as one: every path in the initial image names an
    ordinary file on an ordinary filesystem.  Nothing in the model
    enforces that.  `Fs.valid_fs` requires only that the image be sorted
    and NUL-free, and `Equivalence.strong_universal_T` quantifies over
    every image satisfying it, so `("/proc/self/mounts", bytes)` is an
    admissible input: `openat` would mint an ordinary `FdFile` for it and
    this predicate would answer `true`, where Linux consults
    `mounts_poll` and reports no `EPOLLOUT`.  That is a model-vs-Linux
    fidelity gap, not a break in the equivalence -- source and target are
    judged against the same model, so both get the same answer.
    A run whose working directory is on tmpfs meets the obligation:
    tmpfs regular files take
    `shmem_file_operations` (mm/shmem.c shmem_get_inode), which has no
    `->poll`, and every `FdFile` is a bare name in that directory, since
    `openat` declines a pathname with a separator (Open.v,
    `path_has_slash`).  The directory descriptors -- the cwd, and its
    parent through ".." -- rest on the tree-wide claim above instead.
    `ioctl` carries the identical commitment in the identical shape.

    Anon-inode descriptors are the one neighbouring worry that is NOT
    an obligation: `alloc_anon_inode` (fs/libfs.c) sets no `S_IFMT`
    bits at all, so an eventfd or an epoll fd can never be mistaken for
    a regular file.  That holds unconditionally.

    `DEFAULT_POLLMASK` is
    `EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM`, which meets `POLLIN_SET`
    and `POLLOUT_SET` and misses `POLLEX_SET` -- so a file or directory
    descriptor is unconditionally readable and writable and never
    exceptional, with no dependence on its contents, its offset, or the
    passage of time.  That is what makes an answer possible here without
    a readiness notion.

    `FdChannel` is the opposite case and is why this predicate exists.
    A channel may be a pipe, and a pipe's readiness
    is a function of what the peer has written SO FAR -- wall-clock
    arrival, which the model does not represent.  `m_stdin` says which
    bytes will eventually arrive, not which have.  Answering from it
    would assert that a pipe with pending input is ready NOW, which is
    false for any peer slower than the reader; answering "not ready"
    would be false whenever it is. -/
def bits_all_pollable (fds : List (word × FdEntry)) (z : Int) : Nat → Bool
  | 0 => true
  | k + 1 =>
      (if z_testbit z k
       then match fd_lookup fds (BitVec.ofInt 64 k) with
            /- ENUMERATED ON PURPOSE, no wildcard.  A `some _ => true`
               catch-all here would be extensionally identical today,
               and would silently absorb the NEXT `FdEntry`
               constructor -- asserting a pipe end or a socket
               unconditionally readable AND writable, which is an
               unsound ACCEPT rather than a decline.  A wildcard stays
               exhaustive, so the compiler would not flag it and no proof would
               break.  Listing the kinds that ARE unconditionally
               pollable makes a new constructor a compile error
               instead. -/
            | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir => true
            | some (.FdFileRW _ _) => true
            /- the same regular file, opened O_RDWR.  A regular file has
               no `->poll` whatever its access mode, so `vfs_poll` hands
               back `DEFAULT_POLLMASK` here as it does for the kinds
               above -/
            | some (.FdFileA _ _) => true
            /- the same regular file, opened in append mode.  O_APPEND
               changes where a write lands, not which `->poll` the
               inode has, and a regular file still has none -- so
               `vfs_poll` hands back `DEFAULT_POLLMASK` here exactly as
               it does for the three kinds above -/
            | some (.FdChannel _) | some (.FdSocket _) | none => false
            /- A PIPE END IS THE `FdChannel` CASE WITH THE PEER INSIDE
               THE MODEL, and it declines for the same reason.
               `pipeanon_fops` defines `.poll = pipe_poll`
               (fs/pipe.c:1261, v6.18.46), so a pipe end never takes
               `DEFAULT_POLLMASK`: `pipe_poll` (:660) reports EPOLLIN only
               when the ring is non-empty (:688-690) and EPOLLOUT only
               when it is not full (:695-697), so
               readiness is a function of what the OTHER end has
               written and consumed so far.  Answering `true` would
               assert a fresh pipe's read end readable, which
               `pipe_poll` denies on an empty ring -- and would assert
               it WRITABLE, which is wrong unconditionally: the read
               end holds FMODE_READ alone, so `pipe_poll`'s EPOLLOUT
               branch never runs for it and no ring state makes it meet
               POLLOUT_SET.  Deriving the real
               answer needs the queue state and the peer's schedule,
               so this fails closed to `PsCoreGap`. -/
            | some (.FdPipe _ _) => false
            | some (.FdDevNull _ _) => false
            /- FAIL-CLOSED, though derivable: `null_fops`
               (drivers/char/mem.c, v6.18.46) has no `.poll`, so
               `vfs_poll` hands back `DEFAULT_POLLMASK` for /dev/null
               exactly as it does for a regular file, and the answer
               would be `true`.  It is declined until that arm is
               written; a decline here is
               `PsCoreGap`, never a wrong answer. -/
            | some .FdUrandom => false
            /- FAIL-CLOSED, the same way: `urandom_fops`
               (drivers/char/random.c, v6.18.46) has no `.poll` — the
               blocking `random_fops` is the table that does — so the
               answer is `DEFAULT_POLLMASK` and would be `true`.  Not
               written; declined. -/
       else true)
      && bits_all_pollable fds z k

/-- A range the call will WRITE must be writable end to end, or the model
    declines.

    `set_fd_set` and `put_timespec64` are `copy_to_user`s, which copy a
    PREFIX and then fault: an 8-byte write straddling a page boundary
    whose second page is unmapped lands 4 bytes and returns -EFAULT, and
    a set written earlier in the `inp`, `outp`, `exp` order stays
    written when a later one faults.  The model has no representation
    for "some unspecified prefix landed", so it declines the whole shape
    rather than assert a byte count it cannot derive.  The band is
    narrow: an unreadable set already answered -EFAULT at import, so
    what is left is a set that is readable but not writable, i.e. one
    living in .rodata. -/
def range_writable (i : SyscallInput) (a : word) (len : Int) : Bool :=
  match read_bytes_map i.in_wmem a (BitVec.ofInt 64 len) with
  | some _ => true
  | none => false

def writes_all_writable (i : SyscallInput)
    (ws : List (word × List byte)) : Bool :=
  ws.all (fun w => range_writable i w.1 (w.2.length : Int))

/-- The sixth argument, after `get_sigset_argpack` and
    `set_user_sigmask`.  Most architectures cannot take a seventh
    syscall argument, so `pselect6` packs the signal mask into a
    {`sigset_t *`, `size_t`} pair in memory and takes a pointer to
    that.  Both musl and glibc's `pselect` always pass one, and musl's
    plain `select` passes the constant pair {NULL, 8} rather than a NULL
    pointer -- so "no mask" reaches the kernel as a real 16-byte read,
    and modeling only the NULL sixth argument would leave `select`
    itself outside the modeled surface. -/
inductive PselectSig where
  /-- the pair itself is unreadable: -EFAULT -/
  | PsSigFault
  /-- no mask: the sixth argument is NULL, or its first word is -/
  | PsSigNone
  /-- a mask with the wrong `sigsetsize`: -EINVAL -/
  | PsSigBadSize
  /-- a mask that would be installed: unmodeled -/
  | PsSigReal
  deriving DecidableEq, Repr

open PselectSig

def pselect_sigpack (mp : word → Option byte) (sig : word) : PselectSig :=
  if w_is0 sig then PsSigNone
  else match read_u64 mp sig, read_u64 mp (sig + BitVec.ofInt 64 8) with
       | some sp, some ss =>
           if w_is0 sp then PsSigNone
             /- `set_user_sigmask` returns 0 on a NULL mask BEFORE it looks
                at the size, so {NULL, anything} is "no mask" -- the 8 musl
                passes is never read. -/
           else if (ss.toNat : Int) == kernel_sigset_bytes then PsSigReal
           else PsSigBadSize
       | _, _ => PsSigFault

/-- The fifth argument, after `get_timespec64` and
    `poll_select_set_timeout`.

    `do_pselect` hands `poll_select_set_timeout` the RAW pair --
    `poll_select_set_timeout(to, ts.tv_sec, ts.tv_nsec)` -- and
    `get_timespec64` normalizes nothing, so `timespec64_valid` judges the
    fields exactly as the program wrote them: `tv_sec < 0` is invalid,
    and so is a `tv_nsec` at or above `NSEC_PER_SEC` when read as
    `unsigned long`, which every negative value is.  A `tv_nsec` of
    1000000000 is therefore -EINVAL and NOT one second.

    The carry that would make it one second belongs to a different
    function: `kern_select`, which serves the `select` and `_newselect`
    numbers, converts microseconds to nanoseconds and folds the overflow
    into `tv_sec`.  riscv64 has neither of those numbers, so that path is
    unreachable here -- and importing its rule would make the model
    answer a deadline four ways the kernel answers -EINVAL.  (musl's
    `select` wrapper does the same fold in USER space before issuing
    `pselect6`, which is why the difference is invisible through it and
    visible through `pselect` and through a raw call.)

    The three admissible shapes are kept apart because they decide the
    TIMEOUT WRITE-BACK, which is the whole difficulty of this syscall --
    see `pselect_finish`. -/
inductive PselectTimeout where
  /-- `tsp` unreadable: -EFAULT -/
  | PsToFault
  /-- `timespec64_valid` rejects it: -EINVAL -/
  | PsToInval
  /-- `tsp` NULL: no deadline at all -/
  | PsToNone
  /-- exactly {0,0}: poll once and return -/
  | PsToZero
  /-- a real deadline -/
  | PsToDeadline
  deriving DecidableEq, Repr

open PselectTimeout

def pselect_timeout (mp : word → Option byte) (tsp : word) :
    PselectTimeout :=
  if w_is0 tsp then PsToNone
  else match read_u64 mp tsp, read_u64 mp (tsp + BitVec.ofInt 64 8) with
       | some sec, some nsec =>
           if decide (sec.toInt < 0) then PsToInval
           else if decide (NSEC_PER_SEC ≤ (nsec.toNat : Int)) then PsToInval
                  /- the `unsigned long` cast in `timespec64_valid`:
                     a negative `tv_nsec` is an enormous unsigned one -/
           else if w_is0 sec && w_is0 nsec then PsToZero
           else PsToDeadline
       | _, _ => PsToFault

/-- What `core_sys_select` answers, before `poll_select_finish` decides
    the timeout write-back. -/
inductive PselectCore where
  /-- the model declines -/
  | PsCoreGap
  /-- a deterministic errno -/
  | PsCoreErr (e : Int)
  | PsCoreDone (ret : Int) (ws : List (word × List byte))
  deriving DecidableEq, Repr

open PselectCore

/-- `core_sys_select` within the modeled band.

    ORDER, and it is the kernel's: `n < 0` is -EINVAL before anything is
    read; the three sets are copied in, `inp` then `outp` then `exp`,
    and an unreadable one is -EFAULT; then `max_select_fd` answers
    -EBADF if any requested descriptor is closed, before a single
    descriptor is polled.  The -ENOMEM the kernel can raise between the
    -EINVAL and the -EFAULT is UNREACHABLE here: `core_sys_select`
    allocates on the stack whenever `FDS_BYTES(n)` is at most
    `SELECT_STACK_ALLOC / 6` = 42 bytes, and the modeled band caps
    `FDS_BYTES(n)` at 8.  That is what lets this spec commit to an
    answer at all, rather than having to union an optional allocation
    failure with every later verdict. -/
def pselect_core (i : SyscallInput) (m : Model)
    (n32 inp outp exp : word) : PselectCore :=
  let n := nfds_signed n32
  if decide (n < 0) then PsCoreErr EINVAL
  else if decide (pselect_nfds_max < n) then PsCoreGap
  else
    match read_fd_set i.in_mem inp n,
          read_fd_set i.in_mem outp n,
          read_fd_set i.in_mem exp n with
    | some rin, some rout, some rex =>
        let win := fd_set_scanned rin n
        let wout := fd_set_scanned rout n
        let wex := fd_set_scanned rex n
        let all := z_lor (z_lor (win.toNat : Int) (wout.toNat : Int))
                         (wex.toNat : Int)
        let k := n.toNat
        if !(bits_all_open (m_fds m) all k) then PsCoreErr EBADF
        else if !(bits_all_pollable (m_fds m) all k) then PsCoreGap
        else
          /- Every polled descriptor carries `DEFAULT_POLLMASK`, so the
             read and write sets come back UNCHANGED, the exception set
             comes back empty, and the count is the total number of bits
             across the three -- two for a descriptor named in both
             `readfds` and `writefds`. -/
          PsCoreDone (popcount64 win + popcount64 wout)
                     (fd_set_writeback inp n win
                      ++ fd_set_writeback outp n wout
                      ++ fd_set_writeback exp n (BitVec.ofInt 64 0))
    | _, _, _ => PsCoreErr EFAULT

/-- An errno return: no user memory is written on any error path that
    the modeled band reaches. -/
def pselect_err (e : Int) : Option (word × List (word × List byte)) :=
  some (errno_ret e, [])

/-- The 16 zero bytes `put_timespec64` writes for a remaining time of
    {0,0}. -/
def pselect_timespec_zero : List byte := List.replicate 16 (BitVec.ofInt 8 0)

def pselect_writes (i : SyscallInput) (ret : Int)
    (ws : List (word × List byte)) : Option (word × List (word × List byte)) :=
  if writes_all_writable i ws then some (BitVec.ofInt 64 ret, ws) else none

/-- `poll_select_finish` -- and the reason most of this syscall is not
    modeled.  STATED OVER AN ABSTRACT `PselectCore` rather than over
    `core_sys_select`, because the kernel's function is shared: ppoll
    (73) reaches the identical call with the identical `PT_TIMESPEC`
    argument, so `ppoll_outcome` reuses this definition unchanged and
    every sentence below is about both syscalls.

    Every return that comes out of `core_sys_select` passes through it,
    errors included, and it writes the REMAINING TIME back to `*tsp`.
    That value is `end_time - ktime_get_ts64()`, sampled after the work
    is done, so its content is a function of how long the call took.  The
    model has no clock and no representation of elapsed time, so the only
    returns it can describe are the ones where that write does not
    happen, or happens with a value that is forced:

    - `tsp` NULL, or a requested timeout that normalized to {0,0}:
      `poll_select_finish` returns early and writes nothing at all.
    - a real deadline that the call ran out: `end_time` is now in the
      past, the clamp `if (rts.tv_sec < 0) rts.tv_sec = rts.tv_nsec = 0`
      fires, and exactly 16 zero bytes are written.  The hrtimer range
      slack only ever fires LATE
      (`hrtimer_set_expires_range_ns` keeps the soft expiry at the
      deadline and pushes the hard one out), so a deadline can never be
      reached early and the remaining time can never be positive.
    - a real deadline that the call did NOT run out -- any positive
      return, and every errno from `core_sys_select` -- is where the
      value is a live clock reading.  UNMODELED.

    The expiry case assumes `current->personality` carries no
    `STICKY_TIMEOUTS`: `poll_select_finish` tests that bit before it
    looks at the deadline and returns with `*tsp` untouched when it is
    set, so the 16 zero bytes would not be written.  That is an
    ENVIRONMENT PREMISE rather than a kernel fact -- `execve` preserves
    the bit (`SET_PERSONALITY` keeps every flag above `PER_MASK`) and
    only `personality(2)` sets it -- and, like the `->poll` premise of
    `bits_all_pollable`, it is not discharged by the model: a run must
    start with the personality `PER_LINUX` and no flag.

    Because every polled descriptor in the modeled band is always ready
    for reading and writing and NEVER exceptional, a real deadline is
    reached exactly when no bit below `n` is set in `readfds` or in
    `writefds`: an `n` of 0, NULL pointers for those two, or sets with no
    bit below `n`.  `exceptfds` is not part of that condition --
    `DEFAULT_POLLMASK` misses `POLLEX_SET`, so an `exceptfds` bit never
    raises the count and the set always comes back zeroed.  So there are
    two modeled shapes in which this syscall waits, not one: the
    portable-sleep idiom `select(0, NULL, NULL, NULL, &tv)`, and an
    `exceptfds`-only request naming an open file or directory.  The model
    says WHAT that wait returns and not how long it takes, which is the
    same partial-correctness reading every other syscall here gets; a
    `tv_sec` near `TIME64_MAX` -- where `timespec64_add_safe` saturates
    the deadline rather than overflowing it -- still returns 0,
    eventually.

    The NULL-timeout case has the opposite corner.
    `schedule_hrtimeout_range_clock` treats a NULL expiry as infinite --
    it calls `schedule()` and returns -EINTR, so `do_select`'s
    `timed_out` flag is never set and the loop cannot exit with a zero
    count.  A zero count under a NULL timeout therefore means the call
    never returns at all, and the model has no way to say that:
    UNMODELED rather than an invented 0. -/
def pselect_finish (i : SyscallInput) (tsp : word)
    (tmo : PselectTimeout) (c : PselectCore) :
    Option (word × List (word × List byte)) :=
  match c with
  | PsCoreGap => none
  | PsCoreErr e =>
      match tmo with
      | PsToDeadline => none   /- the errno carries a live clock reading with it -/
      | _ => pselect_err e
  | PsCoreDone ret ws =>
      match tmo with
      | PsToNone => if ret == 0 then none else pselect_writes i ret ws
      | PsToZero => pselect_writes i ret ws
      | PsToDeadline =>
          if ret == 0
          then pselect_writes i 0 (ws ++ [(tsp, pselect_timespec_zero)])
          else none
      | _ => none   /- unreachable: `pselect6_outcome` answers these first -/

/-- `pselect6 n inp outp exp tsp sig` -- the ONE outcome the modeled band
    admits, or `none` where the model declines (fail closed).

    Nothing here is nondeterministic.  Readiness, the one thing this
    syscall exists to report, is a kernel CONSTANT for every descriptor
    kind the model has: `vfs_poll` hands back `DEFAULT_POLLMASK` for any
    file with no `->poll` method, and neither regular files nor
    directories define one on any filesystem in the tree.  A descriptor
    whose readiness is a schedule rather than a constant -- the piped
    stdio channels -- is refused by `bits_all_pollable` instead of
    guessed at.

    The arms below are in the kernel's own decision order, so reading
    them top to bottom is reading `SYSCALL_DEFINE6(pselect6, ...)`,
    `do_pselect` and `core_sys_select` in sequence. -/
def pselect6_outcome (i : SyscallInput) (m : Model)
    (n32 inp outp exp tsp sig : word) :
    Option (word × List (word × List byte)) :=
  let core := pselect_core i m n32 inp outp exp
  match pselect_sigpack i.in_mem sig, pselect_timeout i.in_mem tsp with
  /- `get_sigset_argpack`, in the syscall entry, before `do_pselect` -/
  | PsSigFault, _ => pselect_err EFAULT
  /- `get_timespec64` and `poll_select_set_timeout` -/
  | _, PsToFault => pselect_err EFAULT
  | _, PsToInval => pselect_err EINVAL
  /- `set_user_sigmask` -/
  | PsSigBadSize, _ => pselect_err EINVAL
  | PsSigReal, _ => none    /- the model has no signals; see `pselect_sigpack` -/
  /- `core_sys_select`, then `poll_select_finish` -/
  | PsSigNone, PsToNone => pselect_finish i tsp PsToNone core
  | PsSigNone, PsToZero => pselect_finish i tsp PsToZero core
  | PsSigNone, PsToDeadline => pselect_finish i tsp PsToDeadline core

def pselect6_spec (n32 inp outp exp tsp sig : word) :
    SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
    match pselect6_outcome i m n32 inp outp exp tsp sig with
    | none => unmodeled
    | some (r, ws) => pure (mkEffect r ws [])

/-! ## ppoll (73)

    `SYSCALL_DEFINE5(ppoll, struct pollfd __user *, ufds, unsigned int,
    nfds, struct __kernel_timespec __user *, tsp, const sigset_t __user *,
    sigmask, size_t, sigsetsize)` is defined in the same fs/select.c, so
    it belongs in this file for the same reason pselect6 does, and it
    shares three of its four steps verbatim.  Its body IS
    `do_pselect`'s with the middle replaced:

      1. `get_timespec64` on a non-NULL `tsp`, then
         `poll_select_set_timeout` -- the same -EFAULT then -EINVAL, on
         the same RAW fields, judged by the same non-strict
         `timespec64_valid`.  `pselect_timeout` answers it unchanged.
      2. `set_user_sigmask`, whose errnos `return` from the syscall
         entry DIRECTLY and never reach `poll_select_finish`.
      3. `do_sys_poll`, where the two syscalls differ.
      4. `poll_select_finish`, reached from step 3 alone, with
         `PT_TIMESPEC` -- the same function, the same argument, the same
         remaining-time write-back.  `pselect_finish` answers it
         unchanged, which is why that definition is stated over an
         abstract `PselectCore` rather than over `core_sys_select`.

    THE SIXTH ARGUMENT IS NOT PACKED HERE.  pselect6 needs seven values
    and has six registers, so it takes a pointer to a
    {`sigset_t *`, `size_t`} pair and unpacks it with
    `get_sigset_argpack`; ppoll needs five and passes the mask pointer
    and the size as arguments 3 and 4.  So ppoll has no -EFAULT for an
    unreadable argpack and no `PsSigFault` equivalent AHEAD of the
    timeout -- its only mask -EFAULT is `set_user_sigmask`'s own
    `copy_from_user`, which runs AFTER the timeout is judged.  Reading
    the ORDER off pselect6 and transplanting it would put that -EFAULT
    two steps too early.

    WHAT `do_sys_poll` ADDS, AND WHAT EACH ADDITION COSTS.

    Readiness is answered exactly as `core_sys_select` answers it and
    for the same reason: `vfs_poll` returns `DEFAULT_POLLMASK` for any
    file with no `->poll` method, so a regular file or a directory is
    unconditionally readable and writable and never exceptional, with no
    dependence on contents, offset or time.  Every caveat
    `bits_all_pollable` carries carries here unchanged -- including the
    undischarged environment obligation, since a
    `("/proc/self/mounts", bytes)` image would reach `ppoll_revents_of`'s
    `FdFile` arm the same way -- and so does the decline of every
    descriptor whose readiness is a schedule rather than a constant.

    Three things are genuinely new:

    - AN UNOPENED DESCRIPTOR IS AN ANSWER, NOT AN ERROR.  Where
      `max_select_fd` makes one closed descriptor -EBADF for the whole
      call, `do_pollfd` sets `mask = EPOLLNVAL` for it, reports that in
      the entry's `revents`, and COUNTS it.  A negative `fd` is neither:
      `do_pollfd` returns 0 before `fdget`, and the entry's `revents` is
      written as 0 and not counted.  This is the one place the two
      syscalls disagree about the same descriptor.
    - THE ENTRY'S `events` IS A FILTER.  `do_pollfd` builds
      `filter = demangle_poll(pollfd->events) | EPOLLERR | EPOLLHUP` and
      answers `mangle_poll(vfs_poll(...) & filter)`.  Neither
      `EPOLLERR` nor `EPOLLHUP` is in `DEFAULT_POLLMASK`, so they
      contribute nothing, and what survives is
      `DEFAULT_POLLMASK & events`.  riscv64 has no `asm/poll.h`, so its
      POLL* constants are include/uapi/asm-generic/poll.h's, which are
      bit-for-bit the EPOLL* values of include/uapi/linux/eventpoll.h, so
      `mangle_poll` and `demangle_poll` (include/linux/poll.h) are the
      identity on every bit that can survive the mask, and on every bit
      of `events` that the mask can select.  So a bit of `events` outside
      `DEFAULT_POLLMASK` cannot change the answer, whether or not
      `demangle_poll` recognises it, and this spec needs no envelope on
      `events` at all.
    - THE ARRAY IS COPIED IN AND WRITTEN BACK ENTRY BY ENTRY.
      `do_sys_poll` copies `nfds` whole `struct pollfd`s with one
      `copy_from_user` and then, after `do_poll`, writes back the
      `revents` field of each -- two bytes at offset 6 of each entry --
      with `unsafe_put_user` under one `user_write_access_begin`.  The
      write-back runs on EVERY return out of `do_poll`, a zero count
      included, so a call that timed out still rewrites every entry's
      `revents`.

    WHERE THE ORDERING COMES FROM.  As for pselect6: the bodies of
    `SYSCALL_DEFINE5(ppoll, ...)`, `do_sys_poll`, `do_poll` and
    `do_pollfd`.  poll.2's ERRORS section is alphabetical like every
    other man page's and says nothing about precedence.

    NONE OF THIS IS CHECKED AGAINST A KERNEL TREE, so every claim
    above is cited by file and function at v6.18.46, the version the
    rest of this file is pinned to, in the style of its neighbours --
    not by line number, which would be a precision this work does not
    have. -/

/-- `struct pollfd` is {`int fd`, `short events`, `short revents`}
    (include/uapi/asm-generic/poll.h): 8 bytes on LP64 with no padding,
    and `revents` the last two of them.  `do_sys_poll` copies the whole
    thing in and writes back only those two. -/
def pollfd_bytes : Int := 8

def pollfd_revents_off : Int := 6

/-- The largest `nfds` whose answer is a function of the MODELED state,
    and it is a stack-allocation bound rather than a descriptor one.

    `do_sys_poll` keeps the imported array in `stack_pps`, a
    `POLL_STACK_ALLOC` = 256-byte buffer, and chains `kmalloc`ed
    `struct poll_list` blocks after it for anything that does not fit;
    a failed `kmalloc` is -ENOMEM.  `N_STACK_PPS` is
    `(sizeof(stack_pps) - sizeof(struct poll_list)) / sizeof(struct
    pollfd)` = (256 - 16) / 8 = 30, `struct poll_list` being a pointer,
    an `unsigned int` and a flexible array, so 16 bytes on LP64.  At or
    below 30 entries the chain is never extended, no allocation happens
    and -ENOMEM does not exist -- which is what lets this spec commit to
    an answer at all, exactly as `core_sys_select`'s
    `SELECT_STACK_ALLOC` argument does for pselect6.  Above it the model
    would have to union an allocation failure with every verdict, so it
    declines.

    This is a SMALLER band than pselect6's `pselect_nfds_max`, and for
    an unrelated reason: pselect6 stops at `NR_OPEN_DEFAULT` because
    `core_sys_select` clamps `n` to `fdt->max_fds`; ppoll indexes no
    bitmap and has no such clamp. -/
def ppoll_nfds_max : Int := 30

/-- `POLLNVAL`, the answer `do_pollfd` gives for a descriptor that is
    not open: it sets `mask = EPOLLNVAL` before `fdget` and jumps to the
    write-back with it when `fd_empty` holds.  0x20 in both the POLL*
    and the EPOLL* encodings, which coincide on riscv64. -/
def POLLNVAL : Int := 32

/-- `DEFAULT_POLLMASK` (include/linux/poll.h) is
    `EPOLLIN|EPOLLOUT|EPOLLRDNORM|EPOLLWRNORM` = 0x1|0x4|0x40|0x100. -/
def default_pollmask : Int := 325

/-- One imported entry's `fd`, read as the `int` it is: `do_pollfd`'s
    first test is `fd < 0`, which is signed. -/
def pollfd_fd (bs : List byte) : Int :=
  sint32 (le_bytes_to_word (bs.take 4))

/-- One imported entry's `events`.  Read as 16 unsigned bits: the field
    is a `short` and `demangle_poll` takes it as a `u16`, but the sign
    cannot matter here -- see the `events` paragraph above. -/
def pollfd_events (bs : List byte) : Int :=
  (le_bytes_to_word ((bs.drop 4).take 2)).toNat

/-- The array as `do_sys_poll` read it, entry by entry.  `bs` is the
    single `copy_from_user`'s worth of bytes; a shorter list than `k`
    entries cannot arise, since the caller reads exactly
    `pollfd_bytes * nfds` of them or none. -/
def decode_pollfds (bs : List byte) : Nat → List (Int × Int)
  | 0 => []
  | k + 1 =>
      (pollfd_fd bs, pollfd_events bs)
        :: decode_pollfds (bs.drop pollfd_bytes.toNat) k

/-- `do_pollfd` for one entry, or `none` where the model declines.

    The three arms are the function's own: `fd < 0` returns 0 without
    looking anything up; a descriptor that is not open takes
    `EPOLLNVAL`; anything else is `vfs_poll` masked by the entry's
    filter. -/
def ppoll_revents_of (fds : List (word × FdEntry)) (fd events : Int) :
    Option Int :=
  if decide (fd < 0) then some 0
  else match fd_lookup fds (BitVec.ofInt 64 fd) with
       | none => some POLLNVAL
       | some (.FdFile _ _) | some (.FdFileW _ _) | some .FdDir =>
           some (z_land default_pollmask events)
       | some (.FdFileRW _ _) =>
           /- the same regular file, opened O_RDWR.  A regular file has no
              `->poll` whatever its access mode, so `vfs_poll` hands back
              `DEFAULT_POLLMASK` here as it does for the three kinds
              above -- the same argument `bits_all_pollable` makes for
              pselect6 -/
           some (z_land default_pollmask events)
       | some (.FdFileA _ _) =>
           /- the same regular file in append mode, for the reason
              `bits_all_pollable` gives above: O_APPEND changes where a
              write lands, not which `->poll` the inode has, and a
              regular file still has none, so `vfs_poll` hands back
              `DEFAULT_POLLMASK` here exactly as it does for the three
              kinds beside it -/
           some (z_land default_pollmask events)
       /- ENUMERATED ON PURPOSE, exactly as `bits_all_pollable` is and
          for the same reason: a `some _ => true` catch-all would be
          extensionally identical today and would silently absorb the
          next `FdEntry` constructor as unconditionally ready.  A
          channel, a socket and a pipe end each have a `->poll` method
          whose answer is a function of what a peer has done so far,
          which this model does not represent -- and note that
          `EPOLLERR` and `EPOLLHUP` are in the filter unconditionally,
          so not even an `events` of 0 makes such a descriptor's answer
          derivable. -/
       | some (.FdChannel _) | some (.FdSocket _) | some (.FdPipe _ _) => none
       | some (.FdDevNull _ _) => none
           /- FAIL-CLOSED, for the reason `bits_all_pollable` gives: the
              answer is `DEFAULT_POLLMASK` because `null_fops` has no
              `.poll`, and it is not written yet -/
       | some .FdUrandom => none
           /- the same: `urandom_fops` has no `.poll` either -/

def ppoll_revents (fds : List (word × FdEntry)) (es : List (Int × Int)) :
    Option (List Int) :=
  match es with
  | [] => some []
  | (fd, ev) :: rest =>
      match ppoll_revents_of fds fd ev with
      | none => none
      | some r =>
          match ppoll_revents fds rest with
          | none => none
          | some rs => some (r :: rs)

/-- `do_poll`'s return: the number of entries whose `do_pollfd`
    answered a non-zero mask.  Within the modeled band that is exactly
    the number of non-zero `revents`, because every mask this spec
    produces -- 0, `EPOLLNVAL`, or a subset of `DEFAULT_POLLMASK` --
    survives `mangle_poll` unchanged, so the mask is zero exactly when
    the stored `revents` is.  Unlike pselect6's, this count is a
    DESCRIPTOR count: one entry contributes at most 1 however many bits
    its `revents` carries. -/
def ppoll_count : List Int → Int
  | [] => 0
  | r :: rest => (if r == 0 then 0 else 1) + ppoll_count rest

/-- The write-back: two bytes at offset 6 of each entry, in entry
    order, one `unsafe_put_user` each.  Named separately rather than as
    one range because that is what the kernel writes -- the `fd` and
    `events` fields in between are not rewritten. -/
def ppoll_writeback (p : word) : List Int → List (word × List byte)
  | [] => []
  | r :: rest =>
      (p + BitVec.ofInt 64 pollfd_revents_off, word_le2 (BitVec.ofInt 64 r))
        :: ppoll_writeback (p + BitVec.ofInt 64 pollfd_bytes) rest

/-- `do_sys_poll` within the modeled band.

    ORDER, and it is the kernel's: `nfds > rlimit(RLIMIT_NOFILE)` is
    -EINVAL before a byte is copied; then the single `copy_from_user`
    of the whole array, an unreadable byte anywhere in it being -EFAULT
    with nothing written back; then `do_poll`.  The limit test is
    answered from state rather than argued around -- `State.m_nofile`
    carries the soft RLIMIT_NOFILE the run was launched with, the same
    field `Fs.File.dup3_spec` tests -- and it is tested BEFORE this
    spec's own `ppoll_nfds_max` decline, so an `nfds` that is both above
    30 and above the limit gets the kernel's -EINVAL rather than a
    decline.

    `nfds = 0` touches `ufds` not at all: `copy_from_user` of zero bytes
    reads nothing, `do_poll` walks no entries and the write-back loop
    writes none, however wild the pointer is. -/
def ppoll_core (i : SyscallInput) (m : Model) (ufds nfds : word) :
    PselectCore :=
  let n := (nfds.toNat : Int)
  if decide (((m_nofile m).toNat : Int) < n) then PsCoreErr EINVAL
  else if decide (ppoll_nfds_max < n) then PsCoreGap
  else
    match read_bytes_map i.in_mem ufds
            (BitVec.ofInt 64 (pollfd_bytes * n)) with
    | none => PsCoreErr EFAULT
    | some bs =>
        match ppoll_revents (m_fds m) (decode_pollfds bs n.toNat) with
        | none => PsCoreGap
        | some rs => PsCoreDone (ppoll_count rs) (ppoll_writeback ufds rs)

/-- `set_user_sigmask` (kernel/signal.c), reached with the mask pointer
    and the size as separate arguments.

    Its order is its own: a NULL `umask` returns 0 BEFORE the size is
    looked at, so {NULL, anything} is "no mask"; then
    `sigsetsize != sizeof(sigset_t)` is -EINVAL; then the
    `copy_from_user` is -EFAULT.  A mask that would be INSTALLED is
    where the model stops: `set_user_sigmask` saves `current->blocked`
    into `current->saved_sigmask` and installs the caller's, which is a
    read and a write of state this model does not carry.  Widening this
    arm means moving `State.with_sigmask` in the same commit, exactly as
    `pselect_sigpack`'s `PsSigReal` does. -/
inductive PpollSig where
  /-- no mask: the pointer is NULL -/
  | PpSigNone
  /-- the wrong `sigsetsize`: -EINVAL -/
  | PpSigBadSize
  /-- the mask itself is unreadable: -EFAULT -/
  | PpSigFault
  /-- a mask that would be installed: unmodeled -/
  | PpSigReal
  deriving DecidableEq, Repr

open PpollSig

def ppoll_sigmask (mp : word → Option byte) (sig sigsetsize : word) :
    PpollSig :=
  if w_is0 sig then PpSigNone
  else if !((sigsetsize.toNat : Int) == kernel_sigset_bytes)
  then PpSigBadSize
  else match read_bytes_map mp sig (BitVec.ofInt 64 kernel_sigset_bytes) with
       | some _ => PpSigReal
       | none => PpSigFault

/-- `ppoll ufds nfds tsp sigmask sigsetsize` -- the ONE outcome the
    modeled band admits, or `none` where the model declines (fail
    closed).

    The arms are in the kernel's own decision order, so reading them top
    to bottom is reading `SYSCALL_DEFINE5(ppoll, ...)` in sequence.
    Note where `poll_select_finish` is and is not: the two
    `set_user_sigmask` errnos below return from the entry directly and
    write no timeout back, while everything `ppoll_core` answers --
    errnos included -- passes through it. -/
def ppoll_outcome (i : SyscallInput) (m : Model)
    (ufds nfds tsp sig sigsetsize : word) :
    Option (word × List (word × List byte)) :=
  match pselect_timeout i.in_mem tsp with
  /- `get_timespec64` and `poll_select_set_timeout` -/
  | PsToFault => pselect_err EFAULT
  | PsToInval => pselect_err EINVAL
  | tmo =>
      /- `set_user_sigmask` -/
      match ppoll_sigmask i.in_mem sig sigsetsize with
      | PpSigBadSize => pselect_err EINVAL
      | PpSigFault => pselect_err EFAULT
      | PpSigReal => none
      | PpSigNone =>
          /- `do_sys_poll`, then `poll_select_finish` -/
          pselect_finish i tsp tmo (ppoll_core i m ufds nfds)

def ppoll_spec (ufds nfds tsp sig sigsetsize : word) :
    SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
    match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
    | none => unmodeled
    | some (r, ws) => pure (mkEffect r ws [])

/-! ## Sanity checks

    There is no closed goal in this file — it is forty
    definitions and their prose.  The checks below are PORT CHECKS, and
    they pin the computable things the prose argues for:

    - the fd-set BIT ENCODING: which bits a set imports, which survive
      the `max_select_fd` mask, and which the count reports;
    - the EMPTY SET WITH A ZERO TIMEOUT, the portable-sleep idiom, which
      returns 0 having written nothing — and its NULL-timeout corner,
      which is `unmodeled`;
    - -EBADF for a descriptor named by a requested set and not open, and
      the bit ABOVE `n` that does not raise it;
    - the nfds BANDS: -EINVAL for a negative `n` and for ppoll's
      over-the-limit `nfds`, and a DECLINE (`unmodeled`) above each
      spec's own band, which is not an errno;
    - the DEADLINE write-back, and the `{0,0}` timeout that writes
      nothing — the two shapes `pselect_finish` keeps apart.

    Plus ppoll's entry decoding, its `revents` write-back and
    `do_pollfd`'s three arms. -/

/-! ### The fd-set bit encoding -/

/-- A set is touched unless `n` is 0 — the test `get_fd_set`/`set_fd_set`
    turn on. -/
example : pselect_touches_sets 0 = false := by decide
example : pselect_touches_sets 1 = true := by decide
example : pselect_touches_sets 64 = true := by decide

/-- `max_select_fd`'s mask keeps the bits BELOW `n` and clears the rest:
    `0x41` under `n = 3` scans as `1`, under `n = 7` as `0x41`, and under
    `n = 0` as nothing at all. -/
example : fd_set_scanned 0x41 3 = 1 := by decide
example : fd_set_scanned 0x41 7 = 0x41 := by decide
example : fd_set_scanned 0x41 0 = 0 := by decide
example : fd_set_scanned 0x41 64 = 0x41 := by decide

/-- The count is the number of bits, not of descriptors: `0x41` is two. -/
example : popcount64 0x41 = 2 := by decide
example : popcount64 0 = 0 := by decide
example : popcount64 0xffffffffffffffff = 64 := by decide

/-- An all-zero word is an empty request, so nothing is scanned. -/
example : popcount_aux 0 64 = 0 := by decide
example : popcount_aux 1 64 = 1 := by decide

/-! ### -EBADF, and the bit above `n` that does not raise it -/

/-- A tiny fd table for the checks: 0 a channel, 1 a regular file, 2 a
    directory.  Fds 3 and above are NOT open. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x61 : byte), 0x62] 0),
    (2, FdEntry.FdDir) ]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt, no rlimit and no tid — so
    the soft RLIMIT_NOFILE is `default_nofile` = 1024. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- Bit 5 set, and `n = 6`: fd 5 is named by the request and is not
    open, which is -EBADF whatever the other bits would have answered. -/
example : bits_all_open demoFds 0x20 6 = false := by decide

/-- …and the same bit with `n = 5` is INVISIBLE — `do_select` breaks out
    at `i >= n`, so it is never looked up. -/
example : bits_all_open demoFds 0x20 5 = true := by decide

/-- `bits_all_open` is KIND-BLIND: fd 0 — a CHANNEL, which
    `bits_all_pollable` refuses — answers `true`, because -EBADF turns
    only on whether the descriptor is OPEN.  A bit naming an fd the table
    does not hold answers `false`. -/
example : bits_all_open demoFds 0x7 3 = true := by decide
example : bits_all_open demoFds 0x1 1 = true := by decide
example : bits_all_open demoFds 0x8 4 = false := by decide

/-- `bits_all_pollable` is the ENUMERATED one: a regular file and a
    directory are unconditionally pollable, and a CHANNEL is not — its
    readiness is a schedule.  The last line is the bit ABOVE `n`, which
    is never looked up. -/
example : bits_all_pollable demoFds 0x6 3 = true := by decide
example : bits_all_pollable demoFds 0x1 1 = false := by decide
example : bits_all_pollable demoFds 0x10 4 = true := by decide

/-- …and a PIPE END and a SOCKET decline for the same reason. -/
example : bits_all_pollable [(0, FdEntry.FdPipe 0 true)] 0x1 1 = false := by
  decide

/-! ### The pselect6 outcome, arm by arm

    The memory image: byte 1 is 0x20 (bit 5), byte 16 onwards is 16 zero
    bytes (a `{0,0}` timespec), and nothing else is mapped. -/
private def demoMem : word → Option byte :=
  sanityMem ([0, 32] ++ List.replicate 14 0 ++ List.replicate 16 0)

/-- An input for the checks: syscall 72, the memory image below, and a
    writable view that maps nothing (only zero-byte write-backs are
    exercised through it). -/
private def demoInput : SyscallInput :=
  { in_sysno := 72, in_args := [], in_mem := demoMem,
    in_wmem := fun _ => none }

/-- Bit 5 of the imported set, `n = 6`, and fd 5 not open: -EBADF, and
    nothing is written. -/
example :
    pselect6_outcome demoInput demoModel 6 1 0 0 0 0
      = some (errno_ret EBADF, []) := by
  decide

/-- THE EMPTY SET WITH A ZERO TIMEOUT: `select(0, NULL, NULL, NULL, &tv)`
    with `tv = {0,0}` polls once and returns 0, and writes no set back
    (`n = 0` touches no pointer). -/
example :
    pselect6_outcome demoInput demoModel 0 0 0 0 16 0 = some (0, []) := by
  decide

/-- …AND ITS NULL-TIMEOUT CORNER IS `unmodeled`: a zero count under a
    NULL timeout means the call never returns, which the model declines
    rather than inventing a 0 for. -/
example : pselect6_outcome demoInput demoModel 0 0 0 0 0 0 = none := by
  decide

/-- A NEGATIVE `n` IS -EINVAL before anything is read.

    The register reaches `pselect_core` ALREADY NARROWED to 32 bits — that
    is the dispatcher's `nfds32`, applied once at the ABI boundary — so
    the check narrows first and `nfds_signed` of the low half `0xffffffff`
    is -1.  (`nfds_signed` of the FULL register would be 2^64 - 2^32, not
    -1: the narrowing and the sign read are two steps, and only the
    second is this definition's.) -/
example :
    pselect6_outcome demoInput demoModel (nfds32 (BitVec.ofInt 64 (-1)))
        0 0 0 0 0
      = some (errno_ret EINVAL, []) := by
  decide

/-- AN `n` ABOVE THE BAND IS A DECLINE, NOT AN ERRNO: 65 is past
    `NR_OPEN_DEFAULT`, so the model declines (and the spec is
    `unmodeled`). -/
example : pselect6_outcome demoInput demoModel 65 1 0 0 0 0 = none := by
  decide

example :
    pselect6_spec 65 1 0 0 0 0 demoInput demoModel .unmodeled := by
  -- `input`, then `get_model`, then the declining match — both readers
  -- are pure and `bind_unmodeled2` walks the chain
  unfold pselect6_spec
  refine bind_unmodeled2 inputSpec _ demoInput demoModel demoInput demoModel
    [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ demoInput demoModel demoModel demoModel
    [] rfl ?_
  exact unmodeled_intro _ _

/-! ### The deadline arm, and the second shape that waits

    `pselect_finish`'s `PsToDeadline` arm is the one that writes the
    REMAINING TIME back: exactly 16 zero bytes, because the clamp fires
    once the deadline is in the past.  A `{0,0}` timeout (`PsToZero`)
    writes nothing at all — the contrast between the two is the whole
    point of keeping the shapes apart. -/

/-- A memory image with a REAL deadline at 16 (`tv_sec = 1`), a zeroed
    timespec at 32, a set word at address 1 whose bit 2 names fd 2, and
    nothing else mapped. -/
private def demoDeadlineMem : word → Option byte :=
  sanityMem (0 :: 4 :: List.replicate 14 0 ++ [1, 0, 0, 0, 0, 0, 0, 0]
             ++ List.replicate 8 0 ++ List.replicate 16 0)

private def demoInputDeadline : SyscallInput :=
  { in_sysno := 72, in_args := [], in_mem := demoDeadlineMem,
    in_wmem := fun _ => some 0 }

/-- THE PORTABLE-SLEEP IDIOM AT A REAL DEADLINE: the wait is reached (no
    bit below `n = 0` in `readfds` or `writefds`), the count is 0, and
    the 16 zero bytes of remaining time are written back to `*tsp`. -/
example :
    pselect6_outcome demoInputDeadline demoModel 0 0 0 0 16 0
      = some (0, [(16, List.replicate 16 0)]) := by
  decide

/-- …AND THE OTHER WAITING SHAPE: an `exceptfds`-only request naming an
    open descriptor.  `DEFAULT_POLLMASK` misses `POLLEX_SET`, so the
    exception bit never raises the count — it is 0 — and the set comes
    back ZEROED (8 bytes at `exp`), followed by the 16 zero bytes of
    remaining time. -/
example :
    pselect6_outcome demoInputDeadline demoModel 3 0 0 1 16 0
      = some (0, [(1, List.replicate 8 0), (16, List.replicate 16 0)]) := by
  decide

/-- …while the SAME CALL AT A `{0,0}` TIMEOUT writes the set back and no
    timespec at all: `poll_select_finish` returns early on a zeroed
    timeout. -/
example :
    pselect6_outcome demoInputDeadline demoModel 3 0 0 1 32 0
      = some (0, [(1, List.replicate 8 0)]) := by
  decide

/-- A requested set that cannot be imported is -EFAULT, and it is
    reached before any descriptor is examined. -/
example :
    pselect6_outcome demoInput demoModel 6 0x7000 0 0 0 0
      = some (errno_ret EFAULT, []) := by
  decide

/-- THE SPEC'S -EBADF ARM: the errno word, no writes, the model
    untouched, nothing emitted.  Each `bind` is `input`, then
    `get_model`, and `input` is pure at the head of the chain. -/
example :
    pselect6_spec 6 1 0 0 0 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  unfold pselect6_spec
  refine bind_ok inputSpec _ demoInput demoModel demoInput demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  refine bind_ok getModelSpec _ demoInput demoModel demoModel demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  exact pure_ok _ _ _

/-! ### ppoll's entries, its count and its write-back -/

/-- `struct pollfd` decoding, little-endian and signed where the kernel
    reads signed: fd 0 with `events = 1`. -/
example : decode_pollfds [0, 0, 0, 0, 1, 0] 1 = [(0, 1)] := by decide

/-- A NEGATIVE fd: `do_pollfd` answers 0 before `fdget`, so it is
    neither -EBADF nor `POLLNVAL`. -/
example : decode_pollfds [255, 255, 255, 255, 0, 0] 1 = [(-1, 0)] := by
  decide
example : ppoll_revents_of demoFds (-1) 0 = some 0 := by decide

/-- AN UNOPENED DESCRIPTOR IS AN ANSWER HERE, NOT AN ERROR: fd 5 takes
    `POLLNVAL`, and it is COUNTED. -/
example : ppoll_revents_of demoFds 5 0 = some POLLNVAL := by decide
example : ppoll_revents demoFds [(5, 0)] = some [POLLNVAL] := by decide
example : ppoll_count [POLLNVAL] = 1 := by decide

/-- A regular file or a directory answers `DEFAULT_POLLMASK & events` —
    the entry's `events` is a filter. -/
example : ppoll_revents_of demoFds 1 0x7 = some 0x5 := by decide
example : ppoll_revents_of demoFds 2 0x7 = some 0x5 := by decide
example : ppoll_revents_of demoFds 1 0 = some 0 := by decide
example : ppoll_revents_of demoFds 2 0x100 = some 0x100 := by decide
-- a bit outside `DEFAULT_POLLMASK` (here `EPOLLPRI`, 0x2) cannot survive
-- the filter, so it contributes nothing: the answer for `events = 0x36`
-- is `DEFAULT_POLLMASK & 0x36 = 0x4`
example : ppoll_revents_of demoFds 2 0x36 = some 0x4 := by decide

/-- …and a CHANNEL declines: its readiness is a schedule. -/
example : ppoll_revents_of demoFds 0 0x1 = none := by decide

/-- The count is a DESCRIPTOR count: two entries, one of them ready, is
    1 — and the zero `revents` is written back as 0, not omitted. -/
example : ppoll_count [0, 0x5] = 1 := by decide
example : ppoll_count [0, 0] = 0 := by decide
example : ppoll_count [] = 0 := by decide

/-- The write-back is two little-endian bytes at offset 6 of each entry,
    in entry order, 8 bytes apart. -/
example : ppoll_writeback 0 [0, 0x5] = [(6, [0, 0]), (14, [5, 0])] := by
  decide

/-- `word_le2` really is the low two bytes of `word_le8`. -/
example : word_le2 0x1234 = [0x34, 0x12] := by decide
example : word_le2 0x1234 = (word_le8 0x1234).take 2 := by decide

/-! ### The ppoll outcome, arm by arm -/

/-- A ppoll memory image: at address 1 a `struct pollfd` of fd -1 and
    `events = 0` (four 0xff bytes, then two zero bytes), the timespec at
    16, and nothing else mapped. -/
private def demoPollMem : word → Option byte :=
  sanityMem ([0, 255, 255, 255, 255, 0, 0]
             ++ List.replicate 9 0 ++ List.replicate 16 0)

/-- An input whose writable view maps every address, so ppoll's
    write-back is not itself the thing under test. -/
private def demoInputW : SyscallInput :=
  { in_sysno := 73, in_args := [], in_mem := demoPollMem,
    in_wmem := fun _ => some 0 }

/-- ONE ENTRY WITH A NEGATIVE fd, AND A ZERO TIMEOUT: the count is 0, the
    entry's `revents` is REWRITTEN as 0, and the call returns 0 — the
    write-back runs on every return out of `do_poll`, a zero count
    included. -/
example :
    ppoll_outcome demoInputW demoModel 1 1 16 0 0 = some (0, [(7, [0, 0])]) := by
  decide

/-- `nfds = 0` touches `ufds` not at all, and returns 0 under a zero
    timeout — no entry, no write-back. -/
example :
    ppoll_outcome demoInputW demoModel 0 0 16 0 0 = some (0, []) := by
  decide

/-- A NULL TIMEOUT WITH A ZERO COUNT IS `unmodeled`, exactly as for
    pselect6: `do_sys_poll` would wait forever. -/
example : ppoll_outcome demoInputW demoModel 0 0 0 0 0 = none := by decide

/-- AN OVERSIZED `nfds` IS -EINVAL, from the RLIMIT_NOFILE test that runs
    BEFORE the band's own decline: 1025 is above the default 1024. -/
example :
    ppoll_outcome demoInputW demoModel 0 1025 0 0 0
      = some (errno_ret EINVAL, []) := by
  decide

/-- …and an `nfds` that is above the BAND but under the limit declines
    (31 > 30, 1024 ≥ 31): a decline, not an errno. -/
example : ppoll_outcome demoInputW demoModel 0 31 0 0 0 = none := by decide

example :
    ppoll_spec 0 31 0 0 0 demoInputW demoModel .unmodeled := by
  unfold ppoll_spec
  refine bind_unmodeled2 inputSpec _ demoInputW demoModel demoInputW demoModel
    [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ demoInputW demoModel demoModel demoModel
    [] rfl ?_
  exact unmodeled_intro _ _

/-- An unreadable array is -EFAULT, and nothing is written back. -/
example :
    ppoll_outcome demoInputW demoModel 0x7000 1 0 0 0
      = some (errno_ret EFAULT, []) := by
  decide

/-- A mask pointer whose `sigsetsize` is wrong is -EINVAL, and it is
    reached AFTER the timeout is judged — the one ordering fact that
    differs from pselect6's argpack. -/
example :
    ppoll_outcome demoInputW demoModel 0 0 0 1 4 = some (errno_ret EINVAL, []) := by
  decide

/-- …while a mask of the right size that IS readable would be installed,
    which the model does not carry: `unmodeled`. -/
example : ppoll_outcome demoInputW demoModel 0 0 0 1 8 = none := by decide

/-- `ppoll_sigmask`'s own three-way split. -/
example : ppoll_sigmask demoMem 0 4 = PpollSig.PpSigNone := by decide
example : ppoll_sigmask demoMem 1 4 = PpollSig.PpSigBadSize := by decide
example : ppoll_sigmask demoMem 1 8 = PpollSig.PpSigReal := by decide
example : ppoll_sigmask demoMem 0x7000 8 = PpollSig.PpSigFault := by decide

/-- `pselect_timeout`'s: NULL is no deadline, a `{0,0}` pair is the zero
    timeout, a negative `tv_sec` and an over-large `tv_nsec` are both
    -EINVAL, and an unreadable pair is -EFAULT. -/
example : pselect_timeout demoMem 0 = PselectTimeout.PsToNone := by decide
example : pselect_timeout demoMem 16 = PselectTimeout.PsToZero := by decide
example : pselect_timeout demoMem 0x7000 = PselectTimeout.PsToFault := by decide

/-- `1000000000` nanoseconds is NOT one second: `timespec64_valid` reads
    `tv_nsec` unsigned and refuses anything at or above `NSEC_PER_SEC`. -/
private def demoTsOverNsec : word → Option byte :=
  sanityMem (List.replicate 24 0 ++ [0, 202, 154, 59, 0, 0, 0, 0])

example : pselect_timeout demoTsOverNsec 16 = PselectTimeout.PsToInval := by
  decide

/-- …and a negative `tv_sec` is -EINVAL too, read SIGNED. -/
private def demoTsNegSec : word → Option byte :=
  sanityMem (List.replicate 16 0 ++ List.replicate 8 255
             ++ List.replicate 8 0)

example : pselect_timeout demoTsNegSec 16 = PselectTimeout.PsToInval := by
  decide

/-- The constants, at the values the prose quotes. -/
example : pselect_nfds_max = 64 := by decide
example : ppoll_nfds_max = 30 := by decide
example : POLLNVAL = 32 := by decide
example : default_pollmask = 325 := by decide
example : pollfd_bytes = 8 := by decide
example : pollfd_revents_off = 6 := by decide
example : pselect_timespec_zero = List.replicate 16 (0 : byte) := by decide
example : pselect_timespec_zero.length = 16 := by decide

/-- The three errnos in the return word, as every arm above hands them
    back. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EFAULT = BitVec.ofInt 64 (-14) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide

end LinuxSem.LinuxProcessSem.Sys.Fs.Select
