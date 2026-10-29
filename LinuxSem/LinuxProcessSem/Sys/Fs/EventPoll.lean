/-
  * LinuxProcessSem.Sys.Fs.EventPoll — epoll_create1 (20), epoll_ctl (21),
    epoll_pwait (22)

  This file answers to Linux `fs/eventpoll.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines the
  syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  here that is `SysSpec SyscallEffect` from `MonadInstances`. The `sys_scope`
  sequencing `x <- c;; k` is `bind c (fun x => k)` in Lean, which is how the two
  chains in `epoll_ctl_spec` and `epoll_pwait_spec` are written (`input` →
  `inputSpec`, `get_model` → `getModelSpec`).

  `Z` → `Int`; `bv n` → `BitVec n`;
  `bv_unsigned w` → `(w.toNat : Int)`; `bv_signed w` → `w.toInt`;
  `Z_to_bv n z` → `BitVec.ofInt n z`; `Z.eqb a b` → `a == b`;
  `Z.ltb`/`Z.leb` → `<`/`≤`; `negb b` → `!b`; `option`/`list` →
  `Option`/`List`.  `FdEntry`'s constructors keep names, so
  every `match` below reads against the  text line for line.

  Lean core has no `Int` bitwise
  operations, so `Sys.Uapi`'s `z_land` is `Z.land` on non-negative
  `Int`s.  `epoll_create1_outcome` masks with `Z.lnot EPOLL_CLOEXEC mod
  2 ^ 32`; `EPOLL_CLOEXEC` is `2 ^ 19`, so that complement is
  `2 ^ 32 - 1 - EPOLL_CLOEXEC` — the expression written below, pinned
  by a `by decide` check at the bottom of the file rather than asserted.

  This port imports it for the same reason and nothing else, and takes only
  `bits_all_pollable` from it — the two predicates partition the descriptor kinds,
  and nothing else would notice if one moved and the other did not.

  `EpollSigmask` derives `DecidableEq,
  Repr`; `Inductive` carries neither.  This is the same
  benign addition `Fs.Select` makes to its `PselectSig`, and it is what
  lets the checks below compare `epoll_sigmask`'s answer with `decide`.
  `FdEntry` itself still has no `DecidableEq` (its `FdSocket` arm
  reaches the coinductive `SockState`), so descriptor-table equations
  are `simp` over the table's keys instead.

  The  file carries exactly one
  proof — the complement claim `fd_can_poll_is_select_pollable`, ported
  below — and no `decide` goal beyond it.  The checks at the end
  are PORT CHECKS: they pin the constants, the epoll_create1 flag gate
  (including the 2^32 truncation the prose argues for), the epoll_ctl
  arm order (-EFAULT before -EBADF before -EPERM before -EINVAL, and
  the channel decline), and the epoll_pwait sigmask/size/range arms.
-/

import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Fs.File
import LinuxSem.LinuxProcessSem.Sys.Fs.Select

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.LinuxProcessSem.Sys.Fs.Select (bits_all_pollable)

namespace LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll

/- WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name.  Every body quoted below was read from the
    pinned tree itself — stable v6.18.46, commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, this repository's kernel
    of record — rather than from a mainline tag standing in for it.  The
    tags below WERE fetched, and only to bound the windows: every text
    that is CITED is the pinned commit's, and where a tag's text is named
    as differing, that difference was read off the tag itself.  That
    distinction is not pedantry here: `fs/eventpoll.c` is NOT frozen
    across the 6.18.x series.  A rework lands between v6.18.39 and
    v6.18.40 (a rewritten file banner, `linux/seqlock.h`, an
    `ep_deliver_event` delivery path, and `ep_remove_safe` renamed to
    `ep_remove`) which mainline v6.19 does not carry.  So "v6.18.x
    behaves like mainline v6.18" is FALSE for this file, and a window
    written as a mainline range would be wrong for two of the functions
    below.

      fs/eventpoll.c              `do_epoll_create`,
                                  `SYSCALL_DEFINE1(epoll_create1, ...)`,
                                  `SYSCALL_DEFINE4(epoll_ctl, ...)`,
                                  `do_epoll_ctl`, `ep_check_params`,
                                  `do_epoll_wait`, `do_epoll_pwait`,
                                  `SYSCALL_DEFINE6(epoll_pwait, ...)`,
                                  `ep_timeout_to_timespec`, `ep_poll`,
                                  `is_file_epoll`, `eventpoll_fops`,
                                  `EP_MAX_EVENTS`, `EPOLLEXCLUSIVE_OK_BITS`
      include/linux/poll.h        `file_can_poll`, `vfs_poll`
      include/linux/eventpoll.h   `ep_op_has_event`
      include/uapi/linux/eventpoll.h
                                  `struct epoll_event`, `EPOLL_PACKED`,
                                  `EPOLL_CLOEXEC`, `EPOLL_CTL_*`
      kernel/signal.c             `set_user_sigmask`
      include/linux/uaccess.h     `_inline_copy_from_user`
      include/asm-generic/access_ok.h
                                  `__access_ok`

    WINDOWS, per function, ending at the pinned commit.  Each was read
    by fetching `fs/eventpoll.c` at the tag and comparing the function's
    own text; the bound given is the earliest tag that matches AND whose
    successors all match, so a later regression cannot hide inside one.

      v6.18.40 - v6.18.46   `do_epoll_ctl`.  A STABLE-POINT bound, not a
                            mainline one, and the only difference from
                            mainline v6.18's text is the
                            `ep_remove_safe` -> `ep_remove` rename
                            inside the EPOLL_CTL_DEL arm.  Nothing this
                            file models reaches that arm (see
                            `epoll_ctl_outcome`), so the rename is
                            invisible here — but the TEXT is not
                            byte-identical, and this repository pins
                            text.
      v6.18 - v6.18.46      `ep_poll`.  It survived the .40 rework
                            byte-for-byte, so this one IS a genuine
                            mainline bound.
      v6.15 - v6.18.46      `ep_check_params` and `do_epoll_wait`.  A
                            text-identity floor over the probe set, and
                            NOT a claim about when `ep_check_params` was
                            introduced -- nobody established that.
      v6.12 - v6.18.46      `do_epoll_create`.
      at least v5.15        `do_epoll_pwait`, `ep_timeout_to_timespec`.
      at least v5.10        `SYSCALL_DEFINE1(epoll_create1, ...)`,
                            `SYSCALL_DEFINE4(epoll_ctl, ...)`,
                            `file_can_poll`, `EP_MAX_EVENTS`,
                            `EPOLLEXCLUSIVE_OK_BITS`.

    "AT LEAST" IS NOT "UNCHANGED SINCE", and the difference is stated
    rather than smoothed over: v5.10 and v5.15 are the floors of the
    probe set, not established boundaries.  Those functions are
    byte-identical at every tag fetched down to that floor and may well
    go back further; nobody looked.  A reader who needs a real lower
    bound for one of them has to fetch it, and this sentence is what
    tells them the number here will not answer the question.

    WHERE THE ORDERING COMES FROM.  Every ordering claim below is read
    off the bodies of the functions named above and nowhere else.  No
    man page documents error-check ordering — epoll_ctl.2's ERRORS
    section is alphabetical by errno name, which is house style and not
    precedence — so nothing here is taken from a man page, and an
    enumeration of what a call refuses is not a claim about what it
    checks first.

    ON riscv64 THERE IS NO `epoll_create` AND NO `epoll_wait`.  The
    generic 64-bit syscall table carries `epoll_create1` (20),
    `epoll_ctl` (21) and `epoll_pwait` (22) only; glibc and musl both
    compile `epoll_create(size)` to `epoll_create1(0)` and
    `epoll_wait(...)` to `epoll_pwait(..., NULL, 0)`.  So the
    `size <= 0` check in `SYSCALL_DEFINE1(epoll_create, int, size)` is
    unreachable here and is not modeled.

    WHAT THIS FILE DOES NOT MODEL, AND WHY THAT IS THE WHOLE DESIGN.
    `epoll_create1`'s SUCCESS arm is declined.  Everything else follows
    from that one decision, so it is worth stating in full rather than
    as a gap.

    An epoll instance is an interest set plus a ready list, and
    `ep_poll` reports READINESS over the descriptors in it.  This model
    fixes readiness by construction for exactly the descriptor kinds
    that `epoll_ctl` REFUSES: `Select.bits_all_pollable` can answer for
    a file or a directory because `vfs_poll` hands back the constant
    `DEFAULT_POLLMASK` to any file with no `->poll` method, and
    `do_epoll_ctl` rejects precisely those descriptors with -EPERM
    because `file_can_poll` tests that same NULL `->poll`.  The two
    predicates partition the descriptor kinds, and epoll gets the half
    this model cannot observe: a pipe's readiness is a function of what
    the peer has written SO FAR, which is wall-clock arrival, and
    `m_stdin` says which bytes will EVENTUALLY arrive, not which have.
    So pselect6's argument does not extend to epoll — it inverts.

    THAT LEAVES A CHOICE, AND THE OBVIOUS ONE IS A TRAP.  A nullary
    `State.FdEntry` constructor for an epoll fd would compile, and every
    `epoll_ctl` that could populate an interest set would decline, so no
    reachable state would have a non-empty one, so `epoll_pwait` could
    answer 0 on the empty set.  Every step of that is true today.  It is
    still the wrong shape, because the 0 rests on a WHOLE-TREE ABSENCE
    claim — "no modeled transition populates an interest set" — that the
    next change to this file silently falsifies: model one successful
    `EPOLL_CTL_ADD` and `epoll_pwait` keeps answering 0 for a set that
    is not empty, with no check failing anywhere.  A nullary
    constructor has no field to condition that answer on.  So the
    interest set is not represented, no `FdEntry` constructor denotes an
    epoll instance, and `epoll_create1` declines the arm that would mint
    one.

    WHAT THAT BUYS, and it is more than it sounds.  Because no fd in a
    modeled state is an epoll instance, `is_file_epoll` is FALSE for
    every descriptor the model can hand these syscalls — so both
    `epoll_ctl` and `epoll_pwait` reach their -EINVAL arm on every
    input that gets that far, and neither has any reachable path into
    the interest-set machinery at all.  What remains unanswered is
    small and is named on the arm that answers it: `epoll_ctl` declines
    a CHANNEL target, because whether a channel has a `->poll` is the
    one thing `fd_can_poll` cannot decide; `epoll_pwait` declines a real
    signal mask and a user range whose `access_ok` verdict the model
    cannot settle, both of which `pselect6` already declines for the
    same reasons.  Every other input to either is answered.

    That reach is load-bearing on a fact about a different type, so it
    is guarded by one: `fd_can_poll` is enumerated over
    `State.FdEntry` with no wildcard, so a new constructor is a COMPILE
    ERROR here.  Whoever adds one has to classify it, and the arm they
    have to write is the arm that decides whether the paragraph above
    still holds.

    WHAT THE DECLINE COSTS.  It costs priority 3 and nothing else: a
    program that successfully creates an epoll fd yields `unmodeled` at
    that call, so `Equivalence.strong_universal_T` says nothing about it
    either way, rather than saying something wrong.  Source and target
    are judged against the same model, so no pair of programs is
    separated by this; the class of programs the theorem covers is
    smaller by exactly those that reach a successful `epoll_create1`. -/

/-- `EPOLL_CLOEXEC`, and it is `O_CLOEXEC` rather than a value of its
    own: `include/uapi/linux/eventpoll.h` defines it as `O_CLOEXEC`, and
    `do_epoll_create` opens with `BUILD_BUG_ON(EPOLL_CLOEXEC !=
    O_CLOEXEC)` so the identity is compile-enforced rather than
    conventional.  Spelled through `Uapi.O_CLOEXEC` here for the same
    reason. -/
def EPOLL_CLOEXEC : Int := O_CLOEXEC

/-- `EPOLL_CTL_DEL`.  The other two opcodes are deliberately absent:
    nothing below compares against `EPOLL_CTL_ADD` or `EPOLL_CTL_MOD`,
    because every arm that distinguishes them sits past the -EINVAL
    this model always reaches first.  Naming them here would be a
    constant with no consumer. -/
def EPOLL_CTL_DEL : Int := 2

/-- `sizeof(struct epoll_event)` on riscv64, and it is 16 rather than
    12.  `EPOLL_PACKED` is `__attribute__((packed))` only under
    `#ifdef __x86_64__`; every other architecture, riscv64 included,
    gets the empty definition, so the `__u64 data` member takes its
    natural 8-byte alignment and the struct carries four bytes of
    padding at offsets 4..7.  `SYSCALL_DEFINE4(epoll_ctl, ...)` copies
    `sizeof(struct epoll_event)` bytes, so it copies the padding too:
    an `event` pointer with twelve readable bytes and an unreadable
    thirteenth is -EFAULT. -/
def epoll_event_bytes : Int := 16

/-- `EP_MAX_EVENTS`, which is `INT_MAX / sizeof(struct epoll_event)` —
    so it is a function of the 16 above and is 134217727 here, not the
    178956970 an x86-64 reader would compute from a packed 12. -/
def EP_MAX_EVENTS : Int := 134217727

/-- `file_can_poll`, per descriptor kind: does this file have a
    non-NULL `->poll` method?  `none` where the model cannot say.

    ENUMERATED ON PURPOSE, no wildcard, and this is the guard the header
    note above rests on.  A `_ => some false` catch-all would be
    extensionally identical today for the kinds it covers and would
    silently absorb the next `State.FdEntry` constructor — answering
    -EPERM for a descriptor epoll would happily accept, which is a
    modeled WRONG ANSWER rather than a decline.  Worse, an
    epoll-instance constructor absorbed here would leave
    `epoll_ctl_outcome` and `epoll_pwait_outcome` asserting -EINVAL for
    an epfd that IS an epoll fd, silently converting this file's
    reach argument into a false one.  Listing the kinds makes a new
    constructor a compile error instead, at the site whose answer decides
    both.

    WHY THIS IS AN `Option Bool` AND NOT A `Bool`.  `FdChannel` is the
    reason, and it is the one arm where being able to say nothing is
    what keeps the file sound.  The model does not know what a channel's
    far end IS.  `Fs.Stat`'s `fstat` arm declines a channel because
    "S_IFIFO, S_IFSOCK and S_IFCHR are all live and nothing in the model
    chooses between them"; `Fs.Ioctl`'s answer is earned by WIDENING
    over "whether the far end is a pipe, a terminal or a file"; and
    `State.FdEntry`'s own note calls the direction "an ASSUMPTION about
    the environment rather than a fact about the fd number".  A pipe, a
    terminal and a socket all define `->poll`; a REGULAR FILE and
    /dev/null do not — `null_fops` (drivers/char/mem.c) carries
    `.llseek`, `.read`, `.write`, `.read_iter`, `.write_iter`,
    `.splice_write` and `.uring_cmd`, and no `.poll`.  So a channel
    spans both answers, and committing to either is a guess: `some true`
    would answer -EINVAL where Linux answers -EPERM for a file-backed
    or /dev/null channel, and `some false` would do the reverse for a
    pipe.  That is not hypothetical: plain shell redirection gives a
    program a regular file or /dev/null on fd 0 or 1 — so the wrong answer is one a reference program's launcher
    can reach.

    It is tempting to answer `some true` because pipes define `->poll`
    unconditionally.  Pipes do; that answers the wrong question.
    What is unknown is not whether a pipe polls but whether a channel is
    a pipe.

    THE THREE `some false` ARMS ARE AN ENVIRONMENT OBLIGATION, and it is
    the SAME obligation `Select.bits_all_pollable` carries — stated there
    at length.  Briefly: no
    DIRECTORY `file_operations` in the tree defines `->poll`, and neither
    do the REGULAR-FILE operations of the ordinary on-disk and in-memory
    filesystems, which take the `generic_file_*` set.  That does NOT
    extend to `S_IFREG` in general — procfs installs
    `.poll = proc_reg_poll` on every regular file it creates
    (fs/proc/inode.c), and sysctl, kernfs, debugfs, tracefs, securityfs,
    POSIX message queues, ocfs2 dlmfs and FUSE all install one on
    `S_IFREG` inodes.  So a model state holding an `FdFile` for
    "/proc/self/mounts" would answer -EPERM here where Linux accepts the
    descriptor.  `Fs.valid_fs` admits such an image, so the model does
    not discharge the obligation, exactly as for pselect6; it is
    a model-vs-Linux fidelity gap rather than a break in the equivalence,
    since source and target are judged against the same model.

    THE `FdSocket` AND `FdPipe` ARMS NEED NO OBLIGATION, and they are the
    only ones that do not.  A socket's file is minted by
    `sock_alloc_file` with `socket_file_ops` (net/socket.c), whose
    `.poll` is `sock_poll` unconditionally, on every address family and
    every configuration.  A pipe end gets `pipeanon_fops` when
    `create_pipe_files` (fs/pipe.c) mints it and `pipefifo_fops` when a
    FIFO is opened; BOTH carry `.poll = pipe_poll`, so the distinction
    that matters for `fstat` does not matter here.

    What separates these two from `FdChannel` is not the kernel but the
    model: it KNOWS these descriptors are a socket and a pipe, because it
    minted them itself in `Net.Socket.socket_spec` and `Fs.Pipe`'s
    `pipe2` arm.  A channel is handed to the process by whoever ran it,
    so there is a far end to be unsure about; here there is none. -/
def fd_can_poll (e : FdEntry) : Option Bool :=
  match e with
  | FdEntry.FdFile _ _ | FdEntry.FdFileW _ _ | FdEntry.FdFileA _ _
  | FdEntry.FdFileRW _ _ | FdEntry.FdDir => some false
  | FdEntry.FdSocket _ | FdEntry.FdPipe _ _ => some true
  | FdEntry.FdChannel _ => none
  | FdEntry.FdDevNull _ _ => none
      /- FAIL-CLOSED, though the answer is exact and this file already
         states it: `null_fops` (drivers/char/mem.c, v6.18.46) has no
         `.poll`, so `file_can_poll` is false and `epoll_ctl` ADD is
         -EPERM (fs/eventpoll.c) — the `some false` the file kinds
         carry, with no environment obligation at all.  Declined until
         written. -/
  | FdEntry.FdUrandom => none
      /- FAIL-CLOSED, and the answer is again exact: `urandom_fops`
         (drivers/char/random.c, v6.18.46) has no `.poll` either
         (`random_fops` has one; the urandom table does not), so
         `file_can_poll` is false and `epoll_ctl` ADD is the same
         -EPERM.  Declined until written. -/

/-- The complement claim, as a check rather than a sentence.

    `Select.bits_all_pollable` asks whether a descriptor has the CONSTANT
    `DEFAULT_POLLMASK`; `fd_can_poll` asks whether it has a `->poll`
    method at all.  `vfs_poll` returns `DEFAULT_POLLMASK` exactly when
    `->poll` is NULL, so a descriptor is `Select`-pollable exactly when
    this file can say `some false` — not by coincidence but because the
    two read one kernel fact, and a descriptor kind whose `->poll` status
    changes has to move in both files at once.

    THE THREE-VALUED FORM IS WHAT MAKES THIS TRUE RATHER THAN NEARLY
    TRUE.  A bare complement (`bits_all_pollable = negb (fd_can_poll e)`)
    would force `FdChannel` onto one side, and the two files DECLINE it
    for the same reason from opposite directions: `Select` cannot fix a
    channel's readiness, and this file cannot fix whether a channel has a
    `->poll` to fix readiness with.  Reading one decline as the other's
    positive answer is exactly the error this lemma rules out.

    Stated over a one-entry table at bit 0, which is what
    `bits_all_pollable` scrutinises.  A prose assertion of this would go
    stale silently the first time someone classified a kind differently
    in one file; this does not. -/
theorem fd_can_poll_is_select_pollable (e : FdEntry) :
    bits_all_pollable [(BitVec.ofInt 64 0, e)] 1 1 = true ↔
      fd_can_poll e = some false := by
  cases e <;> simp [fd_can_poll, bits_all_pollable, fd_lookup] <;> decide

/- ------------------------------------------------------------------
   epoll_create1 (20)
   ------------------------------------------------------------------ -/

/-- `do_epoll_create`:

      if (flags & ~EPOLL_CLOEXEC)
              return -EINVAL;
      error = ep_alloc(&ep);...
      fd = get_unused_fd_flags(O_RDWR | (flags & O_CLOEXEC));

    ORDER, and it is the only behaviour this arm has: the flag word is
    judged BEFORE `ep_alloc` and before any descriptor is reserved.  So
    a rejected `epoll_create1` allocates nothing, consumes no fd number,
    and cannot answer -ENOMEM or -EMFILE — the two errnos that follow it
    are unreachable on this path rather than merely unmodeled.

    `flags` is an `int` in `SYSCALL_DEFINE1(epoll_create1, int, flags)`,
    so the register's high half is discarded before a bit is read; the
    dispatcher applies `Syscall.flag32` and this function sees the low
    32 bits.  The mask is taken over 32 bits accordingly: a `flags` of
    2^32 is 0 after truncation and is ACCEPTED, where a 64-bit mask
    would reject it.

    THE SUCCESS ARM IS DECLINED, for the reason the header note gives at
    length: minting an epoll fd needs a `State.FdEntry` constructor, and
    the only constructor available without a readiness notion is a
    nullary one whose correctness rests on an absence claim the next
    change falsifies.  So this syscall is modeled on its rejecting half
    and nowhere else, and a program that successfully creates an epoll
    fd leaves the modeled surface at that call.

  writes the mask as
    `Z.lnot EPOLL_CLOEXEC mod 2 ^ 32`; since `EPOLL_CLOEXEC` is
    `2 ^ 19` that complement is `2 ^ 32 - 1 - EPOLL_CLOEXEC`, which is
    the expression below.  The identification is pinned by a
    `by decide` check at the bottom of the file rather than asserted
    here, and `z_land` is `Sys.Uapi`'s port of `Z.land`. -/
def epoll_create1_outcome (flags32 : word) : Option word :=
  if z_land (flags32.toNat : Int) (2 ^ 32 - 1 - EPOLL_CLOEXEC) == 0
  then none                            -- a well-formed create: declined
  else some (errno_ret EINVAL)

/-- `epoll_create1 flags` — the rejecting half of `do_epoll_create`,
    and nothing else.

    No `get_model` and no fd: the answer is a function of the flag word
    alone, exactly as the kernel's gate is.  The -EINVAL arm touches no
    memory, emits no event and changes no state, which is what the
    kernel does on that path too — it returns before `ep_alloc`. -/
def epoll_create1_spec (flags32 : word) : SysSpec SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | none => unmodeled
  | some r => pure (mkEffect r [] [])

/- ------------------------------------------------------------------
   the shared `copy_from_user` verdict
   ------------------------------------------------------------------ -/

/-- What a fixed-size `copy_from_user` does, in three answers.

    `_inline_copy_from_user` (include/linux/uaccess.h) runs
    `access_ok(from, n)` and jumps to its failure path when that fails,
    so the RANGE check comes first and a range it rejects faults without
    a byte being read.  riscv64 takes that branch rather than the
    `can_do_masked_user_access()` one: `masked_user_access_begin` is not
    defined in arch/riscv/include/asm/uaccess.h at the pinned commit, so
    `include/linux/uaccess.h` gives `can_do_masked_user_access()` the
    value 0 and the address is never clamped.

    Two answers: `true` when the range check passes (`State.access_okb`,
    the kernel's own predicate with `State.TASK_SIZE` as its limit) and
    every byte is mapped; `false` — -EFAULT — when the range check fails,
    or when it passes and some byte is unmapped.

    THE `access_okb` CONJUNCT IS ALSO WHAT RULES OUT THE WRAP.
    `State.read_bytes_map` walks in WORD arithmetic and wraps at 2^64, so
    a 16-byte read at 2^64 - 8 would read eight bytes from the top of
    the address space and eight from address 0 and report success, where
    the kernel's `access_ok` rejects the range outright.  Testing the
    range before reading is what stops that here; a site that reads
    without this test can still wrap. -/
def copy_from_user_ok (mp : word → Option byte) (a : word) (len : Int) : Bool :=
  access_okb a len &&
    (match read_bytes_map mp a (BitVec.ofInt 64 len) with
     | some _ => true
     | none => false)

/- ------------------------------------------------------------------
   epoll_ctl (21)
   ------------------------------------------------------------------ -/

/-- `ep_op_has_event(op)` is `op != EPOLL_CTL_DEL`, and it decides
    whether the syscall entry copies the event struct at all.  `op` is
    an `int`, so the comparison is over the low 32 bits: a register whose
    low half is 2 and whose high half is set is still `EPOLL_CTL_DEL` to
    the kernel, because `SYSCALL_DEFINE4` casts the argument to `int` on
    the way in and the high half is gone before `op` is ever compared.
    THIS FUNCTION does not narrow — it is handed an already-narrowed
    word.  `Syscall.int32`, applied once in the dispatcher arm, is that
    cast, and is where every truncated argument here is narrowed. -/
def ep_op_has_event (op32 : word) : Bool :=
  !((op32.toNat : Int) == EPOLL_CTL_DEL)

/-- `epoll_ctl epfd op fd event` — the one outcome the model admits, or
    `none` where it declines.

    The arms are in the kernel's own decision order, so reading them top
    to bottom is reading `SYSCALL_DEFINE4(epoll_ctl, ...)` and then
    `do_epoll_ctl` in sequence.

    1.  `SYSCALL_DEFINE4` copies the event struct BEFORE calling
        `do_epoll_ctl`, hence before any descriptor is looked up:

          if (ep_op_has_event(op) &&
              copy_from_user(&epds, event, sizeof(struct epoll_event)))
                  return -EFAULT;

        So -EFAULT on a bad `event` pointer BEATS -EBADF on `epfd`,
        -EBADF on the target, and -EPERM.  For `EPOLL_CTL_DEL` no copy
        happens and `event` is never dereferenced, however wild it is —
        `epds` is left uninitialised in that case and the DEL path never
        reads it.
    2.  -EBADF if `epfd` is not open.
    3.  -EBADF if the target is not open.
    4.  -EPERM if the target has no `->poll`:

          /* The target file descriptor must support poll */
          if (!file_can_poll(fd_file(tf)))
                  return -EPERM;

        This is the arm worth knowing, because it sits BEFORE the check
        that `epfd` is an epoll fd.  So `epoll_ctl` on two ordinary
        files answers -EPERM, not -EINVAL: the epfd's epoll-ness is not
        tested until step 5, and a reader who assumed -EINVAL wins
        because "epfd isn't an epoll fd" would have the errno wrong.
    5.  -EINVAL otherwise:

          error = -EINVAL;
          if (fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f)))
                  goto error_tgt_fput;

        No `State.FdEntry` constructor denotes an epoll instance, so
        `is_file_epoll(fd_file(f))` is false for every descriptor
        reachable here and the SECOND disjunct always holds.  The first
        disjunct — the self-add check, which compares `struct file`
        identity and therefore also catches adding a `dup` of the epfd —
        is consequently never the reason, and the model needs no notion
        of description identity to get this errno right.

    EVERYTHING PAST STEP 5 IS UNREACHABLE, which is why none of it
    appears below: the `EPOLLEXCLUSIVE` rejections, `ep_take_care_of_-
    epollwakeup`, `epoll_mutex_lock`, the `ep_loop_check` -ELOOP, and
    the whole `switch (op)` with its -EEXIST and -ENOENT arms all sit
    behind a `goto error_tgt_fput` that step 5 has already taken.  An
    unrecognised `op` is likewise -EINVAL through step 5 rather than
    through the switch's fallthrough — the same errno by a different
    route, which is why `op` is read here only to decide whether the
    event struct is copied.

    THE CONTENTS OF THE EVENT STRUCT ARE NEVER USED, only its
    readability.  `epds->events` is read exclusively by the
    `EPOLLEXCLUSIVE` block and by `ep_insert`/`ep_modify`, all
    unreachable.  So this arm needs the copy's VERDICT and not its
    bytes.

    IT NEVERTHELESS RECORDS NO COPY-IN, AND THAT IS A KNOWN-WRONG
    OMISSION rather than a consequence of the bytes being unused.
    `State.eff_copyins` is not bookkeeping about which bytes an arm
    consulted: `State.syscall_effect_accesses` concatenates it with the
    write ledger and `Run.mi_account_step` hands the result to
    `State.materialize_model_accesses`, which charges newly touched
    pages of a lazy anonymous reservation against `vm_backing_used`.  A
    16-byte `event` on a mapped-but-never-touched anonymous page is
    therefore faulted in and charged by Linux and not by this model,
    which UNDER-charges the budget — the direction that lets the model
    grant an allocation the kernel would refuse.  `pselect6` has the
    identical omission.

    ONE ARM DECLINES, named where it is decided: step 4 on a CHANNEL
    target, where `fd_can_poll` cannot say whether the far end has a
    `->poll`.  Every other step answers. -/
def epoll_ctl_outcome (i : SyscallInput) (m : Model)
    (epfd : word) (op32 : word) (tfd : word) (event : word) : Option word :=
  let after_copy :=
    match fd_lookup (m_fds m) epfd with
    | none => some (errno_ret EBADF)
    | some _ =>
        match fd_lookup (m_fds m) tfd with
        | none => some (errno_ret EBADF)
        | some te =>
            match fd_can_poll te with
            | some false => some (errno_ret EPERM)
            | some true => some (errno_ret EINVAL)
            -- a channel: see `fd_can_poll`
            | none => none
  if ep_op_has_event op32
  then if copy_from_user_ok i.in_mem event epoll_event_bytes
       then after_copy
       else some (errno_ret EFAULT)
  else after_copy

/-- `epoll_ctl epfd op fd event`: the arms above, at the dispatcher's
    types.  Nothing here reads or writes user memory on a modeled path —
    the copy is tested for its verdict and its bytes are dropped (see the
    omission noted on `epoll_ctl_outcome`), and no arm writes anything at
    all. -/
def epoll_ctl_spec (epfd op32 tfd event : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
    match epoll_ctl_outcome i m epfd op32 tfd event with
    | none => unmodeled
    | some r => pure (mkEffect r [] [])

/- ------------------------------------------------------------------
   epoll_pwait (22)
   ------------------------------------------------------------------ -/

/-- `set_user_sigmask`, kernel/signal.c, in its own order:

      if (!umask)
              return 0;
      if (sigsetsize != sizeof(sigset_t))
              return -EINVAL;
      if (copy_from_user(&kmask, umask, sizeof(sigset_t)))
              return -EFAULT;

    NULL is tested BEFORE the size, so `epoll_pwait(..., NULL, 0)` —
    which is what musl's and glibc's `epoll_wait` compile to — installs
    nothing and never looks at the 0.  Modeling only the size-8 case
    would leave `epoll_wait` itself outside the modeled surface.

    `sigsetsize` is a `size_t` and is compared FULL WIDTH, so it is not
    narrowed by the dispatcher; a register whose low half is 8 and whose
    high half is set is the wrong size.  `Uapi.kernel_sigset_bytes` is
    the 8.

    A mask that WOULD BE INSTALLED is `unmodeled`, not an answer: this
    model has no signals, so it cannot represent `current->blocked`
    changing, nor the `restore_saved_sigmask_unless` that puts it back.
    `Select.pselect_sigpack` declines the identical case for the
    identical reason. -/
inductive EpollSigmask where
  /-- `umask` is NULL: nothing installed -/
  | EpSigNone
  /-- wrong `sigsetsize`: -EINVAL -/
  | EpSigBadSize
  /-- `umask` unreadable: -EFAULT -/
  | EpSigFault
  /-- a mask that would be installed: unmodeled -/
  | EpSigReal
  deriving DecidableEq, Repr

open EpollSigmask

def epoll_sigmask (mp : word → Option byte) (umask sigsetsize : word) :
    EpollSigmask :=
  if w_is0 umask then EpSigNone
  else if !((sigsetsize.toNat : Int) == kernel_sigset_bytes) then EpSigBadSize
  else if copy_from_user_ok mp umask kernel_sigset_bytes then EpSigReal
  else EpSigFault

/-- `epoll_pwait epfd events maxevents timeout sigmask sigsetsize` — the
    one outcome the model admits, or `none`.

    ORDER, read off `SYSCALL_DEFINE6(epoll_pwait, ...)`,
    `do_epoll_pwait`, `do_epoll_wait` and `ep_check_params`:

    1. `ep_timeout_to_timespec(&to, timeout)` is an ARGUMENT to `do_epoll_pwait`, so
    it runs first — and it cannot fail. It is also the only reader of `timeout`, and
    its result reaches only `ep_poll`, which no modeled path enters. So `timeout` is
    not an argument of this function at all: no arm below depends on it, including
    the arms that would sleep. 2. `set_user_sigmask` — the first fallible step, and
    it precedes the epfd lookup. A bad sigmask therefore BEATS a bad `epfd`. 3.
    -EBADF if `epfd` is not open. Note this precedes the `maxevents` check, which is
    the reverse of the `epoll_ctl` ordering and is worth stating because the two
    files' checks look interchangeable and are not. 4. -EINVAL if `maxevents <= 0 ||
    maxevents > EP_MAX_EVENTS`. `maxevents` is an `int`, read signed, and the `<= 0`
    test is short-circuited FIRST on purpose: `EP_MAX_EVENTS` has type `size_t`
    through its `sizeof`, so the second comparison promotes `maxevents` to `unsigned
    long`, and a negative value would convert to a huge unsigned one and pass. 5.
    -EFAULT if `access_ok(events, maxevents * sizeof(struct epoll_event))` fails. The
    product is computed in 64-bit unsigned arithmetic (the `int` promotes to
    `size_t`) and CANNOT overflow, because step 4 has already bounded `maxevents` by
    `INT_MAX / 16`. This is a pure RANGE check — Linux reads no byte and requires no
    mapping — and so is the model's: `State.access_okb` on the product, with no walk.
    6. -EINVAL if `epfd` is not an epoll fd. It is not, ever, for the reason the
    header note gives, so every call that reaches step 6 answers -EINVAL and
    `ep_poll` is unreachable.

    NOTHING IS WRITTEN ON ANY MODELED PATH.  `ep_poll` is the only
    writer of the `events` array, through `ep_send_events`, and step 6
    stops short of it.  The `access_ok` of step 5 is a range verdict and
    not a store. -/
def epoll_pwait_outcome (i : SyscallInput) (m : Model)
    (epfd events maxevents32 sigmask sigsetsize : word) : Option word :=
  match epoll_sigmask i.in_mem sigmask sigsetsize with
  | EpSigBadSize => some (errno_ret EINVAL)
  | EpSigFault => some (errno_ret EFAULT)
  | EpSigReal => none
  | EpSigNone =>
      match fd_lookup (m_fds m) epfd with
      | none => some (errno_ret EBADF)
      | some _ =>
          let n := sint32 maxevents32
          if n ≤ 0 then some (errno_ret EINVAL)
          else if EP_MAX_EVENTS < n then some (errno_ret EINVAL)
          else
            if access_okb events (n * epoll_event_bytes)
            then some (errno_ret EINVAL)
            else some (errno_ret EFAULT)

/-- `epoll_pwait epfd events maxevents timeout sigmask sigsetsize`: the
    arms above, at the dispatcher's types.  `timeout` is not an argument,
    for the reason step 1 of `epoll_pwait_outcome` gives. -/
def epoll_pwait_spec (epfd events maxevents32 sigmask sigsetsize : word) :
    SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
    match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
    | none => unmodeled
    | some r => pure (mkEffect r [] [])

/-! ## Sanity checks

  And the rest is definitions and prose. The checks below are PORT CHECKS, and they
  pin the computable things the prose argues for:

    - the four constants, and the `Z.lnot ... mod 2^32` restatement the
      `epoll_create1` mask is written with;
    - the `epoll_create1` gate: -EINVAL for any bit outside
      `EPOLL_CLOEXEC`, including bit 31 and the full word, and the
      ACCEPTED `2^32` that only the 32-bit mask admits;
    - `fd_can_poll` kind by kind, and the channel/dev-null/urandom
      declines;
    - the `epoll_ctl` arm ORDER: -EFAULT over everything when the event
      struct is copied and unreadable, no copy at all for
      `EPOLL_CTL_DEL`, then -EBADF (`epfd`, then target), then -EPERM,
      then -EINVAL, and the channel decline;
    - the `epoll_pwait` sigmask arms (NULL before the size, full-width
      size, then the read), -EBADF before the `maxevents` band, the
      signed `<= 0` test that a `size_t` promotion would swallow, the
      `EP_MAX_EVENTS` bound, and -EFAULT vs -EINVAL at the range check;
    - the descriptor number a SUCCESSFUL `epoll_create1` would take,
      pinned at `File.lowest_fd` — the machinery that owns it, because
      the create arm itself declines and so has no arm to test.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so lookup equations are stated as
    equations between `Option FdEntry` and proved by `simp` on the
    tables' keys rather than by `decide`; everything `Bool`-, `word`-,
    `Int`- or `Option Bool`-valued is `by decide`. -/

/-! ### The four constants -/

example : EPOLL_CLOEXEC = 524288 := by decide
example : EPOLL_CLOEXEC = O_CLOEXEC := by decide
example : EPOLL_CTL_DEL = 2 := by decide
example : epoll_event_bytes = 16 := by decide
example : EP_MAX_EVENTS = 134217727 := by decide
/-- `EP_MAX_EVENTS` really is `INT_MAX / sizeof(struct epoll_event)` at
    the 16 above — 134217727, not the 178956970 of a packed 12. -/
example : EP_MAX_EVENTS = (2147483647 / 16 : Int) := by decide

/-- THE MASK IS `Z.lnot EPOLL_CLOEXEC mod 2 ^ 32`: the complement of a
    power of two within 32 bits, which is `2 ^ 32 - 1 - EPOLL_CLOEXEC`,
    and `by decide` is what says so rather than a sentence. -/
example : (-(EPOLL_CLOEXEC + 1)) % 2 ^ 32 = 2 ^ 32 - 1 - EPOLL_CLOEXEC := by
  decide
example : 2 ^ 32 - 1 - EPOLL_CLOEXEC = 4294443007 := by decide

/-! ### The `epoll_create1` flag gate -/

/-- The admitted words: no flag at all, and `EPOLL_CLOEXEC` itself. -/
example : epoll_create1_outcome 0 = none := by decide
example : epoll_create1_outcome (BitVec.ofInt 64 EPOLL_CLOEXEC) = none := by
  decide

/-- ANY OTHER BIT IS -EINVAL, alone or on top of `EPOLL_CLOEXEC` — and
    the gate is a residue test, so bit 31 (negative as an `int`) and the
    all-ones word are refused rather than read as small. -/
example : epoll_create1_outcome 8 = some (errno_ret EINVAL) := by decide
example : epoll_create1_outcome
    (BitVec.ofInt 64 (EPOLL_CLOEXEC + 8)) = some (errno_ret EINVAL) := by
  decide
example : epoll_create1_outcome (BitVec.ofInt 64 2147483648) =
    some (errno_ret EINVAL) := by decide
example : epoll_create1_outcome (BitVec.ofInt 64 (-1)) =
    some (errno_ret EINVAL) := by decide

/-- THE 2^32 WORD IS ACCEPTED, and that is the whole reason the mask is
    taken over 32 bits: `flags` is an `int`, so the register's high half
    is gone before a bit is read, and `flags = 2^32` is `flags = 0`.  A
    64-bit mask would answer -EINVAL here.  One bit above the truncation
    is refused, because the LOW half already carries an unknown bit. -/
example : epoll_create1_outcome (BitVec.ofInt 64 4294967296) = none := by
  decide
example : epoll_create1_outcome (BitVec.ofInt 64 4294967297) =
    some (errno_ret EINVAL) := by decide
example : epoll_create1_outcome (BitVec.ofInt 64 4294967304) =
    some (errno_ret EINVAL) := by decide

/-- The gate reads the word it is handed and does NOT narrow it again;
    the truncation belongs to the dispatcher's `flag32`, which is what
    the accepted 2^32 above and the refused 2^32 + 8 together pin. -/
example : flag32 (BitVec.ofInt 64 4294967296) = 0 := by decide
example : epoll_create1_outcome (flag32 (BitVec.ofInt 64 4294967296)) =
    none := by decide

/-! ### `fd_can_poll`, kind by kind -/

example : fd_can_poll (FdEntry.FdFile [] 0) = some false := by decide
example : fd_can_poll (FdEntry.FdFileW [] 0) = some false := by decide
example : fd_can_poll (FdEntry.FdFileA [] 0) = some false := by decide
example : fd_can_poll (FdEntry.FdFileRW [] 0) = some false := by decide
example : fd_can_poll FdEntry.FdDir = some false := by decide
example : fd_can_poll (FdEntry.FdSocket SockState.SkFresh) = some true := by
  decide
example : fd_can_poll (FdEntry.FdPipe 0 true) = some true := by decide
/-- The three DECLINES: a channel (the far end is unknown), /dev/null and
    urandom (both exact, both not written yet). -/
example : fd_can_poll (FdEntry.FdChannel 7) = none := by decide
example : fd_can_poll (FdEntry.FdDevNull true true) = none := by decide
example : fd_can_poll FdEntry.FdUrandom = none := by decide

/-! ### `-EFAULT` before `-EBADF`, and the `EPOLL_CTL_DEL` that copies
    nothing -/

/-- A syscall input for the `epoll_ctl` checks: the 32-byte image maps
    addresses 0..31, so a 16-byte struct at 1 or at 16 is readable and
    one at 0x7000 is not. -/
private def demoMem : word → Option byte :=
  sanityMem ([0, 32] ++ List.replicate 14 0 ++ List.replicate 16 0)

private def demoInput : SyscallInput :=
  { in_sysno := 21, in_args := [], in_mem := demoMem,
    in_wmem := fun _ => none }

/-- A tiny fd table: 0 a channel, 1 a regular file, 2 a directory (both
    `some false`, so -EPERM), 3 a pipe end and 4 a socket (both
    `some true`, so -EINVAL).  Fds 5 and above are NOT open. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x61 : byte), 0x62] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdSocket SockState.SkFresh) ]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt, no tid and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- `EPOLL_CTL_DEL` is the op whose event struct is never copied — and
    `ep_op_has_event` is the test, over the low half. -/
example : ep_op_has_event (BitVec.ofInt 64 EPOLL_CTL_DEL) = false := by decide
example : ep_op_has_event 0 = true := by decide
example : ep_op_has_event 1 = true := by decide
example : ep_op_has_event 3 = true := by decide
/-- The high half is GONE before the comparison: the dispatcher's `int32`
    makes 2^32 + 2 the `EPOLL_CTL_DEL` 2, where the unnarrowed register
    would read as "has an event" and demand a copy. -/
example : int32 (BitVec.ofInt 64 4294967298) = 2 := by decide
example : ep_op_has_event (int32 (BitVec.ofInt 64 4294967298)) = false := by
  decide

/-- -EFAULT BEATS EVERYTHING when the struct is copied: fd 5 is not open,
    the target is not looked at, and it is still -EFAULT for a wild
    `event` pointer. -/
example : epoll_ctl_outcome demoInput demoModel 5 3 1 0x7000 =
    some (errno_ret EFAULT) := by decide
/-- …and a 16-byte struct at 1 IS readable, which is why the wild pointer
    above is about the range and not about the copy. -/
example : copy_from_user_ok demoMem 1 16 = true := by decide
/-- …whereas the same call with `EPOLL_CTL_DEL` copies nothing and
    answers -EBADF with the same wild pointer. -/
example : epoll_ctl_outcome demoInput demoModel 5 2 1 0x7000 =
    some (errno_ret EBADF) := by decide
/-- THE `epfd` LOOKUP COMES BEFORE THE TARGET: fd 5 is not open, so the
    answer is -EBADF for `epfd` and the target's kind is never asked. -/
example : epoll_ctl_outcome demoInput demoModel 5 2 0 0 =
    some (errno_ret EBADF) := by decide
/-- …then the TARGET, which is -EBADF on the same two steps. -/
example : epoll_ctl_outcome demoInput demoModel 1 2 5 0 =
    some (errno_ret EBADF) := by decide
/-- …then -EPERM for a target with no `->poll`: a regular file and a
    directory.  This is the arm that sits BEFORE the epfd's epoll-ness
    is tested, so two ordinary files answer -EPERM, not -EINVAL. -/
example : epoll_ctl_outcome demoInput demoModel 1 2 1 0 =
    some (errno_ret EPERM) := by decide
example : epoll_ctl_outcome demoInput demoModel 1 2 2 0 =
    some (errno_ret EPERM) := by decide
/-- …then -EINVAL, for the target kinds that DO have a `->poll` — and
    the epfd is not an epoll instance, ever, so this is the answer every
    call that gets this far receives. -/
example : epoll_ctl_outcome demoInput demoModel 1 2 3 0 =
    some (errno_ret EINVAL) := by decide
example : epoll_ctl_outcome demoInput demoModel 1 2 4 0 =
    some (errno_ret EINVAL) := by decide
/-- …and the ONE DECLINE: a CHANNEL target, where `fd_can_poll` cannot
    say whether the far end has a `->poll`.  It is `none`, not an errno,
    and both spellings reach it — `EPOLL_CTL_DEL`, which copies nothing,
    and an op with an event, whose 16-byte struct at 1 is readable. -/
example : epoll_ctl_outcome demoInput demoModel 1 2 0 1 = none := by decide
example : epoll_ctl_outcome demoInput demoModel 1 3 0 1 = none := by decide

/-- THE SPEC'S -EBADF ARM: the errno word, no writes, the model
    untouched, nothing emitted.  Each `bind` is `input`, then
    `get_model`, and `input` is pure at the head of the chain. -/
example :
    epoll_ctl_spec 1 2 5 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  unfold epoll_ctl_spec
  refine bind_ok inputSpec _ demoInput demoModel demoInput demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  refine bind_ok getModelSpec _ demoInput demoModel demoModel demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  exact pure_ok _ _ _

/-- THE SPEC'S DECLINE: the channel target above is `unmodeled`, and its
    arm carries no errno at all. -/
example : epoll_ctl_spec 1 2 0 1 demoInput demoModel .unmodeled := by
  unfold epoll_ctl_spec
  refine bind_unmodeled2 inputSpec _ demoInput demoModel demoInput demoModel
    [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ demoInput demoModel demoModel demoModel
    [] rfl ?_
  exact unmodeled_intro _ _

/-! ### The `epoll_pwait` sigmask, and its four arms -/

/-- NULL is tested BEFORE the size, so `{NULL, 0}` — what `epoll_wait`
    compiles to — is "no mask" and never looks at the 0. -/
example : epoll_sigmask demoMem 0 0 = EpSigNone := by decide
example : epoll_sigmask demoMem 0 4 = EpSigNone := by decide
/-- A wrong `sigsetsize` is -EINVAL, and it is compared FULL WIDTH: the
    low half 8 with the high half set is the wrong size. -/
example : epoll_sigmask demoMem 1 4 = EpSigBadSize := by decide
example : epoll_sigmask demoMem 1 0 = EpSigBadSize := by decide
example : epoll_sigmask demoMem 1 (BitVec.ofInt 64 4294967304) =
    EpSigBadSize := by decide
/-- The mask itself: readable is a REAL mask (declined by the outcome),
    unreadable is -EFAULT. -/
example : epoll_sigmask demoMem 1 8 = EpSigReal := by decide
example : epoll_sigmask demoMem 0x7000 8 = EpSigFault := by decide

/-! ### The `epoll_pwait` outcome, arm by arm -/

/-- The sigmask errnos come FIRST — before the epfd lookup, which is the
    reverse of `epoll_ctl`'s order: fd 5 is not open, and a wrong size
    still answers -EINVAL. -/
example : epoll_pwait_outcome demoInput demoModel 5 16 1 1 4 =
    some (errno_ret EINVAL) := by decide
/-- …and an unreadable mask is -EFAULT, again before the `epfd`. -/
example : epoll_pwait_outcome demoInput demoModel 5 16 1 0x7000 8 =
    some (errno_ret EFAULT) := by decide
/-- A REAL mask is `unmodeled`: the model has no signals to install it
    into, so it declines rather than inventing an answer. -/
example : epoll_pwait_outcome demoInput demoModel 1 16 1 1 8 = none := by
  decide

/-- -EBADF for an `epfd` that is not open, and it PRECEDES the
    `maxevents` test — where `epoll_ctl`'s ordering is the other way
    round. -/
example : epoll_pwait_outcome demoInput demoModel 5 16 0 0 0 =
    some (errno_ret EBADF) := by decide
example : epoll_pwait_outcome demoInput demoModel 5 16 134217728 0 0 =
    some (errno_ret EBADF) := by decide

/-- `maxevents <= 0` IS -EINVAL, and the signed test comes FIRST: a
    `size_t` promotion would turn -1 into a huge unsigned value that
    passes both bounds, so reading it signed is load-bearing. -/
example : epoll_pwait_outcome demoInput demoModel 1 16 0 0 0 =
    some (errno_ret EINVAL) := by decide
example : epoll_pwait_outcome demoInput demoModel 1 16
    (BitVec.ofInt 64 4294967295) 0 0 = some (errno_ret EINVAL) := by decide
/-- `maxevents > EP_MAX_EVENTS` is -EINVAL too: 134217728 is one past
    the bound, 134217727 is the bound and is admitted to the range
    check. -/
example : epoll_pwait_outcome demoInput demoModel 1 16 134217728 0 0 =
    some (errno_ret EINVAL) := by decide

/-- THE RANGE CHECK: step 4 has bounded `maxevents` by `INT_MAX / 16`, so
    the product cannot overflow, and the test is a pure range check with
    no walk.  A range the model cannot vouch for is -EFAULT. -/
example : epoll_pwait_outcome demoInput demoModel 1 0x7fffffffffffffff 1 0 0 =
    some (errno_ret EFAULT) := by decide
/-- …and a range it can is the LAST arm, -EINVAL: the `epfd` is open and
    is not an epoll instance (it never is, in this model), so `ep_poll`
    is unreachable. -/
example : epoll_pwait_outcome demoInput demoModel 1 16 1 0 0 =
    some (errno_ret EINVAL) := by decide
example : epoll_pwait_outcome demoInput demoModel 1 16 134217727 0 0 =
    some (errno_ret EINVAL) := by decide

/-- THE SPEC'S -EBADF ARM. -/
example :
    epoll_pwait_spec 5 16 1 0 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  unfold epoll_pwait_spec
  refine bind_ok inputSpec _ demoInput demoModel demoInput demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  refine bind_ok getModelSpec _ demoInput demoModel demoModel demoModel []
    (mkEffect (errno_ret EBADF) [] []) demoModel [] rfl ?_
  exact pure_ok _ _ _

/-- THE SPEC'S DECLINE. -/
example : epoll_pwait_spec 1 16 1 1 8 demoInput demoModel .unmodeled := by
  unfold epoll_pwait_spec
  refine bind_unmodeled2 inputSpec _ demoInput demoModel demoInput demoModel
    [] rfl ?_
  refine bind_unmodeled2 getModelSpec _ demoInput demoModel demoModel demoModel
    [] rfl ?_
  exact unmodeled_intro _ _

/-! ### The descriptor number a SUCCESSFUL create would take

    `epoll_create1`'s success arm is DECLINED (the header note gives the
    reason at length), so this spec has no arm that returns a descriptor
    and nothing above tests one.  The number such a call WOULD take is
    the kernel's `get_unused_fd_flags(O_RDWR | (flags & O_CLOEXEC))`,
  which is this tree's `File.lowest_fd` over `State.alloc_fd`; it is
    pinned here at the machinery that owns it, so the declined arm is
    not an untested sentence. -/

example : alloc_fd demoFds = 5 := by decide
example : fd_lookup demoFds 5 = none := by simp [demoFds, fd_lookup]
example : fd_lookup demoFds 4 = some (FdEntry.FdSocket SockState.SkFresh) := by
  simp [demoFds, fd_lookup]

/-- THE SUCCESS ARM OF A SURVIVING CALL, at the machinery that owns it:
    the lowest free descriptor is 5, and it is free. -/
example : lowest_fd demoFds demoInput demoModel (.ok 5 demoModel []) := by
  rw [lowest_fd_ok demoFds 5 demoInput demoModel]
  exact ⟨by simp [demoFds, fd_lookup], by decide⟩

/-- …and with a hole at 2 it is 2, not the end of the table — the LOWEST
    free descriptor, as `do_epoll_create`'s `get_unused_fd_flags` hands
    back. -/
private def demoHoleFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7), (1, FdEntry.FdFile [] 0),
    (3, FdEntry.FdPipe 0 true), (4, FdEntry.FdSocket SockState.SkFresh) ]

private def demoHoleModel : Model :=
  mkModel demoHoleFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

example : alloc_fd demoHoleFds = 2 := by decide
example : lowest_fd demoHoleFds demoInput demoHoleModel
    (.ok 2 demoHoleModel []) := by
  rw [lowest_fd_ok demoHoleFds 2 demoInput demoHoleModel]
  exact ⟨by simp [demoHoleFds, fd_lookup], by decide⟩

/-- The four errno words this file's prose names, as every arm above
    hands them back. -/
example : errno_ret EPERM = BitVec.ofInt 64 (-1) := by decide
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EFAULT = BitVec.ofInt 64 (-14) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide

end LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll
