/-
  * LinuxProcessSem.Sys.Fs.File — the fd table, dup (23), dup3 (24)

  This file answers to Linux `fs/file.c`: it holds what the kernel
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
  and `getModelSpec` is `get_model`.  `StateLedger` supplies
  `m_fds`, `m_nofile`, `with_fds` and `mkModel`; `StateFd` supplies
  `fd_lookup`, `fd_insert` and `alloc_fd`; `Sys.Syscall` supplies
  `ret_only`, `err_ret`, `errno_from` and `flag32`; `Sys.Uapi` supplies
  `O_CLOEXEC` and `NR_OPEN_DEFAULT`.  `Sys.Uaccess` is deliberately NOT
  imported: no user buffer is touched by either spec.  Both `Sys.Uapi`
  and `Sys.Syscall` carry a local `abi_low32`/`fd32` (see their PORT
  NOTEs); neither is used here, so the two names are only shadowed, not
  confused.

  `x <- c;; k` has no Lean
  counterpart, so it is `bind c (fun x => k)` here, and the `;;` that
  discards a unit result is `seqSpec`.  `set_fds fds` is
  `Monad.lean`'s `modify (with_fds fds)`, and that wrapper is
  not part of the Lean monad module, so the two writes below spell it
  `modifySpec (with_fds …)` — the same state update, one unfolding
  further out.

  `Z.ldiff a b` is `a & ~b`; `Sys/Uapi.lean` ports `Z.lor`, `Z.land` and
  `Z.ldiff` together, and the `z_ldiff` below is a transparent alias to
  the canonical definition there, kept so the one caller in this file
  (`dup3_flags_ok`) reads by the local name.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Fs.File

/-- The kernel returns the LOWEST free descriptor, as Linux does
    (e.g. after close(1), the next open returns fd 1) — computed by
    `State.alloc_fd`.  The choice set is a singleton (no nondeterminism);
    the freeness conjunct only empties it in the unreachable case where
    `alloc_fd`'s scan bound (4096 fds) is exhausted, leaving just the
    errno alternative — as real kernels fail with -EMFILE at RLIMIT_NOFILE
    well before that.  `alloc_fd fds <= 4096` keeps an fd from ever being
    confused with an error-encoded return. -/
def lowest_fd (fds : List (word × FdEntry)) : SysSpec word :=
  choose (fun fd => fd_lookup fds fd = none ∧ fd = alloc_fd fds)

/- =========================================================================
   Descriptor duplication: dup (23) / dup3 (24)
   ========================================================================= -/

/-- WHAT DUPLICATION SHARES, AND WHAT THIS MODEL CAN NAME.

    `dup` and `dup3` install a second descriptor for the SAME OPEN FILE
    DESCRIPTION: `SYSCALL_DEFINE1(dup)` hands `fd_install` the very
    `struct file` pointer the old fd holds, and `do_dup2` stores that
    same pointer at `newfd` after a `get_file` (fs/file.c).  The file
    OFFSET `f_pos` and the status flags `f_flags` are fields of that
    `struct file` (include/linux/fs.h), so the two fds read and advance
    ONE offset; only the close-on-exec bit is per-descriptor, living in
    the descriptor table's `close_on_exec` bitmap rather than in the
    description (include/linux/fdtable.h, `struct fdtable`,
    byte-identical v5.4..v7.2).

    This model keeps the offset INSIDE the per-fd entry
    (`State.FdEntry`: `FdFile p offset`), so it cannot name one
    description from two fds.  Duplication is therefore modeled exactly
    for the entries that carry NO per-description state, and declines
    for the two that do:

    - `FdChannel ch` carries only the channel id.  A channel's read
      position is the model-wide `m_stdin` and its writes are trace
      events, so two fds naming one channel already share everything a
      description shares: copying the entry IS the sharing.
    - `FdDir` is nullary, and no modeled arm observes a directory
      position: `ReadWrite.lseek_spec` declines on `FdDir`, and
      `Readdir.getdents64_spec` declines every listing, answering only
      where the buffer has no room for an entry — which is the arm that
      moves no position.
    - `FdFile`/`FdFileW`/`FdFileRW` carry `offset`, which read, readv,
      write, writev and lseek rewrite in place.  Copying such an entry would
      give the two fds INDEPENDENT offsets, so
      `fd2 = dup(fd1); read(fd1, b, 4); read(fd2, b, 4)` would deliver
      bytes 0..3 twice where Linux delivers 0..3 and then 4..7 — a
      confident wrong answer rather than a gap.  Duplicating a FILE fd
      is `unmodeled`.  The fix is an open file description layer in
      `State.lean`, where an `FdEntry` names a description by id instead
      of carrying its mutable state.
    - `FdSocket` carries the connection's remaining receive script, and
      a read rewrites it in place — `ReadWrite.read_delivery_clamped`
      consumes the byte, and the -ECONNRESET and -ETIMEDOUT arms move
      the entry to `SkReset`.  Copying it is the `FdFile` mistake with
      a different payload: the two fds would each report the peer's
      reset once, where Linux reports it once for the connection.  So
      duplicating a SOCKET fd is `unmodeled` too, and the same open
      file description layer fixes both. -/
def dup_modeled_entry (e : FdEntry) : Bool :=
  match e with
  | FdEntry.FdChannel _ | FdEntry.FdDir => true
  | FdEntry.FdFile _ _ | FdEntry.FdFileW _ _ | FdEntry.FdSocket _ => false
  /- AN APPEND FD DECLINES WITH THEM, and this one is a CHOICE rather
     than the `FdFile` argument repeated.  A write through an
     `FdFileA` does not read `offset` at all -- it lands at
     `i_size_read(inode)` -- so copying the entry would NOT give the
     two fds independent write positions, and the `FdDir` argument
     ("every syscall that could observe the per-description state is
     already declined") would carry it if `ReadWrite.lseek_spec`
     declined this kind.  It does not: lseek repositions and REPORTS
     `f_pos` on an append fd exactly as on any other, so
     `fd2 = dup(fd1); lseek(fd1, 0, SEEK_SET); lseek(fd2, 0, SEEK_CUR)`
     answers 0 on Linux, where two copied entries would answer the old
     position.  That is the `FdFile` mistake with the read path removed,
     so this arm takes the `FdFile` answer, and it is the lseek arm and
     not the write arm that puts it there. -/
  | FdEntry.FdFileA _ _ => false
  /- AN O_RDWR FD IS THE `FdFile` ARGUMENT UNCHANGED, and it is the
     kind that argument fits best rather than an extension of it: the
     entry carries one `offset` that read, readv, write, writev and
     lseek all rewrite in place, so copying it would give the two fds
     independent positions in BOTH directions.
     `fd2 = dup(fd1); read(fd1, b, 4); write(fd2, b, 4)` writes at 4 on
     Linux, where two copied entries write at 0.  The open file
     description layer named above is what fixes it here too. -/
  | FdEntry.FdFileRW _ _ => false
  /- A PIPE END DECLINES, and it is NOT the `FdChannel` case even
     though `FdPipe` carries no offset either.  What a pipe end names
     is a `pipe_inode_info` with a reader and a writer COUNT, and
     `do_dup2`'s `get_file` adds a reference without touching either
     (fs/file.c, v6.18.46): after `dup` the pipe still has one writer,
     so closing ONE of the two write-end fds must NOT deliver EOF to
     the reader, where closing both must.  `FdChannel` has nothing of
     the kind to get wrong -- its position is the run's `m_stdin` and
     its writes are trace events, so copying the entry IS the sharing.
     Modeling a duplicated pipe end therefore needs an end COUNT, or
     the open file description layer the `FdFile` paragraph above
     already names; with neither, the number of live ends would have to
     be read off the fd table, and `dup` is exactly the operation that
     makes that reading wrong.
     So this fails closed rather than copying the entry. -/
  | FdEntry.FdPipe _ _ => false
  /- /dev/null IS THE `FdChannel` CASE WITH NOTHING TO SHARE AT ALL.
     `do_dup2`'s `get_file` (fs/file.c, v6.18.46) makes the new fd a
     second reference to the one `struct file`, so the two share its
     `f_pos` and `f_flags`; what makes copying the entry exact is that
     no modeled arm can observe either on this kind.  `f_pos` is pinned
     at 0 by `null_lseek` and never advanced by `read_null` or
     `write_null` (drivers/char/mem.c), so `ReadWrite.lseek_spec`
     answers 0 through either fd whatever the other did; `f_flags` is
     read by nothing, since `Fcntl.getfl_f_flags` and
     `Fcntl.setfl_noop_on` both decline this kind; and there is no
     count to keep in step, because a device node has no reader or
     writer count for a close to move.  The access mode the entry
     carries is per `struct file` too, and a copy carries the same
     one.  So copying IS the sharing, as for a channel. -/
  | FdEntry.FdDevNull _ _ => true
  /- /dev/urandom COPIES TOO, and the argument is /dev/null's with one
     more thing to check.  The two fds share the one `struct file`
     (`do_dup2`'s `get_file`); its `f_pos` is pinned at 0 on this kind
     (`noop_llseek`, fs/read_write.c, returns it and `urandom_read_iter`,
     drivers/char/random.c, never moves the `kiocb`'s `ki_pos`,
     include/linux/fs.h; all Linux v6.18.46), and
     `f_flags` is read by nothing modeled (`Fcntl.getfl_f_flags` and
     `Fcntl.setfl_noop_on` both decline the kind).  The one more thing
     is the BYTES: a read through either fd takes the front of the
     device's declared stream, `State.m_urandom`, which is the model's
     and not the entry's — so two references and two separate opens
     read the same stream in the same order, exactly as two `struct
     file`s on the random device draw from one generator.  Copying the
     entry loses nothing. -/
  | FdEntry.FdUrandom => true

/-- dup's injectable failures: fd-table exhaustion at RLIMIT_NOFILE
    (EMFILE, which also keeps the spec receptive when no free fd
    exists) and a descriptor table the kernel cannot grow (ENOMEM, from
    `alloc_fdtable`, fs/file.c — its shape changed at v6.13, from a bare
    NULL to an ERR_PTR, but the errno set `alloc_fd` can raise did not).
    ENFILE is NOT among them: dup allocates no `struct file` — it takes
    a second reference to an existing one — so the system-wide
    open-file limit cannot bite.  EBADF is not injectable either: fd
    validity IS tracked. -/
def dup_errnos : List Int := [ENOMEM, EMFILE]

/-- `dup oldfd`: a second descriptor for `oldfd`'s description, at the
    LOWEST free fd, returned.

    ORDER, from `SYSCALL_DEFINE1(dup, unsigned int, fildes)` (fs/file.c,
    byte-identical v5.9..v7.2): `fget_raw` runs FIRST, so a closed
    `oldfd` is -EBADF BEFORE any allocation — `dup` of a bad fd on a
    full table is -EBADF, never -EMFILE.  Only then does
    `get_unused_fd_flags(0)` take the lowest free slot (`lowest_fd`,
    i.e. `State.alloc_fd`), which is where the two injectable failures
    live.  `fget_raw` (not `fget`) means an O_PATH fd is dup-able too;
    the model has no O_PATH fds, so nothing turns on it.  The new
    descriptor's close-on-exec bit is cleared, `flags` being 0.

    `oldfd` arrives already truncated to 32 bits (see
    `Syscall.fd32`), so `dup(2^32)` duplicates stdin and `dup(-1)` is
    -EBADF. -/
def dup_spec (oldfd : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    match fd_lookup (m_fds m) oldfd with
    | none => err_ret EBADF
    | some e =>
        if !(dup_modeled_entry e) then unmodeled
        else
          alt (bind (errno_from dup_errnos) fun er => err_ret er)
            /- untracked env failure or no free fd -/
            (bind (lowest_fd (m_fds m)) fun fd =>
              seqSpec (modifySpec (with_fds (fd_insert (m_fds m) fd e)))
                (ret_only fd))

/-! ## `Z.ldiff` over `Int`

    Lean's core `Int` library has no bitwise and/or/and-not (see
    `Sys/Uapi.lean`, which ports `Z.lor`, `Z.land` and `Z.ldiff` through
    `Nat`), and `dup3_flags_ok` is the one place in this file that needs
    `Z.ldiff a b = a & ~b`.  The definition IS `Uapi.z_ldiff`, a
    transparent alias below, whose body is `a - (a & b)`.  The operands
    are non-negative there (`flag32 flags` is a 32-bit value and
    `O_CLOEXEC` is a literal), and on those `a & ~b` clears exactly the
    bits of `b` from `a`, i.e. `a - (a & b)` — which is why the two
    spellings agree on every call this file makes. -/

/--  `Z.ldiff` (bitwise "`a` and not `b`") — `Sys.Uapi.z_ldiff`, the
    canonical definition, as a transparent alias. -/
abbrev z_ldiff (a b : Int) : Int := LinuxSem.LinuxProcessSem.Sys.Uapi.z_ldiff a b

/-- `(flags & ~O_CLOEXEC) == 0` — `ksys_dup3`'s first test, on the
    TRUNCATED word.

    The truncation (`Syscall.flag32`) is applied HERE rather than at
    the dispatcher, where `fd32`/`whence32`/`cmd32` are applied, because
    here it is the only thing separating this model from a kernel that
    tested the full 64-bit argument: `SYSCALL_DEFINE3(dup3, unsigned int,
    unsigned int, int flags)` discards the high half, so dup3(2, 1, 2^32)
    returns 1 (fs/file.c, v6.18.46).  A caller reaching
    `dup3_spec` without the truncation would answer -EINVAL there. -/
def dup3_flags_ok (flags : word) : Bool :=
  z_ldiff ((flag32 flags).toNat : Int) O_CLOEXEC == 0

/-- `dup3 oldfd newfd flags`: install `oldfd`'s description at `newfd`,
    silently closing whatever `newfd` held, and return `newfd`.

    ORDER, from `ksys_dup3` (fs/file.c, byte-identical v5.11..v7.2),
    followed exactly:

    1. `(flags & ~O_CLOEXEC) != 0` is -EINVAL, before anything else.
    2. `oldfd == newfd` is -EINVAL — unconditionally, and BEFORE any
       validity test, which is where dup3 differs from dup2 (dup2
       returns `newfd` unchanged for an open fd, and musl's riscv64
       dup2 answers that case itself with an `fcntl(F_GETFD)` probe
       rather than issuing dup3).  The comparison is on the truncated
       fds, so `dup3(2^32, 0, 0)` is -EINVAL too.
    3. `newfd >= rlimit(RLIMIT_NOFILE)` is -EBADF.
    4. `expand_files` is CALLED next, but its result is not read yet.
    5. `oldfd` not open is -EBADF — tested BEFORE step 4's result, so a
       missing `oldfd` beats an `expand_files` failure.  Only then is
       that result read, and only its -EMFILE becomes -EBADF (`goto
       Ebadf`); its -ENOMEM is returned verbatim.

    STEP 3 IS ANSWERED FROM STATE, not argued around: `State.m_nofile`
    carries the soft RLIMIT_NOFILE the run was launched with (an input,
    like the launching uid — see `State.ProcInput`'s `in_nofile`), and
    this spec tests it where `ksys_dup3` does, before the `oldfd`
    lookup.  Both orders agree on the answer wherever both fire, since
    steps 3 and 5 are the same -EBADF; testing it in the kernel's place
    is what makes the case where they DISAGREE come out right, namely a
    process holding an fd at or above its own soft limit.  That is
    reachable — a parent lowers the limit and execs, and the fds already
    open stay open.

    The limit never moves during a run, which is what lets one field
    hold it and what makes this gate a test rather than a guess.  Why
    it cannot move is argued once, on `State.limst_nofile`; what it
    costs if that stops being true lands here.

    THAT ARGUMENT IS AN ABSENCE, so it is REGISTERED rather than only written down.
    It holds while `setrlimit` (164) has no dispatcher arm. And both proofs are in
    this tree at `Checks/ProcessCreation.lean`, so giving 164 an arm breaks them
    rather than silently invalidating this gate; the register this paragraph asks for
    EXISTS. `prlimit64` (261) is the writer that DOES have an arm, and no register
    can speak for it: it is closed by `Sys.prlimit64_spec` declining every resource
    but RLIMIT_CORE, so widening that arm is a change this file has to be re-read
    against.

    WHAT IS STILL DECLINED, AND WHY.  A free `newfd` at or above
    `Uapi.NR_OPEN_DEFAULT` and below the limit.  Linux answers it out of
    two facts this model does not carry — the descriptor table's current
    `max_fds` and the `sysctl_nr_open` ceiling — through `expand_files`,
    which returns -EMFILE for `newfd >= sysctl_nr_open` (rewritten to
    -EBADF by step 5's `goto Ebadf`) and -ENOMEM for a `kvmalloc` that
    fails.  Both are reachable for any such `newfd` — `sysctl_nr_open`
    can be lowered to `BITS_PER_LONG` while a soft limit set earlier
    stays high — so the model can neither answer success nor pick an
    errno, and declines.  Closing it needs `sysctl_nr_open` as a second
    run input and the table's `max_fds` as state; nothing else.

    ONE THING THIS FILE DOES NOT FIX.  The model's own fd allocator
    (`lowest_fd`, and every spec that calls it) hands out numbers
    without consulting the limit, so a modeled run can reach a state
    Linux would have refused with -EMFILE.  That is a divergence rather
    than a decline.

    A FREE `newfd` BELOW `Uapi.NR_OPEN_DEFAULT` IS ANSWERED, and
    deterministically.  That constant is a floor on the live table's
    `max_fds` (the argument is on `Uapi.NR_OPEN_DEFAULT`), so
    `expand_files` takes its `nr < fdt->max_fds` early return, allocates
    nothing, and neither of the two errnos above exists.  This is the
    ordinary redirection case — close a standard descriptor and dup3
    onto it — and it is deterministic for the same reason the
    already-open case is: `do_dup2`'s -EBUSY needs a descriptor reserved
    by another thread in a shared table, and the `filp_close` of the
    displaced description happens after the swap with its return value
    DISCARDED, so no error can come from the close.

    An already-open `newfd` needs no such bound: it is by construction
    below the table's `max_fds`, so `expand_files` returns 0 for it
    too.

    O_CLOEXEC is accepted and IGNORED, as `Open.openat_spec` accepts and
    ignores it: close-on-exec is observable only through execve (221)
    and fcntl (25).  execve is outside `Specs.modeled_sysnos`.  fcntl is
    IN it, but the bit's only reader there is `F_GETFD`, which
    `Fcntl.fcntl_spec` declines; the one fcntl command it does answer
    for the bit, `F_SETFD`, writes it and reports nothing.  So no
    modeled execution can tell the bit's value, and the decision to
    ignore O_CLOEXEC here stands or falls with `Fcntl.fcntl_spec`'s
    decision to decline `F_GETFD`.  The displaced entry is dropped
    exactly as `Open.close_spec` drops one. -/
def dup3_newfd_under_limit (newfd : word) (m : Model) : Bool :=
  decide ((newfd.toNat : Int) < ((m_nofile m).toNat : Int))

/-- `dup3` (24): the definition the argument above is about.  The five
    steps it lists are the five tests below, in that order. -/
def dup3_spec (oldfd newfd flags : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if !(dup3_flags_ok flags) then err_ret EINVAL
    else if bv_eqb oldfd newfd then err_ret EINVAL
    else if !(dup3_newfd_under_limit newfd m) then err_ret EBADF
    else
      match fd_lookup (m_fds m) oldfd with
      | none => err_ret EBADF
      | some e =>
          if !(dup_modeled_entry e) then unmodeled
          else
            match fd_lookup (m_fds m) newfd with
            | none =>
                /- free: answered only below the embedded table's floor -/
                if decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) then
                  seqSpec (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                    (ret_only newfd)
                else unmodeled
            | some _ =>
                seqSpec (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                  (ret_only newfd)

/-! The two returns above are `newfd` ZERO-extended, where `do_dup2`
    returns an `int` that sign-extends at or above 2^31.  Neither arm
    can reach that: the already-open one is bounded by `State.alloc_fd`'s
    4096, and the free one by the explicit `NR_OPEN_DEFAULT` test.  Note
    which fact is load-bearing — it is the two ARMS' own bounds and not
    the limit test, even though `Run.valid_nofile` does bound the limit
    to 2^31 - 64: that predicate constrains the equivalence theorem's
    inputs, while the extracted checker is handed a model directly and
    never sees it, so a caller may still reach this spec with any
    `unsigned long` in `State.m_nofile`. -/

/-! ## Sanity checks

  It is the seven definitions above and their prose. The checks below are PORT
  CHECKS, and they pin the answers that prose argues for against a concrete model:
  `dup` hands out the lowest free fd, `dup3` answers in the kernel's order, and the
  decline arms decline.

    A 4096-FD EXHAUSTION FIXTURE IS NOT EVALUATED.  `alloc_fd`'s scan
    runs 4096 lookups over a 4096-entry table, so a `by decide` on such a
    table costs millions of kernel reduction steps on every build of
    this file; the freeness conjunct is therefore pinned by
    `lowest_fd_occupied` below, which states the general fact that the
    docstring on `lowest_fd` relies on: when the allocator's candidate is
    already taken, the choice set is EMPTY, leaving only the errno arm —
    and `dup_spec_errno` pins that arm's -EMFILE.  `alloc_fd` itself is
    checked on the small fixture (`alloc_fd demoFds = 6`).

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so lookups are stated as equations between
    `Option FdEntry` and proved by `simp` on the tables' keys rather than
    by `decide`; the `Bool`-valued helpers (`dup_modeled_entry`,
    `dup3_flags_ok`, `dup3_newfd_under_limit`, `z_ldiff`) are `by decide`.

    The intro lemmas (`dup_spec_success`, `dup_spec_errno`,
    `dup3_spec_success_open`, `dup3_spec_success_free`) exist because the
    success arms run a `choose`, which needs a witness; the deterministic
    arms are proved directly by naming each `if` in the kernel's order,
    which is also what makes the ORDER checks below readable. -/

/-- The lowest-free-fd choice set, spelled out: its only outcome is the
    allocator's answer, and only when that answer is free. -/
theorem lowest_fd_ok (fds : List (word × FdEntry)) (fd : word)
    (i : SyscallInput) (m : Model) :
    lowest_fd fds i m (.ok fd m []) ↔
      fd_lookup fds fd = none ∧ fd = alloc_fd fds := by
  simp only [lowest_fd, choose]
  constructor
  · rintro ⟨x, ⟨hfree, rfl⟩, ho⟩
    simp only [Outcome.ok.injEq] at ho
    rw [← ho.1] at hfree
    exact ⟨hfree, ho.1⟩
  · rintro ⟨hfree, rfl⟩
    refine Exists.intro (alloc_fd fds) ?_
    exact ⟨⟨hfree, rfl⟩, rfl⟩

/-- FD EXHAUSTION.  When the allocator's candidate is already taken —
    the case `lowest_fd`'s docstring calls unreachable, the 4096-fd scan
    bound being exhausted — the freeness conjunct empties the choice set.
    `dup`'s success arm is then empty, so only its errno arm remains,
    -EMFILE among it. -/
theorem lowest_fd_occupied (fds : List (word × FdEntry))
    (i : SyscallInput) (m : Model) (o : Outcome word Model event)
    (h : fd_lookup fds (alloc_fd fds) ≠ none) :
    ¬ lowest_fd fds i m o := by
  intro ho
  simp only [lowest_fd, choose] at ho
  rcases ho with ⟨x, ⟨hfree, rfl⟩, -⟩
  exact h hfree

/-- THE SUCCESS ARM OF `dup`: with `oldfd` open and its entry modeled, a
    free `fd` that is the allocator's answer is handed back, and the
    entry is installed there. -/
theorem dup_spec_success (m : Model) (oldfd fd : word) (e : FdEntry)
    (i : SyscallInput)
    (hlook : fd_lookup (m_fds m) oldfd = some e)
    (hm : dup_modeled_entry e = true)
    (hfree : fd_lookup (m_fds m) fd = none)
    (halloc : fd = alloc_fd (m_fds m)) :
    dup_spec oldfd i m
      (.ok (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd e) m) []) := by
  simp only [dup_spec, getModelSpec, bind_getModel, hlook, hm, Bool.not_true,
    Bool.false_eq_true, ite_false]
  refine Or.inr ?_
  refine bind_ok (lowest_fd (m_fds m))
    (fun fd' => seqSpec (modifySpec (with_fds (fd_insert (m_fds m) fd' e)))
      (ret_only fd'))
    i m fd m [] (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd e) m) [] ?_ ?_
  · exact ⟨fd, ⟨hfree, halloc⟩, rfl⟩
  · exact bind_ok (modifySpec (with_fds (fd_insert (m_fds m) fd e)))
      (fun _ => ret_only fd) i m () (with_fds (fd_insert (m_fds m) fd e) m) []
      (mkEffect fd [] []) (with_fds (fd_insert (m_fds m) fd e) m) [] rfl rfl

/-- THE ERRNO ARM OF `dup`: an injectable failure may be reported at any
    time the fd is valid, leaving the model untouched.  -EMFILE here is
    the arm fd exhaustion collapses `dup` onto. -/
theorem dup_spec_errno (m : Model) (oldfd : word) (e : FdEntry) (er : Int)
    (i : SyscallInput) (her : er ∈ dup_errnos)
    (hlook : fd_lookup (m_fds m) oldfd = some e)
    (hm : dup_modeled_entry e = true) :
    dup_spec oldfd i m (.ok (mkEffect (errno_ret er) [] []) m []) := by
  simp only [dup_spec, getModelSpec, bind_getModel, hlook, hm, Bool.not_true,
    Bool.false_eq_true, ite_false]
  refine Or.inl ?_
  exact bind_ok (errno_from dup_errnos) (fun er' => err_ret er') i m er m []
    (mkEffect (errno_ret er) [] []) m [] ⟨er, her, rfl⟩ rfl

/-- THE SUCCESS ARM OF `dup3` ON AN OPEN `newfd`: the displaced entry is
    dropped and `oldfd`'s entry installed in its place. -/
theorem dup3_spec_success_open (m : Model) (oldfd newfd : word)
    (e e' : FdEntry) (flags : word) (i : SyscallInput)
    (hflags : dup3_flags_ok flags = true)
    (hne : bv_eqb oldfd newfd = false)
    (hlim : dup3_newfd_under_limit newfd m = true)
    (hlook : fd_lookup (m_fds m) oldfd = some e)
    (hm : dup_modeled_entry e = true)
    (hnew : fd_lookup (m_fds m) newfd = some e') :
    dup3_spec oldfd newfd flags i m
      (.ok (mkEffect newfd [] []) (with_fds (fd_insert (m_fds m) newfd e) m) []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel, hflags, hne, hlim,
    Bool.not_true, Bool.false_eq_true, ite_false, hlook, hm, hnew]
  exact bind_ok (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
    (fun _ => ret_only newfd) i m () (with_fds (fd_insert (m_fds m) newfd e) m) []
    (mkEffect newfd [] []) (with_fds (fd_insert (m_fds m) newfd e) m) [] rfl rfl

/-- THE SUCCESS ARM OF `dup3` ON A FREE `newfd` BELOW
    `Uapi.NR_OPEN_DEFAULT`: `expand_files` cannot fail there, so the
    answer is deterministic. -/
theorem dup3_spec_success_free (m : Model) (oldfd newfd : word)
    (e : FdEntry) (flags : word) (i : SyscallInput)
    (hflags : dup3_flags_ok flags = true)
    (hne : bv_eqb oldfd newfd = false)
    (hlim : dup3_newfd_under_limit newfd m = true)
    (hlook : fd_lookup (m_fds m) oldfd = some e)
    (hm : dup_modeled_entry e = true)
    (hnew : fd_lookup (m_fds m) newfd = none)
    (hfloor : (newfd.toNat : Int) < NR_OPEN_DEFAULT) :
    dup3_spec oldfd newfd flags i m
      (.ok (mkEffect newfd [] []) (with_fds (fd_insert (m_fds m) newfd e) m) []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel, hflags, hne, hlim,
    Bool.not_true, Bool.false_eq_true, ite_false, hlook, hm, hnew, hfloor]
  exact bind_ok (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
    (fun _ => ret_only newfd) i m () (with_fds (fd_insert (m_fds m) newfd e) m) []
    (mkEffect newfd [] []) (with_fds (fd_insert (m_fds m) newfd e) m) [] rfl rfl

/-- A tiny fd table for the checks: 0 stdin (a channel), 1 stdout (a
    channel), 2 a regular file, 3 a pipe write end, 4 a directory,
    5 `/dev/null`.  Descriptors 6 and up are free. -/
private def demoFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdChannel 8),
   (2, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
   (3, FdEntry.FdPipe 1 true), (4, FdEntry.FdDir),
   (5, FdEntry.FdDevNull true false)]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and the default
    RLIMIT_NOFILE (1024). -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- The same table with fd 1 closed — the header's own example: after
    `close(1)` the next descriptor handed out is 1 again. -/
private def demoHoleFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (2, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
   (3, FdEntry.FdPipe 1 true), (4, FdEntry.FdDir),
   (5, FdEntry.FdDevNull true false)]

private def demoHoleModel : Model :=
  mkModel demoHoleFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A syscall input for `dup`/`dup3`.  Neither spec reads it; it is here
    because a `SysSpec` is a relation on an input as well as a model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 24, in_args := [1], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-! ### The computable parts -/

/-- The allocator hands out the first free descriptor — 6 here. -/
example : alloc_fd demoFds = 6 := by decide

/-- …and after `close(1)` it hands out 1 again, not 6. -/
example : alloc_fd demoHoleFds = 1 := by decide

/-- The two injectable errnos are ENOMEM and EMFILE, ENFILE is not
    among them. -/
example : dup_errnos = [12, 24] := by decide

/-- Which kinds of entry duplication may copy.  The four modeled kinds
    answer `true`; the four carrying per-description state answer
    `false`. -/
example : dup_modeled_entry (FdEntry.FdChannel 7) = true := by decide
example : dup_modeled_entry FdEntry.FdDir = true := by decide
example : dup_modeled_entry (FdEntry.FdDevNull true false) = true := by decide
example : dup_modeled_entry FdEntry.FdUrandom = true := by decide
example : dup_modeled_entry (FdEntry.FdFile [] 0) = false := by decide
example : dup_modeled_entry (FdEntry.FdFileW [] 0) = false := by decide
example : dup_modeled_entry (FdEntry.FdFileA [] 0) = false := by decide
example : dup_modeled_entry (FdEntry.FdFileRW [] 0) = false := by decide
example : dup_modeled_entry (FdEntry.FdPipe 1 true) = false := by decide
example : dup_modeled_entry (FdEntry.FdSocket SockState.SkFresh) = false := by
  decide

/-- `Z.ldiff` clears the bits of its second argument — and therefore
    that `O_CLOEXEC` alone is invisible to `dup3`'s flag test while a
    second bit is not. -/
example : z_ldiff 5 3 = 4 := by decide
example : z_ldiff 0 5 = 0 := by decide
example : z_ldiff O_CLOEXEC O_CLOEXEC = 0 := by decide
example : z_ldiff (O_CLOEXEC + 1) O_CLOEXEC = 1 := by decide

/-- The flag test: 0 and O_CLOEXEC pass, any other bit fails. -/
example : dup3_flags_ok 0 = true := by decide
example : dup3_flags_ok O_CLOEXEC = true := by decide
example : dup3_flags_ok 1 = false := by decide
example : dup3_flags_ok (O_CLOEXEC + 1) = false := by decide

/-- THE TRUNCATION IS LOAD-BEARING: 2^32 has the low half 0, so it is
    the same flag word as 0 and passes; 2^32 + 1 has the low half 1 and
    fails.  A full-width test would have answered -EINVAL to both. -/
example : dup3_flags_ok (BitVec.ofInt 64 4294967296) = true := by decide
example : dup3_flags_ok (BitVec.ofInt 64 4294967297) = false := by decide

/-- The RLIMIT_NOFILE gate, read unsigned against the model's limit
    (1024 by default): 1023 is under it, 1024 is not. -/
example : dup3_newfd_under_limit 1023 demoModel = true := by decide
example : dup3_newfd_under_limit 1024 demoModel = false := by decide
example : dup3_newfd_under_limit 2000 demoModel = false := by decide

/-! ### `dup` on the fixture -/

/-- DUP ALLOCATES THE LOWEST FREE FD: 0..5 are taken, so `dup 0` answers
    fd 6, and the entry it installs there is the one fd 0 names (the
    same channel — copying IS the sharing for a channel). -/
example :
    dup_spec 0 demoInput demoModel
      (.ok (mkEffect 6 [] [])
        (with_fds (fd_insert demoFds 6 (FdEntry.FdChannel 7)) demoModel) []) :=
  dup_spec_success demoModel 0 6 (FdEntry.FdChannel 7) demoInput
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])
    (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])
    (by decide)

/-- …and it is the LOWEST one, not the next in some other order: with
    fd 1 closed, `dup 0` gets 1 — the header's close(1) example. -/
example :
    dup_spec 0 demoInput demoHoleModel
      (.ok (mkEffect 1 [] [])
        (with_fds (fd_insert demoHoleFds 1 (FdEntry.FdChannel 7)) demoHoleModel) []) :=
  dup_spec_success demoHoleModel 0 1 (FdEntry.FdChannel 7) demoInput
    (by simp [m_fds, demoHoleModel, mkModel, demoHoleFds, fd_lookup])
    (by decide)
    (by simp [m_fds, demoHoleModel, mkModel, demoHoleFds, fd_lookup])
    (by decide)

/-- A /dev/null descriptor is copyable for the reason the docstring
    gives: nothing modeled observes the shared `struct file`. -/
example :
    dup_spec 5 demoInput demoModel
      (.ok (mkEffect 6 [] [])
        (with_fds (fd_insert demoFds 6 (FdEntry.FdDevNull true false)) demoModel) []) :=
  dup_spec_success demoModel 5 6 (FdEntry.FdDevNull true false) demoInput
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])
    (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])
    (by decide)

/-- A MISSING FD IS -EBADF, and it is the fd lookup that decides: no
    allocation is attempted, so a bad fd on a full table is -EBADF and
    never -EMFILE. -/
example :
    dup_spec 9 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup_spec, getModelSpec, bind_getModel, hlook, err_ret, ret_only,
    pure]

/-- A FILE FD IS `unmodeled`: copying the entry would give two
    independent offsets — a confident wrong answer, not a gap. -/
example : dup_spec 2 demoInput demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 2 =
      some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup_spec, getModelSpec, bind_getModel, hlook]
  rw [ite_eq_left (by decide :
    ((!(dup_modeled_entry
      (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0))) = true))]
  simp only [unmodeled]

/-- …and so is a PIPE END, for the end-count reason in the docstring —
    closing one of two duplicated write ends must not deliver EOF. -/
example : dup_spec 3 demoInput demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3 = some (FdEntry.FdPipe 1 true) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup_spec, getModelSpec, bind_getModel, hlook]
  rw [ite_eq_left (by decide : ((!(dup_modeled_entry (FdEntry.FdPipe 1 true))) = true))]
  simp only [unmodeled]

/-- FD EXHAUSTION ANSWERS -EMFILE: it is the injectable arm `dup` falls
    back on when `alloc_fd` finds no free fd (`lowest_fd_occupied` is why
    the success arm is then empty), and it leaves the model alone. -/
example :
    dup_spec 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EMFILE) [] []) demoModel []) :=
  dup_spec_errno demoModel 0 (FdEntry.FdChannel 7) EMFILE demoInput (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]) (by decide)

/-! ### `dup3` on the fixture -/

/-- DUP3 REJECTS EQUAL FDS WITH -EINVAL — and it does so BEFORE any
    validity test: fd 9 is closed, and `dup3 9 9 0` is still -EINVAL
    rather than -EBADF. -/
example :
    dup3_spec 9 9 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_right (by decide : ¬ ((!(dup3_flags_ok (0 : word))) = true))]
  rw [ite_eq_left (by decide : bv_eqb (9 : word) 9 = true)]
  simp only [err_ret, ret_only, pure]

/-- A flag bit other than O_CLOEXEC is -EINVAL, before the fd tests. -/
example :
    dup3_spec 1 5 1 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_left (by decide : ((!(dup3_flags_ok (1 : word))) = true))]
  simp only [err_ret, ret_only, pure]

/-- THE FLAG TEST PRECEDES THE LIMIT TEST: `dup3 1 2000 (O_CLOEXEC+1)`
    is -EINVAL, not the -EBADF that newfd 2000 would otherwise draw. -/
example :
    dup3_spec 1 2000 (O_CLOEXEC + 1) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_left (by decide : ((!(dup3_flags_ok (O_CLOEXEC + 1 : word))) = true))]
  simp only [err_ret, ret_only, pure]

/-- `newfd` AT OR ABOVE RLIMIT_NOFILE IS -EBADF (the default limit is
    1024). -/
example :
    dup3_spec 1 2000 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_right (by decide : ¬ ((!(dup3_flags_ok (0 : word))) = true))]
  rw [ite_eq_right (by decide : ¬ (bv_eqb (1 : word) 2000 = true))]
  rw [ite_eq_left (by decide :
    ((!(dup3_newfd_under_limit (2000 : word) demoModel)) = true))]
  simp only [err_ret, ret_only, pure]

/-- A MISSING OLD FD IS -EBADF, tested after the limit gate and before
    `expand_files`' result. -/
example :
    dup3_spec 9 5 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_right (by decide : ¬ ((!(dup3_flags_ok (0 : word))) = true))]
  rw [ite_eq_right (by decide : ¬ (bv_eqb (9 : word) 5 = true))]
  rw [ite_eq_right (by decide :
    ¬ ((!(dup3_newfd_under_limit (5 : word) demoModel)) = true))]
  simp only [hlook, err_ret, ret_only, pure]

/-- A FILE OLD FD DECLINES the same way `dup`'s does. -/
example : dup3_spec 2 5 0 demoInput demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 2 =
      some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_right (by decide : ¬ ((!(dup3_flags_ok (0 : word))) = true))]
  rw [ite_eq_right (by decide : ¬ (bv_eqb (2 : word) 5 = true))]
  rw [ite_eq_right (by decide :
    ¬ ((!(dup3_newfd_under_limit (5 : word) demoModel)) = true))]
  simp only [hlook]
  rw [ite_eq_left (by decide :
    ((!(dup_modeled_entry
      (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0))) = true))]
  simp only [unmodeled]

/-- A FREE NEWFD AT OR ABOVE `NR_OPEN_DEFAULT` IS DECLINED, not answered:
    `expand_files` would have to consult `max_fds` and `sysctl_nr_open`,
    neither of which the model carries. -/
example : dup3_spec 1 70 0 demoInput demoModel .unmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some (FdEntry.FdChannel 8) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  have hnew : fd_lookup (m_fds demoModel) 70 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_right (by decide : ¬ ((!(dup3_flags_ok (0 : word))) = true))]
  rw [ite_eq_right (by decide : ¬ (bv_eqb (1 : word) 70 = true))]
  rw [ite_eq_right (by decide :
    ¬ ((!(dup3_newfd_under_limit (70 : word) demoModel)) = true))]
  simp only [hlook]
  rw [ite_eq_right (by decide :
    ¬ ((!(dup_modeled_entry (FdEntry.FdChannel 8))) = true))]
  simp only [hnew]
  rw [ite_eq_right (by decide :
    ¬ (decide (((70 : word).toNat : Int) < NR_OPEN_DEFAULT) = true))]
  simp only [unmodeled]

/-- A FREE NEWFD BELOW `NR_OPEN_DEFAULT` IS ANSWERED: the ordinary
    redirection case, close a standard descriptor and dup3 onto it. -/
example :
    dup3_spec 4 6 0 demoInput demoModel
      (.ok (mkEffect 6 [] [])
        (with_fds (fd_insert demoFds 6 FdEntry.FdDir) demoModel) []) :=
  dup3_spec_success_free demoModel 4 6 FdEntry.FdDir 0 demoInput
    (by decide) (by decide) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]) (by decide)

/-- AN OPEN NEWFD IS OVERWRITTEN, silently closing what it held (here fd
    1's channel 8 is displaced by fd 0's channel 7).  O_CLOEXEC is
    accepted and ignored. -/
example :
    dup3_spec 0 1 O_CLOEXEC demoInput demoModel
      (.ok (mkEffect 1 [] [])
        (with_fds (fd_insert demoFds 1 (FdEntry.FdChannel 7)) demoModel) []) :=
  dup3_spec_success_open demoModel 0 1 (FdEntry.FdChannel 7) (FdEntry.FdChannel 8)
    O_CLOEXEC demoInput (by decide) (by decide) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])

/-- THE FLAGS ARE TRUNCATED TO 32 BITS: `dup3(1, 5, 2^32)` is the same
    call as `dup3(1, 5, 0)` and succeeds. -/
example :
    dup3_spec 1 5 (BitVec.ofInt 64 4294967296) demoInput demoModel
      (.ok (mkEffect 5 [] [])
        (with_fds (fd_insert demoFds 5 (FdEntry.FdChannel 8)) demoModel) []) :=
  dup3_spec_success_open demoModel 1 5 (FdEntry.FdChannel 8)
    (FdEntry.FdDevNull true false) (BitVec.ofInt 64 4294967296) demoInput
    (by decide) (by decide) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]) (by decide)
    (by simp [m_fds, demoModel, mkModel, demoFds, fd_lookup])

/-- …while `dup3(1, 5, 2^32 + 1)` really carries a stray bit and is
    -EINVAL, which is what a full-width test would have gotten wrong. -/
example :
    dup3_spec 1 5 (BitVec.ofInt 64 4294967297) demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp only [dup3_spec, getModelSpec, bind_getModel]
  rw [ite_eq_left (by decide :
    ((!(dup3_flags_ok (BitVec.ofInt 64 4294967297))) = true))]
  simp only [err_ret, ret_only, pure]


/-- THE -EMFILE ALTERNATIVE, stated rather than evaluated: when the
    allocator's answer is already taken — the 4096-candidate scan
    exhausted — `lowest_fd` has no success outcome at all, so the only
    answer left is the errno arm's, and `get_unused_fd_flags` carries
    -EMFILE as its only one.  This is `File.lowest_fd_occupied`, cited
    rather than reproved; the EventFd arm declines the whole path, so the
    errno must not appear here. -/
theorem lowest_fd_at_limit (fds : List (word × FdEntry)) (i : SyscallInput)
    (m : Model) (o : Outcome word Model event)
    (h : fd_lookup fds (alloc_fd fds) ≠ none) : ¬ lowest_fd fds i m o :=
  lowest_fd_occupied fds i m o h

end LinuxSem.LinuxProcessSem.Sys.Fs.File
