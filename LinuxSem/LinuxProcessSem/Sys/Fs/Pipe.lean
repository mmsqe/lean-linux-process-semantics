/-
  * LinuxProcessSem.Sys.Fs.Pipe — pipe2 (59)

  Answers to Linux `fs/pipe.c`: this file holds the specs for the
  syscalls defined there, and no others.

  The pipe STATE — `State.PipeBuf`, `State.pipe_write_room`,
  `State.pipe_append`, `State.pipe_consume`, `State.pipe_end_live` —
  lives in `State.lean` beside the rest of the model, because the fd-kind
  arms that read it are spread across `Fs/ReadWrite.lean` (read, write,
  readv, writev, lseek), `Fs/Open.lean` (close, ftruncate),
  `Fs/Sync.lean` (fsync) and `Fs/Ioctl.lean` (ioctl).  What is here is the
  one syscall that CREATES a pipe.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  here that is `SysSpec SyscallEffect` from `MonadInstances`. The `sys_scope`
  sequencing `x <- c;; k` is `bind c (fun x => k)` in Lean. `ret_only` and `err_ret`
  are `Sys/Syscall.lean`'s.

  Require Export Syscall Uapi Uaccess Fs.File`; the definition lives in
  `Sys/Fs/File.lean:29`, which has not been ported yet, so this file carries a staging
  copy of it, documented at the definition. When `Sys/Fs/File.lean` lands, delete the
  copy here and use it instead — it is the same `choose`, and `openat`/`dup` will
  want it too.

  `Monad.lean:316-317`
  defines `set_fds fds := modify (with_fds fds)` and the same for
  `set_pipes`.  `Monad.lean` is parameterized and does not carry them, so
  the two steps below are spelled `modifySpec (with_fds ...)` /
  `modifySpec (with_pipes ...)` — the same `modify`, with the same
  `with_fds`/`with_pipes` from `StateLedger`.

  `Z.ldiff` has no `Int` counterpart in
  Lean core (there is no `Int.land` either), so `Sys/Uapi.lean` ports it
  beside `z_lor`/`z_land`, and the `z_ldiff` below is a transparent alias
  to that canonical definition rather than a second copy of it.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Pipe

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

/-- The flag bits `__do_pipe_flags` accepts: its opening
    `if (flags & ~(O_CLOEXEC | O_NONBLOCK | O_DIRECT | O_NOTIFICATION_PIPE))`
    (fs/pipe.c:987-988, v6.18.46).  Everything else is a deterministic
    -EINVAL, raised BEFORE the pipe is made and before the user pointer is
    touched.  `O_NOTIFICATION_PIPE` is spelled `O_EXCL`
    (include/uapi/linux/watch_queue.h:9, v6.18.46). -/
def pipe2_flags_mask : Int :=
  (O_CLOEXEC + O_NONBLOCK + O_DIRECT + O_EXCL)

/-- pipe2's injectable failures: environment conditions the model does
    not track.  `-EMFILE` at RLIMIT_NOFILE (and pipe2 needs TWO free
    descriptors, so it can hit it where an `openat` would not),
    `-ENFILE` at the system file limit — which is also where a failed
    `alloc_pipe_info` surfaces, since `get_pipe_inode` returns NULL for
    both (fs/pipe.c:886-898, v6.18.46) and `create_pipe_files` turns that
    one NULL into `-ENFILE` (:932-933) — and `-ENOMEM` out of growing the
    fd table.  Like
    `Open.openat_errnos`, this alternative also keeps the spec receptive
    when no free fd exists. -/
def pipe2_errnos : List Int := [EMFILE, ENFILE, ENOMEM]

/-! ## Port helpers

  Both are documented where they are defined. -/

/--  `Z.ldiff` — the bitwise difference `a land lnot b` — is
    `Uapi.z_ldiff`, the canonical definition, as a transparent alias:
    Lean core has no `Int` bitwise operations, which is why the body is
    spelled through `Nat`.

    The body there is `a - (a &&& b)`, which agrees with
    `a land lnot b` on the inputs this file has — `a` is a `bv 64` read
    unsigned (`flags.toNat`), and `b` is `pipe2_flags_mask`, 0x84880 —
    because a value below `2^64` occupies no bit above 63, so exactly the
    bits of `b` are cleared from `a`.  On those bounded operands the
    `Nat`-mask form this file used to spell (`a &&& (2^64 - 1 - b)`) and
    `a - (a &&& b)` are the same value.  Truncating either argument would
    be visible; both are bounded. -/
abbrev z_ldiff (a b : Int) : Int := LinuxSem.LinuxProcessSem.Sys.Uapi.z_ldiff a b

/-- The kernel returns the LOWEST free descriptor, as Linux does
    (e.g. after close(1), the next open returns fd 1) — computed by
    `State.alloc_fd`.  The choice set is a singleton (no nondeterminism);
    the freeness conjunct only empties it in the unreachable case where
    `alloc_fd`'s scan bound (4096 fds) is exhausted, leaving just the
    errno alternative — as real kernels fail with -EMFILE at
    RLIMIT_NOFILE well before that.  `alloc_fd fds <= 4096` keeps an fd
    from ever being confused with an error-encoded return.

  This is `Fs.File.lowest_fd` verbatim; -/
def lowest_fd (fds : List (word × FdEntry)) : SysSpec word :=
  choose (fun fd => fd_lookup fds fd = none ∧ fd = alloc_fd fds)

/-- `pipe2 fildes flags`: make a pipe and write its two descriptors —
    read end first — through `fildes`.  THE MODEL'S FIRST FD WHOSE
    CONTENTS COME FROM THE PROGRAM: everything else an fd names is
    supplied by the environment (a channel) or by the file system.

    Kernel source for everything below is fs/pipe.c at v6.18.46 (commit
    1f99e9ab748f): `SYSCALL_DEFINE2(pipe2)` at:1054, `do_pipe2` at:1032, `__do_pipe_flags` at:982, `create_pipe_files` at:926,
    `pipe_release` at:725, and the transfer pair `anon_pipe_read` at:269 and `anon_pipe_write` at:431.

    THE PAIR IS NAMED `anon_pipe_*` BECAUSE THAT IS WHAT EXISTS HERE, and
    the older names are a trap rather than a synonym: at v6.18.46
    `pipe_read` and `pipe_write` survive only inside three comments
    (:76, :1068, :1071), and the functions were split in two — an
    anonymous pair, `pipe_read`/`pipe_write`'s successors, and a FIFO
    pair `fifo_pipe_read` at :407 / `fifo_pipe_write` at :604 that wraps
    them with a timestamp update.  Which pair a descriptor gets is
    decided by its file-operations table: `pipefifo_fops` (:1246-1255)
    takes the FIFO pair, `pipeanon_fops` (:1257-1266) the anonymous one.
    `create_pipe_files` installs `pipeanon_fops` on both ends (:946,:957), so every claim in this file and in the pipe arms it points at
    is about `anon_pipe_read`/`anon_pipe_write`, never the FIFO wrappers.

    ORDER, as `do_pipe2` has it:

    - FLAGS FIRST (:987-988), before anything else and before the user
      pointer is read: a bit outside `pipe2_flags_mask` is `-EINVAL`, so
      `pipe2(unmapped, 1)` is `-EINVAL` and never `-EFAULT`.  Of the four
      accepted bits the model interprets only their ABSENCE: `flags = 0`
      is the whole modeled surface (it is what a `pipe(2)` call becomes
      on riscv64, which has no `pipe` syscall — musl's src/unistd/pipe.c
      issues `pipe2(fd, 0)`), and any nonzero accepted combination is
      `unmodeled`.  Each of the four would need something the model does
      not have: `O_CLOEXEC` an execve, `O_NONBLOCK` the `-EAGAIN`
      answers this spec's whole design declines, `O_DIRECT` packet mode
      (where a read DISCARDS the tail of a packet it did not take), and
      `O_NOTIFICATION_PIPE` a kernel built with CONFIG_WATCH_QUEUE —
      `create_pipe_files` calls `watch_queue_init` for that bit (:935-942)
      and the stub the option compiles out to returns `-ENOPKG`
      (include/linux/watch_queue.h:126-128, v6.18.46), so even the failure
      is configuration-dependent.
    - THEN THE DESCRIPTORS (:994-1006).  `__do_pipe_flags` takes the read
      end first and the write end second, each the lowest free number
      (`get_unused_fd_flags` -> `alloc_fd`, scanning `open_fds` from 0),
      so `fd[0] < fd[1]` and the write end is allocated with the read end
      already reserved.
    - THEN THE COPY-OUT (:1040), and only then `fd_install` (:1047-1048).
      The eight bytes go out as ONE `copy_to_user` of `int fildes[2]`, so
      the effect is one contiguous range, not two.  A failed copy is
      `-EFAULT` with NOTHING installed: `do_pipe2` `fput`s both files and
      `put_unused_fd`s both reservations (:1041-1045), so the call is
      atomic — the fd table is exactly as it was.  The model therefore
      answers `-EFAULT` and changes nothing.
      A PARTIALLY writable destination is `unmodeled` instead: the kernel
      copies a prefix before it faults, and how much depends on the
      architecture's uaccess loop, so the model will not say what is in
      those bytes.
    - ONE INVERSION OF THAT ORDER, named rather than assumed away.  The
      term tests the destination's writability BEFORE it allocates, so on
      the wholly-unwritable branch it offers `-EFAULT` beside the
      injected `pipe2_errnos`.  Linux runs `__do_pipe_flags` first, so a
      task with fewer than two free descriptors answers `-EMFILE` and
      never attempts the copy — the model admits an answer that kernel
      would not give in that one state.  It is over-permissive, not
      unsound: `-EMFILE` is admitted there too, so no real trace is
      refused.  Reaching it needs RLIMIT_NOFILE exhausted AND an
      unwritable `fildes` in the same call, so it is recorded
      the way `openat` records the `-EMFILE` a real kernel can raise
      before path resolution rather than being restructured around.

    WHAT A PIPE COSTS THE THEOREM.  Nothing observable: pipe bytes are
    not events, and `State.event` gains no constructor, so two runs that
    differ only in what a pipe holds are equivalent exactly as before.
    What changes is coverage — programs that create and use a pipe move
    from `unmodeled` to modeled, and the parts that stay `unmodeled` are
    named where they arise: a read of an empty pipe with a live writer
    and a write to a pipe with no reader (both would block or signal), a
    write needing a second ring slot (see `State.pipe_write_room`), a
    faulting source or a partially writable destination, and every
    vectored pipe transfer.  A source binary that reaches any of those
    fails `Equivalence.modeled`, so the task is REJECTED rather than
    vacuously satisfied.

    WHY A PIPE IS THE FIRST FD KIND TO COST ANYTHING HERE.  Every fd kind
    before it either always has an answer (a channel, a file) or never
    transfers (a directory).  A pipe is the first whose answer can depend
    on what the OTHER end does next, and that is the whole of the gap
    above: each declined arm is a place where the model would have to
    know something about a peer it does not represent.

    WHAT WOULD CLOSE IT: a model of blocking, which means a notion of a
    call that has no answer until the other end acts, and of the process
    death a SIGPIPE is; or at minimum a model of `O_NONBLOCK`, whose
    `-EAGAIN` answers are a function of the pipe state alone, plus a way
    for a program to ASK for them.  There are two such ways and neither
    is available today: `pipe2`'s own `O_NONBLOCK` is inside the accepted
    mask but any nonzero flag word is `unmodeled` (above), and `fcntl`
    answers `F_SETFL` only where it provably changes nothing — the
    `F_SETFL` that would actually set `O_NONBLOCK` declines, and the
    `F_GETFL` that `setnonblocking` issues first declines ahead of it
    (see `Fs.Fcntl.fcntl_spec` and `Fs.Fcntl.setfl_noop_on`).

    That is a measured gap on a real target's common path, not a
    hypothetical.  dropbear 2026.94 sets its pipes non-blocking as a
    matter of course, through one helper: `setnonblocking`
    (src/dbutil.c), called on the parent-side ends of the three pipes
    `spawn_command` (src/dbutil.c) creates, and on BOTH ends of the
    signal self-pipe (`ses.signal_pipe`, src/common-session.c).  dropbear
    uses no `pipe2` flags, no `socketpair`, no `accept4` and no
    SOCK_NONBLOCK, so every non-blocking PIPE OR SOCKET it holds went
    through that helper after the fact (it does open a regular file
    O_NONBLOCK directly, in src/svr-authpubkey.c, which is not one) — which means the `F_GETFL` decline is
    what it stops at, before any pipe arm here is reached.

    `flags` arrives already truncated to 32 bits (see
    `Syscall.pipe_flags32`), because pipe2's flag word is an `int`. -/
def pipe2_spec (fildes flags : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
  bind getModelSpec fun m =>
    if !(z_ldiff (flags.toNat : Int) pipe2_flags_mask == 0) then
      err_ret EINVAL
      /- a bit outside the accepted mask: real -EINVAL, before
         the pipe is made and before `fildes` is touched -/
    else if !(w_is0 flags) then unmodeled
      /- an accepted but uninterpreted flag: fail closed -/
    else
      let id := pipe_new_id (m_pipes m)
      match pipe_lookup (m_pipes m) id with
      | some _ => unmodeled
        /- the id-space wrapped: see `State.pipe_new_id`.
           Unreachable, and fail closed rather than alias -/
      | none =>
          let injected : SysSpec SyscallEffect :=
            bind (errno_from pipe2_errnos) fun e => err_ret e
          if !(access_okb fildes 8) then alt injected (err_ret EFAULT)
          /- `copy_to_user` IS `access_ok` AND THEN THE COPY, and this is the
             `access_ok` half.  Without it nothing bounds `fildes` before the
             walk below: `State.read_bytes_map` advances with WRAPPING `bv`
             addition, so a `fildes` near 2^64 walks off the top and back in
             at 0, and if an `mp` backs both halves the walk answers `some`
             and this spec returns SUCCESS — a pipe made and two descriptors
             installed — on a range Linux's `access_ok` refuses outright.
             `State.access_okb` sums in `Int` and so refuses it.

             Same shape and same repair as `Net.Socket.socketpair_dest_writable`,
             whose comment carries the argument; do not re-derive it here.
             ONE DIFFERENCE, and it is what lets this arm answer where that
             one declines: `do_pipe2` copies both descriptors with a SINGLE
             `copy_to_user` of `int fildes[2]` (fs/pipe.c:1040, v6.18.46), so
             there is one `access_ok` over the whole 8 bytes rather than
             socketpair's two `put_user`s over 4 each.  A refused range
             therefore copies NOTHING — no partial write to rule out — and
             `-EFAULT` with the model unchanged is Linux's answer rather than
             a fail-closed stand-in.  `do_pipe2` then `fput`s both files and
             `put_unused_fd`s both reservations (:1041-1045), which is why
             nothing is installed. -/
          else
            match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 8) with
            | some _ =>
                alt injected
                  (bind (lowest_fd (m_fds m)) fun fdr =>
                   /- read end: the lowest free fd -/
                   let fds1 := fd_insert (m_fds m) fdr (FdEntry.FdPipe id false)
                   bind (lowest_fd fds1) fun fdw =>
                   /- write end: the next lowest -/
                   bind (modifySpec
                         (with_fds (fd_insert fds1 fdw (FdEntry.FdPipe id true)))) fun _ =>
                   bind (modifySpec
                         (with_pipes (pipe_insert (m_pipes m) id ([], (0 : Int))))) fun _ =>
                   /- an empty queue -/
                   pure (mkEffect (BitVec.ofInt 64 0)
                           [(fildes, pipe_fd_bytes fdr fdw)] []))
            | none =>
                match read_bytes_map i.in_wmem fildes (BitVec.ofInt 64 1) with
                | none => alt injected (err_ret EFAULT)
                  /- not one byte of the destination is writable: real -EFAULT,
                     with no pipe made and no descriptor installed -/
                | some _ => unmodeled
                  /- a writable prefix and an unwritable tail: `copy_to_user`
                     leaves an architecture-dependent number of bytes behind.
                     Fail closed -/

/-! ## Sanity checks

  It is one definition and the prose above. The checks below are PORT CHECKS, and
  they pin the computable decisions the header argues for: the accepted flag mask and
  the injectable errno list, `-EINVAL` for a bit outside the mask, the two descriptor
  numbers a fresh table hands out (`fd[0] < fd[1]`, the second allocated with the
  first already reserved), the one contiguous eight-byte write of `int fildes[2]`,
  `-EFAULT` for a wholly unwritable destination, and `unmodeled` for a partially
  writable one and for any accepted-but-uninterpreted flag.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so the checks state the spec's OUTCOME
    rather than comparing entries: the outcome carries the returned word,
    the whole `SyscallEffect` and the resulting `Model`, which is what a
    caller observes.  The spec is a `bind` chain over a `choose`, so each
    proof below supplies the chain's witnesses explicitly — the input,
    the model, and (where a pipe is made) the two descriptor numbers —
    and leaves the arithmetic to `decide`. -/

/-- The flags `__do_pipe_flags` accepts — `O_CLOEXEC | O_NONBLOCK |
    O_DIRECT | O_NOTIFICATION_PIPE(= O_EXCL)` — as one word. -/
example : pipe2_flags_mask = 542848 := by decide

/-- The injectable set, in order:
    `-EMFILE`, `-ENFILE`, `-ENOMEM`. -/
example : pipe2_errnos = [24, 23, 12] := by decide

/-- `z_ldiff` is  `Z.ldiff` on the values this file feeds it: a bit
    inside the mask survives only where the mask has it. -/
example : z_ldiff 1 542848 = 1 := by decide

example : z_ldiff 542848 542848 = 0 := by decide

example : z_ldiff 0 542848 = 0 := by decide

/-- …and a bit OUTSIDE it is exactly what survives — the -EINVAL test. -/
example : z_ldiff 542849 542848 = 1 := by decide

/-! ### Fixtures

    Three destinations to hand `pipe2`: every address writable, NO address
    writable, and exactly one byte writable at `fildes`.  `read_bytes_map`
    only asks whether a range is mapped, so "writable" here is "answers a
    byte"; the bytes themselves are not observed by this spec. -/

/-- Every address is writable, every byte zero. -/
private def demoWmem : word → Option byte := fun _ => some 0

/-- The model the checks run in: an empty fd table, an empty pipe table,
    an empty file system, EOF on stdin and no halt. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- A `pipe2` input: `fildes = 0x1000`, `flags = 0`. -/
private def demoInput : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := demoWmem }

/-- `read_bytes_map` sees the whole eight-byte range: every address is
    writable and answers a zero byte. -/
private theorem demoRead8 :
    read_bytes_map demoWmem (BitVec.ofNat 64 0x1000) (BitVec.ofNat 64 8)
      = some [0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- The writable view of a destination with NOTHING mapped. -/
private def noWmem : word → Option byte := fun _ => none

/-- …so the eight-byte walk reads nothing. -/
private theorem noRead8 :
    read_bytes_map noWmem (BitVec.ofNat 64 0x1000) (BitVec.ofNat 64 8) = none := by
  decide

/-- …nor does the one-byte probe. -/
private theorem noRead1 :
    read_bytes_map noWmem (BitVec.ofNat 64 0x1000) (BitVec.ofNat 64 1) = none := by
  decide

/-- A `pipe2` input whose destination is wholly unmapped. -/
private def demoInputUnmapped : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := noWmem }

/-- A writable view with exactly ONE byte mapped at the destination. -/
private def oneByteWmem : word → Option byte :=
  fun a => if a == (BitVec.ofNat 64 0x1000) then some 0 else none

/-- The eight-byte walk does not fit. -/
private theorem oneByteRead8 :
    read_bytes_map oneByteWmem (BitVec.ofNat 64 0x1000) (BitVec.ofNat 64 8) = none := by
  decide

/-- …but the one-byte probe does. -/
private theorem oneByteRead1 :
    read_bytes_map oneByteWmem (BitVec.ofNat 64 0x1000) (BitVec.ofNat 64 1)
      = some [0] := by
  decide

/-- A `pipe2` input whose destination is writable for one byte only. -/
private def demoInputPartial : SyscallInput :=
  { in_sysno := 59, in_args := [0x1000, 0], in_mem := fun _ => some 0,
    in_wmem := oneByteWmem }

/-! ### THE FLAGS ARE TESTED FIRST -/

/-- `pipe2(UNMAPPED, 1)` is `-EINVAL`, never `-EFAULT`: the mask test
    precedes the user-pointer walk, and the model is untouched. -/
example :
    pipe2_spec 0x1000 1 demoInputUnmapped demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp +decide [pipe2_spec, inputSpec, getModelSpec, input, getModel, bind, pure,
    err_ret, ret_only, demoInputUnmapped, demoModel]

/-- An accepted but uninterpreted flag (`O_CLOEXEC`) is `unmodeled`: the
    model interprets only the ABSENCE of all four. -/
example :
    pipe2_spec 0x1000 (BitVec.ofNat 64 O_CLOEXEC.toNat) demoInput demoModel .unmodeled := by
  simp +decide [pipe2_spec, inputSpec, getModelSpec, input, getModel, bind,
    unmodeled, demoInput, demoModel]

/-! ### THE DESCRIPTORS, AND THE EIGHT BYTES -/

/-- The success arm: `fd[0] = 0`, `fd[1] = 1` (allocated above the read end
    already reserved), both entries installed, the pipe an empty queue, and
    the whole effect one eight-byte write of `int fildes[2]`. -/
example :
    pipe2_spec 0x1000 0 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0)
              [(0x1000, pipe_fd_bytes 0 1)] [])
        (with_pipes [(0, ([], (0 : Int)))]
          (with_fds [(1, FdEntry.FdPipe 0 true), (0, FdEntry.FdPipe 0 false)]
            demoModel)) []) := by
  -- the two heads of the chain: `input`, then `get_model`
  simp +decide [pipe2_spec, inputSpec, getModelSpec, input, getModel, bind,
    demoInput, demoModel]
  refine ⟨demoInput, demoModel, ⟨rfl, rfl⟩, demoModel, demoModel, ⟨rfl, rfl⟩, ?_⟩
  -- the mask test passes, the pipe id is free, and the destination is
  -- mapped for all eight bytes
  simp +decide [m_pipes, m_fds, demoInput, demoModel, mkModel, pipe_new_id,
    pipe_lookup, fd_insert, with_fds, with_pipes, pipe_insert]
  rw [demoRead8]
  refine Or.inr ?_
  simp +decide [bind, pure]
  -- the two allocations: `fd[0] = 0`, then `fd[1] = 1` above it
  refine ⟨0, demoModel, ⟨0, ⟨rfl, rfl⟩, rfl⟩, 1, demoModel, ⟨1, ⟨?_, rfl⟩, rfl⟩, ?_⟩
  · decide
  · simp +decide [modifySpec, modify, with_fds, with_pipes, demoModel, mkModel]

/-- The eight bytes really are `fildes[0]` then `fildes[1]`, each four
    little-endian bytes — one contiguous range, not two. -/
example : pipe_fd_bytes 0 1 = [(0 : byte), 0, 0, 0, 1, 0, 0, 0] := by decide

/-! ### THE DESTINATION

    -EFAULT when not one byte of the destination is writable (with the
    injected errnos as the alternative), and `unmodeled` when a writable
    prefix is followed by an unwritable tail. -/

/-- A wholly unwritable destination is `-EFAULT` with no pipe made and no
    descriptor installed — the model unchanged, as `do_pipe2`'s `fput` and
    `put_unused_fd` unwind both ends. -/
example :
    pipe2_spec 0x1000 0 demoInputUnmapped demoModel
      (.ok (mkEffect (errno_ret EFAULT) [] []) demoModel []) := by
  simp +decide [pipe2_spec, inputSpec, getModelSpec, input, getModel, bind,
    demoInputUnmapped, demoModel]
  refine ⟨demoInputUnmapped, demoModel, ⟨rfl, rfl⟩, demoModel, demoModel, ⟨rfl, rfl⟩, ?_⟩
  simp +decide [m_pipes, m_fds, demoInputUnmapped, demoModel, mkModel, pipe_new_id,
    pipe_lookup]
  rw [noRead8]
  dsimp only
  rw [noRead1]
  dsimp only
  refine Or.inr ?_
  simp +decide [err_ret, ret_only, pure]

/-- A writable PREFIX and an unwritable tail is `unmodeled`: `copy_to_user`
    leaves an architecture-dependent number of bytes behind, so the model
    fails closed rather than guess. -/
example :
    pipe2_spec 0x1000 0 demoInputPartial demoModel .unmodeled := by
  simp +decide [pipe2_spec, inputSpec, getModelSpec, input, getModel, bind,
    demoInputPartial, demoModel]
  refine ⟨demoInputPartial, demoModel, ⟨rfl, rfl⟩, demoModel, demoModel, ⟨rfl, rfl⟩, ?_⟩
  simp +decide [m_pipes, m_fds, demoInputPartial, demoModel, mkModel, pipe_new_id,
    pipe_lookup]
  rw [oneByteRead8]
  dsimp only
  rw [oneByteRead1]
  dsimp only
  exact rfl

end LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
