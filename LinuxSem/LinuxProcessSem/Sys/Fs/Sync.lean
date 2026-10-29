/-
  * LinuxProcessSem.Sys.Fs.Sync — fsync (82), fdatasync (83)

  This file answers to Linux `fs/sync.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines
  the syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  A spec's monad is `SysSpec SyscallEffect` from `MonadInstances`, fixed
  at the concrete `Model`/`SyscallInput`/`event`.  The 
  `sys_scope` sequencing `x <- c ;; k` is `bind c (fun x => k)` in Lean,
  which is how the one `get_model` step below is written.  `ret_only`
  and `err_ret` are `Sys/Syscall.lean`'s.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Sync

open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall

/-- `fsync fd` / `fdatasync fd`: flush this file to stable storage.

    The model's file system is an interpreted map from paths to byte
    contents (`Fs.Fs`) with no page cache, no dirty state and no
    durability notion: a write is already durable when it returns, and
    the map is observed only at exit (it rides out in `ExitEv`).  A
    SUCCESSFUL fsync is therefore observationally inert — it returns 0,
    touches no memory and emits no event.  Its whole content is the
    ERROR cases below, and those are real kernel returns, not modeling
    gaps.

    THE FD IS RESOLVED FIRST, exactly as the kernel orders it: `do_fsync`
    (Linux v6.10-v6.15, fs/sync.c, `do_fsync`) performs the `fdget` and
    returns -EBADF before `vfs_fsync` is ever entered, so -EBADF strictly
    precedes the -EINVAL below and a closed fd is -EBADF whatever kind of
    object the number would have named.  (`do_fsync` itself does move over the
    range, and the MAINLINE tags alone do not pin it: v6.12 renamed the
    accessor to `fd_file`, and v6.13 rewrote the function around the
    `CLASS(fd, f)` scope guard, restructuring the control flow and
    dropping the explicit `fdput` — but that rewrite was backported, so
    the `linux-6.12.y` STABLE branch already carries it and the
    intermediate `fd_file` shape exists on no stable branch at all.
    None of the three shapes changes what the lookup DOES or when it
    runs — `CLASS(fd, ...)` is declared over plain `fdget`, not
    `fdget_pos` or `fdget_raw` — so -EBADF precedes `vfs_fsync` in every
    one of them, mainline tag and stable head alike.  The bodies of
    `SYSCALL_DEFINE1(fsync)`, `SYSCALL_DEFINE1(fdatasync)`,
    `vfs_fsync` and `vfs_fsync_range` ARE byte-identical across the
    whole range.)

    -EINVAL FOR A CHANNEL.  `vfs_fsync_range` (Linux v6.10-v6.15,
    fs/sync.c, `vfs_fsync_range`) returns -EINVAL when the file's
    operations table carries no `.fsync` member.  The model's channels
    are PIPES — the `FdEntry` docstring in State.lean fixes that, and the
    precedent for RELYING on it is `ReadWrite.lseek_spec`'s -ESPIPE, cited just
    below.  It is NOT the rule that makes stdout write-only: that one
    survives shell redirection, since `prog > out.txt` really does give
    an O_WRONLY regular file whose read is -EBADF, whereas pipe-ness
    does not survive it.  Pipe-ness is the strictly stronger
    commitment, and -ESPIPE is the only place the model already spends
    it — and the anonymous-pipe operations carry no
    `.fsync`: `pipefifo_fops` (Linux v6.10-v6.14, fs/pipe.c), and
    `pipeanon_fops` (Linux v6.15, fs/pipe.c) once that release split the
    anonymous-pipe table out of the FIFO one.  Nor has any other object
    a channel is attached to in practice: `socket_file_ops` (Linux
    v6.10-v6.15, net/socket.c), `tty_fops` (Linux v6.10-v6.15,
    drivers/tty/tty_io.c) and `null_fops` (Linux v6.10-v6.15,
    drivers/char/mem.c) omit it too.

    It is the ABSENCE of `.fsync` that is cited, and THAT holds for
    every one of these tables across the whole range.  The tables
    themselves are not fixed, so claiming they were byte-identical would
    be wrong: `pipefifo_fops`, `socket_file_ops` and `tty_fops` each
    dropped a then-redundant `.llseek = no_llseek` in v6.12, and v6.15
    split `pipeanon_fops` off.  `null_fops` alone is byte-identical,
    carrying `.llseek = null_lseek` unchanged.

    The one object that answers 0 instead is a REGULAR FILE on a channel
    fd — which plain shell redirection (prog > out.txt) produces.  So
    this is a MODEL ASSUMPTION that redirected stdio falsifies.
    `ReadWrite.lseek_spec`'s -ESPIPE rests on the very same assumption
    and the very same redirection falsifies it.

    0 FOR A FILE, WHATEVER ITS ACCESS MODE.  fs/sync.c consults `f_mode`
    nowhere — nor `FMODE_*`, `MAY_WRITE`, `mnt_want_write`, `IS_RDONLY`
    or -EROFS; there is no access-mode check in that file to
    misattribute — so fsync on a descriptor opened O_RDONLY succeeds
    exactly as on one opened for writing, and `FdFile` and `FdFileW`
    agree.  (The one fd that defeats the shorthand is an O_PATH one,
    which is -EINVAL rather than 0 — `do_dentry_open` gives it
    `empty_fops`, so it fails the `.fsync` test above rather than any
    mode test.  `Open.openat_spec` models three flag words and O_PATH is not
    among them, so no such fd exists here.)  This is
    the arm where copying `ReadWrite.write_spec`'s -EBADF-on-a-read-only-fd would
    be a confident wrong answer.

    0 FOR A DIRECTORY FD — the case a real caller depends on: dropbear
    fsyncs the parent directory to make a `link`-published key durable.
    `ext4_dir_operations` (Linux v6.10-v6.15, fs/ext4/dir.c) does set
    `.fsync = ext4_sync_file`, and the non-regular inode is handled
    explicitly one call further down: `!S_ISREG` takes
    `ext4_force_commit` (the call site is Linux v6.10-v6.15,
    fs/ext4/fsync.c, `ext4_fsync_journal`; the function itself is
    defined in fs/ext4/super.c).  So the call succeeds rather than taking the
    -EINVAL a missing `.fsync` would give.  tmpfs agrees: its directories carry
    `.fsync = noop_fsync` through `simple_offset_dir_operations` (Linux
    v6.10-v6.15, fs/libfs.c, `simple_offset_dir_operations`; the
    assignment is in `__shmem_get_inode`, Linux v6.10-v6.15, mm/shmem.c,
    which `shmem_get_inode` wraps), and `noop_fsync` (Linux v6.10-v6.15,
    fs/libfs.c, `noop_fsync`) returns 0.

    The bound worth naming, because it is a real one: this holds of the
    filesystems a run can plausibly sit on, NOT of every filesystem.
    `proc_dir_operations` (Linux v6.10-v6.15, fs/proc/generic.c) and
    `kernfs_dir_fops` (Linux v6.10-v6.15, fs/kernfs/dir.c) set no
    `.fsync` at all, so a directory fd on procfs or sysfs really is
    -EINVAL.  `FdDir` only ever comes from `openat` of "." or ".."
    (`Open.path_is_dirref`), so a run diverges here when its working
    directory OR ITS PARENT is on procfs or sysfs.

    THAT IS WIDER THAN A BOUND ON THE WORKING DIRECTORY ALONE, and the reason
    is worth having in front of you: A DIRECTORY'S PARENT CAN BE ON A
    DIFFERENT FILESYSTEM THAN THE DIRECTORY, because a mount point sits
    in one and resolves into the other.  So the ".." half admits runs
    a "."-only bound would exclude by construction:

      cwd = /sys/kernel/debug            (debugfs, a mount UNDER sysfs)
        openat(".",  O_RDONLY) + fsync   Linux 0        model 0   conforms
        openat("..", O_RDONLY) + fsync   Linux -EINVAL  model 0   DIVERGES

    debugfs gives its directories `simple_dir_operations`
    (fs/debugfs/inode.c, Linux v6.18.46, commit 1f99e9ab748f), whose
    `.fsync` is `noop_fsync` (fs/libfs.c, same tree), so the cwd answers
    0 and that call conforms; ".." resolves to /sys/kernel, whose
    `kernfs_dir_fops` sets no `.fsync` at all, so that call is -EINVAL.
    (The other citations in this file are to the v6.10-v6.15 window;
    the two above are to the version README.md names.)  The cwd here is on NEITHER procfs nor sysfs,
    and the same run conforms on one call and diverges on the next.
    /proc/sys/fs/binfmt_misc does it too, and so does any mount point
    under either filesystem.

    This divergence is a known limitation, kept on purpose: the arm
    answers 0 here rather than declining.

    `fd` arrives ALREADY TRUNCATED to 32 bits (see `Syscall.fd32`): the ABI
    declares it `unsigned int` and the syscall wrapper narrows it (Linux
    v6.10-v6.15, arch/riscv/include/asm/syscall_wrapper.h,
    `__SYSCALL_DEFINEx`; Linux v6.10-v6.15, include/linux/syscalls.h,
    `__SC_CAST`).  So `fsync(2^32)` IS `fsync(0)` — it targets stdin and
    answers -EINVAL.  It is NOT -EBADF: the truncation aliases, it does
    not reject.

    OUT OF SCOPE, and unreachable rather than approximated: the deferred
    writeback errors `ext4_sync_file` can report (-EIO, -ENOSPC, -EROFS,
    and the `file_check_and_advance_wb_err` consumption, which reports
    each distinct `errseq_t` value at most once per `struct file`).  Each needs a failing or
    shut-down mount; the model has no I/O error state for one to come
    from, so no execution reaches them.

    `fdatasync` SHARES THIS SPEC, as `exit` and `exit_group` share
    `Exit.exit_spec`.  The two are one kernel function — `do_fsync(fd, 0)`
    against `do_fsync(fd, 1)` — and `datasync` is not read until AFTER
    both the -EBADF and the -EINVAL decisions are settled, so neither
    error can depend on it.

    The stronger claim, that `datasync` never branches an error path at
    all, would be FALSE, and is deliberately not the one made here.
    `__generic_file_fsync` (Linux v6.10-v6.15, fs/libfs.c) and
    `generic_buffers_fsync_noflush` (Linux v6.10-v6.15, fs/buffer.c)
    both skip `sync_inode_metadata` — and the error it would otherwise
    fold into the return — when `datasync` is set and the inode is not
    `I_DIRTY_DATASYNC`, so an fsync can report an error where an
    fdatasync on the same fd returns 0.  A no-journal ext4 mount reaches
    the second of those through `ext4_fsync_nojournal`.  ext4's journal
    target differs too (`i_datasync_tid` against `i_sync_tid`).

    Every one of those divergences needs a writeback error, an aborted
    journal or a shut-down mount to become visible — exactly the class
    the OUT OF SCOPE paragraph above excludes, and one the model has no
    state to produce.  So the two agree on every input this model can
    express, which is what lets them share a spec.

    THE SHARING IS CONDITIONAL ON THAT, and the condition is worth
    stating where a future change would look for it: the spec holds
    because the model records no metadata, no timestamps and NO I/O
    ERROR STATE.  Give it any of the three — a failing mount, a stored
    writeback error, a dirty-metadata bit — and `__generic_file_fsync`,
    `generic_buffers_fsync_noflush`, ext4's commit-tid selection and its
    barrier choice all become observable, at which point these two must
    stop sharing a spec.  Splitting them is then the fail-closed move,
    not an optimization.

    -EINVAL FOR A PIPE END, and here the missing `.fsync` the channel
    arm ASSUMES is instead a fact the model owns.  `pipeanon_fops`, the
    table `create_pipe_files` installs on both ends of an anonymous pipe
    (fs/pipe.c:1257-1266, installed at :946 and :957, v6.18.46), has no
    `.fsync` line — nor does the FIFO table `pipefifo_fops` (:1246-1255),
    which a `pipe2` fd never gets.  That is the same table
    `ReadWrite.lseek_spec`'s -ESPIPE arm reads, and for the same reason:
    both errnos come from an absent method rather than from a test on the
    file.  So `vfs_fsync_range` (fs/sync.c:179-188, v6.18.46) takes its
    opening `if (!file->f_op->fsync) return -EINVAL` (:183-184) before it
    does anything else, on both ends and whatever the pipe holds.  That
    test also precedes the `datasync` read at :185, so fdatasync agrees —
    the sharing argument above needs no pipe-specific clause.

    THE DIRECTORY ARM IS WHAT THIS MUST NOT BE CONFUSED WITH.  Three of
    the five entries answer 0 and two answer -EINVAL, and the split does
    not follow "is it a file": a directory fd succeeds, a pipe does not.
    Inheriting the success answer would have been the confident wrong
    one, which is why the arms are enumerated rather than collapsed into
    a `some _` catch-all: a new `FdEntry` constructor should force a
    decision here, not pick up whichever answer the majority of the
    existing arms happen to give. -/
def fsync_spec (fd : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    match fd_lookup (m_fds m) fd with
    | none => err_ret EBADF
      /- fd not open: real -EBADF, before the file is examined -/
    | some (FdEntry.FdChannel _) => err_ret EINVAL
      /- no `.fsync` on a pipe, socket or terminal -/
    | some (FdEntry.FdSocket _) => err_ret EINVAL
      /- nor on a socket: `socket_file_ops` carries no
         `.fsync`, so `vfs_fsync_range` is -EINVAL -/
    | some (FdEntry.FdPipe _ _) => err_ret EINVAL
      /- no `.fsync` on a pipe — see the header -/
    | some (FdEntry.FdDevNull _ _) => err_ret EINVAL
      /- no `.fsync` on /dev/null either: `null_fops`
         (drivers/char/mem.c, v6.18.46) lists `.llseek`,
         `.read`, `.write`, `.read_iter`, `.write_iter`,
         `.splice_write` and `.uring_cmd` and nothing
         else, so `vfs_fsync_range` (fs/sync.c) takes
         its opening `if (!file->f_op->fsync) return
         -EINVAL`, before the `datasync` read — the
         pipe argument above, on a table the model
         knows exactly -/
    | some FdEntry.FdUrandom => err_ret EINVAL
      /- nor on /dev/urandom: `urandom_fops`
         (drivers/char/random.c, v6.18.46) lists
         `.read_iter`, `.write_iter`, `.unlocked_ioctl`,
         `.compat_ioctl`, `.fasync`, `.llseek`,
         `.splice_read` and `.splice_write` and no
         `.fsync`, so the same opening test in
         `vfs_fsync_range` answers -EINVAL -/
    | some (FdEntry.FdFile _ _) => ret_only (BitVec.ofInt 64 0)
      /- O_RDONLY is not an error here: no `f_mode` check -/
    | some (FdEntry.FdFileW _ _) => ret_only (BitVec.ofInt 64 0)
    | some (FdEntry.FdFileA _ _) => ret_only (BitVec.ofInt 64 0)
      /- the same file, opened in append mode: `vfs_fsync_range`
         reads `f_op->fsync`, never `f_flags` -/
    | some (FdEntry.FdFileRW _ _) => ret_only (BitVec.ofInt 64 0)
      /- and opened O_RDWR: it reads no access mode
         either, which is why the read-only arm
         above is not an error -/
    | some FdEntry.FdDir => ret_only (BitVec.ofInt 64 0)
      /- directory fsync succeeds; the key-publish path needs it -/

/-! ## Sanity checks

  It is one definition and the prose above. The checks below are PORT CHECKS, and
  they pin the three answers the header argues for against a concrete model: 0 (with
  an empty effect) for a regular file and for a directory, -EBADF for an fd that is
  not open, and -EINVAL for a descriptor whose object carries no `.fsync`.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so the checks state the spec's OUTCOME
    rather than comparing entries: the outcome carries the returned word
    and the whole `SyscallEffect`, which is what a caller observes. -/

/-- A tiny fd table for the checks: 0 a channel, 1 a regular file
    (`out`), 2 a directory, 3 a pipe end, 4 `/dev/null`. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdDevNull true false) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A syscall input for `fsync` (82).  The spec reads none of it; it is
    here because a `SysSpec` is a relation on an input as well as a
    model. -/
private def demoInput : SyscallInput :=
  { in_sysno := 82, in_args := [1], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- THE SUCCESS ARM RETURNS 0 AND AN EMPTY EFFECT: a regular file leaves
    the model untouched, writes no memory, zeroes and unmaps nothing,
    copies nothing, records no copy-ins and emits no event. -/
example :
    fsync_spec 1 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp [fsync_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- The success arm is not told apart by access mode or concreteness:
    a DIRECTORY answers 0 as well (the key-publish case the header
    argues for). -/
example :
    fsync_spec 2 demoInput demoModel
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) demoModel []) := by
  simp [fsync_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A MISSING FD IS -EBADF, and it is the fd lookup that decides: no
    object is examined at all. -/
example :
    fsync_spec 9 demoInput demoModel
      (.ok (mkEffect (errno_ret EBADF) [] []) demoModel []) := by
  simp [fsync_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- A NON-FILE FD IS -EINVAL: a channel carries no `.fsync`, so
    `vfs_fsync_range`'s opening test answers before anything else. -/
example :
    fsync_spec 0 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp [fsync_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- …and a pipe end is -EINVAL too — the arm whose table the model owns
    (`pipeanon_fops` has no `.fsync`). -/
example :
    fsync_spec 3 demoInput demoModel
      (.ok (mkEffect (errno_ret EINVAL) [] []) demoModel []) := by
  simp [fsync_spec, getModelSpec, bind_getModel, fd_lookup, demoFds,
    demoModel, m_fds, mkModel, err_ret, ret_only, pure]

/-- The two errnos really are the kernel's numbers in the return word,
    and the success return really is a zero word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end LinuxSem.LinuxProcessSem.Sys.Fs.Sync
