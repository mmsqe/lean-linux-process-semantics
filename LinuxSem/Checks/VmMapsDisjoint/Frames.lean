/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames — the bulk of PART 3:
    the cheap frame lemmas, one per syscall arm that leaves [vm_maps] alone.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  The body below is carried over VERBATIM from
  `Checks/VmMapsDisjoint.lean` (commit 63c70ae), in its ORIGINAL ORDER: the
  ranges 1868-2095, 2153-2283, 2480-2533, 2545-2647 and 2666-2974 of the
  pre-split file, under the prelude's imports, options and opens.  Every
  lemma is still the one-line `vm_frame` / `vm_close` / `vm_ret_only` loop
  it was; the tactics come from
  `LinuxSem.Checks.VmMapsDisjoint.Tactics`.

  WHAT IS NOT HERE, and why — the two other groups, both of which cost more
  than this whole module and are therefore split off so that lake can check
  them concurrently with it:

  * `Frames/Wide.lean` — the five arms whose MODEL-state dispatch is wide
    but whose guards are all cheap (`accept4`, `pread64`, `read`,
    `rt_sigaction`, `tgkill`).  Measured: 22.3 s as a module, against
    16.7 s for everything left here, so they cannot ride along;
  * `Frames/CostlyA.lean` … `CostlyF.lean` — the eight `vm_frame_m` arms of
    the wide block, `getsockopt` through `sched_setscheduler` (14.7 s,
    23.5 s, 32.4 s, 25.0 s, 32.1 s and 3.6 s as modules; `writev` and
    `prlimit64` are the two long poles of the whole build).

  Still carried here verbatim: the block notes that introduce the arm
  groups whose members are here — the four `private`-helper arms note
  (with the `vm_close` route it explains) and the getdents64 /
  `vm_ret_only` note.  The `vm_ret_only` and `vm_ret_only_copyins*` macros those arms
  call live in `Tactics.lean`; their doc comments travel with them.

  The split is a MOVE: the arms are independent of each other (each
  proof's only local dependency is the shared `*_model` inversion), which
  is what makes it safe to elaborate them in any module.
-/

import LinuxSem.Checks.VmMapsDisjoint.Tactics
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Sys.Fs.Readdir
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Mm.Madvise
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Drivers.Char.Random
open LinuxSem.Checks.Sys.Fs.DPath
open LinuxSem.Checks.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Fs.EventPoll
open LinuxSem.Checks.Sys.Fs.Fcntl
open LinuxSem.Checks.Sys.Fs.File
open LinuxSem.Checks.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Fs.Open
open LinuxSem.Checks.Sys.Fs.Pipe
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Fs.Select
open LinuxSem.Checks.Sys.Fs.Stat
open LinuxSem.Checks.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Fs.Timerfd
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Kernel.Groups
open LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Kernel.Time.Time
open LinuxSem.Checks.Sys.Net.Socket

namespace LinuxSem.Checks.VmMapsDisjoint

/- -------------------------------------------------------------------------
   The frame lemmas of PART 3: one per arm whose checker reduces after
   the effect-destruct.  Each is one line of the `vm_frame` macro above —
   a single `vm_frame H` — except the nine at the end of the block, which
   need one written-out `cases h : <guard>` step
   first (`vm_close`, see the note there).
   ------------------------------------------------------------------------- -/

theorem check_getcwd_frame (size : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getcwd size eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.DPath.check_getcwd

theorem check_eventfd2_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_eventfd2 flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.EventFd.check_eventfd2 LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_epoll_create1_frame (flags32 : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_epoll_create1 flags32 eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.EventPoll.check_epoll_create1 LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_epoll_ctl_frame (i : SyscallInput) (epfd op32 tfd eventPtr : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_epoll_ctl i epfd op32 tfd eventPtr eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.EventPoll.check_epoll_ctl LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_epoll_pwait_frame (i : SyscallInput) (epfd events maxevents32 sigmask sigsetsize : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_epoll_pwait i epfd events maxevents32 sigmask sigsetsize eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.EventPoll.check_epoll_pwait LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_dup_frame (oldfd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_dup oldfd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.File.check_dup LinuxSem.Checks.Sys.Fs.File.check_dup_result LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_dup3_frame (oldfd newfd flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_dup3 oldfd newfd flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.File.check_dup3 LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_fcntl_frame (fd cmd arg : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fcntl fd cmd arg eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Fcntl.check_fcntl LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_ioctl_frame (fd req : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ioctl fd req eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Ioctl.check_ioctl LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_flock_frame (fd cmd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_flock fd cmd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Locks.check_flock LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_close_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_close fd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Open.check_close LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_pipe2_frame (i : SyscallInput) (fildes flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pipe2 i fildes flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Pipe.check_pipe2 LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_lseek_frame (fd off whence : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_lseek fd off whence eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.ReadWrite.check_lseek LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_pselect6_frame (i : SyscallInput) (n32 inp outp exp tsp sig : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pselect6 i n32 inp outp exp tsp sig eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Select.check_pselect6

theorem check_ppoll_frame (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ppoll i ufds nfds tsp sig sigsetsize eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Select.check_ppoll

theorem check_readlinkat_frame (dirfd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_readlinkat dirfd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Stat.check_readlinkat LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_fstat_frame (i : SyscallInput) (fd statbuf : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fstat i fd statbuf eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Stat.check_fstat LinuxSem.Checks.Sys.Fs.Stat.check_fstat_chrdev LinuxSem.Checks.Sys.Fs.Stat.check_fstat_deliver LinuxSem.Checks.Sys.Fs.Stat.check_fstat_deliver_by LinuxSem.Checks.Sys.Fs.Stat.check_fstat_devnull LinuxSem.Checks.Sys.Fs.Stat.check_fstat_file LinuxSem.Checks.Sys.Fs.Stat.check_fstat_urandom LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_fsync_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fsync fd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Sync.check_fsync LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_timerfd_create_frame (clkid flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_timerfd_create clkid flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.Timerfd.check_timerfd_create LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_exit_frame (code : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_exit code eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Exit.check_exit LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_set_tid_address_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_set_tid_address eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Fork.check_set_tid_address

theorem check_sched_getaffinity_frame (len : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sched_getaffinity len eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_getaffinity LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_sched_yield_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sched_yield eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_yield LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_setid_frame (get : Creds → IdTriple) (put : IdTriple → Creds → Creds) (user : Bool) (v : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_setid get put user v eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_setid LinuxSem.Checks.Sys.Prelude.check_ret_only LinuxSem.Checks.Sys.Kernel.Sys.check_setid_result

theorem check_setsid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_setsid eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_setsid

theorem check_setgroups_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_setgroups eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Groups.check_setgroups LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_uname_frame (i : SyscallInput) (name : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_uname i name eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_uname LinuxSem.Checks.Sys.Prelude.check_ret_only LinuxSem.Checks.Sys.Kernel.Sys.check_uname_copy

theorem check_prctl_frame (option_ arg2 : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_prctl option_ arg2 eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_prctl LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_gettimeofday_frame (i : SyscallInput) (tv tz : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_gettimeofday i tv tz eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Time.Time.check_gettimeofday LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_getpid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getpid eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_getpid LinuxSem.Checks.Sys.Kernel.Fork.check_set_tid_address

theorem check_getid_frame (sel : Creds → word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getid sel eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_getid LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_gettid_frame (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_gettid eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Sys.check_gettid LinuxSem.Checks.Sys.Kernel.Fork.check_set_tid_address

theorem check_socketpair_frame (i : SyscallInput) (family type protocol sv : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_socketpair i family type protocol sv eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_socketpair LinuxSem.Checks.Sys.Prelude.check_ret_only LinuxSem.Checks.Sys.Net.Socket.check_socketpair_faulted LinuxSem.Checks.Sys.Net.Socket.check_socketpair_written

theorem check_listen_frame (fd backlog : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_listen fd backlog eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_listen LinuxSem.Checks.Sys.Net.Socket.check_errno_or_success LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_getsockname_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getsockname fd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_getsockname LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_getpeername_frame (fd : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getpeername fd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_getpeername LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_recvfrom_frame (_i : SyscallInput) (fd buf size : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_recvfrom _i fd buf size eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_recvfrom LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero LinuxSem.Checks.Sys.Net.Socket.check_recv_fd_answer LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_shutdown_frame (fd how : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_shutdown fd how eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_shutdown LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_recvmsg_frame (fd flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_recvmsg fd flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_recvmsg LinuxSem.Checks.Sys.Net.Socket.check_recv_fd_answer LinuxSem.Checks.Sys.Prelude.check_ret_only

theorem check_clone_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_clone flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Fork.check_clone LinuxSem.Checks.Sys.Kernel.Fork.check_clone_answer LinuxSem.Checks.Sys.Kernel.Fork.check_clone_resolve

theorem check_wait4_frame (i : SyscallInput) (upid stat_addr options rusage : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_wait4 i upid stat_addr options rusage eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Exit.check_wait4

theorem check_getrandom_frame (i : SyscallInput) (buf cap flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getrandom i buf cap flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Drivers.Char.Random.check_getrandom LinuxSem.Checks.Sys.Drivers.Char.Random.check_getrandom_zero

theorem check_clone3_frame (i : SyscallInput) (uargs size : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_clone3 i uargs size eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Fork.check_clone3 LinuxSem.Checks.Sys.Kernel.Fork.check_clone3_resolve LinuxSem.Checks.Sys.Kernel.Fork.check_clone_answer

/- -------------------------------------------------------------------------
   The four `private`-helper arms: `ftruncate`, `faccessat`, `faccessat2`,
   `unlinkat`.

   These are NOT closed by `vm_frame`, for two independent reasons, and the
   fix for each is measured:

   (a) their accepting branch leaves the module through a `private def`
       (`Open.check_ftruncate_file_arm`, `Open.check_faccessat_body`,
       `Namei.check_unlinkat_body`), whose equation lemmas are not nameable
       from here, so `simp only` cannot unfold it.  `Checks/Sys/Fs/Open.lean`
       and `Checks/Sys/Fs/Namei.lean` now carry a PUBLIC `*_frame` for each
       of those helpers, and the loop cites it as a term (`vm_close`'s
       bracketed form);

   (b) their FIRST guard is a bitvector computation — `decide (len.toInt < 0)`,
       `!(modeled_access_mode mode)`, `!(modeled_unlink_flags flags)`.  The
       loop's `split at H` / `simp only [check_X] at H` must reduce such a
       guard to decide which branch it is in, and `BitVec.toInt` /
       `z_ldiff` / `z_land` on a SYMBOLIC word do not reduce: the attempt
       runs off `maxRecDepth` (measured: `simp only [check_ftruncate] at H`
       spends ~250,000 `Nat.rec` unfoldings before the ceiling), which is
       an UNRECOVERABLE error, so it cannot even be caught by `first`.

   THE ROUTE THAT WORKS (one `destruct` per guard) is to
   case the guard as a BOOLEAN — `cases h1 : decide (len.toInt < 0)`, never
   `split` — and then let `simp only [h1, Bool.false_eq_true, ite_false]`
   rewrite the `if`.  `cases` on a `Bool` term only generalises and splits
   it; it never reduces it.  After the guards are gone the ordinary
   `vm_close` loop takes over.  Measured: 1.3 s - 2.0 s per arm.
   ------------------------------------------------------------------------- -/

/-- `ftruncate`'s frame.  The `len.toInt < 0` guard is cased as a `Bool`
    (`cases` does not reduce it); every `fd_lookup` arm but the three
    writable-file ones answers `check_ret_only`, and those three go through
    the now-public `Open.check_ftruncate_file_arm_frame`. -/
theorem check_ftruncate_frame (fd len : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ftruncate fd len eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Open.check_ftruncate at H
    cases h1 : decide (len.toInt < 0)
    all_goals (simp only [h1, Bool.false_eq_true, ite_true, ite_false] at H)
    vm_close H [exact LinuxSem.Checks.Sys.Fs.Open.check_ftruncate_file_arm_frame _ _ _ _ _ _ H] LinuxSem.Checks.Sys.Fs.Open.check_ftruncate LinuxSem.Checks.Sys.Prelude.check_ret_only)

/-- `faccessat`'s frame: two `Bool` guards, then the copy-in ledger and
    `check_faccessat_body`. -/
theorem check_faccessat_frame (i : SyscallInput) (dirfd pathp mode : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat i dirfd pathp mode eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Open.check_faccessat at H
    cases h1 : !(Sys.Fs.Open.modeled_access_mode mode)
    · simp only [h1, Bool.false_eq_true, ite_false] at H
      cases h2 : !(Sys.Fs.Open.access_mode_f_ok mode)
      · simp only [h2, Bool.false_eq_true, ite_false] at H
        vm_close H [exact LinuxSem.Checks.Sys.Fs.Open.check_faccessat_body_frame _ _ _ _ _ _ _ H] LinuxSem.Checks.Sys.Fs.Open.check_faccessat LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
      · simp only [h2, ite_true] at H
        vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
    · simp only [h1, ite_true] at H
      vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only)

/-- `faccessat2`'s frame: four `Bool` guards in front of the same body
    `faccessat` uses. -/
theorem check_faccessat2_frame (i : SyscallInput) (dirfd pathp mode flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat2 i dirfd pathp mode flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 at H
    cases h1 : !(Sys.Fs.Open.modeled_access_mode mode)
    · simp only [h1, Bool.false_eq_true, ite_false] at H
      cases h2 : !(Sys.Fs.Open.valid_access_flags flags)
      · simp only [h2, Bool.false_eq_true, ite_false] at H
        cases h3 : !(Sys.Fs.Open.modeled_access_flags flags)
        · simp only [h3, Bool.false_eq_true, ite_false] at H
          cases h4 : !(Sys.Fs.Open.access_mode_f_ok mode)
          · simp only [h4, Bool.false_eq_true, ite_false] at H
            vm_close H [exact LinuxSem.Checks.Sys.Fs.Open.check_faccessat_body_frame _ _ _ _ _ _ _ H] LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
          · simp only [h4, ite_true] at H
            vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
        · simp only [h3, ite_true] at H
          vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
      · simp only [h2, ite_true] at H
        vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
    · simp only [h1, ite_true] at H
      vm_close H LinuxSem.Checks.Sys.Fs.Open.check_faccessat2 LinuxSem.Checks.Sys.Fs.Open.check_access_exists LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only)

/-- `unlinkat`'s frame: one `Bool` guard, the copy-in ledger, then the
    private `Namei.check_unlinkat_body` through its public frame. -/
theorem check_unlinkat_frame (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Fs.Namei.check_unlinkat i dirfd pathp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Namei.check_unlinkat at H
    cases h1 : !(Sys.Fs.Namei.modeled_unlink_flags flags)
    · simp only [h1, Bool.false_eq_true, ite_false] at H
      vm_close H [exact LinuxSem.Checks.Sys.Fs.Namei.check_unlinkat_body_frame _ _ _ _ _ _ _ _ H] LinuxSem.Checks.Sys.Fs.Namei.check_unlinkat LinuxSem.Checks.Sys.Fs.Namei.check_unlink_result LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only
    · simp only [h1, ite_true] at H
      vm_close H LinuxSem.Checks.Sys.Fs.Namei.check_unlinkat LinuxSem.Checks.Sys.Fs.Namei.check_unlink_result LinuxSem.Checks.Sys.Prelude.check_copyins LinuxSem.Checks.Sys.Prelude.check_copyins_after LinuxSem.Checks.Sys.Prelude.check_ret_only)

/-- `rt_sigprocmask`'s frame.  The arm CHANGES the model — `with_sigmask`,
    and on the delivery branch `with_killed` over it — so no `vm_frame` loop
    could close it; what it does not change is the VM half, and
    `Checks/Sys/Kernel/Signal.lean` proves exactly that statement beside the
    checker (`check_rt_sigprocmask_frame`, which has the
    `check_write_oset_ok_iff` inversion it needs).  This is
    `vm_frame H` discharged one module across. -/
theorem check_rt_sigprocmask_frame (i : SyscallInput) (how nset oset ss : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Signal.check_rt_sigprocmask i how nset oset ss eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m :=
  LinuxSem.Checks.Sys.Kernel.Signal.check_rt_sigprocmask_frame i how nset oset ss eff m m' evs H

/- -------------------------------------------------------------------------
   Five more arms, and the leaf closer they share: `getdents64`,
   `getgroups`, `setsockopt`, `sigaltstack` (and `getdents64`'s
   ten-constructor descriptor dispatch, which is also `socketpair`'s
   shape).

   WHY THEY NEEDED A WRITTEN-OUT WALK rather than one `vm_frame` line.
   Two reasons, both measured, and both new relative to the block above:

   (a) THE DESCRIPTOR DISPATCH IS A MATCH ON NESTED PATTERNS
       (`none`, `some (.FdChannel _)`, … , `some .FdDir`).
       `split at H` answers "Missing cases: _" on it — the wildcard arm
       over a nested constructor pattern is not a case `split` builds a
       motive for — so the dispatch has to be `generalize hq : fd_lookup
       (m_fds m) fd = q` + `cases q` + `cases e`, which is `(4)` of
       `Checks/Sys/Fs/ReadWrite.lean`'s header recipe.  `unfold` on the
       checker then leaves `match none with …` UNREDUCED: `dsimp only`
       is what performs that iota step, and it must be `try`-guarded
       because in the `none`/non-directory arms there is nothing to
       reduce.

   (b) THE EFFECT SHAPE MUST BE DISPOSED OF BEFORE `cases H`, and the
       disposal has to be `contradiction`, never `exact nomatch H`.
       `check_ret_only`'s body is a `match` on the effect with a
       WILDCARD arm, so in 31 of the 32 shapes `simp only [check_ret_only]
       at H` rewrites `H` to `CheckReject = CheckOk …` — a plain
       constructor clash — while in the 32nd it leaves the `if bv_eqb ret
       r`.  `nomatch` on that `if` emits "Missing cases: _", which is
       NOT recoverable, so a `first` chain containing it would abort the
       whole arm; `contradiction` fails cleanly on the `if` and closes the
       clash.  (This is the footgun `Checks/Sys/Fs/ReadWrite.lean`'s
       header records for the `check_read` proofs.)

   The four guards cased as `Bool`s below (`m_sigaltstack_installed`,
   `sock_fd`, `int32_neg`, `sint32 … < 0`) are `cases`-able without
   reducing anything on a symbolic word — that is the `cases h : <guard>`
   route — and
   `check_ret_only`'s terminal `if bv_eqb …` is closed by `vm_ret_only`,
   which also absorbs the `with_sigaltstack_installed` rebuild (`rw` then
   `rfl`, because a projection of a structure update is the old
   projection).
   ------------------------------------------------------------------------- -/

open LinuxSem.LinuxProcessSem.Sys.Fs.Readdir in
/-- `getdents64`'s frame: nine descriptor kinds answer a bare
    `check_ret_only -ENOTDIR`, the directory one answers `-EINVAL` or one
    of the injectable errnos on a buffer too small for an entry, and the
    rest decline.  No arm writes, so no arm moves `vm_maps`. -/
theorem check_getdents64_frame (fd count : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Fs.Readdir.check_getdents64 fd count eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Readdir.check_getdents64 at H
    generalize hq : fd_lookup (m_fds m) fd = q at H
    cases q with
    | none =>
      try (dsimp only at H)
      simp only [check_ret_only] at H
      first
        | (contradiction)
        | (by_cases hv : bv_eqb r (errno_ret EBADF) = true
           · rw [ite_eq_left hv] at H
             cases H
             rfl
           · rw [ite_eq_right hv] at H
             contradiction)
    | some e =>
      cases e with
      | FdDir =>
        try (dsimp only at H)
        by_cases hroom : getdents64_no_room count = true
        · rw [ite_eq_left hroom] at H
          try (dsimp only at H)
          first
            | (by_cases he : errno_ret_in getdents64_errnos r = true
               · rw [ite_eq_left he] at H
                 cases H
                 rfl
               · rw [ite_eq_right he] at H
                 by_cases hv : bv_eqb r (errno_ret EINVAL) = true
                 · rw [ite_eq_left hv] at H
                   cases H
                   rfl
                 · rw [ite_eq_right hv] at H
                   contradiction)
            | (contradiction)
        · rw [ite_eq_right hroom] at H
          contradiction
      | _ =>
        try (dsimp only at H)
        simp only [check_ret_only] at H
        first
          | (contradiction)
          | (by_cases hv : bv_eqb r (errno_ret ENOTDIR) = true
             · rw [ite_eq_left hv] at H
               cases H
               rfl
             · rw [ite_eq_right hv] at H
               contradiction))

/-- `madvise`'s frame: the page-alignment gate, the advice gate, the
    empty-length answer, the range overflow, then the ledger gate and the
    effect match — whose ONE accepted shape rebuilds the model with
    `madvise_dontneed_next`, a `vm_backing` update that leaves `vm_maps`
    definitionally alone. -/
theorem check_madvise_frame (addr len advice : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_madvise addr len advice eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Mm.Madvise.check_madvise at H
    try (dsimp only at H)
    by_cases h1 : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left h1] at H
      vm_ret_only H
    · rw [ite_eq_right h1] at H
      by_cases h2 : (!madvise_dontneed_b advice) = true
      · rw [ite_eq_left h2] at H
        contradiction
      · rw [ite_eq_right h2] at H
        by_cases h3 : w_is0 len = true
        · rw [ite_eq_left h3] at H
          vm_ret_only H
        · rw [ite_eq_right h3] at H
          by_cases h4 : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
          · rw [ite_eq_left h4] at H
            vm_ret_only H
          · rw [ite_eq_right h4] at H
            try (dsimp only at H)
            by_cases h5 : madvise_dontneed_ok (m_vmmaps m) addr (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
            · rw [ite_eq_left h5] at H
              try (dsimp only at H)
              by_cases h6 : (w_is0 r && listNN_eqb zs [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
              · first
                  | (rw [ite_eq_left h6] at H
                     cases H
                     rfl)
                  | (contradiction)
              · (first | (rw [ite_eq_right h6] at H) | (skip))
                contradiction
            · rw [ite_eq_right h5] at H
              contradiction)

set_option maxHeartbeats 1000000 in
/-- `readv`'s frame — closed by
    applying `check_readv_imported_frame` (in
    `Checks/Sys/Fs/ReadWrite.lean`) to the imported-vector body, cited here
    as a TERM.  The effect destruct leaves 32 shapes; only
    `⟨r, [], [], [], [], []⟩` can be accepted, and every terminal of this
    checker is a `check_ret_only`, a `check_ret_only_copyins`, or that
    body. -/
theorem check_readv_frame (i : SyscallInput) (fd iov iovcnt : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_readv i fd iov iovcnt eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.ReadWrite.check_readv at H
    generalize hq : fd_lookup (m_fds m) fd = q at H
    cases q with
    | none =>
      try (dsimp only at H)
      vm_ret_only H
    | some e =>
      try (dsimp only at H)
      generalize hr : LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite.readable_fd e = rd at H
      cases rd with
      | none =>
        try (dsimp only at H)
        vm_ret_only H
      | some rv =>
        try (dsimp only at H)
        by_cases h1 : LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite.readv_heap_iovecb iovcnt = true
        · rw [ite_eq_left h1] at H
          contradiction
        · rw [ite_eq_right h1] at H
          try (dsimp only at H)
          generalize hi : import_iovecs i.in_mem iov (LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite.iovcnt32 iovcnt) = im at H
          cases im with
          | ImpFault =>
            try (dsimp only at H)
            vm_ret_only_copyins H
          | ImpInval =>
            try (dsimp only at H)
            vm_ret_only_copyins H
          | ImpOk iovs0 =>
            try (dsimp only at H)
            first
              | (exact LinuxSem.Checks.Sys.Fs.ReadWrite.check_readv_imported_frame
                   i fd rv iovs0 _ m m' evs
                   (check_copyin_prefix_model _ _ _ m' evs H))
              | (contradiction))

set_option maxHeartbeats 1000000 in
/-- `sendto`'s frame.  Three declines, then the buffer's range verdict —
    which answers `check_ret_only -EFAULT` or hands the descriptor match
    through — and the socket half is `check_send_on_socket_frame`
    (in `Checks/Sys/Net/Socket.lean`), cited as a TERM. -/
theorem check_sendto_frame (i : SyscallInput) (fd buf count flags addrp : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sendto i fd buf count flags addrp eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Net.Socket.check_sendto at H
    try (dsimp only at H)
    by_cases h1 : (!(LinuxSem.LinuxProcessSem.Sys.Net.Socket.send_flags_modeled flags)) = true
    · rw [ite_eq_left h1] at H
      contradiction
    · rw [ite_eq_right h1] at H
      by_cases h2 : (!(w_is0 addrp)) = true
      · rw [ite_eq_left h2] at H
        contradiction
      · rw [ite_eq_right h2] at H
        by_cases h3 : (!(LinuxSem.LinuxProcessSem.Sys.Uaccess.modeled_rw_count count)) = true
        · rw [ite_eq_left h3] at H
          contradiction
        · rw [ite_eq_right h3] at H
          try (dsimp only at H)
          unfold LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero at H
          by_cases h4 : LinuxSem.LinuxProcessSem.access_okb buf (count.toNat : Int) = true
          · rw [ite_eq_left h4] at H
            try (dsimp only at H)
            generalize hq : fd_lookup (m_fds m) fd = q at H
            cases q with
            | none =>
              try (dsimp only at H)
              vm_ret_only H
            | some e =>
              cases e with
              | FdSocket sk =>
                try (dsimp only at H)
                first
                  | (exact LinuxSem.Checks.Sys.Net.Socket.check_send_on_socket_frame
                       [] (fun n => [(buf, n)]) fd sk count _ _ m m' evs H)
                  | (contradiction)
              | _ =>
                try (dsimp only at H)
                vm_ret_only H
          · rw [ite_eq_right h4] at H
            try (dsimp only at H)
            vm_ret_only H)

set_option maxHeartbeats 1000000 in
/-- `sendmsg`'s frame: the flag gate, the descriptor match, the 56-byte
    `msghdr` read, the six-field `read_u64` import (all six `generalize`d
    and `cases`d — a six-way simultaneous `match` on options has no
    `split`), the two count bands, `copy_iovecs_aux`'s three verdicts, the
    controllen/`rw_bytes_max` gates — and then the same
    `check_send_on_socket_frame` `sendto` uses. -/
theorem check_sendmsg_frame (i : SyscallInput) (fd msgp flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sendmsg i fd msgp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Net.Socket.check_sendmsg at H
    try (dsimp only at H)
    by_cases h1 : (!(LinuxSem.LinuxProcessSem.Sys.Net.Socket.send_flags_modeled flags)) = true
    · rw [ite_eq_left h1] at H
      contradiction
    · rw [ite_eq_right h1] at H
      try (dsimp only at H)
      generalize hq : fd_lookup (m_fds m) fd = q at H
      cases q with
      | none =>
        try (dsimp only at H)
        vm_ret_only H
      | some e =>
        cases e with
        | FdSocket sk =>
          try (dsimp only at H)
          generalize hm : read_bytes_map i.in_mem msgp (BitVec.ofInt 64 LinuxSem.LinuxProcessSem.Sys.Net.Socket.MSGHDR_SIZE) = rb at H
          cases rb with
          | none =>
            try (dsimp only at H)
            vm_ret_only H
          | some mh =>
            try (dsimp only at H)
            generalize h2 : read_u64 i.in_mem msgp = u2 at H
            generalize h3 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 8) = u3 at H
            generalize h4 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 16) = u4 at H
            generalize h5 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 24) = u5 at H
            generalize h6 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 32) = u6 at H
            generalize h7 : read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) = u7 at H
            cases u2 with
            | none => vm_ret_only_copyins_ds H
            | some name =>
              cases u3 with
              | none => vm_ret_only_copyins_ds H
              | some u3v =>
                cases u4 with
                | none => vm_ret_only_copyins_ds H
                | some iov =>
                  cases u5 with
                  | none => vm_ret_only_copyins_ds H
                  | some iovlen =>
                    cases u6 with
                    | none => vm_ret_only_copyins_ds H
                    | some u6v =>
                      cases u7 with
                      | none => vm_ret_only_copyins_ds H
                      | some ctllen =>
                        try (dsimp only at H)
                        by_cases hg1 : (!(w_is0 name)) = true
                        · rw [ite_eq_left hg1] at H
                          contradiction
                        · rw [ite_eq_right hg1] at H
                          by_cases hg2 : decide (LinuxSem.LinuxProcessSem.IOV_MAX < (iovlen.toNat : Int)) = true
                          · rw [ite_eq_left hg2] at H
                            vm_ret_only_copyins H
                          · rw [ite_eq_right hg2] at H
                            by_cases hg3 : decide (LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite.UIO_FASTIOV < (iovlen.toNat : Int)) = true
                            · rw [ite_eq_left hg3] at H
                              contradiction
                            · rw [ite_eq_right hg3] at H
                              try (dsimp only at H)
                              generalize hcv : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = cv at H
                              cases cv with
                              | ImpFault => vm_ret_only_copyins_ds H
                              | ImpInval => vm_ret_only_copyins_ds H
                              | ImpOk iovs0 =>
                                try (dsimp only at H)
                                by_cases hg4 : (!(w_is0 ctllen)) = true
                                · rw [ite_eq_left hg4] at H
                                  contradiction
                                · rw [ite_eq_right hg4] at H
                                  by_cases hg5 : (!(decide (iovs_total (cap_iovecs iovs0) ≤ LinuxSem.LinuxProcessSem.Sys.Uaccess.rw_bytes_max))) = true
                                  · rw [ite_eq_left hg5] at H
                                    contradiction
                                  · rw [ite_eq_right hg5] at H
                                    exact LinuxSem.Checks.Sys.Net.Socket.check_send_on_socket_frame
                                      _ _ _ _ _ _ _ _ _ _ H
        | _ =>
          try (dsimp only at H)
          vm_ret_only H)

/-- `getgroups`'s frame: four `Int` comparisons on the count and on the
    credential group list, each answered by a bare `check_ret_only`, and
    one decline.  Nothing writes. -/
theorem check_getgroups_frame (gidsetsize : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getgroups gidsetsize eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Groups.check_getgroups at H
    try (dsimp only at H)
    by_cases hneg : sint32 gidsetsize < 0
    · rw [ite_eq_left hneg] at H
      vm_ret_only H
    · rw [ite_eq_right hneg] at H
      try (dsimp only at H)
      by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
      · rw [ite_eq_left hmax] at H
        contradiction
      · rw [ite_eq_right hmax] at H
        by_cases hzero : sint32 gidsetsize = 0
        · rw [ite_eq_left hzero] at H
          vm_ret_only H
        · rw [ite_eq_right hzero] at H
          by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
          · rw [ite_eq_left hsmall] at H
            vm_ret_only H
          · rw [ite_eq_right hsmall] at H
            by_cases hng : ((m_creds m).cr_groups.length : Int) = 0
            · rw [ite_eq_left hng] at H
              vm_ret_only H
            · rw [ite_eq_right hng] at H
              contradiction)

open LinuxSem.LinuxProcessSem.Sys.Net.Socket in

/-- `setsockopt`'s frame: `sock_fd` answers the errno, the level gate
    answers `-ENOPROTOOPT`, and the rest declines.  No arm touches the
    ledger. -/
theorem check_setsockopt_frame (fd level optlen : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_setsockopt fd level optlen eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Net.Socket.check_setsockopt at H
    generalize hq : sock_fd m fd = q at H
    cases q with
    | inr e =>
      try (dsimp only at H)
      vm_ret_only H
    | inl sk =>
      try (dsimp only at H)
      by_cases h1 : int32_neg optlen = true
      · rw [ite_eq_left h1] at H
        vm_ret_only H
      · rw [ite_eq_right h1] at H
        by_cases h2 : (!(sock_level_known level)) = true
        · rw [ite_eq_left h2] at H
          vm_ret_only H
        · rw [ite_eq_right h2] at H
          contradiction)

open LinuxSem.LinuxProcessSem.Sys.Kernel.Signal in
/-- `sigaltstack`'s frame: the "already installed" decline, the `uoss`
    gate, then the three answers on a read `sigaltstack_at` — including
    the one that INSTALLS the stack, whose rebuild touches `m_proc`
    only. -/
theorem check_sigaltstack_frame (i : SyscallInput) (uss uoss : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sigaltstack i uss uoss eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Signal.check_sigaltstack at H
    try (dsimp only at H)
    by_cases h1 : m_sigaltstack_installed m = true
    · rw [ite_eq_left h1] at H
      contradiction
    · rw [ite_eq_right h1] at H
      by_cases h2 : (!(w_is0 uoss)) = true
      · rw [ite_eq_left h2] at H
        contradiction
      · rw [ite_eq_right h2] at H
        by_cases h3 : w_is0 uss = true
        · rw [ite_eq_left h3] at H
          vm_ret_only H
        · rw [ite_eq_right h3] at H
          try (dsimp only at H)
          generalize hg : sigaltstack_at i.in_mem uss = g at H
          cases g with
          | none =>
            try (dsimp only at H)
            vm_ret_only H
          | some bs =>
            try (dsimp only at H)
            by_cases h4 : (!(ss_mode_ok (ss_flags_of bs))) = true
            · rw [ite_eq_left h4] at H
              vm_ret_only H
            · rw [ite_eq_right h4] at H
              by_cases h5 : ss_disabling (ss_flags_of bs) = true
              · rw [ite_eq_left h5] at H
                vm_ret_only H
              · rw [ite_eq_right h5] at H
                by_cases h6 : (w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs)) = true
                · rw [ite_eq_left h6] at H
                  contradiction
                · rw [ite_eq_right h6] at H
                  by_cases h7 : ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ
                  · rw [ite_eq_left h7] at H
                    vm_ret_only H
                  · rw [ite_eq_right h7] at H
                    vm_ret_only H)


/- -------------------------------------------------------------------------
   TWO ARMS WHOSE ACCEPTING BRANCH ENDS IN AN `if` OVER A BITVECTOR GUARD,
   and the two one-line facts that close them.

   `clock_gettime` and `nanosleep` accept on

     if bv_eqb r 0 && bv_eqb a tp && realtime_ok_b bs then .CheckOk m [] …
     if bv_eqb r 0 then … else if bv_eqb r EINTR then … else …

   whose guard is a `Bool` computation on a SYMBOLIC word:
   `split`/`simp only [check_X]` cannot case it (that would have to REDUCE
   `BitVec.toInt`), and the `cases h : <guard>` route is what the
   rest of this file uses.  HERE THE `cases` ROUTE IS NOT ENOUGH, for a
   reason one layer below the tactic-level obstacles: casing a guard of this
   size with `by_cases h : <guard> = true` and then `rw [ite_eq_left h] at H`
   makes the proof term so deep that the KERNEL refuses it — "(kernel) deep
   recursion detected", with the tactic block itself reporting 0.04 s of
   elaboration (measured with `set_option profiler true`), i.e. the tactics
   are fine and the term they build is not.  Measured on
   `check_clock_gettime`: 0.35 s with one guard leaf replaced by `skip`,
   108 s and a kernel error with all three in place.  The culprit is the
   chain of `if`-rewrites INSIDE the enlarged hypothesis: each one builds a
   motive over the whole surviving checker body, and `maxRecDepth` does not
   reach the kernel's limit, so raising it is not a route.

   THE ROUTE THAT WORKS is to make the terminal `if` its own lemma, so the
   leaf is a LEMMA APPLICATION and the kernel never puts the `if` in a
   motive.  Inside the lemma the two branches are split with `split at H`,
   which is cheap there because the condition is a VARIABLE of type `Prop`
   (nothing to reduce) — the exact opposite of the situation in the arm.
   Two shapes cover both arms (and `write`'s channel arm): one `if`, and two
   nested ones.  Everything else in the arm is then the ordinary
   `simp only [m_vmmaps]` projection work.

   The effect shape is destructed FIRST and the walk run once per shape
   class (an empty write list and a nonempty one), because `clock_gettime`'s
   accepting pattern is `[(a, bs)]`: the one-element class is the only one
   whose `match` survives, and closing the other one first keeps the leaf
   lemma out of its goals. -/

/-- A `CheckOk`-accepting `if` hands back the model ITS `then`
    branch was built from, whatever the event list is; the `else` branch is
    `.CheckReject`, which cannot equal a `.CheckOk`.  See the note above for
    why this is a lemma rather than a `by_cases` at the call site. -/
theorem check_ok_if_model {p : Prop} [Decidable p] {k m' : Model}
    {evs0 evs : List event}
    (H : (if p then (.CheckOk k evs0 : check_result) else .CheckReject) = .CheckOk m' evs) :
    m' = k := by
  split at H
  · cases H
    rfl
  · cases H

/-- The two-`if` chain `clock_gettime`'s per-call arms and
    `nanosleep`'s no-remainder arm end in — both answers are `CheckOk`s, so
    the model is one of the two. -/
theorem check_ok_if2_model {p q : Prop} [Decidable p] [Decidable q]
    {k1 k2 m' : Model} {e1 e2 evs : List event}
    (H : (if p then (.CheckOk k1 e1 : check_result)
          else if q then .CheckOk k2 e2 else .CheckReject) = .CheckOk m' evs) :
    m' = k1 ∨ m' = k2 := by
  split at H
  · left
    cases H
    rfl
  · split at H
    · right
      cases H
      rfl
    · cases H

/-- `clock_gettime`'s frame: three clock classes, each a `match` on the
    same effect shapes, and the accepting branch of each is the `if`
    `check_ok_if_model` closes.  The monotonic class is the only one that
    rebuilds the model (`with_clock`), whose `m_vmmaps` projection is the
    old one, and the two per-call classes hand back `m` itself. -/
theorem check_clock_gettime_frame (i : SyscallInput) (clkid tp : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime i clkid tp eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws with
  | nil =>
    all_goals (
      unfold LinuxSem.Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime at H
      by_cases h1 : clockid_percall_b clkid = true
      · rw [ite_eq_left h1] at H
        generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
        cases rb with
        | none =>
          try (dsimp only at H)
          first
            | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
            | (cases check_ok_if2_model H with
               | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
               | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
            | (cases H)
        | some x =>
          try (dsimp only at H)
          first
            | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
            | (cases check_ok_if2_model H with
               | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
               | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
            | (cases H)
      · rw [ite_eq_right h1] at H
        by_cases h2 : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
        · rw [ite_eq_left h2] at H
          generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
          cases rb with
          | none =>
            try (dsimp only at H)
            first
              | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model H with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases H)
          | some x =>
            try (dsimp only at H)
            first
              | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model H with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases H)
        · rw [ite_eq_right h2] at H
          by_cases h3 : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
          · rw [ite_eq_left h3] at H
            cases H
          · rw [ite_eq_right h3] at H
            by_cases h4 : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
            · rw [ite_eq_left h4] at H
              cases H
            · rw [ite_eq_right h4] at H
              generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
              cases rb with
              | none =>
                try (dsimp only at H)
                first
                  | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases check_ok_if2_model H with
                     | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                     | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases H)
              | some x =>
                try (dsimp only at H)
                first
                  | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases check_ok_if2_model H with
                     | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                     | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases H)
    )
  | cons w tl =>
    cases tl <;> cases zs <;> cases us <;> cases cs <;> cases ci
    all_goals (
      unfold LinuxSem.Checks.Sys.Kernel.Time.PosixTimers.check_clock_gettime at H
      by_cases h1 : clockid_percall_b clkid = true
      · rw [ite_eq_left h1] at H
        generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
        cases rb with
        | none =>
          try (dsimp only at H)
          first
            | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
            | (cases check_ok_if2_model H with
               | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
               | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
            | (cases H)
        | some x =>
          try (dsimp only at H)
          first
            | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
            | (cases check_ok_if2_model H with
               | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
               | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
            | (cases H)
      · rw [ite_eq_right h1] at H
        by_cases h2 : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
        · rw [ite_eq_left h2] at H
          generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
          cases rb with
          | none =>
            try (dsimp only at H)
            first
              | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model H with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases H)
          | some x =>
            try (dsimp only at H)
            first
              | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model H with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases H)
        · rw [ite_eq_right h2] at H
          by_cases h3 : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
          · rw [ite_eq_left h3] at H
            cases H
          · rw [ite_eq_right h3] at H
            by_cases h4 : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
            · rw [ite_eq_left h4] at H
              cases H
            · rw [ite_eq_right h4] at H
              generalize hrb : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = rb at H
              cases rb with
              | none =>
                try (dsimp only at H)
                first
                  | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases check_ok_if2_model H with
                     | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                     | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases H)
              | some x =>
                try (dsimp only at H)
                first
                  | (rw [check_ok_if_model H] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases check_ok_if2_model H with
                     | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                     | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases H)
    )

/-- `nanosleep`'s frame.  Two declines and one copy-in ledger lead to a
    `check_copyins` over the effect `match`; the accepted shapes are the
    empty write list (the completed sleep, or -EINTR with a NULL `rmtp`) and
    the one-element one (the interrupted sleep with a remainder), and both
    hand back a `with_clock` rebuild or `m`, so `check_ok_if_model` /
    `check_ok_if2_model` close them.  The invalid-timespec verdict is the
    `check_ret_only_copyins` wrapper, inverted with its own `*_model`. -/
theorem check_nanosleep_frame (i : SyscallInput) (rqtp rmtp : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep i rqtp rmtp eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs
    all_goals (
      unfold LinuxSem.Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep at H
      generalize hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = rq at H
      cases rq with
      | none => cases H
      | some req =>
        try (dsimp only at H)
        by_cases hv : (!(timespec_valid_b req)) = true
        · rw [ite_eq_left hv] at H
          rw [check_ret_only_copyins_model [(rqtp, 16)] _ _ _ _ _ _ H]
        · rw [ite_eq_right hv] at H
          by_cases hw : w_is0 rmtp = true
          · rw [ite_eq_left hw] at H
            have Hci := check_copyins_model [(rqtp, 16)] _ _ _ _ H
            try (dsimp only at Hci)
            first
              | (rw [check_ok_if_model Hci] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model Hci with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases Hci)
          · rw [ite_eq_right hw] at H
            generalize hrm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) = rm at H
            cases rm with
            | none => cases H
            | some x =>
              have Hci := check_copyins_model [(rqtp, 16)] _ _ _ _ H
              try (dsimp only at Hci)
              first
                | (rw [check_ok_if_model Hci] <;> simp only [m_vmmaps] <;> rfl)
                | (cases check_ok_if2_model Hci with
                   | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                   | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                | (cases Hci)
    )
  | cons w tl =>
    cases tl <;> cases zs <;> cases us <;> cases cs
    all_goals (
      unfold LinuxSem.Checks.Sys.Kernel.Time.Hrtimer.check_nanosleep at H
      generalize hrq : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = rq at H
      cases rq with
      | none => cases H
      | some req =>
        try (dsimp only at H)
        by_cases hv : (!(timespec_valid_b req)) = true
        · rw [ite_eq_left hv] at H
          rw [check_ret_only_copyins_model [(rqtp, 16)] _ _ _ _ _ _ H]
        · rw [ite_eq_right hv] at H
          by_cases hw : w_is0 rmtp = true
          · rw [ite_eq_left hw] at H
            have Hci := check_copyins_model [(rqtp, 16)] _ _ _ _ H
            try (dsimp only at Hci)
            first
              | (rw [check_ok_if_model Hci] <;> simp only [m_vmmaps] <;> rfl)
              | (cases check_ok_if2_model Hci with
                 | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                 | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
              | (cases Hci)
          · rw [ite_eq_right hw] at H
            generalize hrm : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) = rm at H
            cases rm with
            | none => cases H
            | some x =>
              have Hci := check_copyins_model [(rqtp, 16)] _ _ _ _ H
              try (dsimp only at Hci)
              first
                | (rw [check_ok_if_model Hci] <;> simp only [m_vmmaps] <;> rfl)
                | (cases check_ok_if2_model Hci with
                   | inl hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl
                   | inr hh => rw [hh] <;> simp only [m_vmmaps] <;> rfl)
                | (cases Hci)
    )

/- -------------------------------------------------------------------------
   THE `socket` ARM, and the measured reason it did NOT need the
   `private abbrev` workaround the ledger expected.

   `check_socket`'s nine gates are spelled through the CANONICAL
   `Sys.Syscall.abi_low32` (`Checks/Sys/Net/Socket.lean` binds it with a
   `local notation`; it no longer declares a helper of its own).  The
   recorded obstacle says a `private` helper's terms cannot be written from
   another module.  THAT WAS NEVER TRUE FOR THE `abbrev` THIS ARM USED: a
   transparency check holds — the checker's alias was the public `def`'s body
   — so `by_cases h : <guard> = true` followed by
   `rw [ite_eq_left h] at H` unifies through it.  Measured here: every one
   of the twelve gates rewrites.  The `*_frame`-beside-the-helper route is
   still the right one for a private `DEF` (whose equation lemmas are
   unnameable) — it is just not what this arm needed.

   The abbrev below only makes the guard text readable; being an `abbrev` it
   is transparent for the same reason.  Nothing else in the arm is special:
   the six error answers are `check_ret_only` (inverted by its `*_model`),
   the five declines are `.CheckUnmodeled`, and the single accepting
   `SOCK_STREAM`/`IPPROTO_TCP` branch is `check_new_fd_result`, whose frame is
   the lemma above (`mk` is a `with_fds` rebuild, so the projection is the
   old one). -/

/-- The socket gate's 32-bit truncation, spelled out so the guards below are
    writable; the checker binds the same canonical `def` with a
    `local notation`, and this is the same function. -/
private abbrev socket_low32 (w : word) : word :=
  LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32 w

/-- An accepted `check_new_fd_result` hands back `mk fd` — the
    only model it builds — so it leaves `m_vmmaps` alone whenever `mk` does.
    `socket`'s `mk` is a `with_fds` rebuild; `openat` has its own copy of the
    lemma beside its own copy of the acceptor. -/
theorem check_new_fd_result_frame (es : List Int) (eff : SyscallEffect) (m m' : Model)
    (mk : word → Model) (evs : List event)
    (hkeep : ∀ fd, m_vmmaps (mk fd) = m_vmmaps m)
    (H : LinuxSem.Checks.Sys.Net.Socket.check_new_fd_result es eff m mk = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold LinuxSem.Checks.Sys.Net.Socket.check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs with
    | nil =>
      cases us with
      | nil =>
        cases cs with
        | nil =>
          cases ks with
          | nil =>
            try (dsimp only at H)
            by_cases he : errno_ret_in es ret = true
            · rw [ite_eq_left he] at H
              cases H
              rfl
            · rw [ite_eq_right he] at H
              try (dsimp only at H)
              generalize hf : fd_lookup (m_fds m) ret = q at H
              cases q with
              | some x =>
                try (dsimp only at H)
                cases H
              | none =>
                try (dsimp only at H)
                by_cases ha : bv_eqb ret (alloc_fd (m_fds m)) = true
                · rw [ite_eq_left ha] at H
                  cases H
                  exact hkeep ret
                · rw [ite_eq_right ha] at H
                  cases H
          | cons _ _ => try (dsimp only at H); cases H
        | cons _ _ => try (dsimp only at H); cases H
      | cons _ _ => try (dsimp only at H); cases H
    | cons _ _ => try (dsimp only at H); cases H
  | cons w tl => try (dsimp only at H); cases H

open LinuxSem.LinuxProcessSem.Sys.Net.Socket in

theorem check_socket_frame (domain type protocol : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Net.Socket.check_socket domain type protocol eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold LinuxSem.Checks.Sys.Net.Socket.check_socket at H
  try (dsimp only at H)
  by_cases h1 : (!(z_ldiff (z_ldiff (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = true
  · rw [ite_eq_left h1] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right h1] at H
    by_cases h2 : (!(z_land (z_ldiff (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) SOCK_NONBLOCK == 0)) = true
    · rw [ite_eq_left h2] at H
      cases H
    · rw [ite_eq_right h2] at H
      by_cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = true
      · rw [ite_eq_left h3] at H
        rw [check_ret_only_model _ _ _ _ _ _ H]
      · rw [ite_eq_right h3] at H
        by_cases h4 : decide (SOCK_MAX ≤ z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) = true
        · rw [ite_eq_left h4] at H
          rw [check_ret_only_model _ _ _ _ _ _ H]
        · rw [ite_eq_right h4] at H
          by_cases h5 : (!(sint32 domain == AF_INET)) = true
          · rw [ite_eq_left h5] at H
            cases H
          · rw [ite_eq_right h5] at H
            by_cases h6 : ((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_PACKET) = true
            · rw [ite_eq_left h6] at H
              cases H
            · rw [ite_eq_right h6] at H
              by_cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = true
              · rw [ite_eq_left h7] at H
                rw [check_ret_only_model _ _ _ _ _ _ H]
              · rw [ite_eq_right h7] at H
                by_cases h8 : ((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_STREAM) = true
                · rw [ite_eq_left h8] at H
                  by_cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = true
                  · rw [ite_eq_left h9] at H
                    cases H
                  · rw [ite_eq_right h9] at H
                    by_cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))) = true
                    · rw [ite_eq_left h10] at H
                      rw [check_ret_only_model _ _ _ _ _ _ H]
                    · rw [ite_eq_right h10] at H
                      exact check_new_fd_result_frame socket_errnos eff m m'
                        (fun fd => with_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) m) evs
                        (fun fd => by simp only [m_vmmaps_with_fds]) H
                · rw [ite_eq_right h8] at H
                  by_cases h11 : (((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_DGRAM) || (((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_RAW))) = true
                  · rw [ite_eq_left h11] at H
                    cases H
                  · rw [ite_eq_right h11] at H
                    by_cases h12 : (((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_SEQPACKET) || (((z_land (((socket_low32 type).toNat : Int)) SOCK_TYPE_MASK) == SOCK_DCCP))) = true
                    · rw [ite_eq_left h12] at H
                      cases H
                    · rw [ite_eq_right h12] at H
                      rw [check_ret_only_model _ _ _ _ _ _ H]


/- -------------------------------------------------------------------------
   `write`, and the two facts it needs.

   `check_write` dispatches on the descriptor FIRST (ten kinds, nested
   constructor patterns, so `generalize`/`cases` rather than `split`),
   and every arm but the channel one ends in a `check_ret_only`
   or a `check_ret_only_copyins` over a `with_fds`/`with_fs` rebuild — both
   inverted by their own `*_model` and closed by the projection identity.
   The channel arm's one acceptance is a nested `if` in the THEN branch
   (its events are the written prefix), which is what
   `check_ok_if_nest_model` is for; `check_access_ok_zero`'s `-EFAULT`
   short-circuit is its own one-line frame below. -/

/-- The mirror of `check_ok_if2_model` with the second `if` in
    the THEN branch — the shape `check_write`'s channel arm uses. -/
theorem check_ok_if_nest_model {p q : Prop} [Decidable p] [Decidable q]
    {k m' : Model} {e evs : List event}
    (H : (if p then (if q then (.CheckOk k e : check_result) else .CheckReject)
          else .CheckReject) = .CheckOk m' evs) :
    m' = k := by
  split at H
  · split at H
    · cases H
      rfl
    · cases H
  · cases H

theorem check_access_ok_zero_ret_only_frame (buf count : word) (r : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero buf count eff m
          (check_ret_only eff r m []) = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero at H
  by_cases hok : access_okb buf (count.toNat : Int) = true
  · rw [ite_eq_left hok] at H
    rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
  · rw [ite_eq_right hok] at H
    rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl

open LinuxSem.Checks.Sys.Uaccess in
open LinuxSem.LinuxProcessSem.Sys.Uaccess in
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite in
/-- `write`'s frame: ten descriptor kinds, and not one of them moves the
    ledger.  See the note above for the three closers. -/
theorem check_write_frame (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Fs.ReadWrite.check_write i fd buf count eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold LinuxSem.Checks.Sys.Fs.ReadWrite.check_write at H
  generalize hq : fd_lookup (m_fds m) fd = q at H
  cases q with
  | none =>
    try (dsimp only at H)
    rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
  | some e =>
    try (dsimp only at H)
    cases e with
    | FdChannel ch =>
      try (dsimp only at H)
      by_cases h1 : w_is0 ch = true
      · rw [ite_eq_left h1] at H
        rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
      · rw [ite_eq_right h1] at H
        by_cases h2 : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left h2] at H
          cases H
        · rw [ite_eq_right h2] at H
          by_cases h3 : w_is0 count = true
          · rw [ite_eq_left h3] at H
            exact check_access_ok_zero_ret_only_frame buf count (BitVec.ofInt 64 0) eff m m' evs H
          · rw [ite_eq_right h3] at H
            by_cases h4 : ((write_source i.in_mem buf count).length == 0) = true
            · rw [ite_eq_left h4] at H
              rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
            · rw [ite_eq_right h4] at H
              obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
              cases ws <;> cases zs <;> cases us <;> cases cs
              all_goals (
                try (dsimp only at H)
                first
                  | (rw [check_ok_if_nest_model H] <;> simp only [m_vmmaps] <;> rfl)
                  | (cases H))
    | FdFileW p off =>
      try (dsimp only at H)
      by_cases h1 : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left h1] at H
        cases H
      · rw [ite_eq_right h1] at H
        generalize hbs : write_source i.in_mem buf count = bs at H
        by_cases h2 : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left h2] at H
          rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
        · rw [ite_eq_right h2] at H
          by_cases h3 : w_is0 count = true
          · rw [ite_eq_left h3] at H
            try (dsimp only at H)
            unfold LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero at H
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H
              try (dsimp only at H)
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
              cases lk with
              | none => cases H
              | some data =>
                try (dsimp only at H)
                by_cases hg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hg] at H
                  cases H
                · rw [ite_eq_right hg] at H
                  rw [ite_eq_left h3] at H
                  rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
            · rw [ite_eq_right hok] at H
              rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
          · rw [ite_eq_right h3] at H
            try (dsimp only at H)
            generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
            cases lk with
            | none => cases H
            | some data =>
              try (dsimp only at H)
              by_cases hg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hg] at H
                cases H
              · rw [ite_eq_right hg] at H
                rw [ite_eq_right h3] at H
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
    | FdFileRW p off =>
      try (dsimp only at H)
      by_cases h1 : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left h1] at H
        cases H
      · rw [ite_eq_right h1] at H
        generalize hbs : write_source i.in_mem buf count = bs at H
        by_cases h2 : (!(w_is0 count) && (bs.length == 0)) = true
        · rw [ite_eq_left h2] at H
          rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
        · rw [ite_eq_right h2] at H
          by_cases h3 : w_is0 count = true
          · rw [ite_eq_left h3] at H
            try (dsimp only at H)
            unfold LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero at H
            by_cases hok : access_okb buf (count.toNat : Int) = true
            · rw [ite_eq_left hok] at H
              try (dsimp only at H)
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
              cases lk with
              | none => cases H
              | some data =>
                try (dsimp only at H)
                by_cases hg : (!(modeled_file_gap data off bs)) = true
                · rw [ite_eq_left hg] at H
                  cases H
                · rw [ite_eq_right hg] at H
                  rw [ite_eq_left h3] at H
                  rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
            · rw [ite_eq_right hok] at H
              rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
          · rw [ite_eq_right h3] at H
            try (dsimp only at H)
            generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
            cases lk with
            | none => cases H
            | some data =>
              try (dsimp only at H)
              by_cases hg : (!(modeled_file_gap data off bs)) = true
              · rw [ite_eq_left hg] at H
                cases H
              · rw [ite_eq_right hg] at H
                rw [ite_eq_right h3] at H
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
    | FdFileA p off =>
      try (dsimp only at H)
      by_cases h1 : (!(modeled_rw_range buf count)) = true
      · rw [ite_eq_left h1] at H
        cases H
      · rw [ite_eq_right h1] at H
        by_cases h2 : (!(access_okb buf (count.toNat : Int))) = true
        · rw [ite_eq_left h2] at H
          rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
        · rw [ite_eq_right h2] at H
          by_cases h3 : rw_pos_einvalb off (count.toNat : Int) = true
          · rw [ite_eq_left h3] at H
            rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
          · rw [ite_eq_right h3] at H
            generalize hbs : write_source i.in_mem buf count = bs at H
            by_cases h4 : (!(w_is0 count) && (bs.length == 0)) = true
            · rw [ite_eq_left h4] at H
              rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
            · rw [ite_eq_right h4] at H
              by_cases h5 : w_is0 count = true
              · rw [ite_eq_left h5] at H
                try (dsimp only at H)
                unfold LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero at H
                by_cases hok : access_okb buf (count.toNat : Int) = true
                · rw [ite_eq_left hok] at H
                  try (dsimp only at H)
                  generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
                  cases lk with
                  | none => cases H
                  | some data =>
                    try (dsimp only at H)
                    rw [ite_eq_left h5] at H
                    rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
                · rw [ite_eq_right hok] at H
                  rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
              · rw [ite_eq_right h5] at H
                try (dsimp only at H)
                generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
                cases lk with
                | none => cases H
                | some data =>
                  try (dsimp only at H)
                  rw [ite_eq_right h5] at H
                  rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
    | FdDevNull _ wr =>
      try (dsimp only at H)
      by_cases h1 : (!wr) = true
      · rw [ite_eq_left h1] at H
        rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
      · rw [ite_eq_right h1] at H
        by_cases h2 : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left h2] at H
          cases H
        · rw [ite_eq_right h2] at H
          exact check_access_ok_zero_ret_only_frame buf count (BitVec.ofInt 64 (rw_count_clamp count)) eff m m' evs H
    | FdPipe id w =>
      try (dsimp only at H)
      by_cases h1 : (!w) = true
      · rw [ite_eq_left h1] at H
        rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
      · rw [ite_eq_right h1] at H
        by_cases h2 : (!(modeled_rw_range buf count)) = true
        · rw [ite_eq_left h2] at H
          cases H
        · rw [ite_eq_right h2] at H
          by_cases h3 : w_is0 count = true
          · rw [ite_eq_left h3] at H
            exact check_access_ok_zero_ret_only_frame buf count (BitVec.ofInt 64 0) eff m m' evs H
          · rw [ite_eq_right h3] at H
            by_cases h4 : (!(pipe_end_live (m_fds m) id false)) = true
            · rw [ite_eq_left h4] at H
              cases H
            · rw [ite_eq_right h4] at H
              try (dsimp only at H)
              generalize hp : pipe_lookup (m_pipes m) id = st at H
              cases st with
              | none => cases H
              | some st =>
                try (dsimp only at H)
                by_cases h5 : (!(pipe_write_room st (count.toNat : Int))) = true
                · rw [ite_eq_left h5] at H
                  cases H
                · rw [ite_eq_right h5] at H
                  generalize hbs : write_source i.in_mem buf count = bs at H
                  by_cases h6 : (!(bs.length == word_to_nat count)) = true
                  · rw [ite_eq_left h6] at H
                    cases H
                  · rw [ite_eq_right h6] at H
                    rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl
    | FdSocket _ =>
      try (dsimp only at H)
      cases H
    | _ =>
      try (dsimp only at H)
      rw [check_ret_only_model _ _ _ _ _ _ H] <;> simp only [m_vmmaps] <;> rfl


/- -------------------------------------------------------------------------
   `openat`, which is a TREE and not a chain.

   `check_openat` is `check_copyins_after reads` over `check_openat_body`,
   and the body is a `read_cstr` verdict followed by
   `check_openat_resolved`, whose flag chain fans out into eight arms
   (`read`, `create`, `excl`, `dir`, `append`, `rdwr`, `rdwr_excl`, and the
   pathname classes of `check_openat_sep` before them).  The walk is one
   lemma per flag arm rather than a single `check_openat_frame`, because
   the nest has to be written out.

   THE OBSTACLE is that `split at H` on this
   nest is unproductive: it generalises `check_openat_body`'s `read_cstr`
   match and leaves the `x✝ : (match …) = .CheckUnmodeled → False` goals
   the loop cannot close.  It is not `by_cases`-hostile though: every guard
   here is a plain `Bool` test on `flags`/`pathp`/the fd, so a written-out
   `cases` walk closes all of it — 0.36 s for the whole family, which is
   why the family is factored into one lemma per arm instead of one 200-line
   `all_goals` block.  Each leaf is a `check_ret_only`/`check_ret_only_copyins`
   (its own `*_model` inversion) or a `check_open_result`, whose one frame
   `check_open_result_frame` is stated FIRST (the `private` one next door is
   about `Checks.Sys.Fs.Open.check_open_result`, a different definition, and
   is not nameable anyway).  The two `private` openers —
   `check_open_devnull`, `check_open_urandom` — are cited through the PUBLIC
   frames `Checks/Sys/Fs/Open.lean` already carries for them. -/

open LinuxSem.LinuxProcessSem.Sys.Fs.Open

theorem check_open_result_frame (eff : SyscallEffect) (m m' : Model) (mk : word → Model) (evs : List event)
    (H : check_open_result eff m mk = .CheckOk m' evs)
    (hkeep : ∀ fd, m_vmmaps (mk fd) = m_vmmaps m) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_open_result LinuxSem.Checks.Sys.Fs.Open.check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs with
    | nil =>
      cases us with
      | nil =>
        cases cs with
        | nil =>
          cases ks with
          | nil =>
            try (dsimp only at H)
            by_cases he : errno_ret_in openat_errnos ret = true
            · rw [ite_eq_left he] at H
              cases H
              rfl
            · rw [ite_eq_right he] at H
              try (dsimp only at H)
              generalize hf : fd_lookup (m_fds m) ret = q at H
              cases q with
              | some x =>
                try (dsimp only at H)
                cases H
              | none =>
                try (dsimp only at H)
                by_cases ha : bv_eqb ret (alloc_fd (m_fds m)) = true
                · rw [ite_eq_left ha] at H
                  cases H
                  exact hkeep ret
                · rw [ite_eq_right ha] at H
                  cases H
          | cons _ _ => try (dsimp only at H); cases H
        | cons _ _ => try (dsimp only at H); cases H
      | cons _ _ => try (dsimp only at H); cases H
    | cons _ _ => try (dsimp only at H); cases H
  | cons w tl => try (dsimp only at H); cases H

theorem check_openat_read_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_read p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_read at H
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)
  · rw [ite_eq_right hd] at H
    try (dsimp only at H)
    generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
    cases lk with
    | none =>
      try (dsimp only at H)
      rw [check_ret_only_model _ _ _ _ _ _ H]
    | some x =>
      try (dsimp only at H)
      exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_create_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_create p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_create at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right hd] at H
    unfold check_create_wronly at H
    exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_append_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_append p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_append at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right hd] at H
    unfold check_open_append at H
    exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_excl_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_excl p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_excl at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right hd] at H
    try (dsimp only at H)
    generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some x =>
      try (dsimp only at H)
      rw [check_ret_only_model _ _ _ _ _ _ H]
    | none =>
      try (dsimp only at H)
      unfold check_create_wronly at H
      exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_dir_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_dir p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_dir at H
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)
  · rw [ite_eq_right hd] at H
    by_cases hmax : decide (NAME_MAX < p.length) = true
    · rw [ite_eq_left hmax] at H
      cases H
    · rw [ite_eq_right hmax] at H
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        cases H
      · rw [ite_eq_right hun] at H
        try (dsimp only at H)
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
        cases lk with
        | none =>
          try (dsimp only at H)
          rw [check_ret_only_model _ _ _ _ _ _ H]
        | some x =>
          try (dsimp only at H)
          rw [check_ret_only_model _ _ _ _ _ _ H]

theorem check_openat_rdwr_frame (creat trunc : Bool) (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_rdwr creat trunc p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_rdwr at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right hd] at H
    try (dsimp only at H)
    generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
    cases lk with
    | none =>
      try (dsimp only at H)
      by_cases hc : creat = true
      · rw [ite_eq_left hc] at H
        unfold check_open_rdwr at H
        exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)
      · rw [ite_eq_right hc] at H
        rw [check_ret_only_model _ _ _ _ _ _ H]
    | some x =>
      try (dsimp only at H)
      unfold check_open_rdwr at H
      exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_rdwr_excl_frame (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_rdwr_excl p eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_rdwr_excl at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  · rw [ite_eq_right hd] at H
    try (dsimp only at H)
    generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some x =>
      try (dsimp only at H)
      rw [check_ret_only_model _ _ _ _ _ _ H]
    | none =>
      try (dsimp only at H)
      unfold check_open_rdwr at H
      exact check_open_result_frame eff m m' _ evs H (fun fd => rfl)

theorem check_openat_localtime_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_localtime flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_localtime at H
  generalize hfs : Fs.fs_lookup (m_fs m) localtime_path = lk at H
  cases lk with
  | some x => try (dsimp only at H); cases H
  | none =>
    try (dsimp only at H)
    by_cases hun : fs_under (m_fs m) localtime_path = true
    · rw [ite_eq_left hun] at H
      cases H
    · rw [ite_eq_right hun] at H
      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
      · rw [ite_eq_left hcr] at H
        cases H
      · rw [ite_eq_right hcr] at H
        rw [check_ret_only_model _ _ _ _ _ _ H]

theorem check_openat_devnull_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_devnull flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_devnull at H
  generalize hfs : Fs.fs_lookup (m_fs m) devnull_path = lk at H
  cases lk with
  | some x => try (dsimp only at H); cases H
  | none =>
    try (dsimp only at H)
    by_cases hun : fs_under (m_fs m) devnull_path = true
    · rw [ite_eq_left hun] at H
      cases H
    · rw [ite_eq_right hun] at H
      try (dsimp only at H)
      by_cases h0 : (z_ldiff (flags.toNat : Int) open_ignored_flags == 0) = true
      · rw [ite_eq_left h0] at H
        exact check_open_devnull_frame true false eff m m' evs H
      · rw [ite_eq_right h0] at H
        by_cases h1 : (z_ldiff (flags.toNat : Int) open_ignored_flags == wr_create_flags) = true
        · rw [ite_eq_left h1] at H
          exact check_open_devnull_frame false true eff m m' evs H
        · rw [ite_eq_right h1] at H
          by_cases h2 : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
          · rw [ite_eq_left h2] at H
            rw [check_ret_only_model _ _ _ _ _ _ H]
          · rw [ite_eq_right h2] at H
            by_cases h3 : (z_ldiff (flags.toNat : Int) open_ignored_flags == O_DIRECTORY) = true
            · rw [ite_eq_left h3] at H
              rw [check_ret_only_model _ _ _ _ _ _ H]
            · rw [ite_eq_right h3] at H
              by_cases h4 : (z_ldiff (flags.toNat : Int) open_ignored_flags == append_create_flags) = true
              · rw [ite_eq_left h4] at H
                exact check_open_devnull_frame false true eff m m' evs H
              · rw [ite_eq_right h4] at H
                by_cases h5 : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left h5] at H
                  exact check_open_devnull_frame true true eff m m' evs H
                · rw [ite_eq_right h5] at H
                  by_cases h6 : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                  · rw [ite_eq_left h6] at H
                    rw [check_ret_only_model _ _ _ _ _ _ H]
                  · rw [ite_eq_right h6] at H
                    cases H

theorem check_openat_urandom_frame (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_urandom flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_urandom at H
  generalize hfs : Fs.fs_lookup (m_fs m) urandom_path = lk at H
  cases lk with
  | some x => try (dsimp only at H); cases H
  | none =>
    try (dsimp only at H)
    by_cases hun : fs_under (m_fs m) urandom_path = true
    · rw [ite_eq_left hun] at H
      cases H
    · rw [ite_eq_right hun] at H
      try (dsimp only at H)
      by_cases h0 : (z_ldiff (flags.toNat : Int) open_ignored_flags == 0) = true
      · rw [ite_eq_left h0] at H
        exact check_open_urandom_frame eff m m' evs H
      · rw [ite_eq_right h0] at H
        by_cases h2 : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left h2] at H
          rw [check_ret_only_model _ _ _ _ _ _ H]
        · rw [ite_eq_right h2] at H
          by_cases h3 : (z_ldiff (flags.toNat : Int) open_ignored_flags == O_DIRECTORY) = true
          · rw [ite_eq_left h3] at H
            rw [check_ret_only_model _ _ _ _ _ _ H]
          · rw [ite_eq_right h3] at H
            by_cases h6 : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
            · rw [ite_eq_left h6] at H
              rw [check_ret_only_model _ _ _ _ _ _ H]
            · rw [ite_eq_right h6] at H
              cases H

theorem check_openat_tmp_frame (n p : Fs.path) (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_tmp n p flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_tmp at H
  by_cases hmax : decide (NAME_MAX < n.length) = true
  · rw [ite_eq_left hmax] at H
    cases H
  · rw [ite_eq_right hmax] at H
    try (dsimp only at H)
    by_cases h0 : (z_ldiff (flags.toNat : Int) open_ignored_flags == 0) = true
    · rw [ite_eq_left h0] at H
      try (dsimp only at H)
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        cases H
      · rw [ite_eq_right hun] at H
        try (dsimp only at H)
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at H
        cases lk with
        | none => try (dsimp only at H); cases H
        | some x =>
          try (dsimp only at H)
          exact check_openat_read_frame p eff m m' evs H
    · rw [ite_eq_right h0] at H
      by_cases h1 : (z_ldiff (flags.toNat : Int) open_ignored_flags == wr_create_flags) = true
      · rw [ite_eq_left h1] at H
        exact check_openat_create_frame p eff m m' evs H
      · rw [ite_eq_right h1] at H
        cases H

theorem check_openat_sep_frame (p : Fs.path) (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_sep p flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_sep at H
  by_cases h0 : Fs.path_eqb p localtime_path = true
  · rw [ite_eq_left h0] at H
    exact check_openat_localtime_frame flags eff m m' evs H
  · rw [ite_eq_right h0] at H
    by_cases h1 : Fs.path_eqb p devnull_path = true
    · rw [ite_eq_left h1] at H
      exact check_openat_devnull_frame flags eff m m' evs H
    · rw [ite_eq_right h1] at H
      by_cases h2 : Fs.path_eqb p urandom_path = true
      · rw [ite_eq_left h2] at H
        exact check_openat_urandom_frame flags eff m m' evs H
      · rw [ite_eq_right h2] at H
        generalize htn : tmp_name p = tn at H
        cases tn with
        | none => try (dsimp only at H); cases H
        | some n =>
          try (dsimp only at H)
          exact check_openat_tmp_frame n p flags eff m m' evs H

theorem check_openat_resolved_frame (p : Fs.path) (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_resolved p flags eff m = .CheckOk m' evs) : m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_resolved at H
  by_cases hs : path_has_slash p = true
  · rw [ite_eq_left hs] at H
    exact check_openat_sep_frame p flags eff m m' evs H
  · rw [ite_eq_right hs] at H
    try (dsimp only at H)
    by_cases h0 : (z_ldiff (flags.toNat : Int) open_ignored_flags == 0) = true
    · rw [ite_eq_left h0] at H
      exact check_openat_read_frame p eff m m' evs H
    · rw [ite_eq_right h0] at H
      by_cases h1 : (z_ldiff (flags.toNat : Int) open_ignored_flags == wr_create_flags) = true
      · rw [ite_eq_left h1] at H
        exact check_openat_create_frame p eff m m' evs H
      · rw [ite_eq_right h1] at H
        by_cases h2 : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left h2] at H
          exact check_openat_excl_frame p eff m m' evs H
        · rw [ite_eq_right h2] at H
          by_cases h3 : (z_ldiff (flags.toNat : Int) open_ignored_flags == O_DIRECTORY) = true
          · rw [ite_eq_left h3] at H
            exact check_openat_dir_frame p eff m m' evs H
          · rw [ite_eq_right h3] at H
            by_cases h4 : (z_ldiff (flags.toNat : Int) open_ignored_flags == append_create_flags) = true
            · rw [ite_eq_left h4] at H
              exact check_openat_append_frame p eff m m' evs H
            · rw [ite_eq_right h4] at H
              by_cases h5 : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
              · rw [ite_eq_left h5] at H
                exact check_openat_rdwr_frame
                  (flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT)
                  (flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_TRUNC) p eff m m' evs H
              · rw [ite_eq_right h5] at H
                by_cases h6 : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left h6] at H
                  exact check_openat_rdwr_excl_frame p eff m m' evs H
                · rw [ite_eq_right h6] at H
                  cases H

theorem check_openat_body_frame (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_body i dirfd pathp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_openat_body at H
  generalize hc : read_cstr i.in_mem pathp = c at H
  cases c with
  | CstrTooLong =>
    try (dsimp only at H)
    rw [check_ret_only_model _ _ _ _ _ _ H]
  | CstrFault =>
    try (dsimp only at H)
    rw [check_ret_only_model _ _ _ _ _ _ H]
  | CstrOk p =>
    try (dsimp only at H)
    by_cases hp : Fs.path_eqb p [] = true
    · rw [ite_eq_left hp] at H
      rw [check_ret_only_model _ _ _ _ _ _ H]
    · rw [ite_eq_right hp] at H
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        cases H
      · rw [ite_eq_right hd] at H
        exact check_openat_resolved_frame p flags eff m m' evs H

theorem check_openat_frame (i : SyscallInput) (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Fs.Open.check_openat i dirfd pathp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold LinuxSem.Checks.Sys.Fs.Open.check_openat at H
  by_cases hf : (!(modeled_open_flags flags)) = true
  · rw [ite_eq_left hf] at H
    cases H
  · rw [ite_eq_right hf] at H
    have Hb := check_copyins_after_model [(pathp, cstr_access_len_aux i.in_mem pathp path_max)] _ _ _ _ H
    exact check_openat_body_frame i dirfd pathp flags (clear_copyins eff) m m' evs Hb


/- -------------------------------------------------------------------------
   THE LAST TWO FRAMES: `bind` and `connect`.

   Both closed every goal at the tactic level and then died in the KERNEL
   with "(kernel) deep recursion detected".  THE MEASURED CAUSE is the
   `rw [ite_eq_left h] at H` step, not the size of the checker body: `ite_eq_left` is
   an equation whose STATEMENT embeds both branches of the `if`, so one such
   rewrite copies the surviving tail of the body into the proof term, and
   chained once per guard the term's DEPTH (not merely its size) outgrows
   the kernel's own recursion budget — which `set_option maxRecDepth` does
   not reach.

   `bind` therefore uses the shape `check_bind_sound_ok` already uses in
   `Checks/Sys/Net/Socket.lean`: `generalize` the `addrlen` truncation once,
   then `by_cases h : <guard> = true` plus `simp only [h, ite_true] at H`
   instead of `rw [ite_eq_left h] at H`.  `simp` rewrites the guard to `True` in
   the CONDITION (a one-hole motive over the guard, not over the `if`) and
   then reduces the `if` by iota, so no sub-term ever embeds the tail.  One
   `by_cases`/`simp only` pair per guard, exactly as the soundness proof
   walks the same body.

   NOTE on `check_errno_or_success`, the one helper those arms end in that
   had no `*_model` inversion yet: its success branch is either the model it
   was given (`errno_ret_in`) or the `with_fds` rebuild, so the inversion
   below is a disjunction and each side is closed by the projection.

   `connect` cannot even take that route: its body is the widest in this
   module (10 `FdEntry` x 5 `SockState` specializations) and EVERY
   hypothesis-level transformation of the unfolded body reproduces the
   kernel error on its own — measured individually: `simp only [] at H`
   (zeta of the two `let`s, `al` and `copied`), `generalize` of the
   `addrlen` truncation, and the `cases` over the `fd_lookup` dispatch each
   fail alone.  So `connect` is proved the way `Connect.lean` proves its own
   four agreement lemmas: the checker STAYS FOLDED in `H` (so the
   hypothesis is the one-line application `check_connect … = .CheckOk …`)
   and each leaf opens it with a pre-proved ARM EQUATION, whose left-hand
   side is that same application — a one-hole motive again, so nothing
   embeds the body.  The 11 equations are the public `connect_chk_*` of
   `Checks/Sys/Net/Socket/Connect.lean`, stated once there, so this module
   cites them directly, at the same statements and with the same
   `unfold check_connect` / `simp only […]` proofs.  They are the frozen
   checker's equation lemmas; the frame below is their dispatcher.
   ------------------------------------------------------------------------- -/

/-- `check_errno_or_success` hands back the model it was GIVEN
    (the errno arm) or the `with_fds` rebuild it builds on success — hence a
    disjunction, unlike the single-model `check_ret_only_model` /
    `check_ret_only_copyins_model` inversions.

    It is the acceptor `bind`'s fresh-socket arm ends in.  `listen` ends in
    it too, but `listen`'s frame is a one-line `vm_frame` that can afford to
    UNFOLD the acceptor in the hypothesis; `bind`'s arm is under six guards
    and a copy-in ledger, so it is inverted here instead. -/
theorem check_errno_or_success_model (es : List Int) (fds : List (word × FdEntry))
    (r : word) (eff : SyscallEffect) (mm m' : Model) (evs : List event)
    (H : check_errno_or_success es fds r eff mm = .CheckOk m' evs) :
    m' = mm ∨ m' = with_fds fds mm := by
  unfold check_errno_or_success at H
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  · try dsimp only at H
    by_cases he : errno_ret_in es ret = true
    · rw [ite_eq_left he] at H
      cases H
      exact Or.inl rfl
    · rw [ite_eq_right he] at H
      by_cases hb : bv_eqb ret r = true
      · rw [ite_eq_left hb] at H
        cases H
        exact Or.inr rfl
      · rw [ite_eq_right hb] at H
        cases H
  all_goals (try (dsimp only at H); cases H)

open LinuxSem.LinuxProcessSem.Sys.Net.Socket in

/-- `bind`'s frame.  The guard walk is `check_bind_sound_ok`'s, with
    `simp only [h, ite_true]` doing the `if`-reduction (see the block note
    for why `rw [ite_eq_left]` must not be used here); `bind`'s socket arm never
    moves the ledger — the three -EINVALs and the -EFAULT return before or
    without the copy, and the accepting arm only rebuilds `m_fds`. -/
theorem check_bind_frame (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_bind i fd addrp addrlen eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_bind at H
  generalize hal : sint32 addrlen = av at H
  simp only [] at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H
  cases e with
  | none =>
      simp only [] at H
      rw [check_ret_only_model _ _ _ _ _ _ H]
  | some e =>
    cases e with
    | FdSocket sk =>
      simp only [] at H
      by_cases hp : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true
      · simp only [hp, ite_true] at H
        rw [check_ret_only_model _ _ _ _ _ _ H]
      · simp only [hp, Bool.false_eq_true, ite_false] at H
        by_cases hz : (av == 0) = true
        · simp only [hz, ite_true] at H
          rw [check_ret_only_model _ _ _ _ _ _ H]
        · simp only [hz, Bool.false_eq_true, ite_false] at H
          cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) with
          | none =>
              simp only [hrb] at H
              rw [check_ret_only_model _ _ _ _ _ _ H]
          | some bs =>
              simp only [hrb] at H
              by_cases hs : decide (av < SOCKADDR_IN_SIZE) = true
              · simp only [hs, ite_true] at H
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
              · simp only [hs, Bool.false_eq_true, ite_false] at H
                by_cases hfam : (!(sa_family_of bs == AF_INET
                      || (sa_family_of bs == AF_UNSPEC
                          && sin_addr_of bs == INADDR_ANY))) = true
                · simp only [hfam, ite_true] at H
                  rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                · simp only [hfam, Bool.false_eq_true, ite_false] at H
                  by_cases ha : (!(sin_addr_of bs == INADDR_ANY)) = true
                  · simp only [ha, ite_true] at H
                    cases H
                  · simp only [ha, Bool.false_eq_true, ite_false] at H
                    by_cases hpo : (!(sin_port_of bs == 0)) = true
                    · simp only [hpo, ite_true] at H
                      cases H
                    · simp only [hpo, Bool.false_eq_true, ite_false] at H
                      cases sk with
                      | SkFresh =>
                          simp only [check_copyins] at H
                          by_cases hck : access_ranges_eqb eff.eff_copyins
                              [(addrp, av.toNat)] = true
                          · simp only [hck, ite_true] at H
                            rcases check_errno_or_success_model _ _ _ _ _ _ _ H with h | h
                            · rw [h]
                            · rw [h]
                              simp only [m_vmmaps_with_fds]
                          · simp only [hck, Bool.false_eq_true, ite_false] at H
                            cases H
                      | SkBound =>
                          rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                      | SkListening =>
                          rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                      | SkConnected peer chan rx =>
                          cases hrx : rx 0 with
                          | cons b =>
                              simp only [hrx] at H
                              rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                          | fin =>
                              simp only [hrx] at H
                              rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                          | rst =>
                              simp only [hrx] at H
                              cases H
                          | timedOut =>
                              simp only [hrx] at H
                              cases H
                      | SkReset peer chan =>
                          cases H
    | _ =>
        simp only [] at H
        rw [check_ret_only_model _ _ _ _ _ _ H]

/- -------------------------------------------------------------------------
   `connect`'s frozen-checker arm equations.

   The `connect_chk_*` equations live once, in
   `Checks/Sys/Net/Socket/Connect.lean`; this module cites them directly.
   `av` is opaque on purpose:
   the dispatcher instantiates it with `sint32 addrlen` and `hal` with
   `rfl`, so no `decide`-bearing `Int` term is ever forced to normalise
   inside the kernel.
   ------------------------------------------------------------------------- -/

open LinuxSem.LinuxProcessSem.Sys.Net.Socket in

/-- `connect`'s frame: the dispatcher over the frozen checker, one
    `connect_chk_*` equation per leaf and the `*_model` inversions
    for the three closers.  Every `cases` here is on a guard term that
    occurs in NEITHER the hypothesis nor the goal (the checker stays
    folded), so no motive over the body is ever built — see the block note
    for the measurements that force this shape.  The arm order is not
    `bind`'s: the copy precedes the descriptor dispatch, which is why
    -ENOTSOCK carries a ledger here and -EBADF does not. -/
theorem check_connect_frame (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_connect i fd addrp addrlen eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [connect_chk_ebadf i fd addrp addrlen eff m hfd] at H
    rw [check_ret_only_model _ _ _ _ _ _ H]
  | some e =>
    cases hg : (decide (sint32 addrlen < 0) || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) with
    | false =>
      cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) with
      | none =>
        rw [connect_chk_efault i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg hrb]
          at H
        rw [check_ret_only_model _ _ _ _ _ _ H]
      | some bs =>
        cases e with
        | FdSocket sk =>
          cases hs : decide (sint32 addrlen < SA_FAMILY_SIZE) with
          | false =>
            cases hfam : (sa_family_of bs == AF_UNSPEC) with
            | false =>
              cases sk with
              | SkFresh =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf] at H
                    cases H
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf] at H
                    rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs
                    (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi] at H
                  rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
              | SkBound =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf] at H
                    cases H
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf] at H
                    rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs
                    (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi] at H
                  rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
              | _ =>
                rw [connect_chk_eisconn i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                  hfd hg hrb hs hfam (by intro h; cases h) (by intro h; cases h)] at H
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
            | true =>
              cases sk with
              | SkFresh =>
                rw [connect_chk_unspec_fresh i fd addrp addrlen eff m bs (sint32 addrlen)
                  rfl hfd hg hrb hs hfam] at H
                rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
              | _ =>
                rw [connect_chk_unspec_other i fd addrp addrlen eff m _ bs (sint32 addrlen)
                  rfl hfd hg hrb hs hfam (by intro h; cases h)] at H
                cases H
          | true =>
            rw [connect_chk_family i fd addrp addrlen eff m sk bs (sint32 addrlen) rfl hfd
              hg hrb hs] at H
            rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
        | _ =>
          rw [connect_chk_enotsock i fd addrp addrlen eff m _ (by rintro s h; cases h)
            (sint32 addrlen) rfl hfd hg bs hrb] at H
          rw [check_ret_only_copyins_model _ _ _ _ _ _ _ H]
    | true =>
      rw [connect_chk_guard i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg] at H
      rw [check_ret_only_model _ _ _ _ _ _ H]



end LinuxSem.Checks.VmMapsDisjoint












