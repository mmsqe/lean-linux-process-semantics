/-
  * LinuxProcessSem.Sys.SyscallTable — the modeled syscall surface, one
    line each.

  This file answers to Linux `arch/riscv/kernel/syscall_table.c`, which is
  where the kernel keeps `sys_call_table` — the array a syscall number
  indexes.

  TRUST BOUNDARY: this file is part of the trusted specification.

  This list IS the modeled surface: `Specs.syscall_spec` dispatches over
  it and `Specs.modeled_sysnos` is read off it, so the two cannot disagree.

  SORTED BY SYSCALL NUMBER, one arm per line, `[]` on its own.  An arm
  reads its own arguments out of the `SyscallInput`: the same thing
  `arg 0`, `arg 1` … do, but doing it directly lets one lookup serve arms
  of every arity.
-/
import LinuxSem.LinuxProcessSem.Sys.Dispatch
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

-- Fs
import LinuxSem.LinuxProcessSem.Sys.Fs.DPath
import LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
import LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll
import LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl
import LinuxSem.LinuxProcessSem.Sys.Fs.File
import LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
import LinuxSem.LinuxProcessSem.Sys.Fs.Locks
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei
import LinuxSem.LinuxProcessSem.Sys.Fs.Open
import LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
import LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
import LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
import LinuxSem.LinuxProcessSem.Sys.Fs.Select
import LinuxSem.LinuxProcessSem.Sys.Fs.Stat
import LinuxSem.LinuxProcessSem.Sys.Fs.Sync
import LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
-- Mm
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
-- Kernel
import LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
import LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
import LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Time
-- Net, drivers
import LinuxSem.LinuxProcessSem.Sys.Net.Socket
import LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random

namespace LinuxSem.LinuxProcessSem.Sys.SyscallTable

open LinuxSem.LinuxProcessSem

-- The spec modules, so the table reads like the kernel's.
open LinuxSem.LinuxProcessSem.Sys.Fs.DPath
open LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
open LinuxSem.LinuxProcessSem.Sys.Fs.EventPoll
open LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.LinuxProcessSem.Sys.Fs.Ioctl
open LinuxSem.LinuxProcessSem.Sys.Fs.Locks
open LinuxSem.LinuxProcessSem.Sys.Fs.Namei
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Fs.Pipe
open LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.LinuxProcessSem.Sys.Fs.Select
open LinuxSem.LinuxProcessSem.Sys.Fs.Stat
open LinuxSem.LinuxProcessSem.Sys.Fs.Sync
open LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Dispatch

open LinuxSem.Riscv

/-- The arm for one syscall number. -/
def arm (no : Int) (g : SyscallInput → SysSpec SyscallEffect) : SpecArm :=
  SpecArm.mk no (fun i => g i i)

def spec_table : List SpecArm :=
  [ arm 17  (fun i => getcwd_spec (in_arg i 1)),
    arm 19  (fun i => eventfd2_spec (flag32 (in_arg i 1))),
    arm 20  (fun i => epoll_create1_spec (flag32 (in_arg i 0))),
    arm 21  (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3)),
    arm 22  (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5)),
    arm 23  (fun i => dup_spec (fd32 (in_arg i 0))),
    arm 24  (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2)),
    arm 25  (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2)),
    arm 29  (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))),
    arm 32  (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1))),
    arm 35  (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 46  (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1)),
    arm 48  (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 56  (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 57  (fun i => close_spec (fd32 (in_arg i 0))),
    arm 59  (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1))),
    arm 61  (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2)),
    arm 62  (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2))),
    arm 63  (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 64  (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 65  (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 66  (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 67  (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 68  (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 72  (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)),
    arm 73  (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)),
    arm 78  (fun i => readlinkat_spec (fd32 (in_arg i 0))),
    arm 79  (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3))),
    arm 80  (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1)),
    arm 82  (fun i => fsync_spec (fd32 (in_arg i 0))),
    arm 83  (fun i => fsync_spec (fd32 (in_arg i 0))),
    arm 85  (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1))),
    arm 93  (fun i => exit_spec (in_arg i 0)),
    arm 94  (fun i => exit_spec (in_arg i 0)),
    arm 96  (fun _ => set_tid_address_spec),
    arm 98  (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 101 (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1)),
    arm 113 (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1)),
    arm 119 (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)),
    arm 123 (fun i => sched_getaffinity_spec (in_arg i 1)),
    arm 124 (fun _ => sched_yield_spec),
    arm 130 (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1))),
    arm 131 (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2))),
    arm 132 (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1)),
    arm 134 (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 135 (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 144 (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))),
    arm 146 (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))),
    arm 147 (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))),
    arm 149 (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))),
    arm 157 (fun _ => setsid_spec),
    arm 158 (fun i => getgroups_spec (in_arg i 0)),
    arm 159 (fun _ => setgroups_spec),
    arm 160 (fun i => uname_spec (in_arg i 0)),
    arm 167 (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1)),
    arm 169 (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1)),
    arm 172 (fun _ => getpid_spec),
    arm 174 (fun _ => getid_spec Creds.cr_uid),
    arm 175 (fun _ => getid_spec Creds.cr_euid),
    arm 176 (fun _ => getid_spec Creds.cr_gid),
    arm 177 (fun _ => getid_spec Creds.cr_egid),
    arm 178 (fun _ => gettid_spec),
    arm 198 (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)),
    arm 199 (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 200 (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 201 (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1)),
    arm 202 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0)),
    arm 203 (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 204 (fun i => getsockname_spec (fd32 (in_arg i 0))),
    arm 205 (fun i => getpeername_spec (fd32 (in_arg i 0))),
    arm 206 (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)),
    arm 207 (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 208 (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))),
    arm 209 (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)),
    arm 210 (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))),
    arm 211 (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)),
    arm 212 (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)),
    arm 214 (fun i => brk_spec (in_arg i 0)),
    arm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1)),
    arm 216 (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 220 (fun i => clone_spec (in_arg i 0)),
    arm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)),
    arm 226 (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)),
    arm 233 (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2))),
    arm 242 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 260 (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)),
    arm 261 (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)),
    arm 278 (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)),
    arm 435 (fun i => clone3_spec (in_arg i 0) (in_arg i 1)),
    arm 439 (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) ]

end LinuxSem.LinuxProcessSem.Sys.SyscallTable
