/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyA — the first
    group of PART 3's wide frame arms: `getsockopt`, `newfstatat`, `futex`.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  The banner and the three arms below are carried over VERBATIM from
  `Checks/VmMapsDisjoint.lean` lines 2339-2394 of commit 63c70ae.  The
  banner's measurement table is the reason this directory exists: those
  seven arms were ~80 s of the pre-split 92.8 s, so each group is its own
  module and lake checks the groups concurrently.  `futex` is the most
  expensive arm here (12.1 s measured); the other two are 1.3 s and 4.4 s.
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
   The nine arms closed by the `vm_frame_m` route (plus `newfstatat`, whose
   only obstacle was the same terminal wrapper).  Every guard on the way
   down is a `Bool` test or a `match` on model state — none of the
   `decide`/`z_ldiff` guards of the block still deferred below — so the
   `split`/`simp` loop needs no `cases h : <guard>` prelude here.

   Measured in a probe file with warm oleans: `getsockopt` 1.3 s,
   `newfstatat` 4.4 s, `futex` 12.1 s, `setresgid` 20.7 s, `writev` 26 s,
   `pwrite64` 22 s, `prlimit64` 28 s.  The last four are the wide ones: the
   `fd_lookup` dispatch is entered once per effect shape.
   ------------------------------------------------------------------------- -/

set_option maxHeartbeats 1000000 in
/-- `getsockopt`'s frame: `sock_fd` splits into the errno half (which answers
    `check_ret_only`) and the socket half, whose single answering arm is the
    -EOPNOTSUPP `check_ret_only_copyins`. -/
theorem check_getsockopt_frame (i : SyscallInput) (fd level optlenp : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Net.Socket.check_getsockopt i fd level optlenp eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Net.Socket.check_getsockopt at H
    vm_frame_m H LinuxSem.Checks.Sys.Net.Socket.check_getsockopt)

set_option maxHeartbeats 1000000 in
/-- `newfstatat`'s frame: the flag guard, the `read_cstr` classification, the
    `AT_FDCWD` / dot-path guards — and then two `check_ret_only_copyins`
    answers.  No `fs` write, so no ledger change. -/
theorem check_newfstatat_frame (i : SyscallInput) (dirfd pathp flag : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Fs.Stat.check_newfstatat i dirfd pathp flag eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Fs.Stat.check_newfstatat at H
    try dsimp only at H
    vm_frame_m H LinuxSem.Checks.Sys.Fs.Stat.check_newfstatat)

set_option maxHeartbeats 1000000 in
/-- `futex`'s frame: the two `bv_eqb` command gates, then
    `check_futex_wake_private` (three `check_ret_only` answers, one of them
    behind the `uaddr % 4 == 0` alignment gate) or
    `check_futex_wait_private` (the same two gates, then `read_bytes_map`
    and the value comparison).  Only the model's `futex` field could move
    and neither helper touches it. -/
theorem check_futex_frame (i : SyscallInput) (uaddr op val utime : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Futex.Syscalls.check_futex i uaddr op val utime eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Futex.Syscalls.check_futex at H
    vm_frame_m H LinuxSem.Checks.Sys.Kernel.Futex.Syscalls.check_futex LinuxSem.Checks.Sys.Kernel.Futex.Syscalls.check_futex_wake_private LinuxSem.Checks.Sys.Kernel.Futex.Syscalls.check_futex_wait_private)


end LinuxSem.Checks.VmMapsDisjoint
