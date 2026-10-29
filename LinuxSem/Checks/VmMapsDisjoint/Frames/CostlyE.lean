/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyE —
    `prlimit64`.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  Carried over VERBATIM from `Checks/VmMapsDisjoint.lean` lines 2439-2451
  of commit 63c70ae.  Measured at 28 s — the most expensive arm in the
  file, and therefore the long pole of the parallel build as well; it is
  alone in its module so that nothing else waits behind it.
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

set_option maxHeartbeats 1000000 in
/-- `prlimit64`'s frame: both pointer-pair gates, the `read_bytes_map` split,
    `check_rlim64_read` (which rebuilds `m_rlimit_core` only) and the
    `RLIMIT_CORE` write, which rebuilds `m_rlimit_core` and nothing else. -/
theorem check_prlimit64_frame (i : SyscallInput) (pid resource new_rlim old_rlim : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Sys.check_prlimit64 i pid resource new_rlim old_rlim eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Sys.check_prlimit64 at H
    vm_frame_m H LinuxSem.Checks.Sys.Kernel.Sys.check_prlimit64 LinuxSem.Checks.Sys.Kernel.Sys.check_rlim64_read)


end LinuxSem.Checks.VmMapsDisjoint
