/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyB —
    `setresuid` / `setresgid`, one arm stated over `check_setresid`.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  Carried over VERBATIM from `Checks/VmMapsDisjoint.lean` lines 2395-2410
  of commit 63c70ae, whose banner (`Frames/CostlyA.lean`) records the
  measurement: 20.7 s, the third most expensive arm in the file and on its
  own enough to pay for a module.
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
/-- `setresuid` / `setresgid`'s frame, stated over the shared
    `check_setresid` so that ONE lemma covers both arms.  Three answers
    (`0`, `-EPERM`, and the `check_setid_result` tail), the last of which
    rebuilds the model with `with_creds` — a projection update, which is
    why `rfl` closes it. -/
theorem check_setresid_frame (get : Creds → Sys.Kernel.Sys.IdTriple) (put : Sys.Kernel.Sys.IdTriple → Creds → Creds) (user : Bool) (r e s : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Sys.check_setresid get put user r e s eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r', ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Sys.check_setresid at H
    try dsimp only at H
    vm_frame_m H LinuxSem.Checks.Sys.Kernel.Sys.check_setresid LinuxSem.Checks.Sys.Kernel.Sys.check_setid_result)


end LinuxSem.Checks.VmMapsDisjoint
