/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames.CostlyF —
    `sched_setscheduler`, the `sint32`-gated `vm_frame_m` arm.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  Carried over VERBATIM from `Checks/VmMapsDisjoint.lean` lines 2452-2479
  of commit 63c70ae, including the note that explains why its first gate
  needs `by_cases` (`sint32 policy < 0` is a PROPOSITION, so the
  `split`/`simp` loop cannot decide it without reducing `sint32` on a
  symbolic word).  It sits last in the `vm_frame_m` block because the
  pre-split file ordered it there, and the order is preserved.
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
   `sched_setscheduler`: the same loop once the FIRST gate is a `sint32`
   comparison.  That one is a PROPOSITION (`sint32 policy < 0`), so the
   `split`/`simp` loop cannot decide it without reducing `sint32` on a
   symbolic word; casing it with `by_cases` first (`cases` never reduces)
   puts the loop back in business.  The rest of the arm — `w_is0 param ||
   decide (sint32 pid < 0)`, the four-byte copy, `sched_targets_self_b` and
   the shared `sched_setscheduler_answer` — is ordinary `Bool` work.
   ------------------------------------------------------------------------- -/

set_option maxHeartbeats 1000000 in
/-- `sched_setscheduler`'s frame: the policy gate, the pid/param gate, the
    four-byte copy, the self-target gate and the shared
    `sched_setscheduler_answer` — whose accepting arm is
    `check_ret_only_copyins`, so the model is the one it was given. -/
theorem check_sched_setscheduler_frame (i : SyscallInput) (pid policy param : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler i pid policy param eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci
  all_goals (
    unfold LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler at H
    by_cases h1 : sint32 policy < 0
    · simp only [ite_eq_left h1] at H
      vm_frame_m H LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler
    · simp only [ite_eq_right h1] at H
      vm_frame_m H LinuxSem.Checks.Sys.Kernel.Sched.Syscalls.check_sched_setscheduler)


end LinuxSem.Checks.VmMapsDisjoint
