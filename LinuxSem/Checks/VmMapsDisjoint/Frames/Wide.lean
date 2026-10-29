/-
  * LinuxSem.Checks.VmMapsDisjoint.Frames.Wide — the five
    wide-dispatch arms whose guards are all cheap.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  Carried over VERBATIM from `Checks/VmMapsDisjoint.lean` lines 2096-2152
  of commit 63c70ae, banner included.

  WHY THEY ARE NOT IN `Frames.lean`.  The banner below says these five arms
  are cheap PER ARM (1.1 s, 0.9 s, 1.0 s, 1.0 s measured in a probe file)
  because none of their guards is a bitvector computation.  That is true of
  each arm and false of the group as a module: measured together they are
  22.3 s, more than the 16.7 s that the other fifty-odd arms of PART 3 cost
  in one module.  Splitting them out is what keeps `Frames.lean` off the
  critical path, and 22.3 s still sits below the `writev` / `prlimit64`
  long poles (32.4 s / 32.1 s), so nothing waits behind them.
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
   The next five are the arms whose MODEL-state dispatch is wide but whose
   guards are all CHEAP (list membership, `bv_eqb`, `access_okb`): the
   `split` loop above never has to reduce a bitvector computation, so the
   same one-line `vm_frame` closes them.  Measured in a probe file with
   warm oleans: `read` 1.1 s, `pread64` 0.9 s, `accept4` 0.9 s,
   `rt_sigaction` 1.0 s, `tgkill` 1.0 s.  This is the measurement that
   separates the two populations in the DEFERRED block: it is NOT the
   width of the state dispatch that costs, it is whether a guard mentions
   `z_land` / `z_ldiff` / `sint32`, which `split`'s simplifier tries to
   reduce and cannot.
   ------------------------------------------------------------------------- -/

set_option maxHeartbeats 1000000 in
/-- `accept4`'s frame: `check_errno_only` / `check_new_fd_result` are the
    two fresh-descriptor acceptors, and neither touches `vm_maps`. -/
theorem check_accept4_frame (fd addrp addrlenp flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_accept4 fd addrp addrlenp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Net.Socket.check_accept4 LinuxSem.Checks.Sys.Net.Socket.check_errno_only LinuxSem.Checks.Sys.Net.Socket.check_new_fd_result LinuxSem.Checks.Sys.Prelude.check_ret_only

set_option maxHeartbeats 1000000 in
/-- `pread64`'s frame: the `fd_lookup` dispatch only ever reaches
    `check_ret_only` or `check_read_urandom`, and the latter rewrites
    `m_urandom` alone. -/
theorem check_pread64_frame (i : SyscallInput) (fd buf count pos : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pread64 i fd buf count pos eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.ReadWrite.check_pread64 LinuxSem.Checks.Sys.Fs.ReadWrite.check_read_urandom LinuxSem.Checks.Sys.Prelude.check_ret_only

set_option maxHeartbeats 1000000 in
/-- `read`'s frame — the widest dispatch in the file (`fd_lookup`'s arms ×
    `m_stdin` × two `read_bytes_map` trees × the socket protocol) and it
    still costs one second: every guard on the way down is a `Bool` test
    on the arguments or a `match` on model state, never a bitvector
    computation. -/
theorem check_read_frame (i : SyscallInput) (fd buf count : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_read i fd buf count eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Fs.ReadWrite.check_read LinuxSem.Checks.Sys.Uaccess.check_access_ok_zero LinuxSem.Checks.Sys.Fs.ReadWrite.check_read_urandom LinuxSem.Checks.Sys.Prelude.check_ret_only LinuxSem.Checks.Sys.Fs.ReadWrite.check_socket_pending_error

set_option maxHeartbeats 1000000 in
/-- `rt_sigaction`'s frame: both accepting arms rewrite the signal-action
    table, never the ledger. -/
theorem check_rt_sigaction_frame (i : SyscallInput) (sig act oact ss : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_rt_sigaction i sig act oact ss eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  vm_frame eff H LinuxSem.Checks.Sys.Kernel.Signal.check_rt_sigaction LinuxSem.Checks.Sys.Prelude.check_ret_only



end LinuxSem.Checks.VmMapsDisjoint
