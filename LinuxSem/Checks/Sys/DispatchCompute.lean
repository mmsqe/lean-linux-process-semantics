/-
  * LinuxProcessSem.Checks.Sys.DispatchCompute — what the dispatchers compute to

  Split from `Checks.Sys.Dispatch` because these need `check_syscall` and
  `syscall_spec_witness`, which dispatch over the table `Arm` builds.

  The arms' `check_*` and `*_witness` are reached the way
  `Checks/Sys/Dispatch.lean` reaches them, so this file imports that module
  (through `Checks/Progress.lean`) and repeats its `open` list for the
  checkers and witnesses.  Nothing here is stated at a name that file does
  not already hold.

  Every one of the 69 syscalls below is in the 90-arm `checked_table`, at
  the same number, with the same argument projection and the same exported
  `check_*` / `*_witness` application.  So each lemma here is the lookup,
  and the lookup is `rfl`-level computation over that table.

  `reflexivity` in full conversion is the same fact reached in two steps,
  as `Common/LibWritev.lean`'s `check_syscall_writev` does it: fix the table
  lookup at the literal number (one `simp` over `checked_table` and
  `lookup_ca`, which is the `arm_dispatch` tactic's first branch), then hand
  the arm that answered back to its exported lemma (`ca_check_arm_*` /
  `ca_witness_arm_*`).  Nothing is reproved per arm beyond that.

  The `arm_dispatch` tactic lives in `Checks/Sys/Dispatch.lean` §4 — a
  `macro` in the `Dispatch` namespace — and is not restated here;
  `Checks/Progress.lean` and `Common/LibWritev.lean` are its call sites.
-/
import LinuxSem.Checks.Progress
import LinuxSem.Checks.ExecutableSpecs

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs (syscall_spec)
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Progress
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable (spec_table)
open LinuxSem.LinuxProcessSem.Sys.Syscall
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
open LinuxSem.Checks.Sys.Fs.DPath
open LinuxSem.Checks.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Fs.EventPoll
open LinuxSem.Checks.Sys.Fs.Fcntl
open LinuxSem.Checks.Sys.Fs.File
open LinuxSem.Checks.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Fs.Namei
open LinuxSem.Checks.Sys.Fs.Open
open LinuxSem.Checks.Sys.Fs.Pipe
open LinuxSem.Checks.Sys.Fs.Readdir
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Fs.Select
open LinuxSem.Checks.Sys.Fs.Stat
open LinuxSem.Checks.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Fs.Timerfd
open LinuxSem.Checks.Sys.Mm.Madvise
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Kernel.Futex.Syscalls
open LinuxSem.Checks.Sys.Kernel.Groups
open LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Kernel.Time.Hrtimer
open LinuxSem.Checks.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks.Sys.Kernel.Time.Time
open LinuxSem.Checks.Sys.Net.Socket
open LinuxSem.Checks.Sys.Drivers.Char.Random
open LinuxSem.Checks.Witness.Fs.DPath
open LinuxSem.Checks.Witness.Fs.EventFd
open LinuxSem.Checks.Witness.Fs.EventPoll
open LinuxSem.Checks.Witness.Fs.Fcntl
open LinuxSem.Checks.Witness.Fs.File
open LinuxSem.Checks.Witness.Fs.Ioctl
open LinuxSem.Checks.Witness.Fs.Locks
open LinuxSem.Checks.Witness.Fs.Namei
open LinuxSem.Checks.Witness.Fs.Open
open LinuxSem.Checks.Witness.Fs.Pipe
open LinuxSem.Checks.Witness.Fs.Readdir
open LinuxSem.Checks.Witness.Fs.ReadWrite
open LinuxSem.Checks.Witness.Fs.Select
open LinuxSem.Checks.Witness.Fs.Stat
open LinuxSem.Checks.Witness.Fs.Sync
open LinuxSem.Checks.Witness.Fs.Timerfd
open LinuxSem.Checks.Witness.Mm.Madvise
open LinuxSem.Checks.Witness.Mm.Mmap
open LinuxSem.Checks.Witness.Mm.Mprotect
open LinuxSem.Checks.Witness.Mm.Mremap
open LinuxSem.Checks.Witness.Kernel.Exit
open LinuxSem.Checks.Witness.Kernel.Fork
open LinuxSem.Checks.Witness.Kernel.Futex.Syscalls
open LinuxSem.Checks.Witness.Kernel.Groups
open LinuxSem.Checks.Witness.Kernel.Sched.Syscalls
open LinuxSem.Checks.Witness.Kernel.Signal
open LinuxSem.Checks.Witness.Kernel.Sys
open LinuxSem.Checks.Witness.Kernel.Time.Hrtimer
open LinuxSem.Checks.Witness.Kernel.Time.PosixTimers
open LinuxSem.Checks.Witness.Kernel.Time.Time
open LinuxSem.Checks.Witness.Net.Socket
open LinuxSem.Checks.Witness.Drivers.Char.Random

namespace LinuxSem.Checks.Sys.DispatchCompute

/-! ## The local shims

    The unsigned value of the syscall number.  A transparent alias, so no
    statement below changes meaning: this is the very term
    `Dispatch.check_syscall` dispatches on. -/

/-- The unsigned value of a bitvector, in `Int` so that range arithmetic
    does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `in_sysno` as a function (a `SyscallInput` field projection). -/
abbrev in_sysno (i : SyscallInput) : word := i.in_sysno

/-- The `Creds` projections, as functions: the four `get*id` checkers take
    the selector as an argument, and the alias is what lets a statement
    read `check_getid cr_uid eff m`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

abbrev cr_uid : Creds → word := Creds.cr_uid
abbrev cr_euid : Creds → word := Creds.cr_euid
abbrev cr_gid : Creds → word := Creds.cr_gid
abbrev cr_egid : Creds → word := Creds.cr_egid

/- =========================================================================
   What the dispatchers compute to, per number

   What the dispatchers compute to, per number.  Full conversion settles the
   lookup outright, where a `simp` with a delta list cannot, because the arms
   were built by `refine` and `simp` will not unfold them.  A proof that knows
   its syscall number rewrites with one of these and is back to the plain
   `check_*` it was written against.
   ========================================================================= -/

theorem check_syscall_dup (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 23) :
    check_syscall i eff m = check_dup (fd32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_dup := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_dup]

theorem syscall_witness_dup (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 23) :
    syscall_spec_witness i m = dup_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_dup := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_dup]

theorem check_syscall_dup3 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 24) :
    check_syscall i eff m = check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_dup3 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_dup3]

theorem syscall_witness_dup3 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 24) :
    syscall_spec_witness i m = dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_dup3 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_dup3]

theorem check_syscall_fcntl (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 25) :
    check_syscall i eff m = check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fcntl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_fcntl]

theorem syscall_witness_fcntl (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 25) :
    syscall_spec_witness i m = fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fcntl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_fcntl]

theorem check_syscall_ioctl (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 29) :
    check_syscall i eff m = check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ioctl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_ioctl]

theorem syscall_witness_ioctl (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 29) :
    syscall_spec_witness i m = ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ioctl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_ioctl]

theorem check_syscall_flock (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 32) :
    check_syscall i eff m = check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_flock := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_flock]

theorem syscall_witness_flock (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 32) :
    syscall_spec_witness i m = flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_flock := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_flock]

theorem check_syscall_unlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 35) :
    check_syscall i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_unlinkat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_unlinkat]

theorem syscall_witness_unlinkat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 35) :
    syscall_spec_witness i m = unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_unlinkat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_unlinkat]

theorem check_syscall_ftruncate (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 46) :
    check_syscall i eff m = check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ftruncate := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_ftruncate]

theorem syscall_witness_ftruncate (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 46) :
    syscall_spec_witness i m = ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ftruncate := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_ftruncate]

theorem check_syscall_faccessat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 48) :
    check_syscall i eff m = check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_faccessat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_faccessat]

theorem syscall_witness_faccessat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 48) :
    syscall_spec_witness i m = faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_faccessat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_faccessat]

theorem check_syscall_openat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 56) :
    check_syscall i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_openat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_openat]

theorem syscall_witness_openat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 56) :
    syscall_spec_witness i m = openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_openat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_openat]

theorem check_syscall_close (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 57) :
    check_syscall i eff m = check_close (fd32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_close := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_close]

theorem syscall_witness_close (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 57) :
    syscall_spec_witness i m = close_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_close := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_close]

theorem check_syscall_pipe2 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 59) :
    check_syscall i eff m = check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_pipe2 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_pipe2]

theorem syscall_witness_pipe2 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 59) :
    syscall_spec_witness i m = pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_pipe2 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_pipe2]

theorem check_syscall_lseek (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 62) :
    check_syscall i eff m = check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_lseek := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_lseek]

theorem syscall_witness_lseek (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 62) :
    syscall_spec_witness i m = lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_lseek := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_lseek]

theorem check_syscall_read (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 63) :
    check_syscall i eff m = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_read := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_read]

theorem syscall_witness_read (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 63) :
    syscall_spec_witness i m = read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_read := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_read]

theorem check_syscall_write (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 64) :
    check_syscall i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_write := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_write]

theorem syscall_witness_write (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 64) :
    syscall_spec_witness i m = write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_write := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_write]

theorem check_syscall_readv (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 65) :
    check_syscall i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_readv := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_readv]

theorem syscall_witness_readv (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 65) :
    syscall_spec_witness i m = readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_readv := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_readv]

theorem check_syscall_writev (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 66) :
    check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_writev := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_writev]

theorem syscall_witness_writev (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 66) :
    syscall_spec_witness i m = writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_writev := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_writev]

theorem check_syscall_pselect6 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 72) :
    check_syscall i eff m = check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_pselect6 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_pselect6]

theorem syscall_witness_pselect6 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 72) :
    syscall_spec_witness i m = pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_pselect6 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_pselect6]

theorem check_syscall_ppoll (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 73) :
    check_syscall i eff m = check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ppoll := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_ppoll]

theorem syscall_witness_ppoll (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 73) :
    syscall_spec_witness i m = ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_ppoll := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_ppoll]

theorem check_syscall_readlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 78) :
    check_syscall i eff m = check_readlinkat (fd32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_readlinkat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_readlinkat]

theorem syscall_witness_readlinkat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 78) :
    syscall_spec_witness i m = readlinkat_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_readlinkat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_readlinkat]

theorem check_syscall_newfstatat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 79) :
    check_syscall i eff m = check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_newfstatat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_newfstatat]

theorem syscall_witness_newfstatat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 79) :
    syscall_spec_witness i m = newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_newfstatat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_newfstatat]

theorem check_syscall_fstat (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 80) :
    check_syscall i eff m = check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fstat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_fstat]

theorem syscall_witness_fstat (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 80) :
    syscall_spec_witness i m = fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fstat := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_fstat]

theorem check_syscall_fsync (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 82) :
    check_syscall i eff m = check_fsync (fd32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fsync := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_fsync]

theorem syscall_witness_fsync (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 82) :
    syscall_spec_witness i m = fsync_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fsync := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_fsync]

theorem check_syscall_fdatasync (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 83) :
    check_syscall i eff m = check_fsync (fd32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fdatasync := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_fdatasync]

theorem syscall_witness_fdatasync (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 83) :
    syscall_spec_witness i m = fsync_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_fdatasync := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_fdatasync]

theorem check_syscall_exit (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 93) :
    check_syscall i eff m = check_exit (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_exit := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_exit]

theorem syscall_witness_exit (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 93) :
    syscall_spec_witness i m = exit_witness (in_arg i 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_exit := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_exit]

theorem check_syscall_exit_group (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 94) :
    check_syscall i eff m = check_exit (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_exit_group := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_exit_group]

theorem syscall_witness_exit_group (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 94) :
    syscall_spec_witness i m = exit_witness (in_arg i 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_exit_group := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_exit_group]

theorem check_syscall_set_tid_address (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 96) :
    check_syscall i eff m = check_set_tid_address eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_set_tid_address := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_set_tid_address]

theorem syscall_witness_set_tid_address (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 96) :
    syscall_spec_witness i m = set_tid_address_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_set_tid_address := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_set_tid_address]

theorem check_syscall_nanosleep (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 101) :
    check_syscall i eff m = check_nanosleep i (in_arg i 0) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_nanosleep := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_nanosleep]

theorem syscall_witness_nanosleep (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 101) :
    syscall_spec_witness i m = nanosleep_witness (in_arg i 0) (in_arg i 1) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_nanosleep := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_nanosleep]

theorem check_syscall_clock_gettime (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 113) :
    check_syscall i eff m = check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clock_gettime := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_clock_gettime]

theorem syscall_witness_clock_gettime (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 113) :
    syscall_spec_witness i m = clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clock_gettime := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_clock_gettime]

theorem check_syscall_sched_setscheduler (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 119) :
    check_syscall i eff m = check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_setscheduler := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_sched_setscheduler]

theorem syscall_witness_sched_setscheduler (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 119) :
    syscall_spec_witness i m = sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_setscheduler := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_sched_setscheduler]

theorem check_syscall_sched_getaffinity (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 123) :
    check_syscall i eff m = check_sched_getaffinity (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_getaffinity := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_sched_getaffinity]

theorem syscall_witness_sched_getaffinity (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 123) :
    syscall_spec_witness i m = sched_getaffinity_witness (in_arg i 1) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_getaffinity := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_sched_getaffinity]

theorem check_syscall_sched_yield (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 124) :
    check_syscall i eff m = check_sched_yield eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_yield := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_sched_yield]

theorem syscall_witness_sched_yield (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 124) :
    syscall_spec_witness i m = sched_yield_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_sched_yield := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_sched_yield]

theorem check_syscall_rt_sigaction (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 134) :
    check_syscall i eff m = check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_rt_sigaction := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_rt_sigaction]

theorem syscall_witness_rt_sigaction (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 134) :
    syscall_spec_witness i m = rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_rt_sigaction := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_rt_sigaction]

theorem check_syscall_rt_sigprocmask (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 135) :
    check_syscall i eff m = check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_rt_sigprocmask := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_rt_sigprocmask]

theorem syscall_witness_rt_sigprocmask (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 135) :
    syscall_spec_witness i m = rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_rt_sigprocmask := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_rt_sigprocmask]

theorem check_syscall_setgid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 144) :
    check_syscall i eff m = check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setgid]

theorem syscall_witness_setgid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 144) :
    syscall_spec_witness i m = setid_witness (uid32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setgid]

theorem check_syscall_setuid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 146) :
    check_syscall i eff m = check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setuid]

theorem syscall_witness_setuid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 146) :
    syscall_spec_witness i m = setid_witness (uid32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setuid]

theorem check_syscall_setresuid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 147) :
    check_syscall i eff m = check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setresuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setresuid]

theorem syscall_witness_setresuid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 147) :
    syscall_spec_witness i m = setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setresuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setresuid]

theorem check_syscall_setresgid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 149) :
    check_syscall i eff m = check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setresgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setresgid]

theorem syscall_witness_setresgid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 149) :
    syscall_spec_witness i m = setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setresgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setresgid]

theorem check_syscall_setsid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 157) :
    check_syscall i eff m = check_setsid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setsid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setsid]

theorem syscall_witness_setsid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 157) :
    syscall_spec_witness i m = setsid_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setsid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setsid]

theorem check_syscall_getgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 158) :
    check_syscall i eff m = check_getgroups (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getgroups := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getgroups]

theorem syscall_witness_getgroups (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 158) :
    syscall_spec_witness i m = getgroups_witness (in_arg i 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getgroups := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getgroups]

theorem check_syscall_setgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 159) :
    check_syscall i eff m = check_setgroups eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setgroups := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_setgroups]

theorem syscall_witness_setgroups (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 159) :
    syscall_spec_witness i m = setgroups_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_setgroups := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_setgroups]

theorem check_syscall_prctl (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 167) :
    check_syscall i eff m = check_prctl (int32 (in_arg i 0)) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_prctl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_prctl]

theorem syscall_witness_prctl (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 167) :
    syscall_spec_witness i m = prctl_witness (int32 (in_arg i 0)) (in_arg i 1) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_prctl := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_prctl]

theorem check_syscall_gettimeofday (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 169) :
    check_syscall i eff m = check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_gettimeofday := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_gettimeofday]

theorem syscall_witness_gettimeofday (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 169) :
    syscall_spec_witness i m = gettimeofday_witness (in_arg i 0) (in_arg i 1) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_gettimeofday := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_gettimeofday]

theorem check_syscall_getpid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 172) :
    check_syscall i eff m = check_getpid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getpid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getpid]

theorem syscall_witness_getpid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 172) :
    syscall_spec_witness i m = getpid_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getpid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getpid]

theorem check_syscall_getuid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 174) :
    check_syscall i eff m = check_getid cr_uid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getuid]

theorem syscall_witness_getuid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 174) :
    syscall_spec_witness i m = getid_witness cr_uid m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getuid]

theorem check_syscall_geteuid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 175) :
    check_syscall i eff m = check_getid cr_euid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_geteuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_geteuid]

theorem syscall_witness_geteuid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 175) :
    syscall_spec_witness i m = getid_witness cr_euid m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_geteuid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_geteuid]

theorem check_syscall_getgid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 176) :
    check_syscall i eff m = check_getid cr_gid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getgid]

theorem syscall_witness_getgid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 176) :
    syscall_spec_witness i m = getid_witness cr_gid m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getgid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getgid]

theorem check_syscall_getegid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 177) :
    check_syscall i eff m = check_getid cr_egid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getegid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getegid]

theorem syscall_witness_getegid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 177) :
    syscall_spec_witness i m = getid_witness cr_egid m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getegid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getegid]

theorem check_syscall_gettid (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 178) :
    check_syscall i eff m = check_gettid eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_gettid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_gettid]

theorem syscall_witness_gettid (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 178) :
    syscall_spec_witness i m = gettid_witness m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_gettid := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_gettid]

theorem check_syscall_socket (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 198) :
    check_syscall i eff m = check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_socket := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_socket]

theorem syscall_witness_socket (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 198) :
    syscall_spec_witness i m = socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_socket := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_socket]

theorem check_syscall_bind (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 200) :
    check_syscall i eff m = check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_bind := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_bind]

theorem syscall_witness_bind (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 200) :
    syscall_spec_witness i m = bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_bind := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_bind]

theorem check_syscall_listen (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 201) :
    check_syscall i eff m = check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_listen := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_listen]

theorem syscall_witness_listen (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 201) :
    syscall_spec_witness i m = listen_witness (fd32 (in_arg i 0)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_listen := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_listen]

theorem check_syscall_accept (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 202) :
    check_syscall i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_accept := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_accept]

theorem syscall_witness_accept (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 202) :
    syscall_spec_witness i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (Z_to_bv 64 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_accept := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_accept]

theorem check_syscall_connect (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 203) :
    check_syscall i eff m = check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_connect := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_connect]

theorem syscall_witness_connect (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 203) :
    syscall_spec_witness i m = connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_connect := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_connect]

theorem check_syscall_brk (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 214) :
    check_syscall i eff m = check_brk (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_brk := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_brk]

theorem syscall_witness_brk (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 214) :
    syscall_spec_witness i m = brk_witness (in_arg i 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_brk := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_brk]

theorem check_syscall_munmap (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 215) :
    check_syscall i eff m = check_munmap (in_arg i 0) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_munmap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_munmap]

theorem syscall_witness_munmap (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 215) :
    syscall_spec_witness i m = munmap_witness (in_arg i 0) (in_arg i 1) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_munmap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_munmap]

theorem check_syscall_mremap (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 216) :
    check_syscall i eff m = check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mremap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_mremap]

theorem syscall_witness_mremap (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 216) :
    syscall_spec_witness i m = mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mremap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_mremap]

theorem check_syscall_clone (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 220) :
    check_syscall i eff m = check_clone (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clone := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_clone]

theorem syscall_witness_clone (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 220) :
    syscall_spec_witness i m = clone_witness (in_arg i 0) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clone := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_clone]

theorem check_syscall_mmap (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 222) :
    check_syscall i eff m = check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mmap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_mmap]

theorem syscall_witness_mmap (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 222) :
    syscall_spec_witness i m = mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mmap := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_mmap]

theorem check_syscall_mprotect (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 226) :
    check_syscall i eff m = check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mprotect := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_mprotect]

theorem syscall_witness_mprotect (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 226) :
    syscall_spec_witness i m = mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_mprotect := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_mprotect]

theorem check_syscall_madvise (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 233) :
    check_syscall i eff m = check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_madvise := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_madvise]

theorem syscall_witness_madvise (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 233) :
    syscall_spec_witness i m = madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_madvise := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_madvise]

theorem check_syscall_recvfrom (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 207) :
    check_syscall i eff m = check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_recvfrom := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_recvfrom]

theorem syscall_witness_recvfrom (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 207) :
    syscall_spec_witness i m = recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_recvfrom := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_recvfrom]

theorem check_syscall_recvmsg (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 212) :
    check_syscall i eff m = check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_recvmsg := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_recvmsg]

theorem syscall_witness_recvmsg (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 212) :
    syscall_spec_witness i m = recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_recvmsg := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_recvmsg]

theorem check_syscall_accept4 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 242) :
    check_syscall i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_accept4 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_accept4]

theorem syscall_witness_accept4 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 242) :
    syscall_spec_witness i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_accept4 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_accept4]

theorem check_syscall_wait4 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 260) :
    check_syscall i eff m = check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_wait4 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_wait4]

theorem syscall_witness_wait4 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 260) :
    syscall_spec_witness i m = wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_wait4 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_wait4]

theorem check_syscall_uname (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 160) :
    check_syscall i eff m = check_uname i (in_arg i 0) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_uname := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_uname]

theorem syscall_witness_uname (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 160) :
    syscall_spec_witness i m = uname_witness (in_arg i 0) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_uname := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_uname]

theorem check_syscall_prlimit64 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 261) :
    check_syscall i eff m = check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_prlimit64 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_prlimit64]

theorem syscall_witness_prlimit64 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 261) :
    syscall_spec_witness i m = prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_prlimit64 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_prlimit64]

theorem check_syscall_getrandom (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 278) :
    check_syscall i eff m = check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getrandom := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_getrandom]

theorem syscall_witness_getrandom (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 278) :
    syscall_spec_witness i m = getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_getrandom := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_getrandom]

theorem check_syscall_clone3 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 435) :
    check_syscall i eff m = check_clone3 i (in_arg i 0) (in_arg i 1) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clone3 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_clone3]

theorem syscall_witness_clone3 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 435) :
    syscall_spec_witness i m = clone3_witness i (in_arg i 0) (in_arg i 1) m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_clone3 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_clone3]

theorem check_syscall_faccessat2 (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : bv_unsigned (in_sysno i) = 439) :
    check_syscall i eff m = check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_faccessat2 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_check_arm_faccessat2]

theorem syscall_witness_faccessat2 (i : SyscallInput) (m : Model)
    (H : bv_unsigned (in_sysno i) = 439) :
    syscall_spec_witness i m = faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := by
  have hlook : LinuxSem.Checks.Sys.Dispatch.lookup_ca LinuxSem.Checks.Sys.Dispatch.checked_table (bv_unsigned (in_sysno i))
      = some LinuxSem.Checks.Sys.Dispatch.arm_faccessat2 := by
    rw [H]
    simp only [LinuxSem.Checks.Sys.Dispatch.checked_table, LinuxSem.Checks.Sys.Dispatch.lookup_ca]
    simp
  simp only [LinuxSem.Checks.Progress.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.syscall_spec_witness,
    LinuxSem.Checks.Sys.Dispatch.syscall_spec_witness,
    hlook, LinuxSem.Checks.Sys.Dispatch.ca_witness_arm_faccessat2]
/-! ## Sanity check — the 69 numbers below are the table's

    Every number here is one the `checked_table` carries by construction,
    and the lemmas above are the proof.  This states it as one computation
    over the REAL table, so a number that lost its arm is caught here rather
    than by a caller that happens to cite it.  The list is the 69 numbers
    this file names. -/

/-- Every number this file states a lemma for is a number the checked
    table answers for. -/
example :
    [23, 24, 25, 29, 32, 35, 46, 48, 56, 57, 59, 62, 63, 64, 65, 66, 72, 73, 78, 79, 80, 82, 83, 93, 94, 96, 101, 113, 119, 123, 124, 134, 135, 144, 146, 147, 149, 157, 158, 159, 160, 167, 169, 172, 174, 175, 176, 177, 178, 198, 200, 201, 202, 203, 207, 212, 214, 215, 216, 220, 222, 226, 233, 242, 260, 261, 278, 435, 439].all
      (fun n => (LinuxSem.Checks.Sys.Dispatch.lookup_ca
        LinuxSem.Checks.Sys.Dispatch.checked_table n).isSome) = true := by
  decide

end LinuxSem.Checks.Sys.DispatchCompute
