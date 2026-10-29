/-
  * LinuxProcessSem.Checks.Sys.Dispatch — a checked syscall, and the tables over them

  `Sys.Dispatch` makes a syscall a value on the spec side.  This does the same
  for the two things the Checks layer adds -- the executable checker and
  the progress witness -- and, crucially, carries the PROOFS relating them
  to that syscall's spec as fields.

  TWO RECORDS, not one, and the reason is the trust boundary: the spec
  layer must not depend on `Checks`, so a proof about a checker cannot
  live in a `SpecArm`.  A `CheckedArm` therefore holds a `SpecArm` and
  everything the Checks layer knows about it, and `checked_table_arms`
  below pins that the two tables describe the same surface.

  What this buys: the four soundness/completeness theorems and
  `receptive` each become one lookup and one field, instead of one block
  per syscall.  They stop growing when a syscall is added, and adding one
  stops touching them.

  CONTENTS.  The framework (`CheckedArm`, `ca_no`, `lookup_ca`,
  `lookup_ca_arm`, §1); the 90 arms with the concrete table (§2); the 270
  pointwise lemmas and the `ca_no_arm_*` lemmas (§2, all `rfl`, registered
  for `simp`); the four soundness/completeness theorems and `receptive` for
  ANY table (§3); and their concrete instances at `checked_table`, plus the
  `arm_dispatch` tactic (§4).

  FIVE POINTS ABOUT THE SHAPE, all bookkeeping:

  * `checked_table` is sorted by syscall number, the same order as
    `Sys.SyscallTable.spec_table`, because `checked_table_arms` is `rfl` only
    if the two lists are written in the same order.  A list in definition
    order would put `arm_uname` (160) between `arm_wait4` (260) and
    `arm_prlimit64` (261), and `arm_recvmsg` (212) after `arm_madvise`
    (233); the arms themselves are the same 90.
  * `ca_no_arm_*` is given for all 90 arms.  Stating it for 81 and leaving
    out eventfd2, epoll_create1, epoll_ctl, epoll_pwait, pread64, pwrite64,
    tkill, tgkill and uname would leave `arm_dispatch` unable to resolve
    those nine numbers; the nine extra lemmas are `rfl` too, so nothing is
    assumed.
  * `arm_dispatch` is a `macro` over `simp` rather than an `Ltac` over
    `autorewrite`: Lean has no `Hint Rewrite` database, and a local
    `register_simp_attr` would drag `Lean.Meta` into a library file.  The
    pointwise lemmas are therefore plain `simp` lemmas and the tactic is
    `simp` after the two definitions are unfolded.  Same effect, wider
    registration.
  * The concrete instances of the five theorems live in `namespace
    CheckedTable` (§4), because `Checks/ExecutableSpecs.lean` and
    `Checks/Progress.lean` cannot be reached from here without a cycle, and
    the generic versions of §3 already hold the unqualified names.
  * Two syscalls -- `getgroups` (158) and `sched_setscheduler` (119) -- mark
    their spec, checker and witness `[local irreducible]` for the span of
    their arm, then `[local semireducible]` again.  Nothing about what they
    mean changes; the unifier just stops unfolding a body whose first branch
    is a stuck `ite`, which is what `rfl` would otherwise do (see the note
    above `arm_sched_setscheduler`).
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Uaccess
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.SyscallTable
-- The checkers, one module per family.
import LinuxSem.Checks.Sys.Fs.DPath
import LinuxSem.Checks.Sys.Fs.EventFd
import LinuxSem.Checks.Sys.Fs.EventPoll
import LinuxSem.Checks.Sys.Fs.Fcntl
import LinuxSem.Checks.Sys.Fs.File
import LinuxSem.Checks.Sys.Fs.Ioctl
import LinuxSem.Checks.Sys.Fs.Locks
import LinuxSem.Checks.Sys.Fs.Namei
import LinuxSem.Checks.Sys.Fs.Open
import LinuxSem.Checks.Sys.Fs.Pipe
import LinuxSem.Checks.Sys.Fs.Readdir
import LinuxSem.Checks.Sys.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.ReadWrite.Readv
import LinuxSem.Checks.Sys.Fs.ReadWrite.Vec
import LinuxSem.Checks.Sys.Fs.ReadWrite.Write
import LinuxSem.Checks.Sys.Fs.Select
import LinuxSem.Checks.Sys.Fs.Stat
import LinuxSem.Checks.Sys.Fs.Sync
import LinuxSem.Checks.Sys.Fs.Timerfd
import LinuxSem.Checks.Sys.Mm.Madvise
import LinuxSem.Checks.Sys.Mm.Mmap
import LinuxSem.Checks.Sys.Mm.Mprotect
import LinuxSem.Checks.Sys.Mm.Mremap
import LinuxSem.Checks.Sys.Kernel.Exit
import LinuxSem.Checks.Sys.Kernel.Fork
import LinuxSem.Checks.Sys.Kernel.Futex.Syscalls
import LinuxSem.Checks.Sys.Kernel.Groups
import LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
import LinuxSem.Checks.Sys.Kernel.Signal
import LinuxSem.Checks.Sys.Kernel.Sys
import LinuxSem.Checks.Sys.Kernel.Time.Hrtimer
import LinuxSem.Checks.Sys.Kernel.Time.PosixTimers
import LinuxSem.Checks.Sys.Kernel.Time.Time
import LinuxSem.Checks.Sys.Net.Socket
import LinuxSem.Checks.Sys.Net.Socket.Connect
import LinuxSem.Checks.Sys.Net.Socket.Send
import LinuxSem.Checks.Sys.Net.Socket.Socket
import LinuxSem.Checks.Sys.Drivers.Char.Random
-- The witnesses, likewise.
import LinuxSem.Checks.Witness.Fs.DPath
import LinuxSem.Checks.Witness.Fs.EventFd
import LinuxSem.Checks.Witness.Fs.EventPoll
import LinuxSem.Checks.Witness.Fs.Fcntl
import LinuxSem.Checks.Witness.Fs.File
import LinuxSem.Checks.Witness.Fs.Ioctl
import LinuxSem.Checks.Witness.Fs.Locks
import LinuxSem.Checks.Witness.Fs.Namei
import LinuxSem.Checks.Witness.Fs.Open
import LinuxSem.Checks.Witness.Fs.Pipe
import LinuxSem.Checks.Witness.Fs.Readdir
import LinuxSem.Checks.Witness.Fs.ReadWrite
import LinuxSem.Checks.Witness.Fs.Select
import LinuxSem.Checks.Witness.Fs.Stat
import LinuxSem.Checks.Witness.Fs.Sync
import LinuxSem.Checks.Witness.Fs.Timerfd
import LinuxSem.Checks.Witness.Mm.Madvise
import LinuxSem.Checks.Witness.Mm.Mmap
import LinuxSem.Checks.Witness.Mm.Mprotect
import LinuxSem.Checks.Witness.Mm.Mremap
import LinuxSem.Checks.Witness.Kernel.Exit
import LinuxSem.Checks.Witness.Kernel.Fork
import LinuxSem.Checks.Witness.Kernel.Futex.Syscalls
import LinuxSem.Checks.Witness.Kernel.Groups
import LinuxSem.Checks.Witness.Kernel.Sched.Syscalls
import LinuxSem.Checks.Witness.Kernel.Signal
import LinuxSem.Checks.Witness.Kernel.Sys
import LinuxSem.Checks.Witness.Kernel.Time.Hrtimer
import LinuxSem.Checks.Witness.Kernel.Time.PosixTimers
import LinuxSem.Checks.Witness.Kernel.Time.Time
import LinuxSem.Checks.Witness.Net.Socket
import LinuxSem.Checks.Witness.Drivers.Char.Random

namespace LinuxSem.Checks.Sys.Dispatch

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.LinuxProcessSem.Specs (syscall_spec)
open LinuxSem.LinuxProcessSem.Sys.Dispatch
  (SpecArm lookup_arm dispatch dispatch_arm dispatch_unmodeled)
-- `Specs` re-exports the table only by `open`, so it is cited at its home.
open LinuxSem.LinuxProcessSem.Sys.SyscallTable (spec_table)
-- The spec modules, so the arms read like the kernel's table.  This is the
-- same list `Sys.SyscallTable` opens.
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
-- The checkers and the witnesses, one `open` per family.
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

/- =========================================================================
   §1  The checked arm, and the two lookups
   ========================================================================= -/

/-- One modeled syscall, with its checker, its witness, and the five facts
    that tie them to its spec.  Holding the proofs as FIELDS is what makes
    the dispatcher's theorems constant-size: the theorem does the lookup,
    the field does the work. -/
structure CheckedArm where
  /-- The spec-side arm this one checks. -/
  ca_arm : SpecArm
  /-- The executable checker. -/
  ca_check : SyscallInput → SyscallEffect → Model → check_result
  /-- The progress witness: one admissible outcome for every input. -/
  ca_witness : SyscallInput → Model → Outcome SyscallEffect Model event
  /-- What the checker accepts, the spec admits. -/
  ca_sound_ok : ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event),
    ca_check i eff m = .CheckOk m' evs → ca_arm.sa_spec i m (.ok eff m' evs)
  /-- A `CheckUnmodeled` is a spec-side `unmodeled` too. -/
  ca_sound_unmodeled : ∀ (i : SyscallInput) (eff : SyscallEffect) (m : Model),
    ca_check i eff m = .CheckUnmodeled → ca_arm.sa_spec i m .unmodeled
  /-- And conversely: every admitted `Ok` is checked to itself. -/
  ca_complete_ok : ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event),
    ca_arm.sa_spec i m (.ok eff m' evs) → ca_check i eff m = .CheckOk m' evs
  /-- Every spec-side `unmodeled` is checked to `CheckUnmodeled`. -/
  ca_complete_unmodeled : ∀ (i : SyscallInput) (m : Model) (eff : SyscallEffect),
    ca_arm.sa_spec i m .unmodeled → ca_check i eff m = .CheckUnmodeled
  /-- The witness is admissible. -/
  ca_receptive : ∀ (i : SyscallInput) (m : Model), ca_arm.sa_spec i m (ca_witness i m)

/-- The number a checked arm answers to. -/
def ca_no (c : CheckedArm) : Int := c.ca_arm.sa_no

/-- The first checked arm answering to `n`, if any.  The same lookup
    `Sys.Dispatch.lookup_arm` performs, over the checked table. -/
def lookup_ca : List CheckedArm → Int → Option CheckedArm
  | [], _ => none
  | c :: r, n => if ca_no c == n then some c else lookup_ca r n

/-- The two lookups agree, which is what lets a theorem stated over
    `Specs.syscall_spec` be discharged by a `CheckedArm`'s field.  Proved
    once, by induction on the table; it does not grow with the surface. -/
theorem lookup_ca_arm (t : List CheckedArm) (n : Int) :
    lookup_arm (t.map CheckedArm.ca_arm) n = (lookup_ca t n).map CheckedArm.ca_arm := by
  induction t with
  | nil => rfl
  | cons c r ih =>
    -- the two tables' guards must be the SAME term before the destruct
    -- reaches both of them, which is what unfolding ca_no does
    simp only [List.map_cons, lookup_ca, lookup_arm, ca_no]
    by_cases h : c.ca_arm.sa_no == n
    · simp [h]
    · simp [h, ih]

/- =========================================================================
   §2  The 90 arms, `checked_table`, `checked_table_arms`, and the
       pointwise lemmas

   One arm per modeled syscall:

     arm_<name> := mkCheckedArm (mkSpecArm N (fun i => <name>_spec <args> i))
                                (fun i eff m => check_<name> <args> eff m)
                                (fun i m => <name>_witness <args> m)
                                <the five fields>

   where `<args>` is the argument projection the spec already applies
   (`fd32 (in_arg i 0)`, `flag32 (in_arg i 1)`, `clockid32 ...`, ...), the
   same projections `Sys.SyscallTable.spec_table` uses, and the five fields
   are the exported lemmas of the checker and the witness:

     check_<name>_sound_ok, check_<name>_sound_unmodeled,
     check_<name>_complete_ok, check_<name>_complete_unmodeled,
     <name>_witness_ok

   Four arms are worth a comment, because they record kernel facts rather
   than bookkeeping.

   * eventfd2 (19).  `flag32` is applied HERE, at the ABI boundary,
     exactly as `timerfd_create`'s and `epoll_create1`'s flag words are:
     the kernel's own narrowing happens in the syscall wrapper, so the
     spec, the acceptor and the witness all receive a word already cut to
     32 bits and none of them narrows again.

     THE FLAG WORD IS ARGUMENT 1, NOT ARGUMENT 0.
     `SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)` puts
     the initial counter first, so an arm that read `in_arg i 0` would be
     judging the counter against a flag mask -- which is not a decline
     but a wrong answer, since `eventfd2(1, 0)` would then take the
     -EINVAL Linux gives no `count` at all.  `in_arg i 1` is the flag
     word.

   * timerfd_create (85).  `clockid32` and `flag32` are applied HERE, at
     the ABI boundary, exactly as `clock_gettime`'s id is: the kernel's
     own narrowing happens in the syscall wrapper, so the spec, the
     acceptor and the witness all receive words already cut to 32 bits
     and none of them narrows again.

   * sched_yield (124).  The only arm here that reads no argument at all:
     riscv's `SYSCALL_DEFINE0` expands without `SC_RISCV_REGS_TO_ARGS`, so
     the input is ignored on purpose rather than by omission
     (`Kernel.Sched.Syscalls.sched_yield_spec`).

   * tkill (130).  The checker's own answer is `CheckUnmodeled` on every
     shape whenever the model's abort declaration is clear, so an arm on a
     number the task did not ask for behaves as a number with no arm.

   Two numbers share an arm body with a neighbour:
   `arm_fdatasync` (83) is `fsync_spec` / `check_fsync` / `fsync_witness`,
   and `arm_accept` (202) is `accept4_spec` / `check_accept4` /
   `accept4_witness` with the flag word `BitVec.ofInt 64 0`.
   ========================================================================= -/

/-- getcwd (17). -/
def arm_getcwd : CheckedArm where
  ca_arm := SpecArm.mk 17 (fun i => getcwd_spec (in_arg i 1) i)
  ca_check := fun i eff m => check_getcwd (in_arg i 1) eff m
  ca_witness := fun i m => getcwd_witness (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_getcwd_sound_ok (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getcwd_sound_unmodeled (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getcwd_complete_ok (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getcwd_complete_unmodeled (in_arg i 1) m i eff H
  ca_receptive := fun i m => getcwd_witness_ok (in_arg i 1) i m

/-- eventfd2 (19). -/
def arm_eventfd2 : CheckedArm where
  ca_arm := SpecArm.mk 19 (fun i => eventfd2_spec (flag32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_eventfd2 (flag32 (in_arg i 1)) eff m
  ca_witness := fun i m => eventfd2_witness (flag32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_eventfd2_sound_ok (flag32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_eventfd2_sound_unmodeled (flag32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_eventfd2_complete_ok (flag32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_eventfd2_complete_unmodeled (flag32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => eventfd2_witness_ok (flag32 (in_arg i 1)) i m

/-- epoll_create1 (20). -/
def arm_epoll_create1 : CheckedArm where
  ca_arm := SpecArm.mk 20 (fun i => epoll_create1_spec (flag32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_epoll_create1 (flag32 (in_arg i 0)) eff m
  ca_witness := fun i m => epoll_create1_witness (flag32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_epoll_create1_sound_ok (flag32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_epoll_create1_sound_unmodeled (flag32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_epoll_create1_complete_ok (flag32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_epoll_create1_complete_unmodeled (flag32 (in_arg i 0)) m eff i H
  ca_receptive := fun i m => epoll_create1_witness_ok (flag32 (in_arg i 0)) i m

/-- epoll_ctl (21). -/
def arm_epoll_ctl : CheckedArm where
  ca_arm := SpecArm.mk 21 (fun i => epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i)
  ca_check := fun i eff m => check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m
  ca_witness := fun i m => epoll_ctl_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_epoll_ctl_sound_ok i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_epoll_ctl_sound_unmodeled i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_epoll_ctl_complete_ok i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_epoll_ctl_complete_unmodeled i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) m eff H
  ca_receptive := fun i m => epoll_ctl_witness_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m

/-- epoll_pwait (22). -/
def arm_epoll_pwait : CheckedArm where
  ca_arm := SpecArm.mk 22 (fun i => epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => epoll_pwait_witness (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m
  ca_sound_ok := fun i eff m m' evs H => check_epoll_pwait_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_epoll_pwait_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_epoll_pwait_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_epoll_pwait_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) m eff H
  ca_receptive := fun i m => epoll_pwait_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m

/-- dup (23). -/
def arm_dup : CheckedArm where
  ca_arm := SpecArm.mk 23 (fun i => dup_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_dup (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => dup_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_dup_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_dup_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_dup_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_dup_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => dup_witness_ok (fd32 (in_arg i 0)) i m

/-- dup3 (24). -/
def arm_dup3 : CheckedArm where
  ca_arm := SpecArm.mk 24 (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i)
  ca_check := fun i eff m => check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m
  ca_witness := fun i m => dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_dup3_sound_ok (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_dup3_sound_unmodeled (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_dup3_complete_ok (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_dup3_complete_unmodeled (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m i eff H
  ca_receptive := fun i m => dup3_witness_ok (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i m

/-- fcntl (25). -/
def arm_fcntl : CheckedArm where
  ca_arm := SpecArm.mk 25 (fun i => fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i)
  ca_check := fun i eff m => check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m
  ca_witness := fun i m => fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_fcntl_sound_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_fcntl_sound_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_fcntl_complete_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_fcntl_complete_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m i eff H
  ca_receptive := fun i m => fcntl_witness_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m

/-- ioctl (29). -/
def arm_ioctl : CheckedArm where
  ca_arm := SpecArm.mk 29 (fun i => ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m
  ca_witness := fun i m => ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_ioctl_sound_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_ioctl_sound_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_ioctl_complete_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_ioctl_complete_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => ioctl_witness_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m

/-- flock (32). -/
def arm_flock : CheckedArm where
  ca_arm := SpecArm.mk 32 (fun i => flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m
  ca_witness := fun i m => flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_flock_sound_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_flock_sound_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_flock_complete_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_flock_complete_unmodeled (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => flock_witness_ok (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m

/-- unlinkat (35). -/
def arm_unlinkat : CheckedArm where
  ca_arm := SpecArm.mk 35 (fun i => unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_unlinkat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_unlinkat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_unlinkat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_unlinkat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => unlinkat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- ftruncate (46). -/
def arm_ftruncate : CheckedArm where
  ca_arm := SpecArm.mk 46 (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_ftruncate_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_ftruncate_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_ftruncate_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_ftruncate_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) m i eff H
  ca_receptive := fun i m => ftruncate_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) i m

/-- faccessat (48). -/
def arm_faccessat : CheckedArm where
  ca_arm := SpecArm.mk 48 (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_faccessat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_faccessat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_faccessat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_faccessat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => faccessat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- openat (56). -/
def arm_openat : CheckedArm where
  ca_arm := SpecArm.mk 56 (fun i => openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_openat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_openat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_openat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_openat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => openat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- close (57). -/
def arm_close : CheckedArm where
  ca_arm := SpecArm.mk 57 (fun i => close_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_close (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => close_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_close_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_close_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_close_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_close_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => close_witness_ok (fd32 (in_arg i 0)) i m

/-- pipe2 (59). -/
def arm_pipe2 : CheckedArm where
  ca_arm := SpecArm.mk 59 (fun i => pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m
  ca_witness := fun i m => pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m
  ca_sound_ok := fun i eff m m' evs H => check_pipe2_sound_ok i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_pipe2_sound_unmodeled i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_pipe2_complete_ok i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_pipe2_complete_unmodeled i (in_arg i 0) (pipe_flags32 (in_arg i 1)) m eff H
  ca_receptive := fun i m => pipe2_witness_ok (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m

/-- getdents64 (61). -/
def arm_getdents64 : CheckedArm where
  ca_arm := SpecArm.mk 61 (fun i => getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i)
  ca_check := fun i eff m => check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m
  ca_witness := fun i m => getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_getdents64_sound_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getdents64_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getdents64_complete_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getdents64_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) m i eff H
  ca_receptive := fun i m => getdents64_witness_ok (fd32 (in_arg i 0)) (in_arg i 2) i m

/-- lseek (62). -/
def arm_lseek : CheckedArm where
  ca_arm := SpecArm.mk 62 (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i)
  ca_check := fun i eff m => check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m
  ca_witness := fun i m => lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs H => check_lseek_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_lseek_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_lseek_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_lseek_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m i eff H
  ca_receptive := fun i m => lseek_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m i

/-- read (63). -/
def arm_read : CheckedArm where
  ca_arm := SpecArm.mk 63 (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_read_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_read_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_read_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_read_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => read_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- write (64). -/
def arm_write : CheckedArm where
  ca_arm := SpecArm.mk 64 (fun i => write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_write_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_write_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_write_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_write_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => write_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- readv (65). -/
def arm_readv : CheckedArm where
  ca_arm := SpecArm.mk 65 (fun i => readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_readv_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_readv_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_readv_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_readv_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => readv_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- writev (66). -/
def arm_writev : CheckedArm where
  ca_arm := SpecArm.mk 66 (fun i => writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_writev_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_writev_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_writev_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_writev_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => writev_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- pread64 (67). -/
def arm_pread64 : CheckedArm where
  ca_arm := SpecArm.mk 67 (fun i => pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_pread64_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_pread64_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_pread64_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_pread64_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => pread64_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- pwrite64 (68). -/
def arm_pwrite64 : CheckedArm where
  ca_arm := SpecArm.mk 68 (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_pwrite64_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_pwrite64_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_pwrite64_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_pwrite64_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => pwrite64_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- pselect6 (72). -/
def arm_pselect6 : CheckedArm where
  ca_arm := SpecArm.mk 72 (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)
  ca_sound_ok := fun i eff m m' evs H => check_pselect6_sound_ok i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_pselect6_sound_unmodeled i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_pselect6_complete_ok i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_pselect6_complete_unmodeled i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff H
  ca_receptive := fun i m => pselect6_witness_ok (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

/-- ppoll (73). -/
def arm_ppoll : CheckedArm where
  ca_arm := SpecArm.mk 73 (fun i => ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i)
  ca_check := fun i eff m => check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m
  ca_witness := fun i m => ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4)
  ca_sound_ok := fun i eff m m' evs H => check_ppoll_sound_ok i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_ppoll_sound_unmodeled i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_ppoll_complete_ok i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_ppoll_complete_unmodeled i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) m eff H
  ca_receptive := fun i m => ppoll_witness_ok (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m

/-- readlinkat (78). -/
def arm_readlinkat : CheckedArm where
  ca_arm := SpecArm.mk 78 (fun i => readlinkat_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_readlinkat (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => readlinkat_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_readlinkat_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_readlinkat_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_readlinkat_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_readlinkat_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => readlinkat_witness_ok (fd32 (in_arg i 0)) i m

/-- newfstatat (79). -/
def arm_newfstatat : CheckedArm where
  ca_arm := SpecArm.mk 79 (fun i => newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i)
  ca_check := fun i eff m => check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m
  ca_witness := fun i m => newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m
  ca_sound_ok := fun i eff m m' evs H => check_newfstatat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_newfstatat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_newfstatat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_newfstatat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) m eff H
  ca_receptive := fun i m => newfstatat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m

/-- fstat (80). -/
def arm_fstat : CheckedArm where
  ca_arm := SpecArm.mk 80 (fun i => fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs H => check_fstat_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_fstat_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_fstat_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_fstat_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) m eff H
  ca_receptive := fun i m => fstat_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) i m

/-- fsync (82). -/
def arm_fsync : CheckedArm where
  ca_arm := SpecArm.mk 82 (fun i => fsync_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_fsync (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => fsync_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_fsync_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_fsync_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_fsync_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_fsync_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => fsync_witness_ok (fd32 (in_arg i 0)) i m

/-- fdatasync (83). -/
def arm_fdatasync : CheckedArm where
  ca_arm := SpecArm.mk 83 (fun i => fsync_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_fsync (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => fsync_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_fsync_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_fsync_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_fsync_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_fsync_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => fsync_witness_ok (fd32 (in_arg i 0)) i m

/-- timerfd_create (85). -/
def arm_timerfd_create : CheckedArm where
  ca_arm := SpecArm.mk 85 (fun i => timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_timerfd_create (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m
  ca_witness := fun i m => timerfd_create_witness (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_timerfd_create_sound_ok (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_timerfd_create_sound_unmodeled (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_timerfd_create_complete_ok (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_timerfd_create_complete_unmodeled (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => timerfd_create_witness_ok (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i m

/-- exit (93). -/
def arm_exit : CheckedArm where
  ca_arm := SpecArm.mk 93 (fun i => exit_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_exit (in_arg i 0) eff m
  ca_witness := fun i m => exit_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs H => check_exit_sound_ok (in_arg i 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_exit_sound_unmodeled (in_arg i 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_exit_complete_ok (in_arg i 0) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_exit_complete_unmodeled (in_arg i 0) m i eff H
  ca_receptive := fun i m => exit_witness_ok (in_arg i 0) i m

/-- exit_group (94). -/
def arm_exit_group : CheckedArm where
  ca_arm := SpecArm.mk 94 (fun i => exit_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_exit (in_arg i 0) eff m
  ca_witness := fun i m => exit_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs H => check_exit_sound_ok (in_arg i 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_exit_sound_unmodeled (in_arg i 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_exit_complete_ok (in_arg i 0) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_exit_complete_unmodeled (in_arg i 0) m i eff H
  ca_receptive := fun i m => exit_witness_ok (in_arg i 0) i m

/-- set_tid_address (96). -/
def arm_set_tid_address : CheckedArm where
  ca_arm := SpecArm.mk 96 (fun i => set_tid_address_spec i)
  ca_check := fun _ eff m => check_set_tid_address eff m
  ca_witness := fun _ m => set_tid_address_witness m
  ca_sound_ok := fun i eff m m' evs H => check_set_tid_address_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_set_tid_address_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_set_tid_address_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_set_tid_address_complete_unmodeled m i eff H
  ca_receptive := fun i m => set_tid_address_witness_ok i m

/-- futex (98). -/
def arm_futex : CheckedArm where
  ca_arm := SpecArm.mk 98 (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_futex i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => futex_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_futex_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_futex_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_futex_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_futex_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => futex_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- nanosleep (101). -/
def arm_nanosleep : CheckedArm where
  ca_arm := SpecArm.mk 101 (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => check_nanosleep i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => nanosleep_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs H => check_nanosleep_sound_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_nanosleep_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_nanosleep_complete_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_nanosleep_complete_unmodeled i (in_arg i 0) (in_arg i 1) m eff H
  ca_receptive := fun i m => nanosleep_witness_ok i (in_arg i 0) (in_arg i 1) m

/-- clock_gettime (113). -/
def arm_clock_gettime : CheckedArm where
  ca_arm := SpecArm.mk 113 (fun i => clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs H => check_clock_gettime_sound_ok i (clockid32 (in_arg i 0)) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_clock_gettime_sound_unmodeled i (clockid32 (in_arg i 0)) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_clock_gettime_complete_ok i (clockid32 (in_arg i 0)) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_clock_gettime_complete_unmodeled i (clockid32 (in_arg i 0)) (in_arg i 1) m eff H
  ca_receptive := fun i m => clock_gettime_witness_ok i (clockid32 (in_arg i 0)) (in_arg i 1) m

/- `sched_setscheduler_spec`, `check_sched_setscheduler` and
   `sched_setscheduler_witness` are marked irreducible for the span of this
   arm and its four pointwise lemmas, and reducible again after them (see
   the `[local semireducible]` after `ca_no_arm_sched_setscheduler`).
   Nothing about what they MEAN changes -- the arm applies them exactly as
   the spec table does, and the pointwise lemmas still hold by `rfl`.  What
   changes is that the unifier stops unfolding a body it does not need: all
   three head their first branch with `if w_is0 ...`/`if sint32 ... < 0`,
   and reducing such a stuck `ite` to compare it with itself diverges,
   which is what `rfl` otherwise does.  `getgroups_spec` and its checker
   and witness need the same treatment, for the same reason. -/

attribute [local irreducible] sched_setscheduler_spec check_sched_setscheduler sched_setscheduler_witness

/-- sched_setscheduler (119). -/
def arm_sched_setscheduler : CheckedArm where
  ca_arm := SpecArm.mk 119 (fun i => sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_sched_setscheduler_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_sched_setscheduler_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_sched_setscheduler_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_sched_setscheduler_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m H
  ca_receptive := fun i m => sched_setscheduler_witness_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) m

/-- sched_getaffinity (123). -/
def arm_sched_getaffinity : CheckedArm where
  ca_arm := SpecArm.mk 123 (fun i => sched_getaffinity_spec (in_arg i 1) i)
  ca_check := fun i eff m => check_sched_getaffinity (in_arg i 1) eff m
  ca_witness := fun i m => sched_getaffinity_witness (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_sched_getaffinity_sound_ok (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_sched_getaffinity_sound_unmodeled (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_sched_getaffinity_complete_ok (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_sched_getaffinity_complete_unmodeled (in_arg i 1) m i eff H
  ca_receptive := fun i m => sched_getaffinity_witness_ok (in_arg i 1) i m

/-- sched_yield (124). -/
def arm_sched_yield : CheckedArm where
  ca_arm := SpecArm.mk 124 (fun i => sched_yield_spec i)
  ca_check := fun _ eff m => check_sched_yield eff m
  ca_witness := fun _ m => sched_yield_witness m
  ca_sound_ok := fun i eff m m' evs H => check_sched_yield_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_sched_yield_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_sched_yield_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_sched_yield_complete_unmodeled m i eff H
  ca_receptive := fun i m => sched_yield_witness_ok i m

/-- tkill (130). -/
def arm_tkill : CheckedArm where
  ca_arm := SpecArm.mk 130 (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m
  ca_witness := fun i m => tkill_witness (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_tkill_sound_ok (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_tkill_sound_unmodeled (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_tkill_complete_ok (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_tkill_complete_unmodeled (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => tkill_witness_ok (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i m

/-- tgkill (131). -/
def arm_tgkill : CheckedArm where
  ca_arm := SpecArm.mk 131 (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i)
  ca_check := fun i eff m => check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m
  ca_witness := fun i m => tgkill_witness (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs H => check_tgkill_sound_ok (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_tgkill_sound_unmodeled (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_tgkill_complete_ok (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_tgkill_complete_unmodeled (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) m i eff H
  ca_receptive := fun i m => tgkill_witness_ok (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i m

/-- sigaltstack (132). -/
def arm_sigaltstack : CheckedArm where
  ca_arm := SpecArm.mk 132 (fun i => sigaltstack_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => sigaltstack_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs H => check_sigaltstack_sound_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_sigaltstack_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_sigaltstack_complete_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_sigaltstack_complete_unmodeled i (in_arg i 0) (in_arg i 1) m eff H
  ca_receptive := fun i m => sigaltstack_witness_ok (in_arg i 0) (in_arg i 1) i m

/-- rt_sigaction (134). -/
def arm_rt_sigaction : CheckedArm where
  ca_arm := SpecArm.mk 134 (fun i => rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_rt_sigaction_sound_ok i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_rt_sigaction_sound_unmodeled i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_rt_sigaction_complete_ok i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_rt_sigaction_complete_unmodeled i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => rt_sigaction_witness_ok (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- rt_sigprocmask (135). -/
def arm_rt_sigprocmask : CheckedArm where
  ca_arm := SpecArm.mk 135 (fun i => rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_rt_sigprocmask_sound_ok i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_rt_sigprocmask_sound_unmodeled i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_rt_sigprocmask_complete_ok i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_rt_sigprocmask_complete_unmodeled i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => rt_sigprocmask_witness_ok (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- setgid (144). -/
def arm_setgid : CheckedArm where
  ca_arm := SpecArm.mk 144 (fun i => setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m
  ca_witness := fun i m => setid_witness (uid32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_setid_sound_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setid_sound_unmodeled cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setid_complete_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setid_complete_unmodeled cred_gids set_cred_gids false (uid32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => setid_witness_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) i m

/-- setuid (146). -/
def arm_setuid : CheckedArm where
  ca_arm := SpecArm.mk 146 (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m
  ca_witness := fun i m => setid_witness (uid32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_setid_sound_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setid_sound_unmodeled cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setid_complete_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setid_complete_unmodeled cred_uids set_cred_uids true (uid32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => setid_witness_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) i m

/-- setresuid (147). -/
def arm_setresuid : CheckedArm where
  ca_arm := SpecArm.mk 147 (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
  ca_check := fun i eff m => check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m
  ca_witness := fun i m => setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs H => check_setresid_sound_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setresid_sound_unmodeled cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setresid_complete_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setresid_complete_unmodeled cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m i eff H
  ca_receptive := fun i m => setresid_witness_ok cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m

/-- setresgid (149). -/
def arm_setresgid : CheckedArm where
  ca_arm := SpecArm.mk 149 (fun i => setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i)
  ca_check := fun i eff m => check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m
  ca_witness := fun i m => setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs H => check_setresid_sound_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setresid_sound_unmodeled cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setresid_complete_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setresid_complete_unmodeled cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m i eff H
  ca_receptive := fun i m => setresid_witness_ok cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m

/-- setsid (157). -/
def arm_setsid : CheckedArm where
  ca_arm := SpecArm.mk 157 (fun i => setsid_spec i)
  ca_check := fun _ eff m => check_setsid eff m
  ca_witness := fun _ m => setsid_witness m
  ca_sound_ok := fun i eff m m' evs H => check_setsid_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setsid_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setsid_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setsid_complete_unmodeled m i eff H
  ca_receptive := fun i m => setsid_witness_ok i m

attribute [local irreducible] getgroups_spec check_getgroups getgroups_witness

/-- getgroups (158). -/
def arm_getgroups : CheckedArm where
  ca_arm := SpecArm.mk 158 (fun i => getgroups_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_getgroups (in_arg i 0) eff m
  ca_witness := fun i m => getgroups_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs H => check_getgroups_sound_ok (in_arg i 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getgroups_sound_unmodeled (in_arg i 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getgroups_complete_ok (in_arg i 0) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getgroups_complete_unmodeled (in_arg i 0) m i eff H
  ca_receptive := fun i m => getgroups_witness_ok (in_arg i 0) i m

/-- setgroups (159). -/
def arm_setgroups : CheckedArm where
  ca_arm := SpecArm.mk 159 (fun i => setgroups_spec i)
  ca_check := fun _ eff m => check_setgroups eff m
  ca_witness := fun _ m => setgroups_witness m
  ca_sound_ok := fun i eff m m' evs H => check_setgroups_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setgroups_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setgroups_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setgroups_complete_unmodeled m i eff H
  ca_receptive := fun i m => setgroups_witness_ok i m

/-- uname (160). -/
def arm_uname : CheckedArm where
  ca_arm := SpecArm.mk 160 (fun i => uname_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_uname i (in_arg i 0) eff m
  ca_witness := fun i m => uname_witness (in_arg i 0) i m
  ca_sound_ok := fun i eff m m' evs H => check_uname_sound_ok i (in_arg i 0) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_uname_sound_unmodeled i (in_arg i 0) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_uname_complete_ok i (in_arg i 0) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_uname_complete_unmodeled i (in_arg i 0) m eff H
  ca_receptive := fun i m => uname_witness_ok (in_arg i 0) i m

/-- prctl (167). -/
def arm_prctl : CheckedArm where
  ca_arm := SpecArm.mk 167 (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_prctl (int32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => prctl_witness (int32 (in_arg i 0)) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_prctl_sound_ok (int32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_prctl_sound_unmodeled (int32 (in_arg i 0)) (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_prctl_complete_ok (int32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_prctl_complete_unmodeled (int32 (in_arg i 0)) (in_arg i 1) m i eff H
  ca_receptive := fun i m => prctl_witness_ok (int32 (in_arg i 0)) (in_arg i 1) i m

/-- gettimeofday (169). -/
def arm_gettimeofday : CheckedArm where
  ca_arm := SpecArm.mk 169 (fun i => gettimeofday_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => gettimeofday_witness (in_arg i 0) (in_arg i 1) i m
  ca_sound_ok := fun i eff m m' evs H => check_gettimeofday_sound_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_gettimeofday_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_gettimeofday_complete_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_gettimeofday_complete_unmodeled i (in_arg i 0) (in_arg i 1) m eff H
  ca_receptive := fun i m => gettimeofday_witness_ok i (in_arg i 0) (in_arg i 1) m

/-- getpid (172). -/
def arm_getpid : CheckedArm where
  ca_arm := SpecArm.mk 172 (fun i => getpid_spec i)
  ca_check := fun _ eff m => check_getpid eff m
  ca_witness := fun _ m => getpid_witness m
  ca_sound_ok := fun i eff m m' evs H => check_getpid_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getpid_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getpid_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getpid_complete_unmodeled m i eff H
  ca_receptive := fun i m => getpid_witness_ok i m

/-- getuid (174). -/
def arm_getuid : CheckedArm where
  ca_arm := SpecArm.mk 174 (fun i => getid_spec Creds.cr_uid i)
  ca_check := fun _ eff m => check_getid Creds.cr_uid eff m
  ca_witness := fun _ m => getid_witness Creds.cr_uid m
  ca_sound_ok := fun i eff m m' evs H => check_getid_sound_ok Creds.cr_uid eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getid_sound_unmodeled Creds.cr_uid eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getid_complete_ok Creds.cr_uid eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getid_complete_unmodeled Creds.cr_uid m i eff H
  ca_receptive := fun i m => getid_witness_ok Creds.cr_uid i m

/-- geteuid (175). -/
def arm_geteuid : CheckedArm where
  ca_arm := SpecArm.mk 175 (fun i => getid_spec Creds.cr_euid i)
  ca_check := fun _ eff m => check_getid Creds.cr_euid eff m
  ca_witness := fun _ m => getid_witness Creds.cr_euid m
  ca_sound_ok := fun i eff m m' evs H => check_getid_sound_ok Creds.cr_euid eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getid_sound_unmodeled Creds.cr_euid eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getid_complete_ok Creds.cr_euid eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getid_complete_unmodeled Creds.cr_euid m i eff H
  ca_receptive := fun i m => getid_witness_ok Creds.cr_euid i m

/-- getgid (176). -/
def arm_getgid : CheckedArm where
  ca_arm := SpecArm.mk 176 (fun i => getid_spec Creds.cr_gid i)
  ca_check := fun _ eff m => check_getid Creds.cr_gid eff m
  ca_witness := fun _ m => getid_witness Creds.cr_gid m
  ca_sound_ok := fun i eff m m' evs H => check_getid_sound_ok Creds.cr_gid eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getid_sound_unmodeled Creds.cr_gid eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getid_complete_ok Creds.cr_gid eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getid_complete_unmodeled Creds.cr_gid m i eff H
  ca_receptive := fun i m => getid_witness_ok Creds.cr_gid i m

/-- getegid (177). -/
def arm_getegid : CheckedArm where
  ca_arm := SpecArm.mk 177 (fun i => getid_spec Creds.cr_egid i)
  ca_check := fun _ eff m => check_getid Creds.cr_egid eff m
  ca_witness := fun _ m => getid_witness Creds.cr_egid m
  ca_sound_ok := fun i eff m m' evs H => check_getid_sound_ok Creds.cr_egid eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getid_sound_unmodeled Creds.cr_egid eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getid_complete_ok Creds.cr_egid eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getid_complete_unmodeled Creds.cr_egid m i eff H
  ca_receptive := fun i m => getid_witness_ok Creds.cr_egid i m

/-- gettid (178). -/
def arm_gettid : CheckedArm where
  ca_arm := SpecArm.mk 178 (fun i => gettid_spec i)
  ca_check := fun _ eff m => check_gettid eff m
  ca_witness := fun _ m => gettid_witness m
  ca_sound_ok := fun i eff m m' evs H => check_gettid_sound_ok eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_gettid_sound_unmodeled eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_gettid_complete_ok eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_gettid_complete_unmodeled m i eff H
  ca_receptive := fun i m => gettid_witness_ok i m

/-- socket (198). -/
def arm_socket : CheckedArm where
  ca_arm := SpecArm.mk 198 (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_socket_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_socket_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_socket_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_socket_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) i m eff H
  ca_receptive := fun i m => socket_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i m

/-- socketpair (199). -/
def arm_socketpair : CheckedArm where
  ca_arm := SpecArm.mk 199 (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_socketpair_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_socketpair_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_socketpair_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_socketpair_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => socketpair_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- bind (200). -/
def arm_bind : CheckedArm where
  ca_arm := SpecArm.mk 200 (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_bind_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_bind_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_bind_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_bind_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => bind_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- listen (201). -/
def arm_listen : CheckedArm where
  ca_arm := SpecArm.mk 201 (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i)
  ca_check := fun i eff m => check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m
  ca_witness := fun i m => listen_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_listen_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_listen_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_listen_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_listen_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) m i eff H
  ca_receptive := fun i m => listen_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) i m

/-- accept (202). -/
def arm_accept : CheckedArm where
  ca_arm := SpecArm.mk 202 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) i)
  ca_check := fun i eff m => check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) eff m
  ca_witness := fun i m => accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (BitVec.ofInt 64 0) m
  ca_sound_ok := fun i eff m m' evs H => check_accept4_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_accept4_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_accept4_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) i eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_accept4_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) i m eff H
  ca_receptive := fun i m => accept4_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) i m

/-- connect (203). -/
def arm_connect : CheckedArm where
  ca_arm := SpecArm.mk 203 (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_connect_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_connect_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_connect_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_connect_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => connect_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- getsockname (204). -/
def arm_getsockname : CheckedArm where
  ca_arm := SpecArm.mk 204 (fun i => getsockname_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_getsockname (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => getsockname_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_getsockname_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getsockname_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getsockname_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getsockname_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => getsockname_witness_ok (fd32 (in_arg i 0)) i m

/-- getpeername (205). -/
def arm_getpeername : CheckedArm where
  ca_arm := SpecArm.mk 205 (fun i => getpeername_spec (fd32 (in_arg i 0)) i)
  ca_check := fun i eff m => check_getpeername (fd32 (in_arg i 0)) eff m
  ca_witness := fun i m => getpeername_witness (fd32 (in_arg i 0)) m
  ca_sound_ok := fun i eff m m' evs H => check_getpeername_sound_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_getpeername_sound_unmodeled (fd32 (in_arg i 0)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_getpeername_complete_ok (fd32 (in_arg i 0)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_getpeername_complete_unmodeled (fd32 (in_arg i 0)) m i eff H
  ca_receptive := fun i m => getpeername_witness_ok (fd32 (in_arg i 0)) i m

/-- sendto (206). -/
def arm_sendto : CheckedArm where
  ca_arm := SpecArm.mk 206 (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m
  ca_witness := fun i m => sendto_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m
  ca_sound_ok := fun i eff m m' evs H => check_sendto_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_sendto_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_sendto_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_sendto_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m eff H
  ca_receptive := fun i m => sendto_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

/-- recvfrom (207). -/
def arm_recvfrom : CheckedArm where
  ca_arm := SpecArm.mk 207 (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_recvfrom_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_recvfrom_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_recvfrom_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_recvfrom_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => recvfrom_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- setsockopt (208). -/
def arm_setsockopt : CheckedArm where
  ca_arm := SpecArm.mk 208 (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i)
  ca_check := fun i eff m => check_setsockopt (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m
  ca_witness := fun i m => setsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) m
  ca_sound_ok := fun i eff m m' evs H => check_setsockopt_sound_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_setsockopt_sound_unmodeled (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_setsockopt_complete_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_setsockopt_complete_unmodeled (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) m i eff H
  ca_receptive := fun i m => setsockopt_witness_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i m

/-- getsockopt (209). -/
def arm_getsockopt : CheckedArm where
  ca_arm := SpecArm.mk 209 (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i)
  ca_check := fun i eff m => check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m
  ca_witness := fun i m => getsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m
  ca_sound_ok := fun i eff m m' evs H => check_getsockopt_sound_ok i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_getsockopt_sound_unmodeled i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_getsockopt_complete_ok i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_getsockopt_complete_unmodeled i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) m eff H
  ca_receptive := fun i m => getsockopt_witness_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m

/-- shutdown (210). -/
def arm_shutdown : CheckedArm where
  ca_arm := SpecArm.mk 210 (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i)
  ca_check := fun i eff m => check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m
  ca_witness := fun i m => shutdown_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) m
  ca_sound_ok := fun i eff m m' evs H => check_shutdown_sound_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_shutdown_sound_unmodeled (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_shutdown_complete_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_shutdown_complete_unmodeled (fd32 (in_arg i 0)) (int32 (in_arg i 1)) m i eff H
  ca_receptive := fun i m => shutdown_witness_ok (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i m

/-- sendmsg (211). -/
def arm_sendmsg : CheckedArm where
  ca_arm := SpecArm.mk 211 (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => sendmsg_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_sendmsg_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_sendmsg_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_sendmsg_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_sendmsg_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => sendmsg_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m

/-- recvmsg (212). -/
def arm_recvmsg : CheckedArm where
  ca_arm := SpecArm.mk 212 (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i)
  ca_check := fun i eff m => check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m
  ca_witness := fun i m => recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_recvmsg_sound_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_recvmsg_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_recvmsg_complete_ok (fd32 (in_arg i 0)) (in_arg i 2) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_recvmsg_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 2) m eff i H
  ca_receptive := fun i m => recvmsg_witness_ok (fd32 (in_arg i 0)) (in_arg i 2) i m

/-- brk (214). -/
def arm_brk : CheckedArm where
  ca_arm := SpecArm.mk 214 (fun i => brk_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_brk (in_arg i 0) eff m
  ca_witness := fun i m => brk_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs H => check_brk_sound_ok (in_arg i 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_brk_sound_unmodeled (in_arg i 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_brk_complete_ok (in_arg i 0) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_brk_complete_unmodeled (in_arg i 0) m i eff H
  ca_receptive := fun i m => brk_witness_ok (in_arg i 0) i m

/-- munmap (215). -/
def arm_munmap : CheckedArm where
  ca_arm := SpecArm.mk 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => check_munmap (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => munmap_witness (in_arg i 0) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_munmap_sound_ok (in_arg i 0) (in_arg i 1) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_munmap_sound_unmodeled (in_arg i 0) (in_arg i 1) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_munmap_complete_ok (in_arg i 0) (in_arg i 1) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_munmap_complete_unmodeled (in_arg i 0) (in_arg i 1) m i eff H
  ca_receptive := fun i m => munmap_witness_ok (in_arg i 0) (in_arg i 1) i m

/-- mremap (216). -/
def arm_mremap : CheckedArm where
  ca_arm := SpecArm.mk 216 (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m
  ca_sound_ok := fun i eff m m' evs H => check_mremap_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_mremap_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_mremap_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_mremap_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m i eff H
  ca_receptive := fun i m => mremap_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- clone (220). -/
def arm_clone : CheckedArm where
  ca_arm := SpecArm.mk 220 (fun i => clone_spec (in_arg i 0) i)
  ca_check := fun i eff m => check_clone (in_arg i 0) eff m
  ca_witness := fun i m => clone_witness (in_arg i 0) m
  ca_sound_ok := fun i eff m m' evs H => check_clone_sound_ok (in_arg i 0) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_clone_sound_unmodeled (in_arg i 0) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_clone_complete_ok (in_arg i 0) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_clone_complete_unmodeled (in_arg i 0) m i eff H
  ca_receptive := fun i m => clone_witness_ok (in_arg i 0) i m

/-- mmap (222). -/
def arm_mmap : CheckedArm where
  ca_arm := SpecArm.mk 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i)
  ca_check := fun i eff m => check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m
  ca_witness := fun i m => mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m
  ca_sound_ok := fun i eff m m' evs H => check_mmap_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_mmap_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_mmap_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_mmap_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m i eff H
  ca_receptive := fun i m => mmap_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m

/-- mprotect (226). -/
def arm_mprotect : CheckedArm where
  ca_arm := SpecArm.mk 226 (fun i => mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  ca_sound_ok := fun i eff m m' evs H => check_mprotect_sound_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_mprotect_sound_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_mprotect_complete_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_mprotect_complete_unmodeled (in_arg i 0) (in_arg i 1) (in_arg i 2) m i eff H
  ca_receptive := fun i m => mprotect_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i m

/-- madvise (233). -/
def arm_madvise : CheckedArm where
  ca_arm := SpecArm.mk 233 (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i)
  ca_check := fun i eff m => check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m
  ca_witness := fun i m => madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m
  ca_sound_ok := fun i eff m m' evs H => check_madvise_sound_ok (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_madvise_sound_unmodeled (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_madvise_complete_ok (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m m' evs i H
  ca_complete_unmodeled := fun i m eff H => check_madvise_complete_unmodeled (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m i eff H
  ca_receptive := fun i m => madvise_witness_ok (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m

/-- accept4 (242). -/
def arm_accept4 : CheckedArm where
  ca_arm := SpecArm.mk 242 (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m
  ca_sound_ok := fun i eff m m' evs H => check_accept4_sound_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i H
  ca_sound_unmodeled := fun i eff m H => check_accept4_sound_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m i H
  ca_complete_ok := fun i eff m m' evs H => check_accept4_complete_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_accept4_complete_unmodeled (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m eff H
  ca_receptive := fun i m => accept4_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- wait4 (260). -/
def arm_wait4 : CheckedArm where
  ca_arm := SpecArm.mk 260 (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i)
  ca_check := fun i eff m => check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m
  ca_witness := fun i m => wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_wait4_sound_ok i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_wait4_sound_unmodeled i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_wait4_complete_ok i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_wait4_complete_unmodeled i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) m eff H
  ca_receptive := fun i m => wait4_witness_ok (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m

/-- prlimit64 (261). -/
def arm_prlimit64 : CheckedArm where
  ca_arm := SpecArm.mk 261 (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_prlimit64_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_prlimit64_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_prlimit64_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_prlimit64_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => prlimit64_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- getrandom (278). -/
def arm_getrandom : CheckedArm where
  ca_arm := SpecArm.mk 278 (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i)
  ca_check := fun i eff m => check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m
  ca_witness := fun i m => getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m
  ca_sound_ok := fun i eff m m' evs H => check_getrandom_sound_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_getrandom_sound_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_getrandom_complete_ok i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_getrandom_complete_unmodeled i (in_arg i 0) (in_arg i 1) (in_arg i 2) m eff H
  ca_receptive := fun i m => getrandom_witness_ok (in_arg i 0) (in_arg i 1) (in_arg i 2) i m

/-- clone3 (435). -/
def arm_clone3 : CheckedArm where
  ca_arm := SpecArm.mk 435 (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i)
  ca_check := fun i eff m => check_clone3 i (in_arg i 0) (in_arg i 1) eff m
  ca_witness := fun i m => clone3_witness i (in_arg i 0) (in_arg i 1) m
  ca_sound_ok := fun i eff m m' evs H => check_clone3_sound_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_clone3_sound_unmodeled i (in_arg i 0) (in_arg i 1) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_clone3_complete_ok i (in_arg i 0) (in_arg i 1) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_clone3_complete_unmodeled i (in_arg i 0) (in_arg i 1) m eff H
  ca_receptive := fun i m => clone3_witness_ok i (in_arg i 0) (in_arg i 1) m

/-- faccessat2 (439). -/
def arm_faccessat2 : CheckedArm where
  ca_arm := SpecArm.mk 439 (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i)
  ca_check := fun i eff m => check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m
  ca_witness := fun i m => faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m
  ca_sound_ok := fun i eff m m' evs H => check_faccessat2_sound_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_sound_unmodeled := fun i eff m H => check_faccessat2_sound_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m H
  ca_complete_ok := fun i eff m m' evs H => check_faccessat2_complete_ok i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs H
  ca_complete_unmodeled := fun i m eff H => check_faccessat2_complete_unmodeled i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) m eff H
  ca_receptive := fun i m => faccessat2_witness_ok (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m

/-- The 90 modeled syscalls, one checked arm each, sorted by syscall number --
    the same order, and the same 90 numbers, as `Sys.SyscallTable.spec_table`. -/
def checked_table : List CheckedArm :=
  [ arm_getcwd,
    arm_eventfd2,
    arm_epoll_create1,
    arm_epoll_ctl,
    arm_epoll_pwait,
    arm_dup,
    arm_dup3,
    arm_fcntl,
    arm_ioctl,
    arm_flock,
    arm_unlinkat,
    arm_ftruncate,
    arm_faccessat,
    arm_openat,
    arm_close,
    arm_pipe2,
    arm_getdents64,
    arm_lseek,
    arm_read,
    arm_write,
    arm_readv,
    arm_writev,
    arm_pread64,
    arm_pwrite64,
    arm_pselect6,
    arm_ppoll,
    arm_readlinkat,
    arm_newfstatat,
    arm_fstat,
    arm_fsync,
    arm_fdatasync,
    arm_timerfd_create,
    arm_exit,
    arm_exit_group,
    arm_set_tid_address,
    arm_futex,
    arm_nanosleep,
    arm_clock_gettime,
    arm_sched_setscheduler,
    arm_sched_getaffinity,
    arm_sched_yield,
    arm_tkill,
    arm_tgkill,
    arm_sigaltstack,
    arm_rt_sigaction,
    arm_rt_sigprocmask,
    arm_setgid,
    arm_setuid,
    arm_setresuid,
    arm_setresgid,
    arm_setsid,
    arm_getgroups,
    arm_setgroups,
    arm_uname,
    arm_prctl,
    arm_gettimeofday,
    arm_getpid,
    arm_getuid,
    arm_geteuid,
    arm_getgid,
    arm_getegid,
    arm_gettid,
    arm_socket,
    arm_socketpair,
    arm_bind,
    arm_listen,
    arm_accept,
    arm_connect,
    arm_getsockname,
    arm_getpeername,
    arm_sendto,
    arm_recvfrom,
    arm_setsockopt,
    arm_getsockopt,
    arm_shutdown,
    arm_sendmsg,
    arm_recvmsg,
    arm_brk,
    arm_munmap,
    arm_mremap,
    arm_clone,
    arm_mmap,
    arm_mprotect,
    arm_madvise,
    arm_accept4,
    arm_wait4,
    arm_prlimit64,
    arm_getrandom,
    arm_clone3,
    arm_faccessat2 ]

/- =========================================================================
   The two tables describe the same surface.

   `rfl` rather than a proof: each `CheckedArm` was built around the very
   `SpecArm` the spec table lists, so if this ever fails the two lists have
   drifted, which is exactly the failure the single-table design exists to
   prevent.
   ========================================================================= -/

theorem checked_table_arms : checked_table.map CheckedArm.ca_arm = spec_table := rfl

/- =========================================================================
   Each arm's three components, pointwise, so a proof that has resolved the
   lookup can get back to the plain `check_*` / `*_witness` / `*_spec` shape
   it was written against.  Every one is `rfl`: the arm IS that component,
   and these only give `simp` a handle on a constant it will not unfold on
   its own.

   Registered for `simp`, so a caller writes `arm_dispatch` (§4) and does
   not have to name the syscall.

   `ca_no_arm_*` is what makes the LOOKUP compute: the `refine`-built
   constants do not unfold, so the numbers need their own handles --
   without them the dispatch is stuck at `ca_no arm_ioctl =? 64` with
   neither side able to move.
   ========================================================================= -/

@[simp] theorem ca_check_arm_getcwd (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getcwd i eff m = check_getcwd (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_getcwd (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getcwd i m = getcwd_witness (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_getcwd (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getcwd).sa_spec i m o = getcwd_spec (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_getcwd : ca_no arm_getcwd = 17 := rfl

@[simp] theorem ca_check_arm_eventfd2 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_eventfd2 i eff m = check_eventfd2 (flag32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_eventfd2 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_eventfd2 i m = eventfd2_witness (flag32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_eventfd2 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_eventfd2).sa_spec i m o = eventfd2_spec (flag32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_eventfd2 : ca_no arm_eventfd2 = 19 := rfl

@[simp] theorem ca_check_arm_epoll_create1 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_epoll_create1 i eff m = check_epoll_create1 (flag32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_epoll_create1 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_epoll_create1 i m = epoll_create1_witness (flag32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_epoll_create1 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_epoll_create1).sa_spec i m o = epoll_create1_spec (flag32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_epoll_create1 : ca_no arm_epoll_create1 = 20 := rfl

@[simp] theorem ca_check_arm_epoll_ctl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_epoll_ctl i eff m = check_epoll_ctl i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_epoll_ctl (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_epoll_ctl i m = epoll_ctl_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_epoll_ctl (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_epoll_ctl).sa_spec i m o = epoll_ctl_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (fd32 (in_arg i 2)) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_epoll_ctl : ca_no arm_epoll_ctl = 21 := rfl

@[simp] theorem ca_check_arm_epoll_pwait (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_epoll_pwait i eff m = check_epoll_pwait i (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) eff m := rfl

@[simp] theorem ca_witness_arm_epoll_pwait (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_epoll_pwait i m = epoll_pwait_witness (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m := rfl

@[simp] theorem sa_spec_arm_epoll_pwait (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_epoll_pwait).sa_spec i m o = epoll_pwait_spec (fd32 (in_arg i 0)) (in_arg i 1) (int32 (in_arg i 2)) (in_arg i 4) (in_arg i 5) i m o := rfl

@[simp] theorem ca_no_arm_epoll_pwait : ca_no arm_epoll_pwait = 22 := rfl

@[simp] theorem ca_check_arm_dup (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_dup i eff m = check_dup (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_dup (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_dup i m = dup_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_dup (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_dup).sa_spec i m o = dup_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_dup : ca_no arm_dup = 23 := rfl

@[simp] theorem ca_check_arm_dup3 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_dup3 i eff m = check_dup3 (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_dup3 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_dup3 i m = dup3_witness (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_dup3 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_dup3).sa_spec i m o = dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_dup3 : ca_no arm_dup3 = 24 := rfl

@[simp] theorem ca_check_arm_fcntl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_fcntl i eff m = check_fcntl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_fcntl (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_fcntl i m = fcntl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_fcntl (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_fcntl).sa_spec i m o = fcntl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_fcntl : ca_no arm_fcntl = 25 := rfl

@[simp] theorem ca_check_arm_ioctl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_ioctl i eff m = check_ioctl (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_ioctl (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_ioctl i m = ioctl_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_ioctl (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_ioctl).sa_spec i m o = ioctl_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_ioctl : ca_no arm_ioctl = 29 := rfl

@[simp] theorem ca_check_arm_flock (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_flock i eff m = check_flock (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_flock (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_flock i m = flock_witness (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_flock (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_flock).sa_spec i m o = flock_spec (fd32 (in_arg i 0)) (cmd32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_flock : ca_no arm_flock = 32 := rfl

@[simp] theorem ca_check_arm_unlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_unlinkat i eff m = check_unlinkat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_unlinkat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_unlinkat i m = unlinkat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_unlinkat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_unlinkat).sa_spec i m o = unlinkat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_unlinkat : ca_no arm_unlinkat = 35 := rfl

@[simp] theorem ca_check_arm_ftruncate (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_ftruncate i eff m = check_ftruncate (fd32 (in_arg i 0)) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_ftruncate (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_ftruncate i m = ftruncate_witness (fd32 (in_arg i 0)) (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_ftruncate (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_ftruncate).sa_spec i m o = ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_ftruncate : ca_no arm_ftruncate = 46 := rfl

@[simp] theorem ca_check_arm_faccessat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_faccessat i eff m = check_faccessat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_faccessat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_faccessat i m = faccessat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_faccessat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_faccessat).sa_spec i m o = faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_faccessat : ca_no arm_faccessat = 48 := rfl

@[simp] theorem ca_check_arm_openat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_openat i eff m = check_openat i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_openat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_openat i m = openat_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_openat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_openat).sa_spec i m o = openat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_openat : ca_no arm_openat = 56 := rfl

@[simp] theorem ca_check_arm_close (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_close i eff m = check_close (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_close (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_close i m = close_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_close (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_close).sa_spec i m o = close_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_close : ca_no arm_close = 57 := rfl

@[simp] theorem ca_check_arm_pipe2 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_pipe2 i eff m = check_pipe2 i (in_arg i 0) (pipe_flags32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_pipe2 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_pipe2 i m = pipe2_witness (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m := rfl

@[simp] theorem sa_spec_arm_pipe2 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_pipe2).sa_spec i m o = pipe2_spec (in_arg i 0) (pipe_flags32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_pipe2 : ca_no arm_pipe2 = 59 := rfl

@[simp] theorem ca_check_arm_getdents64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getdents64 i eff m = check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_getdents64 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getdents64 i m = getdents64_witness (fd32 (in_arg i 0)) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_getdents64 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getdents64).sa_spec i m o = getdents64_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_getdents64 : ca_no arm_getdents64 = 61 := rfl

@[simp] theorem ca_check_arm_lseek (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_lseek i eff m = check_lseek (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) eff m := rfl

@[simp] theorem ca_witness_arm_lseek (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_lseek i m = lseek_witness (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) m := rfl

@[simp] theorem sa_spec_arm_lseek (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_lseek).sa_spec i m o = lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i m o := rfl

@[simp] theorem ca_no_arm_lseek : ca_no arm_lseek = 62 := rfl

@[simp] theorem ca_check_arm_read (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_read i eff m = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_read (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_read i m = read_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_read (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_read).sa_spec i m o = read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_read : ca_no arm_read = 63 := rfl

@[simp] theorem ca_check_arm_write (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_write i eff m = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_write (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_write i m = write_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_write (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_write).sa_spec i m o = write_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_write : ca_no arm_write = 64 := rfl

@[simp] theorem ca_check_arm_readv (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_readv i eff m = check_readv i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_readv (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_readv i m = readv_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_readv (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_readv).sa_spec i m o = readv_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_readv : ca_no arm_readv = 65 := rfl

@[simp] theorem ca_check_arm_writev (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_writev i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_writev (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_writev i m = writev_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_writev (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_writev).sa_spec i m o = writev_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_writev : ca_no arm_writev = 66 := rfl

@[simp] theorem ca_check_arm_pread64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_pread64 i eff m = check_pread64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_pread64 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_pread64 i m = pread64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_pread64 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_pread64).sa_spec i m o = pread64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_pread64 : ca_no arm_pread64 = 67 := rfl

@[simp] theorem ca_check_arm_pwrite64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_pwrite64 i eff m = check_pwrite64 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_pwrite64 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_pwrite64 i m = pwrite64_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_pwrite64 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_pwrite64).sa_spec i m o = pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_pwrite64 : ca_no arm_pwrite64 = 68 := rfl

@[simp] theorem ca_check_arm_pselect6 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_pselect6 i eff m = check_pselect6 i (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := rfl

@[simp] theorem ca_witness_arm_pselect6 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_pselect6 i m = pselect6_witness i m (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) := rfl

@[simp] theorem sa_spec_arm_pselect6 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_pselect6).sa_spec i m o = pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl

@[simp] theorem ca_no_arm_pselect6 : ca_no arm_pselect6 = 72 := rfl

@[simp] theorem ca_check_arm_ppoll (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_ppoll i eff m = check_ppoll i (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m := rfl

@[simp] theorem ca_witness_arm_ppoll (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_ppoll i m = ppoll_witness i m (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) := rfl

@[simp] theorem sa_spec_arm_ppoll (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_ppoll).sa_spec i m o = ppoll_spec (in_arg i 0) (unfds32 (in_arg i 1)) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m o := rfl

@[simp] theorem ca_no_arm_ppoll : ca_no arm_ppoll = 73 := rfl

@[simp] theorem ca_check_arm_readlinkat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_readlinkat i eff m = check_readlinkat (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_readlinkat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_readlinkat i m = readlinkat_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_readlinkat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_readlinkat).sa_spec i m o = readlinkat_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_readlinkat : ca_no arm_readlinkat = 78 := rfl

@[simp] theorem ca_check_arm_newfstatat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_newfstatat i eff m = check_newfstatat i (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) eff m := rfl

@[simp] theorem ca_witness_arm_newfstatat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_newfstatat i m = newfstatat_witness (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m := rfl

@[simp] theorem sa_spec_arm_newfstatat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_newfstatat).sa_spec i m o = newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m o := rfl

@[simp] theorem ca_no_arm_newfstatat : ca_no arm_newfstatat = 79 := rfl

@[simp] theorem ca_check_arm_fstat (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_fstat i eff m = check_fstat i (fd32 (in_arg i 0)) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_fstat (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_fstat i m = fstat_witness (fd32 (in_arg i 0)) (in_arg i 1) i m := rfl

@[simp] theorem sa_spec_arm_fstat (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_fstat).sa_spec i m o = fstat_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_fstat : ca_no arm_fstat = 80 := rfl

@[simp] theorem ca_check_arm_fsync (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_fsync i eff m = check_fsync (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_fsync (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_fsync i m = fsync_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_fsync (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_fsync).sa_spec i m o = fsync_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_fsync : ca_no arm_fsync = 82 := rfl

@[simp] theorem ca_check_arm_fdatasync (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_fdatasync i eff m = check_fsync (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_fdatasync (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_fdatasync i m = fsync_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_fdatasync (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_fdatasync).sa_spec i m o = fsync_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_fdatasync : ca_no arm_fdatasync = 83 := rfl

@[simp] theorem ca_check_arm_timerfd_create (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_timerfd_create i eff m = check_timerfd_create (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_timerfd_create (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_timerfd_create i m = timerfd_create_witness (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_timerfd_create (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_timerfd_create).sa_spec i m o = timerfd_create_spec (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_timerfd_create : ca_no arm_timerfd_create = 85 := rfl

@[simp] theorem ca_check_arm_exit (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_exit i eff m = check_exit (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_exit (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_exit i m = exit_witness (in_arg i 0) m := rfl

@[simp] theorem sa_spec_arm_exit (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_exit).sa_spec i m o = exit_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_exit : ca_no arm_exit = 93 := rfl

@[simp] theorem ca_check_arm_exit_group (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_exit_group i eff m = check_exit (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_exit_group (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_exit_group i m = exit_witness (in_arg i 0) m := rfl

@[simp] theorem sa_spec_arm_exit_group (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_exit_group).sa_spec i m o = exit_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_exit_group : ca_no arm_exit_group = 94 := rfl

@[simp] theorem ca_check_arm_set_tid_address (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_set_tid_address i eff m = check_set_tid_address eff m := rfl

@[simp] theorem ca_witness_arm_set_tid_address (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_set_tid_address i m = set_tid_address_witness m := rfl

@[simp] theorem sa_spec_arm_set_tid_address (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_set_tid_address).sa_spec i m o = set_tid_address_spec i m o := rfl

@[simp] theorem ca_no_arm_set_tid_address : ca_no arm_set_tid_address = 96 := rfl

@[simp] theorem ca_check_arm_futex (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_futex i eff m = check_futex i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_futex (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_futex i m = futex_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_futex (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_futex).sa_spec i m o = futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_futex : ca_no arm_futex = 98 := rfl

@[simp] theorem ca_check_arm_nanosleep (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_nanosleep i eff m = check_nanosleep i (in_arg i 0) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_nanosleep (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_nanosleep i m = nanosleep_witness (in_arg i 0) (in_arg i 1) i m := rfl

@[simp] theorem sa_spec_arm_nanosleep (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_nanosleep).sa_spec i m o = nanosleep_spec (in_arg i 0) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_nanosleep : ca_no arm_nanosleep = 101 := rfl

@[simp] theorem ca_check_arm_clock_gettime (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_clock_gettime i eff m = check_clock_gettime i (clockid32 (in_arg i 0)) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_clock_gettime (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_clock_gettime i m = clock_gettime_witness (clockid32 (in_arg i 0)) (in_arg i 1) i m := rfl

@[simp] theorem sa_spec_arm_clock_gettime (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_clock_gettime).sa_spec i m o = clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_clock_gettime : ca_no arm_clock_gettime = 113 := rfl

@[simp] theorem ca_check_arm_sched_setscheduler (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sched_setscheduler i eff m = check_sched_setscheduler i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_sched_setscheduler (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sched_setscheduler i m = sched_setscheduler_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_sched_setscheduler (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sched_setscheduler).sa_spec i m o = sched_setscheduler_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_sched_setscheduler : ca_no arm_sched_setscheduler = 119 := rfl

attribute [local semireducible] sched_setscheduler_spec check_sched_setscheduler sched_setscheduler_witness

@[simp] theorem ca_check_arm_sched_getaffinity (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sched_getaffinity i eff m = check_sched_getaffinity (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_sched_getaffinity (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sched_getaffinity i m = sched_getaffinity_witness (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_sched_getaffinity (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sched_getaffinity).sa_spec i m o = sched_getaffinity_spec (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_sched_getaffinity : ca_no arm_sched_getaffinity = 123 := rfl

@[simp] theorem ca_check_arm_sched_yield (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sched_yield i eff m = check_sched_yield eff m := rfl

@[simp] theorem ca_witness_arm_sched_yield (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sched_yield i m = sched_yield_witness m := rfl

@[simp] theorem sa_spec_arm_sched_yield (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sched_yield).sa_spec i m o = sched_yield_spec i m o := rfl

@[simp] theorem ca_no_arm_sched_yield : ca_no arm_sched_yield = 124 := rfl

@[simp] theorem ca_check_arm_tkill (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_tkill i eff m = check_tkill (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_tkill (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_tkill i m = tkill_witness (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_tkill (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_tkill).sa_spec i m o = tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_tkill : ca_no arm_tkill = 130 := rfl

@[simp] theorem ca_check_arm_tgkill (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_tgkill i eff m = check_tgkill (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) eff m := rfl

@[simp] theorem ca_witness_arm_tgkill (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_tgkill i m = tgkill_witness (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) m := rfl

@[simp] theorem sa_spec_arm_tgkill (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_tgkill).sa_spec i m o = tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i m o := rfl

@[simp] theorem ca_no_arm_tgkill : ca_no arm_tgkill = 131 := rfl

@[simp] theorem ca_check_arm_sigaltstack (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sigaltstack i eff m = check_sigaltstack i (in_arg i 0) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_sigaltstack (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sigaltstack i m = sigaltstack_witness (in_arg i 0) (in_arg i 1) i m := rfl

@[simp] theorem sa_spec_arm_sigaltstack (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sigaltstack).sa_spec i m o = sigaltstack_spec (in_arg i 0) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_sigaltstack : ca_no arm_sigaltstack = 132 := rfl

@[simp] theorem ca_check_arm_rt_sigaction (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_rt_sigaction i eff m = check_rt_sigaction i (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_rt_sigaction (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_rt_sigaction i m = rt_sigaction_witness (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_rt_sigaction (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_rt_sigaction).sa_spec i m o = rt_sigaction_spec (sig32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_rt_sigaction : ca_no arm_rt_sigaction = 134 := rfl

@[simp] theorem ca_check_arm_rt_sigprocmask (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_rt_sigprocmask i eff m = check_rt_sigprocmask i (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_rt_sigprocmask (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_rt_sigprocmask i m = rt_sigprocmask_witness (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_rt_sigprocmask (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_rt_sigprocmask).sa_spec i m o = rt_sigprocmask_spec (how32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_rt_sigprocmask : ca_no arm_rt_sigprocmask = 135 := rfl

@[simp] theorem ca_check_arm_setgid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setgid i eff m = check_setid cred_gids set_cred_gids false (uid32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_setgid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setgid i m = setid_witness (uid32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_setgid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setgid).sa_spec i m o = setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_setgid : ca_no arm_setgid = 144 := rfl

@[simp] theorem ca_check_arm_setuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setuid i eff m = check_setid cred_uids set_cred_uids true (uid32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_setuid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setuid i m = setid_witness (uid32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_setuid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setuid).sa_spec i m o = setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_setuid : ca_no arm_setuid = 146 := rfl

@[simp] theorem ca_check_arm_setresuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setresuid i eff m = check_setresid cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := rfl

@[simp] theorem ca_witness_arm_setresuid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setresuid i m = setresid_witness cred_uids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := rfl

@[simp] theorem sa_spec_arm_setresuid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setresuid).sa_spec i m o = setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o := rfl

@[simp] theorem ca_no_arm_setresuid : ca_no arm_setresuid = 147 := rfl

@[simp] theorem ca_check_arm_setresgid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setresgid i eff m = check_setresid cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) eff m := rfl

@[simp] theorem ca_witness_arm_setresgid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setresgid i m = setresid_witness cred_gids (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) m := rfl

@[simp] theorem sa_spec_arm_setresgid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setresgid).sa_spec i m o = setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i m o := rfl

@[simp] theorem ca_no_arm_setresgid : ca_no arm_setresgid = 149 := rfl

@[simp] theorem ca_check_arm_setsid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setsid i eff m = check_setsid eff m := rfl

@[simp] theorem ca_witness_arm_setsid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setsid i m = setsid_witness m := rfl

@[simp] theorem sa_spec_arm_setsid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setsid).sa_spec i m o = setsid_spec i m o := rfl

@[simp] theorem ca_no_arm_setsid : ca_no arm_setsid = 157 := rfl

@[simp] theorem ca_check_arm_getgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getgroups i eff m = check_getgroups (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_getgroups (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getgroups i m = getgroups_witness (in_arg i 0) m := rfl

@[simp] theorem sa_spec_arm_getgroups (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getgroups).sa_spec i m o = getgroups_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_getgroups : ca_no arm_getgroups = 158 := rfl

attribute [local semireducible] getgroups_spec check_getgroups getgroups_witness

@[simp] theorem ca_check_arm_setgroups (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setgroups i eff m = check_setgroups eff m := rfl

@[simp] theorem ca_witness_arm_setgroups (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setgroups i m = setgroups_witness m := rfl

@[simp] theorem sa_spec_arm_setgroups (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setgroups).sa_spec i m o = setgroups_spec i m o := rfl

@[simp] theorem ca_no_arm_setgroups : ca_no arm_setgroups = 159 := rfl

@[simp] theorem ca_check_arm_uname (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_uname i eff m = check_uname i (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_uname (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_uname i m = uname_witness (in_arg i 0) i m := rfl

@[simp] theorem sa_spec_arm_uname (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_uname).sa_spec i m o = uname_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_uname : ca_no arm_uname = 160 := rfl

@[simp] theorem ca_check_arm_prctl (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_prctl i eff m = check_prctl (int32 (in_arg i 0)) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_prctl (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_prctl i m = prctl_witness (int32 (in_arg i 0)) (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_prctl (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_prctl).sa_spec i m o = prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_prctl : ca_no arm_prctl = 167 := rfl

@[simp] theorem ca_check_arm_gettimeofday (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_gettimeofday i eff m = check_gettimeofday i (in_arg i 0) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_gettimeofday (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_gettimeofday i m = gettimeofday_witness (in_arg i 0) (in_arg i 1) i m := rfl

@[simp] theorem sa_spec_arm_gettimeofday (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_gettimeofday).sa_spec i m o = gettimeofday_spec (in_arg i 0) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_gettimeofday : ca_no arm_gettimeofday = 169 := rfl

@[simp] theorem ca_check_arm_getpid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getpid i eff m = check_getpid eff m := rfl

@[simp] theorem ca_witness_arm_getpid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getpid i m = getpid_witness m := rfl

@[simp] theorem sa_spec_arm_getpid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getpid).sa_spec i m o = getpid_spec i m o := rfl

@[simp] theorem ca_no_arm_getpid : ca_no arm_getpid = 172 := rfl

@[simp] theorem ca_check_arm_getuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getuid i eff m = check_getid Creds.cr_uid eff m := rfl

@[simp] theorem ca_witness_arm_getuid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getuid i m = getid_witness Creds.cr_uid m := rfl

@[simp] theorem sa_spec_arm_getuid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getuid).sa_spec i m o = getid_spec Creds.cr_uid i m o := rfl

@[simp] theorem ca_no_arm_getuid : ca_no arm_getuid = 174 := rfl

@[simp] theorem ca_check_arm_geteuid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_geteuid i eff m = check_getid Creds.cr_euid eff m := rfl

@[simp] theorem ca_witness_arm_geteuid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_geteuid i m = getid_witness Creds.cr_euid m := rfl

@[simp] theorem sa_spec_arm_geteuid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_geteuid).sa_spec i m o = getid_spec Creds.cr_euid i m o := rfl

@[simp] theorem ca_no_arm_geteuid : ca_no arm_geteuid = 175 := rfl

@[simp] theorem ca_check_arm_getgid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getgid i eff m = check_getid Creds.cr_gid eff m := rfl

@[simp] theorem ca_witness_arm_getgid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getgid i m = getid_witness Creds.cr_gid m := rfl

@[simp] theorem sa_spec_arm_getgid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getgid).sa_spec i m o = getid_spec Creds.cr_gid i m o := rfl

@[simp] theorem ca_no_arm_getgid : ca_no arm_getgid = 176 := rfl

@[simp] theorem ca_check_arm_getegid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getegid i eff m = check_getid Creds.cr_egid eff m := rfl

@[simp] theorem ca_witness_arm_getegid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getegid i m = getid_witness Creds.cr_egid m := rfl

@[simp] theorem sa_spec_arm_getegid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getegid).sa_spec i m o = getid_spec Creds.cr_egid i m o := rfl

@[simp] theorem ca_no_arm_getegid : ca_no arm_getegid = 177 := rfl

@[simp] theorem ca_check_arm_gettid (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_gettid i eff m = check_gettid eff m := rfl

@[simp] theorem ca_witness_arm_gettid (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_gettid i m = gettid_witness m := rfl

@[simp] theorem sa_spec_arm_gettid (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_gettid).sa_spec i m o = gettid_spec i m o := rfl

@[simp] theorem ca_no_arm_gettid : ca_no arm_gettid = 178 := rfl

@[simp] theorem ca_check_arm_socket (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_socket i eff m = check_socket (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_socket (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_socket i m = socket_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_socket (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_socket).sa_spec i m o = socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_socket : ca_no arm_socket = 198 := rfl

@[simp] theorem ca_check_arm_socketpair (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_socketpair i eff m = check_socketpair i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_socketpair (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_socketpair i m = socketpair_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_socketpair (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_socketpair).sa_spec i m o = socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_socketpair : ca_no arm_socketpair = 199 := rfl

@[simp] theorem ca_check_arm_bind (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_bind i eff m = check_bind i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_bind (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_bind i m = bind_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_bind (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_bind).sa_spec i m o = bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_bind : ca_no arm_bind = 200 := rfl

@[simp] theorem ca_check_arm_listen (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_listen i eff m = check_listen (fd32 (in_arg i 0)) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_listen (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_listen i m = listen_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_listen (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_listen).sa_spec i m o = listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_listen : ca_no arm_listen = 201 := rfl

@[simp] theorem ca_check_arm_accept (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_accept i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) eff m := rfl

@[simp] theorem ca_witness_arm_accept (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_accept i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (BitVec.ofInt 64 0) m := rfl

@[simp] theorem sa_spec_arm_accept (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_accept).sa_spec i m o = accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (BitVec.ofInt 64 0) i m o := rfl

@[simp] theorem ca_no_arm_accept : ca_no arm_accept = 202 := rfl

@[simp] theorem ca_check_arm_connect (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_connect i eff m = check_connect i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_connect (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_connect i m = connect_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_connect (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_connect).sa_spec i m o = connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_connect : ca_no arm_connect = 203 := rfl

@[simp] theorem ca_check_arm_getsockname (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getsockname i eff m = check_getsockname (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_getsockname (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getsockname i m = getsockname_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_getsockname (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getsockname).sa_spec i m o = getsockname_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_getsockname : ca_no arm_getsockname = 204 := rfl

@[simp] theorem ca_check_arm_getpeername (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getpeername i eff m = check_getpeername (fd32 (in_arg i 0)) eff m := rfl

@[simp] theorem ca_witness_arm_getpeername (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getpeername i m = getpeername_witness (fd32 (in_arg i 0)) m := rfl

@[simp] theorem sa_spec_arm_getpeername (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getpeername).sa_spec i m o = getpeername_spec (fd32 (in_arg i 0)) i m o := rfl

@[simp] theorem ca_no_arm_getpeername : ca_no arm_getpeername = 205 := rfl

@[simp] theorem ca_check_arm_sendto (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sendto i eff m = check_sendto i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) eff m := rfl

@[simp] theorem ca_witness_arm_sendto (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sendto i m = sendto_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) i m := rfl

@[simp] theorem sa_spec_arm_sendto (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sendto).sa_spec i m o = sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl

@[simp] theorem ca_no_arm_sendto : ca_no arm_sendto = 206 := rfl

@[simp] theorem ca_check_arm_recvfrom (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_recvfrom i eff m = check_recvfrom i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_recvfrom (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_recvfrom i m = recvfrom_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_recvfrom (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_recvfrom).sa_spec i m o = recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_recvfrom : ca_no arm_recvfrom = 207 := rfl

@[simp] theorem ca_check_arm_setsockopt (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_setsockopt i eff m = check_setsockopt (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) eff m := rfl

@[simp] theorem ca_witness_arm_setsockopt (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_setsockopt i m = setsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) m := rfl

@[simp] theorem sa_spec_arm_setsockopt (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_setsockopt).sa_spec i m o = setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i m o := rfl

@[simp] theorem ca_no_arm_setsockopt : ca_no arm_setsockopt = 208 := rfl

@[simp] theorem ca_check_arm_getsockopt (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getsockopt i eff m = check_getsockopt i (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) eff m := rfl

@[simp] theorem ca_witness_arm_getsockopt (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getsockopt i m = getsockopt_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m := rfl

@[simp] theorem sa_spec_arm_getsockopt (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getsockopt).sa_spec i m o = getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i m o := rfl

@[simp] theorem ca_no_arm_getsockopt : ca_no arm_getsockopt = 209 := rfl

@[simp] theorem ca_check_arm_shutdown (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_shutdown i eff m = check_shutdown (fd32 (in_arg i 0)) (int32 (in_arg i 1)) eff m := rfl

@[simp] theorem ca_witness_arm_shutdown (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_shutdown i m = shutdown_witness (fd32 (in_arg i 0)) (int32 (in_arg i 1)) m := rfl

@[simp] theorem sa_spec_arm_shutdown (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_shutdown).sa_spec i m o = shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i m o := rfl

@[simp] theorem ca_no_arm_shutdown : ca_no arm_shutdown = 210 := rfl

@[simp] theorem ca_check_arm_sendmsg (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_sendmsg i eff m = check_sendmsg i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_sendmsg (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_sendmsg i m = sendmsg_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_sendmsg (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_sendmsg).sa_spec i m o = sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_sendmsg : ca_no arm_sendmsg = 211 := rfl

@[simp] theorem ca_check_arm_recvmsg (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_recvmsg i eff m = check_recvmsg (fd32 (in_arg i 0)) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_recvmsg (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_recvmsg i m = recvmsg_witness (fd32 (in_arg i 0)) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_recvmsg (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_recvmsg).sa_spec i m o = recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_recvmsg : ca_no arm_recvmsg = 212 := rfl

@[simp] theorem ca_check_arm_brk (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_brk i eff m = check_brk (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_brk (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_brk i m = brk_witness (in_arg i 0) m := rfl

@[simp] theorem sa_spec_arm_brk (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_brk).sa_spec i m o = brk_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_brk : ca_no arm_brk = 214 := rfl

@[simp] theorem ca_check_arm_munmap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_munmap i eff m = check_munmap (in_arg i 0) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_munmap (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_munmap i m = munmap_witness (in_arg i 0) (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_munmap (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_munmap).sa_spec i m o = munmap_spec (in_arg i 0) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_munmap : ca_no arm_munmap = 215 := rfl

@[simp] theorem ca_check_arm_mremap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_mremap i eff m = check_mremap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_mremap (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_mremap i m = mremap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m := rfl

@[simp] theorem sa_spec_arm_mremap (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_mremap).sa_spec i m o = mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_mremap : ca_no arm_mremap = 216 := rfl

@[simp] theorem ca_check_arm_clone (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_clone i eff m = check_clone (in_arg i 0) eff m := rfl

@[simp] theorem ca_witness_arm_clone (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_clone i m = clone_witness (in_arg i 0) m := rfl

@[simp] theorem sa_spec_arm_clone (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_clone).sa_spec i m o = clone_spec (in_arg i 0) i m o := rfl

@[simp] theorem ca_no_arm_clone : ca_no arm_clone = 220 := rfl

@[simp] theorem ca_check_arm_mmap (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_mmap i eff m = check_mmap (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) eff m := rfl

@[simp] theorem ca_witness_arm_mmap (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_mmap i m = mmap_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m := rfl

@[simp] theorem sa_spec_arm_mmap (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_mmap).sa_spec i m o = mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o := rfl

@[simp] theorem ca_no_arm_mmap : ca_no arm_mmap = 222 := rfl

@[simp] theorem ca_check_arm_mprotect (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_mprotect i eff m = check_mprotect (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_mprotect (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_mprotect i m = mprotect_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) m := rfl

@[simp] theorem sa_spec_arm_mprotect (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_mprotect).sa_spec i m o = mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_mprotect : ca_no arm_mprotect = 226 := rfl

@[simp] theorem ca_check_arm_madvise (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_madvise i eff m = check_madvise (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) eff m := rfl

@[simp] theorem ca_witness_arm_madvise (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_madvise i m = madvise_witness (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) m := rfl

@[simp] theorem sa_spec_arm_madvise (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_madvise).sa_spec i m o = madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i m o := rfl

@[simp] theorem ca_no_arm_madvise : ca_no arm_madvise = 233 := rfl

@[simp] theorem ca_check_arm_accept4 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_accept4 i eff m = check_accept4 (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_accept4 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_accept4 i m = accept4_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 3) m := rfl

@[simp] theorem sa_spec_arm_accept4 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_accept4).sa_spec i m o = accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_accept4 : ca_no arm_accept4 = 242 := rfl

@[simp] theorem ca_check_arm_wait4 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_wait4 i eff m = check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_wait4 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_wait4 i m = wait4_witness (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_wait4 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_wait4).sa_spec i m o = wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_wait4 : ca_no arm_wait4 = 260 := rfl

@[simp] theorem ca_check_arm_prlimit64 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_prlimit64 i eff m = check_prlimit64 i (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_prlimit64 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_prlimit64 i m = prlimit64_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_prlimit64 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_prlimit64).sa_spec i m o = prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_prlimit64 : ca_no arm_prlimit64 = 261 := rfl

@[simp] theorem ca_check_arm_getrandom (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_getrandom i eff m = check_getrandom i (in_arg i 0) (in_arg i 1) (in_arg i 2) eff m := rfl

@[simp] theorem ca_witness_arm_getrandom (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_getrandom i m = getrandom_witness (in_arg i 0) (in_arg i 1) (in_arg i 2) i m := rfl

@[simp] theorem sa_spec_arm_getrandom (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_getrandom).sa_spec i m o = getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o := rfl

@[simp] theorem ca_no_arm_getrandom : ca_no arm_getrandom = 278 := rfl

@[simp] theorem ca_check_arm_clone3 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_clone3 i eff m = check_clone3 i (in_arg i 0) (in_arg i 1) eff m := rfl

@[simp] theorem ca_witness_arm_clone3 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_clone3 i m = clone3_witness i (in_arg i 0) (in_arg i 1) m := rfl

@[simp] theorem sa_spec_arm_clone3 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_clone3).sa_spec i m o = clone3_spec (in_arg i 0) (in_arg i 1) i m o := rfl

@[simp] theorem ca_no_arm_clone3 : ca_no arm_clone3 = 435 := rfl

@[simp] theorem ca_check_arm_faccessat2 (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_faccessat2 i eff m = check_faccessat2 i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m := rfl

@[simp] theorem ca_witness_arm_faccessat2 (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_faccessat2 i m = faccessat2_witness (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m := rfl

@[simp] theorem sa_spec_arm_faccessat2 (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) :
    (CheckedArm.ca_arm arm_faccessat2).sa_spec i m o = faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o := rfl

@[simp] theorem ca_no_arm_faccessat2 : ca_no arm_faccessat2 = 439 := rfl

/- =========================================================================
   §3  The dispatcher's theorems, for ANY table

   `check_syscall`, the four soundness/completeness theorems,
   `syscall_spec_witness` and `receptive` are stated here over an arbitrary
   table `t` with the one fact the concrete table supplies --
   `t.map ca_arm = spec_table`, stated as `checked_table_arms` — because
   that is the whole content of the argument: the tables are the same
   surface, so the lookup agrees and the arm's field is the goal.
   Instantiated at the concrete table and its arm equality they are the
   concrete statements (`check_syscall t i eff m` becoming
   `check_syscall i eff m`); §4 does exactly that.  Nothing in them is
   specific to a syscall, and none of them grows when one is added.
   ========================================================================= -/

/-- Dispatch on the syscall number, through the one table the relational
    spec dispatches over as well.  The two cannot disagree about which
    numbers are modeled, because they read the same list. -/
def check_syscall (t : List CheckedArm) (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match lookup_ca t (i.in_sysno.toNat : Int) with
  | some c => c.ca_check i eff m
  | none => .CheckUnmodeled

/-- The witness for this input's syscall, from the same table the spec and
    the checker dispatch over.  A number with no arm has no witness and is
    `unmodeled` -- which is what `receptive` then has to show, once. -/
def syscall_spec_witness (t : List CheckedArm) (i : SyscallInput) (m : Model) :
    Outcome SyscallEffect Model event :=
  match lookup_ca t (i.in_sysno.toNat : Int) with
  | some c => c.ca_witness i m
  | none => .unmodeled

/-- `lookup_ca_arm` at a table that covers the spec table: the spec side's
    lookup and the checked side's are the same lookup.  Every proof below
    needs that rewrite; this is it, once. -/
theorem lookup_arm_of_map (t : List CheckedArm) (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) :
    lookup_arm spec_table (i.in_sysno.toNat : Int)
      = (lookup_ca t (i.in_sysno.toNat : Int)).map CheckedArm.ca_arm := by
  rw [← ht]
  exact lookup_ca_arm t _

/-- No arm in the checked lookup, no arm in the spec-side lookup either:
    the checked table covers the spec table.  This is the `none` branch of
    every theorem below, where `dispatch` falls through to `unmodeled`. -/
theorem lookup_arm_none_of_lookup_ca_none (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table) (i : SyscallInput)
    (h : lookup_ca t (i.in_sysno.toNat : Int) = none) :
    lookup_arm spec_table (i.in_sysno.toNat : Int) = none := by
  rw [lookup_arm_of_map t ht i, h]
  rfl

/-- `lookup_ca_arm` is what lets a goal about `Specs.syscall_spec` -- which
    dispatches over `spec_table` -- be closed by a `CheckedArm`'s field: the
    two tables are the same surface.  Both sides of every theorem below
    therefore turn on the SAME lookup, so each one is a destruct and a
    field.  None of the four mentions a syscall. -/
theorem check_syscall_sound_ok (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_syscall t i eff m = .CheckOk m' evs) :
    syscall_spec i m (.ok eff m' evs) := by
  cases h : lookup_ca t (i.in_sysno.toNat : Int) with
  | none =>
    have hnone := lookup_arm_none_of_lookup_ca_none t ht i h
    have : check_syscall t i eff m = .CheckUnmodeled := by simp [check_syscall, h]
    rw [this] at H
    cases H
  | some c =>
    have hsome := lookup_arm_of_map t ht i
    rw [h] at hsome
    exact (dispatch_arm spec_table i m (.ok eff m' evs) c.ca_arm hsome).mpr
      (c.ca_sound_ok i eff m m' evs (by simpa [check_syscall, h] using H))

/-- A `CheckUnmodeled` is the spec's `unmodeled`, for the arm the number
    selects -- or for the fail-closed fallback when it selects none. -/
theorem check_syscall_sound_unmodeled (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : check_syscall t i eff m = .CheckUnmodeled) :
    syscall_spec i m .unmodeled := by
  cases h : lookup_ca t (i.in_sysno.toNat : Int) with
  | none =>
    exact dispatch_unmodeled spec_table i m (lookup_arm_none_of_lookup_ca_none t ht i h)
  | some c =>
    have hsome := lookup_arm_of_map t ht i
    rw [h] at hsome
    exact (dispatch_arm spec_table i m .unmodeled c.ca_arm hsome).mpr
      (c.ca_sound_unmodeled i eff m (by simpa [check_syscall, h] using H))

/-- Completeness, `Ok` direction: an admitted outcome is checked to itself.
    With no arm answering, the spec is `unmodeled` and the hypothesis is
    absurd. -/
theorem check_syscall_complete_ok (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : syscall_spec i m (.ok eff m' evs)) :
    check_syscall t i eff m = .CheckOk m' evs := by
  cases h : lookup_ca t (i.in_sysno.toNat : Int) with
  | none =>
    have hnone := lookup_arm_none_of_lookup_ca_none t ht i h
    have hcontr : (Outcome.ok eff m' evs : Outcome SyscallEffect Model event) = .unmodeled := by
      simp only [syscall_spec, dispatch, unmodeled, hnone] at H
      exact H
    cases hcontr
  | some c =>
    have hsome := lookup_arm_of_map t ht i
    rw [h] at hsome
    have Hc : c.ca_arm.sa_spec i m (.ok eff m' evs) :=
      (dispatch_arm spec_table i m (.ok eff m' evs) c.ca_arm hsome).mp H
    simpa [check_syscall, h] using c.ca_complete_ok i eff m m' evs Hc

/-- Completeness, `unmodeled` direction. -/
theorem check_syscall_complete_unmodeled (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (H : syscall_spec i m .unmodeled) :
    check_syscall t i eff m = .CheckUnmodeled := by
  cases h : lookup_ca t (i.in_sysno.toNat : Int) with
  | none => simp [check_syscall, h]
  | some c =>
    have hsome := lookup_arm_of_map t ht i
    rw [h] at hsome
    have Hc : c.ca_arm.sa_spec i m .unmodeled :=
      (dispatch_arm spec_table i m .unmodeled c.ca_arm hsome).mp H
    simpa [check_syscall, h] using c.ca_complete_unmodeled i m eff Hc

/-- The checker decides the syscall body: `CheckOk` is exactly the spec's
    `Ok`, both ways. -/
theorem check_syscall_ok_iff (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event) :
    check_syscall t i eff m = .CheckOk m' evs ↔ syscall_spec i m (.ok eff m' evs) :=
  ⟨check_syscall_sound_ok t ht i eff m m' evs,
   check_syscall_complete_ok t ht i eff m m' evs⟩

/-- And `CheckUnmodeled` is exactly the spec's `unmodeled`, both ways. -/
theorem check_syscall_err_iff (t : List CheckedArm)
    (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall t i eff m = .CheckUnmodeled ↔ syscall_spec i m .unmodeled :=
  ⟨check_syscall_sound_unmodeled t ht i eff m,
   check_syscall_complete_unmodeled t ht i m eff⟩

/-- The dispatcher is receptive: `syscall_spec_witness t i m` is an
    admissible outcome for every input and model state.

    Receptivity in one lookup: the spec dispatches over `spec_table`, the
    witness over the checked table, and `ht` says those are the same
    surface -- so the arm that answers is the arm whose `ca_receptive`
    field is exactly this goal.  No case analysis over the numbers, and
    nothing here grows when a syscall is added. -/
theorem receptive (t : List CheckedArm) (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (m : Model) :
    syscall_spec i m (syscall_spec_witness t i m) := by
  cases h : lookup_ca t (i.in_sysno.toNat : Int) with
  | none =>
    have hnone := lookup_arm_none_of_lookup_ca_none t ht i h
    simpa [syscall_spec, syscall_spec_witness, h] using dispatch_unmodeled spec_table i m hnone
  | some c =>
    have hsome := lookup_arm_of_map t ht i
    rw [h] at hsome
    simpa [syscall_spec, syscall_spec_witness, h] using
      (dispatch_arm spec_table i m (c.ca_witness i m) c.ca_arm hsome).mpr (c.ca_receptive i m)

/-- Receptivity, existentially: no input leaves the spec stuck. -/
theorem receptive_ex (t : List CheckedArm) (ht : t.map CheckedArm.ca_arm = spec_table)
    (i : SyscallInput) (m : Model) :
    ∃ o, syscall_spec i m o :=
  ⟨_, receptive t ht i m⟩

/- =========================================================================
   §4  The concrete table's theorems, and the `arm_dispatch` tactic

   These belong with the dispatcher's theorems in
   `Checks/ExecutableSpecs.lean` / `Checks/Progress.lean`, but those two
   files would close a cycle against this one, and §3 already holds the
   unqualified names at an arbitrary table, so the instances live in
   `CheckedTable` below, at `checked_table` and `checked_table_arms`.
   ========================================================================= -/

namespace CheckedTable

/-- The dispatcher at the concrete table. -/
def check_syscall (i : SyscallInput) (eff : SyscallEffect) (m : Model) : check_result :=
  Dispatch.check_syscall checked_table i eff m

/-- The witness at the concrete table. -/
def syscall_spec_witness (i : SyscallInput) (m : Model) :
    Outcome SyscallEffect Model event :=
  Dispatch.syscall_spec_witness checked_table i m

/-- What the checker accepts, the spec admits. -/
theorem check_syscall_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (H : check_syscall i eff m = .CheckOk m' evs) :
    syscall_spec i m (.ok eff m' evs) :=
  Dispatch.check_syscall_sound_ok checked_table checked_table_arms i eff m m' evs H

/-- A `CheckUnmodeled` is a spec-side `unmodeled` too. -/
theorem check_syscall_sound_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (H : check_syscall i eff m = .CheckUnmodeled) :
    syscall_spec i m .unmodeled :=
  Dispatch.check_syscall_sound_unmodeled checked_table checked_table_arms i eff m H

/-- And conversely: every admitted `Ok` is checked to itself. -/
theorem check_syscall_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (H : syscall_spec i m (.ok eff m' evs)) :
    check_syscall i eff m = .CheckOk m' evs :=
  Dispatch.check_syscall_complete_ok checked_table checked_table_arms i eff m m' evs H

/-- Every spec-side `unmodeled` is checked to `CheckUnmodeled`. -/
theorem check_syscall_complete_unmodeled (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (H : syscall_spec i m .unmodeled) :
    check_syscall i eff m = .CheckUnmodeled :=
  Dispatch.check_syscall_complete_unmodeled checked_table checked_table_arms i m eff H

/-- The checker decides the syscall body: `CheckOk` is exactly the spec's
    `Ok`, both ways. -/
theorem check_syscall_ok_iff (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) :
    check_syscall i eff m = .CheckOk m' evs ↔ syscall_spec i m (.ok eff m' evs) :=
  Dispatch.check_syscall_ok_iff checked_table checked_table_arms i eff m m' evs

/-- And `CheckUnmodeled` is exactly the spec's `unmodeled`, both ways. -/
theorem check_syscall_err_iff (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall i eff m = .CheckUnmodeled ↔ syscall_spec i m .unmodeled :=
  Dispatch.check_syscall_err_iff checked_table checked_table_arms i eff m

/-- The dispatcher is receptive: `syscall_spec_witness i m` is an admissible
    outcome for every input and model state. -/
theorem receptive (i : SyscallInput) (m : Model) :
    syscall_spec i m (syscall_spec_witness i m) :=
  Dispatch.receptive checked_table checked_table_arms i m

/-- Receptivity, existentially: no input leaves the spec stuck. -/
theorem receptive_ex (i : SyscallInput) (m : Model) : ∃ o, syscall_spec i m o :=
  Dispatch.receptive_ex checked_table checked_table_arms i m

end CheckedTable

/-! ## `arm_dispatch`

    Resolve the dispatch: unfold the table and the lookup, turn the arms'
    numbers into literals (the `ca_no_arm_*` lemmas), compute the lookup,
    then turn the arm that answered back into its plain `check_*` or
    `*_witness` (the pointwise lemmas).  A caller writes this and never
    names a syscall.  Lean's rewrite database is the `simp` set, so this is
    two `simp` passes.

    The second branch handles the goal that is already one arm's component
    (no lookup left to compute): the first pass has nothing to do, and
    `simp` alone is the whole job.  Without it such a goal would stop at
    `simp only`'s "no progress". -/

macro "arm_dispatch" : tactic =>
  `(tactic| first
    | (simp only [checked_table, lookup_ca]; simp)
    | simp)

/-! ## Sanity checks

    These are the module's own checks; they pin the two tables, the
    lookups, and `arm_dispatch` on the REAL 90-arm table. -/

/-- The table carries one arm per modeled syscall. -/
example : checked_table.length = 90 := by decide

/-- The numbers are the spec table's, in the same order. -/
example : checked_table.map ca_no = spec_table.map SpecArm.sa_no := by
  have h := checked_table_arms
  rw [← h]
  simp [ca_no, List.map_map, Function.comp_def]

/-- A number the table carries is found, with the right number back. -/
example : (lookup_ca checked_table 64).map ca_no = some 64 := by arm_dispatch

/-- A number between two arms is not. -/
example : (lookup_ca checked_table 18).isNone = true := by arm_dispatch

/-- The first and last arms, through the same lookup. -/
example : (lookup_ca checked_table 17).map ca_no = some 17 := by arm_dispatch
example : (lookup_ca checked_table 439).map ca_no = some 439 := by arm_dispatch

/-- `arm_dispatch` turns the arm that answered back into its checker. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    CheckedArm.ca_check arm_write i eff m
      = check_write i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  arm_dispatch

/-- And into its witness. -/
example (i : SyscallInput) (m : Model) :
    CheckedArm.ca_witness arm_timerfd_create i m
      = timerfd_create_witness (clockid32 (in_arg i 0)) (flag32 (in_arg i 1)) m := by
  arm_dispatch

/-- The whole chain: once the lookup answers `arm_read`, `check_syscall` IS
    that arm's checker -- no case analysis, one rewrite. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (h : lookup_ca checked_table (i.in_sysno.toNat : Int) = some arm_read) :
    check_syscall checked_table i eff m
      = check_read i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m := by
  simp only [check_syscall, h, ca_check_arm_read]

/-! And the pre-existing sanity checks on an arbitrary table. -/

/-- A throwaway arm: number 999, admitting nothing but `unmodeled`.  It
    exists only so the lookups below have something to find. -/
private def armSanity : CheckedArm where
  ca_arm := ⟨999, fun _ _ o => o = .unmodeled⟩
  ca_check := fun _ _ _ => .CheckUnmodeled
  ca_witness := fun _ _ => .unmodeled
  ca_sound_ok := by intro _ _ _ _ _ h; cases h
  ca_sound_unmodeled := by intro _ _ _ _; rfl
  ca_complete_ok := by intro _ _ _ _ _ h; cases h
  ca_complete_unmodeled := by intro _ _ _ _; rfl
  ca_receptive := by intro _ _; rfl

/-- `ca_no` reads the arm's number. -/
example : ca_no armSanity = 999 := by decide

/-- An empty table answers nothing. -/
example : lookup_ca [] 0 = none := rfl

/-- The arm the number selects is the arm that comes back. -/
example : lookup_ca [armSanity] 999 = some armSanity := rfl

/-- A number no arm carries falls through. -/
example : lookup_ca [armSanity] 998 = none := by simp [lookup_ca, ca_no, armSanity]

/-- With no arms, the checker is the fail-closed `CheckUnmodeled` -- the one
    `none` case, in one place. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_syscall [] i eff m = .CheckUnmodeled := rfl

/-- And the witness of a number with no arm is `unmodeled`. -/
example (i : SyscallInput) (m : Model) : syscall_spec_witness [] i m = .unmodeled := rfl

end LinuxSem.Checks.Sys.Dispatch
