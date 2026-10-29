/-
  * LinuxProcessSem.Sys.Fs.Timerfd — timerfd_create (85)


  This file answers to Linux `fs/timerfd.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines the
  syscall.  `Specs.v` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.v` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  THIS ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE.  Every input
  that survives it is declined.  The reason is that a surviving input
  CREATES A FILE DESCRIPTOR, and this model has no descriptor kind to put
  a timer behind: none of `State.FdEntry`'s constructors is a timerfd.
  Adding one is not a local change — every `FdEntry` match in the tree is
  exhaustive on purpose, so the read, write, stat, sync, ioctl, select
  and socket specs, their acceptors, their witnesses and the example
  proofs would each have to decide the new case.

  What that costs is priority 3 and nothing else: a program that
  successfully creates a timerfd leaves the modeled surface at the
  `timerfd_create` itself, so `Equivalence.strong_universal` is vacuous
  over it rather than wrong about it.  The condition that would let this
  arm grow a success is a single one, and it is worth writing down
  because it is one step to check rather than an argument to re-derive: a
  descriptor kind for a timer in `State.FdEntry`, which is what
  `timerfd_settime` (86) and `timerfd_gettime` (87) also wait on.

  So what is here is exact rather than approximate: the -EINVAL the
  kernel returns before it allocates anything, and a fail-closed
  decline for everything after.  The bound is named in place, the way
  `Open.openat_spec` names the -EMFILE it stops short of.

  THE GATE IS ONE `if`, AND THAT IS BEHAVIOR.  Linux writes

    if ((flags & ~TFD_CREATE_FLAGS) ||
        (clockid != CLOCK_MONOTONIC && clockid != CLOCK_REALTIME &&
         clockid != CLOCK_REALTIME_ALARM && clockid != CLOCK_BOOTTIME &&
         clockid != CLOCK_BOOTTIME_ALARM))
      return -EINVAL;

  (Linux v6.18.46, fs/timerfd.c, `SYSCALL_DEFINE2(timerfd_create)`).
  The two halves are DISJUNCTS OF ONE CONDITION, not two sequential
  tests, so there is no ordering question between them and no
  "which errno wins" between them either — they win together.  Where
  the ordering does matter is against the NEXT test: the capability
  check for the alarm clocks sits in a separate `if` BELOW this one,
  so an unknown flag bit together with `CLOCK_REALTIME_ALARM` is
  -EINVAL and never -EPERM.  That is the one precedence fact this arm
  encodes.

  WHY THE ALARM CLOCKS ARE IN THE ADMITTED SET even though the model
  can never answer for them.  Dropping `CLOCK_REALTIME_ALARM` and
  `CLOCK_BOOTTIME_ALARM` from the membership test would be the
  tempting simplification — they need CAP_WAKE_ALARM, which this model
  has no notion of, so they are declined either way.  It would also be
  WRONG, and wrong in the direction that matters: `timerfd_create
  (CLOCK_REALTIME_ALARM, 0)` would then answer -EINVAL, an errno Linux
  does not produce for it.  Linux answers -EPERM without the
  capability and a descriptor with it, and both are outside the
  modeled surface.  A declined input costs coverage; a confidently
  wrong errno costs soundness, so the two ids are admitted here and
  declined below.

  WHAT THE DECLINE COVERS, walked from the source so the gap is a
  named list rather than "the rest": -EPERM from
  `capable(CAP_WAKE_ALARM)` on the two alarm ids; -ENOMEM from the
  `kzalloc` of the `timerfd_ctx`; -EMFILE from `get_unused_fd_flags`;
  -ENOENT or -ENODEV from `anon_inode_getfile_fmode`; and the success,
  which is the descriptor number.

  NO -EINVAL IS REACHABLE ON ANY OF THEM, which is what makes this a
  decline that loses coverage WITHOUT losing precision: the errno the
  arm commits to is exactly the errno Linux commits to, and there is no
  input where the model answers -EINVAL and Linux answers something
  else.  The claim is worth its own paragraph because it is the one
  that justifies the arm's shape, and it is checkable rather than
  rhetorical — these are the returns of the functions `timerfd_create`
  reaches after the gate, each read at v6.18.46:

  - `timerfd_create` itself (fs/timerfd.c) has exactly one
    `return -EINVAL` in its body, the gate's;
  - `alloc_fd` (fs/file.c), under `get_unused_fd_flags`, carries
    -EMFILE as its only errno, and `expand_files` beneath it the same;
  - `__anon_inode_getfile` (fs/anon_inodes.c) yields -ENOENT or
    -ENODEV, and `alloc_file_pseudo` (fs/file_table.c) forwards
    `alloc_path_pseudo` and `alloc_file`, which are allocation
    failures.

  That is the walk, not a claim about the whole tree: a caller reaching
  `timerfd_create` through some path not enumerated here is outside
  what was checked.

  THE ARGUMENTS ARRIVE ALREADY TRUNCATED TO 32 BITS, and that is
  load-bearing rather than incidental.  Both parameters are declared
  `int` in the `SYSCALL_DEFINE2`, and riscv64's wrapper narrows each
  at the boundary: `__SYSCALL_DEFINEx` calls `__do_sys##name` through
  `__SC_CAST`, which is `(__force t) a` (Linux v6.18.46,
  arch/riscv/include/asm/syscall_wrapper.h and include/linux/syscalls.h),
  while `SC_RISCV_REGS_TO_ARGS` hands over the registers full-width.
  So the high half of either register is DISCARDED before any test
  runs, and `timerfd_create(2^32 + 1, 0)` is `timerfd_create(1, 0)` —
  which Linux answers with a descriptor, not with the -EINVAL a
  full-register comparison would give.  `Sys.SyscallTable` applies
  `clockid32` and `flag32` at the arm, which is where the kernel does
  it and where `clock_gettime`'s id is already narrowed; this spec
  receives both words narrowed and must not narrow them again.

  THE MEMBERSHIP TEST IS STATED OVER THE UNSIGNED LOW HALF while
  Linux compares a signed `int`.  The two agree on every input, and
  the argument is not "small constants" hand-waving: each of the five
  targets is below 2^31, and for such a constant `c`, a 32-bit pattern
  equals `c` as a signed `int` exactly when it equals `c` as an
  unsigned one.  Equality against a non-negative constant cannot
  separate the two readings.  (The sign question is real elsewhere —
  `clockid32`'s own comment records that the NEGATIVE id space reaches
  a live CPU-clock family `clock_gettime` partly succeeds on.  It does
  not arise here because this test is equality, not ordering, and
  because every negative id lands outside the admitted set and takes
  the -EINVAL Linux gives it.)

  THE FLAG TEST IS A TRUTHINESS TEST, not a sign test, and that is
  what makes `Z.ldiff` the faithful spelling.  `flags & ~TFD_CREATE_FLAGS`
  is used directly as the `if` condition, so a result of 0x80000000 —
  which is negative as an `int` — is nonzero and takes the -EINVAL
  just as 1 does.  An implementation that compared the residue against
  0 with `>` rather than `<>` would admit `flags = 1 << 31`; this one
  does not.

  CONFIG_TIMERFD IS ASSUMED ON.  fs/Makefile builds timerfd.c under
  `obj-$(CONFIG_TIMERFD)` and kernel/sys_ni.c carries
  `COND_SYSCALL(timerfd_create)`, so a kernel built without it answers
  -ENOSYS to every input this arm calls -EINVAL.  init/Kconfig defaults
  it to y and hides the switch behind EXPERT.  It is the same class of
  assumption every arm whose syscall carries a `COND_SYSCALL` makes —
  kernel/sys_ni.c has one for `socket` too — and it is stated here
  rather than tested because no syscall argument distinguishes the two
  builds.  It is the ONE premise outside this call's own arguments that
  the -EINVAL rests on.

  What each dependency supplies:

      From LinuxSem.LinuxProcessSem Require Import BvBase Fs State Monad.
      From LinuxSem.LinuxProcessSem.Sys Require Export Syscall Uapi.

  Here `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
  so a spec's type is `SysSpec SyscallEffect`.
  `Sys.Syscall` supplies `err_ret` and the `clockid32`/`flag32`
  truncations the checks use; `Sys.Uapi` supplies `TFD_CREATE_FLAGS` and
  the five clock ids; `State` supplies the errno constants (`EINVAL`,
  `EMFILE`) and `mkEffect`; `Monad` supplies `unmodeled`;
  `StateLedger`/`StateFd` supply `m_fds`, `mkModel`, `fd_lookup` and
  `alloc_fd`, and `Sys.Fs.File` supplies `z_ldiff` (`Z.ldiff`) and
  `lowest_fd` — imported, never redefined.  `Sys.Uaccess` is deliberately
  NOT imported: no user buffer is touched by this spec.

  `bv_unsigned`.  `bv_unsigned w` is `(w.toNat : Int)`
  here — the same function on the same carrier, spelled out because the
  Lean tree has no `bv_unsigned` (`StateVm.lean` records the same
  identification).  `Z.eqb _ 0` is `_ == 0`, and `negb` is `!`.

  `Z.ldiff`.  The bit-difference `a & ~b`; Lean has no
  such constant and `Sys/Uapi.lean` ports only `Z.lor`/`Z.land`, so
  `Fs.File.z_ldiff` — defined beside its first caller, `dup3_flags_ok` —
  is imported and reused rather than copied a second time.  Every operand
  here is non-negative (`flags.toNat` is, `TFD_CREATE_FLAGS` is a
  literal), which is the condition under which `a - (a & b)` is `a & ~b`;
  its docstring carries that argument.

  the declined success.  The spec declines it, so nothing
  below produces a descriptor or an errno other than -EINVAL.  The checks
  at the end of the file therefore pin the descriptor number and the
  -EMFILE limit on `File.lowest_fd`/`alloc_fd` — the machinery the
  docstring's gap list names — rather than on an arm this spec does not
  have; the note above them spells that out.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Fs.File

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File

namespace LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd

/-- The five clock ids `timerfd_create` admits, written out of the
    kernel's own five-way comparison.  RESTATED rather than shared with
    the acceptor and the witness, and deliberately so: this predicate
    decides WHICH ARM RUNS, and a gate the three layers imported from
    one definition would agree with itself however wrong it was.  The
    soundness and completeness lemmas are what force the three
    statements to coincide, which is the same reason
    `Kernel.Time.PosixTimers` restates its envelope bound in each layer
    instead of sharing it. -/
def timerfd_create_einval_b (clkid flags : word) : Bool :=
  !(z_ldiff (flags.toNat : Int) TFD_CREATE_FLAGS == 0) ||
    !((clkid.toNat : Int) == CLOCK_REALTIME ||
      ((clkid.toNat : Int) == CLOCK_MONOTONIC ||
        ((clkid.toNat : Int) == CLOCK_BOOTTIME ||
          ((clkid.toNat : Int) == CLOCK_REALTIME_ALARM ||
            (clkid.toNat : Int) == CLOCK_BOOTTIME_ALARM))))

/-- `timerfd_create clockid flags`: create a descriptor bound to a clock.

    No `get_model`: the answer is a function of the two arguments alone.
    The -EINVAL arm touches no memory, emits no event and changes no
    state, which is what the kernel does on that path too — it returns
    before the `kzalloc`. -/
def timerfd_create_spec (clkid flags : word) : SysSpec SyscallEffect :=
  if timerfd_create_einval_b clkid flags
  then err_ret EINVAL      -- real -EINVAL, decided before anything is allocated
  else unmodeled           -- EPERM / ENOMEM / EMFILE / the descriptor: fail closed

/-! ## Sanity checks

    There is no closed computation to re-use in this file — it is the two
    definitions above and their prose.  The checks below are PORT CHECKS,
    and they pin the three things the prose argues for:

    1. **The gate**, id by id: the five admitted clock ids answer `false`
       and everything else `true`, the flag residue is a truthiness test
       (`1 << 31` included), the two halves are disjuncts of ONE
       condition (bad flags together with an alarm clock is -EINVAL, not
       -EPERM), and both arguments are read at the width the dispatcher
       hands them.
    2. **The two arms**, at the spec: -EINVAL is an `ok` outcome carrying
       the errno word, and every admitted input is `unmodeled` — the
       alarm clocks included, because answering -EINVAL to them would be
       a confidently wrong errno.
    3. **The two things the decline stands in for** — the descriptor
       number and the -EMFILE at the table's limit.  They are NOT arms of
       this spec, so they are pinned where the
       kernel takes them: `File.lowest_fd` over a small fixture, and the
       allocator's fuel-exhaustion branch, whose freeness conjunct is
       what leaves only the -EMFILE alternative.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so lookup equations are stated as
    equations between `Option FdEntry` and proved by `simp` on the
    tables' keys rather than by `decide`; everything `Bool`- or
    `word`-valued (`timerfd_create_einval_b`, `z_ldiff`, `alloc_fd`,
    the errno constants) is `by decide`. -/

/-! ### The gate -/

/-- The residue test is `Z.ldiff` (`a & ~b`), imported from `Fs.File`:
    it clears exactly the mask's bits. -/
example : z_ldiff TFD_CREATE_FLAGS TFD_CREATE_FLAGS = 0 := by decide
example : z_ldiff (TFD_CREATE_FLAGS + 1) TFD_CREATE_FLAGS = 1 := by decide
example : z_ldiff 0 TFD_CREATE_FLAGS = 0 := by decide

/-- Each of the five admitted clocks passes the membership test — the
    kernel's own five-way comparison, in its order. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_REALTIME) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_BOOTTIME) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_BOOTTIME_ALARM) 0 = false := by
  decide

/-- …and every other id fails it, the ids `clock_gettime` answers
    included: the two families overlap but neither contains the other. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_PROCESS_CPUTIME_ID) 0 = true := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC_RAW) 0 = true := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_REALTIME_COARSE) 0 = true := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC_COARSE) 0 = true := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 10) 0 = true := by decide

/-- A NEGATIVE id lands outside the admitted set and takes the -EINVAL
    Linux gives it; narrowing does not move it inside, which is why the
    unsigned reading of the membership test cannot differ from the signed
    one on the five non-negative targets. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 (-1)) 0 = true := by decide
example : timerfd_create_einval_b (clockid32 (BitVec.ofInt 64 (-1))) 0 = true := by
  decide

/-- The flag test accepts exactly `TFD_CREATE_FLAGS`' bits. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) O_CLOEXEC = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) O_NONBLOCK = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) TFD_CREATE_FLAGS = false := by
  decide

/-- Bit 0 is `TFD_TIMER_ABSTIME`, `timerfd_settime`'s flag: passing it to
    `timerfd_create` is -EINVAL, which is what separates
    `TFD_CREATE_FLAGS` from `EFD_FLAGS_SET`.  And any other stray bit is
    -EINVAL too. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) 1 = true := by decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC)
    (TFD_CREATE_FLAGS + 1) = true := by decide

/-- THE FLAG TEST IS TRUTHINESS, NOT SIGN: `1 << 31` is 0x80000000, which
    is negative as a 32-bit `int`, and it is still -EINVAL — as is the
    full 64-bit word with that bit set.  A `> 0` comparison would admit
    both. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC) 2147483648 = true := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC)
    (BitVec.ofInt 64 2147483648) = true := by decide

/-- THE TWO HALVES ARE DISJUNCTS OF ONE CONDITION: bad flags together
    with an alarm clock is -EINVAL.  The -EPERM the capability check
    would give sits in a separate `if` BELOW the gate, so it never
    competes with this one. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 1 = true := by
  decide

/-- THE ARGUMENTS ARRIVE NARROWED AND ARE NOT NARROWED AGAIN.  Read at
    full width, `timerfd_create(2^32 + 1, 0)`'s id is outside the
    admitted set and -EINVAL, where the kernel (narrowing at the
    boundary) sees `timerfd_create(1, 0)` and hands back a descriptor.
    The dispatcher applies `clockid32`/`flag32`; applied, the test
    admits the call — so a spec that narrowed internally would be
    agreeing with itself, not with the kernel. -/
example : timerfd_create_einval_b (BitVec.ofInt 64 4294967297) 0 = true := by decide
example : timerfd_create_einval_b (clockid32 (BitVec.ofInt 64 4294967297)) 0 = false := by
  decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC)
    (BitVec.ofInt 64 4294967296) = true := by decide
example : timerfd_create_einval_b (BitVec.ofInt 64 CLOCK_MONOTONIC)
    (flag32 (BitVec.ofInt 64 4294967296)) = false := by decide

/-! ### The two arms -/

/-- THE -EINVAL ARM: a `true` gate answers the errno word, leaving the
    model untouched and emitting nothing — the kernel returns before the
    `kzalloc`. -/
theorem timerfd_create_einval (clkid flags : word) (i : SyscallInput)
    (m : Model) (h : timerfd_create_einval_b clkid flags = true) :
    timerfd_create_spec clkid flags i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp only [timerfd_create_spec]
  rw [ite_eq_left h]
  simp only [err_ret, ret_only, pure]

/-- THE DECLINE: every input that survives the gate is `unmodeled`,
    whatever it is — the alarm clocks included, since -EINVAL is an
    errno Linux does not produce for them. -/
theorem timerfd_create_declines (clkid flags : word) (i : SyscallInput)
    (m : Model) (h : timerfd_create_einval_b clkid flags = false) :
    timerfd_create_spec clkid flags i m .unmodeled := by
  have h' : timerfd_create_einval_b clkid flags ≠ true := by
    rw [h]
    decide
  simp only [timerfd_create_spec, ite_eq_right h', unmodeled]

/-- Bad flags are -EINVAL, whatever the clock id says. -/
example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_MONOTONIC) 1 i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  timerfd_create_einval (BitVec.ofInt 64 CLOCK_MONOTONIC) 1 i m (by decide)

/-- An unknown clock id is -EINVAL too — `CLOCK_PROCESS_CPUTIME_ID`, which
    `clock_gettime` answers and `timerfd_create` refuses. -/
example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_PROCESS_CPUTIME_ID) 0 i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  timerfd_create_einval _ 0 i m (by decide)

/-- THE PRECEDENCE FACT: an unknown flag bit with an alarm clock is
    -EINVAL, not -EPERM. -/
example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 1 i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  timerfd_create_einval _ 1 i m (by decide)

/-- With the gate passed, the answer is the DECLINE, not an errno: the
    admitted clocks, at the accepted flag words. -/
example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 i m .unmodeled :=
  timerfd_create_declines _ _ i m (by decide)

example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_REALTIME) TFD_CREATE_FLAGS i m
      .unmodeled :=
  timerfd_create_declines _ _ i m (by decide)

/-- AND THE ALARM CLOCKS DECLINE RATHER THAN REJECT: -EPERM (without
    CAP_WAKE_ALARM) and the descriptor (with it) are both outside the
    modeled surface, and neither is -EINVAL. -/
example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 0 i m .unmodeled :=
  timerfd_create_declines _ _ i m (by decide)

example (i : SyscallInput) (m : Model) :
    timerfd_create_spec (BitVec.ofInt 64 CLOCK_BOOTTIME_ALARM) 0 i m .unmodeled :=
  timerfd_create_declines _ _ i m (by decide)

/-! ### The descriptor number (the success this arm declines)

    A surviving call reaches `get_unused_fd_flags`, which takes the
    LOWEST free descriptor — `File.lowest_fd`, the port's `choose` over
    `State.alloc_fd`.  That number is what the kernel returns, and it is
    pinned here rather than in an arm of `timerfd_create_spec`, which by
    construction has none. -/

/-- A syscall input for `timerfd_create`.  The spec does not read it —
    the answer is a function of the two arguments alone — but a `SysSpec`
    is a relation on an input and a model as well, so the checks name
    one. -/
private def demoInput : SyscallInput :=
  { in_sysno := 85, in_args := [BitVec.ofInt 64 CLOCK_MONOTONIC, 0],
    in_mem := fun _ => none, in_wmem := fun _ => none }

/-- A tiny fd table for the checks: 0, 1 and 2 are the three standard
    descriptors, so the next descriptor a create call would hand out is
    3. -/
private def demoFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdChannel 8),
   (2, FdEntry.FdChannel 9)]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and the default
    RLIMIT_NOFILE (1024). -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The same table with fd 1 closed — after `close(1)` the next
    descriptor handed out is 1 again, not 3. -/
private def demoHoleFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (2, FdEntry.FdChannel 9)]

private def demoHoleModel : Model :=
  mkModel demoHoleFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The allocator hands out the first free descriptor — 3 here. -/
example : alloc_fd demoFds = 3 := by decide

/-- …and after `close(1)` it hands out 1 again. -/
example : alloc_fd demoHoleFds = 1 := by decide

/-- THE SUCCESS ARM OF A SURVIVING CALL, at the machinery that owns it:
    the lowest free descriptor is 3, and it is free. -/
example : lowest_fd demoFds demoInput demoModel (.ok 3 demoModel []) := by
  rw [lowest_fd_ok demoFds 3 demoInput demoModel]
  exact ⟨by simp [demoFds, fd_lookup], by decide⟩

/-- …and with fd 1 closed it is 1 — the lowest, not the next in some
    other order. -/
example : lowest_fd demoHoleFds demoInput demoHoleModel (.ok 1 demoHoleModel []) := by
  rw [lowest_fd_ok demoHoleFds 1 demoInput demoHoleModel]
  exact ⟨by simp [demoHoleFds, fd_lookup], by decide⟩

/-! ### -EMFILE at the table's limit

    `get_unused_fd_flags` answers -EMFILE when the descriptor table has no
    free slot below `sysctl_nr_open`.  The model's allocator is
    fuel-bounded at 4096 candidates, and its last branch returns the
    candidate UNCONDITIONALLY; `File.lowest_fd`'s freeness conjunct then
    empties the success set, which is the -EMFILE alternative.  The
    4096-candidate instance is not evaluated — a 4097-entry table costs
    millions of kernel reduction steps on every build of this file, the
    cost `Fs/File.lean` declines for its own fixture — so the mechanism
    is pinned on a miniature with explicit fuel, and the general fact is
    stated as `lowest_fd_at_limit`. -/

/-- THE EXHAUSTION BRANCH OF `alloc_fd`, in miniature: a table holding
    0..5 and fuel for five candidates stops on 5, which is TAKEN — the
    state the freeness conjunct rejects. -/
private def demoSixFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdChannel 8),
   (2, FdEntry.FdChannel 9), (3, FdEntry.FdChannel 10),
   (4, FdEntry.FdChannel 11), (5, FdEntry.FdChannel 12)]

example : alloc_fd_aux demoSixFds (BitVec.ofInt 64 0) 5 = 5 := by decide

/-- …and 5 really is occupied there. -/
example : fd_lookup demoSixFds 5 = some (FdEntry.FdChannel 12) := by
  simp [demoSixFds, fd_lookup]

/-- THE -EMFILE ALTERNATIVE, stated rather than evaluated: when the
    allocator's answer is already taken — the 4096-candidate scan
    exhausted — `lowest_fd` has no success outcome at all, so the only
    answer left is the errno arm's, and `get_unused_fd_flags` carries
    -EMFILE as its only one.  This is `File.lowest_fd_occupied`, cited
    rather than reproved; the Timerfd arm declines the whole path, so the
    errno must not appear here. -/
theorem lowest_fd_at_limit (fds : List (word × FdEntry)) (i : SyscallInput)
    (m : Model) (o : Outcome word Model event)
    (h : fd_lookup fds (alloc_fd fds) ≠ none) : ¬ lowest_fd fds i m o :=
  lowest_fd_occupied fds i m o h

/-- The two errno words this file's prose names. -/
example : EINVAL = 22 := by decide
example : EMFILE = 24 := by decide

end LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
