/-
  * LinuxProcessSem.Sys.Kernel.Sched.Syscalls — sched_getaffinity (123),
    sched_setscheduler (119), sched_yield (124)

    This file answers to Linux `kernel/sched/syscalls.c`: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  `Specs.lean` carries the whole map.  The
    scheduler syscalls moved out of `kernel/sched/core.c` into
    `kernel/sched/syscalls.c` at v6.11.  That the MOVE was behaviourally
    empty is checked for `sched_getaffinity`'s two functions and claimed
    for no others: both are byte-identical either side of it.  The
    `sched_setscheduler` arm below makes no cross-version claim at all
    and is read at v6.18.46 alone.  `sched_yield` moved with them and
    is read at v6.12.1.

    TRUST BOUNDARY: this file is part of the trusted specification.
    `Specs.lean` holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

  - `ret_only` / `err_ret` / `w_is0` / `abi_low32` / `pid32` / `sint32` /
    `record_copyins` are `Sys.Syscall`'s; the `SCHED_*` words and
    `MAX_RT_PRIO` are `Sys.Uapi`'s; `read_bytes_map` / `access_okb` /
    `le_bytes_to_word` are the state layer's.  All of them are put into
    unqualified
    scope; the `open`s below do the same.
  - `abi_low32` is opened from `Sys.Syscall` ONLY, not from `Sys.Uapi`:
    `Sys/Uapi.lean` still carries a local copy of that name (see the
    note in `Sys/Syscall.lean`), so only one definition should remain.
    `Sys.Uapi` is therefore opened selectively, for the seven `SCHED_*`
    constants and `MAX_RT_PRIO` alone.
  - `Z.land pol SCHED_RESET_ON_FORK` has no direct Lean spelling
    (`Int.land` does not exist at v4.31.0); `sched_reset_on_fork_b`
    below is the one added definition in this file, and it states the
    same bit test.  See its note.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Uaccess

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
  (SCHED_NORMAL SCHED_FIFO SCHED_RR SCHED_BATCH SCHED_IDLE SCHED_DEADLINE
   SCHED_EXT SCHED_RESET_ON_FORK MAX_RT_PRIO)

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls

/-! ## sched_getaffinity (123) -/

/- `sched_getaffinity pid len user_mask_ptr` (123).

    Every kernel citation below is at v6.18.46, commit 1f99e9ab748f,
    unless it names a version window of its own.

    NUMBER 123 HAS TWO ENTRY POINTS and this spec models one of them.
    include/uapi/asm-generic/unistd.h wires it with `__SC_COMP`, which
    names sys_sched_getaffinity in the native table and
    compat_sys_sched_getaffinity in the compat one; the second is
    defined by kernel/compat.c's
    `COMPAT_SYSCALL_DEFINE3(sched_getaffinity)`.  Neither generated
    symbol is written in angle brackets here on purpose: the name a
    reader can retrace is the macro, not what it expands to.
    Which table an ecall indexes is decided by `syscall_handler`
    (arch/riscv/include/asm/syscall.h): `compat_sys_call_table` when
    `(regs->status & SR_UXL) == SR_UXL_32`, the native one otherwise.
    Every process this model can load is LP64 — elf-snapshot refuses any
    image whose `EI_CLASS` is not `ELFCLASS64`, and the ISA model is RV64
    — so the native arm is the only one reachable here.  That is worth
    naming because it is NOT a property of the architecture: riscv64
    defaults `CONFIG_COMPAT` on (arch/riscv/Kconfig, `config COMPAT`,
    `default 64BIT`), and the two bodies gate differently.  The compat
    one is `len & (sizeof(compat_ulong_t) - 1)`, which is `& 3` where the
    native gate is `& 7`, so a 32-bit task SUCCEEDS at a `len` of 4 where
    an LP64 task is refused.  A 32-bit caller does not see a different 8;
    it lands in a different function.  This spec stops being right about
    a `len` of 4 the day something teaches the loader to accept an
    ELFCLASS32 image.

    THE NATIVE FUNCTION, in its own order (kernel/sched/syscalls.c,
    `SYSCALL_DEFINE3(sched_getaffinity)` and the `sched_getaffinity`
    helper it calls):

      if ((len * BITS_PER_BYTE) < nr_cpu_ids)  return -EINVAL;
      if (len & (sizeof(unsigned long)-1))     return -EINVAL;
      if (!zalloc_cpumask_var(&mask, GFP_KERNEL)) return -ENOMEM;
      ret = sched_getaffinity(pid, mask);      /* -ESRCH, or an LSM's
                                                  errno, or 0 with
                                                  mask = p->cpus_mask
                                                       & cpu_active_mask */
      if (ret == 0) {
        unsigned int retlen = min(len, cpumask_size());
        if (copy_to_user(user_mask_ptr, cpumask_bits(mask), retlen))
             ret = -EFAULT;
        else ret = retlen;
      }
      return ret;

    The outer body is byte-identical from v6.3 through v6.18.46; before
    v6.3 it differs only in `alloc_cpumask_var` versus `zalloc_` and in
    passing `mask` rather than `cpumask_bits(mask)` to `copy_to_user`,
    neither of which touches the two gates.  The helper is
    byte-identical from v6.7 through v6.18.46.  v6.1 through v6.6 are a
    different TEXT — explicit `rcu_read_lock` and `raw_spin_lock_irqsave`
    where v6.7+ uses `guard`, a `goto out_unlock` single exit where v6.7+
    returns early — and the same BEHAVIOUR: same errno set, same
    `security_task_getscheduler` position, same `cpumask_and(mask,
    &p->cpus_mask, cpu_active_mask)`.  Nothing this spec models is inside
    the helper at all.  Both claims are over the whole interval rather
    than its endpoints: the two bodies were extracted and compared at
    every release tag in the range, the v6.10/v6.11 move of the file
    included.

    WHAT IS MODELED IS THE MACHINE-INDEPENDENT HALF, and that is the
    whole argument for this arm.  Both gates return the SAME errno, so
    which of them fires is not observable — only whether one of them
    does.  That lets the spec answer for a length either gate refuses
    without knowing `nr_cpu_ids`, the runtime CPU count this model has
    no representation of at all:

    - A LENGTH THAT IS NOT A MULTIPLE OF 8 is -EINVAL whatever
      `nr_cpu_ids` is.  If the size gate fires first the answer is
      -EINVAL; if it does not, the alignment gate fires and the answer
      is -EINVAL.
    - A LENGTH WHOSE BIT COUNT WRAPS TO ZERO is -EINVAL because
      `nr_cpu_ids >= 1`.  `len` is an `unsigned int` and `BITS_PER_BYTE`
      is the plain `8` (include/linux/bits.h — the constant this arm
      rests on, since an `8UL` there would widen the product to 64 bits
      and leave no wrap to model), so `len * BITS_PER_BYTE` is computed
      in `unsigned int` and WRAPS modulo 2^32.  The product is zero
      exactly on the multiples of 2^29, which a model doing the
      multiplication over the integers would call successes.
      `nr_cpu_ids >= 1` is what turns "the product is 0" into "-EINVAL".
      IT IS A CLAIM ABOUT RISCV64 AND IS STATED THAT WAY ON PURPOSE:
      the general form is false, because arch/x86/xen/smp_pv.c's
      `xen_smp_count_cpus` calls `set_nr_cpu_ids(cpus)` with an
      unguarded `cpus` that is 0 when the very first `VCPUOP_is_up`
      hypercall fails.  On riscv64 it holds by two routes, and which
      one applies is a config question.  Where `nr_cpu_ids` is a
      variable at all — kernel/smp.c guards
      `unsigned int nr_cpu_ids __read_mostly = NR_CPUS` with
      `#if (NR_CPUS > 1) && !defined(CONFIG_FORCE_NR_CPUS)` — it starts
      at `NR_CPUS` and `setup_nr_cpu_ids()` resets it to
      `find_last_bit(cpumask_bits(cpu_possible_mask), NR_CPUS) + 1`, at
      least 1 for any argument because `find_last_bit`
      (include/linux/find.h and lib/find_bit.c, both arms) answers
      `size` when no bit is set, so an empty possible mask would give
      `NR_CPUS + 1` rather than 0.  The `nr_cpus=` boot parameter is
      the one knob that reaches it from outside and `nrcpus()` guards
      it with `nr_cpus > 0`.  Otherwise include/linux/cpumask.h
      replaces the variable with the constant `((unsigned int)NR_CPUS)`
      and `set_nr_cpu_ids` degenerates to a `WARN_ON`, so nothing can
      write it; `NR_CPUS` is then at least 1 because
      arch/riscv/Kconfig's `config NR_CPUS` is `depends on SMP` with
      every `range` starting at 2, and a `!SMP` build takes
      include/linux/threads.h's
      `#ifndef CONFIG_NR_CPUS / #define CONFIG_NR_CPUS 1`.  What makes
      the riscv64 scoping checkable rather than a hedge: the cited
      tree has ten `set_nr_cpu_ids` call sites across seven files and
      none of them is under arch/riscv, so the arch never overrides the
      value and the two routes above are the whole story here.

    THE ORDER IS WHY `pid` AND `user_mask_ptr` ARE ABSENT FROM THE
    SIGNATURE.  Both gates run before `find_process_by_pid` is reached
    and before the pointer is touched at all: there is no `access_ok`
    anywhere in kernel/sched/syscalls.c, and the pointer's first and
    only use is the `copy_to_user` inside the `ret == 0` block.  A
    malformed length therefore beats -ESRCH and -EFAULT both.  The -ENOMEM from
    `zalloc_cpumask_var` sits behind both gates too, so it cannot
    pre-empt either answer.

    WHY THE REST IS DECLINED.  A length that is a nonzero multiple of 8
    whose bit count does not wrap either succeeds or is -EINVAL, and
    which one it is depends on `nr_cpu_ids`.  Modeling that needs three
    facts about the machine, none of which this model represents:

    - `nr_cpu_ids`, which decides the first gate;
    - `cpumask_size()`, which decides the RETURN VALUE, since a success
      returns `min(len, cpumask_size())` and not 0.  It is
      `bitmap_size(large_cpumask_bits)` (include/linux/cpumask.h), and
      `large_cpumask_bits` is the compile-time `NR_CPUS` when
      `NR_CPUS <= 4*BITS_PER_LONG` and the runtime `nr_cpu_ids` above
      that — so the byte count a successful call returns is not a
      function of `len` alone;
    - the mask itself, `p->cpus_mask & cpu_active_mask`, which is the
      bytes copied out.

    They are also not per-call choices.  A machine has one CPU count for
    the life of a process, so a `choose` resolved afresh at each call
    would admit a trace in which two `sched_getaffinity` calls disagree
    about how many CPUs exist — a trace no Linux machine produces.  The
    honest shape is a model-state field pinned at the first observation,
    the way `State.limst_core` pins RLIMIT_CORE and `State.procst_tid`
    pins the tid; that field does not exist yet, and adding it is what
    the successful path waits on.  `State.lean`'s note above `Record Model`
    compares that mechanism against the two alternatives.

    Cost of the decline, stated plainly: a program that asks how many
    CPUs it may run on leaves the modeled surface on that call.  musl's
    `do_getaffinity` (musl 1.2.5, src/sched/affinity.c) passes `size`
    through unchanged and then uses the RETURNED byte count to zero the
    tail of the caller's `cpu_set_t` before answering 0 — so the count
    this spec declines to produce is the one that wrapper depends on,
    and a `CPU_COUNT` query over any plausible `cpu_set_t` lands in the
    declined band.  So does the Zig standard library's
    `std.Thread.getCpuCount`.  A program that merely passes a malformed
    length — a zero, an unaligned one, or one of the wrapping ones —
    does not. -/
/-- The two gates, as one predicate over the `unsigned int` the ABI
    delivers.  The disjunction's order is not the kernel's order (the
    size gate is first there); it does not have to be, because both
    gates answer -EINVAL and no execution can tell them apart.

    THE `abi_low32` IS DOCUMENTATION HERE, NOT ARITHMETIC, and saying so
    saves someone writing a test that cannot fail.  `len` really is
    narrowed to 32 bits before the kernel sees it (`__SC_CAST` in
    include/linux/syscalls.h, applied by `__SYSCALL_DEFINEx` out of
    arch/riscv/include/asm/syscall_wrapper.h), but this predicate cannot
    observe the narrowing.  `l mod 8` is unchanged by adding a multiple
    of 2^32 because 8 divides 2^32; `l * 8 mod 2^32` is unchanged because
    2^32 divides 8 * 2^32.  So deleting the truncation would leave every
    test in this tree passing.  A spec arm that compared `len` against a
    BOUND would be a different matter.

  inner term is

      `((l * 8) mod 2^32 =? 0)%Z || negb ((l mod 8 =? 0)%Z)`

    with `l := bv_unsigned (abi_low32 len)`.  `Z.mod` on a non-negative
    `l` is Lean's `%` on `Int` (Euclidean, and `l ≥ 0` here because it
    came through `Nat`), the `=?` are `==`, and `negb` is `!` — so the
    term transfers unchanged. -/
def affinity_len_einval_b (len : word) : Bool :=
  let l : Int := ((abi_low32 len).toNat : Int)
  (l * 8) % 2 ^ 32 == 0 || !(l % 8 == 0)

def sched_getaffinity_spec (len : word) : SysSpec SyscallEffect :=
  if affinity_len_einval_b len then err_ret EINVAL else unmodeled

/-! ## sched_setscheduler (119) -/

/- `sched_setscheduler pid policy param` (119).

    Every kernel citation below is at v6.18.46, commit 1f99e9ab748f.

    THE CALL, IN THE ORDER LINUX MAKES ITS DECISIONS.  Four functions,
    all in kernel/sched/syscalls.c bar the last hop:

      SYSCALL_DEFINE3(sched_setscheduler):
        if (policy < 0) return -EINVAL;
      do_sched_setscheduler(pid, policy, param):
        if (unlikely(!param || pid < 0)) return -EINVAL;
        if (copy_from_user(&lparam, param, sizeof(struct sched_param)))
          return -EFAULT;
        CLASS(find_get_task, p)(pid);   /* pid ? find_task_by_vpid(pid): current */
        if (!p) return -ESRCH;
        return sched_setscheduler(p, policy, &lparam);
      _sched_setscheduler(p, policy, param, check = true):
        attr = {.sched_policy = policy,.sched_priority = param->sched_priority,.sched_nice = PRIO_TO_NICE(p->static_prio) };
        if (p->se.custom_slice) attr.sched_runtime = p->se.slice;
        if (policy & SCHED_RESET_ON_FORK) {      /* the legacy hack */
          attr.sched_flags |= SCHED_FLAG_RESET_ON_FORK;
          attr.sched_policy = policy &= ~SCHED_RESET_ON_FORK;
        }
      __sched_setscheduler(p, &attr, user = true, pi = true):
        if (!valid_policy(policy))                    return -EINVAL;
        if (attr->sched_flags & ~(SCHED_FLAG_ALL | SCHED_FLAG_SUGOV))
                                                      return -EINVAL;
        if (attr->sched_priority > MAX_RT_PRIO-1)      return -EINVAL;
        if ((dl_policy(policy) && !__checkparam_dl(attr)) ||
            (rt_policy(policy) != (attr->sched_priority != 0)))
                                                      return -EINVAL;
        user_check_sched_setscheduler(...)            /* -EPERM */
        security_task_setscheduler(p)                 /* an LSM's errno */... scx_check_setscheduler, the SCHED_DEADLINE bandwidth check,
        and then the state change, which returns 0.

    `struct sched_param` is the single `int sched_priority`
    (include/linux/sched.h), so the copy is FOUR bytes and its width is
    not an argument of the call.  `attr.sched_priority` is a `__u32`
    (include/uapi/linux/sched/types.h), so a NEGATIVE `int` priority
    arrives at the `> MAX_RT_PRIO-1` comparison as a large unsigned and
    is -EINVAL — the same answer, by the opposite route, as a priority
    of 100.

    WHAT IS ANSWERED, AND THE ONE THING THAT MAKES IT ANSWERABLE.  Every
    decision above the `user_check_sched_setscheduler` line is a function
    of the ARGUMENTS alone: no `nr_cpu_ids`, no credentials, no rlimit,
    no scheduling state.  So the whole prefix — the two -EINVALs, the
    -EFAULT, and the four -EINVALs `__sched_setscheduler` raises before
    it consults the task — is modeled exactly, in the kernel's order.
    Order is the load-bearing half of that: a call with a negative
    policy AND a null `param` AND an unreadable priority is -EINVAL and
    not -EFAULT, and the `policy < 0` test is why.

    Past that line the answer stops being a function of the arguments,
    with ONE exception, and that exception is this arm's reason to
    exist:

    - SCHED_IDLE AT PRIORITY 0, ON THE CALLING TASK, IS 0.  Walk
      `user_check_sched_setscheduler` with `policy = SCHED_IDLE`:
      `fair_policy(5)`, `rt_policy(5)` and `dl_policy(5)` are all false
      (kernel/sched/sched.h), so the nice, RT-priority and DEADLINE
      gates are skipped; `task_has_idle_policy(p) && !idle_policy(5)` is
      false on its second conjunct WHATEVER `p->policy` is, which is the
      step that removes the scheduling state from the answer;
      `check_same_owner(p)` holds because `p` IS `current`, so its
      `uid_eq(cred->euid, pcred->euid)` compares a task's euid with its
      own; and `p->sched_reset_on_fork` is 0 (below).  It returns 0
      without ever reaching `capable(CAP_SYS_NICE)`, so no capability
      and no rlimit is consulted.  `scx_check_setscheduler`
      (kernel/sched/ext.c) is 0 for every `policy` but SCHED_EXT.  Both
      exits then return 0: if `p->policy` is already SCHED_IDLE the
      `policy == p->policy` fast path stores `reset_on_fork` and returns
      0, and if it is not, `change:` skips the RT-group and DEADLINE
      bandwidth gates (both `rt_policy`/`dl_policy` guarded), performs
      the change and returns 0.

    WHAT SCHED_IDLE ASSUMES, STATED AS SUCH.  Two facts about the
    process, and one about the kernel:

    - `p->sched_reset_on_fork` IS 0.  `sched_fork` (kernel/sched/core.c)
      clears it unconditionally on the branch that reads it —
      `if (unlikely(p->sched_reset_on_fork)) { ...; p->sched_reset_on_fork = 0; }`
      — so a task has it clear at the moment `fork` returns, whether or
      not the parent had it set.  It is the last gate of
      `user_check_sched_setscheduler`, and with it SET an unprivileged
      SCHED_IDLE call is -EPERM rather than 0.
    - `p` IS NOT SCHED_DEADLINE.  The same `sched_fork` returns -EAGAIN
      for `dl_prio(p->prio)`, so a SCHED_DEADLINE task cannot fork at
      all and no child is one.  Nothing in the modeled run can make the
      process one either: this arm answers -EINVAL for SCHED_DEADLINE
      (see below) and `sched_setattr` (274) has no arm.  If it were one,
      the `(dl_policy(policy) || dl_task(p)) && sched_dl_overflow(...)`
      gate would run.
    - NO LSM.  `security_task_setscheduler` (kernel/sched/syscalls.c)
      is 0 under the model's standing position that no LSM is
      registered, the same one
      `Fs.Fcntl.fcntl_spec` takes for `security_file_fcntl` and
      `Fs.Stat.newfstatat_spec` for `security_inode_getattr`.

    The first two hold at `execve` and are preserved by every syscall
    the model admits; what they exclude is a LAUNCHER that changed the
    child's scheduling parameters between `fork` and `exec`.  That is
    the same world `State.init_model` already pins by deriving the
    effective and saved ids from the real ones — an ordinary exec — and
    a run launched otherwise is outside this model, exactly as a run
    with file capabilities is.

    WHY THERE IS NO STATE FIELD, and what would falsify that.  A
    SCHED_IDLE call really does write `p->policy`, `p->rt_priority`,
    `p->prio` and `p->sched_class`, and this model carries none of them.
    That is sound because the model DECLINES every call whose answer
    depends on them, and the declines are not incidental:
    SCHED_NORMAL and SCHED_BATCH are declined precisely because
    `task_has_idle_policy(p)` decides them — a task already SCHED_IDLE
    needs `RLIMIT_NICE` or CAP_SYS_NICE to leave, and this arm can PUT
    it there — and SCHED_FIFO/SCHED_RR because `RLIMIT_RTPRIO`,
    `p->rt_priority` and CAP_SYS_NICE decide them.  No other modeled
    syscall reads a scheduling parameter; `sched_getscheduler` (120),
    `sched_getparam` (121), `sched_getattr` (274), `sched_setattr` (274)
    and `getpriority` (141) have no arms.  THIS STOPS BEING TRUE THE DAY
    ANY OF THOSE FIVE LANDS, or the day SCHED_NORMAL is answered: each
    of them needs a `Model` field pinned the way `State.limst_core` pins
    RLIMIT_CORE, and this arm has to gain it FIRST or it starts
    answering a call the reader can then observe was wrong.

    THE ONE PIECE OF STATE THAT IS READ ELSEWHERE is
    `p->timer_slack_ns`, which `Kernel.Time.Hrtimer.nanosleep_spec`
    argues about.  `__setscheduler_params` (kernel/sched/syscalls.c)
    zeroes it for
    `rt_or_dl_task_policy(p)` and otherwise restores
    `p->default_timer_slack_ns` if it is 0, so a move to SCHED_IDLE
    either leaves it alone (the usual case, where it is nonzero) or
    RAISES it from 0 to the default.  Neither direction reaches the
    nanosleep model, whose remainder is deliberately unbounded from
    above; what the move cannot do is make the task RT or DL, which is
    the condition those arguments actually turn on.

    WHY SCHED_EXT (7) IS DECLINED AND NOT ANSWERED.  `valid_policy` is
    `idle_policy || fair_policy || rt_policy || dl_policy`, and
    `normal_policy` — the first disjunct of `fair_policy` — reads
    `if (policy == SCHED_EXT) return true;` under
    `#ifdef CONFIG_SCHED_CLASS_EXT` (kernel/sched/sched.h).  So whether
    7 is a valid policy at all is a config question, and this model does
    not fix that config.  A priority the `> MAX_RT_PRIO-1` gate refuses,
    or a nonzero one the `rt_policy(7) != (priority != 0)` gate refuses,
    happens to be -EINVAL under BOTH configs; policy 7 at priority 0 is
    not, so the whole number is declined rather than half of it.

    WHY SCHED_DEADLINE (6) IS -EINVAL AND NEVER ANYTHING ELSE.  The
    legacy entry point cannot express a DEADLINE parameter set:
    `_sched_setscheduler` builds an `attr` whose `sched_deadline` is 0,
    and `__checkparam_dl` (kernel/sched/deadline.c) refuses
    `attr->sched_deadline == 0`, so `dl_policy(policy) &&
    !__checkparam_dl(attr)` fires for every `param` a caller can pass.
    That is what makes the second assumption above self-maintaining.

    WHY A NONZERO pid THAT IS NOT THE CALLER IS DECLINED.  `pid = 0` is
    `current` by `find_process_by_pid`, and a `pid` equal to the tid the
    model has pinned (`State.procst_tid`, which musl's
    `pthread_setschedparam` supplies — it passes `t->tid`, not 0) is
    that same task.  Any OTHER positive pid is a task this model has no
    representation of: whether one exists at all decides -ESRCH, and if
    one does, `check_same_owner` and its credentials decide the rest.
    So the model cannot tell -ESRCH from a permitted call, and declines.
    A pid the model has not pinned a tid for is declined for the same
    reason: with `m_tid` still `None` the model cannot say whether the
    number names the caller.

    THE COPY-IN IS RECORDED ON EVERY PATH PAST IT, including the four
    -EINVALs and every decline, because `copy_from_user` runs BEFORE the
    task lookup and before `__sched_setscheduler` sees the policy.  A
    -EFAULT records nothing: an `access_ok` refusal happens before any
    load.  A range `access_ok` admits that is not wholly mapped is
    `unmodeled` rather than -EFAULT, for the reason
    `Kernel.Sys.prlimit64_spec` gives for its own `new_rlim` — Linux
    answers -EFAULT there too, but which bytes it read first is not
    something the ledger can state.

    COST OF THE DECLINES.  A program that lowers itself to SCHED_IDLE
    stays inside the modeled surface, which is the shape a
    `pthread_setschedparam(self, SCHED_IDLE, {0})` takes; a program that
    RAISES its policy, that sets one on another task, or that returns
    from SCHED_IDLE to SCHED_NORMAL, leaves it. -/
/-- `valid_policy` minus SCHED_EXT, which is declined before this test
    is reached.  Written as a membership test because the six numbers
    are not an interval: the header leaves 4 to an unimplemented
    SCHED_ISO. -/
def sched_valid_policy_b (pol : Int) : Bool :=
  pol == SCHED_NORMAL || pol == SCHED_FIFO || pol == SCHED_RR
    || pol == SCHED_BATCH || pol == SCHED_IDLE || pol == SCHED_DEADLINE

/-- `rt_policy`, which is config-independent. -/
def sched_rt_policy_b (pol : Int) : Bool :=
  pol == SCHED_FIFO || pol == SCHED_RR

/-- Whether the call names the CALLING task, which is the only task this
    model represents.  `find_process_by_pid` is
    `pid ? find_task_by_vpid(pid) : current`, so a zero pid always does;
    a positive one does exactly when it is the pinned tid.  The pid is
    read at `pid32` width because it arrives as a `pid_t`, and the zero
    test is on those low 32 bits for the same reason — a register whose
    low half is zero IS a zero pid to the kernel. -/
def sched_targets_self_b (pid : word) (m : Model) : Bool :=
  w_is0 (pid32 pid)
    || (match m_tid m with
        | some tid => pid32 pid == tid
        | none => false)

/-- THE `SCHED_RESET_ON_FORK` TEST that opens `__sched_setscheduler`'s
    chain, written inline as

      `negb (Z.land pol SCHED_RESET_ON_FORK =? 0)%Z`

    i.e. "the RESET_ON_FORK bit is set in `pol`", `Z.land` being the
    bitwise and on `Z`.

  Lean core has no `Int.land`
    (its bitwise operations are `Nat`-only at v4.31.0), so the term
    cannot be transliterated.  `Z.land pol SCHED_RESET_ON_FORK` for the
    single-bit mask `2^30` is "bit 30 of `pol`'s two's-complement
    representation", and Euclidean division reads that bit off:
    `2^30 > 0`, so `Int.ediv pol 2^30` is `floor (pol / 2^30)` and
    `Int.emod _ 2` is the bit itself, for NEGATIVE `pol` too
    (`pol = -1` gives `ediv = -1`, `emod = 1`; `pol = -2^31` gives
    `ediv = -2`, `emod = 0`).  So this is the same test on all of `Int`,
    not only on the non-negative `bv_unsigned` the one call site passes.

    `_sched_setscheduler` strips the bit before `valid_policy` ever runs. -/
def sched_reset_on_fork_b (pol : Int) : Bool :=
  Int.emod (Int.ediv pol SCHED_RESET_ON_FORK) 2 == 1

/-- EVERYTHING `__sched_setscheduler` DECIDES ONCE THE TASK IS IN HAND,
    as one function of the policy word and the copied-in priority:
    `Some r` is the value `a0` takes, `None` is the decline.  Written
    apart from the spec because it is the whole of what the checker in
    `Checks/Sys/Kernel/Sched/Syscalls.lean` mirrors, and a single ordered
    chain is easier to compare against the kernel's than the same chain
    transcribed twice.

    THE ORDER IS THE KERNEL'S, and the two declines are placed where
    Linux's decision sits rather than at the front: `SCHED_RESET_ON_FORK`
    is stripped by `_sched_setscheduler` before `valid_policy` runs, and
    SCHED_EXT is a `valid_policy` question, so both precede every
    -EINVAL below them.  Declining early is what fail-closed costs here;
    answering early would be a wrong answer.

    `prio` is the `__u32` the `int sched_priority` was widened to, so
    the `> MAX_RT_PRIO-1` test catches a negative `int` as well as a
    priority of 100 or more, and `prio != 0` is the
    `attr->sched_priority != 0` the RT/non-RT agreement test compares
    against. -/
def sched_setscheduler_answer (pol prio : Int) : Option word :=
  if sched_reset_on_fork_b pol then none
  else if pol == SCHED_EXT then none
  else if !sched_valid_policy_b pol then some (errno_ret EINVAL)
  else if MAX_RT_PRIO - 1 < prio then some (errno_ret EINVAL)
  else if pol == SCHED_DEADLINE then some (errno_ret EINVAL)
  else if xor (sched_rt_policy_b pol) (!(prio == 0)) then
    some (errno_ret EINVAL)
  else if pol == SCHED_IDLE then some (BitVec.ofInt 64 0)
  else none

def sched_setscheduler_spec (pid policy param : word) : SysSpec SyscallEffect :=
  if sint32 policy < 0 then err_ret EINVAL
  else if w_is0 param || decide (sint32 pid < 0) then err_ret EINVAL
  else
    bind inputSpec fun i =>
    bind getModelSpec fun m =>
    match read_bytes_map i.in_mem param (BitVec.ofInt 64 4) with
    | none =>
        if !access_okb param 4 then err_ret EFAULT else unmodeled
    | some bs =>
        record_copyins [(param, 4)]
          (if !sched_targets_self_b pid m then unmodeled
           else
             match sched_setscheduler_answer ((abi_low32 policy).toNat : Int)
                     ((le_bytes_to_word bs).toNat : Int) with
             | some r => ret_only r
             | none => unmodeled)

/-! ## sched_yield (124) -/

/-- `sched_yield` (124): 0, with nothing this model can see changed.

    (Linux v6.12.1, kernel/sched/syscalls.c,
    `SYSCALL_DEFINE0(sched_yield)`, whose whole body is
    `do_sched_yield(); return 0;` and whose kernel-doc says "Return: 0."
    The number has one entry point: include/uapi/asm-generic/unistd.h
    wires 124 with `__SYSCALL` and not `__SC_COMP`, so there is no
    compat body to land in the way `sched_getaffinity` above has.)

    NO ARGUMENT IS READ, and that is a fact about the declaration rather
    than about this spec's convenience.  riscv64 overrides
    `SYSCALL_DEFINE0` (arch/riscv/include/asm/syscall_wrapper.h) to take
    `const struct pt_regs *__unused` and to expand without
    `SC_RISCV_REGS_TO_ARGS`, so no argument register reaches the body on
    this path.  Ignoring all six argument words is therefore exact, not
    an approximation, and a spec that refused some argument shape would
    be wrong about a call Linux answers 0.

    WHAT `do_sched_yield` DOES, and why none of it is modeled state: it
    takes the run queue lock, bumps `rq->yld_count`, calls the
    scheduling class's `yield_task`, and calls `schedule`.  All four are
    per-run-queue scheduler bookkeeping.  Nothing there is reachable
    through the syscall interface this model covers — the model carries
    no run queue, no scheduling class and no notion of which task holds
    a CPU — so an arm that changed no model state is not discarding an
    effect a later call could observe.  What `schedule` really costs is
    TIME, and time is where this arm stops being the whole truth:
    another task may run in between, so a `sched_yield` can separate two
    of this process's observations.  That costs nothing here because
    this model has one process — `Fork.clone_fork_flags_b` admits
    `SIGCHLD` alone and every sharing flag forces `Unmodeled`, so there
    is no second thread whose interleaving a yield could expose.  The
    day a shared-memory clone is modeled, this comment is what has to be
    re-read.

    Residual infidelity, stated rather than modeled, and shared with
    every zero-argument arm here: `SYSCALL_DEFINE0` emits
    `ALLOW_ERROR_INJECTION(..., ERRNO)`, riscv's override included, so
    on a kernel built with `CONFIG_FUNCTION_ERROR_INJECTION` and running
    a BPF program that calls `bpf_override_return` the call can be made
    to return an errno.  The model describes a kernel with no such
    override attached; `Kernel.Sys.getpid_spec` carries the same note. -/
def sched_yield_spec : SysSpec SyscallEffect :=
  ret_only (BitVec.ofInt 64 0)

/-! ## Sanity checks on the computable parts

  These pin the arms its prose argues for, one per claim: `sched_getaffinity`'s two
  gates (an unaligned length, a length whose bit count wraps to zero, a zero length)
  and the decline that follows them; `abi_low32` being documentation rather than
  arithmetic; `sched_setscheduler`'s ordered chain and the copy-in ledger on each of
  its paths; and `sched_yield`'s 0.

    -/

/-- A syscall input whose memory holds a `struct sched_param` at address
    4 — `sched_priority = 0`, little-endian — and nothing else.  Address 4
    and not 0: a zero `param` is the null-pointer gate, which is a
    different arm.  `sanityMem` is `StateMemory`'s test memory; no part of
    the model refers to it. -/
private def demoInput : SyscallInput :=
  { in_sysno := 119, in_args := [],
    in_mem := sanityMem [0, 0, 0, 0, 0, 0, 0, 0], in_wmem := fun _ => none }

/-- The same struct with `sched_priority = 100` — the first priority
    `__sched_setscheduler` refuses. -/
private def prio100Input : SyscallInput :=
  { in_sysno := 119, in_args := [],
    in_mem := sanityMem [0, 0, 0, 0, 100, 0, 0, 0], in_wmem := fun _ => none }

/-- An input with NOTHING mapped: every `param` pointer resolves against
    no byte at all, at every address. -/
private def emptyInput : SyscallInput :=
  { in_sysno := 119, in_args := [], in_mem := fun _ => none,
    in_wmem := fun _ => none }

/-- A model with no pinned tid: `m_tid` is `none`, so only a zero pid can
    name the caller. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The effect of a call that answered `r` after copying `param` in: the
    answer, no writes, and the copy-in range on the ledger. -/
private abbrev effCopy (r param : word) : SyscallEffect :=
  ⟨r, [], [], [], [], [(param, 4)]⟩

/-- Reading the syscall input is pure — the twin of `Monad.bind_getModel`,
    proved here once.  No such lemma is needed elsewhere: the `input` read
    and the rest of the chain are one `bind`. -/
private theorem bind_inputSpec {A : Type} (k : SyscallInput → SysSpec A)
    (i : SyscallInput) (m : Model) (o : Outcome A Model event) :
    bind inputSpec k i m o ↔ k i i m o := by
  cases o with
  | ok x m' evs =>
      simp only [bind]
      constructor
      · rintro ⟨x0, m1, evs1, evs2, h1, h2, h3⟩
        simp only [inputSpec, input, Outcome.ok.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        simp only [List.nil_append] at h3
        subst h3
        exact h2
      · intro h
        exact ⟨i, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
      simp only [bind]
      constructor
      · rintro (h | ⟨x0, m1, evs1, h1, h2⟩)
        · exact absurd h (by simp [inputSpec, input])
        · simp only [inputSpec, input, Outcome.ok.injEq] at h1
          obtain ⟨rfl, rfl, rfl⟩ := h1
          exact h2
      · intro h
        exact Or.inr ⟨i, m, [], rfl, h⟩

/-- `record_copyins reads (ret_only r)`: the answer `r`, no writes, and
    `reads` on the ledger.  (`record_copyins` prepends to `eff.eff_copyins`,
    which is `[]` for `ret_only`, so the `reads ++ []` it builds is that
    same list.) -/
private theorem record_copyins_ret_only_ok (reads : List (word × Nat))
    (r : word) (i : SyscallInput) (m : Model) :
    record_copyins reads (ret_only r) i m
      (.ok ⟨r, [], [], [], [], reads⟩ m []) := by
  refine ⟨mkEffect r [] [], m, [], [], rfl, ?_, rfl⟩
  simp [pure, with_copyins, List.append_nil]

/-- `record_copyins` over a decline is still the decline: the copy-in is
    recorded only on the paths that reach it, and a decline is one. -/
private theorem record_copyins_unmodeled_ok (reads : List (word × Nat))
    (i : SyscallInput) (m : Model) :
    record_copyins reads unmodeled i m .unmodeled :=
  record_copyins_unmodeled (unmodeled_intro i m)

/-! ### sched_getaffinity: the two gates, and the decline behind them -/

/-- 3 is not a multiple of 8: the alignment gate answers -EINVAL. -/
example (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec 3 i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h : affinity_len_einval_b (3 : word) = true := by decide
  unfold sched_getaffinity_spec
  rw [ite_eq_left h]
  rfl

/-- `len * 8` wraps MODULO 2^32, so a length of 2^29 — a multiple of 8,
    and a length that would look well formed to a model doing the
    multiplication over the integers — has a bit count of ZERO and is
    -EINVAL. -/
example : affinity_len_einval_b (BitVec.ofInt 64 536870912) = true := by
  decide

/-- The same value through the syscall. -/
example (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec (BitVec.ofInt 64 536870912) i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h : affinity_len_einval_b (BitVec.ofInt 64 536870912) = true := by decide
  unfold sched_getaffinity_spec
  rw [ite_eq_left h]
  rfl

/-- A length of 0 is a multiple of 8 AND its bit count is 0 — the wrap
    case on the smallest multiple of 2^29. -/
example (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec 0 i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h : affinity_len_einval_b (0 : word) = true := by decide
  unfold sched_getaffinity_spec
  rw [ite_eq_left h]
  rfl

/-- 8 is a nonzero multiple of 8: neither gate fires, and the spec
    DECLINES.  This is the successful path waiting on `nr_cpu_ids` and
    `cpumask_size()` — the decline the prose above argues for. -/
example (i : SyscallInput) (m : Model) :
    sched_getaffinity_spec 8 i m .unmodeled := by
  have h : ¬ (affinity_len_einval_b (8 : word) = true) := by decide
  unfold sched_getaffinity_spec
  rw [ite_eq_right h]
  rfl

/-- `abi_low32` is DOCUMENTATION here, not arithmetic: 2^32 + 3 and 3 are
    the same predicate value, because 8 divides 2^32 — deleting the
    truncation would leave this test passing. -/
example : affinity_len_einval_b (BitVec.ofInt 64 (4294967296 + 3))
    = affinity_len_einval_b (BitVec.ofInt 64 3) := by
  decide

/-! ### sched_setscheduler: the chain, and the copy-in ledger -/

/-- The answer chain itself, arm by arm.

    A policy outside `valid_policy` — 4, the number the header reserves
    for the unimplemented SCHED_ISO — is -EINVAL. -/
example : sched_setscheduler_answer 4 0 = some (errno_ret EINVAL) := by decide

/-- SCHED_DEADLINE is -EINVAL and never anything else: the legacy entry
    point builds an `attr` whose `sched_deadline` is 0, which
    `__checkparam_dl` refuses. -/
example : sched_setscheduler_answer 6 0 = some (errno_ret EINVAL) := by decide

/-- A priority above `MAX_RT_PRIO-1` is -EINVAL — 100 is the first one
    the kernel refuses. -/
example : sched_setscheduler_answer 1 100 = some (errno_ret EINVAL) := by
  decide

/-- 99 is the last priority it accepts, and SCHED_FIFO at 99 is DECLINED
    rather than answered: `RLIMIT_RTPRIO`, `p->rt_priority` and
    CAP_SYS_NICE decide it. -/
example : sched_setscheduler_answer 1 99 = none := by decide

/-- SCHED_FIFO at priority 0 is the RT/non-RT disagreement: -EINVAL. -/
example : sched_setscheduler_answer 1 0 = some (errno_ret EINVAL) := by decide

/-- …and SCHED_IDLE at a NONZERO priority is the same disagreement. -/
example : sched_setscheduler_answer 5 1 = some (errno_ret EINVAL) := by decide

/-- SCHED_IDLE at priority 0 is the one arm that is answered: 0. -/
example : sched_setscheduler_answer 5 0 = some 0 := by decide

/-- SCHED_NORMAL at priority 0 is DECLINED — `task_has_idle_policy` decides
    it, and the model carries no scheduling state to decide it with. -/
example : sched_setscheduler_answer 0 0 = none := by decide

/-- SCHED_EXT at priority 0 is DECLINED: whether 7 is a valid policy at
    all is a `CONFIG_SCHED_CLASS_EXT` question. -/
example : sched_setscheduler_answer 7 0 = none := by decide

/-- The RESET_ON_FORK bit declines before any policy test — SCHED_IDLE
    with the bit ORed in is not SCHED_IDLE. -/
example :
    sched_setscheduler_answer (SCHED_IDLE + SCHED_RESET_ON_FORK) 0 = none := by
  decide

/-- …and `sched_reset_on_fork_b` is `negb (Z.land pol SCHED_RESET_ON_FORK
    =? 0)` on ALL of `Int`, negative `pol` included, which is what lets
  this tree take the same branch the kernel does: bit 30 of the
    two's-complement representation.  A plain `pol / 2^30 % 2` on
    TRUNCATING division would get the first one wrong. -/
example : sched_reset_on_fork_b (-1) = true := by decide

example : sched_reset_on_fork_b (-2147483648) = false := by decide

example : sched_reset_on_fork_b 5 = false := by decide

example : sched_reset_on_fork_b SCHED_RESET_ON_FORK = true := by decide

/-- A NEGATIVE policy is -EINVAL and is refused BEFORE the copy: no
    copy-in is recorded, because none happened. -/
example (m : Model) :
    sched_setscheduler_spec 0 (BitVec.ofInt 64 (-1)) 4 demoInput m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h : sint32 (BitVec.ofInt 64 (-1)) < 0 := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_left h]
  rfl

/-- A null `param` is -EINVAL, after the policy sign test and before any
    load — and again no copy-in. -/
example (m : Model) :
    sched_setscheduler_spec 0 5 0 demoInput m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : (w_is0 (0 : word) || decide (sint32 (0 : word) < 0)) = true := by
    decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_left h2]
  rfl

/-- A NEGATIVE pid is -EINVAL the same way, and the copy has not happened
    either. -/
example (m : Model) :
    sched_setscheduler_spec (BitVec.ofInt 64 (-1)) 5 4 demoInput m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : (w_is0 (4 : word)
      || decide (sint32 (BitVec.ofInt 64 (-1)) < 0)) = true := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_left h2]
  rfl

/-- The `param` pointer past the gates, resolved against `demoInput`'s
    memory: four zero bytes at address 4. -/
private theorem demo_read :
    read_bytes_map demoInput.in_mem 4 (BitVec.ofInt 64 4) = some [0, 0, 0, 0] := by
  decide

/-- …and the same struct with priority 100 at `prio100Input`. -/
private theorem prio100_read :
    read_bytes_map prio100Input.in_mem 4 (BitVec.ofInt 64 4)
      = some [100, 0, 0, 0] := by
  decide

/-- A zero pid always names the caller, whatever the model's tid is: the
    first disjunct of `sched_targets_self_b` short-circuits. -/
private theorem self_zero (m : Model) :
    sched_targets_self_b (0 : word) m = true := by
  unfold sched_targets_self_b
  rw [show w_is0 (pid32 (0 : word)) = true from by decide]
  rfl

/-- …and for a zero pid the spec takes the ANSWER branch, not the
    decline: the `!sched_targets_self_b` test is false. -/
private theorem not_self_zero (m : Model) :
    ¬ ((!sched_targets_self_b (0 : word) m) = true) := by
  rw [self_zero]
  simp

/-- A positive pid names the caller only when the model has pinned it: with
    `m_tid = none`, 7 does not. -/
example : sched_targets_self_b (7 : word) demoModel = false := by
  unfold sched_targets_self_b
  rw [show w_is0 (pid32 (7 : word)) = false from by decide]
  rfl

/-- A bad policy (4, the unimplemented SCHED_ISO) is -EINVAL, and the
    copy-in IS on the ledger: `copy_from_user` ran before the policy was
    looked at. -/
example :
    sched_setscheduler_spec 0 4 4 demoInput demoModel
      (.ok (effCopy (errno_ret EINVAL) 4) demoModel []) := by
  have h1 : ¬ (sint32 (4 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hans : sched_setscheduler_answer ((abi_low32 (4 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = some (errno_ret EINVAL) := by
    decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [demo_read]
  rw [ite_eq_right (not_self_zero demoModel), hans]
  exact record_copyins_ret_only_ok [(4, 4)] (errno_ret EINVAL) demoInput demoModel

/-- A priority of 100 is -EINVAL, with the copy recorded: the same answer
    a negative `int` priority takes, by the `__u32` widening. -/
example :
    sched_setscheduler_spec 0 1 4 prio100Input demoModel
      (.ok (effCopy (errno_ret EINVAL) 4) demoModel []) := by
  have h1 : ¬ (sint32 (1 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hans : sched_setscheduler_answer ((abi_low32 (1 : word)).toNat : Int)
      ((le_bytes_to_word [100, 0, 0, 0]).toNat : Int)
        = some (errno_ret EINVAL) := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [prio100_read]
  rw [ite_eq_right (not_self_zero demoModel), hans]
  exact record_copyins_ret_only_ok [(4, 4)] (errno_ret EINVAL) prio100Input demoModel

/-- THE SUCCESS ARM: SCHED_IDLE at priority 0 on the calling task answers
    0, with the copy-in recorded. -/
example :
    sched_setscheduler_spec 0 5 4 demoInput demoModel
      (.ok (effCopy 0 4) demoModel []) := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hans : sched_setscheduler_answer ((abi_low32 (5 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = some 0 := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [demo_read]
  rw [ite_eq_right (not_self_zero demoModel), hans]
  exact record_copyins_ret_only_ok [(4, 4)] 0 demoInput demoModel

/-- SCHED_NORMAL at priority 0 is DECLINED, with the copy-in recorded —
    the decline the prose's `task_has_idle_policy` argument is about. -/
example :
    sched_setscheduler_spec 0 0 4 demoInput demoModel .unmodeled := by
  have h1 : ¬ (sint32 (0 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hans : sched_setscheduler_answer ((abi_low32 (0 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = none := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [demo_read]
  rw [ite_eq_right (not_self_zero demoModel), hans]
  exact record_copyins_unmodeled_ok [(4, 4)] demoInput demoModel

/-- SCHED_EXT at priority 0 is DECLINED — and the copy-in is still
    recorded, because it happened. -/
example :
    sched_setscheduler_spec 0 7 4 demoInput demoModel .unmodeled := by
  have h1 : ¬ (sint32 (7 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hans : sched_setscheduler_answer ((abi_low32 (7 : word)).toNat : Int)
      ((le_bytes_to_word [0, 0, 0, 0]).toNat : Int) = none := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [demo_read]
  rw [ite_eq_right (not_self_zero demoModel), hans]
  exact record_copyins_unmodeled_ok [(4, 4)] demoInput demoModel

/-- A NONZERO pid that is not the caller is DECLINED: with `m_tid` still
    `none`, the model cannot say whether 7 names it. -/
example :
    sched_setscheduler_spec 7 5 4 demoInput demoModel .unmodeled := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4 : word) || decide (sint32 (7 : word) < 0)) = true) := by
    decide
  have hself : (!sched_targets_self_b (7 : word) demoModel) = true := by
    unfold sched_targets_self_b
    rw [show w_is0 (pid32 (7 : word)) = false from by decide]
    rfl
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [demo_read]
  rw [ite_eq_left hself]
  exact record_copyins_unmodeled_ok [(4, 4)] demoInput demoModel

/-- A range `access_ok` REFUSES is -EFAULT, and it records NOTHING: no load
    happened. -/
example :
    sched_setscheduler_spec 0 5 (BitVec.ofInt 64 (-1)) emptyInput demoModel
      (.ok (mkEffect (errno_ret EFAULT) [] []) demoModel []) := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (BitVec.ofInt 64 (-1))
      || decide (sint32 (0 : word) < 0)) = true) := by decide
  have hread : read_bytes_map emptyInput.in_mem (BitVec.ofInt 64 (-1))
      (BitVec.ofInt 64 4) = none := by decide
  have hok : (!access_okb (BitVec.ofInt 64 (-1)) 4) = true := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [hread]
  rw [ite_eq_left hok]
  rfl

/-- A range `access_ok` ADMITS that is not wholly mapped is `unmodeled`,
    not -EFAULT: which bytes the copy read first is not something the
    ledger can state. -/
example :
    sched_setscheduler_spec 0 5 4096 emptyInput demoModel .unmodeled := by
  have h1 : ¬ (sint32 (5 : word) < 0) := by decide
  have h2 : ¬ ((w_is0 (4096 : word) || decide (sint32 (0 : word) < 0)) = true) := by
    decide
  have hread : read_bytes_map emptyInput.in_mem (4096 : word)
      (BitVec.ofInt 64 4) = none := by decide
  have hok : ¬ ((!access_okb (4096 : word) 4) = true) := by decide
  unfold sched_setscheduler_spec
  rw [ite_eq_right h1, ite_eq_right h2]
  simp only [bind_inputSpec, getModelSpec, bind_getModel]
  simp only [hread]
  rw [ite_eq_right hok]
  rfl

/-! ### sched_yield: 0, and nothing else -/

/-- `sched_yield` answers 0 with an EMPTY effect: no writes, no zeroed
    ranges, no copies, and nothing on the copy-in ledger. -/
example (i : SyscallInput) (m : Model) :
    sched_yield_spec i m (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  simp [sched_yield_spec, ret_only, pure]

end LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
