/-
  * LinuxProcessSem.Sys.Kernel.Time.PosixTimers — clock_gettime (113)

    This file answers to Linux [kernel/time/posix-timers.c]: it holds
    what the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.lean] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.lean] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.


  - UPSTREAM'S `set_clock` HAS NO LEAN COUNTERPART IN `Monad.lean`.  It is
    `Definition set_clock (t : word) : Sys unit := modify (with_clock t)`
  in ``, i.e. exactly `modify` applied to
    `StateLedger`'s `with_clock`; the monotonic arm below spells that term
    out rather than restating the definition here, because this file owns
    no `Monad.lean` item.  The term is the same, so nothing is weakened.
  - `m_clock`/`with_clock` are `StateLedger`'s; `read_bytes_map` is
    `StateMemory`'s; `CLOCK_*`, `tv_frac_of`, `timespec_ns`,
    `timespec_ns_signed` and `CLOCK_NS_ENVELOPE` are `Sys/Uapi`'s;
    `mkEffect`/`errno_ret` are `State.lean`'s.
  - `clockid32` (`Sys/Syscall.lean`) is applied ONCE, at the ABI boundary
    in `Sys.SyscallTable.spec_table`, exactly as the kernel narrows the
    `clockid_t`; `clock_gettime_spec` therefore receives an already
    truncated id, as does.
  - IMPORTS.  `Require Export Syscall Uapi Uaccess` becomes the
    imports below, with two differences.  `Sys/Uaccess.lean` is not
    imported: it still carries staging copies of `ret_only`/`err_ret`
    that this file does not use (every decline here is `unmodeled`, never
    an `errno`), and `read_bytes_map` is reached from `StateMemory`
    directly.  `Sys/Syscall.lean` IS imported for `clockid32`'s
    documentation of the ABI narrowing, which the note above cites, even
    though no identifier from it appears in a definition here.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.StateMatrix
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers

/-! ## Why `Uapi.CLOCK_NS_ENVELOPE` bounds this clock.

    The envelope is a fact about `ktime_t`'s range; that a
    `CLOCK_MONOTONIC` reading stays inside it is a fact about the path
    `clock_gettime` takes, and that path does not materialize a `ktime_t`
    at all: `posix_get_monotonic_timespec` calls `ktime_get_ts64`
    (kernel/time/timekeeping.c), which fills the `timespec64` directly
    from `tk->xtime_sec` plus `wall_to_monotonic` via
    `timespec64_add_ns`, and then `timens_add_monotonic` adds the time
    namespace's offset.  That last one is a `static inline` in
    include/linux/time_namespace.h — NOT kernel/time/namespace.c, which
    holds the offset's WRITE path instead — and is byte-identical at
    v6.10-v6.15, compiling to an empty body when CONFIG_TIME_NS is off.

    Both the clock and that offset are signed 64-bit nanosecond counts,
    and the offset is bounded where it is SET, by
    `proc_timens_set_offset` (kernel/time/namespace.c, byte-identical
    across the range): it refuses an offset whose `tv_sec` exceeds
    `KTIME_SEC_MAX`, and then refuses again unless the resulting
    `tv_sec` is at or below `KTIME_SEC_MAX / 2` — the halving is
    deliberate, and the comment beside it says why, "to be sure that
    KTIME_MAX is still unreachable".  So the sum a
    `struct __kernel_timespec` can report cannot exceed 2^63
    nanoseconds — about 292 years.  The bound is a kernel fact rather
    than a modeling convenience.

    It is also what keeps `Uapi.tv_sec_of`/`Uapi.tv_frac_of` in the
    non-negative range: at `t < 2^63` both `t / 10^9` and `t mod 10^9`
    are non-negative, so neither field of the timespec is ever an `s64`
    the kernel could not have produced.

    The bound on `m_clock` is tested SEPARATELY in each of the three
    layers — here, in `Checks/Sys/Kernel/Time/PosixTimers.check_clock_gettime`
    and in `Checks/Witness/Kernel/Time/PosixTimers.clock_gettime_witness`
    — and that repetition is structural rather than an oversight.  The
    acceptor and the witness are verified AGAINST this spec, by the four
    soundness/completeness lemmas and by `clock_gettime_witness_ok`;
    they may not import its reasoning, or the proofs would be circular
    and a wrong guard would agree with itself.  Each layer therefore
    restates the test and the lemmas are what force the three to
    coincide.  Contrast the per-reading conditions, which ARE shared:
    `timespec_ok_b` is one definition used by name in all three places,
    because a reading is checked against a value rather than deciding
    whether a layer runs at all. -/

/-- What a `CLOCK_MONOTONIC` reading of `bs`, following a previous
    reading of `prev`, must satisfy.  Defined ONCE and used by name by
    `clock_gettime_spec`, by the acceptor and by the witness, so that a
    later change to the conditions cannot prove one thing and execute
    another.  Four conditions:

    - EXACTLY 16 BYTES — the size of the struct the kernel writes.
    - `tv_nsec` IS NORMALIZED, below 10^9.  On this path the
      normalization is `timespec64_add_ns` (include/linux/time64.h),
      which carries whole seconds out of the nanosecond field as it
      adds, and — under CONFIG_TIME_NS — `set_normalized_timespec64`
      (kernel/time/time.c) reached from `timens_add_monotonic`.  (NOT
      `ktime_to_timespec64`, which is a macro alias for
      `ns_to_timespec64` and belongs to the `.clock_get_ktime` path
      `clock_gettime` never calls.)  So a kernel never writes a
      nanosecond field at or above a full second.  This is the
      condition that makes the two fields a unique reading rather than
      one of many spellings of the same instant.
    - THE READING DOES NOT PRECEDE `prev` — `CLOCK_MONOTONIC`'s whole
      guarantee.  Non-strict: the clock never runs backwards, but it is
      not required to advance between two reads, and a coarse
      clocksource really does answer two quick calls alike.
    - THE READING IS BELOW `CLOCK_NS_ENVELOPE`, so it is a time
      `ktime_t` can represent. -/
def timespec_ok_b (bs : List byte) (prev : word) : Bool :=
  (bs.length == 16)
  && decide (tv_frac_of bs < 1000000000)
  && decide ((prev.toNat : Int) ≤ timespec_ns bs)
  && decide (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- What a `CLOCK_REALTIME` reading of `bs` must satisfy.  It is
    `timespec_ok_b` MINUS ONE CONJUNCT, and the missing one is the
    point of this definition: there is no `prev`.

    THE WALL CLOCK CARRIES NO GUARANTEE IN EITHER DIRECTION, so there
    is nothing to relate this reading to and no model field to record
    it in.  Two writers settle that, and neither needs the modeled
    process to do anything:

    - `do_settimeofday64` (kernel/time/timekeeping.c) refuses NOTHING
      for setting the wall clock EARLIER.  Its only ordering check is
      `timespec64_compare(&tks->wall_to_monotonic, &ts_delta) > 0`,
      which is -EINVAL — the wall clock may not be set below
      CLOCK_MONOTONIC — and that is a floor at the boot instant, not a
      ratchet at the last reading.  Between any two readings the clock
      may be set anywhere above that floor, backwards included.
    - `adjtimex`'s `ADJ_SETOFFSET` reaches
      `timekeeping_inject_offset` (same file), which adds a SIGNED
      `struct timespec64` straight from userspace, subject only to a
      normalized `tv_nsec`, the same `wall_to_monotonic` floor, and
      `timespec64_valid_settod` on the result.  A negative offset is
      exactly how NTP steps the clock backwards.

    (Both are byte-identical at v6.13-v6.15; the v6.10-v6.12 spellings
    take the timekeeper lock by hand and hold an explicit `ret` instead
    of using `scoped_guard` and `timekeeping_restore_shadow`, with the
    same two -EINVAL conditions and the same writes.  All of it holds
    on the linux-6.10.y through linux-6.15.y stable branches too.)

    A FIELD WRITTEN BY THE SPEC AND READ BY NOTHING WOULD BE WORSE THAN NONE: it
    would look like a guarantee the model does not have. So the `forall` is not
    stated here; the arm's leaving the model unchanged is read off its code).

    What is left is what one reading, on its own, must look like:

    - EXACTLY 16 BYTES, as above.
    - `tv_nsec` IS NORMALIZED, below 10^9.  `posix_get_realtime_timespec`
      is `ktime_get_real_ts64` (kernel/time/timekeeping.c,
      byte-identical at v6.10-v6.15), which sets `tv_nsec` to 0 and
      then normalizes with `timespec64_add_ns`.
    - THE READING IS BELOW `CLOCK_NS_ENVELOPE`.  The wall clock is
      settable, but only through writers that pass
      `timespec64_valid_settod` (include/linux/time64.h, byte-identical
      at v6.10-v6.15), which rejects a negative `tv_sec`, a `tv_nsec`
      outside `[0, 10^9)`, and a `tv_sec` at or above
      `TIME_SETTOD_SEC_MAX` — `KTIME_SEC_MAX` LESS thirty years, the
      headroom the comment beside it says is there so a reasonable
      uptime cannot carry the clock past what `ktime_t` holds.  So a
      settable clock reported by `ktime_get_real_ts64` still fits in
      the same 2^63 ns envelope `ktime_t` gives the monotonic one, and
      the same split argument keeps both fields non-negative. -/
def realtime_ok_b (bs : List byte) : Bool :=
  (bs.length == 16)
  && decide (tv_frac_of bs < 1000000000)
  && decide (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- What a `CLOCK_PROCESS_CPUTIME_ID` reading of `bs` must satisfy.  It
    is `realtime_ok_b` with the envelope moved onto the SIGNED reading
    and made TWO-SIDED, and that one change is the point of this
    definition.

    THIS IS NOT A CLOCK.  It is a count of CPU the thread group has
    CONSUMED, and every step of the path says so.  `clock_gettime`
    resolves id 2 through `posix_clocks`, whose
    `[CLOCK_PROCESS_CPUTIME_ID] = &clock_process`
    (kernel/time/posix-timers.c); `clock_process`'s
    `.clock_get_timespec` is `process_cpu_clock_get`, which is one
    line, `posix_cpu_clock_get(PROCESS_CLOCK, tp)`, with
    `#define PROCESS_CLOCK make_process_cpuclock(0, CPUCLOCK_SCHED)`;
    `posix_cpu_clock_get` takes the `!CPUCLOCK_PERTHREAD` branch to
    `cpu_clock_sample_group(CPUCLOCK_SCHED, tsk, false)`; and
    `store_samples` fills that slot with the scheduler's
    `sum_exec_runtime` — `samples[CPUCLOCK_SCHED] = rtime`, where
    `samples[CPUCLOCK_PROF] = stime + utime` is the sum of user and
    system time this id never selects (kernel/time/posix-cpu-timers.c).
    Every one of those — `posix_clocks`, `clock_process`,
    `process_cpu_clock_get`, `PROCESS_CLOCK`, `posix_cpu_clock_get`,
    `cpu_clock_sample_group` and `store_samples` — is byte-identical
    across mainline v6.10-v6.15 and across the 6.10.y through 6.15.y
    stable branches.

    IT CANNOT FAIL, which is why the arm below has no error path other
    than the destination gate.  `posix_cpu_clock_get`'s only `-EINVAL`
    is a NULL task, and `pid_for_clock` cannot return one for this id:
    `CPUCLOCK_WHICH(PROCESS_CLOCK)` is `CPUCLOCK_SCHED`, below
    `CPUCLOCK_MAX`, and `CPUCLOCK_PID(PROCESS_CLOCK)` is 0, so it takes
    the `upid == 0` branch and answers `task_tgid(current)` without
    looking anything up.

    A NEGATIVE `tv_sec` IS A SHAPE THIS ID REALLY EMITS, which is why
    the envelope has to move.  Nothing clamps the sample:
    `thread_group_cputime` (kernel/sched/cputime.c) accumulates
    `read_sum_exec_runtime(t)` over `for_each_thread` on top of
    `sig->sum_sched_runtime` in a `u64`, and a thread group running on
    several CPUs burns CPU faster than any clock advances.  What
    happens when that `u64` passes 2^63 is not undefined and not an
    error: `ns_to_timespec64` (kernel/time/time.c, byte-identical at
    v6.10-v6.15 and on the matching stable branches) takes an `s64`,
    and HAS A BRANCH FOR IT — the `nsec < 0` case, reached exactly when
    the sample has bit 63 set, writes a NEGATIVE `tv_sec` and keeps
    `tv_nsec` positive.  So `realtime_ok_b`'s
    `timespec_ns bs <? CLOCK_NS_ENVELOPE`, which reads `tv_sec`
    UNSIGNED, would reject a conforming kernel here.  The other two
    arms may read it unsigned because a kernel writer keeps their
    quantity non-negative — `timespec64_valid_settod` for the wall
    clock, `ktime_t` itself for the monotonic one.  Nothing does that
    for a count of nanoseconds burned.

    WHAT IS LEFT IS THE SAME ENVELOPE, READ THE WAY THE KERNEL READS
    IT, and it is exact rather than cautious: `ns_to_timespec64` is a
    BIJECTION from the `s64` it is handed onto the timespecs below,
    so the four conjuncts admit every reading a kernel can produce here
    and nothing else.

    - EXACTLY 16 BYTES, the `struct __kernel_timespec` the syscall
      writes; the same argument as on the other two arms.
    - `tv_nsec` IS NORMALIZED, below 10^9, on all three branches: the
      zero case leaves the `{ 0, 0 }` initializer, the `nsec > 0` case
      takes `div_u64_rem(nsec, NSEC_PER_SEC, &rem)`'s remainder, and
      the `nsec < 0` case computes `NSEC_PER_SEC - rem - 1`, which the
      comment beside it says is kept positive on purpose.
    - THE SIGNED TOTAL IS AN `s64` NUMBER OF NANOSECONDS, at or above
      `-CLOCK_NS_ENVELOPE` and below it.  That is the argument the
      whole `u64` sample fits in, and it is two-sided for the one
      reason: the argument is signed, so the bottom of its range is a
      real bound and not a formality.  It also does the work
      `timespec_ns bs <? CLOCK_NS_ENVELOPE` does on the other arms —
      an absurd `tv_sec` cannot present itself as a small admissible
      count, in either direction. -/
def cputime_ok_b (bs : List byte) : Bool :=
  (bs.length == 16)
  && decide (tv_frac_of bs < 1000000000)
  && decide (-CLOCK_NS_ENVELOPE ≤ timespec_ns_signed bs)
  && decide (timespec_ns_signed bs < CLOCK_NS_ENVELOPE)

/-- The clock ids answered PER CALL, against `realtime_ok_b` alone — no
    model field read, none written, each call's reading independently
    arbitrary.  `CLOCK_REALTIME` is here for `realtime_ok_b`'s reason:
    the kernel guarantees NOTHING across two wall-clock readings, so
    there is nothing to record.  The other four DO carry cross-call
    guarantees in the kernel, and the model deliberately states NONE of
    them — each is a strict over-approximation of exactly the kind the
    CPU-time arm already takes: every reading a kernel can produce is
    admitted, so no conforming trace is rejected, and the price is the
    CPU-time arm's price, that a program whose OUTPUT depends on the
    value it read cannot be proved equivalent to anything.  Per id, what
    is deliberately not said, and why saying it against `m_clock` would
    be wrong anyway:

    - `CLOCK_MONOTONIC_RAW` (4): `ktime_get_raw_ts64`
      (kernel/time/timekeeping.c) — the monotonic clock WITHOUT NTP
      frequency correction.  Monotone in the kernel, but a DIFFERENT
      quantity from what `m_clock` records: NTP slews the adjusted clock
      both faster and slower than the raw one, so no inequality between
      a raw reading and the recorded `CLOCK_MONOTONIC` reading is a
      kernel fact in either direction.
    - `CLOCK_REALTIME_COARSE` (5): `ktime_get_coarse_real_ts64` (same
      file) — the wall clock as of the last tick.  Everything
      `realtime_ok_b` says about the wall clock's absence of guarantees
      applies verbatim, with up to a tick of staleness on top.
    - `CLOCK_MONOTONIC_COARSE` (6): `ktime_get_coarse_ts64` (same file)
      — the monotonic clock as of the last tick.  Monotone in the
      kernel, but a coarse reading may PRECEDE a fine-grained reading
      already recorded in `m_clock`, so constraining it against that
      field would reject conforming traces.
    - `CLOCK_BOOTTIME` (7): `ktime_get_boottime_ts64` (same file) — the
      monotonic clock PLUS time spent suspended.  It never precedes the
      monotonic clock, but the two are read at different instants and
      the model has no suspend accounting, so the inequality it does
      carry relates nothing the model can state.

    Not modeling their cross-call monotonicity is a CHOICE, not an
    oversight: recording four more clock fields would buy proofs about
    programs whose behavior depends on values this model already makes
    unprovable the moment they are consulted, at the cost of four more
    envelope gates of the kind the monotonic arm needs to stay
    receptive.  A later change that needs, say, BOOTTIME monotonicity
    can split its id out of this set the way `CLOCK_MONOTONIC` already
    is.

    The per-reading conditions ARE `realtime_ok_b`'s, and that is a
    kernel fact five times over: every one of these paths writes a
    16-byte `struct __kernel_timespec`, normalizes `tv_nsec` below 10^9
    (`timespec64_add_ns` on the fine paths; the coarse pair copies a
    timekeeper field that was stored normalized), and reports a
    `ktime_t`-representable non-negative time, so the same three
    conjuncts admit every reading any of them can produce.

    THE SCOPE, as on the CPU-time arm: `CLOCK_BOOTTIME` is answered on
    both sides of the `CONFIG_POSIX_TIMERS` gate
    (kernel/time/posix-stubs.c serves REALTIME, MONOTONIC and BOOTTIME);
    the raw and coarse ids, like `CLOCK_PROCESS_CPUTIME_ID`, are
    answered only with the option on. -/
def clockid_percall_b (clkid : word) : Bool :=
  ((clkid.toNat : Int) == CLOCK_REALTIME)
  || ((clkid.toNat : Int) == CLOCK_MONOTONIC_RAW)
  || ((clkid.toNat : Int) == CLOCK_REALTIME_COARSE)
  || ((clkid.toNat : Int) == CLOCK_MONOTONIC_COARSE)
  || ((clkid.toNat : Int) == CLOCK_BOOTTIME)

/-- `clock_gettime clkid tp`: read a clock into a `struct timespec`.

    SEVEN IDS ARE MODELED, IN THREE ARMS THAT ARE NOT FOLDED TOGETHER.
    `CLOCK_MONOTONIC` (1), `CLOCK_REALTIME` (0) and
    `CLOCK_PROCESS_CPUTIME_ID` (2) are different quantities carrying
    different guarantees, and each arm below says only what its own
    quantity promises; `CLOCK_MONOTONIC_RAW` (4), `CLOCK_REALTIME_COARSE`
    (5), `CLOCK_MONOTONIC_COARSE` (6) and `CLOCK_BOOTTIME` (7) share the
    wall-clock arm through `clockid_percall_b`, whose header carries the
    argument that the sharing attaches nothing: that arm states only
    per-reading facts every one of its five ids satisfies, and no
    cross-call relation at all.  Each arm changes exactly one thing from
    the one above it, and every change is a kernel fact:

    - a MONOTONIC reading is constrained against the previous one, by
      `timespec_ok_b`, and RECORDED in `m_clock`;
    - a WALL-CLOCK reading DROPS the relation to the previous reading
      and is constrained per call, by `realtime_ok_b` alone, leaving
      the model exactly as it found it.  `CLOCK_REALTIME` is settable
      and can jump in either direction under
      `settimeofday`/`clock_settime` and NTP, so it is not monotone at
      all — `realtime_ok_b` carries the two writers that settle it, and
      what they leave is a floor at the boot instant rather than a
      ratchet at the last reading;
    - a CPU-TIME reading MOVES the 2^63 ns envelope, by `cputime_ok_b`,
      onto the SIGNED reading of the struct and makes it two-sided.
      The envelope is not dropped — it is the same 2^63, applied the
      way `ns_to_timespec64` applies it.  `cputime_ok_b` carries why.

    Sharing one arm — or one model field — between any two of those
    three would attach a guarantee to a quantity that does not have it.
    The per-call ids can share theirs because it attaches none.

    MODELING `CLOCK_REALTIME` IS WHAT MAKES A LIBC `gettimeofday`
    MODELED, which is why it is here rather than left with the other
    ids.  musl's `gettimeofday` (src/time/gettimeofday.c, musl 1.2.6)
    is `clock_gettime(CLOCK_REALTIME, &ts)`
    followed by a divide by 1000, and issues syscall 169 on NO
    architecture — so dropbear's three call sites (src/dbrandom.c,
    src/loginrec.c, src/dbutil.c) arrive here, at 113 with id 0.

    MODELING `CLOCK_PROCESS_CPUTIME_ID` (2) IS WHAT MAKES A LIBC
    `clock()` MODELED, and it is here for that reason, alongside the
    one above.  musl's `clock` (src/time/clock.c, musl 1.2.6) is
    `clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts)` followed by a
    convert to microseconds, so dropbear's `seedrandom`
    (src/dbrandom.c at v2026.94) arrives here, at 113 with id 2, BEFORE
    the server has accepted anything.  It is also the ONE modeled id a
    real machine cannot serve out of the vDSO —
    `__cvdso_clock_gettime_common` answers only the ids in
    `VDSO_HRES | VDSO_COARSE | VDSO_RAW` and no CPU clock is in any of
    them — so it is the only one a LIBC call reaches the kernel
    through on hardware, the other six being absorbed before the
    syscall is made.

    IT IS A DIFFERENT QUANTITY FROM BOTH OTHERS, AND IT GETS NO MODEL
    FIELD.  `m_clock` is elapsed monotonic nanoseconds; this is
    nanoseconds of CPU the thread group has burned.  Answering either
    out of the other would be a confident wrong answer of exactly the
    kind the fail-closed rule exists to forbid — and so, for the same
    reason, would answering a `CLOCK_REALTIME` read out of `m_clock`.

    So the reading is chosen per call against `cputime_ok_b` alone,
    and, as on the wall-clock arm, an accepted call leaves the model
    UNCHANGED.  The reason is not the wall clock's: nothing about this
    quantity is settable.  It is that THE MODEL HAS NO NOTION OF WORK
    DONE, so there is nothing here for a reading to be related to —
    not the previous reading, and not `m_clock`, which measures
    elapsed time rather than CPU consumed and is related to it by no
    inequality this model could state (a thread group on several CPUs
    burns CPU faster than the clock runs, and one that is not
    scheduled burns none at all).  Relating it to nothing is a STRICT
    OVER-APPROXIMATION: every reading a kernel can produce is
    admitted, whatever a kernel does or does not guarantee across
    calls, so no conforming trace is rejected.  It costs the same as
    the wall clock's arm costs — a program whose output depends on the
    value it read cannot be proved equivalent to anything — and it is
    of a piece with the over-approximation the monotonic arm already
    takes, where the clock does not advance for work either.

    A FIELD FOR IT WOULD BE WORSE THAN NONE, for the reason `realtime_ok_b` gives: it
    could only be written and never usefully read, and would look like a guarantee
    the model does not have. THE KERNEL DOES NOT MAKE THAT GUARANTEE, which is the
    second reason not to state it and the reason not to state its negation either.
    The value IS non-decreasing in the implementation, but only as the conclusion of
    an argument over four separate mechanisms — the `delta_exec <= 0` guard in
    `update_curr_se`, the `write_seqlock(&sig->stats_lock)` section in
    `__exit_signal` that moves a dying thread's runtime into `sig->sum_sched_runtime`
    before unhashing it, `__sched_fork` zeroing a new thread's counter, and
    `update_gt_cputime`'s per-field max when a process-wide timer arms and moves
    reads from the live walk to `cputimer.cputime_atomic`.

    A WRONG INFERENCE TO AVOID, because it is an easy one to reach.
    It is tempting to say
    the value is "NOT NON-DECREASING" and use that as a second reason
    to decline the id, on the grounds that
    `cpu_clock_sample_group` reads the live sum while
    `!pct->timers_active` and the cached `cputime_atomic` once timers
    are armed, and that the cache omits the slice running at the moment
    of the switch.  It cannot move backwards:
    `__update_gt_cputime` returns early on
    `sum_cputime <= curr_cputime` and otherwise raises the value by
    `cmpxchg`, so `cputime_atomic` is a monotone max and activation can
    only lift what is reported.  What the omission produces is a STALE
    reading, not a backwards one — `thread_group_cputime`'s own comment
    says it deliberately skips the pending time of other running tasks
    on other CPUs — and a sum that omits work still only accumulates.

    Modeling it as a guarantee would be claiming more than Linux
    does; modeling its negation would be claiming a step this code
    does not take.  Claiming neither is the honest option, and it is
    free, because the model has nothing to relate the reading to
    anyway.

    That is NOT the monotonic arm's situation, though its
    non-decreasing constraint rests on a reading of five mechanisms
    below and so looks like the same move made the other way.  The
    difference is what the reading is ABOUT: `CLOCK_MONOTONIC` is
    REQUIRED to be non-decreasing, so those mechanisms are how the
    kernel KEEPS a promise it has made, where the same reading here
    would establish a property the next patch may break without
    breaking anything it owes.

    THE SCOPE, named rather than assumed: this arm describes a kernel
    built with `CONFIG_POSIX_TIMERS`.  Without it `posix_cpu_clock_get`
    is not built at all and `do_clock_gettime`
    (kernel/time/posix-stubs.c, byte-identical at v6.10-v6.15) answers
    -EINVAL for every id but REALTIME, MONOTONIC and BOOTTIME.  Those
    three modeled ids are answered on BOTH sides of that gate; this one
    is not, and neither are the raw and coarse ids on the per-call arm
    (`clockid_percall_b`'s header restates the split), so which modeled
    ids answer depends on that kernel config option.

    EVERY OTHER ID IS `unmodeled`, fail closed.  The `_COARSE` ids in
    particular are not answered by analogy with the MONOTONIC arm.
    That arm's non-decreasing conjunct leans below on the anti-step
    compensation in `timekeeping_apply_adjustment` — the
    `xtime_nsec -= offset` that pairs with a slope change — and the
    coarse getters never applied it, which is exactly what let
    `CLOCK_MONOTONIC_COARSE` step backwards.  A coarse reading is
    non-decreasing at the cited tree only because of b71f9804f66c
    ("timekeeping: Prevent coarse clocks going backwards", v6.15-rc6),
    which added `tk->coarse_nsec` (include/linux/timekeeper_internal.h)
    to carry that compensation for the coarse path too.  Stable
    `linux-6.12.y` has not taken that fix as of v6.12.105 and
    `linux-6.14.y` took it at v6.14.7, measured by the presence of
    `coarse_nsec` at each tag.  So a coarse arm would rest on a
    guarantee younger than the clock, and needs its own argument, read
    at the cited tree, rather than this one's.

    ORDER.  The id is decoded FIRST, as Linux does, so a bad id beats
    a bad pointer and the model's decline sits where the kernel's
    -EINVAL does.  Cited below.

    WHAT THE ENVIRONMENT CHOOSES, ON THE MONOTONIC ARM.  The reading is
    the environment's, constrained only to be NON-DECREASING and inside
    `CLOCK_NS_ENVELOPE`.  Non-decreasing rather than strictly
    increasing, and BOTH halves of that are kernel facts rather than
    caution.

    IT NEVER GOES BACKWARDS, against each mechanism that could
    plausibly move it.  MONOTONIC is `xtime + wall_to_monotonic`, and
    `do_settimeofday64` edits the pair together —
    `tk_set_wall_to_mono(tk, wall_to_monotonic - ts_delta)` against
    `tk_set_xtime(tk, ts)` — so a settimeofday cancels exactly, and
    `tk_set_wall_to_mono` touches neither `tkr_mono.mult` nor
    `cycle_last`; `accumulate_nsecs_to_secs` pairs the same way for a
    leap second.

    (THE SPELLING, not the behaviour, moves inside the window: the
    v6.13-v6.15 form of `do_settimeofday64` passes the shadow
    timekeeper and uses `scoped_guard` with
    `timekeeping_restore_shadow`, where v6.10-v6.12 takes the timekeeper
    lock by hand and holds an explicit `ret`.  The shadow variable does
    not exist before v6.13 at all.  Same two -EINVAL conditions and the
    same writes either way, so the argument above is unaffected — but
    "byte-identical across v6.10-v6.15" would be false of these
    functions, and is not claimed.)

    NTP slewing changes the SLOPE only: `timekeeping_apply_adjustment`
    does `tkr_mono.mult += mult_adj` together with
    `tkr_mono.xtime_nsec -= offset`, the second line being the anti-step
    compensation.  It runs on the SHADOW timekeeper and is published
    atomically afterwards, which is what makes it invisible to a reader
    mid-update — at v6.10 `timekeeping_adjust` is called eight lines
    BEFORE `write_seqcount_begin(&tk_core.seq)` opens the section that
    then copies the shadow across, and at v6.13 its caller has no
    `write_seqcount_begin` at all, publishing through
    `timekeeping_update_from_shadow` instead.  So the guarantee is
    shadow-then-publish rather than "inside the write section".

    Suspend stops the clock rather than jumping it —
    `__timekeeping_inject_sleeptime` adds the sleep to xtime and
    subtracts it from `wall_to_monotonic`, so REALTIME and BOOTTIME
    advance across a suspend and MONOTONIC does not.  And a backwards
    COUNTER read is clamped rather than propagated:
    `timekeeping_cycles_to_ns` returns `xtime_nsec >> shift` when the
    masked delta has the mask's MSB set — but only inside
    `if (unlikely(delta > tkr->clock->max_cycles))`, so the MSB test is
    necessary and not sufficient, and an ordinary small delta never
    reaches it.  Time stalls but never steps back.

    IT IS NOT REQUIRED TO ADVANCE, for two separate reasons, which is
    why the model must not demand a strict increase: two reads inside
    one counter tick return the identical value — on riscv the counter
    is `rdtime`, about 10 MHz under qemu-virt, so equal consecutive
    readings are ordinary rather than a corner case — and the clamp
    above freezes the clock outright while it is in effect.
    `clock_getres` answering 1 ns does not contradict this: that is
    timer-programming granularity, not a promise that two reads differ.
    Requiring an advance would reject a conforming trace.
    The chosen value is recorded in `m_clock`, which is the only reason
    the constraint can be stated at all: it is a relation between this
    call and the previous one, and a per-call `choose` has nothing to
    relate to.

    NOT MODELED, deliberately: the clock does not advance at any OTHER
    syscall, so the model admits traces in which unbounded work happens
    between two readings that return the same nanosecond.  That is a
    strict over-approximation of the reachable set — every real trace
    is still admitted — and it is the honest shape while nothing else
    in the model has a notion of duration.

    ORDER, cited: `clock_gettime` resolves `which_clock` through
    `clockid_to_kclock` and returns -EINVAL for an id with no `k_clock`
    before `tp` is touched, and `put_timespec64` runs only under
    `!error` (kernel/time/posix-timers.c, v6.10-v6.15).

    THE DESTINATION GATE declines rather than answering -EFAULT, and it
    declines a WIDER band than its reason strictly covers.  The reason
    is the partial case: a 16-byte `tp` straddling into an unmapped
    page keeps its first bytes and still reports -EFAULT, because
    `put_timespec64`'s `copy_to_user` reaches riscv64's
    `__asm_copy_to_user` (arch/riscv/lib/uaccess.S), which copies
    forward and whose fixup returns bytes-not-copied — so there is no
    single answer the model could commit to.  A WHOLLY unwritable `tp`
    is not like that: Linux answers -EFAULT having written nothing, and
    `read_spec` does commit to -EFAULT in exactly that shape.  It is
    folded into the same decline anyway, for uniformity with
    `getrandom_spec`'s whole-buffer gate, which takes the same decision.
    The cost is coverage on a shape the model could have answered. -/
def clock_gettime_spec (clkid tp : word) : SysSpec SyscallEffect :=
  if clockid_percall_b clkid then
    -- THE PER-CALL IDS, WHICH THE MODEL DOES NOT REMEMBER.  No
    -- `get_model`, no `set_clock` and no relation to any earlier
    -- reading: `realtime_ok_b` carries the argument that the wall
    -- clock has nothing to relate to, and `clockid_percall_b` the
    -- argument that relating the other four to nothing is a strict
    -- over-approximation taken on purpose.  The destination gate and
    -- the effect shape are the monotonic arm's, for the monotonic
    -- arm's reasons.
    bind inputSpec fun i =>
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => unmodeled   -- destination not fully writable: fail closed
    | some _ =>
        bind (choose (fun bs : List byte => realtime_ok_b bs = true)) fun bs =>
          pure (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [])
  else if ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) then
    -- CPU CONSUMED, WHICH THE MODEL CANNOT HAVE AN OPINION ABOUT.  The
    -- wall-clock arm's shape exactly — no `get_model` and no
    -- `set_clock` — under a predicate of its own: `cputime_ok_b`
    -- carries both the argument that there is nothing to relate a
    -- count of nanoseconds burned to, and the envelope, which is
    -- moved rather than dropped.  The destination gate and the effect
    -- shape are the monotonic arm's, for the monotonic arm's
    -- reasons.
    bind inputSpec fun i =>
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => unmodeled   -- destination not fully writable: fail closed
    | some _ =>
        bind (choose (fun bs : List byte => cputime_ok_b bs = true)) fun bs =>
          pure (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [])
  else if !((clkid.toNat : Int) == CLOCK_MONOTONIC) then unmodeled
  else
  bind getModelSpec fun m =>
  if !decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) then unmodeled
    -- the recorded clock has left the range `ktime_t` can represent.
    -- Unreachable from `init_model` — the origin is 0 and this is the
    -- only arm of this spec that writes `m_clock`, under a predicate
    -- that holds it below the envelope — but `Progress.receptive`
    -- quantifies over ARBITRARY model states, not reachable ones, and
    -- the choice below would be empty here.  Declining keeps the spec
    -- receptive without inventing a reading.
  else
  bind inputSpec fun i =>
  match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
  | none => unmodeled   -- destination not fully writable: fail closed
  | some _ =>
      bind (choose (fun bs : List byte => timespec_ok_b bs (m_clock m) = true)) fun bs =>
      bind (modify (with_clock (BitVec.ofInt 64 (timespec_ns bs)))) fun _ =>
      pure (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [])

/-! ## Sanity checks

  What follows is this tree's own check on the computable part (AGENTS.md,
  "definition of done") plus the three arms' shapes restated as theorems, so that the
  comments' claims — the 16-byte write, the recorded monotonic advance, the per-call
  arms leaving the model alone, and the declines — are machine-checked here rather
  than only argued in prose.

    -/

-- The shape lemmas below invert a five-deep monad chain, and Lean's
-- kernel/linters walk the resulting terms; the default recursion depth
-- is not enough for either.  (Same option, same reason, as
-- `Sys/Fs/Namei.lean` and `Sys/Drivers/Char/Random.lean`.)
set_option maxRecDepth 10000

-- `Lean.Linter.constructorNameAsVariable` walks every declaration's term
-- to a fixed depth and CRASHES (it does not complain) on the shape
-- lemmas below, whose `obtain` patterns produce very large terms.  It is
-- a style lint with nothing to say about this file; the proofs are
-- checked either way.
set_option linter.constructorNameAsVariable false

/-! ### Inversion helpers for the monad (port scaffolding)

    `bind`/`choose`/`pure`/`modify`/`getModelSpec` have no inversion
    lemmas at the concrete types, and the arm checks below need to read
    an outcome backwards.  Each iff below is definitional (`Iff.rfl`),
    so nothing is assumed: they only name the unfoldings `bind`'s and
    `pure`'s bodies already give. -/

private theorem bind_ok_iff {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (y : B) (m2 : Model) (evs : List event) :
    bind c k i m (.ok y m2 evs) ↔
      ∃ x m1 evs1 evs2,
        c i m (.ok x m1 evs1) ∧ k x i m1 (.ok y m2 evs2) ∧ evs = evs1 ++ evs2 :=
  Iff.rfl

private theorem bind_unmodeled_iff {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) :
    bind c k i m .unmodeled ↔
      c i m .unmodeled ∨
        ∃ x m1 evs1, c i m (.ok x m1 evs1) ∧ k x i m1 .unmodeled :=
  Iff.rfl

private theorem input_iff (i : SyscallInput) (m : Model)
    (o : Outcome SyscallInput Model event) :
    inputSpec i m o ↔ o = .ok i m [] :=
  Iff.rfl

private theorem getModel_iff (i : SyscallInput) (m : Model)
    (o : Outcome Model Model event) :
    getModelSpec i m o ↔ o = .ok m m [] :=
  Iff.rfl

private theorem choose_iff {A : Type} (P : A → Prop) (i : SyscallInput) (m : Model)
    (o : Outcome A Model event) :
    choose P i m o ↔ ∃ x, P x ∧ o = .ok x m [] :=
  Iff.rfl

private theorem modify_iff (f : Model → Model) (i : SyscallInput) (m : Model)
    (o : Outcome Unit Model event) :
    modify f i m o ↔ o = .ok () (f m) [] :=
  Iff.rfl

private theorem pure_iff {A : Type} (x : A) (i : SyscallInput) (m : Model)
    (o : Outcome A Model event) :
    pure x i m o ↔ o = .ok x m [] :=
  Iff.rfl

/-! ### The decoded fields of a `struct __kernel_timespec` -/

/-- One second, as the kernel would write it: `tv_sec = 1`, `tv_nsec = 0`. -/
private def ts1s : List byte := Z_to_le_bytes 8 1 ++ List.replicate 8 0

/-- Two seconds. -/
private def ts2s : List byte := Z_to_le_bytes 8 2 ++ List.replicate 8 0

/-- One nanosecond BEFORE one second: `tv_sec = 0`, `tv_nsec = 999999999`. -/
private def ts1sMinus : List byte := Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 999999999

/-- `tv_sec = 1` with an UNNORMALIZED `tv_nsec` of exactly 10^9 — the
    reading a kernel never writes, and the condition that makes the two
    fields a unique reading of the instant. -/
private def tsDenorm : List byte := Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 1000000000

/-- The first 8 bytes decode as `tv_sec`. -/
example : tv_sec_of ts1s = 1 := by decide

/-- The second 8 bytes decode as `tv_nsec`. -/
example : tv_frac_of ts1s = 0 := by decide

/-- And the two together as a nanosecond count. -/
example : timespec_ns ts2s = 2000000000 := by decide

/-- One nanosecond below a second is still under 10^9. -/
example : tv_frac_of ts1sMinus = 999999999 := by decide

/-- A `struct __kernel_timespec` is exactly 16 bytes. -/
example : ts1s.length = 16 := by decide

/-! ### `timespec_ok_b`: the four conjuncts, one at a time -/

/-- A normalized, in-envelope reading at or above `prev` passes. -/
example :
    timespec_ok_b ts1s (BitVec.ofInt 64 1000000000) = true := by decide

/-- EQUAL READINGS ARE ADMISSIBLE — the constraint is non-strict, which is
    the "not required to advance" half of the comment: a coarse
    clocksource really does answer two quick calls alike. -/
example :
    timespec_ok_b ts1s (BitVec.ofInt 64 1000000000) = true := by decide

/-- A READING ONE NANOSECOND EARLIER IS REFUSED — the monotonicity
    guarantee itself. -/
example :
    timespec_ok_b ts1sMinus (BitVec.ofInt 64 1000000000) = false := by decide

/-- `tv_nsec = 10^9` is not normalized; the kernel carries the second out
    as it adds. -/
example :
    timespec_ok_b tsDenorm (BitVec.ofInt 64 0) = false := by decide

/-- 15 bytes is not a `timespec`: the length test is EXACTLY 16. -/
example :
    timespec_ok_b (Z_to_le_bytes 8 1 ++ Z_to_le_bytes 7 0) (BitVec.ofInt 64 0)
      = false := by decide

/-- The empty buffer is refused — the length test alone catches it. -/
example : timespec_ok_b [] (BitVec.ofInt 64 0) = false := by decide

/-- `CLOCK_NS_ENVELOPE` nanoseconds is one past `ktime_t`: refused. -/
example :
    timespec_ok_b (Z_to_le_bytes 8 9223372037 ++ List.replicate 8 0)
      (BitVec.ofInt 64 0) = false := by decide

/-- ...and the largest value `ktime_t` holds passes, so the bound is the
    envelope and not something smaller. -/
example :
    timespec_ok_b (Z_to_le_bytes 8 9223372036 ++ Z_to_le_bytes 8 854775807)
      (BitVec.ofInt 64 0) = true := by decide

/-! ### `realtime_ok_b`: the same predicate MINUS the conjunct with `prev` -/

/-- A well-formed wall-clock reading passes. -/
example : realtime_ok_b ts1s = true := by decide

/-- NO `prev`: the reading one nanosecond BEFORE the monotonic one still
    passes here, which is exactly the conjunct this predicate drops. -/
example : realtime_ok_b ts1sMinus = true := by decide

/-- `tv_nsec` is normalized on this arm too. -/
example : realtime_ok_b tsDenorm = false := by decide

/-- 15 bytes is not a `timespec`. -/
example : realtime_ok_b (Z_to_le_bytes 8 1) = false := by decide

/-- The wall clock is settable but still inside the same 2^63 ns
    envelope: `timespec64_valid_settod` is what holds it there. -/
example :
    realtime_ok_b (Z_to_le_bytes 8 9223372037 ++ List.replicate 8 0)
      = false := by decide

/-! ### `cputime_ok_b`: the envelope MOVED onto the signed reading -/

/-- A well-formed CPU-time reading passes. -/
example : cputime_ok_b ts1s = true := by decide

/-- A NEGATIVE `tv_sec` IS A SHAPE THIS ID EMITS: `-1` second reads as
    -10^9 nanoseconds, inside the two-sided envelope. -/
example :
    timespec_ns_signed (Z_to_le_bytes 8 (-1) ++ List.replicate 8 0)
      = -1000000000 := by decide

example : cputime_ok_b (Z_to_le_bytes 8 (-1) ++ List.replicate 8 0) = true := by
  decide

/-- ...AND `realtime_ok_b` WOULD REJECT IT, because it reads the same
    `tv_sec` UNSIGNED and sees 2^64 - 1 seconds.  This is the whole
    reason `cputime_ok_b` exists as a separate predicate. -/
example : realtime_ok_b (Z_to_le_bytes 8 (-1) ++ List.replicate 8 0) = false := by
  decide

/-- `-CLOCK_NS_ENVELOPE` exactly: the bottom of the range, and it passes
    (the bound is `at or above`, and the range is two-sided). -/
example :
    cputime_ok_b (Z_to_le_bytes 8 (-9223372037) ++ Z_to_le_bytes 8 145224192)
      = true := by decide

/-- One nanosecond below it: refused.  The lower bound is real, not a
    formality. -/
example :
    cputime_ok_b (Z_to_le_bytes 8 (-9223372037) ++ Z_to_le_bytes 8 145224191)
      = false := by decide

/-- The top of the range: `CLOCK_NS_ENVELOPE - 1` passes. -/
example :
    cputime_ok_b (Z_to_le_bytes 8 9223372036 ++ Z_to_le_bytes 8 854775807)
      = true := by decide

/-- `CLOCK_NS_ENVELOPE` is refused on the signed reading too. -/
example :
    cputime_ok_b (Z_to_le_bytes 8 9223372037 ++ List.replicate 8 0) = false := by
  decide

/-- Normalization is unchanged on this arm. -/
example : cputime_ok_b tsDenorm = false := by decide

/-- 15 bytes is not a `timespec`. -/
example : cputime_ok_b (Z_to_le_bytes 8 1) = false := by decide

/-! ### `clockid_percall_b`: the five ids answered against
    `realtime_ok_b` alone, and the two that are not -/

/-- `CLOCK_REALTIME` (0). -/
example : clockid_percall_b (BitVec.ofInt 64 0) = true := by decide

/-- `CLOCK_MONOTONIC_RAW` (4). -/
example : clockid_percall_b (BitVec.ofInt 64 4) = true := by decide

/-- `CLOCK_REALTIME_COARSE` (5). -/
example : clockid_percall_b (BitVec.ofInt 64 5) = true := by decide

/-- `CLOCK_MONOTONIC_COARSE` (6) — per-call, NOT by analogy with the
    monotonic arm; see `clock_gettime_spec`'s header. -/
example : clockid_percall_b (BitVec.ofInt 64 6) = true := by decide

/-- `CLOCK_BOOTTIME` (7), answered on both sides of
    `CONFIG_POSIX_TIMERS`. -/
example : clockid_percall_b (BitVec.ofInt 64 7) = true := by decide

/-- `CLOCK_MONOTONIC` (1) is NOT per-call: it is the arm that reads and
    writes `m_clock`. -/
example : clockid_percall_b (BitVec.ofInt 64 1) = false := by decide

/-- `CLOCK_PROCESS_CPUTIME_ID` (2) is not per-call either: it has an arm
    of its own, on `cputime_ok_b`. -/
example : clockid_percall_b (BitVec.ofInt 64 2) = false := by decide

/-- `CLOCK_THREAD_CPUTIME_ID` (3) is one the model declines. -/
example : clockid_percall_b (BitVec.ofInt 64 3) = false := by decide

/-- `CLOCK_REALTIME_ALARM` (8) is `timerfd_create`'s and is declined here. -/
example : clockid_percall_b (BitVec.ofInt 64 8) = false := by decide

/-- `CLOCK_TAI` (11) likewise. -/
example : clockid_percall_b (BitVec.ofInt 64 11) = false := by decide

/-- A negative `clockid_t`, zero-extended from its low half: no modeled
    id, so it declines (`Sys.Syscall.clockid32` documents the truncation
    the dispatcher performs). -/
example : clockid_percall_b (BitVec.ofInt 64 (-6)) = false := by decide

/-! ### A demo input and model for the spec-level checks -/

/-- Every address writable: the destination gate accepts the 16-byte
    range. -/
private def wmemAll : word → Option byte := fun _ => some 0

/-- No writable memory at all: the destination gate declines. -/
private def wmemNone : word → Option byte := fun _ => none

/-- A `clock_gettime` (113) input whose destination is at 4096 and whose
    writable view is the argument. -/
private def demoInput (w : word → Option byte) : SyscallInput :=
  { in_sysno := 113, in_args := [1, 4096, 0, 0, 0, 0],
    in_mem := fun _ => none, in_wmem := w }

/-- The model the checks run in: empty fd table, empty VM ledger, EOF on
    stdin, empty file system, no halt, no rlimit, and — `mkModel`'s
    origin — a clock reading 0. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof []

/-- A model whose recorded `CLOCK_MONOTONIC` reading is `t` nanoseconds. -/
private def clockModel (t : Int) : Model :=
  with_clock (BitVec.ofInt 64 t) demoModel

/-- The destination walk the checks below rewrite through: at `wmemAll`
    every address holds a byte, so the 16-byte range is `some`-shaped and
    only the predicates decide. -/
private theorem demo_read_all :
    read_bytes_map wmemAll (4096 : word) (BitVec.ofInt 64 16)
      = some (List.replicate 16 0) := by decide

/-- ...and at `wmemNone` it is not writable at all. -/
private theorem demo_read_none :
    read_bytes_map wmemNone (4096 : word) (BitVec.ofInt 64 16) = none := by
  decide

/-- The recorded clock is the field `with_clock` writes — `rfl`, because
    `with_clock` rebuilds only `m_time`. -/
private theorem clockModel_clock (t : Int) :
    m_clock (clockModel t) = BitVec.ofInt 64 t := rfl

/-! ### The three arms, forwards: what each one admits -/

/-- THE PER-CALL ARM.  `CLOCK_REALTIME` (and the four ids
    `clockid_percall_b` folds in with it) writes exactly 16 bytes the
    environment chose against `realtime_ok_b`, returns a literal 0, and
    LEAVES THE MODEL EXACTLY AS IT FOUND IT — no `m_clock` read, none
    written. -/
theorem clock_gettime_spec_percall_ok (clkid tp : word) (i : SyscallInput)
    (m : Model) (bs bs0 : List byte)
    (hpc : clockid_percall_b clkid = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (hbs : realtime_ok_b bs = true) :
    clock_gettime_spec clkid tp i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] []) m []) := by
  unfold clock_gettime_spec
  simp only [hpc, ite_true, bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread, bind_ok_iff]
  refine ⟨bs, m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ bs i m hbs
  · rfl

/-- THE CPU-TIME ARM.  Same shape, same untouched model, under
    `cputime_ok_b` — the envelope moved onto the SIGNED reading. -/
theorem clock_gettime_spec_cputime_ok (tp : word) (i : SyscallInput)
    (m : Model) (bs bs0 : List byte)
    (hpc : clockid_percall_b (BitVec.ofInt 64 2) = false)
    (hcpu : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (hbs : cputime_ok_b bs = true) :
    clock_gettime_spec (BitVec.ofInt 64 2) tp i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] []) m []) := by
  have hmono : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_MONOTONIC) = false := by
    decide
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.not_false, ite_true]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread, bind_ok_iff]
  refine ⟨bs, m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ bs i m hbs
  · rfl

/-- THE MONOTONIC ARM, WHICH IS THE ONLY ONE THAT TOUCHES THE MODEL.  The
    reading is constrained against the recorded clock by
    `timespec_ok_b`, the 16-byte write is the environment's, the return
    is a literal 0, and the model's `m_clock` ADVANCES to the reading's
    nanosecond count. -/
theorem clock_gettime_spec_monotonic_ok (clkid tp : word) (i : SyscallInput)
    (m : Model) (bs bs0 : List byte)
    (hpc : clockid_percall_b clkid = false)
    (hcpu : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = false)
    (hmono : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = true)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (hbs : timespec_ok_b bs (m_clock m) = true) :
    clock_gettime_spec clkid tp i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [])
        (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m) []) := by
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.not_true, Bool.false_eq_true, ite_false,
    bind_ok_iff]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  simp only [hclock, Bool.not_true, Bool.false_eq_true, ite_false]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread, bind_ok_iff]
  refine ⟨bs, m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ bs i m hbs
  · refine ⟨(), with_clock (BitVec.ofInt 64 (timespec_ns bs)) m, [], [],
      ?_, ?_, rfl⟩
    · rfl
    · rfl

/-- The model clock after an accepted `CLOCK_MONOTONIC` reading is the
    reading's nanosecond count: the advance, named. -/
theorem m_clock_monotonic_advance (bs : List byte) (m : Model) :
    m_clock (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m)
      = BitVec.ofInt 64 (timespec_ns bs) := rfl

/-- ...and nothing else in the model moves: `with_clock` rebuilds only
    `m_time`. -/
example (bs : List byte) (m : Model) :
    m_fds (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m) = m_fds m :=
  m_fds_with_clock _ m

/-- THE 16 BYTES, FROM THE PREDICATE.  Every accepted `CLOCK_MONOTONIC`
    reading is a 16-byte struct — the first conjunct, and the size
    `struct __kernel_timespec` really is. -/
theorem timespec_ok_b_length {bs : List byte} {prev : word}
    (h : timespec_ok_b bs prev = true) : bs.length = 16 := by
  unfold timespec_ok_b at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1.1

/-- The same, for the two per-call predicates. -/
theorem realtime_ok_b_length {bs : List byte} (h : realtime_ok_b bs = true) :
    bs.length = 16 := by
  unfold realtime_ok_b at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1

theorem cputime_ok_b_length {bs : List byte} (h : cputime_ok_b bs = true) :
    bs.length = 16 := by
  unfold cputime_ok_b at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1.1

/-- CONCRETELY: a clock at one second accepts a two-second reading, the
    write is 16 bytes at the destination, and the recorded clock is
    handed 2000000000 nanoseconds. -/
example (tp : word) (i : SyscallInput) (bs0 : List byte)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    ∃ m' : Model,
      clock_gettime_spec (BitVec.ofInt 64 1) tp i (clockModel 1000000000)
        (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, ts2s)] []) m' []) ∧
      m_clock m' = BitVec.ofInt 64 2000000000 := by
  refine ⟨with_clock (BitVec.ofInt 64 (timespec_ns ts2s)) (clockModel 1000000000),
    ?_, ?_⟩
  · exact clock_gettime_spec_monotonic_ok _ _ _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) hread (by decide)
  · rw [m_clock_monotonic_advance]
    have h : timespec_ns ts2s = 2000000000 := by decide
    rw [h]

/-- TWO EQUAL READINGS ARE BOTH ADMISSIBLE, and the second records the
    same value: the clock is not required to advance. -/
example (tp : word) (i : SyscallInput) (bs0 : List byte)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    clock_gettime_spec (BitVec.ofInt 64 1) tp i (clockModel 1000000000)
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, ts1s)] [])
        (with_clock (BitVec.ofInt 64 1000000000) (clockModel 1000000000))
        []) := by
  have h := clock_gettime_spec_monotonic_ok (BitVec.ofInt 64 1) tp i
    (clockModel 1000000000) ts1s bs0 (by decide) (by decide) (by decide)
    (by decide) hread (by decide)
  have hns : timespec_ns ts1s = 1000000000 := by decide
  rw [hns] at h
  exact h

/-! ### The three arms, backwards: what each one can have produced -/

/-- THE PER-CALL ARM'S SHAPE.  Any `ok` outcome of a per-call id is a
    16-byte write the environment chose against `realtime_ok_b` alone, a
    literal-zero return, and the model UNCHANGED.  That `m' = m` is the
    "no model field" claim, read backwards. -/
theorem clock_gettime_spec_percall_shape {clkid tp : word} {i : SyscallInput}
    {m m' : Model} {evs : List event} {eff : SyscallEffect}
    (hpc : clockid_percall_b clkid = true)
    {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (h : clock_gettime_spec clkid tp i m (.ok eff m' evs)) :
    ∃ bs : List byte,
      realtime_ok_b bs = true ∧
      eff = mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [] ∧
      m' = m ∧
      evs = [] := by
  unfold clock_gettime_spec at h
  simp only [hpc, ite_true, bind_ok_iff] at h
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := h
  simp only [input_iff, Outcome.ok.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  simp only [List.nil_append] at hevs
  simp only [hread, bind_ok_iff] at hk
  obtain ⟨bs, mw, evsw, evs3, hc2, hk2, hevs2⟩ := hk
  simp only [choose_iff] at hc2
  obtain ⟨b, hb, hc2'⟩ := hc2
  simp only [Outcome.ok.injEq] at hc2'
  obtain ⟨hbs, rfl, rfl⟩ := hc2'
  rw [← hbs] at hb
  simp only [pure_iff, Outcome.ok.injEq] at hk2
  obtain ⟨heff, hm', hevs3⟩ := hk2
  simp only [List.nil_append] at hevs2
  have hevs' : evs = [] := by rw [hevs, hevs2, hevs3]
  exact ⟨bs, hb, heff, hm', hevs'⟩

/-- THE CPU-TIME ARM'S SHAPE: `realtime_ok_b`'s counterpart under
    `cputime_ok_b`, and again the model is UNCHANGED. -/
theorem clock_gettime_spec_cputime_shape {tp : word} {i : SyscallInput}
    {m m' : Model} {evs : List event} {eff : SyscallEffect}
    (hpc : clockid_percall_b (BitVec.ofInt 64 2) = false)
    (hcpu : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true)
    {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (h : clock_gettime_spec (BitVec.ofInt 64 2) tp i m (.ok eff m' evs)) :
    ∃ bs : List byte,
      cputime_ok_b bs = true ∧
      eff = mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [] ∧
      m' = m ∧
      evs = [] := by
  have hmono : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_MONOTONIC) = false := by
    decide
  unfold clock_gettime_spec at h
  simp only [hpc, hcpu, hmono, Bool.not_false, ite_true] at h
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := h
  simp only [input_iff, Outcome.ok.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  simp only [List.nil_append] at hevs
  simp only [hread, bind_ok_iff] at hk
  obtain ⟨bs, mw, evsw, evs3, hc2, hk2, hevs2⟩ := hk
  simp only [choose_iff] at hc2
  obtain ⟨b, hb, hc2'⟩ := hc2
  simp only [Outcome.ok.injEq] at hc2'
  obtain ⟨hbs, rfl, rfl⟩ := hc2'
  rw [← hbs] at hb
  simp only [pure_iff, Outcome.ok.injEq] at hk2
  obtain ⟨heff, hm', hevs3⟩ := hk2
  simp only [List.nil_append] at hevs2
  have hevs' : evs = [] := by rw [hevs, hevs2, hevs3]
  exact ⟨bs, hb, heff, hm', hevs'⟩

/-- THE MONOTONIC ARM'S SHAPE, which is the one that records.  Any `ok`
    outcome is a 16-byte write a `timespec_ok_b` reading describes, a
    literal-zero return, NO EVENTS, and a model whose clock is that
    reading's nanosecond count. -/
theorem clock_gettime_spec_monotonic_shape {clkid tp : word} {i : SyscallInput}
    {m m' : Model} {evs : List event} {eff : SyscallEffect}
    (hpc : clockid_percall_b clkid = false)
    (hcpu : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = false)
    (hmono : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = true)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = true)
    {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0)
    (h : clock_gettime_spec clkid tp i m (.ok eff m' evs)) :
    ∃ bs : List byte,
      timespec_ok_b bs (m_clock m) = true ∧
      eff = mkEffect (BitVec.ofInt 64 0) [(tp, bs)] [] ∧
      m' = with_clock (BitVec.ofInt 64 (timespec_ns bs)) m ∧
      evs = [] := by
  unfold clock_gettime_spec at h
  simp only [hpc, hcpu, hmono, Bool.not_true, Bool.false_eq_true, ite_false] at h
  rw [bind_ok_iff] at h
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := h
  simp only [getModel_iff, Outcome.ok.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  simp only [List.nil_append] at hevs
  simp only [hclock, Bool.not_true, Bool.false_eq_true, ite_false] at hk
  rw [bind_ok_iff] at hk
  obtain ⟨x2, m2, evs3, evs4, hc2, hk2, hevs2⟩ := hk
  simp only [input_iff, Outcome.ok.injEq] at hc2
  obtain ⟨rfl, rfl, rfl⟩ := hc2
  simp only [List.nil_append] at hevs2
  simp only [hread] at hk2
  rw [bind_ok_iff] at hk2
  obtain ⟨bs, mw, evsw, evs5, hc3, hk3, hevs3⟩ := hk2
  simp only [choose_iff] at hc3
  obtain ⟨b, hb, hc3'⟩ := hc3
  simp only [Outcome.ok.injEq] at hc3'
  obtain ⟨hbs, rfl, rfl⟩ := hc3'
  rw [← hbs] at hb
  rw [bind_ok_iff] at hk3
  obtain ⟨w, mw2, evsw2, evs6, hc4, hk4, hevs4⟩ := hk3
  simp only [modify_iff, Outcome.ok.injEq] at hc4
  obtain ⟨-, rfl, rfl⟩ := hc4
  simp only [pure_iff, Outcome.ok.injEq] at hk4
  obtain ⟨heff, hm', hevs6⟩ := hk4
  simp only [List.nil_append] at hevs3 hevs4
  have hevs' : evs = [] := by rw [hevs, hevs2, hevs3, hevs4, hevs6]
  exact ⟨bs, hb, heff, hm', hevs'⟩

/-! ### The declines -/

/-- A BAD CLOCK ID IS THE KERNEL'S `-EINVAL`, AND THE MODEL'S ANSWER TO
    IT IS A DECLINE.  `clock_gettime` resolves `which_clock` through
    `clockid_to_kclock` and returns `-EINVAL` for an id with no
    `k_clock`, BEFORE `tp` is touched (kernel/time/posix-timers.c,
    v6.10-v6.15, cited at `clock_gettime_spec`).  An id outside the seven
    modeled ones is exactly that input class, and the spec answers
    `unmodeled` — from the arm structure below, not from a separate
    test: the id is decided FIRST, so the decline sits where the kernel's
    `-EINVAL` does and a bad id beats a bad pointer.

    EVERY OTHER ID IS DECLINED, fail closed, which is why this is
    `unmodeled` and not `err_ret EINVAL`: the model declines calls it
    cannot interpret instead of committing to an answer the kernel gives
    for reasons the model does not state.  case is
    `clock_gettime_only_the_modeled_clocks`; here it is the same
    statement about the spec. -/
theorem clock_gettime_spec_unmodeled_bad_clockid (clkid tp : word)
    (i : SyscallInput) (m : Model)
    (hpc : clockid_percall_b clkid = false)
    (hcpu : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = false)
    (hmono : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = false) :
    clock_gettime_spec clkid tp i m .unmodeled := by
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.false_eq_true, ite_false, Bool.not_false,
    ite_true, unmodeled]

/-- The same, for `clockid_t` 3 — `CLOCK_THREAD_CPUTIME_ID`, which the
    model declines: Linux serves it, this spec does not, and the decline
    (not a wrong answer) is the fail-closed rule. -/
example (tp : word) (i : SyscallInput) (m : Model) :
    clock_gettime_spec (BitVec.ofInt 64 3) tp i m .unmodeled :=
  clock_gettime_spec_unmodeled_bad_clockid _ _ _ _ (by decide) (by decide)
    (by decide)

/-- The same for a negative `clockid_t`: the negative half of the id
    space is a live CPU-clock family Linux partly answers, and the model
    declines it rather than agree with an `-EINVAL`. -/
example (tp : word) (i : SyscallInput) (m : Model) :
    clock_gettime_spec (BitVec.ofInt 64 (-6)) tp i m .unmodeled :=
  clock_gettime_spec_unmodeled_bad_clockid _ _ _ _ (by decide) (by decide)
    (by decide)

/-- THE RECORDED CLOCK AT OR PAST THE ENVELOPE DECLINES, rather than
    inventing a reading.  Unreachable from `init_model`, but
    `Progress.receptive` quantifies over ARBITRARY model states, and the
    `choose` below would be empty here. -/
theorem clock_gettime_spec_unmodeled_clock_at_envelope (clkid tp : word)
    (i : SyscallInput) (m : Model)
    (hpc : clockid_percall_b clkid = false)
    (hcpu : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = false)
    (hmono : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = true)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = false) :
    clock_gettime_spec clkid tp i m .unmodeled := by
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [bind_unmodeled_iff]
  refine Or.inr ⟨m, m, [], rfl, ?_⟩
  simp only [hclock, Bool.not_false, ite_true, unmodeled]

/-- The same at the concrete envelope: a model whose clock reads
    `CLOCK_NS_ENVELOPE` (one nanosecond past `KTIME_MAX`) declines. -/
example (tp : word) (i : SyscallInput) :
    clock_gettime_spec (BitVec.ofInt 64 1) tp i
      (clockModel (2 ^ 63)) .unmodeled := by
  apply clock_gettime_spec_unmodeled_clock_at_envelope
  · decide
  · decide
  · decide
  · decide

/-- A DESTINATION THAT IS NOT WHOLLY WRITABLE IS DECLINED on the per-call
    arm — the fail-closed gate, which does not commit to `-EFAULT`. -/
theorem clock_gettime_spec_unmodeled_percall_dest (clkid tp : word)
    (i : SyscallInput) (m : Model)
    (hpc : clockid_percall_b clkid = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = none) :
    clock_gettime_spec clkid tp i m .unmodeled := by
  unfold clock_gettime_spec
  simp only [hpc, ite_true]
  refine bind_unmodeled2 _ _ i m i m [] rfl ?_
  simp only [hread, unmodeled]

/-- ...on the CPU-time arm, too. -/
theorem clock_gettime_spec_unmodeled_cputime_dest (tp : word)
    (i : SyscallInput) (m : Model)
    (hpc : clockid_percall_b (BitVec.ofInt 64 2) = false)
    (hcpu : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = none) :
    clock_gettime_spec (BitVec.ofInt 64 2) tp i m .unmodeled := by
  have hmono : (((BitVec.ofInt 64 2).toNat : Int) == CLOCK_MONOTONIC) = false := by
    decide
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.not_false, ite_true]
  refine bind_unmodeled2 _ _ i m i m [] rfl ?_
  simp only [hread, unmodeled]

/-- ...and on the monotonic arm. -/
theorem clock_gettime_spec_unmodeled_monotonic_dest (clkid tp : word)
    (i : SyscallInput) (m : Model)
    (hpc : clockid_percall_b clkid = false)
    (hcpu : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = false)
    (hmono : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = true)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = true)
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = none) :
    clock_gettime_spec clkid tp i m .unmodeled := by
  unfold clock_gettime_spec
  simp only [hpc, hcpu, hmono, Bool.not_true, Bool.false_eq_true, ite_false]
  refine bind_unmodeled2 _ _ i m m m [] rfl ?_
  simp only [hclock, Bool.not_true, Bool.false_eq_true, ite_false]
  refine bind_unmodeled2 _ _ i m i m [] rfl ?_
  simp only [hread, unmodeled]

/-- A BACKWARDS `CLOCK_MONOTONIC` READING IS REJECTED — no admissible
    outcome carries that 16-byte write, whatever else the call does. -/
theorem clock_gettime_spec_monotonic_rejects_backwards (tp : word)
    (i : SyscallInput) (m : Model)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = true)
    (hprev : m_clock m = BitVec.ofInt 64 1000000000)
    {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    ¬ ∃ (eff : SyscallEffect) (m' : Model) (evs : List event),
        clock_gettime_spec (BitVec.ofInt 64 1) tp i m (.ok eff m' evs) ∧
          eff.eff_writes = [(tp, ts1sMinus)] := by
  rintro ⟨eff, m', evs, h, hw⟩
  obtain ⟨bs, hbs, heff, -, -⟩ :=
    clock_gettime_spec_monotonic_shape (clkid := BitVec.ofInt 64 1) (tp := tp)
      (i := i) (m := m) (hpc := by decide) (hcpu := by decide)
      (hmono := by decide) (hclock := hclock) (hread := hread) h
  rw [heff] at hw
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hw
  obtain ⟨-, rfl⟩ := hw
  rw [hprev] at hbs
  exact absurd hbs (by decide)

/-- AN UNNORMALIZED READING IS REJECTED by the same route: the second
    condition is what makes the two fields a unique reading. -/
theorem clock_gettime_spec_monotonic_rejects_denorm (tp : word)
    (i : SyscallInput) (m : Model)
    (hclock : decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE) = true)
    (hprev : m_clock m = BitVec.ofInt 64 0)
    {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    ¬ ∃ (eff : SyscallEffect) (m' : Model) (evs : List event),
        clock_gettime_spec (BitVec.ofInt 64 1) tp i m (.ok eff m' evs) ∧
          eff.eff_writes = [(tp, tsDenorm)] := by
  rintro ⟨eff, m', evs, h, hw⟩
  obtain ⟨bs, hbs, heff, -, -⟩ :=
    clock_gettime_spec_monotonic_shape (clkid := BitVec.ofInt 64 1) (tp := tp)
      (i := i) (m := m) (hpc := by decide) (hcpu := by decide)
      (hmono := by decide) (hclock := hclock) (hread := hread) h
  rw [heff] at hw
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hw
  obtain ⟨-, rfl⟩ := hw
  rw [hprev] at hbs
  exact absurd hbs (by decide)

/-- THE COARSE AND RAW IDS ARE NOT CONSTRAINED AGAINST `m_clock`: a
    reading the monotonic arm refuses is admitted for
    `CLOCK_MONOTONIC_COARSE` (6) even when the model's clock already
    reads a second.  That is the deliberate over-approximation
    `clockid_percall_b`'s header argues for. -/
example (tp : word) (i : SyscallInput) {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    clock_gettime_spec (BitVec.ofInt 64 6) tp i (clockModel 1000000000)
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, ts1sMinus)] [])
        (clockModel 1000000000) []) :=
  clock_gettime_spec_percall_ok _ _ _ _ _ _ (by decide) hread (by decide)

/-- ...whereas the same reading on `CLOCK_MONOTONIC` (1) is refused: the
    two arms differ exactly in what they relate the reading to. -/
example (tp : word) (i : SyscallInput) {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    ¬ ∃ (eff : SyscallEffect) (m' : Model) (evs : List event),
        clock_gettime_spec (BitVec.ofInt 64 1) tp i (clockModel 1000000000)
          (.ok eff m' evs) ∧
          eff.eff_writes = [(tp, ts1sMinus)] :=
  clock_gettime_spec_monotonic_rejects_backwards tp i (clockModel 1000000000)
    (by decide) (clockModel_clock 1000000000) hread

/-- THE WALL CLOCK IS NOT RECORDED: an accepted `CLOCK_REALTIME` reading
    leaves `m_clock` exactly where it was, which is the "a field written
    and read by nothing would be worse than none" decision, made
    checkable. -/
example (tp : word) (i : SyscallInput) {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    clock_gettime_spec (BitVec.ofInt 64 0) tp i (clockModel 1000000000)
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, ts1s)] [])
        (clockModel 1000000000) []) :=
  clock_gettime_spec_percall_ok _ _ _ _ _ _ (by decide) hread (by decide)

/-- ...and the CPU-time arm does not touch it either. -/
example (tp : word) (i : SyscallInput) {bs0 : List byte}
    (hread : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) = some bs0) :
    clock_gettime_spec (BitVec.ofInt 64 2) tp i (clockModel 1000000000)
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tp, ts1s)] [])
        (clockModel 1000000000) []) :=
  clock_gettime_spec_cputime_ok _ _ _ _ _ (by decide) (by decide) hread (by decide)

end LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
