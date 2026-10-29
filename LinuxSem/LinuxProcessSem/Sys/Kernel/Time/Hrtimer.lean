/-
  * LinuxProcessSem.Sys.Kernel.Time.Hrtimer — nanosleep (101)

    This file answers to Linux `kernel/time/hrtimer.c`: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  `Specs.lean` carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    `Specs.lean` holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

  - There is no `bv_unsigned` in the Lean tree ():
    `bv_unsigned prev` is `(prev.toNat : Int)`, the same function on the
    same carrier, and `nanosleep_clock` below uses it in that spelling.
  - `ret_only`/`err_ret`/`record_copyins`/`w_is0` are `Sys/Syscall.lean`'s;
    `timespec_ns`/`timespec_ktime`/`tv_sec_of`/`tv_frac_of`/`KTIME_MAX`/
    `CLOCK_NS_ENVELOPE` are `Sys/Uapi.lean`'s; `read_bytes_map` is
    `State.lean`'s; `m_clock`/`with_clock` are `StateLedger.lean`'s.
    `Require Export Syscall Uapi Uaccess` puts them all in
    unqualified scope; the three `open`s below do the same (the `Uaccess`
    one SELECTIVELY: that file still carries staging copies of
    `ret_only`/`err_ret` — see its note — which must not shadow
    `Sys/Syscall`'s, the same hazard `Sys/Fs/ReadWrite.lean` records).
  - `set_clock` is `Monad.lean`'s
    `Definition set_clock (t : word) : Sys unit := modify (with_clock t)`,
    i.e. exactly `modify` applied to `StateLedger`'s `with_clock`, and
    `Monad.lean` (parameterized over the model) does not carry it.  The
    two write sites below spell that term out as
    `modifySpec (with_clock t)` — the same term, one unfolding closer —
    rather than restating a `Monad.lean` item this file does not own; the
    monotonic writer in `Kernel/Time/PosixTimers.lean` does the same, for
    the same reason.  Nothing is weakened by the spelling.
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
open LinuxSem.LinuxProcessSem.Sys.Uaccess (delivered_writes)

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer

/-- What `timespec64_valid` (include/linux/time64.h, byte-identical at
    v6.10-v6.15) accepts, applied to the 16 bytes read out of `rqtp`:

      if (ts->tv_sec < 0) return false;
      if ((unsigned long)ts->tv_nsec >= NSEC_PER_SEC) return false;

    `tv_sec` is signed, so "not negative" is "below 2^63 read
    unsigned"; `tv_nsec` is cast to unsigned before the comparison, so
    a negative nanosecond field fails the same test a too-large one
    does.  A request failing either is -EINVAL, and the model commits
    to that: the kernel writes nothing and returns before it touches
    `rmtp`.

    No length conjunct: the only caller applies this to exactly the
    bytes `read_bytes_map` returned for a 16-byte read. -/
def timespec_valid_b (bs : List byte) : Bool :=
  decide (tv_sec_of bs < 2 ^ 63)
  && decide (tv_frac_of bs < 1000000000)

/-- What a remainder the kernel wrote into `rmtp` must satisfy.
    Normalized and strictly positive — and NOT bounded by the request,
    which is the surprising half and is argued at `nanosleep_spec`. -/
def nanosleep_rem_ok_b (bs : List byte) : Bool :=
  (bs.length == 16)
  && decide (tv_frac_of bs < 1000000000)
  && decide (0 < timespec_ns bs)
  && decide (timespec_ns bs < CLOCK_NS_ENVELOPE)

/-- The monotonic clock after a sleep that requested `req` and reported
    remainder `rem`.  `rem` is `[]` on the success path, where the whole
    request elapsed — `timespec_ns [] = 0`, both fields decoding out of
    an empty byte list as 0.

    Read it as the deadline the kernel actually armed, less what was
    left of it, and never behind where the clock already stood:

      `timespec_ktime req`              the request, as `ktime_set` took it
      `max (prev + that) KTIME_MAX`     the deadline, SATURATING
      `- timespec_ns rem`               less the reported remainder
      `max prev ...`                    and the clock never runs back

    THE REQUEST SATURATES TWICE, at two different functions, and the
    model needs both.  `hrtimer_nanosleep` is handed a `ktime_t` that
    `SYSCALL_DEFINE2(nanosleep, ...)` built with `timespec64_to_ktime`
    (kernel/time/hrtimer.c and include/linux/ktime.h at v6.18.46),
    which is `ktime_set` and which returns `KTIME_MAX` outright once
    `tv_sec >= KTIME_SEC_MAX` — that is `Uapi.timespec_ktime`, and it
    is what makes a request past the ceiling a SLEEP rather than a
    shape to decline.  The absolute expiry then saturates again, at
    `ktime_add_safe`, which is the `min` below.

    THE TWO SATURATIONS ARE NOT LOAD-BEARING IN THE SAME WAY, and it is
    worth being exact about which one soundness needs, because getting
    the reason wrong here would license removing the other one.

    THE SECOND IS LOAD-BEARING: without the `min`, an ordinary sleep
    against a clock near the ceiling would record a sum `ktime_t`
    cannot hold, and the paragraph below shows the lower bound fails
    outright there.

    THE FIRST IS NOT, and the argument is the `min` rather than any
    comparison between `timespec_ns` and `timespec_ktime` — those two
    do not order the convenient way.  In the band `ktime_set` saturates
    over, the deadline the kernel armed is `KTIME_MAX` exactly: the
    conversion hands `hrtimer_nanosleep` that constant and every add
    after it saturates back to it.  A model that read the request as a
    plain product and clamped afterwards would record
    `min (prev + timespec_ns req) KTIME_MAX`, and NO value of that
    shape exceeds `KTIME_MAX`, so it would still be at or below the
    armed deadline — a sound lower bound, whichever way the two
    readings of the request happen to compare.

    What `timespec_ktime` buys is EXACTNESS, and only in one place: at `tv_sec =
    KTIME_SEC_MAX` with `tv_nsec` under 854775807 the product is BELOW `KTIME_MAX`,
    so the plain-product model would record less time than the kernel really armed.
    All three have since landed in `Checks/Cases/Kernel/Time/Hrtimer.lean`; that
    module is not yet imported by the root module, so this note's argument still
    stands on its own rather than on them.

    THE SATURATION IS THE KERNEL'S, not a modeling convenience.
    `__hrtimer_start_range_ns` (kernel/time/hrtimer.c at v6.18.46)
    turns the relative request into an absolute expiry with

      if (mode & HRTIMER_MODE_REL)
              tim = ktime_add_safe(tim, __hrtimer_cb_get_time(base->clockid));

    and `ktime_add_safe` (same file, same tree)
    does NOT report an error when that sum leaves the type: it adds as
    `u64`, tests `if (res < 0 || res < lhs || res < rhs)`, and on any
    of those replaces the result with `ktime_set(KTIME_SEC_MAX, 0)` —
    which is `KTIME_MAX`, for the `>=` reason `Uapi.KTIME_MAX` argues.
    Since both operands are non-negative `ktime_t`s, that test fires
    exactly when the true sum exceeds `KTIME_MAX`, so the arm is a
    `min` with `KTIME_MAX` and nothing else.  A sleep whose deadline
    would leave the type therefore SUCCEEDS, at a nearer deadline; it
    does not fail, and it is not a shape the model may decline.

    THE CALL SITE IS STABLE; THE FUNCTION AROUND IT IS NOT, which is
    worth recording because it is what a two-endpoint check misses.
    `__hrtimer_start_range_ns` has had three shapes across the versions
    cited here: byte-identical at v6.10-v6.13, changed for
    v6.14 by commit 2f8dea1692ee ("hrtimers: Handle CPU state correctly
    on hotplug", which adds the offline-CPU handling), and changed
    again by v6.18.46, where `hrtimer_clock_base` no longer carries a
    `get_time` pointer on this path and the reading goes through
    `__hrtimer_cb_get_time(base->clockid)` instead.  None of the three
    touches the `HRTIMER_MODE_REL` branch or the `ktime_add_safe` call
    it feeds, so the argument above holds across all of them — but the
    spec cites v6.18.46 and quotes that tree, not the window.

    WHY THIS IS A SOUND LOWER BOUND, which is the only thing `m_clock`
    claims.  Write `now` for the real monotonic clock when the call
    started and `wake` for when it returned; `prev <= now <= wake`.
    Write `k` for the request as a `ktime_t`, which is
    `timespec_ktime req`: the syscall converted it with
    `timespec64_to_ktime` before `hrtimer_nanosleep` ever saw it, so
    `k` and not the `timespec` product is what the timer was armed
    from.  `_softexpires` is `ktime_add_safe(now, k) = min (now + k)
    KTIME_MAX`.  `node.expires` is that plus a NON-NEGATIVE delta —
    `hrtimer_start_expires` (include/linux/hrtimer.h) hands
    `hrtimer_start_range_ns` the gap between the relative pair
    `hrtimer_nanosleep` set, which is the task's timer slack less
    whatever the relative add itself saturated away — and the delta is
    added with `ktime_add_safe` again.  The exact width does not matter
    to the bound; only that it is non-negative, so
    `node.expires >= _softexpires`.  `do_nanosleep` computes the
    remainder as `hrtimer_expires_remaining`
    (include/linux/hrtimer.h), which is `node.expires - now_at_wake`,
    so

      `wake = node.expires - rem >= _softexpires - rem`
           ` = min (now + k) KTIME_MAX - rem`
           `>= min (prev + k) KTIME_MAX - rem`

    the last step by `now >= prev` and `min` being monotone.  Taking
    `max` with `prev` keeps the other lower bound `wake >= prev`, so
    the recorded value is below the real clock on both arms.

    WITHOUT THE `min` THE BOUND IS FALSE, and not by a rounding
    error.  Once the deadline saturates, the sleep is SHORTER than the
    request — the kernel armed `KTIME_MAX`, not `now + k` — so
    recording `prev + k` would claim time that never elapsed and
    would let a later `clock_gettime` reading be rejected for running
    backwards when it did no such thing.  That is a false REJECTION,
    the worse kind.

    `max prev` is load-bearing for two separate reasons, and the
    second is new here.  A remainder may EXCEED the request, by up to
    the task's timer slack, so the subtraction goes negative on an
    ordinary interruption — `nanosleep_spec` argues that at length.
    And once the deadline saturates, `KTIME_MAX - rem` can fall below
    `prev` outright, which is the same subtraction going negative
    against a different quantity.  Both are the clock refusing to run
    backwards.

    THE RESULT STAYS UNDER `CLOCK_NS_ENVELOPE`, so this spec cannot
    push `m_clock` into the band
    `Kernel.Time.PosixTimers.clock_gettime_spec` declines on: the value
    is at most `max prev KTIME_MAX`, and `KTIME_MAX` is
    `CLOCK_NS_ENVELOPE - 1`.  So a model whose clock is below the
    envelope still has one after any sleep, which is what lets this
    file carry no envelope gate of its own. -/
def nanosleep_clock (prev : word) (req rem : List byte) : word :=
  BitVec.ofInt 64
    (max (prev.toNat : Int)
       (min ((prev.toNat : Int) + timespec_ktime req) KTIME_MAX
        - timespec_ns rem))

/-- `nanosleep rqtp rmtp`: sleep for a relative `struct timespec`, and
    on interruption report what was left.

    BOTH OUTCOMES ARE ADMITTED, and that is the decision this spec
    turns on.  The tempting simplification is that the model has no
    signals, so -EINTR cannot arise and the success path is the only
    one.  It does not survive contact with the source: the model does
    not FORBID signals, it says nothing about them, and a real kernel
    running the real program delivers them.  In dropbear specifically
    it does — `sesssigchild_handler` is installed for SIGCHLD in the
    very session process that runs the anti-user-enumeration auth
    delay (src/svr-chansession.c at v2026.94), and the delay is
    `while (nanosleep(&delay, &delay) == -1 && errno == EINTR) {}`
    (src/svr-auth.c).  A model claiming `nanosleep` always succeeds
    would REJECT that conforming trace.  So the environment chooses
    which outcome occurred, exactly as it chooses a short read: an
    `alt` of a completed sleep and an interruption.

    Declining just the interrupted case is not available: whether a
    signal arrived is not a function of the arguments, so there is no
    gate to put it behind, and folding `unmodeled` into the `alt` would
    make EVERY `nanosleep` call unmodeled rather than some of them —
    the same trap `Drivers.Char.Random.getrandom_spec` spells its
    zero-byte arm out to avoid.

    ALIASING IS FINE.  dropbear passes `rqtp == rmtp`, the same 16
    bytes as request and remainder.  The kernel reads the request into
    a kernel-local `struct timespec64` with `get_timespec64` before
    anything else, and only writes `rmtp` at the very end, so the write
    cannot disturb the read.  The model has the same order — `req` is
    read out of `in_mem` and the remainder is a separate write entry —
    so nothing special is needed and no gate has to notice the two
    pointers are equal.

    ORDER, following `SYSCALL_DEFINE2(nanosleep, ...)`
    (kernel/time/hrtimer.c, byte-identical at v6.10-v6.15): the
    request is read first (`get_timespec64`, -EFAULT), validated
    second (`timespec64_valid`, -EINVAL), and only then slept on.
    `rmtp` is NEVER validated up front — a completed sleep with an
    unwritable `rmtp` answers 0 without touching it — which the model
    gives up by gating on `rmtp` before the `alt`.  The cost is
    coverage on a shape the model could have answered; the reason is
    the straddle below.

    THE REQUEST'S CEILING IS JUDGED, not declined.
    `timespec64_to_ktime` is `ktime_set` (include/linux/ktime.h at
    v6.18.46), which returns `KTIME_MAX` outright when
    `secs >= KTIME_SEC_MAX` rather than converting.  A request at or
    above that ceiling is therefore a sleep toward the end of
    `ktime_t` — an ORDINARY interruptible sleep, armed by the same
    `__hrtimer_start_range_ns`, waited on by the same `do_nanosleep`
    and broken by the same signal as any other, differing only in the
    deadline it carries.  Linux does not refuse it, so the model does
    not decline it: `Uapi.timespec_ktime` carries the conversion into
    `nanosleep_clock` and both arms answer.  Note where the band sits:
    a `tv_sec` at or past 2^63 reads as negative and is -EINVAL, and
    the band this paragraph is about is the valid one just below it,
    `[KTIME_SEC_MAX, 2^63)`.

    WHAT THE MODEL ANSWERS THERE, since "judged" has to name an answer.
    Both arms stay admissible and the environment still chooses.  On an
    interruption `m_clock` moves to `KTIME_MAX` less the reported
    remainder, floored at `prev` — the deadline the kernel really armed
    less what was left of it, exactly as at any other request.  On a
    completed sleep `m_clock` moves to `KTIME_MAX`, and the model is
    then claiming the monotonic clock reached the largest value
    `ktime_t` holds; that is what returning 0 from a timer armed at
    `KTIME_MAX` means, and it is sound for the reason every completed
    sleep is — a timer never fires before its soft expiry.  In practice
    that arm is the one no run reaches, since `KTIME_MAX` is 292 years
    of CLOCK_MONOTONIC away.  The model does not say so and does not
    need to: an admissible outcome nothing reaches costs nothing, where
    a decline costs the whole program.

    WHY IT IS NOT DECLINED, which is not a coverage argument.  The
    remainder this spec may WRITE is not bounded by the request, and
    `nanosleep_rem_ok_b` admits any normalized positive `timespec`
    under `CLOCK_NS_ENVELOPE` — `tv_sec = KTIME_SEC_MAX` among them,
    inside that envelope by 854775808 ns.  The standard retry loop
    hands the remainder straight back as the next request:
    `while (nanosleep(&ts, &ts) == -1 && errno == EINTR);`, which is
    dropbear's auth delay (src/svr-auth.c) and is quoted above.  So
    with a decline, ONE
    admissible environment choice — interrupt, report
    `{KTIME_SEC_MAX, 0}` — would make the NEXT call `unmodeled`.
    `Equivalence.modeled` is the negation of an existential over
    resolutions, so that single resolution would cost the whole program its
    `modeled` status, on every input on which it slept at all.

    THE OTHER FIX IS NOT AVAILABLE.  Bounding the admissible remainder
    by the request would close the loop too, and would be wrong:
    `hrtimer_expires_remaining` measures against `node.expires`, which
    `hrtimer_set_expires_range_ns` puts `current->timer_slack_ns` past
    the soft expiry, and `prctl(PR_SET_TIMERSLACK)` (kernel/sys.c) sets
    that field to any nonzero `unsigned long`, and an `arg2` of 0
    RESETS to `current->default_timer_slack_ns` rather than setting
    zero.  Neither restriction bounds the slack from above, and the
    value is inherited from the parent rather than derived from
    anything the model can see, so there is nothing to bound it WITH:
    the model carries no timer slack.

    THE CLOCK ADVANCES, and the bound is one-sided on purpose.
    (`hrtimer_nanosleep` and `do_nanosleep` are both in
    kernel/time/hrtimer.c; `do_nanosleep` is byte-identical at
    v6.10-v6.15, `hrtimer_nanosleep` at v6.12-v6.15.  The boundary is
    v6.12 and not v6.13: v6.10 and v6.11 carry
    `slack = current->timer_slack_ns; if (rt_task(current)) slack = 0;`
    and pass `slack`, where v6.12 onwards passes
    `current->timer_slack_ns` to `hrtimer_set_expires_range_ns`
    unconditionally.  Those two earlier spellings therefore differ only
    in zeroing the slack for an RT task explicitly rather than relying
    on the scheduler having already zeroed `timer_slack_ns`, and — from
    v6.15 — in the `hrtimer_init_sleeper_on_stack` to
    `hrtimer_setup_sleeper_on_stack` rename.  No behavioural difference
    for a task under a policy that is neither RT nor SCHED_DEADLINE,
    which is every task the model describes: `State.init_model` starts
    an ordinary exec, and the one arm that can change the policy at
    all, `Kernel.Sched.Syscalls.sched_setscheduler_spec`, answers
    SCHED_IDLE and declines every RT and DEADLINE request.)

    - ON A COMPLETED SLEEP, by the request as `ktime_set` took it — or
      up to `Uapi.KTIME_MAX`, whichever is nearer.  `hrtimer_nanosleep`
      arms a CLOCK_MONOTONIC hrtimer with `HRTIMER_MODE_REL` and a
      soft expiry of exactly now + that `ktime_t` SATURATED at the top
      of the type by `ktime_add_safe`, and a timer never fires
      before its soft expiry, so returning 0 means at least that much
      elapsed on the very clock `m_clock` tracks.  THERE IS NO GATE ON
      THE SUM: a sleep whose deadline would leave the type is one
      Linux serves at a nearer deadline rather than refusing, so the
      model records the nearer deadline instead of declining.
      `nanosleep_clock` carries the saturation and the argument that
      what it records is a lower bound on the real clock.  Recording
      that is strictly more faithful than leaving the clock still: it
      makes a later `clock_gettime` have to report a time at least a
      sleep further on.  It also covers the case that LOOKS like an
      interruption and is reported as success — `do_nanosleep` returns
      0 without writing anything when the remainder it computes is at
      or below zero, and that can only happen once the deadline is
      past.
    - ON AN INTERRUPTION, by the SATURATED DEADLINE less the reported
      remainder, floored at the clock's previous value — the same
      `min (prev + timespec_ktime req) KTIME_MAX` the completed sleep
      records, minus what was left of it.  The deadline is the one the kernel really
      armed, so subtracting the remainder from it subtracts from the
      sleep that RAN rather than from the one that was asked for; the
      two differ exactly when the request saturated.  The floor is
      reachable, which is the one genuinely surprising fact in this
      syscall.  `do_nanosleep`
      computes the remainder as `hrtimer_expires_remaining`
      (include/linux/hrtimer.h), which measures against the HARD
      expiry, and `hrtimer_nanosleep` sets the hard expiry to
      `current->timer_slack_ns` PAST the soft one
      (`hrtimer_set_expires_range_ns`).  So a remainder may EXCEED the
      request, by up to the task's timer slack — 50 microseconds by
      default (`init_task`'s `.timer_slack_ns = 50000` in
      init/init_task.c), inherited rather than derived, and settable by
      `prctl(PR_SET_TIMERSLACK)` — though not to ANYTHING: kernel/sys.c
      breaks out without setting when `rt_or_dl_task_policy(current)`,
      and an `arg2 <= 0` RESETS to `current->default_timer_slack_ns`
      rather than setting that value.  Neither restriction bounds the
      slack from above for the non-RT, non-DEADLINE tasks this model
      describes, which is what the argument below needs.  This is why
      `nanosleep_rem_ok_b` does NOT bound the remainder by the
      request: a model that did would reject a trace a real kernel can
      produce, and the model carries no timer slack to bound it
      properly.  What survives is the one-sided fact that at least
      (deadline - remainder) elapsed, which is what gets recorded, and
      the `max prev` is what makes that statable when the difference
      goes the other way: the clock stands still rather than running
      backwards.

    A REMAINDER IS WRITTEN ONLY WITH THE INTERRUPTION, and only when
    it is strictly positive: `do_nanosleep` returns 0 without writing
    when the computed remainder is at or below zero, so the completed
    sleep has no write entry at all and -EINTR with a non-NULL `rmtp`
    always has exactly one, never `{0, 0}`.  With a NULL `rmtp` the
    restart block's type is `TT_NONE` and nothing is written on either
    path — and then the slept duration is unknowable, so that
    interrupted arm leaves the clock where it was.

    -EINTR NEEDS A HANDLER TO HAVE RUN, and the model does not step
    one.  `do_nanosleep` itself never returns -EINTR; it returns
    -ERESTART_RESTARTBLOCK, and riscv64's
    `arch_do_signal_or_restart` (arch/riscv/kernel/signal.c,
    byte-identical at v6.10-v6.15) rewrites that to -EINTR ONLY on the
    branch where `get_signal` handed back a signal to deliver — and it
    does so there whatever the handler's flags say, the `SA_RESTART`
    test being attached to the -ERESTARTSYS disjunct alone, which is
    why `SA_RESTART` does not make `nanosleep` restartable.  (The one
    other guard on that rewrite is `regs->epc == restart_addr`, which
    fails only when a ptracer has moved the program counter, and the
    model steps no ptracer.)  So a run that observes -EINTR is a run
    in which a handler's instructions executed, and those the machine
    model does not step.  Admitting this arm therefore does not model
    signal delivery; it stops the model REJECTING the one part of a
    signal-interrupted run that is visible at the syscall boundary.
    Whether the rest of such a run is covered is a pre-existing gap
    and not one this changes.

    NOT MODELED: the transparent-restart path.  When `get_signal` has
    nothing to deliver — a job-control stop and continue — the same
    -ERESTART_RESTARTBLOCK is turned into a fresh `restart_syscall`
    (nr 128) with the program counter rewound, rather than a return to
    the program.  `rmtp` HAS ALREADY BEEN WRITTEN by then, because
    `nanosleep_copyout` runs inside `do_nanosleep`, before the signal
    layer chooses.  What the model would see at that step is neither
    of the two arms, so it REJECTS rather than declining: a known
    gap.  Reaching it takes
    a stop signal from another process, and the number the run goes on
    to make is outside `Specs.modeled_sysnos` anyway.

    THE REQUEST IS A COPY-IN.  `get_timespec64` (kernel/time/time.c,
    byte-identical at v6.10-v6.15) is a single
    `copy_from_user(&kts, uts, sizeof(kts))` of the whole
    `struct __kernel_timespec` into a kernel-local `struct timespec64`,
    and it runs BEFORE any other decision the call makes.  The width is
    16 because that struct is two 8-byte fields — `__kernel_time64_t
    tv_sec` and `long long tv_nsec` (include/uapi/linux/time_types.h).
    So every outcome reached through a successful read has already
    consumed those bytes — the -EINVAL, the one decline that is left
    past it, the completed sleep and the interruption alike — and
    `record_copyins` therefore wraps the whole `some req` arm rather
    than any one branch of it.  The `none` arm carries no ledger
    because nothing was copied: a request that is not wholly readable
    is the -EFAULT `get_timespec64` reports with the kernel buffer
    untouched, and the model declines that shape rather than describing
    it. -/
def nanosleep_spec (rqtp rmtp : word) : SysSpec SyscallEffect :=
  bind inputSpec fun i =>
    match read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) with
    | none => unmodeled   -- request not wholly readable: fail closed
    | some req =>
        record_copyins [(rqtp, 16)]
        (
        if !(timespec_valid_b req) then err_ret EINVAL
        else
        bind getModelSpec fun m =>
        let slept : SysSpec SyscallEffect :=
          seqSpec (modifySpec (with_clock (nanosleep_clock (m_clock m) req [])))
            (ret_only (BitVec.ofInt 64 0))
        if w_is0 rmtp
        then alt slept (err_ret EINTR)   -- nothing to report the remainder in
        else
          match read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) with
          | none => unmodeled
              -- remainder destination not wholly writable.  Linux answers
              -- -EFAULT here HAVING CONSUMED THE SLEEP and, on a 16-byte
              -- `rmtp` straddling into an unwritable page, having torn
              -- the struct: `put_timespec64`'s `copy_to_user` reaches
              -- riscv64's `__asm_copy_to_user` (arch/riscv/lib/uaccess.S),
              -- which copies forward and leaves the bytes it managed
              -- written.  Fail closed.
          | some _ =>
              alt slept
                (bind (choose (fun rem : List byte =>
                          nanosleep_rem_ok_b rem = true)) fun rem =>
                 seqSpec (modifySpec (with_clock (nanosleep_clock (m_clock m) req rem)))
                   (pure (mkEffect (errno_ret EINTR) [(rmtp, rem)] []))))

/-! ## Sanity checks

  What follows is the port's own check on the computable part (AGENTS.md, "definition
  of done"): the two predicates on the bytes `read_bytes_map` hands over, the clock
  arithmetic including both saturations and the floor, and the shape of each arm of
  `nanosleep_spec` — the -EINVAL, the completed sleep with `rmtp` NULL, the -EINTR
  with its remainder write-back, and the two declines. -/

/-! ### Inversion helpers for the monad (port scaffolding)

    `bind` has no inversion lemma at the concrete types, and the arm
    checks below need to read an outcome backwards.  Both iffs are
    definitional (`Iff.rfl`), so nothing is assumed: they only name the
    unfoldings `bind`'s body already gives.  `Sys/Kernel/Time/Time.lean`
    carries the first of them; the two steps that are definitional
    (`pure`, `choose`) are discharged by `pure_ok`/`choose_ok`, and the
    clock write's by `rfl`. -/

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

/-- The model's clock is what the write put there — the clock advance,
    read off the model rather than off the effect.  (`State/StateMatrix.lean`
    registers the same identity as a `@[simp]` lemma; it is restated here
    because this file does not import that one.) -/
theorem m_clock_with_clock (t : word) (m : Model) : m_clock (with_clock t m) = t :=
  rfl

/-! ### `timespec64_valid`, as `timespec_valid_b` reads it -/

/-- A well-formed `struct __kernel_timespec`: `tv_sec = 3`,
    `tv_nsec = 5`, 8 little-endian bytes each. -/
private def tsOk : List byte := Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 5

/-- The well-formed request passes both conjuncts. -/
example : timespec_valid_b tsOk = true := by decide

/-- An empty byte list decodes both fields as 0 and passes — the
    predicate has no length conjunct, which is the point of the note on
    `timespec_valid_b`. -/
example : timespec_valid_b [] = true := by decide

/-- A NEGATIVE `tv_nsec` is the -EINVAL of the second conjunct: the
    field is cast to `unsigned long` before the comparison, so -1 reads
    as 2^64-1, far past `NSEC_PER_SEC`. -/
example : timespec_valid_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 (-1)) = false := by
  decide

/-- `tv_nsec = 10^9` itself is refused: the comparison is `>=`. -/
example : timespec_valid_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 1000000000) = false := by
  decide

/-- …and one nanosecond below it passes. -/
example : timespec_valid_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 999999999) = true := by
  decide

/-- A NEGATIVE `tv_sec` is the -EINVAL of the first conjunct: `tv_sec` is
    signed, so "not negative" is "below 2^63 read unsigned". -/
example : timespec_valid_b (Z_to_le_bytes 8 (-1) ++ Z_to_le_bytes 8 5) = false := by
  decide

/-- `tv_sec = 2^63` — the first value that reads back negative — is
    refused too, and the test is strict. -/
example : timespec_valid_b (Z_to_le_bytes 8 (2 ^ 63) ++ Z_to_le_bytes 8 5) = false := by
  decide

/-- 15 bytes still passes when both fields decode under their bounds:
    there is NO length conjunct, which is exactly the note in the
    comment on `timespec_valid_b` and not an accident of the encoding. -/
example : timespec_valid_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 7 5) = true := by
  decide

/-! ### What a remainder may be -/

/-- One second and no nanoseconds: normalized and positive. -/
example : nanosleep_rem_ok_b (Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 0) = true := by
  decide

/-- `tv_nsec = 10^9` is not normalized. -/
example : nanosleep_rem_ok_b (Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 1000000000) = false := by
  decide

/-- The length test is EXACTLY 16. -/
example : nanosleep_rem_ok_b (Z_to_le_bytes 8 1 ++ Z_to_le_bytes 7 0) = false := by
  decide

/-- `{0, 0}` is NOT a remainder the kernel writes: `do_nanosleep`
    returns 0 without writing when the remainder is at or below zero. -/
example : nanosleep_rem_ok_b (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0) = false := by
  decide

/-- `tv_sec = KTIME_SEC_MAX` IS admitted, though the request could never
    have been that long: the predicate does not bound the remainder by
    the request, which is the surprising half and is argued at
    `nanosleep_spec`. -/
example : nanosleep_rem_ok_b (Z_to_le_bytes 8 KTIME_SEC_MAX ++ Z_to_le_bytes 8 0) = true := by
  decide

/-! ### `nanosleep_clock`: the advance, both saturations, and the floor -/

/-- A five-second request against a clock at 1000 ns: the completed
    sleep advances the clock by the request.  `rem = []` decodes to 0. -/
example :
    nanosleep_clock (BitVec.ofInt 64 1000)
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0) [] = BitVec.ofInt 64 5000001000 := by
  decide

/-- A zero-duration request leaves the clock exactly where it stood: the
    zero-duration success, at the level of the clock. -/
example :
    nanosleep_clock (BitVec.ofInt 64 1000)
      (Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0) [] = BitVec.ofInt 64 1000 := by
  decide

/-- The interruption case: a 3-second remainder taken off a 5-second
    deadline records `prev + 5s - 3s`, not the whole request. -/
example :
    nanosleep_clock (BitVec.ofInt 64 1000)
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0)
      (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 0) = BitVec.ofInt 64 2000001000 := by
  decide

/-- A remainder that EXCEEDS the request floors at the previous reading:
    the clock stands still rather than running backwards, which is the
    floor's first reason. -/
example :
    nanosleep_clock (BitVec.ofInt 64 1000)
      (Z_to_le_bytes 8 1 ++ Z_to_le_bytes 8 0)
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0) = BitVec.ofInt 64 1000 := by
  decide

/-- THE REQUEST SATURATES AT `KTIME_SEC_MAX`: `timespec_ktime` hands back
    `KTIME_MAX` rather than the product, so a request at the ceiling
    records the ceiling (the deadline `min` cannot raise it, and
    `prev` is below it). -/
example :
    nanosleep_clock (BitVec.ofInt 64 1000)
      (Z_to_le_bytes 8 KTIME_SEC_MAX ++ Z_to_le_bytes 8 0) [] =
        BitVec.ofInt 64 KTIME_MAX := by
  decide

/-- …and THE DEADLINE SATURATES: with the clock already near the top of
    `ktime_t`, an ordinary five-second request still records a value
    `ktime_t` holds, not a wrapped sum. -/
example :
    nanosleep_clock (BitVec.ofInt 64 (KTIME_MAX - 1000))
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0) [] = BitVec.ofInt 64 KTIME_MAX := by
  decide

/-- The floor's second reason: once the deadline saturates,
    `KTIME_MAX - rem` can fall below `prev` outright, and the recorded
    clock is `prev`. -/
example :
    nanosleep_clock (BitVec.ofInt 64 (KTIME_MAX - 1000))
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0)
      (Z_to_le_bytes 8 5 ++ Z_to_le_bytes 8 0) = BitVec.ofInt 64 (KTIME_MAX - 1000) := by
  decide

/-! ### The arms of `nanosleep_spec` -/

/-- A request that is not wholly readable is DECLINED, before anything
    else is decided: the `-EFAULT` `get_timespec64` would report is a
    shape the model refuses to describe, and no copy-in is recorded. -/
theorem nanosleep_spec_unmodeled_read (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = none) :
    nanosleep_spec rqtp rmtp i m .unmodeled := by
  unfold nanosleep_spec
  simp only [bind_unmodeled_iff]
  refine Or.inr ⟨i, m, [], rfl, ?_⟩
  simp only [hread]
  exact unmodeled_intro i m

/-- THE -EINVAL ARM: a request `timespec64_valid` refuses answers -EINVAL,
    writes nothing, leaves the clock untouched — and still records the
    16-byte copy-in, because `get_timespec64` runs before the validation
    and so every outcome past a successful read has consumed those
    bytes. -/
theorem nanosleep_spec_einval (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hbad : timespec_valid_b req = false) :
    nanosleep_spec rqtp rmtp i m
      (.ok (with_copyins [(rqtp, 16)] (mkEffect (errno_ret EINVAL) [] [])) m []) := by
  unfold nanosleep_spec
  simp only [bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread]
  refine record_copyins_ok_empty (reads := [(rqtp, 16)])
    (eff := mkEffect (errno_ret EINVAL) [] []) rfl ?_
  simp only [hbad, Bool.not_false, ite_true]
  exact pure_ok (mkEffect (errno_ret EINVAL) [] []) i m

/-- THE COMPLETED SLEEP, with `rmtp` NULL: the return is a literal 0 and
    the clock advances by `nanosleep_clock (m_clock m) req []`, i.e. by
    the request as `ktime_set` took it, saturated at `KTIME_MAX`.  With
    a zero-duration request that value is the previous reading, so this
    is the zero-duration success as well — see
    `nanosleep_spec_zero_duration` for that case stated directly. -/
theorem nanosleep_spec_slept (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hvalid : timespec_valid_b req = true) (hnull : w_is0 rmtp = true) :
    nanosleep_spec rqtp rmtp i m
      (.ok (with_copyins [(rqtp, 16)] (mkEffect (BitVec.ofInt 64 0) [] []))
        (with_clock (nanosleep_clock (m_clock m) req []) m) []) := by
  unfold nanosleep_spec
  simp only [bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread]
  refine record_copyins_ok_empty (reads := [(rqtp, 16)])
    (eff := mkEffect (BitVec.ofInt 64 0) [] []) rfl ?_
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [bind_ok_iff]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  simp only [hnull, ite_true]
  refine alt_l _ _ i m _ ?_
  unfold seqSpec
  simp only [bind_ok_iff]
  refine ⟨(), with_clock (nanosleep_clock (m_clock m) req []) m, [], [], rfl, ?_, rfl⟩
  exact pure_ok (mkEffect (BitVec.ofInt 64 0) [] []) i _

/-- THE ZERO-DURATION SUCCESS, stated as the clock standing still: a
    request whose `ktime_t` is 0 records `nanosleep_clock prev req []`,
    which is `prev` re-encoded.  (The value is `max prev (min (prev + 0)
    KTIME_MAX - 0)` and `min (prev + 0) KTIME_MAX ≤ prev`, so the outer
    `max` keeps `prev`.) -/
theorem nanosleep_clock_zero (prev : word) (req : List byte)
    (h : timespec_ktime req = 0) :
    nanosleep_clock prev req [] = prev := by
  have hns : timespec_ns ([] : List byte) = 0 := by decide
  -- `min p KTIME_MAX ≤ p` whatever `p` is, so the outer `max` keeps `p`;
  -- the split is only because `Int.min`'s two lemmas each need an order.
  have hmax : max (prev.toNat : Int) (min (prev.toNat : Int) KTIME_MAX) =
      (prev.toNat : Int) := by
    by_cases hle : (prev.toNat : Int) ≤ KTIME_MAX
    · rw [Int.min_eq_left hle, Int.max_self]
    · have hlt : KTIME_MAX ≤ (prev.toNat : Int) := Int.le_of_lt (Int.lt_of_not_ge hle)
      rw [Int.min_eq_right hlt, Int.max_eq_left hlt]
  unfold nanosleep_clock
  rw [h, hns, Int.add_zero, Int.sub_zero, hmax, BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- …and at the level of the spec: a zero-duration sleep with `rmtp`
    NULL answers 0 and leaves `m_clock` exactly where it was. -/
theorem nanosleep_spec_zero_duration (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hvalid : timespec_valid_b req = true) (hnull : w_is0 rmtp = true)
    (hzero : timespec_ktime req = 0) :
    nanosleep_spec rqtp rmtp i m
      (.ok (with_copyins [(rqtp, 16)] (mkEffect (BitVec.ofInt 64 0) [] [])) m []) := by
  have h := nanosleep_spec_slept rqtp rmtp i m hread hvalid hnull
  rw [nanosleep_clock_zero (m_clock m) req hzero] at h
  exact h

/-- THE INTERRUPTION ARM: with a non-NULL, wholly writable `rmtp`, the
    environment may report any remainder the predicate admits; the
    return is -EINTR, exactly one 16-byte write goes to `rmtp`, and the
    clock advances by the saturated deadline less that remainder. -/
theorem nanosleep_spec_rem (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hvalid : timespec_valid_b req = true) (hnull : w_is0 rmtp = false)
    {bs0 : List byte} (hwmem : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) = some bs0)
    (rem : List byte) (hrem : nanosleep_rem_ok_b rem = true) :
    nanosleep_spec rqtp rmtp i m
      (.ok (with_copyins [(rqtp, 16)] (mkEffect (errno_ret EINTR) [(rmtp, rem)] []))
        (with_clock (nanosleep_clock (m_clock m) req rem) m) []) := by
  unfold nanosleep_spec
  simp only [bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread]
  refine record_copyins_ok_empty (reads := [(rqtp, 16)])
    (eff := mkEffect (errno_ret EINTR) [(rmtp, rem)] []) rfl ?_
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [bind_ok_iff]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  simp only [hnull, Bool.false_eq_true, ite_false, hwmem]
  refine alt_r _ _ i m _ ?_
  simp only [bind_ok_iff]
  refine ⟨rem, m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ rem i m hrem
  · unfold seqSpec
    simp only [bind_ok_iff]
    refine ⟨(), with_clock (nanosleep_clock (m_clock m) req rem) m, [], [], rfl, ?_, rfl⟩
    exact pure_ok (mkEffect (errno_ret EINTR) [(rmtp, rem)] []) i _

/-- …and the -EINTR arm when `rmtp` is NULL: nothing may be written, so
    the slept duration is unknowable and THE CLOCK STAYS WHERE IT WAS. -/
theorem nanosleep_spec_intr_null (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hvalid : timespec_valid_b req = true) (hnull : w_is0 rmtp = true) :
    nanosleep_spec rqtp rmtp i m
      (.ok (with_copyins [(rqtp, 16)] (mkEffect (errno_ret EINTR) [] [])) m []) := by
  unfold nanosleep_spec
  simp only [bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread]
  refine record_copyins_ok_empty (reads := [(rqtp, 16)])
    (eff := mkEffect (errno_ret EINTR) [] []) rfl ?_
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [bind_ok_iff]
  refine ⟨m, m, [], [], rfl, ?_, rfl⟩
  simp only [hnull, ite_true]
  refine alt_r _ _ i m _ ?_
  exact pure_ok (mkEffect (errno_ret EINTR) [] []) i m

/-- THE STRADDLE DECLINE: a remainder destination that is not wholly
    writable is unmodeled, and it is unmodeled AFTER the sleep was
    consumed — which is what the comment at the arm says, and why the
    arm cannot answer -EFAULT with the clock untouched. -/
theorem nanosleep_spec_unmodeled_rmtp (rqtp rmtp : word) (i : SyscallInput) (m : Model)
    {req : List byte} (hread : read_bytes_map i.in_mem rqtp (BitVec.ofInt 64 16) = some req)
    (hvalid : timespec_valid_b req = true) (hnull : w_is0 rmtp = false)
    (hwmem : read_bytes_map i.in_wmem rmtp (BitVec.ofInt 64 16) = none) :
    nanosleep_spec rqtp rmtp i m .unmodeled := by
  unfold nanosleep_spec
  simp only [bind_unmodeled_iff]
  refine Or.inr ⟨i, m, [], rfl, ?_⟩
  simp only [hread]
  refine record_copyins_unmodeled ?_
  simp only [hvalid, Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [bind_unmodeled_iff]
  refine Or.inr ⟨m, m, [], rfl, ?_⟩
  simp only [hnull, Bool.false_eq_true, ite_false, hwmem]
  exact unmodeled_intro i m

/-- THE REMAINDER WRITE, in `Uaccess.delivered_writes`' canonical shape:
    an admissible remainder is 16 bytes, so the write list is exactly one
    entry and never the vacuous `(rmtp, [])` the zero-byte shape would
    give.  That is the "never `{0, 0}`" half of the note above the
    interruption arm, read through the shared write shape. -/
theorem nanosleep_rem_write_shape (rmtp : word) (rem : List byte)
    (hrem : nanosleep_rem_ok_b rem = true) :
    delivered_writes rmtp rem = [(rmtp, rem)] := by
  cases rem with
  | nil => simp [nanosleep_rem_ok_b] at hrem
  | cons b bs => rfl

/-- …and the two halves of the written effect: the remainder arm's list
    is the only write entry and the copy-in is carried beside it, not
    inside it. -/
example (rmtp : word) (rem : List byte) :
    (mkEffect (errno_ret EINTR) [(rmtp, rem)] []).eff_writes = [(rmtp, rem)] := rfl

example (rmtp : word) (rem : List byte) :
    (mkEffect (errno_ret EINTR) [(rmtp, rem)] []).eff_copyins = [] := rfl

end LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
