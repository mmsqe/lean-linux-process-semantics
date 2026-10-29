/-
  * LinuxSem.Checks.Cases.Kernel.Time.Hrtimer — worked examples over nanosleep (101)

  Worked cases over `Sys.Kernel.Time.Hrtimer`, which answers to Linux
  [kernel/time/hrtimer.c]: the examples for the syscalls defined there,
  and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  What is here is the whole of
  [m_clock] — how far a sleep carries the clock is model-internal
  state that reaches no trace at all — plus the request CEILING and
  the SATURATING deadline, both of which need a request or a clock 292
  years along and so are unreachable from either side, and the
  remainder shapes no truthful kernel writes.

  Spelling.  `wmem_ts`, `clock_model` and `ts_1s` are
  [Checks/Cases/Kernel/Time/PosixTimers]'s shared fixtures, imported
  rather than duplicated, which is where the other clock code looks for
  them.  `Z` is `Int`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
  `bv_unsigned w` is `(w.toNat : Int)`, `None`/`Some` are `none`/`some`,
  `nth_error` comes from `LinuxSem.Common.RocqSpelling` (Lean's `l[n]?`),
  `mkInput` is the `SyscallInput` constructor and
  `CheckOk`/`CheckReject`/`CheckUnmodeled` are the `check_result`
  constructors.  The local `infix` notations restore the `Z` comparisons
  verbatim.

  Proofs.  The examples are NOT one-line `rfl`s: each reads a 16-byte
  request out of user memory and computes `nanosleep_clock` over a
  `Nat -> Int` cast, which the kernel cannot reduce — the `rfl` wall this
  file's own evaluator exists for, in the scaffolding section below.  The
  route, the measurements behind each step, and why
  `Checks/Cases/CheckToolkit`'s `check_unmodeled` closes none of the 29
  are recorded at the end of this file.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Kernel.Time.PosixTimers
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Time.Hrtimer
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Hrtimer
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Time.Hrtimer
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Kernel.Time.PosixTimers

namespace LinuxSem.Checks.Cases.Kernel.Time.Hrtimer

open LinuxSem.Common.RocqSpelling

/-! Rocq spellings (`bv_unsigned`, `Z_to_bv`, `zleb`/`zltb`, `nth_error`) come
    from `LinuxSem.Common.RocqSpelling`, opened above. -/

/-- `<=?` on `Z`. -/
local infix:50 " <=? " => zleb
/-- `<?` on `Z`. -/
local infix:50 " <? " => zltb

def mem_at (base : Int) (bs : List byte) : word → Option byte :=
  fun a => if (base <=? bv_unsigned a)
           then nth_error bs (Int.toNat (bv_unsigned a - base))
           else none

/-! [nanosleep(8192, rmtp)] with [req] readable at 8192.  A non-NULL
    [rmtp] is passed as 4096, which [wmem_ts] makes wholly writable. -/
def nanosleep_input (rmtp : word) (req : List byte) : SyscallInput :=
  SyscallInput.mkInput 101 [8192, rmtp, 0, 0, 0, 0] (mem_at 8192 req) wmem_ts

/-! Requests and remainders, each 16 bytes of [struct timespec]. -/
/-! tv_sec = 0, tv_nsec = 0 — no time at all. -/
def ts_zero : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-! tv_sec = 0, tv_nsec = 250000000 — a quarter second. -/
def ts_250ms : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [128, 178, 230, 14, 0, 0, 0, 0]
/-! tv_sec = 0, tv_nsec = 1000 — one microsecond. -/
def ts_1us : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [232, 3, 0, 0, 0, 0, 0, 0]
/-! tv_sec = 0, tv_nsec = 51000 — 51 microseconds, which is one
    microsecond plus the default 50us of timer slack. -/
def ts_51us : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [56, 199, 0, 0, 0, 0, 0, 0]

/-! ## The staged evaluator the examples go through

    Nothing in this section is a statement about the model; it is route B —
    the staged evaluation — made concrete for THIS file.  The three pieces,
    and why each is needed:

    * `check_syscall_nanosleep_input` resolves the 90-arm `checked_table`
      dispatch ONCE, by `rfl`.  Unlike the `sint32`-reading arms of
      `Checks.Cases.Net.Socket`, nothing here is stuck behind a `Nat -> Int` cast:
      the lookup lands on `arm_nanosleep` because `in_sysno` is the literal
      101, and `Ca_check_arm_nanosleep` is `rfl`-true.  Measured: `rfl`
      closes it in ~0.2 s.  Doing it through `simp only [check_syscall, …,
      lookup_ca]` does NOT work here — `simp` unrolls the table into the raw
      `if`-chain and then cannot decide the `Int` `==` guards — which is
      exactly the opposite of the `sint32` case.

    * `clock_after_sleep` lifts a `BitVec`-level clock equation to the
      `Model`-level one, so the examples never have to compare two `Model`s
      (there is no `DecidableEq` on `Model`, and `with_clock` is a record
      update: `with_clock t (clock_model x)` is `clock_model …`-shaped once
      the inner write is peeled, which is what makes the lift `rfl`).

    * the per-example `have`s (`read_bytes_map`, `timespec_valid_b`,
      `nanosleep_rem_ok_b`, `access_ranges_eqb`, `nanosleep_clock`) are all
      closed by `by decide`.  That is the literal evaluator this file needs:
      `read_bytes_map`'s sixteen-byte walk is `read_bytes_acc` unrolled
      sixteen times, and putting `read_bytes_map` into a `simp` set does not
      reduce it — it EXPANDS into `read_bytes_chunks`/`read_bytes_acc`/
      `word_to_nat` and the goal never closes (the negative measured by the
      earlier attempt at this file).  `by decide` computes it outright, in
      the elaborator, and leaves an ordinary proof term — no `native_decide`,
      no extra postulate.  Likewise `nanosleep_clock`'s `max` / saturating
      `min` / subtraction over the `Nat -> Int` cast: `rfl` diverges on its
      `Decidable` instances, `by decide` decides it in ~0.05 s.

    With those three in place each example is: `rw` the dispatch, state the
    literal facts, `simp only` the checker's body with them, `rfl` the rest.
    The residual after `simp only` is a tree of `if <literal> = true`, which
    the kernel DOES reduce — that is why the last step is `try rfl` and not
    another `simp`, and why `repeat' apply And.intro` / a conjunction
    splitter is not needed anywhere here: every example is a single
    `check_result` equation, not an n-way conjunction. -/

/-- The dispatch, resolved once.  `nanosleep` is 101, so the lookup in
    `checked_table` lands on `arm_nanosleep`, whose `ca_check` is
    `check_nanosleep` at `rqtp = in_arg i 0` (the 8192 in
    `nanosleep_input`) and `rmtp = in_arg i 1`.  `rfl` closes it. -/
theorem check_syscall_nanosleep_input (rmtp : word) (req : List byte)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (nanosleep_input rmtp req) eff m
      = check_nanosleep (nanosleep_input rmtp req) (Z_to_bv 64 8192) rmtp eff m := by
  rw [show check_syscall (nanosleep_input rmtp req) eff m
      = check_nanosleep (nanosleep_input rmtp req)
          (in_arg (nanosleep_input rmtp req) 0) (in_arg (nanosleep_input rmtp req) 1) eff m
      from rfl]
  rfl

/-- A clock equation at `BitVec` level, lifted to the model the example
    states.  `m_clock (clock_model x)` is `Z_to_bv 64 x` by `rfl`, and the
    outer `with_clock` overwrites the one `clock_model` already wrote, so
    the two sides meet. -/
theorem clock_after_sleep (x z : Int) (req rem : List byte)
    (h : nanosleep_clock (Z_to_bv 64 x) req rem = Z_to_bv 64 z) :
    with_clock (nanosleep_clock (m_clock (clock_model x)) req rem) (clock_model x)
      = clock_model z := by
  have hm : m_clock (clock_model x) = Z_to_bv 64 x := rfl
  rw [hm, h]
  rfl

/-- `BitVec.ofInt` round-trips through `toNat` for a non-negative `z` below
    the modulus, which the two envelope lemmas below need.  (`StateMemory`
    has the same fact as a `private` lemma; this file cannot reach it.) -/
theorem bv_unsigned_ofInt_eq {z : Int} (h0 : 0 ≤ z) (h1 : z < ((2 ^ 64 : Nat) : Int)) :
    bv_unsigned (Z_to_bv 64 z) = z := by
  show ((BitVec.ofInt 64 z).toNat : Int) = z
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-! MODEL-INTERNAL STATE.  A completed sleep carries [m_clock] forward
    by the WHOLE request: the hrtimer's soft expiry is exactly now plus
    the request and a timer never fires early, so returning 0 means at
    least that much elapsed on the very clock [m_clock] tracks.
    Nothing about [m_clock] reaches a trace, so no run sees the
    advance directly; a run feels it only indirectly, through a
    later [clock_gettime] being judged against a clock a second further
    on.  [rmtp] is NULL here, the shape a program that does not care
    what was left passes. -/
theorem nanosleep_completed_sleep_advances_the_clock :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0)
    = .CheckOk (clock_model 1000000000) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_1s []) (clock_model 0)
      = clock_model 1000000000 := clock_after_sleep 0 1000000000 ts_1s [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! MODEL-INTERNAL STATE.  With a NULL [rmtp] the interrupted arm has
    nowhere to report the remainder, so how much of the sleep elapsed is
    unknowable and the clock stays where it was.  This is the only
    accepted [nanosleep] outcome that does not move [m_clock], and the
    pair with the case above is what makes the distinction non-vacuous. -/
theorem nanosleep_null_remainder_interruption_holds_the_clock :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINTR) [] []))
      (clock_model 0)
    = .CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw]
  try rfl

/-! MODEL-INTERNAL STATE.  The interrupted arm carries [m_clock] forward
    by the request LESS the reported remainder — a second requested with
    a quarter second left is three quarters of a second elapsed.  What
    the model records is the one-sided fact the kernel actually
    establishes, and it is invisible from outside for the same reason
    the case above is. -/
theorem nanosleep_interruption_advances_by_the_difference :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0)
    = .CheckOk (clock_model 750000000) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_250ms = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_1s ts_250ms) (clock_model 0)
      = clock_model 750000000 := clock_after_sleep 0 750000000 ts_1s ts_250ms (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! MODEL-INTERNAL STATE, and the sharp one.  A remainder LARGER than
    the request is admissible, because [do_nanosleep] measures what is
    left against the HARD expiry and [hrtimer_nanosleep] sets that
    [current->timer_slack_ns] past the soft one — 50 microseconds by
    default.  So a one-microsecond sleep can report 51 microseconds
    remaining, and [nanosleep_rem_ok_b] deliberately does not bound the
    remainder by the request.  The advance is then floored at the
    clock's previous value rather than going negative: without the
    [Z.max (bv_unsigned prev)] in [nanosleep_clock] the difference would
    be -50000 and the clock would wrap to within 50 microseconds of
    2^64, turning a one-microsecond sleep into 584 years of recorded
    time.  This is the case that makes that [Z.max] non-vacuous, and no
    run can see it — the reported remainder is observable, the clock
    it moves is not. -/
theorem nanosleep_remainder_past_the_request_floors_at_zero :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_51us)] []))
      (clock_model 0)
    = .CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1us) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1us := by decide
  have htv : (!(timespec_valid_b ts_1us)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_51us = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_1us ts_51us) (clock_model 0)
      = clock_model 0 := clock_after_sleep 0 0 ts_1us ts_51us (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! The request at the ceiling, and the remainder that reaches it.
    [tv_sec = KTIME_SEC_MAX] is where [ktime_set] stops converting; one
    second below it is the control that shows it still does. -/
/-! tv_sec = 9223372036 = [KTIME_SEC_MAX], tv_nsec = 0. -/
def ts_ceiling : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-! tv_sec = 9223372035, tv_nsec = 0 — one second below the ceiling. -/
def ts_below_ceiling : List byte :=
  [3, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-! tv_sec = 2^63, tv_nsec = 0 — the first second [timespec64_valid]
    refuses, reading the field as the [s64] it is. -/
def ts_neg_sec : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 128] ++ [0, 0, 0, 0, 0, 0, 0, 0]

/-! MODEL-INTERNAL STATE.
    A request AT [KTIME_SEC_MAX] is ANSWERED, and a completed sleep
    carries [m_clock] to [Uapi.KTIME_MAX].  That is what Linux serves:
    [timespec64_to_ktime] is [ktime_set] (include/linux/ktime.h at
    v6.18.46), whose [if (unlikely(secs >= KTIME_SEC_MAX)) return
    KTIME_MAX;] hands [hrtimer_nanosleep] the end of [ktime_t] rather
    than a product, and the sleep that follows is an ordinary
    interruptible one toward that deadline.

    A real run cannot reach this from either side — issuing the call
    really would park the process for 292 years —
    so the whole of the arm is here.

    A decline here would not be conservative.  [nanosleep_rem_ok_b]
    admits a remainder with
    [tv_sec = KTIME_SEC_MAX] (the case below exhibits one), and the
    standard retry loop
    [while (nanosleep(&ts, &ts) == -1 && errno == EINTR);] — dropbear's
    auth delay — hands the remainder back as the next request.  So one
    admissible environment choice would make the NEXT call unmodeled, and
    [Equivalence.modeled] being the negation of an existential over
    resolutions, that one resolution would cost the whole program its
    [modeled] status on every input on which it slept. -/
theorem nanosleep_request_at_the_ceiling_sleeps_to_ktime_max :
    check_syscall (nanosleep_input 0 ts_ceiling)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0)
    = .CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_ceiling) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_ceiling := by decide
  have htv : (!(timespec_valid_b ts_ceiling)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_ceiling []) (clock_model 0)
      = clock_model (2 ^ 63 - 1) := clock_after_sleep 0 (2 ^ 63 - 1) ts_ceiling [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! MODEL-INTERNAL STATE — the control, and the reason the case above is
    not vacuous.  One second BELOW the ceiling [ktime_set] converts
    rather than saturating, so the recorded clock is the plain product
    9223372035 * 10^9 and not [KTIME_MAX].  The two requests are one
    second apart and the clocks they record are 1854775807 ns apart:
    that gap is exactly [ktime_set]'s early return firing, and a
    [timespec_ktime] that always converted, or always saturated, would
    fail one of the pair. -/
theorem nanosleep_request_below_the_ceiling_converts :
    check_syscall (nanosleep_input 0 ts_below_ceiling)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0)
    = .CheckOk (clock_model 9223372035000000000) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_below_ceiling) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_below_ceiling := by decide
  have htv : (!(timespec_valid_b ts_below_ceiling)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_below_ceiling []) (clock_model 0)
      = clock_model 9223372035000000000 := clock_after_sleep 0 9223372035000000000 ts_below_ceiling [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! MODEL-INTERNAL STATE — the band's TOP, and the case that stops the
    two above from being read as a claim about one value.  The band
    [ktime_set] saturates over is [[KTIME_SEC_MAX, 2^63)] of whole
    seconds, and every other case here sits at its BOTTOM: a spec that
    judged [tv_sec = KTIME_SEC_MAX] and went on declining everything
    above it would satisfy all of them, and would still cost the retry
    loop nothing, since [nanosleep_rem_ok_b] cannot spell a remainder
    past the bottom.  The largest [tv_sec] [timespec64_valid] accepts is
    2^63 - 1, one below the word that reads as negative, and it sleeps
    to [KTIME_MAX] exactly as the bottom of the band does — [ktime_set]
    tests [secs >= KTIME_SEC_MAX] and returns the same constant across
    the whole band. -/
/-! tv_sec = 2^63 - 1, tv_nsec = 999999999 — the largest request
    [timespec64_valid] accepts, and the top of the saturating band. -/
def ts_top_of_band : List byte :=
  [255, 255, 255, 255, 255, 255, 255, 127]
  ++ [255, 201, 154, 59, 0, 0, 0, 0]

theorem nanosleep_request_at_the_top_of_the_band_sleeps_to_ktime_max :
    check_syscall (nanosleep_input 0 ts_top_of_band)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model 0)
    = .CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_top_of_band) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_top_of_band := by decide
  have htv : (!(timespec_valid_b ts_top_of_band)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_top_of_band []) (clock_model 0)
      = clock_model (2 ^ 63 - 1) := clock_after_sleep 0 (2 ^ 63 - 1) ts_top_of_band [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the same rejection at
    the top of the band as at its bottom.  An -EINTR reporting a
    remainder of exactly zero is refused wherever the request sits, and
    with this pair the whole band is judged in both directions rather
    than merely answered in one. -/
theorem nanosleep_at_the_top_of_the_band_zero_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_top_of_band)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_top_of_band) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_top_of_band := by decide
  have htv : (!(timespec_valid_b ts_top_of_band)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_zero = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! MODEL-INTERNAL STATE.  The ceiling request INTERRUPTED: the clock
    moves to the deadline the kernel armed — [KTIME_MAX] — less the
    reported remainder, exactly as at any smaller request.  A quarter
    second left leaves [KTIME_MAX - 250000000]. -/
theorem nanosleep_request_at_the_ceiling_interrupted :
    check_syscall (nanosleep_input 4096 ts_ceiling)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model 0)
    = .CheckOk (clock_model 9223372036604775807) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_ceiling) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_ceiling := by decide
  have htv : (!(timespec_valid_b ts_ceiling)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_250ms = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_ceiling ts_250ms) (clock_model 0)
      = clock_model 9223372036604775807 := clock_after_sleep 0 9223372036604775807 ts_ceiling ts_250ms (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and this is the
    REJECTION a decline at the ceiling would cost: a spec that answered
    [CheckUnmodeled] there for EVERY effect would refuse nothing.  The
    -EINTR reporting a remainder of exactly zero is REFUSED, as it is at
    every other request. -/
theorem nanosleep_at_the_ceiling_zero_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_ceiling)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_ceiling) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_ceiling := by decide
  have htv : (!(timespec_valid_b ts_ceiling)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_zero = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the other half of the
    band, and the boundary the ceiling arm must NOT move.  One
    second past the ceiling is still inside [timespec64_valid]; 2^63
    seconds is not, because [tv_sec] is signed and that word reads as
    negative.  So the answer there is -EINVAL and not a sleep, and
    judging the ceiling does not widen the band that answers.  Without
    this case a [timespec_valid_b] weakened alongside the gate would go
    unnoticed. -/
theorem nanosleep_request_at_two_to_the_63_is_einval :
    check_syscall (nanosleep_input 4096 ts_neg_sec)
      (with_copyins [(8192, 16)] (mkEffect (errno_ret EINVAL) [] []))
      (clock_model 0)
    = .CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_neg_sec) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_neg_sec := by decide
  have htv : (!(timespec_valid_b ts_neg_sec)) = true := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder AT the
    ceiling, which is the value that would poison the next call if a
    request at the ceiling declined.
    [nanosleep_rem_ok_b] admits it: 9223372036 * 10^9 is 854775808 ns
    below [CLOCK_NS_ENVELOPE], so the envelope conjunct passes, and the
    other three do too.  The clock does not move — the request was a
    second and the remainder is 292 years, so the difference is negative
    and [Z.max prev] holds it — which is the [nanosleep_clock] floor
    doing its job at the top of the range rather than the bottom.

    Read this case together with the request cases above: THIS is the
    remainder, THAT is what the next call does with it. -/
theorem nanosleep_remainder_at_the_ceiling_admitted :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_ceiling)] []))
      (clock_model 0)
    = .CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_ceiling = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_1s ts_ceiling) (clock_model 0)
      = clock_model 0 := clock_after_sleep 0 0 ts_1s ts_ceiling (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! UNIVERSALLY QUANTIFIED, and the pinning test for the retry loop.
    EVERY remainder this spec may write is a request the same spec
    JUDGES: given the destination the loop reuses, no [rem] that
    [nanosleep_rem_ok_b] admits can make the next call decline.  The
    two hypotheses are the loop's own, not extra assumptions —
    [while (nanosleep(&ts, &ts) == -1 && errno == EINTR);] passes the
    remainder back as the request, and it passes the same pointer as
    both, so the destination it hands the second call is one the first
    call already found writable.  The disjunction covers the other
    spelling, where [rmtp] is NULL and no remainder is reported at all.

    THE STATEMENT IS A NON-DECLINE, not an acceptance, on purpose: it
    must hold for EVERY effect, and most effects at a given input are
    rejected.  What it rules out is the third verdict — the one that
    escapes through [Equivalence]'s unmodeled arm and takes the whole
    program's [modeled] status with it.

    Nothing else in the tree states this.  The concrete cases above pin
    one remainder value and one request value; this pins that no value
    in between them, or beyond, reopens the hole. -/
/-! [bytes_le_to_Z] never decodes to a negative number, which is what
    turns [nanosleep_rem_ok_b]'s bound on the TOTAL into a bound on
    [tv_sec] alone.  [Common.PropExec] proves the same fact, and is not
    in this file's import closure. -/

theorem bytes_le_to_Z_nonneg' (bs : List byte) : (0 : Int) ≤ bytes_le_to_Z bs :=
  Int.natCast_nonneg _


theorem timespec_ns_nonneg (bs : List byte) : (0 : Int) ≤ timespec_ns bs := by
  unfold timespec_ns tv_sec_of tv_frac_of
  exact Int.add_nonneg
    (Int.mul_nonneg (Int.natCast_nonneg _) (by decide))
    (Int.natCast_nonneg _)


theorem timespec_ktime_nonneg (bs : List byte) : (0 : Int) ≤ timespec_ktime bs := by
  unfold timespec_ktime
  split
  · exact timespec_ns_nonneg bs
  · unfold KTIME_MAX
    decide

/-! UNIVERSALLY QUANTIFIED, and the machine-checkable proxy for the one
    thing [nanosleep_clock]'s prose claims: that what it records is a
    LOWER bound on the real [CLOCK_MONOTONIC].  The full statement is
    not expressible here — the real clock is not a term in this
    development, and the argument that a timer never fires before its
    soft expiry is kernel prose, not a term here.  What IS expressible is the
    model-side half of it, and this is that half: the recorded clock
    never runs past the deadline the kernel armed, which
    [nanosleep_clock] computes as [Z.min (prev + timespec_ktime req)
    KTIME_MAX].

    Both saturating arms land on that bound, from a clock the
    model may have anywhere below the envelope, so it is worth having
    checked rather than argued.  It is also the step the spec's
    "the FIRST saturation is not load-bearing" paragraph rests on:
    NOTHING of the shape [Z.min _ KTIME_MAX] exceeds [KTIME_MAX], which
    is the armed deadline throughout the saturating band, so reading the
    request as a plain product would still be sound — it would just be
    less exact.

    The remaining gap, and it is a real one: this is a fact about one
    call, not an invariant of the model.  Nothing in the tree says
    every arm preserves [m_clock < CLOCK_NS_ENVELOPE]; the two arms
    that move the clock at all are this one and
    [Kernel.Time.PosixTimers.clock_gettime_spec], and each argues its
    own bound in prose.  No model invariant states it. -/
theorem nanosleep_clock_at_most_the_armed_deadline (prev : word) (req rem : List byte)
    (hprev : bv_unsigned prev ≤ KTIME_MAX) :
    bv_unsigned (nanosleep_clock prev req rem)
      ≤ min (bv_unsigned prev + timespec_ktime req) KTIME_MAX := by
  have hk : (0 : Int) ≤ timespec_ktime req := timespec_ktime_nonneg req
  have hn : (0 : Int) ≤ timespec_ns rem := timespec_ns_nonneg rem
  have hprev0 : (0 : Int) ≤ bv_unsigned prev := Int.natCast_nonneg _
  have h0 : (0 : Int) ≤ max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem) := by omega
  have h64 : max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem)
      < ((2 ^ 64 : Nat) : Int) := by
    have hK : KTIME_MAX = 2 ^ 63 - 1 := rfl
    have h64' : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by simp
    omega
  have hval : bv_unsigned (nanosleep_clock prev req rem)
      = max (bv_unsigned prev)
          (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem) := by
    unfold nanosleep_clock
    exact bv_unsigned_ofInt_eq h0 h64
  rw [hval]
  omega

/-! UNIVERSALLY QUANTIFIED — the corollary [nanosleep_spec] needs to
    carry no envelope gate of its own.  A clock inside the band
    [Kernel.Time.PosixTimers.clock_gettime_spec] ANSWERS in is still
    inside it after any sleep, whatever the request and whatever the
    remainder, because the deadline is clamped at [KTIME_MAX] and that
    is [CLOCK_NS_ENVELOPE - 1].  Without this a sleep could park
    [m_clock] where the very next monotonic read declines; the
    saturating deadline avoids that trap by one nanosecond. -/
theorem nanosleep_clock_under_the_envelope (prev : word) (req rem : List byte)
    (hprev : bv_unsigned prev < CLOCK_NS_ENVELOPE) :
    bv_unsigned (nanosleep_clock prev req rem) < CLOCK_NS_ENVELOPE := by
  have hk : (0 : Int) ≤ timespec_ktime req := timespec_ktime_nonneg req
  have hn : (0 : Int) ≤ timespec_ns rem := timespec_ns_nonneg rem
  have hprev0 : (0 : Int) ≤ bv_unsigned prev := Int.natCast_nonneg _
  have h0 : (0 : Int) ≤ max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem) := by omega
  have h64 : max (bv_unsigned prev)
      (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem)
      < ((2 ^ 64 : Nat) : Int) := by
    have henv : CLOCK_NS_ENVELOPE = 2 ^ 63 := rfl
    have h64' : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by simp
    have hK : KTIME_MAX = CLOCK_NS_ENVELOPE - 1 := rfl
    omega
  have hval : bv_unsigned (nanosleep_clock prev req rem)
      = max (bv_unsigned prev)
          (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem) := by
    unfold nanosleep_clock
    exact bv_unsigned_ofInt_eq h0 h64
  rw [hval]
  have hK : KTIME_MAX = CLOCK_NS_ENVELOPE - 1 := rfl
  omega

theorem nanosleep_admissible_remainder_is_a_judged_request (i : SyscallInput)
    (rqtp rmtp : word) (eff : SyscallEffect) (m : Model) (rem : List byte)
    (hread : read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) = some rem)
    (_hrem : nanosleep_rem_ok_b rem = true)
    (hwm : w_is0 rmtp = true ∨ read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) ≠ none) :
    check_nanosleep i rqtp rmtp eff m ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro h
  unfold check_nanosleep at h
  rw [hread] at h
  dsimp only at h
  by_cases hv : (!(timespec_valid_b rem)) = true
  · rw [ite_eq_left hv] at h
    exact absurd h (check_ret_only_copyins_no_unmodeled _ _ _ _ _)
  · rw [ite_eq_right hv] at h
    by_cases hw : w_is0 rmtp = true
    · rw [ite_eq_left hw] at h
      cases ws <;> cases zs <;> cases us <;> cases cs
      repeat' first
        | dsimp only at h
        | unfold check_copyins at h
        | split at h
        | cases h
    · rw [ite_eq_right hw] at h
      rcases hwm with h0 | h0
      · exact absurd h0 hw
      · cases hwmem : read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
        | none => exact h0 hwmem
        | some bs =>
          rw [hwmem] at h
          try dsimp only at h
          cases ws <;> cases zs <;> cases us <;> cases cs
          repeat' first
            | dsimp only at h
            | unfold check_copyins at h
            | split at h
            | cases h

/-! MODEL-INTERNAL STATE.  A
    clock already within a second of the top of [ktime_t]'s range
    ANSWERS a one-second sleep, recording the saturated deadline
    [Uapi.KTIME_MAX] rather than a sum the type cannot hold.  That is
    what Linux does: [__hrtimer_start_range_ns] converts the relative
    request with [ktime_add_safe], which replaces an overflowing sum
    with [ktime_set(KTIME_SEC_MAX, 0)] — [KTIME_MAX] — and sleeps to
    THAT deadline rather than reporting an error.

    A decline here would not be
    merely conservative: [PosixTimers.clock_gettime_spec] records
    whatever monotonic reading the ENVIRONMENT chooses, bounded only by
    [timespec_ok_b]'s [< 2^63], so a single [clock_gettime] from
    [init_model] could put [m_clock] here and the next sleep of one
    nanosecond would decline.  [Equivalence.modeled] is the negation of an
    existential over resolutions, so that one resolution would cost the
    whole program its [modeled] status — for ANY program that reads the
    monotonic clock and then sleeps, which is dropbear's shape.

    Note the recorded value is [2^63 - 1] and not [2^63]: the
    saturation constant is [KTIME_MAX], because [ktime_set]'s early
    return tests [secs >= KTIME_SEC_MAX] and so fires on the very value
    [ktime_add_safe] passes it.  One nanosecond, and it is the
    nanosecond that keeps [m_clock] inside the band
    [clock_gettime_spec] answers in. -/
theorem nanosleep_clock_near_envelope_clamps :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 1000000000))
    = .CheckOk (clock_model (2 ^ 63 - 1)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model (2 ^ 63 - 1000000000))) ts_1s []) (clock_model (2 ^ 63 - 1000000000))
      = clock_model (2 ^ 63 - 1) := clock_after_sleep (2 ^ 63 - 1000000000) (2 ^ 63 - 1) ts_1s [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! MODEL-INTERNAL STATE — the control for the case above, and the
    reason it is not vacuous.  The same one-second sleep against a
    clock two seconds below the ceiling does NOT clamp: the sum fits,
    so the recorded value is the plain [prev + request].  Without this
    pair a [nanosleep_clock] that clamped everything to [KTIME_MAX]
    would satisfy the case above. -/
theorem nanosleep_clock_below_the_ceiling_does_not_clamp :
    check_syscall (nanosleep_input 0 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [] []))
      (clock_model (2 ^ 63 - 2000000000))
    = .CheckOk (clock_model (2 ^ 63 - 1000000000)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hbv0 : bv_eqb (0 : word) (BitVec.ofInt 64 0) = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model (2 ^ 63 - 2000000000))) ts_1s []) (clock_model (2 ^ 63 - 2000000000))
      = clock_model (2 ^ 63 - 1000000000) := clock_after_sleep (2 ^ 63 - 2000000000) (2 ^ 63 - 1000000000) ts_1s [] (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hbv0, hclk]
  try rfl

/-! MODEL-INTERNAL STATE, and the case that pins WHERE the remainder is
    subtracted.  A saturating one-second sleep interrupted with one
    microsecond left records [KTIME_MAX - 1000], not [prev + request -
    remainder].  The order matters because the two disagree by more
    than the whole envelope here.  A [nanosleep_clock] that subtracted
    BEFORE clamping would compute [Z.min (prev + 10^9 - 1000)
    KTIME_MAX], which is [KTIME_MAX] outright, losing the microsecond.
    One that did not clamp at all would record
    [prev + 10^9 - 1000 = 2^63 + 999997000] — no wrap, since that is
    well under 2^64, but ABOVE [CLOCK_NS_ENVELOPE], which is the band
    [PosixTimers.clock_gettime_spec] declines in.  So the unclamped
    spelling would put the clock somewhere the very next monotonic read
    is [unmodeled], reintroducing one call later exactly the existential
    decline the clamp exists to prevent.  Keeping [m_clock]
    inside [clock_gettime]'s answering band is the clamp's job as much
    as faithfulness is.

    The soundness argument is [nanosleep_spec]'s: the kernel armed
    [node.expires] at the saturated deadline, [hrtimer_expires_remaining]
    measures the remainder against THAT, so the wake time is the
    saturated deadline less the remainder — never [prev + request] less
    it, because the sleep the kernel ran was shorter than the one asked
    for. -/
theorem nanosleep_saturated_deadline_less_the_remainder :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_1us)] []))
      (clock_model (2 ^ 63 - 2000))
    = .CheckOk (clock_model (2 ^ 63 - 1001)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_1us = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model (2 ^ 63 - 2000))) ts_1s ts_1us) (clock_model (2 ^ 63 - 2000))
      = clock_model (2 ^ 63 - 1001) := clock_after_sleep (2 ^ 63 - 2000) (2 ^ 63 - 1001) ts_1s ts_1us (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! MODEL-INTERNAL STATE — the [Z.max prev] floor, in its SECOND form.
    The floor already had a case above, where a remainder exceeding the
    request drove the difference negative.  This is the other way it
    can fire, and it needs the clamp to exist at all: a saturating
    sleep interrupted with a quarter second left leaves
    [KTIME_MAX - 250000000], which is BELOW a clock sitting 1000 ns
    from the ceiling.  The clock holds where it was rather than
    stepping back a quarter second.

    Nothing else in the tree separates [Z.max prev] from [Z.max 0]
    applied to the subtraction: with the clock at 0 the two agree, and
    only a clock near the ceiling makes [KTIME_MAX - rem] fall below
    [prev]. -/
theorem nanosleep_saturated_deadline_never_steps_the_clock_back :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000))
    = .CheckOk (clock_model (2 ^ 63 - 1000)) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_250ms = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model (2 ^ 63 - 1000))) ts_1s ts_250ms) (clock_model (2 ^ 63 - 1000))
      = clock_model (2 ^ 63 - 1000) := clock_after_sleep (2 ^ 63 - 1000) (2 ^ 63 - 1000) ts_1s ts_250ms (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and this is the
    REJECTION a decline near the ceiling would cost.  A spec that
    answered [CheckUnmodeled] there for EVERY effect would refuse
    nothing: a lying kernel's impossible answers would be declined
    rather than rejected, and a decline is not a rejection — it admits
    the step under [Equivalence]'s unmodeled escape instead of ruling it
    out.  With the clamp in place the same [-EINTR] reporting a
    remainder of exactly zero is REFUSED at a clock near the ceiling,
    exactly as it is at a clock of 0.

    So the clamp gives the model reach in BOTH directions: it models a
    trace Linux really produces, and it rejects impossible traces in
    this band. -/
theorem nanosleep_near_the_ceiling_zero_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model (2 ^ 63 - 1000000000))
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_zero = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror of the
    case above, at the ceiling.  A completed sleep that also writes a
    remainder is refused near the envelope too.  Together the two pin
    that the band near the ceiling is fully judged rather
    than waved through. -/
theorem nanosleep_near_the_ceiling_completed_sleep_with_a_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model (2 ^ 63 - 1000000000))
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hbv0 : bv_eqb (0 : word) (errno_ret EINTR) = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hbv0]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  An -EINTR reporting
    a remainder of exactly zero is REFUSED.  [do_nanosleep] computes
    what is left and, when that is at or below zero, returns 0 having
    written nothing — the deadline has passed, so the call is a
    completed sleep and is reported as one.  A remainder of [{0, 0}] is
    therefore a shape no kernel produces, and [nanosleep_rem_ok_b]'s
    strict positivity is what refuses it. -/
theorem nanosleep_zero_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_zero)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_zero = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
    ENVELOPE conjunct, which nothing else reaches.  A remainder of
    9223372037 seconds is normalized ([tv_nsec = 0]), sixteen bytes
    long and strictly positive, so it fails [nanosleep_rem_ok_b]'s
    fourth conjunct ALONE and the rejection attributes to it. -/
def ts_over_envelope : List byte :=   /- 9223372037 s: past 2^63 ns -/
  [5, 125, 193, 37, 2, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]

theorem nanosleep_remainder_past_the_envelope_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_over_envelope)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_over_envelope = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVELOPE CONJUNCT'S BOUNDARY, one nanosecond either side.
    [ts_over_envelope] above sits a whole second past the boundary and
    so does not locate it; the pair below does.

    [KTIME_MAX] nanoseconds — 9223372036 s and 854775807 ns — is the
    LARGEST remainder [nanosleep_rem_ok_b] admits, and the request here
    is a microsecond, so the difference is 292 years negative and
    [Z.max prev] holds the clock at 0. -/
def ts_ktime_max : List byte :=      /- 9223372036 s, 854775807 ns -/
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [255, 215, 242, 50, 0, 0, 0, 0]

theorem nanosleep_remainder_of_exactly_ktime_max_admitted :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_ktime_max)] []))
      (clock_model 0)
    = .CheckOk (clock_model 0) [] := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1us) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1us := by decide
  have htv : (!(timespec_valid_b ts_1us)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_ktime_max = true := by decide
  have hclk : with_clock (nanosleep_clock (m_clock (clock_model 0)) ts_1us ts_ktime_max) (clock_model 0)
      = clock_model 0 := clock_after_sleep 0 0 ts_1us ts_ktime_max (by decide)
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem, hclk]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — ONE NANOSECOND
    further.  9223372036 s and 854775808 ns is 2^63 exactly, which is
    [CLOCK_NS_ENVELOPE] and not below it, so the fourth conjunct's
    strict [<] refuses it and the other three still pass.  Without this
    twin the case above would be satisfied by a bound of [<=] as
    happily as by [<]. -/
def ts_at_envelope : List byte :=    /- 9223372036 s, 854775808 ns -/
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 216, 242, 50, 0, 0, 0, 0]

theorem nanosleep_remainder_of_exactly_the_envelope_rejected :
    check_syscall (nanosleep_input 4096 ts_1us)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_at_envelope)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1us) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1us := by decide
  have htv : (!(timespec_valid_b ts_1us)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_at_envelope = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the remainder's
    LENGTH conjunct, on its own.  Eight bytes decoding to
    [tv_sec = 1]: [tv_frac_of] of the empty tail is 0, so the reading
    is normalized, and [timespec_ns] is 10^9, positive and far under
    the envelope.  Only the length is wrong.

    This is the shape a truncating kernel would produce. -/
def ts_half : List byte :=            /- 8 bytes: tv_sec = 1 -/
  [1, 0, 0, 0, 0, 0, 0, 0]

theorem nanosleep_half_a_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)]
       (mkEffect (errno_ret EINTR) [(4096, ts_half)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hrem : nanosleep_rem_ok_b ts_half = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hrem]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the mirror.  A
    completed sleep that ALSO writes a remainder is refused.  The kernel
    reaches [nanosleep_copyout] only on the interrupted path, so a
    return of 0 and a write at [rmtp] cannot both happen; admitting the
    pair would let a lying kernel move [m_clock] by the whole request
    while claiming a remainder against it.  The remainder written here
    is a PERFECTLY VALID one, which is what makes the case attribute:
    the only thing wrong with this effect is that a completed sleep
    carries it. -/
theorem nanosleep_completed_sleep_with_a_remainder_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(8192, 16)] (mkEffect 0 [(4096, ts_250ms)] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(8192, 16)] [(Z_to_bv 64 8192, 16)] = true := by decide
  have hbv0 : bv_eqb (0 : word) (errno_ret EINTR) = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc, hbv0]
  try rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the LEDGER, which
    every case above carries and none of them pins.  The kernel reads
    the request with [get_timespec64] before it decides anything, so
    every outcome [nanosleep] can reach has already consumed those
    sixteen bytes at [rqtp].  An effect that is otherwise the accepted
    completed sleep, but claims to have decided without reading the
    request, describes a kernel that cannot exist, and is refused.

    Without this case the [record_copyins] in [nanosleep_spec] would be
    unfalsifiable from the example side: every other case here would
    still pass with the ledger dropped from both the spec and the
    acceptor. -/
theorem nanosleep_missing_copyin_rejected :
    check_syscall (nanosleep_input 0 ts_1s)
      (mkEffect 0 [] [])
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 (0 : word) = true := by decide
  have hacc : access_ranges_eqb [] [(Z_to_bv 64 8192, 16)] = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hacc]
  try rfl

/-! And the ledger has to name the REQUEST.  Sixteen bytes recorded at
    [rmtp] — the remainder destination, which [nanosleep] writes and
    never reads — is the right width at the wrong address, and is
    refused for that alone.  This is what separates an acceptor that
    compares the whole range from one that only counts bytes. -/
theorem nanosleep_copyin_at_the_wrong_pointer_rejected :
    check_syscall (nanosleep_input 4096 ts_1s)
      (with_copyins [(4096, 16)] (mkEffect 0 [] []))
      (clock_model 0)
    = .CheckReject := by
  rw [check_syscall_nanosleep_input]
  have hread : read_bytes_map (mem_at 8192 ts_1s) (Z_to_bv 64 8192)
      (BitVec.ofInt 64 16) = some ts_1s := by decide
  have htv : (!(timespec_valid_b ts_1s)) = false := by decide
  have hw : w_is0 ((4096 : word)) = false := by decide
  have hwm : read_bytes_map wmem_ts ((4096 : word)) (BitVec.ofInt 64 16)
      = some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  have hacc : access_ranges_eqb [(4096, 16)] [(Z_to_bv 64 8192, 16)] = false := by decide
  simp only [check_nanosleep, nanosleep_input, with_copyins,
    check_copyins, check_ret_only_copyins, check_ret_only, clear_copyins,
    hread, htv, hw, hwm, hacc]
  try rfl


/-! ## PROVED — nothing deferred in this file any more

    All 26 worked examples above and the three UNIVERSALLY QUANTIFIED lemmas
    between them are proved.  The route, and what it cost, is recorded here
    because an earlier version of this file deferred them and argued they
    could not be reached; the two obstacles it named were real, but each has
    a measured answer.

    (1) THE 16-BYTE READS.  `check_nanosleep` fetches the request with
    `read_bytes_map (in_mem i) rqtp 16`.  Putting `read_bytes_map` into a
    `simp` set does not reduce it — it EXPANDS into `read_bytes_chunks` /
    `read_bytes_acc` / `word_to_nat` and leaves the goal as that chunk chain,
    which is the negative the earlier attempt measured.  Going the other way
    works: `read_bytes_map (mem_at 8192 <req>) (Z_to_bv 64 8192) 16 = some
    <req>` is closed by `by decide` for each of the six literal requests, in
    the elaborator, as an ordinary proof term.  Sixteen unrollings of
    `read_bytes_acc` with `mem_at`'s `if` at each address is exactly the
    computation `decide` performs.

    (2) `nanosleep_clock`.  Its `max` / saturating `min` / subtraction over
    the `Nat -> Int` cast is the divergent `Decidable` shape (see the
    `rfl`-wall note above), so `rfl` cannot see it.  `by decide` decides it — measured
    ~0.05 s per concrete instance, including the 2^63-sized ones — and then
    `clock_after_sleep` lifts the `BitVec` equation to the `Model` equation
    the examples state (there is no `DecidableEq` on `Model`, so this lift is
    a `rw`, not a `decide`).

    (3) THE DISPATCH.  `check_syscall_nanosleep_input` resolves the 90-arm
    `checked_table` lookup by `rfl`, in ~0.2 s.  Note that this is the
    opposite of `Cases/Net/Socket`'s `sint32` arms: there, `simp` had to
    resolve the table because `rfl`/`whnf` ran into the stuck `sint32`
    `ite`; here nothing in the dispatch reads a value through an `Int` cast,
    and `simp only [check_syscall, …, lookup_ca]` instead UNROLLS the table
    into its raw `if`-chain and cannot decide the `Int` `==` guards.

    ROUTE A (`Checks/Cases/CheckToolkit.lean`'s `check_unmodeled`) WAS TRIED
    on all 26 examples and on the three lemmas, and closes none of them —
    the reason is structural, not a weakness of the toolkit.  Fifteen of the
    examples are `= .CheckOk m evs` and eleven are `= .CheckReject`;
    `check_unmodeled`'s bridge `isUnmodeledR_eq_true` only ever concludes
    `r = .CheckUnmodeled`, so on either shape its `_` stays unsolved and the
    attempt dies with "Expected type must not contain metavariables".  The
    three lemmas are UNIVERSALLY QUANTIFIED, so `by decide` — Route A's whole
    engine — has nothing to compute.  What this file needed was Route B's
    staged evaluation, which is what it uses: no `CheckUnmodeled` verdict is
    asserted anywhere in this file, so the constructor test has no target.

    NO INVARIANT IS CLAIMED.  `nanosleep_clock_under_the_envelope` is a
    statement about ONE call, not an invariant of the model: nothing in this
    tree says every arm preserves `m_clock < CLOCK_NS_ENVELOPE`, and the two
    arms that move the clock at all (`nanosleep_spec` and
    `Kernel.Time.PosixTimers.clock_gettime_spec`) each argue their own bound
    in prose.  That gap is unchanged by this file and is stated where the
    lemma is.
-/

end LinuxSem.Checks.Cases.Kernel.Time.Hrtimer
