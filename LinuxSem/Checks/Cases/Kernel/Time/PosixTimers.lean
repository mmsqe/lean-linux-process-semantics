/-
  * LinuxSem.Checks.Cases.Kernel.Time.PosixTimers — worked examples over clock_gettime (113)

  Worked cases over `Sys.Kernel.Time.PosixTimers`, which answers to Linux
  [kernel/time/posix-timers.c]: the examples for the syscalls defined
  there, and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  What is here is the model's own notion of
  a clock: [m_clock] is internal state no observation reveals, and no
  kernel can be asked to run CLOCK_MONOTONIC backwards or to stand still
  on demand.  For CLOCK_REALTIME what is here is the mirror image — the
  ABSENCE of a cross-call constraint, which shows up as the cases the
  monotonic arm rejects and this one admits.

  Spelling.  `Z` is `Int`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
  `bv_unsigned w` is `(w.toNat : Int)`, `Some`/`None` are `some`/`none`,
  `mkInput` is the `SyscallInput` constructor,
  `CheckOk`/`CheckReject`/`CheckUnmodeled` are the `check_result`
  constructors, and `mkEffect r ws zs` is `State.mkEffect`.  The two
  local `infix` notations below restore the `Z` comparisons verbatim
  (`Z.leb` is `zleb`, `Z.ltb` is `zltb`), so the statements read as they
  are written.

  Proofs.  The one-liners on the CLOCK_REALTIME (0),
  CLOCK_PROCESS_CPUTIME_ID (2) and per-call arms are `rfl` — kernel
  reduction — because `check_result` carries a `Model` and so has no
  `DecidableEq`, which rules out `decide`.  The three QUANTIFIED lemmas
  are ordinary tactic proofs: `rw [H]` for a rewrite, `try dsimp only`
  for the reduction of a `let`, and `cases …` with `nomatch` in the
  impossible arm.  The two state-preservation lemmas read the checker's
  one-write arm back with `split` (the same shape
  `Checks.Sys.Kernel.Time.PosixTimers` uses), and the accepted arm is the
  only `CheckOk` in that arm, which is what makes them one-liners after
  the split.

  Why only the monotonic arm: it is the only arm that reads `m_clock`,
  and every test it builds on that reading (`!decide ((m_clock m).toNat :
  Int < CLOCK_NS_ENVELOPE)`, `timespec_ok_b`, `timespec_ns`) goes through
  an `Int.ofNat` of a `BitVec.toNat`, which `Int.decLt`/`Int.decEq`
  cannot unwind under `whnf`.  `decide` computes the same facts fine,
  which is why every one of them is discharged with `by decide` in the
  proofs below.  The eight CLOCK_MONOTONIC cases go through the two
  routes documented under "The CLOCK_MONOTONIC cases" below —
  `check_unmodeled` for the `CheckUnmodeled` one and `clock_monotonic` for
  the seven payload ones — and none of them is weakened.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.CheckToolkit
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Time.PosixTimers
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Time

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Kernel.Time.PosixTimers

/-! ## The prelude's abbreviations, restored

    Each is a transparent alias, so no statement below changes meaning.
    (The same block heads every `Cases/Kernel/` file of this tree.) -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-- `=?` on `Z`. -/
local infix:50 " =? " => BEq.beq
/-- `<=?` on `Z`. -/
local infix:50 " <=? " => zleb
/-- `<?` on `Z`. -/
local infix:50 " <? " => zltb

/-! Sixteen writable bytes at 4096, and nothing else. -/
def wmem_ts : word → Option byte :=
  fun a => if ((4096 <=? bv_unsigned a) && (bv_unsigned a <? 4112))
           then some 0 else none

def clock_input (clkid : word) : SyscallInput :=
  SyscallInput.mkInput 113 [clkid, 4096, 0, 0, 0, 0] (fun _ => none) wmem_ts

/-! A model whose monotonic clock reads [t] nanoseconds.  [mkModel]
    starts the clock at its origin, so the reading is set on top of one. -/
def clock_model (t : Int) : Model :=
  with_clock (Z_to_bv 64 t)
    (mkModel [] (mkVmMaps [] [] 0 0 demo_limit) IEof [] none none none)

/-! One second, as the kernel would write it: tv_sec = 1, tv_nsec = 0. -/
def ts_1s : List byte :=
  [1, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-! Two seconds. -/
def ts_2s : List byte :=
  [2, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]
/-! One nanosecond BEFORE one second: tv_sec = 0, tv_nsec = 999999999. -/
def ts_1s_minus : List byte :=
  [0, 0, 0, 0, 0, 0, 0, 0] ++ [255, 201, 154, 59, 0, 0, 0, 0]
/-! tv_sec = 1 with an UNNORMALIZED tv_nsec of exactly 10^9. -/
def ts_denorm : List byte :=
  [1, 0, 0, 0, 0, 0, 0, 0] ++ [0, 202, 154, 59, 0, 0, 0, 0]

/-! UNIVERSALLY QUANTIFIED.  Every clock id but the SEVEN modeled ones
    declines, whatever the destination, the effect or the model — so no
    future arm can quietly start answering for CLOCK_THREAD_CPUTIME_ID,
    CLOCK_TAI or the alarm variants without this failing.  The id is
    tested before anything else, which is why no hypothesis about [tp]
    or [eff] is needed. -/

theorem clock_gettime_only_the_modeled_clocks (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model)
    (Hrt : (bv_unsigned clkid =? CLOCK_REALTIME) = false)
    (Hraw : (bv_unsigned clkid =? CLOCK_MONOTONIC_RAW) = false)
    (Hrtc : (bv_unsigned clkid =? CLOCK_REALTIME_COARSE) = false)
    (Hmc : (bv_unsigned clkid =? CLOCK_MONOTONIC_COARSE) = false)
    (Hbt : (bv_unsigned clkid =? CLOCK_BOOTTIME) = false)
    (Hcp : (bv_unsigned clkid =? CLOCK_PROCESS_CPUTIME_ID) = false)
    (Hmono : (bv_unsigned clkid =? CLOCK_MONOTONIC) = false) :
    check_clock_gettime i clkid tp eff m = .CheckUnmodeled := by
  unfold check_clock_gettime clockid_percall_b
  rw [Hrt, Hraw, Hrtc, Hmc, Hbt, Hcp, Hmono]
  rfl

/-! MODEL-INTERNAL STATE.  A clock already at the top of [ktime_t]'s
    range declines rather than inventing a reading.  Unreachable from
    [init_model] — the origin is 0 and every arm stays under the
    envelope — but [Progress.receptive] quantifies over arbitrary model
    states, so the arm has to be there and has to be right. -/

/-! ### The CLOCK_MONOTONIC cases: the `rfl` wall, MEASURED, and how it was passed

    The eight examples below all reach the MONOTONIC arm, and
    that arm is the only one in this checker the kernel cannot reduce.
    Its guard is

      `else if !decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)`

    and that proposition is `Int.decLt` at an `Int.ofNat` of a
    `BitVec.toNat` — the divergent shape.
    MEASURED: `rfl` on `clock_backwards_reading_rejected` reports
    "maximum recursion depth has been reached" (at 10^7 it overflows the
    stack), while `by decide` closes the same fact in milliseconds.
    `timespec_ok_b` and `timespec_ns` are the same class: they read
    `tv_sec`/`tv_nsec` through `bv_unsigned`, i.e. through that same cast.

    The other three arms do NOT hit it, which is why the CLOCK_REALTIME
    (0), CLOCK_PROCESS_CPUTIME_ID (2) and per-call cases below are `rfl`
    one-liners: none of them consults `m_clock`, so no test of theirs
    touches the shape the kernel cannot unwind.

    Two routes, the same two `Checks/Cases/Net/Socket.lean` documents,
    close the eight.

    ROUTE A (the constructor test) — `check_unmodeled`, from
    `Checks/Cases/CheckToolkit.lean`.  `isUnmodeledR` projects a
    `check_result` to a `Bool` on CONSTRUCTORS only, so `by decide` can
    compute it (0.2-0.5 s), and `isUnmodeledR_eq_true` reflects that back
    into the equality the kernel cannot see.  It settles
    `clock_at_envelope_declines` without ever naming the model.

    ROUTE B (the staged evaluation) — `clock_monotonic` below, for the
    seven cases that answer `CheckOk` or `CheckReject`.  Route A cannot
    reach a payload (`check_result` has no `DecidableEq`: `Model`'s
    `IoState` holds functions), so the goal is made to REDUCE instead:
    `check_syscall_clock_gettime` takes the 90-arm `checked_table`
    dispatch out of the way (the kernel resolves `lookup_ca checked_table
    113` by `rfl`, and `Dispatch.ca_check_arm_clock_gettime` reads the arm
    back), then the checker is unfolded and every branch test the kernel
    cannot decide is BOUND BY NAME with `by decide` and rewritten with
    `ite_eq_left`/`ite_eq_right`.  What is left is an `if`-chain on literals, which
    the kernel closes — and for the `CheckOk` cases the recorded reading
    is then normalised (`timespec_ns ts_1s = 1000000000`, by `decide`) so
    that `with_clock` puts the same clock back and `rfl` finishes.

    Nothing below is `native_decide`: every proof is an ordinary proof
    term, so no extra postulate enters the library.

    The macro bodies are a single parenthesised `;`-separated sequence on
    purpose — a `(tactic| …)` quotation in this toolchain parses ONE
    tactic, so a multi-line sequence without the parentheses and the
    semicolons does not parse — and each fact is bound with `have` rather
    than inlined into `rw [ … ]`, because an antiquotation inside a `rw`
    bracket does not parse while one in a `have`'s type does. -/

/-- The dispatch, resolved once: sysno 113 is
    `Dispatch.arm_clock_gettime`, and the arm passes
    `clockid32 (in_arg i 0)` and `in_arg i 1` to the checker.  The kernel
    resolves the table lookup because `lookup_ca` at a literal number is a
    closed computation over arms whose `ca_no` is `rfl`-known. -/
theorem check_syscall_clock_gettime (clkid : word) (eff : SyscallEffect) (m : Model) :
    check_syscall (clock_input clkid) eff m
      = check_clock_gettime (clock_input clkid) (clockid32 clkid) (4096 : word) eff m := by
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, clock_input]
  exact Sys.Dispatch.ca_check_arm_clock_gettime _ _ _

/-- Route B, up to the monotonic arm's one-write test: the three clock-id
    tests, the `m_clock` envelope test and the destination-mapping test
    are all discharged, leaving

      `if bv_eqb 0 0 && bv_eqb tp tp && timespec_ok_b bs (m_clock m)`

    as the only branch left.  `t` is the CLOCK_MONOTONIC reading the model
    carries, i.e. the argument of `clock_model`; it has to be a parameter
    because the envelope test's `by decide` fact mentions it.

    `read_bytes_map` is a `def`, so neither `rfl` nor `dsimp` will reduce
    it (`DecidableEq (Option (List byte))` does exist, so `by decide`
    will): it is discharged as a fact and rewritten. -/
macro "clock_monotonic" "(" t:term ")" : tactic =>
  `(tactic|
    (rw [check_syscall_clock_gettime];
     unfold check_clock_gettime;
     dsimp only;
     have h1 : ¬(clockid_percall_b (clockid32 (1 : word)) = true) := (by decide);
     rw [ite_eq_right h1];
     have h2 : ¬((↑(BitVec.toNat (clockid32 (1 : word))) == CLOCK_PROCESS_CPUTIME_ID) = true) := (by decide);
     rw [ite_eq_right h2];
     have h3 : ¬((!↑(BitVec.toNat (clockid32 (1 : word))) == CLOCK_MONOTONIC) = true) := (by decide);
     rw [ite_eq_right h3];
     have h4 : ¬((!decide (↑(BitVec.toNat (m_clock (clock_model ($t)))) < CLOCK_NS_ENVELOPE)) = true) := (by decide);
     rw [ite_eq_right h4];
     have hrd : read_bytes_map (clock_input 1).in_wmem (4096 : word) (BitVec.ofInt 64 16) = some (List.replicate 16 0) := (by decide);
     rw [hrd];
     dsimp only))

/-! PROVED — route A (`check_unmodeled`): the model's clock is past the
    envelope, so the arm declines, and the constructor projection settles it
    without naming a model. -/
theorem clock_at_envelope_declines :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
      (clock_model (2 ^ 63)) = .CheckUnmodeled
:= by check_unmodeled

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  Two readings that
    return the SAME nanosecond are admissible: CLOCK_MONOTONIC never runs
    backwards, but it is not required to advance, and a coarse
    clocksource really does answer two quick calls alike.  No program can
    force that coincidence, so it is pinned here.  The accepted step
    leaves [m_clock] where it was. -/

/-! PROVED — route B (`clock_monotonic`), with the recorded reading
    normalised by `decide` so that `with_clock` puts the same clock back.
-/
theorem clock_equal_reading_is_admissible :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s)] [])
      (clock_model 1000000000) = .CheckOk (clock_model 1000000000) []
:= by
  clock_monotonic (1000000000)
  rw [show timespec_ns ts_1s = 1000000000 from by decide]
  rw [ite_eq_left (by decide : (bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_1s (m_clock (clock_model 1000000000))) = true)]
  rfl

/-! MODEL-INTERNAL STATE.  An advancing reading is admissible too, and
    the point of the case is the SECOND half: the accepted step carries
    the new time into [m_clock].  That the clock is updated at all is
    invisible from outside — nothing about [m_clock] reaches a trace —
    so no run can check it directly; a run sees it
    only indirectly, through a later call being judged against it. -/

/-! PROVED — route B (`clock_monotonic`).  The right-hand model is
    `clock_model 2000000000`, so this case also fails if the checker ever
    stops carrying the new time into [m_clock].-/
theorem clock_advancing_reading_records_it :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_2s)] [])
      (clock_model 1000000000) = .CheckOk (clock_model 2000000000) []
:= by
  clock_monotonic (1000000000)
  rw [show timespec_ns ts_2s = 2000000000 from by decide]
  rw [ite_eq_left (by decide : (bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_2s (m_clock (clock_model 1000000000))) = true)]
  rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the [CheckReject]
    half.  A reading one nanosecond EARLIER than the last is refused.
    This is the monotonicity guarantee itself, and no real kernel can be
    asked to violate it. -/

/-! PROVED — route B (`clock_monotonic`); the one-write test's
    `timespec_ok_b` conjunct is what fails, and `decide` settles it.  The
-/
theorem clock_backwards_reading_rejected :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_1s_minus)] [])
      (clock_model 1000000000) = .CheckReject
:= by
  clock_monotonic (1000000000)
  rw [ite_eq_right (by decide : ¬((bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_1s_minus (m_clock (clock_model 1000000000))) = true))]

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the exact boundary.
    The boundary itself, tv_nsec = 10^9 exactly, is refused
    even though the total it encodes moves forward: the kernel's
    normalization carries whole seconds out of the nanosecond field, so
    a full second never appears there, and admitting it would make two
    different byte strings mean the same instant. -/

/-! PROVED — route B (`clock_monotonic`).-/
theorem clock_denormalized_nsec_rejected :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_denorm)] [])
      (clock_model 0) = .CheckReject
:= by
  clock_monotonic (0)
  rw [ite_eq_right (by decide : ¬((bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_denorm (m_clock (clock_model 0))) = true))]


/-! The reading's own ENVELOPE, which no real run can reach.

    [timespec_ok_b]'s fourth conjunct bounds the READING, where
    [clock_at_envelope_declines] above bounds the previously RECORDED
    clock; nothing else in the tree separates the two. -/
def ts_max : List byte :=          /- 2^63 - 1 ns exactly -/
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [255, 215, 242, 50, 0, 0, 0, 0]
def ts_over : List byte :=         /- 2^63 ns: one too many -/
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [0, 216, 242, 50, 0, 0, 0, 0]
/-! tv_sec = 18446744073, tv_nsec = 709552616 — a reading of 2^64 + 1000
    nanoseconds, whose LOW 64 BITS are 1000. -/
def ts_wrap : List byte :=
  [9, 250, 130, 75, 4, 0, 0, 0] ++ [232, 233, 74, 42, 0, 0, 0, 0]

/-! The largest reading [ktime_t] can hold is admissible, and recorded. -/

/-! PROVED — route B (`clock_monotonic`), with `timespec_ns ts_max`
    normalised to `2^63 - 1`.  The right-hand model is the reading's own
    value, so this case also pins that the reading is RECORDED.  The
-/
theorem clock_reading_at_envelope_minus_one_admissible :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_max)] [])
      (clock_model 0) = .CheckOk (clock_model (2 ^ 63 - 1)) []
:= by
  clock_monotonic (0)
  rw [show timespec_ns ts_max = 2 ^ 63 - 1 from by decide]
  rw [ite_eq_left (by decide : (bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_max (m_clock (clock_model 0))) = true)]
  rfl

/-! One nanosecond further is refused: [ktime_t] is signed 64-bit, so
    2^63 ns is not a time a kernel can report. -/

/-! PROVED — route B (`clock_monotonic`).-/
theorem clock_reading_at_envelope_rejected :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_over)] [])
      (clock_model 0) = .CheckReject
:= by
  clock_monotonic (0)
  rw [ite_eq_right (by decide : ¬((bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_over (m_clock (clock_model 0))) = true))]

/-! THE ONE CASE THAT PINS THE [Z] ARITHMETIC.  [timespec_ns] sums
    [tv_sec * 10^9 + tv_nsec] in [Z] on purpose.  Summed in [word] this
    reading is 1000 ns — larger than the recorded 0 and far under the
    envelope — so a wrapping spelling answers [CheckOk] and lets an
    absurd [tv_sec] present itself as a small, admissible time.  Every
    other case in this file passes under both spellings; this is the
    only one that separates them. -/

/-! PROVED — route B (`clock_monotonic`); the envelope conjunct of
    `timespec_ok_b` is what refuses it, which `decide` settles.  The
-/
theorem clock_reading_wrapping_sum_rejected :
    check_syscall (clock_input 1) (mkEffect 0 [(4096, ts_wrap)] [])
      (clock_model 0) = .CheckReject
:= by
  clock_monotonic (0)
  rw [ite_eq_right (by decide : ¬((bv_eqb (0 : word) (BitVec.ofInt 64 0) && bv_eqb (4096 : word) (4096 : word) && timespec_ok_b ts_wrap (m_clock (clock_model 0))) = true))]

/-! ---------------------------------------------------------------------
    CLOCK_REALTIME, whose whole content is what it does NOT promise.

    What no real run can reach is the ABSENCE of the
    cross-call constraint: a kernel will not run its wall clock
    backwards between two calls on request, and [m_clock] not moving is
    invisible from outside.  Each case below is therefore paired with
    the CLOCK_MONOTONIC case directly above that it contradicts.
    ------------------------------------------------------------------ -/

/-! UNIVERSALLY QUANTIFIED, and the load-bearing one: an accepted
    per-call — CLOCK_REALTIME, raw, coarse or boottime — call leaves
    the model EXACTLY as it found it, for
    every input, destination, effect and starting model.  This is what
    stops a future change quietly giving any of those ids an [m_clock]-
    style field — a field written by the spec and read by nothing would
    look like a guarantee the kernel does not give.  For the wall clock
    [Kernel.Time.PosixTimers.realtime_ok_b] says why there is none to
    record: [do_settimeofday64] refuses nothing that sets the clock
    EARLIER, and [adjtimex]'s ADJ_SETOFFSET steps it by a signed value
    straight from userspace.  Neither needs the modeled process to do
    anything.  For the other four ids
    [Kernel.Time.PosixTimers.clockid_percall_b] says why the guarantees
    they DO carry are deliberately not stated. -/

theorem clock_gettime_percall_leaves_the_model_alone (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hid : clockid_percall_b clkid = true)
    (H : check_clock_gettime i clkid tp eff m = .CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_clock_gettime at H
  rw [ite_eq_left Hid] at H
  try dsimp only at H
  cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
  | none =>
    rw [hdst] at H
    try dsimp only at H
    exact nomatch H
  | some bs0 =>
    rw [hdst] at H
    try dsimp only at H
    obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
    cases ws with
    | nil => dsimp only at H; exact nomatch H
    | cons p ws' =>
      obtain ⟨a, bs⟩ := p
      cases ws' with
      | cons p' ws'' => dsimp only at H; exact nomatch H
      | nil =>
        cases zs with
        | cons q zs' => dsimp only at H; exact nomatch H
        | nil =>
          cases us with
          | cons q us' => dsimp only at H; exact nomatch H
          | nil =>
            cases cs with
            | cons q cs' => dsimp only at H; exact nomatch H
            | nil =>
              cases ks with
              | cons q ks' => dsimp only at H; exact nomatch H
              | nil =>
                dsimp only at H
                split at H
                · simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨rfl, rfl⟩ := H
                  exact ⟨rfl, rfl⟩
                · exact nomatch H

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the exact
    counterpart of [clock_backwards_reading_rejected] above: the SAME
    bytes, the SAME recorded clock, the other id.  A wall-clock reading
    one nanosecond EARLIER than the last monotonic one is admissible,
    because CLOCK_REALTIME carries no monotonicity at all — and the
    accepted step leaves the recorded clock where it was rather than
    dragging it backwards. -/
theorem realtime_backwards_reading_is_admissible :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = .CheckOk (clock_model 1000000000) []
:= by rfl

/-! MODEL-INTERNAL STATE, and the counterpart of
    [clock_at_envelope_declines].  A recorded clock past what [ktime_t]
    holds declines a MONOTONIC read, because the choice that read makes
    is relative to it and would be empty.  It does not decline a
    WALL-CLOCK read: that arm never consults [m_clock], so there is
    nothing for the envelope to be empty against. -/
theorem realtime_ignores_the_recorded_clock :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = .CheckOk (clock_model (2 ^ 63)) []
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  What the wall clock
    DOES have to satisfy, it satisfies on the same terms as the
    monotonic one.  A tv_nsec of exactly 10^9 is refused:
    [ktime_get_real_ts64] sets the field to 0 and normalizes with
    [timespec64_add_ns], so a full second never appears there. -/
theorem realtime_denormalized_nsec_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  A reading of 2^63 ns
    is refused for the wall clock too.  The bound is
    [timespec64_valid_settod], which every writer of the wall clock
    passes and which stops thirty years SHORT of [KTIME_SEC_MAX]
    precisely so uptime cannot carry the clock out of [ktime_t]. -/
theorem realtime_reading_at_envelope_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! The largest wall-clock reading [ktime_t] can hold is admissible, and
    is NOT recorded — the pair with the case above makes the boundary
    non-vacuous, and the pair with
    [clock_reading_at_envelope_minus_one_admissible], which records the
    same bytes, makes the difference between the arms non-vacuous. -/
theorem realtime_reading_at_envelope_minus_one_admissible :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_max)] [])
    (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

/-! ---------------------------------------------------------------------
    CLOCK_PROCESS_CPUTIME_ID, which is not a clock.

    It reports the thread group's [sum_exec_runtime] — a [u64] count of
    nanoseconds of CPU consumed — so
    [Kernel.Time.PosixTimers.cputime_ok_b] keeps the wall clock's
    per-reading conditions and moves the 2^63 ns envelope onto the
    SIGNED reading, two-sided.  That is the whole difference between
    the arms, and it is the half no real run can reach: no kernel can be
    asked for a reading near either end of an [s64], and [m_clock] not
    moving is invisible from outside.  Where a case below decides a
    boundary or contradicts a sibling arm it is paired — with the
    reading one nanosecond away, or with the case on the arm that
    answers the other way for the same bytes.
    ------------------------------------------------------------------ -/

/-! Readings at the two ends of the [s64] [ns_to_timespec64] is handed.

    [ts_cpu_min] is what the kernel writes for a sample of exactly
    2^63: [ns_to_timespec64]'s [nsec < 0] branch gives
    [tv_sec = -div_u64_rem(-nsec - 1, 10^9, &rem) - 1 = -9223372037] and
    [tv_nsec = 10^9 - rem - 1 = 145224192].  ([-nsec] is the one place
    that expression can overflow, and this is the input where it does:
    at [INT64_MIN] the negation wraps to itself, and the [- 1] and the
    [u64] parameter of [div_u64_rem] are what make the result come out
    right anyway — 2^63 - 1 is the value divided.)  [ts_cpu_below] is that
    reading one nanosecond lower, which is not in the branch's image.
    [ts_cpu_neg1] is the largest sample a [u64] holds, 2^64 - 1, which
    the same branch spells as [tv_sec = -1] with a full [tv_nsec]. -/
def ts_cpu_min : List byte :=      /- signed total -2^63 exactly -/
  [251, 130, 62, 218, 253, 255, 255, 255] ++ [0, 242, 167, 8, 0, 0, 0, 0]
def ts_cpu_below : List byte :=    /- -2^63 - 1: one too few -/
  [251, 130, 62, 218, 253, 255, 255, 255] ++ [255, 241, 167, 8, 0, 0, 0, 0]
def ts_cpu_neg1 : List byte :=     /- tv_sec = -1, tv_nsec = 10^9 - 1 -/
  [255, 255, 255, 255, 255, 255, 255, 255] ++ [255, 201, 154, 59, 0, 0, 0, 0]

/-! UNIVERSALLY QUANTIFIED, and the load-bearing one, for the reason
    [clock_gettime_percall_leaves_the_model_alone] gives and one more
    of its own: an accepted CLOCK_PROCESS_CPUTIME_ID call leaves the
    model EXACTLY as it found it, for every input, destination, effect
    and starting model.  This is what stops a future change relating
    CPU consumed to [m_clock].  The two are different quantities and no
    kernel-enforced inequality connects them — a thread group on
    several CPUs burns CPU faster than any clock advances, and one that
    is not scheduled burns none — so a field here could only be written
    and never read. -/

theorem clock_gettime_cputime_leaves_the_model_alone (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hid : (bv_unsigned clkid =? CLOCK_PROCESS_CPUTIME_ID) = true)
    (H : check_clock_gettime i clkid tp eff m = .CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  have hclk : bv_unsigned clkid = CLOCK_PROCESS_CPUTIME_ID := by
    simpa only [zeqb, beq_iff_eq] using Hid
  have hpc : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true := by
    rw [show ((clkid.toNat : Int)) = CLOCK_PROCESS_CPUTIME_ID from hclk]
    decide
  have Hpc : clockid_percall_b clkid = false := by
    unfold clockid_percall_b
    rw [show ((clkid.toNat : Int)) = CLOCK_PROCESS_CPUTIME_ID from hclk]
    decide
  unfold check_clock_gettime at H
  rw [Hpc, hpc] at H
  simp only [Bool.false_eq_true, ite_true, ite_false] at H
  try dsimp only at H
  cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
  | none =>
    rw [hdst] at H
    try dsimp only at H
    exact nomatch H
  | some bs0 =>
    rw [hdst] at H
    try dsimp only at H
    obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
    cases ws with
    | nil => dsimp only at H; exact nomatch H
    | cons p ws' =>
      obtain ⟨a, bs⟩ := p
      cases ws' with
      | cons p' ws'' => dsimp only at H; exact nomatch H
      | nil =>
        cases zs with
        | cons q zs' => dsimp only at H; exact nomatch H
        | nil =>
          cases us with
          | cons q us' => dsimp only at H; exact nomatch H
          | nil =>
            cases cs with
            | cons q cs' => dsimp only at H; exact nomatch H
            | nil =>
              cases ks with
              | cons q ks' => dsimp only at H; exact nomatch H
              | nil =>
                dsimp only at H
                split at H
                · simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨rfl, rfl⟩ := H
                  exact ⟨rfl, rfl⟩
                · exact nomatch H

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the counterpart
    of [realtime_backwards_reading_is_admissible] and
    [clock_backwards_reading_rejected]: the SAME bytes, the SAME
    recorded clock, a third id.  A CPU-time reading is related to no
    earlier reading and to no clock, so it is admissible below the
    recorded one, and the accepted step leaves that clock alone. -/
theorem cputime_backwards_reading_is_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = .CheckOk (clock_model 1000000000) []
:= by rfl

/-! MODEL-INTERNAL STATE, the counterpart of
    [clock_at_envelope_declines] and [realtime_ignores_the_recorded_clock].
    A recorded clock past what [ktime_t] holds declines a MONOTONIC
    read and not this one: this arm never consults [m_clock] either. -/
theorem cputime_ignores_the_recorded_clock :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = .CheckOk (clock_model (2 ^ 63)) []
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  The conjunct that
    survives on this arm still bites: a tv_nsec of exactly 10^9 is
    refused, because all three branches of [ns_to_timespec64] leave
    that field below 10^9 — the [nsec < 0] one by computing
    [NSEC_PER_SEC - rem - 1]. -/
theorem cputime_denormalized_nsec_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and THE PAIR THAT IS
    THE WHOLE DIFFERENCE BETWEEN THIS ARM AND THE WALL CLOCK'S.  A
    reading with a NEGATIVE tv_sec is what [ns_to_timespec64] writes
    once the [u64] sample passes 2^63, so this arm must admit it; the
    wall clock has no such shape, [realtime_ok_b] reads tv_sec
    unsigned, and the case below rejects the identical bytes. -/
theorem cputime_negative_tv_sec_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
    (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

theorem realtime_negative_tv_sec_rejected :
  check_syscall (clock_input 0) (mkEffect 0 [(4096, ts_cpu_neg1)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — the bottom of the
    envelope, which exists only on this arm.  A SAMPLE of exactly 2^63
    is admissible: it is the smallest [u64] the [nsec < 0] branch sees,
    and so the one whose READING is the most negative of any this id
    can report.  (Larger samples read HIGHER, not lower, back up
    towards -1 — [ts_cpu_neg1] above is the largest sample of all.) -/
theorem cputime_at_signed_envelope_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_min)] [])
    (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

/-! One nanosecond lower is refused, which is what makes the bound
    above non-vacuous: the argument to [ns_to_timespec64] is an [s64],
    so nothing below -2^63 is in its image. -/
theorem cputime_below_signed_envelope_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_cpu_below)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT — and the top of the
    envelope, where this arm agrees with the other two rather than
    differing from them.  Putting the bound on the signed reading does
    not delete it: 2^63 - 1 ns is the largest positive sample, and
    2^63 is refused here exactly as it is for the wall clock. -/
theorem cputime_reading_at_envelope_minus_one_admissible :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_max)] [])
    (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

theorem cputime_reading_at_envelope_rejected :
  check_syscall (clock_input 2) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! ---------------------------------------------------------------------
    The raw, coarse and boottime ids, which share the wall-clock arm.

    [Kernel.Time.PosixTimers.clockid_percall_b] carries the argument;
    what the cases below pin is that the sharing is REAL — each id is
    judged exactly as CLOCK_REALTIME is, per call, against
    [realtime_ok_b] alone, and the model is left exactly as found.
    One case per id, each deciding the conjunct or the absence a real
    run cannot reach for that id.
    ------------------------------------------------------------------ -/

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT, and the counterpart of
    [clock_backwards_reading_rejected] on an id that IS monotone in the
    kernel: a BOOTTIME reading below the recorded monotonic clock is
    admissible, because a per-call id is deliberately related to
    nothing — each call is independently arbitrary — and the accepted
    step leaves the recorded clock alone. -/
theorem boottime_backwards_reading_is_admissible :
  check_syscall (clock_input 7) (mkEffect 0 [(4096, ts_1s_minus)] [])
    (clock_model 1000000000)
  = .CheckOk (clock_model 1000000000) []
:= by rfl

/-! What a per-call id DOES have to satisfy, it satisfies on the wall
    clock's terms.  A tv_nsec of exactly 10^9 is refused for
    CLOCK_MONOTONIC_RAW: [ktime_get_raw_ts64] normalizes with
    [timespec64_add_ns] like every fine-grained path here. -/
theorem monotonic_raw_denormalized_nsec_rejected :
  check_syscall (clock_input 4) (mkEffect 0 [(4096, ts_denorm)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! The envelope survives the sharing: a CLOCK_REALTIME_COARSE reading
    of 2^63 ns is refused — a tick snapshot of the wall clock is still
    a time [ktime_t] must be able to hold. -/
theorem realtime_coarse_reading_at_envelope_rejected :
  check_syscall (clock_input 5) (mkEffect 0 [(4096, ts_over)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! MODEL-INTERNAL STATE, the counterpart of
    [realtime_ignores_the_recorded_clock] for the id nearest the one
    that owns the field: a recorded clock past what [ktime_t] holds
    declines a MONOTONIC read and not a MONOTONIC_COARSE one — a
    per-call arm never consults [m_clock], even for an id that reads
    the same underlying clock at tick granularity. -/
theorem monotonic_coarse_ignores_the_recorded_clock :
  check_syscall (clock_input 6) (mkEffect 0 [(4096, ts_1s)] [])
    (clock_model (2 ^ 63))
  = .CheckOk (clock_model (2 ^ 63)) []
:= by rfl

end LinuxSem.Checks.Cases.Kernel.Time.PosixTimers
