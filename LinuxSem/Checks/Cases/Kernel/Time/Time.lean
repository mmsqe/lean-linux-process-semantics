/-
  * LinuxSem.Checks.Cases.Kernel.Time.Time — worked examples over gettimeofday (169)

  Worked cases over `Sys.Kernel.Time.Time`, which answers to Linux
  [kernel/time/time.c]: the examples for the syscalls defined there, and
  no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  What is here is of three kinds:
  the QUANTIFIED claims — every timezone pointer declines, every
  accepted call leaves the model alone — the two boundaries of the
  [KTIME_SEC_MAX] ceiling, which a real wall clock never lands on, and
  the destinations at the top of the address space, which no real Sv48
  run can map.

  Spelling.  `wmem_ts` and `clock_model` are
  [Checks/Cases/Kernel/Time/PosixTimers]'s shared fixtures, defined there
  rather than duplicated here, which is where the other clock code looks
  for them.  `Z` is `Int`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
  `bv_unsigned w` is `(w.toNat : Int)`, `Some`/`None` are `some`/`none`,
  `mkInput` is the `SyscallInput` constructor and `CheckOk`/`CheckReject`/
  `CheckUnmodeled` are the `check_result` constructors.  The local
  `infix` notations restore the `Z` comparisons verbatim.

  Proofs.  The closed examples are `rfl` — kernel reduction — and
  `decide` cannot be the rule where the answer is a `check_result`, which
  carries a `Model` and so has no `DecidableEq`.  The two `≠` examples
  are `decide`, because their goal is an inequality of
  `Option (List byte)`, which IS decidable.  The two QUANTIFIED lemmas
  are ordinary tactic proofs: `cases` with `nomatch` in the impossible
  arm, and `check_ret_only_ok_iff` from the prelude.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Kernel.Time.PosixTimers
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Time.Time
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.Time
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Time.Time
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Kernel.Time.PosixTimers

namespace LinuxSem.Checks.Cases.Kernel.Time.Time

open LinuxSem.Common.RocqSpelling

/-! Rocq spellings (`bv_unsigned`, `Z_to_bv`, `zleb`/`zltb`) come from
    `LinuxSem.Common.RocqSpelling`, opened above. -/

/-- `<=?` on `Z`. -/
local infix:50 " <=? " => zleb
/-- `<?` on `Z`. -/
local infix:50 " <? " => zltb

/-! [gettimeofday(4096, tz)]: sixteen writable bytes at 4096, nothing
    readable, and the timezone pointer left free. -/
def gettimeofday_input (tz : word) : SyscallInput :=
  SyscallInput.mkInput 169 [4096, tz, 0, 0, 0, 0] (fun _ => none) wmem_ts

/-! UNIVERSALLY QUANTIFIED.  Every non-NULL timezone pointer declines,
    whatever the destination, the effect or the model.  The kernel would
    answer from [sys_tz], eight bytes of mutable global state the model
    has nowhere to carry, so the only honest answer is to decline — and
    this is what stops a future arm quietly answering [{0, 0}] from a
    guess about the deployment.  [tz] is tested before anything else,
    which is why no hypothesis about [tv] or [eff] is needed. -/

theorem gettimeofday_declines_every_timezone (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model)
    (H : w_is0 tz = false) :
    check_gettimeofday i tv tz eff m = .CheckUnmodeled := by
  unfold check_gettimeofday
  rw [H]
  rfl

/-! UNIVERSALLY QUANTIFIED, and the pin on the central design decision.
    There is deliberately no realtime field in [Model]: the reading is
    chosen afresh per call and related to nothing, because relating
    realtime to monotonic would need a per-run offset that stops being
    constant the moment anything sets the clock.  The consequence is
    that an accepted [gettimeofday] moves NOTHING — not the clock, not
    the fds, not the maps — and emits no event.  No trace can establish
    that: a trace shows what an execution did, not that a whole class of
    executions left the model alone. -/

theorem gettimeofday_never_moves_the_model (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_gettimeofday i tv tz eff m = .CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_gettimeofday at H
  cases htz : w_is0 tz with
  | false =>
    rw [htz] at H
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
    exact nomatch H
  | true =>
    rw [htz] at H
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
    cases htv : w_is0 tv with
    | true =>
      rw [htv] at H
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
      exact nomatch H
    | false =>
      rw [htv] at H
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
      cases hcp : copy_bytes_map i.in_wmem tv 16 with
      | none =>
        rw [hcp] at H
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
        cases hok : (!access_okb tv 8) with
        | false =>
          rw [hok] at H
          simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
          exact nomatch H
        | true =>
          rw [hok] at H
          simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
          obtain ⟨_, hm, hev⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
          exact ⟨hm, hev⟩
      | some _ =>
        rw [hcp] at H
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at H
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

/-! tv_sec = KTIME_SEC_MAX - 1 = 9223372035, tv_usec = 999999 — the
    latest wall-clock instant [timeval_ok_b] admits. -/
def tv_ceiling_minus : List byte :=
  [3, 125, 193, 37, 2, 0, 0, 0] ++ [63, 66, 15, 0, 0, 0, 0, 0]
/-! The same microsecond one second later: tv_sec = KTIME_SEC_MAX. -/
def tv_at_ceiling : List byte :=
  [4, 125, 193, 37, 2, 0, 0, 0] ++ [63, 66, 15, 0, 0, 0, 0, 0]

/-! THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  [timeval_ok_b]'s
    third conjunct bounds tv_sec by [KTIME_SEC_MAX], and a real run
    never reaches the boundary from either side: a real reading is a
    wall clock of roughly 1.7e9 seconds, five times under it.  So these
    two cases are the only thing that exercises the conjunct.

    The admitted side first: the last microsecond below the ceiling. -/
theorem gettimeofday_reading_below_ceiling_admissible :
  check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_ceiling_minus)] [])
    (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

/-! One second further is refused.  [KTIME_SEC_MAX] is
    [(2^63 - 1) / 10^9]: a [tv_sec] at or above it is a wall clock
    [ktime_t] cannot hold once converted to nanoseconds, which is the
    same ceiling [nanosleep] declines a request at, reached from the
    other direction. -/
theorem gettimeofday_reading_at_ceiling_rejected :
  check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_at_ceiling)] [])
    (clock_model 0) = .CheckReject
:= by rfl

/-! THE DESTINATION THAT WALKS OFF THE TOP OF THE ADDRESS SPACE, and the
    bands on either side of [TASK_SIZE].
    What belongs here is the THIRD of the four reasons at the top of
    [Checks.Examples] — it pins [in_wmem] and the constant
    [State.TASK_SIZE].  A real Sv48 run maps nothing at or above 2^47,
    so there a wrapping range is unwritable
    twice over and a spec that merely walked would reach the same
    verdict as one that asks the range first; the two separate only in
    the DEFINITION, which is what [Equivalence.strong_universal]
    quantifies over.  So the memories below map the wrapped range IN
    FULL, the bare walk is shown reading it back, and the range test is
    shown refusing it anyway — which is what tells
    [State.copy_bytes_map] from [State.read_bytes_map], and what makes
    the widths 8 and 16 a measurement against [State.TASK_SIZE] rather
    than against what happened to be mapped.

    Same shape as [Checks.Cases.Net.Socket]'s socketpair groups, with
    the widths 4 and 8 scaled to 8 and 16. -/

/-! The last eight bytes of the address space, so the 16-byte walk
    covers them and then the eight at 0. -/
def gettimeofday_wrap_tv : word := Z_to_bv 64 (2 ^ 64 - 8)

/-! A memory that maps EXACTLY the wrapped range and nothing else, which
    is what makes the walk Example below tight. -/
def gettimeofday_wrap_mem : word → Option byte :=
  fun a => if ((bv_unsigned a <? 8) || (2 ^ 64 - 8 <=? bv_unsigned a))
           then some (Z_to_bv 8 0) else none

/-! THE MUTATION TEST, MADE PERMANENT.  This is the walk alone, which
    WRAPS because [State.read_bytes_map] advances in word arithmetic,
    and which reads all sixteen bytes back off a memory that maps only
    those sixteen.  It says "writable", so an arm that consulted only
    the walk would answer 0 and a 16-byte write — where Linux's first
    [put_user] is refused by [access_ok] and the call is -EFAULT with
    nothing written.  Without this beside them the
    two Examples below would also pass if [gettimeofday_wrap_tv] stopped
    wrapping or [gettimeofday_wrap_mem] stopped mapping the range. -/
theorem gettimeofday_wrap_would_pass_the_bare_walk :
  read_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv (Z_to_bv 64 16)
    ≠ none
:= by decide

/-! [State.copy_bytes_map] refuses it before the walk is consulted. -/
theorem gettimeofday_wrap_is_refused_before_the_walk :
  copy_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv 16 = none
:= by rfl

/-! THE ONE THAT MATTERS, at the checker: -EFAULT with nothing written
    is the answer, and the write a bare walk would admit — a reading
    landing at [2^64 - 8] and, after the word wraps, at 0 — is
    refused.  The second half is the negative direction. -/
theorem gettimeofday_wrapping_tv_is_efault :
  check_syscall (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0]
                   (fun _ => none) gettimeofday_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = .CheckOk (clock_model 0) []
  ∧ check_syscall (SyscallInput.mkInput 169 [gettimeofday_wrap_tv, 0, 0, 0, 0, 0]
                     (fun _ => none) gettimeofday_wrap_mem)
       (mkEffect 0 [(gettimeofday_wrap_tv, tv_ceiling_minus)] [])
       (clock_model 0)
     = .CheckReject
:= by constructor <;> rfl

/-! PAST [TASK_SIZE] WITHOUT WRAPPING, and still refused: [tv = 2^63]
    with sixteen bytes sums to 2^63 + 16, under 2^64, so a bare no-wrap
    test would admit it and the walk reads it in full.  riscv64's
    [access_ok] refuses it because [__access_ok] tests
    [addr <= TASK_SIZE - size] (include/asm-generic/access_ok.h at
    v6.18.46, with [TASK_SIZE_MAX] falling back to [TASK_SIZE] since
    arch/riscv defines no other).  Without this pair the three Examples
    above pass under either spelling of the guard. -/
def gettimeofday_high_tv : word := Z_to_bv 64 (2 ^ 63)

def gettimeofday_high_mem : word → Option byte :=
  fun a => if ((2 ^ 63 <=? bv_unsigned a) && (bv_unsigned a <? 2 ^ 63 + 16))
           then some (Z_to_bv 8 0) else none

theorem gettimeofday_high_range_reads :
  read_bytes_map gettimeofday_high_mem gettimeofday_high_tv (Z_to_bv 64 16)
    ≠ none
:= by decide

theorem gettimeofday_high_range_would_pass_a_no_wrap_test :
  (two_pow_64 <=? bv_unsigned gettimeofday_high_tv + 16) = false
:= by rfl

theorem gettimeofday_past_task_size_is_efault :
  check_syscall (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0]
                   (fun _ => none) gettimeofday_high_mem)
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = .CheckOk (clock_model 0) []
  ∧ check_syscall (SyscallInput.mkInput 169 [gettimeofday_high_tv, 0, 0, 0, 0, 0]
                     (fun _ => none) gettimeofday_high_mem)
       (mkEffect 0 [(gettimeofday_high_tv, tv_ceiling_minus)] [])
       (clock_model 0)
     = .CheckReject
:= by constructor <;> rfl

/-! THE TWO WIDTHS, 8 AND 16, measured over a memory that maps
    everything, so the walk is settled for every destination at once
    and the verdict turns on the range tests alone.  Four [tv]s, one
    step apart at each edge of the band the spec declines:

    - [TASK_SIZE - 16]: both stores inside, the reading is delivered.
      This is the control that keeps the refusals above honest — they
      would also pass under a guard that refused every [tv].
    - [TASK_SIZE - 15] and [TASK_SIZE - 8], the two ends of the torn
      band: the first [put_user] passes its own 8-byte test and the
      second does not, so the arm declines whatever the effect says.
    - [TASK_SIZE - 7]: the FIRST store is refused, so -EFAULT with
      nothing written is the answer and a delivered reading is not.

    Move either width by one and one of these flips. -/
def gettimeofday_open_mem : word → Option byte := fun _ => some 0

def gettimeofday_at (tv : word) : SyscallInput :=
  SyscallInput.mkInput 169 [tv, 0, 0, 0, 0, 0] (fun _ => none) gettimeofday_open_mem

def task_size_minus (k : Int) : word := Z_to_bv 64 (TASK_SIZE - k)

theorem gettimeofday_last_admitted_tv_is_delivered :
  check_syscall (gettimeofday_at (task_size_minus 16))
    (mkEffect 0 [(task_size_minus 16, tv_ceiling_minus)] []) (clock_model 0)
  = .CheckOk (clock_model 0) []
:= by rfl

theorem gettimeofday_torn_band_declines :
  check_syscall (gettimeofday_at (task_size_minus 15))
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0) = .CheckUnmodeled
  ∧ check_syscall (gettimeofday_at (task_size_minus 8))
       (mkEffect (errno_ret EFAULT) [] []) (clock_model 0) = .CheckUnmodeled
:= by constructor <;> rfl

theorem gettimeofday_first_store_refused_is_efault :
  check_syscall (gettimeofday_at (task_size_minus 7))
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = .CheckOk (clock_model 0) []
  ∧ check_syscall (gettimeofday_at (task_size_minus 7))
       (mkEffect 0 [(task_size_minus 7, tv_ceiling_minus)] []) (clock_model 0)
     = .CheckReject
:= by constructor <;> rfl

end LinuxSem.Checks.Cases.Kernel.Time.Time
