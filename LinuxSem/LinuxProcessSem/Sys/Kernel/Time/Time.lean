/-
  * LinuxProcessSem.Sys.Kernel.Time.Time — gettimeofday (169)

    This file answers to Linux [kernel/time/time.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs
    in is therefore not a judgement call — look up where the kernel
    defines the syscall.  [Specs.lean] carries the whole map.

    Its own definitions are cited as [Time.<ident>], not
    [Kernel.Time.Time.<ident>]: kernel/time/time.c puts a file called
    [time] inside a directory called [time].  [Time] alone resolves, and it is the only spelling that
    does.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.lean] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.

  -  `x <- c;; k` has no Lean notation in this monad: it is
    `bind c (fun x => k)`, and `pure`/`choose`/`unmodeled` are
    `Monad.lean`'s.
  - `access_okb`/`copy_bytes_map` are `StateMemory`'s (they live in the
    parent namespace `LinuxSem.LinuxProcessSem`);
    `err_ret`/`w_is0` are `Sys.Syscall`'s and
    `tv_sec_of`/`tv_frac_of`/`KTIME_SEC_MAX` are `Sys.Uapi`'s.
    `Require Export Syscall Uapi Uaccess` puts them all in
    unqualified scope; the two `open`s below do the same.

  The well-formedness predicate is named `timeval_ok_b` here, as it is
  throughout the kernel model.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.StateMemory

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Time

/-- What a `struct __kernel_old_timeval` the kernel wrote must satisfy.
    Three conditions, and NOTHING relating it to any earlier reading —
    see `gettimeofday_spec` for why there is nothing to relate it to.

    - EXACTLY 16 BYTES — `__kernel_long_t tv_sec` then
      `__kernel_long_t tv_usec`, 8 bytes each on riscv64
      (include/uapi/linux/time_types.h, byte-identical at v6.10-v6.15).
    - `tv_usec` IS NORMALIZED, below 10^6.  The kernel computes it as
      `ts.tv_nsec / 1000` out of a `timespec64` that
      `timespec64_add_ns` (include/linux/time64.h) has already carried
      whole seconds out of, so `ts.tv_nsec` is below 10^9 and the
      quotient is below 10^6.  Note this is a DIFFERENT normalization
      constant from `PosixTimers.timespec_ok_b`'s, which is why the two
      predicates are separate rather than one parameterized by a unit:
      getting them the same way round is the whole content of the
      condition.
    - `tv_sec` IS BELOW `KTIME_SEC_MAX`.  This bound is weaker-footed
      than `clock_gettime`'s and the difference is worth stating:
      `ktime_get_real_ts64` (kernel/time/timekeeping.c) applies NO
      clamp on the read path.  What is checked is the SET path —
      `timespec64_valid_settod` refuses a `tv_sec` at or above
      `TIME_SETTOD_SEC_MAX`, which is `KTIME_SEC_MAX` less
      `TIME_UPTIME_SEC_MAX`, thirty years of headroom
      (include/linux/time64.h), and every writer goes through it
      (`do_sys_settimeofday64`, `do_settimeofday64`,
      `timekeeping_inject_offset`, `timekeeping_init`).  So the reading
      stays under `KTIME_SEC_MAX` unless the machine has been up for
      more than thirty years since the last time anything set its
      clock.  The model takes that as the envelope and declines above
      it, rather than admitting a value no kernel is built to produce.
      One writer does sit behind that argument. -/
def timeval_ok_b (bs : List byte) : Bool :=
  bs.length == 16
  && decide (tv_frac_of bs < 1000000)
  && decide (tv_sec_of bs < KTIME_SEC_MAX)

/-- `gettimeofday tv tz`: read the WALL CLOCK into a `struct timeval`.

    A DIFFERENT QUANTITY FROM `m_clock`, AND IT GETS NO MODEL FIELD.
    That is the decision this spec turns on, so here is the argument.
    `m_clock` exists for one reason: `CLOCK_MONOTONIC` carries a
    guarantee BETWEEN calls — it never runs backwards — and a relation
    between this call and the previous one cannot be written without
    somewhere to have put the previous one.  `CLOCK_REALTIME` carries
    no such guarantee in EITHER direction.  It is settable, by
    `clock_settime` through `posix_clock_realtime_set` and by
    `settimeofday`, both landing in `do_settimeofday64`
    (kernel/time/timekeeping.c), whose only checks are
    `timespec64_valid_settod` and a guard that stops CLOCK_MONOTONIC
    going negative — neither of which stops the wall clock being set
    EARLIER than it currently reads.  `adjtimex` with `ADJ_SETOFFSET`
    steps it by a signed `tv_sec` the caller supplies, through
    `timekeeping_inject_offset` (kernel/time/timekeeping.c), which
    carries the SAME PAIR of checks and not a weaker one: it rejects a
    `tv_nsec` outside `[0, 10^9)`, then applies
    `timespec64_valid_settod` to the RESULTING wall time and the same
    `wall_to_monotonic` comparison.  Those three are byte-identical at
    v6.13-v6.15; at v6.10-v6.12 they take the timekeeper lock by hand
    and hold an explicit `ret` instead of using `scoped_guard` and
    `timekeeping_restore_shadow` — the shadow timekeeper does not exist
    before v6.13 — with the same conditions and the same writes.  A NEGATIVE `tv_sec` passes all three, which is the point:
    this is a SECOND way the wall clock moves backwards, reached
    through a different syscall, not a less carefully checked one.
    And none of that needs the modeled process to do anything: any
    process on the machine with the capability, or an NTP daemon, can
    step the clock between two of its calls.

    So there is no cross-call invariant to record, and a `Model` field
    holding the last wall-clock reading would be written by this spec
    and read by nothing.  The reading is `choose`n afresh per call,
    constrained only by `timeval_ok_b` — per-sample well-formedness and
    nothing else.  (A field WOULD be needed to state that realtime and
    monotonic differ by a constant offset, which is true only while
    nothing sets the clock.  That is not a fact about one process's
    calls; it would have to be a parameter of the run, like
    `ExecEntry`'s stack and brk bases, not a `Model` field.)

    ORDER, and what each gate costs.  `tz` is decided FIRST because
    declining it is unconditional, then `tv`.

    - A NON-NULL `tz` IS DECLINED.  The kernel copies `sys_tz`
      (kernel/time/time.c) into it — eight bytes of MUTABLE GLOBAL
      state whose only writer is `do_sys_settimeofday64`.  It is
      zero-initialized, being file-scope with no initializer, and on a
      machine that keeps its hardware clock in UTC nothing ever sets
      it; but "nothing ever sets it" is a fact about the deployment,
      not about the kernel, and the model has nowhere to carry the
      value.  Answering `{0, 0}` would be a confident guess.  Note
      dropbear passes NULL at all three of its call sites
      (src/dbrandom.c, src/loginrec.c, src/dbutil.c at v2026.94), so
      the decline costs nothing there.
    - A NULL `tv` IS DECLINED, even though Linux answers 0 there
      having written nothing — the whole `if (likely(tv != NULL))`
      block is skipped.  The model could commit to that; it declines
      for the same reason `PosixTimers.clock_gettime_spec` folds a
      wholly unwritable destination into its gate, uniformity over
      coverage, and because no program calls `gettimeofday(NULL, NULL)`
      on purpose.
    - A `tv` THAT IS NOT WHOLLY WRITABLE IS DECLINED, and here the
      reason is stronger than `clock_gettime`'s.  The kernel writes
      `tv` with TWO SEPARATE `put_user` calls, `tv_sec` then
      `tv_usec`, not one `copy_to_user`:
      `if (put_user(ts.tv_sec, &tv->tv_sec) || put_user(ts.tv_nsec / 1000, &tv->tv_usec)) return -EFAULT;`.
      A 16-byte `tv` straddling into an unmapped page therefore
      COMMITS `tv_sec` and then returns -EFAULT — a half-written
      struct with an error return, which is a shape this model has no
      way to spell as a single effect.  Declining is the only honest
      answer.

      A `tv` THE RANGE TEST REFUSES IS DECIDED BEFORE THE WALK, and
      which answer it gets turns on the same two `put_user`s.
      `State.copy_bytes_map` asks `access_okb tv 16` before it walks,
      which is what stops a `tv` in the last bytes of the address
      space wrapping round to low memory and reading back as writable
      — the bare walk answered 0 and a 16-byte write there, where
      Linux writes nothing.  But a refused 16-byte range is NOT a
      promise that nothing was written.  Each `put_user` carries its
      OWN `access_ok` over its own 8-byte range
      (arch/riscv/include/asm/uaccess.h's `put_user` at v6.18.46 tests
      `access_ok` on the pointer over the pointee's size, 8 bytes here,
      before it stores, and
      `__access_ok` in include/asm-generic/access_ok.h is
      `size <= TASK_SIZE_MAX && addr <= TASK_SIZE_MAX - size`), so the
      refused range splits in two:

      - `access_okb tv 8` FALSE: the first store is refused, nothing is
        written, and the call is -EFAULT.  Every wrapping `tv` is in
        here, since a wrap needs `tv >= 2^64 - 15`.  The arm commits to
        that -EFAULT.
      - `access_okb tv 8` TRUE and `access_okb tv 16` FALSE, `tv` in
        `[TASK_SIZE - 15, TASK_SIZE - 8]`: the first store passes its
        own test and the second is refused.  Linux answers -EFAULT
        having stored `tv_sec` if that top page is mapped and nothing
        if it is not — the half-written struct of the bullet above —
        and the arm declines.

      This is `Net.Socket.socketpair_spec`'s situation exactly — two
      `put_user`s with separate range tests and one band where the
      first passes and the second does not — and it takes the same
      decision, with the widths 4 and 8 scaled to 8 and 16.  Where a
      syscall copies its whole struct with ONE `copy_to_user` the
      refused range copies nothing at all, and `Fs.Pipe.pipe2_spec`
      answers -EFAULT across the whole of it.

    On the modeled path the return is a literal 0
    (kernel/time/time.c's `SYSCALL_DEFINE2(gettimeofday, ...)` at
    v6.18.46) and the effect is exactly one 16-byte write at `tv`.

    NOT OBSERVABLE THROUGH MUSL.  musl's `gettimeofday`
    (src/time/gettimeofday.c) is `clock_gettime(CLOCK_REALTIME, &ts)`
    followed by a divide; it never issues syscall 169, on riscv64 or
    anywhere else.  So this arm is reached only by a program that makes
    the raw syscall itself.  What a musl-linked program's
    `gettimeofday` actually issues is `clock_gettime` with
    `CLOCK_REALTIME`, which `PosixTimers.clock_gettime_spec` MODELS, on
    the arm `PosixTimers.realtime_ok_b` governs — so dropbear's three
    call sites are covered there rather than here, and this arm's
    existence buys the raw-syscall caller alone.  On real hardware the
    call does not reach the kernel at all: the vDSO serves it. -/
def gettimeofday_spec (tv tz : word) : SysSpec SyscallEffect :=
  if !w_is0 tz then unmodeled   -- would report `sys_tz`: fail closed
  else if w_is0 tv then unmodeled     -- Linux writes nothing and answers 0
  else
    bind inputSpec fun i =>
      match copy_bytes_map i.in_wmem tv 16 with
      | none =>
        -- 8, NOT 16: only the FIRST `put_user`'s range being refused
        -- proves nothing was written; the bullet above has the bands.
        if !access_okb tv 8 then err_ret EFAULT
        else unmodeled   -- the torn band, or a destination not wholly
                         -- mapped: a partial `put_user` then -EFAULT
      | some _ =>
        bind (choose (fun bs : List byte => timeval_ok_b bs = true)) fun bs =>
          pure (mkEffect (BitVec.ofInt 64 0) [(tv, bs)] [])

/-! ## Port checks

  What follows is this tree's own check on the computable part (AGENTS.md,
  "definition of done"): the decoded fields of a 16-byte `timeval`, and the shape of
  the effect each arm of the order argument commits to. -/

/-! ### Inversion helpers for the monad (port scaffolding)

    `bind`/`choose`/`pure` have no inversion lemmas at the concrete
    types, and the arm checks below need to read an outcome backwards.
    Each iff is definitional (`Iff.rfl`), so nothing is assumed: they
    only name the unfoldings `bind`'s and `pure`'s bodies already give. -/

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

private theorem choose_iff {A : Type} (P : A → Prop) (i : SyscallInput) (m : Model)
    (o : Outcome A Model event) :
    choose P i m o ↔ ∃ x, P x ∧ o = .ok x m [] :=
  Iff.rfl

private theorem pure_iff {A : Type} (x : A) (i : SyscallInput) (m : Model)
    (o : Outcome A Model event) :
    pure x i m o ↔ o = .ok x m [] :=
  Iff.rfl

/-! ### The decoded fields of a 16-byte `timeval` -/

/-- A `struct __kernel_old_timeval` as the kernel would have written it:
    `tv_sec = 3`, `tv_usec = 500000` (0x07a120), 16 bytes. -/
private def tvExample : List byte :=
  [3, 0, 0, 0, 0, 0, 0, 0, 0x20, 0xa1, 0x07, 0, 0, 0, 0, 0]

/-- The first 8 bytes decode as the seconds field. -/
example : tv_sec_of tvExample = 3 := by decide

/-- The second 8 bytes decode as the microseconds field. -/
example : tv_frac_of tvExample = 500000 := by decide

/-- And there are exactly the 16 bytes the predicate asks for. -/
example : tvExample.length = 16 := by decide

/-- The well-formed example passes. -/
example : timeval_ok_b tvExample = true := by decide

/-- `tv_usec = 10^6` is NOT normalized — the whole content of the
    second condition, which uses 10^6 and not `PosixTimers`' 10^9. -/
example : timeval_ok_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 1000000) = false := by
  decide

/-- `tv_usec = 999999` is the largest value that passes. -/
example : timeval_ok_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 8 999999) = true := by
  decide

/-- `tv_sec = KTIME_SEC_MAX` is refused: the third condition is strict,
    and the envelope is the SET path's, not the read path's. -/
example :
    timeval_ok_b (Z_to_le_bytes 8 KTIME_SEC_MAX ++ Z_to_le_bytes 8 0) = false := by
  decide

/-- One second below it passes — the boundary from the other side. -/
example :
    timeval_ok_b (Z_to_le_bytes 8 (KTIME_SEC_MAX - 1) ++ Z_to_le_bytes 8 0) = true := by
  decide

/-- 15 bytes is not a `timeval`: the length test is EXACTLY 16. -/
example : timeval_ok_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 7 500000) = false := by
  decide

/-- Nor is 17. -/
example : timeval_ok_b (Z_to_le_bytes 8 3 ++ Z_to_le_bytes 9 500000) = false := by
  decide

/-- The empty buffer is refused — the length test alone catches it. -/
example : timeval_ok_b [] = false := by decide

/-! ### The arms of `gettimeofday_spec`, in the order the comment argues -/

/-- A non-NULL `tz` is declined unconditionally, before anything else is
    looked at. -/
theorem gettimeofday_spec_unmodeled_tz (tv tz : word) (i : SyscallInput)
    (m : Model) (h : w_is0 tz = false) :
    gettimeofday_spec tv tz i m .unmodeled := by
  unfold gettimeofday_spec
  simp [h, unmodeled]

/-- A null `tv` is declined next: Linux writes nothing there and answers
    0, and the model declines rather than commit to that. -/
theorem gettimeofday_spec_unmodeled_tv (tv tz : word) (i : SyscallInput)
    (m : Model) (h : w_is0 tv = true) :
    gettimeofday_spec tv tz i m .unmodeled := by
  unfold gettimeofday_spec
  simp [h, unmodeled]

/-- A `tv` whose FIRST 8-byte store is refused is the -EFAULT arm: the
    range test on the whole 16 bytes failed, and the first `put_user`'s
    own 8-byte test failed too, so nothing was written. -/
theorem gettimeofday_spec_efault (tv tz : word) (i : SyscallInput)
    (m : Model) (htz : w_is0 tz = true) (htv : w_is0 tv = false)
    (hcopy : copy_bytes_map i.in_wmem tv 16 = none) (hok : access_okb tv 8 = false) :
    gettimeofday_spec tv tz i m (.ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  unfold gettimeofday_spec
  simp only [htz, htv, Bool.not_true, Bool.false_eq_true, ite_false, bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp [hcopy, hok, err_ret, ret_only, pure_iff]

/-- The torn band, and any destination not wholly mapped: the first store
    passes its own test but the 16-byte range does not, so the model
    declines instead of committing a half-written struct. -/
theorem gettimeofday_spec_unmodeled_torn (tv tz : word) (i : SyscallInput)
    (m : Model) (htz : w_is0 tz = true) (htv : w_is0 tv = false)
    (hcopy : copy_bytes_map i.in_wmem tv 16 = none) (hok : access_okb tv 8 = true) :
    gettimeofday_spec tv tz i m .unmodeled := by
  unfold gettimeofday_spec
  simp only [htz, htv, Bool.not_true, Bool.false_eq_true, ite_false, bind_unmodeled_iff,
    input_iff]
  refine Or.inr ⟨i, m, [], rfl, ?_⟩
  simp [hcopy, hok, unmodeled]

/-- THE WRITE EFFECT'S SHAPE, which is what the modeled path promises:
    exactly one 16-byte write at `tv`, a literal-zero return, no zeros,
    no unmaps, no copies, no copy-ins, the model untouched and no
    events.  The bytes written are constrained only by `timeval_ok_b` —
    the per-sample nondeterminism the `choose` above introduces. -/
theorem gettimeofday_spec_ok_shape {tv tz : word} {i : SyscallInput}
    {m m' : Model} {evs : List event} {eff : SyscallEffect}
    (htz : w_is0 tz = true) (htv : w_is0 tv = false)
    {bs0 : List byte} (hcopy : copy_bytes_map i.in_wmem tv 16 = some bs0)
    (h : gettimeofday_spec tv tz i m (.ok eff m' evs)) :
    ∃ bs : List byte,
      timeval_ok_b bs = true ∧
      eff.eff_ret = BitVec.ofInt 64 0 ∧
      eff.eff_writes = [(tv, bs)] ∧
      eff.eff_zeros = [] ∧
      eff.eff_unmaps = [] ∧
      eff.eff_copies = [] ∧
      eff.eff_copyins = [] ∧
      m' = m ∧
      evs = [] := by
  unfold gettimeofday_spec at h
  simp [htz, htv, bind_ok_iff, input_iff] at h
  obtain ⟨x, m1, evs1, ⟨rfl, rfl, rfl⟩, x1, hk, hevs⟩ := h
  simp only [List.nil_append] at hevs
  subst x1
  rw [hcopy] at hk
  simp [bind_ok_iff, choose_iff, pure_iff] at hk
  obtain ⟨bs, mw, evsw, ⟨z, hbs, hxz, hmw, hevsw⟩, y1, ⟨heff, hm', hy1⟩, hevs2⟩ := hk
  subst hxz
  subst hmw
  subst hevsw
  subst hm'
  subst hy1
  simp only [List.nil_append] at hevs2
  subst hevs2
  subst heff
  exact ⟨bs, hbs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The nondeterminism is real: any well-formed 16-byte `timeval` is an
    admissible write, so the modeled path is not accidentally pinned to
    one reading.  Read forwards, this is the same shape the lemma above
    reads backwards. -/
theorem gettimeofday_spec_ok_any (tv tz : word) (i : SyscallInput) (m : Model)
    (htz : w_is0 tz = true) (htv : w_is0 tv = false)
    {bs0 : List byte} (hcopy : copy_bytes_map i.in_wmem tv 16 = some bs0)
    (bs : List byte) (hbs : timeval_ok_b bs = true) :
    gettimeofday_spec tv tz i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [(tv, bs)] []) m []) := by
  unfold gettimeofday_spec
  simp only [htz, htv, Bool.not_true, Bool.false_eq_true, ite_false, bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hcopy, bind_ok_iff]
  refine ⟨bs, m, [], [], ?_, ?_, rfl⟩
  · exact choose_ok _ bs i m hbs
  · rfl

/-! ### The citation spelling

    Because `kernel/time/time.c` puts a file called `time` inside a directory called
    `time`. That works here for the same reason, and these two checks pin it: after
    opening `…Sys.Kernel`, the bare `Time.` prefix names this module's definitions.
    -/

section Citation

open LinuxSem.LinuxProcessSem.Sys.Kernel

example : word → word → SysSpec SyscallEffect := Time.gettimeofday_spec

example : List byte → Bool := Time.timeval_ok_b

end Citation

end LinuxSem.LinuxProcessSem.Sys.Kernel.Time
