/-
  * LinuxProcessSem.Checks.Sys.Fs.Timerfd — the timerfd_create (85) checker, and its proofs

  Answers to Linux [fs/timerfd.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); flags are read UNSIGNED (`(w.toNat : Int)`); the
  mask difference is `Sys.Fs.File.z_ldiff` (`a & ~b`), imported rather than
  redefined; the spec monad `Sys SyscallEffect` is
  `SysSpec SyscallEffect` (`MonadInstances`); and a branch test is a `Bool`
  equation (`==`, `||`, `!`).  `TFD_CREATE_FLAGS` and the five clock ids
  come from `Sys/Uapi.lean`.

  The gate is WRITTEN OUT here rather than taken from
  [Timerfd.timerfd_create_einval_b], and `gate_eq` below is what makes the
  repetition worth its cost: it forces this statement and the spec's to
  coincide.  Importing the spec's predicate would leave a wrong gate
  agreeing with itself, which is why [Checks/Sys/Kernel/Time/PosixTimers]
  restates its envelope bound instead of sharing it.  The written-out
  expression is the kernel's own text, and its disjunction is *flattened*
  where the spec's is right-nested: `gate_eq` splits the six comparisons,
  so it does not depend on the two files spelling the disjunction with the
  same associativity.  (The expression is factored into a private
  definition only so the proof can name it.)

  `gate_eq` generalizes each of the six comparisons to an opaque `Bool`,
  `cases` all six, and closes each of the 64 leaves by `rfl`.  The four
  theorems then split once on the assembled predicate, which is the spec's,
  and each leaf is one arm: the correspondence step is `arm_ok`, a
  `CheckUnmodeled`-vs-`CheckOk` equation is closed by `exact nomatch H`,
  and a leaf answers with `pure_ok` or `unmodeled_intro`.

  The accepted arm answers through [check_ret_only] and the spec's through
  `err_ret`, so the two directions of that correspondence and the spec's
  never-`unmodeled` fact are the same three private helpers the `Fcntl`,
  `Ioctl` and `Sync` checkers carry.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd

namespace LinuxSem.Checks.Sys.Fs.Timerfd

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxSem.Checks.Sys.Prelude

/-- The gate, WRITTEN OUT.  Linux writes

    `if ((flags & ~TFD_CREATE_FLAGS) || (clockid != CLOCK_MONOTONIC && …))`
    `  return -EINVAL;`

  (Linux v6.18.46, fs/timerfd.c, `SYSCALL_DEFINE2(timerfd_create)`), and
  this is that condition as a `Bool`: the flag residue is a TRUTHINESS
  test (`Z.ldiff` is `a & ~b`, and a nonzero bit anywhere takes the
  -EINVAL), and the clock id is the kernel's own five-way comparison.
  The two halves are disjuncts of ONE condition, so there is no ordering
  question between them and no "which errno wins".

  Note what the repetition does NOT buy, because the difference matters
  here more than usual: an identical MISTAKE made in both files still
  closes every proof.  `gate_eq` relates the checker to the spec and
  never either to Linux.  It does not show that the admitted set really
  is Linux's five. -/
private def timerfd_create_gate (clkid flags : word) : Bool :=
  !(z_ldiff (flags.toNat : Int) TFD_CREATE_FLAGS == 0) ||
    !((clkid.toNat : Int) == CLOCK_REALTIME ||
      (clkid.toNat : Int) == CLOCK_MONOTONIC ||
      (clkid.toNat : Int) == CLOCK_BOOTTIME ||
      (clkid.toNat : Int) == CLOCK_REALTIME_ALARM ||
      (clkid.toNat : Int) == CLOCK_BOOTTIME_ALARM)

/-- The timerfd_create (85) checker: -EINVAL when the kernel's gate is
    taken, `CheckUnmodeled` otherwise — the fail-closed decline that
    covers -EPERM (the alarm clocks), -ENOMEM, -EMFILE, -ENOENT or -ENODEV
    and the descriptor number.

    No -EINVAL is reachable on any of those, which is what makes the
    decline lose coverage WITHOUT losing precision: `timerfd_create`'s
    only `return -EINVAL` is the gate's, and every function it reaches
    after the gate returns something else (fs/file.c `alloc_fd`:
    -EMFILE; fs/anon_inodes.c `__anon_inode_getfile`: -ENOENT or -ENODEV;
    fs/file_table.c `alloc_file_pseudo`: allocation failures). -/
def check_timerfd_create (clkid flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if timerfd_create_gate clkid flags
  then check_ret_only eff (errno_ret EINVAL) m []
  else .CheckUnmodeled

/- =========================================================================
   Private lemma and helpers

   `gate_eq` states the gate equality as a lemma: both sides are Bool
   computations over the same six comparisons, so splitting all six —
   rather than the assembled condition — decides the equality whatever the
   two files' parenthesization.  The three helpers are the one-word arm
   correspondence, as in the `Fcntl` checker.
   ========================================================================= -/

/-- The restated gate and the spec's `timerfd_create_einval_b` coincide on
    every input, by exhaustive split of the six comparisons. -/
private theorem gate_eq (clkid flags : word) :
    timerfd_create_gate clkid flags = timerfd_create_einval_b clkid flags := by
  unfold timerfd_create_gate timerfd_create_einval_b
  generalize h1 : (z_ldiff (flags.toNat : Int) TFD_CREATE_FLAGS == 0) = a
  generalize h2 : ((clkid.toNat : Int) == CLOCK_REALTIME) = b
  generalize h3 : ((clkid.toNat : Int) == CLOCK_MONOTONIC) = c
  generalize h4 : ((clkid.toNat : Int) == CLOCK_BOOTTIME) = d
  generalize h5 : ((clkid.toNat : Int) == CLOCK_REALTIME_ALARM) = e
  generalize h6 : ((clkid.toNat : Int) == CLOCK_BOOTTIME_ALARM) = f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

/-- Checker → spec, for the one answered arm: an accepted
    `check_ret_only` *is* the spec's `err_ret` at that word. -/
private theorem arm_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    ret_only r i m (.ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  exact pure_ok _ i _

/-- Spec → checker, for the one answered arm. -/
private theorem arm_check_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : ret_only r i m (.ok eff m' evs)) :
    check_ret_only eff r m [] = .CheckOk m' evs := by
  obtain ⟨rfl, rfl, rfl⟩ := H
  simp [check_ret_only, bv_eqb_refl]

/-- No `ret_only` (hence no `err_ret`) answers `unmodeled`. -/
private theorem arm_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  exact nomatch H

/- =========================================================================
   The four lemmas
   ========================================================================= -/

/-- timerfd_create soundness, accepted: the -EINVAL the checker accepts is
    the spec's -EINVAL arm. -/
theorem check_timerfd_create_sound_ok (clkid flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_timerfd_create clkid flags eff m = .CheckOk m' evs) :
    timerfd_create_spec clkid flags i m (.ok eff m' evs) := by
  unfold check_timerfd_create at H
  unfold timerfd_create_spec
  rw [gate_eq clkid flags] at H
  by_cases hg : timerfd_create_einval_b clkid flags = true
  · simp only [ite_eq_left hg] at H ⊢
    exact arm_ok (errno_ret EINVAL) eff m m' evs i H
  · simp only [ite_eq_right hg] at H ⊢
    exact nomatch H

/-- timerfd_create soundness, declined: a `CheckUnmodeled` is the spec's
    `unmodeled` arm, which is what the gate's `false` selects. -/
theorem check_timerfd_create_sound_unmodeled (clkid flags : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_timerfd_create clkid flags eff m = .CheckUnmodeled) :
    timerfd_create_spec clkid flags i m .unmodeled := by
  unfold check_timerfd_create at H
  unfold timerfd_create_spec
  rw [gate_eq clkid flags] at H
  by_cases hg : timerfd_create_einval_b clkid flags = true
  · simp only [ite_eq_left hg] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · simp only [ite_eq_right hg] at H ⊢
    exact unmodeled_intro i m

/-- timerfd_create completeness, accepted: the spec's -EINVAL arm is
    accepted at the same word. -/
theorem check_timerfd_create_complete_ok (clkid flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : timerfd_create_spec clkid flags i m (.ok eff m' evs)) :
    check_timerfd_create clkid flags eff m = .CheckOk m' evs := by
  unfold timerfd_create_spec at H
  unfold check_timerfd_create
  rw [gate_eq clkid flags]
  by_cases hg : timerfd_create_einval_b clkid flags = true
  · simp only [ite_eq_left hg] at H ⊢
    exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
  · simp only [ite_eq_right hg] at H ⊢
    exact nomatch H

/-- timerfd_create completeness, declined: the spec's `unmodeled` arm is
    the checker's `CheckUnmodeled`. -/
theorem check_timerfd_create_complete_unmodeled (clkid flags : word)
    (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : timerfd_create_spec clkid flags i m .unmodeled) :
    check_timerfd_create clkid flags eff m = .CheckUnmodeled := by
  unfold timerfd_create_spec at H
  unfold check_timerfd_create
  rw [gate_eq clkid flags]
  by_cases hg : timerfd_create_einval_b clkid flags = true
  · simp only [ite_eq_left hg] at H ⊢
    exact absurd H (arm_ne_unmodeled _ i m)
  · simp only [ite_eq_right hg] at H ⊢

/- =========================================================================
   Sanity checks (not library lemmas)

   The module's proofs contain no `vm_compute` goal either — it is one
   definition, four proofs and the prose above.  The checks below pin the
   gate and the two arms against concrete words: the -EINVAL of a stray
   flag bit and of an unknown clock id, the decline of an admitted clock,
   and the shape (bare effect) of the accepted answer.  (`FdEntry` has no
   `DecidableEq`, so nothing here needs one: `timerfd_create_spec` reads
   no state, and the fixture model is only a carrier.)
   ========================================================================= -/

/-- A model for the checks: an empty fd table, an empty VM ledger, an
    empty file system, EOF on stdin, no halt.  `timerfd_create_spec` reads
    none of it. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- THE GATE, CLOCK ID BY ID: the five admitted ids pass it, and the ids
    `clock_gettime` answers but `timerfd_create` refuses fail it. -/
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_REALTIME) 0 = false := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 = false := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_BOOTTIME) 0 = false := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 0 = false := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_BOOTTIME_ALARM) 0 = false := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_PROCESS_CPUTIME_ID) 0 = true := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 (-1)) 0 = true := by decide

/-- THE FLAG RESIDUE IS A TRUTHINESS TEST, not a sign test: bit 0
    (`TFD_TIMER_ABSTIME`, `timerfd_settime`'s flag) is -EINVAL, bit 31
    (0x80000000, negative as a 32-bit `int`) is -EINVAL, and the admitted
    word passes. -/
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_MONOTONIC) 1 = true := by decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_MONOTONIC) 2147483648 = true := by
  decide
example : timerfd_create_gate (BitVec.ofInt 64 CLOCK_MONOTONIC) TFD_CREATE_FLAGS
    = false := by decide

/-- THE TWO HALVES ARE DISJUNCTS OF ONE CONDITION: bad flags together with
    an alarm clock is -EINVAL, never the -EPERM of the capability check
    below the gate. -/
example :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 1
      (mkEffect (errno_ret EINVAL) [] []) demoModel
      = check_ret_only (mkEffect (errno_ret EINVAL) [] []) (errno_ret EINVAL)
          demoModel [] := by
  rw [check_timerfd_create, ite_eq_left (by decide)]

/-- AN UNKNOWN CLOCK ID IS -EINVAL, the id `clock_gettime` answers
    included. -/
example (eff : SyscallEffect) :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_PROCESS_CPUTIME_ID) 0 eff demoModel
      = check_ret_only eff (errno_ret EINVAL) demoModel [] := by
  rw [check_timerfd_create, ite_eq_left (by decide)]

/-- WITH THE GATE PASSED THE ANSWER IS THE DECLINE, not an errno — the
    alarm clocks included, since -EINVAL is an errno Linux does not
    produce for them. -/
example (eff : SyscallEffect) :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_MONOTONIC) 0 eff demoModel
      = .CheckUnmodeled := by
  rw [check_timerfd_create, ite_eq_right (by decide)]
example (eff : SyscallEffect) :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_REALTIME_ALARM) 0 eff demoModel
      = .CheckUnmodeled := by
  rw [check_timerfd_create, ite_eq_right (by decide)]

/-- THE ANSWERED ARM ACCEPTS THE BARE -EINVAL EFFECT, and REJECTS anything
    whose shape is not that: the kernel's -EINVAL arm touches no memory
    and changes no state. -/
example :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_MONOTONIC) 1
      (mkEffect (errno_ret EINVAL) [] []) demoModel
      = .CheckOk demoModel [] := by
  rw [check_timerfd_create, ite_eq_left (by decide)]
  simp [check_ret_only, bv_eqb_refl]

example :
    check_timerfd_create (BitVec.ofInt 64 CLOCK_MONOTONIC) 1
      ⟨errno_ret EINVAL, [(0, [1])], [], [], [], []⟩ demoModel
      = .CheckReject := by
  rw [check_timerfd_create, ite_eq_left (by decide)]
  simp [check_ret_only]

/-- The errno word really is the kernel's number, and the admitted flag
    mask is `O_CLOEXEC | O_NONBLOCK` (526336). -/
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : TFD_CREATE_FLAGS = 526336 := by decide

end LinuxSem.Checks.Sys.Fs.Timerfd
