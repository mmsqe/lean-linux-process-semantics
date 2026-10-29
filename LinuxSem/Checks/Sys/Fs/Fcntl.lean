/-
  * LinuxProcessSem.Checks.Sys.Fs.Fcntl — the fcntl (25) checker, and its proofs

  Answers to Linux [fs/fcntl.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); the spec monad `Sys SyscallEffect` is
  `SysSpec SyscallEffect` (`MonadInstances`); and bitvector equality is
  `Riscv.Prelude.bv_eqb` (`==` on bitvectors).  The three command words
  `F_SETFD` / `F_SETFL` / `F_GETFL` come from `Sys/Uapi.lean`, and the two
  fd-kind predicates — `setfl_noop_on`, `getfl_f_flags` — are the spec's own,
  so the checker tests exactly what the spec tests.

  A scrutinee is split by
  `generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢` + `cases e`;
  `getfl_f_flags e` gets the same move, which spares a case split on the
  eleven `FdEntry` constructors.  The three nested `bv_eqb` tests are
  `by_cases` on the `Bool` equation plus `simp only [ite_eq_left …]` /
  `[ite_eq_right …]` on both the hypothesis and the goal — the checker's `if` is
  at *function* type on the spec's side, so this is the one split to do with
  the condition, never with the narrowed `SysSpec`.
  `refine bind_ok0 getModelSpec _ … rfl ?_` peels the model reader and
  `exact pure_ok _ i _` closes a pure leaf.  `sys_unfold` is not needed:
  `fcntl_spec`'s only prologue is `getModelSpec`, so `bind_model_inv` peels
  it and leaves the fd match.

  Every answered arm answers through `check_ret_only` at one word while the
  spec's matching arm is `ret_only`/`err_ret` at the same word, so the
  `check_ret_only_ok_iff` step is stated once below as `arm_ok`,
  `arm_check_ok` and `arm_ne_unmodeled` — private helpers with no public
  surface, and the same three the `Ioctl` and `Sync` checkers carry.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl

namespace LinuxSem.Checks.Sys.Fs.Fcntl

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Fcntl
open LinuxSem.Checks.Sys.Prelude

/-- fcntl: a closed fd is -EBADF whatever the command; on an open one
    F_SETFD answers 0 for any arg, an F_SETFL that provably changes
    nothing answers 0, F_GETFL answers the flag word on the fd kinds
    [Fcntl.getfl_f_flags] can derive it for, and every other command is
    unmodeled.

    The fd is resolved FIRST, before `cmd` is examined, which is why the
    -EBADF arm sits outside the three command tests: Linux's
    `SYSCALL_DEFINE3(fcntl, …)` runs `fdget_raw(fd)` and returns -EBADF
    before `do_fcntl` looks at the command (fs/fcntl.c, v6.10–v6.15),
    and `fcntl_spec` arms in the same order.  The four answers below
    mirror the spec's four arms one for one, so the checker neither
    accepts nor declines an effect the spec would not. -/
def check_fcntl (fd cmd arg : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if bv_eqb cmd F_SETFD then check_ret_only eff (BitVec.ofInt 64 0) m []
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then check_ret_only eff (BitVec.ofInt 64 0) m []
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => check_ret_only eff fl m []
        | none => .CheckUnmodeled
      else .CheckUnmodeled

/- =========================================================================
   Private helpers: the one-word arm correspondence

   `check_fcntl` accepts exactly four words — `errno_ret EBADF`, 0 (twice)
   and `fl` — and each is the spec's `ret_only` at the same word.  The
   four theorems would spell the `check_ret_only_ok_iff` inversion out in
   every branch; here it is done twice.
   ========================================================================= -/

/-- Checker → spec, for one arm: an accepted `check_ret_only` *is* the
    spec's `ret_only` at that word, with the claimed model and events. -/
private theorem arm_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    ret_only r i m (.ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  exact pure_ok _ i _

/-- Spec → checker, for one arm: an outcome of the spec's `ret_only` at
    that word is accepted by `check_ret_only` at the same word. -/
private theorem arm_check_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : ret_only r i m (.ok eff m' evs)) :
    check_ret_only eff r m [] = .CheckOk m' evs := by
  obtain ⟨rfl, rfl, rfl⟩ := H
  simp [check_ret_only, bv_eqb_refl]

/-- No `ret_only` (hence no `err_ret`) answers `unmodeled`: the only
    outcome shape of `pure` is `.ok … []`. -/
private theorem arm_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  exact nomatch H

/- =========================================================================
   The four lemmas
   ========================================================================= -/

/-- fcntl soundness, accepted: every accepted effect is one the spec
    admits.  The four answered arms are `ret_only` at the very word the
    checker writes; the two `CheckUnmodeled` arms are excluded by the
    hypothesis. -/
theorem check_fcntl_sound_ok (fd cmd arg : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_fcntl fd cmd arg eff m = .CheckOk m' evs) :
    fcntl_spec fd cmd arg i m (.ok eff m' evs) := by
  unfold check_fcntl at H
  unfold fcntl_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    -- a closed fd: -EBADF, before the command is examined
    dsimp only at H ⊢
    exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    dsimp only at H ⊢
    by_cases hd : bv_eqb cmd F_SETFD = true
    · -- F_SETFD answers 0 for any arg
      simp only [ite_eq_left hd] at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
    · simp only [ite_eq_right hd] at H ⊢
      by_cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) = true
      · -- a provably empty F_SETFL answers 0
        simp only [ite_eq_left hl] at H ⊢
        exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · simp only [ite_eq_right hl] at H ⊢
        by_cases hg : bv_eqb cmd F_GETFL = true
        · simp only [ite_eq_left hg] at H ⊢
          -- F_GETFL answers `fl` where `getfl_f_flags` derives one, declines otherwise
          generalize hfl : getfl_f_flags e = fl at H ⊢
          cases fl with
          | none => exact nomatch H
          | some fl => exact arm_ok fl eff m m' evs i H
        · -- every other command is unmodeled: the checker cannot accept
          simp only [ite_eq_right hg] at H ⊢
          exact nomatch H

/-- fcntl soundness, declined: a `CheckUnmodeled` is exactly the spec's
    `unmodeled`.  The four answered arms are `ret_only`, which never
    declines, so each of them closes by contradiction. -/
theorem check_fcntl_sound_unmodeled (fd cmd arg : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_fcntl fd cmd arg eff m = .CheckUnmodeled) :
    fcntl_spec fd cmd arg i m .unmodeled := by
  unfold check_fcntl at H
  unfold fcntl_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    dsimp only at H ⊢
    by_cases hd : bv_eqb cmd F_SETFD = true
    · simp only [ite_eq_left hd] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    · simp only [ite_eq_right hd] at H ⊢
      by_cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) = true
      · simp only [ite_eq_left hl] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · simp only [ite_eq_right hl] at H ⊢
        by_cases hg : bv_eqb cmd F_GETFL = true
        · simp only [ite_eq_left hg] at H ⊢
          generalize hfl : getfl_f_flags e = fl at H ⊢
          cases fl with
          | none =>
            -- the F_GETFL decline is the spec's `unmodeled` arm
            exact unmodeled_intro i m
          | some fl =>
            exact absurd H (check_ret_only_no_unmodeled eff fl m [])
        · -- every other command: the spec declines, the checker declines
          simp only [ite_eq_right hg] at H ⊢
          exact unmodeled_intro i m

/-- fcntl completeness, accepted: every accepted spec outcome is accepted
    by the checker.  `bind_model_inv` peels the spec's single `getModelSpec`
    reader (the `sys_unfold` step for a spec with no setters). -/
theorem check_fcntl_complete_ok (fd cmd arg : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : fcntl_spec fd cmd arg i m (.ok eff m' evs)) :
    check_fcntl fd cmd arg eff m = .CheckOk m' evs := by
  unfold check_fcntl
  simp only [fcntl_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    dsimp only at H ⊢
    by_cases hd : bv_eqb cmd F_SETFD = true
    · simp only [ite_eq_left hd] at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
    · simp only [ite_eq_right hd] at H ⊢
      by_cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) = true
      · simp only [ite_eq_left hl] at H ⊢
        exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · simp only [ite_eq_right hl] at H ⊢
        by_cases hg : bv_eqb cmd F_GETFL = true
        · simp only [ite_eq_left hg] at H ⊢
          generalize hfl : getfl_f_flags e = fl at H ⊢
          cases fl with
          | none => exact nomatch H
          | some fl => exact arm_check_ok fl eff m m' evs i H
        · simp only [ite_eq_right hg] at H ⊢
          exact nomatch H

/-- fcntl completeness, declined: every `unmodeled` spec outcome is the
    checker's `CheckUnmodeled`. -/
theorem check_fcntl_complete_unmodeled (fd cmd arg : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : fcntl_spec fd cmd arg i m .unmodeled) :
    check_fcntl fd cmd arg eff m = .CheckUnmodeled := by
  unfold check_fcntl
  simp only [fcntl_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (arm_ne_unmodeled _ i m)
  | some e =>
    dsimp only at H ⊢
    by_cases hd : bv_eqb cmd F_SETFD = true
    · simp only [ite_eq_left hd] at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    · simp only [ite_eq_right hd] at H ⊢
      by_cases hl : (bv_eqb cmd F_SETFL && setfl_noop_on e arg) = true
      · simp only [ite_eq_left hl] at H ⊢
        exact absurd H (arm_ne_unmodeled _ i m)
      · simp only [ite_eq_right hl] at H ⊢
        by_cases hg : bv_eqb cmd F_GETFL = true
        · simp only [ite_eq_left hg] at H ⊢
          generalize hfl : getfl_f_flags e = fl at H ⊢
          cases fl with
          | none => rfl
          | some fl => exact absurd H (arm_ne_unmodeled _ i m)
        · simp only [ite_eq_right hg] at H ⊢

/- =========================================================================
   Sanity checks (not library lemmas)

   The module's proofs leave no `vm_compute` goal — it is one
   definition, four proofs and the prose above.  The checks below pin the
   four answers against a concrete fd table: -EBADF on a closed fd (before
   the command is read), 0 for F_SETFD whatever the arg, 0 for a provably
   empty F_SETFL, `O_RDWR` for F_GETFL on a socket — and a decline for
   every command the spec declines and for the fd kinds the flag word is
   not derivable on.  `check_result` and `Outcome` carry no `DecidableEq`,
   so each check states the expected shape as an equation.
   ========================================================================= -/

/-- The model the checks run in: a regular file on fd 3, a pipe read end
    on fd 4 and a socket on fd 5; fd 9 is absent.  (The same fixture
    `Sys/Fs/Fcntl.lean`'s own checks use.) -/
private def demoModel : Model :=
  mkModel
    [(BitVec.ofNat 64 3, FdEntry.FdFile [] (BitVec.ofInt 64 0)),
     (BitVec.ofNat 64 4, FdEntry.FdPipe (BitVec.ofNat 64 0) false),
     (BitVec.ofNat 64 5, FdEntry.FdSocket SockState.SkFresh)]
    (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The fd table, without unfolding the whole `Model` (whose `NetStream`
    field has no decidable equality). -/
private theorem demoModel_fds :
    m_fds demoModel =
      [(BitVec.ofNat 64 3, FdEntry.FdFile [] (BitVec.ofInt 64 0)),
       (BitVec.ofNat 64 4, FdEntry.FdPipe (BitVec.ofNat 64 0) false),
       (BitVec.ofNat 64 5, FdEntry.FdSocket SockState.SkFresh)] := rfl

/-- A CLOSED FD IS -EBADF, whatever the command: the fd is resolved first,
    so `fcntl(9, ⟨unknown⟩, 0)` is the descriptor error rather than an
    unmodeled decline. -/
example (cmd arg : word) (eff : SyscallEffect) :
    check_fcntl 9 cmd arg eff demoModel
      = check_ret_only eff (errno_ret EBADF) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]

/-- F_SETFD ANSWERS 0 FOR ANY ARG, on every open fd kind: only bit 0 is
    consulted and there is no error path, so `0xdeadbeef` is a success. -/
example (eff : SyscallEffect) :
    check_fcntl 3 F_SETFD (BitVec.ofNat 64 0xdeadbeef) eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 0) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_left (by decide : bv_eqb F_SETFD F_SETFD = true)]

/-- A PROVABLY EMPTY F_SETFL ANSWERS 0 on a regular file — `arg = 0` names
    none of the five status bits. -/
example (eff : SyscallEffect) :
    check_fcntl 3 F_SETFL 0 eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 0) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_SETFL F_SETFD = true))]
  rw [ite_eq_left (by decide : (bv_eqb F_SETFL F_SETFL && setfl_noop_on
    (FdEntry.FdFile [] (BitVec.ofInt 64 0)) 0) = true)]

/-- F_GETFL ON THE SOCKET ANSWERS THE WHOLE OF ITS `f_flags`, `O_RDWR` (2)
    — and on the file and the pipe end it DECLINES, for the two different
    reasons the spec's `getfl_f_flags` separates. -/
example (eff : SyscallEffect) :
    check_fcntl 5 F_GETFL 0 eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 O_RDWR) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 5
      = some (FdEntry.FdSocket SockState.SkFresh) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFL F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFL F_SETFL && setfl_noop_on
    (FdEntry.FdSocket SockState.SkFresh) 0) = true))]
  rw [ite_eq_left (by decide : bv_eqb F_GETFL F_GETFL = true)]
  rfl

example (eff : SyscallEffect) :
    check_fcntl 3 F_GETFL 0 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFL F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFL F_SETFL && setfl_noop_on
    (FdEntry.FdFile [] (BitVec.ofInt 64 0)) 0) = true))]
  rw [ite_eq_left (by decide : bv_eqb F_GETFL F_GETFL = true)]
  rfl

example (eff : SyscallEffect) :
    check_fcntl 4 F_GETFL 0 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 4
      = some (FdEntry.FdPipe (BitVec.ofNat 64 0) false) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFL F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFL F_SETFL && setfl_noop_on
    (FdEntry.FdPipe (BitVec.ofNat 64 0) false) 0) = true))]
  rw [ite_eq_left (by decide : bv_eqb F_GETFL F_GETFL = true)]
  rfl

/-- EVERY OTHER COMMAND DECLINES on an open fd — `F_GETFD` (1) and
    `F_DUPFD` (0) are the two the spec names, and an unknown word is
    declined the same way. -/
example (eff : SyscallEffect) :
    check_fcntl 5 F_GETFD 0 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 5
      = some (FdEntry.FdSocket SockState.SkFresh) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFD F_SETFD = true))]
  rw [ite_eq_right (by decide : ¬((bv_eqb F_GETFD F_SETFL && setfl_noop_on
    (FdEntry.FdSocket SockState.SkFresh) 0) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb F_GETFD F_GETFL = true))]

/-- THE ANSWERED ARM ACCEPTS EXACTLY THE BARE EFFECT: one return word and
    no write, zero, unmap, copy or copy-in, which is what makes the
    command modeled at all.  A write alongside the 0 is REJECTED. -/
example :
    check_fcntl 3 F_SETFD 0 (mkEffect (BitVec.ofInt 64 0) [] []) demoModel
      = .CheckOk demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_left (by decide : bv_eqb F_SETFD F_SETFD = true)]
  simp [check_ret_only, bv_eqb_refl]

example :
    check_fcntl 3 F_SETFD 0
      ⟨BitVec.ofInt 64 0, [(0, [1])], [], [], [], []⟩ demoModel
      = .CheckReject := by
  have hlook : fd_lookup (m_fds demoModel) 3
      = some (FdEntry.FdFile [] (BitVec.ofInt 64 0)) := by
    rw [demoModel_fds]
    simp [fd_lookup]
  simp only [check_fcntl, hlook]
  rw [ite_eq_left (by decide : bv_eqb F_SETFD F_SETFD = true)]
  simp [check_ret_only]

/-- The two errno words this file answers with really are the kernel's
    numbers in the return word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : O_RDWR = 2 := by decide

end LinuxSem.Checks.Sys.Fs.Fcntl
