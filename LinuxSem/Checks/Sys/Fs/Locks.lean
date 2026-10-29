/-
  * LinuxProcessSem.Checks.Sys.Fs.Locks — the flock (32) checker, and its proofs

  Answers to Linux [fs/locks.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`).  Nothing here or in the matching witness reads
  `Fs.ReadWrite`, so neither imports it.

  Each proof peels the spec's model reader with `bind_getModel`, which
  rewrites `bind getModel k i m o` to `k i m o` in one go, so every proof
  unfolds the spec to the `bind` and then `rw [bind_getModel]`.  `dsimp only`
  reduces what follows, `exact nomatch H` eliminates a
  `CheckUnmodeled = CheckOk` equation, and a branch equation is rewritten
  with `rw [hfd]`.

  The four `FdFile*` arms share one script: they differ only in the
  constructor tag and all four bind `p` the same way, but Lean's `cases`
  splits them apart, so the shared script is wrapped in a `first` whose
  second branch is the six-arm decline — for a file arm the first branch
  runs (its `p` is in scope), and for the six non-file arms that `p` does
  not elaborate, the branch fails, and `first` falls through to
  `exact nomatch H`.  `set_option autoImplicit false` below is what keeps
  that an error instead of an auto-bound variable.

  `flock_spec` is a `SysSpec`, a FUNCTION, so its body is a chain of `if`s
  at function type; Lean normalises such a goal by trying to decide them,
  which is why each proof first `generalize`s its conclusion into a local
  `Q : Prop` and rewrites `Q` back at the leaves with `rw [← hP]`, as in
  `Checks/Sys/Kernel/Groups.lean`.  (The flock tests themselves get stuck on
  `cmd.toNat` where a literal `sint32` now reduces, so the device is only
  needed for the uniformity of the four scripts.)
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Locks

set_option autoImplicit false

namespace LinuxSem.Checks.Sys.Fs.Locks

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Prelude

/-- flock: a LOCK_MAND word answers 0 without reading the fd, an
    unrecognized operation answers -EINVAL still without reading it, a
    closed fd is then -EBADF, an unlock on any open fd is 0, and a
    shared or exclusive request is 0 only on a file descriptor whose
    path no other descriptor names. -/
def check_flock (fd cmd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if flock_mand_b cmd then check_ret_only eff (BitVec.ofInt 64 0) m []
  else if !(flock_cmd_ok_b cmd) then check_ret_only eff (errno_ret EINVAL) m []
  else
    match fd_lookup (m_fds m) fd with
    | none => check_ret_only eff (errno_ret EBADF) m []
    | some e =>
        if flock_unlock_b cmd then check_ret_only eff (BitVec.ofInt 64 0) m []
        else
          match e with
          | FdEntry.FdFile p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (BitVec.ofInt 64 0) m []
              else .CheckUnmodeled
          | FdEntry.FdFileW p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (BitVec.ofInt 64 0) m []
              else .CheckUnmodeled
          | FdEntry.FdFileA p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (BitVec.ofInt 64 0) m []
              else .CheckUnmodeled
          | FdEntry.FdFileRW p _ =>
              if flock_sole_opener (m_fds m) p
              then check_ret_only eff (BitVec.ofInt 64 0) m []
              else .CheckUnmodeled
          | FdEntry.FdChannel _ => .CheckUnmodeled
          | FdEntry.FdDir       => .CheckUnmodeled
          | FdEntry.FdSocket _  => .CheckUnmodeled
          | FdEntry.FdPipe _ _  => .CheckUnmodeled
          | FdEntry.FdDevNull _ _ => .CheckUnmodeled
          | FdEntry.FdUrandom => .CheckUnmodeled

/-! ## The four directions

    The two cmd-only tests come first, then the descriptor, then the
    unlock test, then the entry — the kernel's order, and the order both
    the spec and the checker use.  The proofs keep that order too:
    `hmand`, `hok`, `hfd`, `hun`, and finally the
    sole-opener gate.  The four `FdFile*` arms are one script under
    `all_goals` (see the header's note); the six non-file arms —
    `FdChannel`, `FdDir`, `FdSocket`, `FdPipe`, and the two device nodes
    `/dev/null` and `/dev/urandom`, each declined for the reason
    [Sys.Fs.Locks.flock_spec] gives — answer `.CheckUnmodeled` /
    `unmodeled` and close with `nomatch H` in the accept direction.

    The two cmd-only tests mention neither the descriptor nor the model the
    `bind` introduces, so their split rewrites the goal's own copy, while
    the two that read `m` need the branch equation propagated into the goal
    — the asymmetry that is why the arms are not one uniform script.  The
    cmd-only tests are `simp only [ite_eq_left/ite_eq_right …] at H`, and `hfd` is a
    `simp` argument in the goal because the spec's own `match` has to be
    rewritten there. -/

theorem check_flock_sound_ok (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_flock fd cmd eff m = .CheckOk m' evs) :
    flock_spec fd cmd i m (.ok eff m' evs) := by
  generalize hP : (flock_spec fd cmd i m (.ok eff m' evs)) = Q at *
  unfold check_flock at H
  by_cases hmand : flock_mand_b cmd = true
  · simp only [ite_eq_left hmand] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
    rw [← hP]
    simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_left hmand, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hmand] at H
    by_cases hok : (!(flock_cmd_ok_b cmd)) = true
    · simp only [ite_eq_left hok] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [← hP]
      simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand, ite_eq_left hok,
        err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hok] at H
      cases hfd : fd_lookup (m_fds m) fd with
      | none =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
        rw [← hP]
        simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand, ite_eq_right hok,
          hfd, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      | some e =>
        rcases e with ⟨c⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | _ | ⟨sk⟩ | ⟨id, w⟩
          | ⟨rd, wr⟩ | _
        all_goals
          (simp only [hfd] at H
           by_cases hun : flock_unlock_b cmd = true
           · simp only [ite_eq_left hun] at H
             obtain ⟨rfl, rfl, rfl⟩ :=
               (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
             rw [← hP]
             simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand,
               ite_eq_right hok, hfd, ite_eq_left hun, ret_only,
               LinuxSem.LinuxProcessSem.pure]
           · simp only [ite_eq_right hun] at H
             first
             | (by_cases hsole : flock_sole_opener (m_fds m) p = true
                · simp only [ite_eq_left hsole] at H
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
                  rw [← hP]
                  simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand,
                    ite_eq_right hok, hfd, ite_eq_right hun, ite_eq_left hsole, ret_only,
                    LinuxSem.LinuxProcessSem.pure]
                · simp only [ite_eq_right hsole] at H
                  exact nomatch H)
             | exact nomatch H)

theorem check_flock_sound_unmodeled (fd cmd : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_flock fd cmd eff m = .CheckUnmodeled) :
    flock_spec fd cmd i m .unmodeled := by
  generalize hP : (flock_spec fd cmd i m .unmodeled) = Q at *
  unfold check_flock at H
  by_cases hmand : flock_mand_b cmd = true
  · simp only [ite_eq_left hmand] at H
    exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
  · simp only [ite_eq_right hmand] at H
    by_cases hok : (!(flock_cmd_ok_b cmd)) = true
    · simp only [ite_eq_left hok] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · simp only [ite_eq_right hok] at H
      cases hfd : fd_lookup (m_fds m) fd with
      | none =>
        simp only [hfd] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      | some e =>
        rcases e with ⟨c⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | _ | ⟨sk⟩ | ⟨id, w⟩
          | ⟨rd, wr⟩ | _
        all_goals
          (simp only [hfd] at H
           by_cases hun : flock_unlock_b cmd = true
           · simp only [ite_eq_left hun] at H
             exact absurd H
               (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
           · simp only [ite_eq_right hun] at H
             first
             | (by_cases hsole : flock_sole_opener (m_fds m) p = true
                · simp only [ite_eq_left hsole] at H
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
                · simp only [ite_eq_right hsole] at H
                  rw [← hP]
                  simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand,
                    ite_eq_right hok, hfd, ite_eq_right hun, ite_eq_right hsole, unmodeled])
             | (rw [← hP]
                simp only [flock_spec, getModelSpec, bind_getModel, ite_eq_right hmand,
                  ite_eq_right hok, hfd, ite_eq_right hun, unmodeled]))

theorem check_flock_complete_ok (fd cmd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : flock_spec fd cmd i m (.ok eff m' evs)) :
    check_flock fd cmd eff m = .CheckOk m' evs := by
  generalize hP : (check_flock fd cmd eff m = .CheckOk m' evs) = Q at *
  unfold flock_spec getModelSpec at H
  rw [bind_getModel] at H
  by_cases hmand : flock_mand_b cmd = true
  · simp only [ite_eq_left hmand] at H
    simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_flock, ite_eq_left hmand]
    simp [check_ret_only, bv_eqb_refl]
  · simp only [ite_eq_right hmand] at H
    by_cases hok : (!(flock_cmd_ok_b cmd)) = true
    · simp only [ite_eq_left hok] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      rw [← hP]
      simp only [check_flock, ite_eq_right hmand, ite_eq_left hok]
      simp [check_ret_only, bv_eqb_refl]
    · simp only [ite_eq_right hok] at H
      cases hfd : fd_lookup (m_fds m) fd with
      | none =>
        simp only [hfd] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        rw [← hP]
        simp only [check_flock, ite_eq_right hmand, ite_eq_right hok, hfd]
        simp [check_ret_only, bv_eqb_refl]
      | some e =>
        rcases e with ⟨c⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | _ | ⟨sk⟩ | ⟨id, w⟩
          | ⟨rd, wr⟩ | _
        all_goals
          (simp only [hfd] at H
           by_cases hun : flock_unlock_b cmd = true
           · simp only [ite_eq_left hun] at H
             simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
               Outcome.ok.injEq] at H
             obtain ⟨rfl, rfl, rfl⟩ := H
             rw [← hP]
             simp only [check_flock, ite_eq_right hmand, ite_eq_right hok, hfd, ite_eq_left hun]
             simp [check_ret_only, bv_eqb_refl]
           · simp only [ite_eq_right hun] at H
             first
             | (by_cases hsole : flock_sole_opener (m_fds m) p = true
                · simp only [ite_eq_left hsole] at H
                  simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
                    Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  rw [← hP]
                  simp only [check_flock, ite_eq_right hmand, ite_eq_right hok, hfd,
                    ite_eq_right hun, ite_eq_left hsole]
                  simp [check_ret_only, bv_eqb_refl]
                · simp only [ite_eq_right hsole] at H
                  simp only [unmodeled] at H
                  exact nomatch H)
             | (simp only [unmodeled] at H
                exact nomatch H))

theorem check_flock_complete_unmodeled (fd cmd : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : flock_spec fd cmd i m .unmodeled) :
    check_flock fd cmd eff m = .CheckUnmodeled := by
  generalize hP : (check_flock fd cmd eff m = .CheckUnmodeled) = Q at *
  unfold flock_spec getModelSpec at H
  rw [bind_getModel] at H
  by_cases hmand : flock_mand_b cmd = true
  · simp only [ite_eq_left hmand] at H
    simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · simp only [ite_eq_right hmand] at H
    by_cases hok : (!(flock_cmd_ok_b cmd)) = true
    · simp only [ite_eq_left hok] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · simp only [ite_eq_right hok] at H
      cases hfd : fd_lookup (m_fds m) fd with
      | none =>
        simp only [hfd] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      | some e =>
        rcases e with ⟨c⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | ⟨p, o⟩ | _ | ⟨sk⟩ | ⟨id, w⟩
          | ⟨rd, wr⟩ | _
        all_goals
          (simp only [hfd] at H
           by_cases hun : flock_unlock_b cmd = true
           · simp only [ite_eq_left hun] at H
             exact absurd H (ret_only_ne_unmodeled _ i m)
           · simp only [ite_eq_right hun] at H
             first
             | (by_cases hsole : flock_sole_opener (m_fds m) p = true
                · simp only [ite_eq_left hsole] at H
                  exact absurd H (ret_only_ne_unmodeled _ i m)
                · simp only [ite_eq_right hsole] at H
                  rw [← hP]
                  simp only [check_flock, ite_eq_right hmand, ite_eq_right hok, hfd,
                    ite_eq_right hun, ite_eq_right hsole]
                  try rfl)
             | (rw [← hP]
                simp only [check_flock, ite_eq_right hmand, ite_eq_right hok, hfd, ite_eq_right hun]
                try rfl))

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal — it is four small
    predicates, two table functions and the spec.  These pin the ARMS of
    [check_flock] IN THE KERNEL'S ORDER against a concrete fd table:
    LOCK_MAND is 0 even on a closed fd, a bad operation is -EINVAL before
    the descriptor is read, a closed fd is -EBADF, a lock on a sole
    opener is 0, a lock on a doubled path declines, an unlock is 0 even
    on that path, and a non-file kind declines.

    `check_result` has no `DecidableEq`, so each states the branch as an
    equation and closes it by unfolding the checker and discharging the
    branch tests by name.  A scrutinee rewrite that also re-reduces the
    `match` it unblocks needs the `dsimp only` after it, for the reason the
    checker's header gives. -/

/-- The path `out` for the table checks. -/
private def outPath : Fs.path := [0x6f, 0x75, 0x74]

/-- The path `dup` for the table checks. -/
private def dupPath : Fs.path := [0x64, 0x75, 0x70]

/-- A tiny fd table: 0 a channel, 1 a regular file (`out`), 2 a
    directory, and 3 and 4 two regular files naming the SAME path
    (`dup`). -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile outPath 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdFile dupPath 0),
    (4, FdEntry.FdFileW dupPath 5) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- `path_openers` counts both file constructors by path: `out` is named
    once, `dup` twice. -/
example : path_openers demoFds outPath = 1 := by decide

example : path_openers demoFds dupPath = 2 := by decide

/-- …which is what the sole-opener gate asks. -/
example : flock_sole_opener demoFds outPath = true := by decide

example : flock_sole_opener demoFds dupPath = false := by decide

/-- LOCK_MAND returns 0 without reading the fd: even a closed one. -/
example (eff : SyscallEffect) :
    check_flock 9 32 eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 0) demoModel [] := by
  unfold check_flock
  rw [ite_eq_left (by decide : flock_mand_b (32 : word) = true)]

/-- An unrecognized operation is -EINVAL, decided before the descriptor:
    `flock(-1, 0)`. -/
example (eff : SyscallEffect) :
    check_flock 9 0 eff demoModel
      = check_ret_only eff (errno_ret EINVAL) demoModel [] := by
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (0 : word) = true)),
    ite_eq_left (by decide : (!(flock_cmd_ok_b (0 : word))) = true)]

/-- A missing fd is -EBADF. -/
example (eff : SyscallEffect) :
    check_flock 9 2 eff demoModel
      = check_ret_only eff (errno_ret EBADF) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true)), hlook]

/-- A LOCK_EX on a regular file no other descriptor names returns 0 — the
    one arm whose grant rests on a premise about the world. -/
example (eff : SyscallEffect) :
    check_flock 1 2 eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 0) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some (FdEntry.FdFile outPath 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, outPath, fd_lookup]
  have hsole : flock_sole_opener (m_fds demoModel) outPath = true := by decide
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true)), ite_eq_left hsole]

/-- A SECOND OPENER IS REFUSED, not answered 0: fd 3's path `dup` is also
    named by fd 4, so the model cannot tell whether a conflicting
    `struct file` holds the lock. -/
example (eff : SyscallEffect) : check_flock 3 2 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 3 = some (FdEntry.FdFile dupPath 0) := by
    simp [m_fds, demoModel, mkModel, demoFds, dupPath, fd_lookup]
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true)),
    ite_eq_right (by decide : ¬(flock_sole_opener (m_fds demoModel) dupPath = true))]

/-- AN UNLOCK IS 0 UNCONDITIONALLY, even on `dup`, the path with a second
    opener. -/
example (eff : SyscallEffect) :
    check_flock 4 8 eff demoModel
      = check_ret_only eff (BitVec.ofInt 64 0) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 4 = some (FdEntry.FdFileW dupPath 5) := by
    simp [m_fds, demoModel, mkModel, demoFds, dupPath, fd_lookup]
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (8 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (8 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_left (by decide : flock_unlock_b (8 : word) = true)]

/-- A channel declines: the object is not in the model. -/
example (eff : SyscallEffect) : check_flock 0 2 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true))]

/-- …and so does a directory reference. -/
example (eff : SyscallEffect) : check_flock 2 2 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 2 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_flock
  rw [ite_eq_right (by decide : ¬(flock_mand_b (2 : word) = true)),
    ite_eq_right (by decide : ¬((!(flock_cmd_ok_b (2 : word))) = true))]
  rw [hlook]
  dsimp only
  rw [ite_eq_right (by decide : ¬(flock_unlock_b (2 : word) = true))]

/-- The two errnos really are the kernel's numbers in the return word, and
    the success return really is the zero word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide
example : (mkEffect (BitVec.ofInt 64 0) [] []).eff_ret = 0 := rfl

end LinuxSem.Checks.Sys.Fs.Locks

