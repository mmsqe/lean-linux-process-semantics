/-
  * LinuxProcessSem.Checks.Sys.Fs.Sync — the fsync (82), fdatasync (83) checkers, and their proofs

  Answers to Linux [fs/sync.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and the spec monad `Sys SyscallEffect` is
  `SysSpec SyscallEffect` (`MonadInstances`).  `check_ret_only` takes
  (effect, return word, post-state, events), and the fd table is
  `m_fds m : List (word × FdEntry)` with `fd_lookup` from `StateFd`, as in
  the spec.

  The eleven-armed `match` on the fd entry is made to reduce by
  `generalize … at H ⊢` followed by `cases`, with `dsimp only at H ⊢` after
  each split, since the `match` on a generalized scrutinee does not reduce
  on its own.  `refine bind_ok0 getModelSpec _ … rfl ?_` peels the model
  reader, its `rfl` being `getModel_ok` by definition, and
  `exact pure_ok _ i _` closes a pure leaf.  The two `_unmodeled` lemmas
  are discharged by ruling the hypothesis out rather than by exhibiting a
  run: `check_ret_only` has no `CheckUnmodeled` answer — the fact
  `check_ret_only_no_unmodeled` states — and `fsync_spec` has no
  `unmodeled` arm, so `exact nomatch H` closes the branch.

  The ten open-fd arms of `check_fsync` differ only in the word they
  answer, so the two directions of the `check_ret_only` correspondence —
  and the fact that a `ret_only` arm never answers `unmodeled` — are
  stated once, as `arm_ok`, `arm_check_ok` and `arm_ne_unmodeled`, instead
  of being spelled out in each of the forty-four arm proofs.  They add no
  public surface.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Sync

namespace LinuxSem.Checks.Sys.Fs.Sync

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Prelude

/-- The `fsync` (82) / `fdatasync` (83) checker: one arm per `FdEntry`,
    exactly as `fsync_spec` enumerates them.

    - a closed fd is -EBADF, and the lookup is what decides it: the fd is
      resolved before the object is examined (`do_fsync`'s `fdget`);
    - the five kinds that carry no `.fsync` in their operations table
      (channel, socket, pipe, `/dev/null`, `/dev/urandom`) are -EINVAL;
    - a file, whatever its access mode, and a directory answer 0.

    The only thing the checker adds to the spec is the *shape* of the
    answer: `check_ret_only` insists that the effect is the bare return
    word with no writes, zeros, unmaps, copies or copy-ins and no events,
    which is exactly what every arm of the spec is (`err_ret` or
    `ret_only`). -/
def check_fsync (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdSocket _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdPipe _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdFileA _ _) => check_ret_only eff (BitVec.ofInt 64 0) m []
  | some (FdEntry.FdFileRW _ _) => check_ret_only eff (BitVec.ofInt 64 0) m []
  | some (FdEntry.FdFile _ _) => check_ret_only eff (BitVec.ofInt 64 0) m []
  | some (FdEntry.FdFileW _ _) => check_ret_only eff (BitVec.ofInt 64 0) m []
  | some FdEntry.FdDir => check_ret_only eff (BitVec.ofInt 64 0) m []

/- =========================================================================
   Private helpers: the two directions of the arm correspondence

   Each of the ten open-fd arms of `check_fsync` answers through
   `check_ret_only` with one word, and the spec's matching arm is
   `ret_only`/`err_ret` with the same word; writing the resulting
   three-line proof out in every arm of all four theorems would repeat it,
   so it is stated twice — once per direction.  `_sound_ok` and
   `_complete_unmodeled` use the first, `_complete_ok` the second, and
   `_complete_unmodeled` also uses the third (a `ret_only` arm has no
   `unmodeled` outcome), which is what a `nomatch` then establishes.
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

/-- Neither of the spec's two arm shapes can answer `unmodeled`: both are
    `ret_only`, whose only outcome is `.ok … []`.  So an `unmodeled`
    hypothesis in one of them is contradictory — which is what a `nomatch`
    shows arm by arm. -/
private theorem arm_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  exact nomatch H

theorem check_fsync_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_fsync fd eff m = .CheckOk m' evs) :
    fsync_spec fd i m (.ok eff m' evs) := by
  unfold check_fsync at H
  unfold fsync_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdChannel _ =>
      dsimp only at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | FdSocket _ =>
      dsimp only at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | FdPipe _ _ =>
      dsimp only at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | FdDevNull _ _ =>
      dsimp only at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | FdUrandom =>
      dsimp only at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | FdFileA _ _ =>
      dsimp only at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFileRW _ _ =>
      dsimp only at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFile _ _ =>
      dsimp only at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFileW _ _ =>
      dsimp only at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdDir =>
      dsimp only at H ⊢
      exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H

/-- [check_fsync] never declines — every [FdEntry] gets an answer, and so
    does a closed fd — so this is discharged by ruling the hypothesis out
    rather than by exhibiting an [Unmodeled] run. -/
theorem check_fsync_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_fsync fd eff m = .CheckUnmodeled) :
    fsync_spec fd i m .unmodeled := by
  unfold check_fsync at H
  unfold fsync_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdChannel _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    | FdSocket _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    | FdPipe _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    | FdDevNull _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    | FdUrandom =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    | FdFileA _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | FdFileRW _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | FdFile _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | FdFileW _ _ =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
    | FdDir =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])

theorem check_fsync_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : fsync_spec fd i m (.ok eff m' evs)) :
    check_fsync fd eff m = .CheckOk m' evs := by
  unfold check_fsync
  simp only [fsync_spec, getModelSpec, bind_getModel] at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdChannel _ =>
      dsimp only at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | FdSocket _ =>
      dsimp only at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | FdPipe _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | FdDevNull _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | FdUrandom =>
      dsimp only at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | FdFileA _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFileRW _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFile _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdFileW _ _ =>
      dsimp only at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
    | FdDir =>
      dsimp only at H ⊢
      exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H

/-- Symmetrically, [fsync_spec] has no [unmodeled] arm, so the hypothesis
    here is contradictory. -/
theorem check_fsync_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : fsync_spec fd i m .unmodeled) :
    check_fsync fd eff m = .CheckUnmodeled := by
  unfold check_fsync
  simp only [fsync_spec, getModelSpec, bind_getModel] at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none =>
    dsimp only at H ⊢
    exact absurd H (arm_ne_unmodeled _ i m)
  | some e =>
    cases e with
    | FdChannel _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdSocket _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdPipe _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdDevNull _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdUrandom =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdFileA _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdFileRW _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdFile _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdFileW _ _ =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)
    | FdDir =>
      dsimp only at H ⊢
      exact absurd H (arm_ne_unmodeled _ i m)

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal — it is one definition,
   four proofs and the prose above.  The checks below pin the arms those
   proofs follow against a concrete fd table: a closed fd is -EBADF, a
   channel is -EINVAL, a regular file and a directory are 0, and the
   success arm accepts the bare zero effect (which is what
   `check_ret_only` demands).

   `check_result` carries no `DecidableEq`, so each check states the
   expected `check_result` — or the expected `check_ret_only` — as an
   equation and closes it by unfolding the checker. -/

/-- A six-descriptor table: 0 a channel, 1 a regular file (`out`), 2 a
    directory, 3 a pipe end, 4 `/dev/null`, 5 `/dev/urandom`. -/
private def portFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0),
    (2, FdEntry.FdDir),
    (3, FdEntry.FdPipe 0 true),
    (4, FdEntry.FdDevNull true false),
    (5, FdEntry.FdUrandom) ]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and no rlimit. -/
private def portModel : Model :=
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A CLOSED FD IS -EBADF: the lookup is what decides, before the object
    is examined. -/
example (eff : SyscallEffect) :
    check_fsync 9 eff portModel = check_ret_only eff (errno_ret EBADF) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync, hlook]

/-- A CHANNEL IS -EINVAL: no `.fsync` on the operations table behind it. -/
example (eff : SyscallEffect) :
    check_fsync 0 eff portModel = check_ret_only eff (errno_ret EINVAL) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync, hlook]

/-- A PIPE END IS -EINVAL TOO — the arm whose table the model owns. -/
example (eff : SyscallEffect) :
    check_fsync 3 eff portModel = check_ret_only eff (errno_ret EINVAL) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 3 = some (FdEntry.FdPipe 0 true) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync, hlook]

/-- A REGULAR FILE IS 0, whatever the access mode. -/
example (eff : SyscallEffect) :
    check_fsync 1 eff portModel
      = check_ret_only eff (BitVec.ofInt 64 0) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync, hlook]

/-- A DIRECTORY IS 0 AS WELL — the key-publish case. -/
example (eff : SyscallEffect) :
    check_fsync 2 eff portModel
      = check_ret_only eff (BitVec.ofInt 64 0) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 2 = some FdEntry.FdDir := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync, hlook]

/-- THE SUCCESS ARM ACCEPTS THE BARE ZERO EFFECT: a regular file's `0` with
    no writes, zeros, unmaps, copies, copy-ins or events is `CheckOk` at
    the same model. -/
example :
    check_fsync 1 (mkEffect (BitVec.ofInt 64 0) [] []) portModel
      = .CheckOk portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync]
  rw [hlook]
  simp [check_ret_only, bv_eqb_refl]

/-- …and an effect that carries anything else is rejected, not accepted:
    the checker is the spec's shape, not just its return word. -/
example :
    check_fsync 1 ⟨BitVec.ofInt 64 0, [(0, [1])], [], [], [], []⟩ portModel
      = .CheckReject := by
  have hlook : fd_lookup (m_fds portModel) 1
      = some (FdEntry.FdFile [(0x6f : byte), 0x75, 0x74] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_fsync]
  rw [hlook]
  simp [check_ret_only]

/-- The two errnos really are the kernel's numbers in the return word. -/
example : errno_ret EBADF = BitVec.ofInt 64 (-9) := by decide
example : errno_ret EINVAL = BitVec.ofInt 64 (-22) := by decide

/- ------------------------------------------------------------- ftruncate -/

/- (That banner has no declaration under it; the `ftruncate` checker it
   announces belongs to another module.) -/

end LinuxSem.Checks.Sys.Fs.Sync
