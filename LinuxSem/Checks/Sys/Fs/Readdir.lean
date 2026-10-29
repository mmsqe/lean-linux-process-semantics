/-
  * LinuxProcessSem.Checks.Sys.Fs.Readdir — the getdents64 (61) checker, and its proofs

  Answers to Linux [fs/readdir.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous
  constructor pattern `⟨ret, [], [], [], [], []⟩` over `SyscallEffect`
  (`State.lean`), whose `mkEffect r [] []` abbreviation is the same term.

  Each proof peels the spec's model reader with `bind_getModel`, which
  rewrites `bind getModel k i m o` to `k m i m o` in one go, so every proof
  unfolds the spec to the `bind` and then `rw [bind_getModel]`.  `dsimp
  only` performs the beta/iota reduction and the `check_ret_only`
  unfolding, `exact nomatch H` eliminates a `CheckReject = CheckOk`
  equation, and the effect's six fields are taken apart with `obtain` plus
  `cases … <;> dsimp only at H` (the `case nil.nil.nil.nil.nil` selector,
  as in `Checks/Sys/Fs/File.lean`).  The `alt`/`choose` step of the
  directory arm uses `alt_l`/`alt_r` with `choose_ok`; `inv_ok`
  deliberately stops at constructor injectivities, so the effect shape is
  inverted with `check_result.CheckOk.injEq` and `check_ret_only_ok_iff`
  instead.

  `getdents64_spec` is a `SysSpec`, a FUNCTION, so its body is an
  `if`/`match` at function type; Lean normalises such a goal by trying to
  decide `getdents64_no_room count`, whose `sint32` is opaque and whose
  reduction does not bottom out.  Each proof therefore starts by
  `generalize`-ing its conclusion into a local `Q : Prop` and case-splits
  against `Q` (an opaque variable, so no reduction happens), rewriting `Q`
  back into the spec at the leaves with `rw [← hP]` — the same device
  `Checks/Sys/Kernel/Groups.lean` documents.

  `simp only [check_getdents64]` on the hypothesis makes `simp` try to
  decide the checker's `if getdents64_no_room count` and recurse past the
  maximum depth, so the proofs unfold with `unfold`/`rw` (delta and iota
  only) everywhere the `if` is still unsettled, and leave `simp` for the
  leaves where the branch is known and the condition has disappeared.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Readdir

namespace LinuxSem.Checks.Sys.Fs.Readdir

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
open LinuxSem.Checks.Sys.Prelude

/-- [getdents64] (61): -EBADF on a closed fd, -ENOTDIR on every fd that
    is not a directory, and on a directory fd either -EINVAL or the one
    injectable errno when the buffer cannot hold the smallest possible
    entry.  Every larger buffer on a directory fd is [CheckUnmodeled].
    Mirrors [Fs.Readdir.getdents64_spec] arm for arm — read that spec
    for why the listing itself is declined, and why the [dirent]
    pointer is not an argument here either.

    All the admitted answers are a bare return with FIVE EMPTY LEDGERS:
    the kernel reaches [user_write_access_begin] only after the
    [reclen > ctx->count] test has failed the call, so nothing this spec
    admits writes, zeroes, unmaps or copies a byte.  A kernel that
    claimed a write alongside one of these returns is rejected on the
    ledger rather than on the return value. -/
def check_getdents64 (fd count : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdFile _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdFileW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdFileA _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdFileRW _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdPipe _ _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdSocket _)  => check_ret_only eff (errno_ret ENOTDIR) m []
  | some (FdEntry.FdDevNull _ _) => check_ret_only eff (errno_ret ENOTDIR) m []
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret ENOTDIR) m []
  | some FdEntry.FdDir =>
      if getdents64_no_room count then
        match eff with
        | ⟨ret, [], [], [], [], []⟩ =>
            if errno_ret_in getdents64_errnos ret then .CheckOk m []
            else if bv_eqb ret (errno_ret EINVAL) then .CheckOk m []
            else .CheckReject
        | _ => .CheckReject
      else .CheckUnmodeled

/-! ## The ten arms

    Every proof below case-splits the descriptor on the same ten
    [FdEntry] constructors.  The nine non-directory arms agree
    completely — the spec answers -ENOTDIR to each and the checker
    accepts exactly the bare [check_ret_only] with that return, so no
    premise turns on WHICH object the descriptor is attached to — which
    is why each direction handles them in a single `all_goals`, which is
    what Lean's `cases` gives once it has split them apart.  [FdDir] and
    the closed fd get their own arms.

    THE DIRECTORY ARM IS SELECTED BY NAME (`case FdDir`), so a constructor
    added ahead of [FdDir] cannot silently move it.  The errno set is
    unfolded before the inversion because [inv_ok] needs
    [In e getdents64_errnos] to be a disjunction, while
    `errno_ret_in_true` does that job here and keeps [e] a variable only
    until `alt_l` has fixed it. -/

theorem check_getdents64_sound_ok (fd count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_getdents64 fd count eff m = .CheckOk m' evs) :
    getdents64_spec fd count i m (.ok eff m' evs) := by
  generalize hP : (getdents64_spec fd count i m (.ok eff m' evs)) = Q at *
  unfold check_getdents64 at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
    rw [← hP]
    unfold getdents64_spec getModelSpec
    rw [bind_getModel, hfd]
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  | some e =>
    cases e
    case FdDir =>
      rw [hfd] at H
      by_cases hroom : getdents64_no_room count = true
      · rw [ite_eq_left hroom] at H
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          dsimp only at H
        case nil.nil.nil.nil.nil =>
          by_cases hin : errno_ret_in getdents64_errnos ret = true
          · rw [ite_eq_left hin] at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨rfl, rfl⟩ := H
            obtain ⟨er, hmem, hret⟩ :=
              (errno_ret_in_true getdents64_errnos ret).mp hin
            subst hret
            rw [← hP]
            unfold getdents64_spec getModelSpec
            rw [bind_getModel, hfd, ite_eq_left hroom]
            refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
            refine bind_ok0 (errno_from getdents64_errnos) (fun e => err_ret e) i m er m
              _ m [] ?_ ?_
            · exact choose_ok (fun e => e ∈ getdents64_errnos) er i m hmem
            · simp only [err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure]
          · rw [ite_eq_right hin] at H
            by_cases heq : bv_eqb ret (errno_ret EINVAL) = true
            · rw [ite_eq_left heq] at H
              simp only [check_result.CheckOk.injEq] at H
              obtain ⟨rfl, rfl⟩ := H
              have hret : ret = errno_ret EINVAL := (Fs.bv_eqb_eq ret _).mp heq
              subst hret
              rw [← hP]
              unfold getdents64_spec getModelSpec
              rw [bind_getModel, hfd, ite_eq_left hroom]
              refine alt_r _ _ i m (.ok (mkEffect (errno_ret EINVAL) [] []) m []) ?_
              simp only [err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure]
            · rw [ite_eq_right heq] at H
              exact nomatch H
        all_goals exact nomatch H
      · rw [ite_eq_right hroom] at H
        exact nomatch H
    all_goals
      (rw [hfd] at H
       obtain ⟨rfl, rfl, rfl⟩ :=
         (check_ret_only_ok_iff eff (errno_ret ENOTDIR) m [] m' evs).mp H
       rw [← hP]
       unfold getdents64_spec getModelSpec
       rw [bind_getModel, hfd]
       simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])

/-- The one decline is the directory arm's roomy half — the listing the
    model cannot produce.  Inside the small-buffer half every effect
    shape is either accepted or rejected, never declined, and so is
    every non-directory fd. -/
theorem check_getdents64_sound_unmodeled (fd count : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_getdents64 fd count eff m = .CheckUnmodeled) :
    getdents64_spec fd count i m .unmodeled := by
  generalize hP : (getdents64_spec fd count i m .unmodeled) = Q at *
  unfold check_getdents64 at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e
    case FdDir =>
      rw [hfd] at H
      by_cases hroom : getdents64_no_room count = true
      · rw [ite_eq_left hroom] at H
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          dsimp only at H
        case nil.nil.nil.nil.nil =>
          by_cases hin : errno_ret_in getdents64_errnos ret = true
          · rw [ite_eq_left hin] at H
            exact nomatch H
          · rw [ite_eq_right hin] at H
            by_cases heq : bv_eqb ret (errno_ret EINVAL) = true
            · rw [ite_eq_left heq] at H
              exact nomatch H
            · rw [ite_eq_right heq] at H
              exact nomatch H
        all_goals exact nomatch H
      · rw [ite_eq_right hroom] at H
        rw [← hP]
        unfold getdents64_spec getModelSpec
        rw [bind_getModel, hfd]
        dsimp only
        rw [ite_eq_right hroom]
        exact unmodeled_intro _ _
    all_goals
      (rw [hfd] at H
       exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m []))

/-- Neither arm of the directory arm's [alt] can be [Unmodeled]: the
    first is a [choose] bound to a [pure], the second a [pure], and
    neither admits anything but [Ok].  Stated as a lemma because [inv_ok]
    cannot discharge it inline: a `bind` over `choose` produces an
    existential rather than a constructor equality. -/
theorem getdents64_alt_unmodeled_false (i : SyscallInput) (m : Model) :
    ¬ alt (bind (errno_from getdents64_errnos) (fun e => err_ret e))
        (err_ret EINVAL) i m .unmodeled := by
  intro H
  rcases H with H1 | H2
  · rcases H1 with hdecl | hrest
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · obtain ⟨x, m1, evs1, hc, hk⟩ := hrest
      exact nomatch hk
  · exact nomatch H2

/-- The relational argument in the accepting direction: -ENOTDIR (or
    -EBADF) for the ten plain arms, and the directory arm's small-buffer
    half, whose two answers are the injected errno (`alt_l`, over the
    `choose` of `errno_from`) and -EINVAL (`alt_r`). -/
theorem check_getdents64_complete_ok (fd count : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : getdents64_spec fd count i m (.ok eff m' evs)) :
    check_getdents64 fd count eff m = .CheckOk m' evs := by
  generalize hP : (check_getdents64 fd count eff m = .CheckOk m' evs) = Q at *
  unfold getdents64_spec getModelSpec at H
  rw [bind_getModel] at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    unfold check_getdents64
    rw [hfd]
    simp [check_ret_only, bv_eqb_refl]
  | some e =>
    cases e
    case FdDir =>
      rw [hfd] at H
      by_cases hroom : getdents64_no_room count = true
      · rw [ite_eq_left hroom] at H
        rcases H with H1 | H2
        · -- the injected errno: `choose` picks the member of the set
          obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
          obtain ⟨er0, hin, heq⟩ := hc
          simp only [Outcome.ok.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          cases her
          simp only [List.nil_append] at hevs
          subst hevs
          rw [← hP]
          unfold check_getdents64
          rw [hfd, ite_eq_left hroom]
          dsimp only
          rw [ite_eq_left (errno_ret_in_intro getdents64_errnos _ hin)]
        · -- `filldir64`'s own answer
          cases H2
          rw [← hP]
          unfold check_getdents64
          rw [hfd, ite_eq_left hroom]
          dsimp only
          rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
                (errno_ret EINVAL) = true)), ite_eq_left (bv_eqb_refl _)]
      · rw [ite_eq_right hroom] at H
        exact nomatch H
    all_goals
      (rw [hfd] at H
       simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
         Outcome.ok.injEq] at H
       obtain ⟨rfl, rfl, rfl⟩ := H
       rw [← hP]
       unfold check_getdents64
       rw [hfd]
       simp [check_ret_only, bv_eqb_refl])

/-- The single decline, in the converse direction: only the directory
    arm's roomy half reaches it.  Neither arm of the [alt] can be
    [Unmodeled] — a [choose] bound to a [pure] admits only [Ok] — which
    is the lemma above. -/
theorem check_getdents64_complete_unmodeled (fd count : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : getdents64_spec fd count i m .unmodeled) :
    check_getdents64 fd count eff m = .CheckUnmodeled := by
  generalize hP : (check_getdents64 fd count eff m = .CheckUnmodeled) = Q at *
  unfold getdents64_spec getModelSpec at H
  rw [bind_getModel] at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [hfd] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | some e =>
    cases e
    case FdDir =>
      rw [hfd] at H
      by_cases hroom : getdents64_no_room count = true
      · rw [ite_eq_left hroom] at H
        exact absurd H (getdents64_alt_unmodeled_false i m)
      · rw [ite_eq_right hroom] at H
        rw [← hP]
        unfold check_getdents64
        rw [hfd, ite_eq_right hroom]
    all_goals
      (rw [hfd] at H
       simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
       exact nomatch H)

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the arms
    the four proofs above follow against a concrete model: -EBADF for an
    fd that is not open, -ENOTDIR for a channel and for a pipe end, the
    decline on a directory with a roomy buffer, and — on a directory with
    a 23-byte buffer — acceptance of the injected -ENOENT and of
    -EINVAL, rejection of any other return, and rejection of any effect
    that carries a write.  `check_result` has no `DecidableEq`, so each
    states the branch as an equation and closes it by unfolding the
    checker and discharging the branch tests by name. -/

/-- A tiny fd table: 0 a channel, 1 a directory, 2 a pipe end. -/
private def demoFds : List (word × FdEntry) :=
  [ (0, FdEntry.FdChannel 7),
    (1, FdEntry.FdDir),
    (2, FdEntry.FdPipe 0 true) ]

/-- The model the checks run in: the fd table above, an empty VM ledger,
    an empty file system, EOF on stdin, no halt and no rlimit. -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- A closed fd is -EBADF, and it is the fd lookup that decides: no
    object is examined at all. -/
example (eff : SyscallEffect) :
    check_getdents64 9 24 eff demoModel
      = check_ret_only eff (errno_ret EBADF) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 9 = none := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook]

/-- A CHANNEL IS -ENOTDIR: no `.iterate_shared` on a non-directory. -/
example (eff : SyscallEffect) :
    check_getdents64 0 24 eff demoModel
      = check_ret_only eff (errno_ret ENOTDIR) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook]

/-- …and so is a PIPE END. -/
example (eff : SyscallEffect) :
    check_getdents64 2 24 eff demoModel
      = check_ret_only eff (errno_ret ENOTDIR) demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 2 = some (FdEntry.FdPipe 0 true) := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook]

/-- A DIRECTORY WITH A ROOMY BUFFER IS DECLINED: the listing is what the
    model cannot produce. -/
example (eff : SyscallEffect) : check_getdents64 1 24 eff demoModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook, ite_eq_right (by decide : ¬(getdents64_no_room (24 : word) = true))]

/-- A 23-BYTE BUFFER CANNOT HOLD THE SMALLEST ENTRY, so the directory arm
    answers rather than declining; -EINVAL is accepted. -/
example :
    check_getdents64 1 23 (mkEffect (errno_ret EINVAL) [] []) demoModel
      = .CheckOk demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook, ite_eq_left (by decide : getdents64_no_room (23 : word) = true)]
  dsimp only
  rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
        (errno_ret EINVAL) = true)), ite_eq_left (bv_eqb_refl _)]

/-- …AND THE INJECTED -ENOENT IS ADMISSIBLE FOR THE SAME CALL:
    `iterate_dir` answers it for a removed directory before `filldir64`
    ever runs. -/
example :
    check_getdents64 1 23 (mkEffect (errno_ret ENOENT) [] []) demoModel
      = .CheckOk demoModel [] := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook, ite_eq_left (by decide : getdents64_no_room (23 : word) = true)]
  dsimp only
  rw [ite_eq_left (errno_ret_in_intro getdents64_errnos ENOENT (by decide))]

/-- ANY OTHER RETURN IS REJECTED on the same call. -/
example :
    check_getdents64 1 23 (mkEffect (errno_ret EACCES) [] []) demoModel
      = .CheckReject := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook, ite_eq_left (by decide : getdents64_no_room (23 : word) = true)]
  dsimp only
  rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
      (errno_ret EACCES) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (errno_ret EACCES)
      (errno_ret EINVAL) = true))]

/-- …AND SO IS A WRITE LEDGER: the kernel has not touched the buffer on
    any admitted arm, so an effect that claims a write is rejected on the
    ledger rather than on the return value. -/
example :
    check_getdents64 1 23 (mkEffect (errno_ret EINVAL) [(0, [1])] []) demoModel
      = .CheckReject := by
  have hlook : fd_lookup (m_fds demoModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, demoModel, mkModel, demoFds, fd_lookup]
  unfold check_getdents64
  rw [hlook, ite_eq_left (by decide : getdents64_no_room (23 : word) = true)]

end LinuxSem.Checks.Sys.Fs.Readdir
