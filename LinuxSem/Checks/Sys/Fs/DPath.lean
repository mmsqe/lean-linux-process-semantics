/-
  * LinuxProcessSem.Checks.Sys.Fs.DPath — the getcwd (17) checker, and its proofs

  Answers to Linux `fs/d_path.c`: this file holds the checkers for the
  syscalls defined there, and no others.

  `Checks/ExecutableSpecs.lean` keeps the dispatcher and the four top-level
  theorems and re-exports this module.  The checkers here are
  executable, and their proofs relate them to the relational specs in
  the matching `Sys` module.

  The size band is `1 < size.toNat` — the UNSIGNED reading of the register —
  and the checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`.
  An effect literal is the anonymous constructor
  `⟨ret, [], [], [], [], []⟩` over `SyscallEffect`.

  Every proof below starts by `generalize`-ing its conclusion into an opaque
  `Q : Prop`, as `Checks/Sys/Kernel/Groups.lean` does and for the same
  reason: `getcwd_spec` is a `SysSpec`, a FUNCTION, so its leading
  `if 1 < size.toNat` sits at function type and `by_cases`/`cases` would
  whnf the goal into the decision procedure on `size.toNat` rather than into
  a branch.  Splitting against the opaque `Q` first, and rewriting `Q` back
  at the leaves, keeps `whnf` away from that `if`.  The branch test is
  `by_cases hbig : 1 < size.toNat`; a `CheckUnmodeled = CheckOk` equation is
  eliminated by `nomatch`; and the effect's five ledgers are split with
  `obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff` followed by
  `cases … <;> dsimp only at H`, with the thirty-one dead shapes closed by
  `nomatch`.  `inv_ok` is available as a macro, but the spec's
  `alt`/`choose`/`bind` produce disjunctions and nested existentials rather
  than constructor equalities, so the two completeness proofs spell the
  inversion out with `rcases`/`obtain` — the same choice
  `Checks/Sys/Fs/File.lean` and `Checks/Sys/Fs/Readdir.lean` make.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.DPath

namespace LinuxSem.Checks.Sys.Fs.DPath

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.DPath
open LinuxSem.Checks.Sys.Prelude

/-- [getcwd] (17): -ERANGE or one of the three injectable errnos when
    [size] is 0 or 1, and [CheckUnmodeled] for every larger buffer.
    Mirrors [Fs.DPath.getcwd_spec] branch for branch — read that spec
    for why the working directory cannot change the answer in the
    modeled band, and why [buf] is not an argument here either.

    All four admitted answers are a bare return with FIVE EMPTY ledgers:
    the kernel reaches its single [copy_to_user] only after the size
    comparison has passed, so nothing this band admits writes, zeroes,
    unmaps or copies a byte.  A kernel that claimed a write alongside
    one of these returns is rejected on the ledger rather than on the
    return value. -/
def check_getcwd (size : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if 1 < size.toNat then .CheckUnmodeled
  else
    match eff with
    | ⟨ret, [], [], [], [], []⟩ =>
        if errno_ret_in getcwd_errnos ret then .CheckOk m []
        else if bv_eqb ret (errno_ret ERANGE) then .CheckOk m []
        else .CheckReject
    | _ => .CheckReject

theorem check_getcwd_sound_ok (size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_getcwd size eff m = .CheckOk m' evs) :
    getcwd_spec size i m (.ok eff m' evs) := by
  generalize hP : (getcwd_spec size i m (.ok eff m' evs)) = Q at *
  unfold check_getcwd at H
  by_cases hbig : 1 < size.toNat
  · rw [ite_eq_left hbig] at H
    exact nomatch H
  · rw [ite_eq_right hbig] at H
    obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis <;>
      dsimp only at H
    case nil.nil.nil.nil.nil =>
      by_cases hin : errno_ret_in getcwd_errnos ret = true
      · rw [ite_eq_left hin] at H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨er, hmem, hret⟩ :=
          (errno_ret_in_true getcwd_errnos ret).mp hin
        subst hret
        rw [← hP]
        unfold getcwd_spec
        rw [ite_eq_right hbig]
        refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
        refine bind_ok0 (errno_from getcwd_errnos) (fun e => err_ret e) i m er m
          _ m [] ?_ ?_
        · exact choose_ok (fun e => e ∈ getcwd_errnos) er i m hmem
        · simp only [err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right hin] at H
        by_cases heq : bv_eqb ret (errno_ret ERANGE) = true
        · rw [ite_eq_left heq] at H
          simp only [check_result.CheckOk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          have hret : ret = errno_ret ERANGE := (Fs.bv_eqb_eq ret _).mp heq
          subst hret
          rw [← hP]
          unfold getcwd_spec
          rw [ite_eq_right hbig]
          refine alt_r _ _ i m (.ok (mkEffect (errno_ret ERANGE) [] []) m []) ?_
          simp only [err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
        · rw [ite_eq_right heq] at H
          exact nomatch H
    all_goals exact nomatch H

/-- The one decline is the size band the working directory would decide;
    inside it every effect shape is either accepted or rejected, never
    declined. -/
theorem check_getcwd_sound_unmodeled (size : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_getcwd size eff m = .CheckUnmodeled) :
    getcwd_spec size i m .unmodeled := by
  generalize hP : (getcwd_spec size i m .unmodeled) = Q at *
  unfold check_getcwd at H
  by_cases hbig : 1 < size.toNat
  · rw [ite_eq_left hbig] at H
    rw [← hP]
    unfold getcwd_spec
    rw [ite_eq_left hbig]
    exact unmodeled_intro i m
  · rw [ite_eq_right hbig] at H
    obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis <;>
      dsimp only at H
    case nil.nil.nil.nil.nil =>
      by_cases hin : errno_ret_in getcwd_errnos ret = true
      · rw [ite_eq_left hin] at H
        exact nomatch H
      · rw [ite_eq_right hin] at H
        by_cases heq : bv_eqb ret (errno_ret ERANGE) = true
        · rw [ite_eq_left heq] at H
          exact nomatch H
        · rw [ite_eq_right heq] at H
          exact nomatch H
    all_goals exact nomatch H

/-- Neither arm of the band's [alt] can be [Unmodeled]: the first is a
    [choose] bound to a [pure], the second a [pure], and neither admits
    anything but [Ok].  Stated as a lemma of its own because `inv_ok`
    cannot discharge it inline: a `bind` over `choose` produces an
    existential rather than a constructor equality.  The same lemma, under
    the same name, is in `Checks/Sys/Fs/Readdir.lean`. -/
theorem getcwd_alt_unmodeled_false (i : SyscallInput) (m : Model) :
    ¬ alt (bind (errno_from getcwd_errnos) (fun e => err_ret e))
        (err_ret ERANGE) i m .unmodeled := by
  intro H
  rcases H with H1 | H2
  · rcases H1 with hdecl | hrest
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · obtain ⟨x, m1, evs1, hc, hk⟩ := hrest
      exact nomatch hk
  · exact nomatch H2

theorem check_getcwd_complete_ok (size : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : getcwd_spec size i m (.ok eff m' evs)) :
    check_getcwd size eff m = .CheckOk m' evs := by
  generalize hP : (check_getcwd size eff m = .CheckOk m' evs) = Q at *
  unfold getcwd_spec at H
  by_cases hbig : 1 < size.toNat
  · rw [ite_eq_left hbig] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hbig] at H
    -- The [alt], the [bind]'s own union and the [In] over [getcwd_errnos]
    -- are all disjunctions; peeling them leaves one leaf per admitted
    -- errno, and each is a closed term the checker computes on.
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
      unfold check_getcwd
      rw [ite_eq_right hbig]
      dsimp only
      rw [ite_eq_left (errno_ret_in_intro getcwd_errnos _ hin)]
    · -- the -ERANGE the model derives from `size`
      cases H2
      rw [← hP]
      unfold check_getcwd
      rw [ite_eq_right hbig]
      dsimp only
      rw [ite_eq_right (by decide : ¬(errno_ret_in getcwd_errnos
            (errno_ret ERANGE) = true)), ite_eq_left (bv_eqb_refl _)]

theorem check_getcwd_complete_unmodeled (size : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : getcwd_spec size i m .unmodeled) :
    check_getcwd size eff m = .CheckUnmodeled := by
  generalize hP : (check_getcwd size eff m = .CheckUnmodeled) = Q at *
  unfold getcwd_spec at H
  by_cases hbig : 1 < size.toNat
  · rw [ite_eq_left hbig] at H
    rw [← hP]
    unfold check_getcwd
    rw [ite_eq_left hbig]
  · rw [ite_eq_right hbig] at H
    -- Neither arm of the [alt] can be [Unmodeled]: a [choose] bound to a
    -- [pure] admits only [Ok].
    exact absurd H (getcwd_alt_unmodeled_false i m)

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal — it is one checker
    and its four proofs.  The checks below are sanity checks, and they pin
    the branch order the proofs above follow: the band answers -ERANGE
    and the injectable -ENOMEM, a two-byte buffer is declined, the POSIX
    -EINVAL is rejected (the kernel has no such arm), and any effect
    carrying a write is rejected on the ledger.  `check_result` has no
    `DecidableEq`, so each states the branch as an equation and closes
    it by unfolding the checker and discharging the branch tests by name
    — the same style as `Checks/Sys/Fs/Readdir.lean`. -/

/-- The model the checks run in: no fds, an empty VM ledger, an empty file
    system, EOF on stdin, no halt and no rlimit.  Nothing in it can
    matter to getcwd — the spec never looks at the model. -/
private def demoModel : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- `getcwd(NULL, 0)` is -ERANGE, and the checker accepts it. -/
example : check_getcwd 0 (mkEffect (errno_ret ERANGE) [] []) demoModel
    = .CheckOk demoModel [] := by
  unfold check_getcwd
  rw [ite_eq_right (by decide : ¬(1 < (0 : word).toNat))]
  dsimp only
  rw [ite_eq_right (by decide : ¬(errno_ret_in getcwd_errnos
        (errno_ret ERANGE) = true)), ite_eq_left (bv_eqb_refl _)]

/-- -ENOMEM IS ADMISSIBLE FOR THE SAME CALL — `__getname()` runs before
    the size comparison, so the injectable arm answers before -ERANGE. -/
example : check_getcwd 0 (mkEffect (errno_ret ENOMEM) [] []) demoModel
    = .CheckOk demoModel [] := by
  unfold check_getcwd
  rw [ite_eq_right (by decide : ¬(1 < (0 : word).toNat))]
  dsimp only
  rw [ite_eq_left (errno_ret_in_intro getcwd_errnos ENOMEM (by decide))]

/-- A TWO-BYTE BUFFER IS PAST THE BAND: the working directory would decide
    the answer, so the call is declined, fail closed. -/
example : check_getcwd 2 (mkEffect (errno_ret ERANGE) [] []) demoModel
    = .CheckUnmodeled := by
  unfold check_getcwd
  rw [ite_eq_left (by decide : 1 < (2 : word).toNat)]

/-- -EINVAL IS NOT AN ARM: the kernel body has no such return, so the
    checker rejects it rather than accepting it as a small-size answer.
    (The -EINVAL a glibc caller sees for a zero size is decided in
    `sysdeps/unix/sysv/linux/getcwd.c`, before the syscall is issued.) -/
example : check_getcwd 0 (mkEffect (errno_ret EINVAL) [] []) demoModel
    = .CheckReject := by
  unfold check_getcwd
  rw [ite_eq_right (by decide : ¬(1 < (0 : word).toNat))]
  dsimp only
  rw [ite_eq_right (by decide : ¬(errno_ret_in getcwd_errnos
        (errno_ret EINVAL) = true)),
      ite_eq_right (by decide : ¬(bv_eqb (errno_ret EINVAL)
        (errno_ret ERANGE) = true))]

/-- …AND SO IS A WRITE LEDGER: on every admitted arm the kernel has not
    touched `buf`, so an effect that claims a write is rejected on the
    ledger rather than on the return value. -/
example : check_getcwd 0 (mkEffect (errno_ret ERANGE) [(0, [1])] []) demoModel
    = .CheckReject := by
  unfold check_getcwd
  rw [ite_eq_right (by decide : ¬(1 < (0 : word).toNat))]

end LinuxSem.Checks.Sys.Fs.DPath
