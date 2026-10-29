/-
  * LinuxProcessSem.Checks.Sys.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) checkers, and their proofs

  Answers to Linux [fs/stat.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  `Checks.Sys.Prelude` re-exports the model/state/monad stack and supplies
  [check_result], [check_ret_only], [check_ret_only_copyins],
  [clear_copyins] and their lemmas; the checker's own spec — `Sys/Fs/Stat.lean`,
  where [readlinkat_spec], [newfstatat_core_spec], [newfstatat_spec],
  [fstat_file_spec], [fstat_chrdev_spec], [fstat_devnull_spec],
  [fstat_urandom_spec] and [fstat_spec] live — is imported directly, and
  `Sys.Uapi` supplies the whole `struct stat` layer.

  The six inversion lemmas the completeness proofs need —
  [input_bind_ok_inv], [input_bind_unmodeled_inv], [bind_get_model_ok_inv],
  [bind_get_model_unmodeled_inv], [record_copyins_ok_inv],
  [record_copyins_unmodeled_inv] — are hoisted into `Checks.Sys.Prelude`
  (the two `get_model` ones as [get_model_bind_ok_inv] /
  [get_model_bind_unmodeled_inv], the tree's argument order), so they are
  not redeclared here: the four completeness proofs below cite them under
  their `Prelude` names.

  A path is `Fs.path` (`List byte`), and an effect literal is the anonymous
  constructor pattern `⟨ret, [], [], [], [], []⟩` over `SyscallEffect`.  The
  checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`, and the
  spec monad with `.ok` / `.unmodeled`.

  Each checker and its spec place the SAME tests in the SAME order at the
  head of a subtree, so each proof walks the two together: `unfold` the
  checker into the hypothesis and the spec into the goal, `dsimp only` for
  the reduction — written `try dsimp only` where `dsimp` would complain
  that there was nothing left to reduce, since unlike a no-op reduction it
  errors — and then, for the pathname walk, `generalize … at H ⊢` plus
  `cases` on `read_cstr`, so that BOTH sides reduce at once.  That last
  step is why the two binds of [newfstatat_core_spec] are discharged BEFORE
  the walk: `bind_ok0` beta-reduces the lambdas, so the `read_cstr`
  occurrence is no longer under a binder and the one `generalize` can
  serve both sides (see the footgun note in
  `Checks/Sys/Kernel/Groups.lean`).  A `CheckReject`-vs-`CheckOk` equation
  is closed by `exact nomatch H`, and the correspondence step is the
  forward direction of `check_ret_only_ok_iff`, taken by
  `obtain ⟨rfl, rfl, rfl⟩`.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Stat

namespace LinuxSem.Checks.Sys.Fs.Stat

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Stat
open LinuxSem.Checks.Sys.Prelude

/- =========================================================================
   readlinkat (78)
   ========================================================================= -/

/-- readlinkat's checker: the AT_FDCWD gate, then the deterministic
    -EINVAL with an empty ledger and no events.  Every argument other
    than the dirfd is uninterpreted by [readlinkat_spec], so this can be
    total on the arms it answers.

    Kernel citations for both arms live on [Stat.readlinkat_spec]. -/
def check_readlinkat (dirfd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(bv_eqb dirfd AT_FDCWD32) then .CheckUnmodeled
  else check_ret_only eff (errno_ret EINVAL) m []

theorem check_readlinkat_sound_ok (dirfd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_readlinkat dirfd eff m = .CheckOk m' evs) :
    readlinkat_spec dirfd i m (.ok eff m' evs) := by
  unfold check_readlinkat at H
  unfold readlinkat_spec
  by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
  · rw [ite_eq_left hd] at H
    exact nomatch H
  · rw [ite_eq_right hd] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]

theorem check_readlinkat_sound_unmodeled (dirfd : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_readlinkat dirfd eff m = .CheckUnmodeled) :
    readlinkat_spec dirfd i m .unmodeled := by
  unfold check_readlinkat at H
  unfold readlinkat_spec
  by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
  · rw [ite_eq_left hd] at H ⊢
    exact unmodeled_intro i m
  · rw [ite_eq_right hd] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_readlinkat_complete_ok (dirfd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : readlinkat_spec dirfd i m (.ok eff m' evs)) :
    check_readlinkat dirfd eff m = .CheckOk m' evs := by
  unfold readlinkat_spec at H
  unfold check_readlinkat
  by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
  · rw [ite_eq_left hd] at H ⊢
    exact nomatch H
  · rw [ite_eq_right hd] at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]

theorem check_readlinkat_complete_unmodeled (dirfd : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : readlinkat_spec dirfd i m .unmodeled) :
    check_readlinkat dirfd eff m = .CheckUnmodeled := by
  unfold readlinkat_spec at H
  unfold check_readlinkat
  by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
  · rw [ite_eq_left hd] at H ⊢
  · rw [ite_eq_right hd] at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H

/- =========================================================================
   newfstatat (79)
   ========================================================================= -/

/-- newfstatat: only the FAILING side is modeled, and it writes nothing —
    a flag word outside {0, AT_SYMLINK_NOFOLLOW}, a dirfd other than
    AT_FDCWD, ".", and any path the file system holds all fail closed,
    because a successful call would have to deliver 128 bytes of
    metadata [Fs] does not carry (see [Stat.newfstatat_spec]).  Writing
    nothing is not reading nothing: each accepting arm is
    [check_ret_only_copyins], which is [check_ret_only]'s empty-effect
    demand on everything BUT the copy-in list, plus an equality on that
    list.  Plain [check_ret_only] would insist the ledger be empty and
    so reject the truthful effect.  The range is the one
    [Open.check_openat] demands, because both syscalls run the same
    [getname_flags]; unlike openat's, no arm here copies in again after
    it, so the whole claimed list is that single range. -/
def check_newfstatat (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
  if !(modeled_statat_flags flag) then .CheckUnmodeled
  else
    match read_cstr i.in_mem pathp with
    | .CstrTooLong => check_ret_only_copyins reads eff (errno_ret ENAMETOOLONG) m []
    | .CstrFault => check_ret_only_copyins reads eff (errno_ret EFAULT) m []
    | .CstrOk p =>
        if path_eqb p [] then check_ret_only_copyins reads eff (errno_ret ENOENT) m []
        else if !(bv_eqb dirfd AT_FDCWD32) then .CheckUnmodeled
        else if path_eqb p dot_path then .CheckUnmodeled
        else
          match fs_lookup (m_fs m) p with
          | none => check_ret_only_copyins reads eff (errno_ret ENOENT) m []
          | some _ => .CheckUnmodeled

/-! ### The two bridges between [newfstatat_spec] and its core

    The two steps are stated once here because the effect has to be NAMED:
    the `with_copyins` in the goal does not invert by unification against
    an unknown argument.  The four proofs below cite them arm for arm. -/

/-- The wrapper, built from a core-spec outcome whose ledger is empty. -/
private theorem newfstatat_spec_ok_of_core (dirfd pathp flag : word)
    (i : SyscallInput) (m : Model) (code : Int)
    (H : newfstatat_core_spec dirfd pathp flag i m
      (.ok (mkEffect (errno_ret code) [] []) m [])) :
    newfstatat_spec dirfd pathp flag i m
      (.ok (with_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
        (mkEffect (errno_ret code) [] [])) m []) := by
  unfold newfstatat_spec
  refine bind_ok0 inputSpec _ i m i m _ m [] (input_ok i m) ?_
  exact record_copyins_ok_empty rfl H

/-- The wrapper, carried through a declining core. -/
private theorem newfstatat_spec_unmodeled_of_core (dirfd pathp flag : word)
    (i : SyscallInput) (m : Model)
    (H : newfstatat_core_spec dirfd pathp flag i m .unmodeled) :
    newfstatat_spec dirfd pathp flag i m .unmodeled := by
  unfold newfstatat_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  exact record_copyins_unmodeled H

theorem check_newfstatat_sound_ok (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_newfstatat i dirfd pathp flag eff m = .CheckOk m' evs) :
    newfstatat_spec dirfd pathp flag i m (.ok eff m' evs) := by
  unfold check_newfstatat at H
  dsimp only at H
  by_cases hfl : (!(modeled_statat_flags flag)) = true
  · rw [ite_eq_left hfl] at H
    exact nomatch H
  · rw [ite_eq_right hfl] at H
    generalize hR : read_cstr i.in_mem pathp = r at H
    cases r with
    | CstrTooLong =>
      dsimp only at H
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_copyins_ok_iff _ eff (errno_ret ENAMETOOLONG) m [] m' evs).mp H
      subst heff; rw [hm] at *; subst hevs
      exact newfstatat_spec_ok_of_core dirfd pathp flag i m ENAMETOOLONG (by
        unfold newfstatat_core_spec
        refine bind_ok0 inputSpec _ i m i m _ m [] (input_ok i m) ?_
        refine bind_ok0 getModelSpec _ i m m m _ m [] (getModel_ok i m) ?_
        rw [ite_eq_right hfl]
        simp only [hR, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])
    | CstrFault =>
      dsimp only at H
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_copyins_ok_iff _ eff (errno_ret EFAULT) m [] m' evs).mp H
      subst heff; rw [hm] at *; subst hevs
      exact newfstatat_spec_ok_of_core dirfd pathp flag i m EFAULT (by
        unfold newfstatat_core_spec
        refine bind_ok0 inputSpec _ i m i m _ m [] (input_ok i m) ?_
        refine bind_ok0 getModelSpec _ i m m m _ m [] (getModel_ok i m) ?_
        rw [ite_eq_right hfl]
        simp only [hR, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])
    | CstrOk p =>
      dsimp only at H
      by_cases hpe : path_eqb p [] = true
      · rw [ite_eq_left hpe] at H
        obtain ⟨heff, hm, hevs⟩ :=
          (check_ret_only_copyins_ok_iff _ eff (errno_ret ENOENT) m [] m' evs).mp H
        subst heff; rw [hm] at *; subst hevs
        exact newfstatat_spec_ok_of_core dirfd pathp flag i m ENOENT (by
          unfold newfstatat_core_spec
          refine bind_ok0 inputSpec _ i m i m _ m [] (input_ok i m) ?_
          refine bind_ok0 getModelSpec _ i m m m _ m [] (getModel_ok i m) ?_
          rw [ite_eq_right hfl]
          simp only [hR]
          rw [ite_eq_left hpe]
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])
      · rw [ite_eq_right hpe] at H
        by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
        · rw [ite_eq_left hd] at H
          exact nomatch H
        · rw [ite_eq_right hd] at H
          by_cases hdot : path_eqb p dot_path = true
          · rw [ite_eq_left hdot] at H
            exact nomatch H
          · rw [ite_eq_right hdot] at H
            generalize hfs : fs_lookup (m_fs m) p = lk at H
            cases lk with
            | none =>
              dsimp only at H
              obtain ⟨heff, hm, hevs⟩ :=
                (check_ret_only_copyins_ok_iff _ eff (errno_ret ENOENT) m [] m' evs).mp H
              subst heff; rw [hm] at *; subst hevs
              exact newfstatat_spec_ok_of_core dirfd pathp flag i m ENOENT (by
                unfold newfstatat_core_spec
                refine bind_ok0 inputSpec _ i m i m _ m [] (input_ok i m) ?_
                refine bind_ok0 getModelSpec _ i m m m _ m [] (getModel_ok i m) ?_
                rw [ite_eq_right hfl]
                simp only [hR]
                rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs]
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure])
            | some data =>
              exact nomatch H

theorem check_newfstatat_sound_unmodeled (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_newfstatat i dirfd pathp flag eff m = .CheckUnmodeled) :
    newfstatat_spec dirfd pathp flag i m .unmodeled := by
  unfold check_newfstatat at H
  dsimp only at H
  -- `record_copyins` carries a decline through untouched, so recording
  -- the pathname costs the declining arms nothing.
  by_cases hfl : (!(modeled_statat_flags flag)) = true
  · exact newfstatat_spec_unmodeled_of_core dirfd pathp flag i m (by
      unfold newfstatat_core_spec
      refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
      refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
      rw [ite_eq_left hfl]
      simp only [LinuxSem.LinuxProcessSem.unmodeled])
  · rw [ite_eq_right hfl] at H
    generalize hR : read_cstr i.in_mem pathp = r at H
    cases r with
    | CstrTooLong =>
      dsimp only at H
      exact absurd H
        (check_ret_only_copyins_no_unmodeled _ eff (errno_ret ENAMETOOLONG) m [])
    | CstrFault =>
      dsimp only at H
      exact absurd H (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EFAULT) m [])
    | CstrOk p =>
      dsimp only at H
      by_cases hpe : path_eqb p [] = true
      · rw [ite_eq_left hpe] at H
        exact absurd H (check_ret_only_copyins_no_unmodeled _ eff (errno_ret ENOENT) m [])
      · rw [ite_eq_right hpe] at H
        by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
        · rw [ite_eq_left hd] at H
          exact newfstatat_spec_unmodeled_of_core dirfd pathp flag i m (by
            unfold newfstatat_core_spec
            refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
            refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
            rw [ite_eq_right hfl]
            simp only [hR]
            rw [ite_eq_right hpe, ite_eq_left hd]
            simp only [LinuxSem.LinuxProcessSem.unmodeled])
        · rw [ite_eq_right hd] at H
          by_cases hdot : path_eqb p dot_path = true
          · rw [ite_eq_left hdot] at H
            exact newfstatat_spec_unmodeled_of_core dirfd pathp flag i m (by
              unfold newfstatat_core_spec
              refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
              refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
              rw [ite_eq_right hfl]
              simp only [hR]
              rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_left hdot]
              simp only [LinuxSem.LinuxProcessSem.unmodeled])
          · rw [ite_eq_right hdot] at H
            generalize hfs : fs_lookup (m_fs m) p = lk at H
            cases lk with
            | none =>
              dsimp only at H
              exact absurd H
                (check_ret_only_copyins_no_unmodeled _ eff (errno_ret ENOENT) m [])
            | some data =>
              dsimp only at H
              exact newfstatat_spec_unmodeled_of_core dirfd pathp flag i m (by
                unfold newfstatat_core_spec
                refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
                refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
                rw [ite_eq_right hfl]
                simp only [hR]
                rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs]
                simp only [LinuxSem.LinuxProcessSem.unmodeled])



/-- Peel [newfstatat_core_spec]'s two reader binds, leaving the body
    applied to the syscall's own input and model.  The shape below is
    [newfstatat_core_spec]'s body with the two `bind`s removed. -/
private theorem newfstatat_core_body {dirfd pathp flag : word} {i : SyscallInput}
    {m : Model} {core : SyscallEffect} {m' : Model} {evs : List event}
    (H : newfstatat_core_spec dirfd pathp flag i m (.ok core m' evs)) :
    (if !(modeled_statat_flags flag) then
        LinuxSem.LinuxProcessSem.unmodeled
     else
        match read_cstr i.in_mem pathp with
        | .CstrTooLong => err_ret ENAMETOOLONG
        | .CstrFault => err_ret EFAULT
        | .CstrOk p =>
            if path_eqb p [] then err_ret ENOENT
            else if !(bv_eqb dirfd AT_FDCWD32) then
              LinuxSem.LinuxProcessSem.unmodeled
            else if path_eqb p dot_path then
              LinuxSem.LinuxProcessSem.unmodeled
            else
              match fs_lookup (m_fs m) p with
              | none => err_ret ENOENT
              | some _ => LinuxSem.LinuxProcessSem.unmodeled) i m
      (.ok core m' evs) := by
  unfold newfstatat_core_spec at H
  obtain ⟨i', m', evs1, evs2, h1, h2, h3⟩ := H
  have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i' m' evs1) := h1.symm
  simp only [Outcome.ok.injEq] at h1'
  obtain ⟨rfl, rfl, rfl⟩ := h1'
  obtain ⟨m0, m2, evs3, evs4, h4, h5, h6⟩ := h2
  have h4' : (Outcome.ok m m ([] : List event)) = (Outcome.ok m0 m2 evs3) := h4.symm
  simp only [Outcome.ok.injEq] at h4'
  obtain ⟨rfl, rfl, rfl⟩ := h4'
  simp only [List.nil_append] at h3 h6
  rw [← h6, ← h3] at h5
  exact h5

/-- The same peel on the declining side. -/
private theorem newfstatat_core_body_unmodeled {dirfd pathp flag : word}
    {i : SyscallInput} {m : Model}
    (H : newfstatat_core_spec dirfd pathp flag i m .unmodeled) :
    (if !(modeled_statat_flags flag) then
        LinuxSem.LinuxProcessSem.unmodeled
     else
        match read_cstr i.in_mem pathp with
        | .CstrTooLong => err_ret ENAMETOOLONG
        | .CstrFault => err_ret EFAULT
        | .CstrOk p =>
            if path_eqb p [] then err_ret ENOENT
            else if !(bv_eqb dirfd AT_FDCWD32) then
              LinuxSem.LinuxProcessSem.unmodeled
            else if path_eqb p dot_path then
              LinuxSem.LinuxProcessSem.unmodeled
            else
              match fs_lookup (m_fs m) p with
              | none => err_ret ENOENT
              | some _ => LinuxSem.LinuxProcessSem.unmodeled) i m
      .unmodeled := by
  unfold newfstatat_core_spec at H
  rcases H with h | ⟨i', m', evs1, h1, h2⟩
  · exact nomatch h
  · have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i' m' evs1) := h1.symm
    simp only [Outcome.ok.injEq] at h1'
    obtain ⟨rfl, rfl, rfl⟩ := h1'
    rcases h2 with h2 | ⟨m0, m2, evs3, h4, h5⟩
    · exact nomatch h2
    · have h4' : (Outcome.ok m m ([] : List event)) = (Outcome.ok m0 m2 evs3) := h4.symm
      simp only [Outcome.ok.injEq] at h4'
      obtain ⟨rfl, rfl, rfl⟩ := h4'
      exact h5

theorem check_newfstatat_complete_ok (i : SyscallInput) (dirfd pathp flag : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : newfstatat_spec dirfd pathp flag i m (.ok eff m' evs)) :
    check_newfstatat i dirfd pathp flag eff m = .CheckOk m' evs := by
  unfold newfstatat_spec at H
  have H1 : record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (newfstatat_core_spec dirfd pathp flag) i m (.ok eff m' evs) :=
    input_bind_ok_inv _ i m eff m' evs H
  obtain ⟨core, Hcore, heff⟩ :=
    record_copyins_ok_inv [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (newfstatat_core_spec dirfd pathp flag) i m eff m' evs H1
  have hbody := newfstatat_core_body Hcore
  subst heff
  unfold check_newfstatat
  dsimp only
  by_cases hfl : (!(modeled_statat_flags flag)) = true
  · rw [ite_eq_left hfl] at hbody ⊢
    exact nomatch hbody
  · rw [ite_eq_right hfl] at hbody ⊢
    generalize hR : read_cstr i.in_mem pathp = r at hbody
    cases r with
    | CstrTooLong =>
      dsimp only at hbody ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at hbody
      obtain ⟨hcore, hm, hev⟩ := hbody
      subst hcore; rw [hm] at *; subst hev
      simp only [List.append_nil]
      exact check_ret_only_copyins_refl _ (errno_ret ENAMETOOLONG) m []
    | CstrFault =>
      dsimp only at hbody ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at hbody
      obtain ⟨hcore, hm, hev⟩ := hbody
      subst hcore; rw [hm] at *; subst hev
      simp only [List.append_nil]
      exact check_ret_only_copyins_refl _ (errno_ret EFAULT) m []
    | CstrOk p =>
      dsimp only at hbody
      by_cases hpe : path_eqb p [] = true
      · rw [ite_eq_left hpe] at hbody
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at hbody
        obtain ⟨hcore, hm, hev⟩ := hbody
        subst hcore; rw [hm] at *; subst hev
        dsimp only
        rw [ite_eq_left hpe]
        simp only [List.append_nil]
        exact check_ret_only_copyins_refl _ (errno_ret ENOENT) m []
      · rw [ite_eq_right hpe] at hbody
        by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
        · rw [ite_eq_left hd] at hbody
          exact nomatch hbody
        · rw [ite_eq_right hd] at hbody
          by_cases hdot : path_eqb p dot_path = true
          · rw [ite_eq_left hdot] at hbody
            exact nomatch hbody
          · rw [ite_eq_right hdot] at hbody
            generalize hfs : fs_lookup (m_fs m) p = lk at hbody
            cases lk with
            | none =>
              dsimp only at hbody
              simp only [err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hbody
              obtain ⟨hcore, hm, hev⟩ := hbody
              subst hcore; rw [hm] at *; subst hev
              dsimp only
              rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs]
              simp only [List.append_nil]
              exact check_ret_only_copyins_refl _ (errno_ret ENOENT) m []
            | some data =>
              exact nomatch hbody

theorem check_newfstatat_complete_unmodeled (i : SyscallInput) (dirfd pathp flag : word)
    (m : Model) (eff : SyscallEffect)
    (H : newfstatat_spec dirfd pathp flag i m .unmodeled) :
    check_newfstatat i dirfd pathp flag eff m = .CheckUnmodeled := by
  unfold newfstatat_spec at H
  have H1 : record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (newfstatat_core_spec dirfd pathp flag) i m .unmodeled :=
    input_bind_unmodeled_inv _ i m H
  have H2 : newfstatat_core_spec dirfd pathp flag i m .unmodeled :=
    record_copyins_unmodeled_inv _ (newfstatat_core_spec dirfd pathp flag) i m H1
  have hbody := newfstatat_core_body_unmodeled H2
  unfold check_newfstatat
  dsimp only
  by_cases hfl : (!(modeled_statat_flags flag)) = true
  · rw [ite_eq_left hfl] at hbody ⊢
  · rw [ite_eq_right hfl] at hbody ⊢
    generalize hR : read_cstr i.in_mem pathp = r at hbody
    cases r with
    | CstrTooLong =>
      dsimp only at hbody ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at hbody
      exact nomatch hbody
    | CstrFault =>
      dsimp only at hbody ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at hbody
      exact nomatch hbody
    | CstrOk p =>
      dsimp only at hbody
      by_cases hpe : path_eqb p [] = true
      · rw [ite_eq_left hpe] at hbody
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at hbody
        exact nomatch hbody
      · rw [ite_eq_right hpe] at hbody
        by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
        · rw [ite_eq_left hd] at hbody
          dsimp only
          rw [ite_eq_right hpe, ite_eq_left hd]
        · rw [ite_eq_right hd] at hbody
          by_cases hdot : path_eqb p dot_path = true
          · rw [ite_eq_left hdot] at hbody
            dsimp only
            rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_left hdot]
          · rw [ite_eq_right hdot] at hbody
            generalize hfs : fs_lookup (m_fs m) p = lk at hbody
            cases lk with
            | none =>
              dsimp only at hbody
              simp only [err_ret, ret_only,
                LinuxSem.LinuxProcessSem.pure] at hbody
              exact nomatch hbody
            | some data =>
              dsimp only at hbody ⊢
              rw [ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs]

/- =========================================================================
   fstat (80)
   ========================================================================= -/

/-- The delivering half of [Stat.fstat_file_spec], mirroring its
    [choose] arm for arm.  The effect must be ONE 128-byte write at
    [statbuf] returning 0 and nothing else — no zero range, no unmap, no
    symbolic copy, and an EMPTY copy-in ledger, because [fstat] takes
    its descriptor in a register and reads no user byte at all.  The
    bytes themselves are then judged by the two predicates the spec
    chooses under, plus the pin.

    THE PIN IS INSTALLED HERE on the branch that had none, exactly as
    [Checks.Sys.Kernel.Sys]'s [check_uname_copy] installs the UTS name:
    the bytes are the KERNEL's, so the model records what it was shown
    rather than reconstructing it. -/
def check_fstat_deliver_by (ok : List byte → Bool) (statbuf : word)
    (p : Fs.path) (pin : Option (List byte)) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨r, [(a, bs)], [], [], [], []⟩ =>
      if !(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf) then .CheckReject
      else if !(stat_buf_wf bs && ok bs) then .CheckReject
      else match pin with
           | some b0 => if stat_stable_eqb bs b0 then .CheckOk m [] else .CheckReject
           | none => .CheckOk (with_statpin p bs m) []
  | _ => .CheckReject

/-- The file arms' delivery: the predicate is the file's [st_size]
    implication.  [check_fstat_devnull] below instantiates the same
    acceptor with the device's assertions. -/
def check_fstat_deliver (statbuf : word) (n : Nat) (p : Fs.path)
    (pin : Option (List byte)) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_fstat_deliver_by (stat_size_ok n) statbuf p pin eff m

/-- The file arms of [Stat.fstat_spec], branch for branch with
    [Stat.fstat_file_spec]: an unlinked path and a partially writable
    destination decline, [access_ok]'s refusal is -EFAULT, and the rest
    is the delivery above. -/
def check_fstat_file (i : SyscallInput) (p : Fs.path) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) p with
  | none => .CheckUnmodeled
  | some data =>
      if !(access_okb statbuf STAT_SIZE)
      then check_ret_only eff (errno_ret EFAULT) m []
      else
        match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
        | none => .CheckUnmodeled
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0) then .CheckUnmodeled
                else check_fstat_deliver statbuf data.length p (some b0) eff m
            | none => check_fstat_deliver statbuf data.length p none eff m

theorem check_fstat_deliver_by_no_unmodeled (ok : List byte → Bool) (statbuf : word)
    (p : Fs.path) (pin : Option (List byte)) (eff : SyscallEffect) (m : Model) :
    check_fstat_deliver_by ok statbuf p pin eff m ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_fstat_deliver_by
  cases ws with
  | nil => cases zs <;> cases us <;> cases cs <;> cases copyins <;> simp
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> simp
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;>
        dsimp only
      · by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf)) = true
        · rw [ite_eq_left hg]; simp
        · rw [ite_eq_right hg]
          by_cases hw : (!(stat_buf_wf bs && ok bs)) = true
          · rw [ite_eq_left hw]; simp
          · rw [ite_eq_right hw]
            cases pin with
            | none => simp
            | some b0 =>
              dsimp only
              by_cases hs : stat_stable_eqb bs b0 = true
              · rw [ite_eq_left hs]; simp
              · rw [ite_eq_right hs]; simp
      all_goals simp

theorem check_fstat_deliver_no_unmodeled (statbuf : word) (n : Nat) (p : Fs.path)
    (pin : Option (List byte)) (eff : SyscallEffect) (m : Model) :
    check_fstat_deliver statbuf n p pin eff m ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_fstat_deliver check_fstat_deliver_by
  cases ws with
  | nil => cases zs <;> cases us <;> cases cs <;> cases copyins <;> simp
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> simp
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;>
        dsimp only
      · by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf)) = true
        · rw [ite_eq_left hg]; simp
        · rw [ite_eq_right hg]
          by_cases hw : (!(stat_buf_wf bs && stat_size_ok n bs)) = true
          · rw [ite_eq_left hw]; simp
          · rw [ite_eq_right hw]
            cases pin with
            | none => simp
            | some b0 =>
              dsimp only
              by_cases hs : stat_stable_eqb bs b0 = true
              · rw [ite_eq_left hs]; simp
              · rw [ite_eq_right hs]; simp
      all_goals simp

theorem check_fstat_deliver_by_ok (ok : List byte → Bool) (statbuf : word)
    (p : Fs.path) (pin : Option (List byte)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_fstat_deliver_by ok statbuf p pin eff m = .CheckOk m' evs) :
    ∃ bs, eff = mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []
      ∧ evs = []
      ∧ stat_buf_wf bs = true
      ∧ ok bs = true
      ∧ ((∃ b0, pin = some b0 ∧ stat_stable_eqb bs b0 = true ∧ m' = m)
         ∨ (pin = none ∧ m' = with_statpin p bs m)) := by
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_fstat_deliver_by at H
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
    all_goals exact nomatch H
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
      all_goals exact nomatch H
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
      by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf)) = true
      · rw [ite_eq_left hg] at H
        exact nomatch H
      · rw [ite_eq_right hg] at H
        have hg' : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf) = true := by
          simpa using hg
        simp only [Bool.and_eq_true] at hg'
        obtain ⟨hr, ha⟩ := hg'
        have hr' : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r _).mp hr
        have ha' : a = statbuf := (Fs.bv_eqb_eq a statbuf).mp ha
        by_cases hw : (!(stat_buf_wf bs && ok bs)) = true
        · rw [ite_eq_left hw] at H
          exact nomatch H
        · rw [ite_eq_right hw] at H
          have hw' : (stat_buf_wf bs && ok bs) = true := by simpa using hw
          simp only [Bool.and_eq_true] at hw'
          obtain ⟨hwf, hok⟩ := hw'
          cases pin with
          | none =>
            dsimp only at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨hm, hevs⟩ := H
            exact ⟨bs, by subst hr'; subst ha'; rfl, hevs.symm, hwf, hok,
              Or.inr ⟨rfl, hm.symm⟩⟩
          | some b0 =>
            dsimp only at H
            by_cases hs : stat_stable_eqb bs b0 = true
            · rw [ite_eq_left hs] at H
              simp only [check_result.CheckOk.injEq] at H
              obtain ⟨hm, hevs⟩ := H
              exact ⟨bs, by subst hr'; subst ha'; rfl, hevs.symm, hwf, hok,
                Or.inl ⟨b0, rfl, hs, hm.symm⟩⟩
            · rw [ite_eq_right hs] at H
              exact nomatch H
      all_goals exact nomatch H

theorem check_fstat_deliver_ok (statbuf : word) (n : Nat) (p : Fs.path)
    (pin : Option (List byte)) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_fstat_deliver statbuf n p pin eff m = .CheckOk m' evs) :
    ∃ bs, eff = mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []
      ∧ evs = []
      ∧ stat_buf_wf bs = true
      ∧ stat_size_ok n bs = true
      ∧ ((∃ b0, pin = some b0 ∧ stat_stable_eqb bs b0 = true ∧ m' = m)
         ∨ (pin = none ∧ m' = with_statpin p bs m)) := by
  obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
  unfold check_fstat_deliver check_fstat_deliver_by at H
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
    all_goals exact nomatch H
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
      all_goals exact nomatch H
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
      by_cases hg : (!(bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf)) = true
      · rw [ite_eq_left hg] at H
        exact nomatch H
      · rw [ite_eq_right hg] at H
        have hg' : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a statbuf) = true := by
          simpa using hg
        simp only [Bool.and_eq_true] at hg'
        obtain ⟨hr, ha⟩ := hg'
        have hr' : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r _).mp hr
        have ha' : a = statbuf := (Fs.bv_eqb_eq a statbuf).mp ha
        by_cases hw : (!(stat_buf_wf bs && stat_size_ok n bs)) = true
        · rw [ite_eq_left hw] at H
          exact nomatch H
        · rw [ite_eq_right hw] at H
          have hw' : (stat_buf_wf bs && stat_size_ok n bs) = true := by simpa using hw
          simp only [Bool.and_eq_true] at hw'
          obtain ⟨hwf, hok⟩ := hw'
          cases pin with
          | none =>
            dsimp only at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨hm, hevs⟩ := H
            exact ⟨bs, by subst hr'; subst ha'; rfl, hevs.symm, hwf, hok,
              Or.inr ⟨rfl, hm.symm⟩⟩
          | some b0 =>
            dsimp only at H
            by_cases hs : stat_stable_eqb bs b0 = true
            · rw [ite_eq_left hs] at H
              simp only [check_result.CheckOk.injEq] at H
              obtain ⟨hm, hevs⟩ := H
              exact ⟨bs, by subst hr'; subst ha'; rfl, hevs.symm, hwf, hok,
                Or.inl ⟨b0, rfl, hs, hm.symm⟩⟩
            · rw [ite_eq_right hs] at H
              exact nomatch H
      all_goals exact nomatch H

/-- Invert one `seqSpec (modifySpec f) (pure e)` step — the
    effect is [e], the model is [f m], and nothing is emitted.
    [Stat.fstat_file_spec]'s pinning arm is the one call site. -/
private theorem seqSpec_modify_pure_inv (f : Model → Model) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (modifySpec f) (pure e) i m (.ok eff m' evs)) :
    eff = e ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m2, evs1, evs2, hm, hr, hevs⟩ := H
  cases hm
  simp only [List.nil_append] at hevs
  cases hr
  exact ⟨rfl, rfl, by simpa using hevs⟩

/-- `pure` never declines — the second component of both
    [Stat.fstat_file_spec] arms. -/
private theorem pure_no_unmodeled (e : SyscallEffect) (i : SyscallInput) (m : Model) :
    ¬ (LinuxSem.LinuxProcessSem.pure e : SysSpec SyscallEffect) i m
      .unmodeled := by
  simp [LinuxSem.LinuxProcessSem.pure]

/-- …and neither does `seqSpec (modifySpec f) (pure e)`. -/
private theorem seqSpec_modify_pure_no_unmodeled (f : Model → Model) (e : SyscallEffect)
    (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (pure e) i m .unmodeled := by
  intro H
  rcases H with h | ⟨u, m1, evs1, h, hk⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · exact pure_no_unmodeled e i _ hk

/-- A [choose] never declines, so a `choose`-headed spec whose continuation
    never declines has no `.unmodeled` outcome. -/
private theorem choose_bind_no_unmodeled {A : Type} (P : A → Prop)
    (k : A → SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (hk : ∀ (a : A) (m' : Model), ¬ k a i m' .unmodeled) :
    ¬ bind (choose P) k i m .unmodeled := by
  intro H
  simp only [LinuxSem.LinuxProcessSem.bind,
    LinuxSem.LinuxProcessSem.choose] at H
  rcases H with h | ⟨a, m1, evs1, hch, hk'⟩
  · exact nomatch h
  · exact hk a m1 hk'

/-- The single-[choose] step of [Stat.fstat_file_spec]: the chosen `bs`
    satisfies `P`, the model does not move and nothing is emitted.
    Stated here, as above. -/
private theorem choose_bind_ok_inv {A : Type} (P : A → Prop) (k : A → SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (choose P) k i m (.ok eff m' evs)) :
    ∃ bs, P bs ∧ k bs i m (.ok eff m' evs) := by
  obtain ⟨bs, m1, evs1, evs2, hch, hcont, hevs⟩ := H
  obtain ⟨bs0, hP, heq⟩ := hch
  have heq' : (Outcome.ok bs0 m ([] : List event)) = (Outcome.ok bs m1 evs1) := heq.symm
  simp only [Outcome.ok.injEq] at heq'
  obtain ⟨hbs, hm1, hev1⟩ := heq'
  rw [← hbs, ← hm1] at hcont
  rw [← hev1] at hevs
  simp only [List.nil_append] at hevs
  rw [← hevs] at hcont
  exact ⟨bs0, hP, hcont⟩

theorem check_fstat_file_sound_ok (i : SyscallInput) (p : Fs.path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fstat_file i p statbuf eff m = .CheckOk m' evs) :
    fstat_file_spec p statbuf i m (.ok eff m' evs) := by
  unfold check_fstat_file at H
  unfold fstat_file_spec
  refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
  refine bind_ok0 getModelSpec _ i m m m _ m' evs (getModel_ok i m) ?_
  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H ⊢
    exact nomatch H
  | some data =>
    dsimp only at H ⊢
    by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
    · rw [ite_eq_left ha] at H ⊢
      obtain ⟨heff, hm, hevs⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
      subst heff; rw [hm] at *; subst hevs
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right ha] at H ⊢
      generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
        at H ⊢
      cases w with
      | none =>
        dsimp only at H ⊢
        exact nomatch H
      | some w =>
        dsimp only at H ⊢
        generalize hp : statpin_lookup (m_statpins m) p = pin at H ⊢
        cases pin with
        | some b0 =>
          dsimp only at H ⊢
          by_cases hb : (!(stat_buf_wf b0)) = true
          · rw [ite_eq_left hb] at H ⊢
            exact nomatch H
          · rw [ite_eq_right hb] at H ⊢
            obtain ⟨bs, heff, hevs, hwf, hsz, hpin⟩ :=
              check_fstat_deliver_ok statbuf data.length p (some b0) eff m m' evs H
            rw [heff, hevs]
            rcases hpin with ⟨b1, hpin, hs, hm⟩ | ⟨hpin, hm⟩
            · have hb1 : b1 = b0 := by simpa using hpin.symm
              rw [hb1] at hs
              rw [hm]
              refine bind_ok0 (choose (fun bs : List byte =>
                  stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true ∧
                  stat_stable_eqb bs b0 = true)) _ i m bs m _ m []
                (choose_ok _ bs i m ⟨hwf, hsz, hs⟩) ?_
              simp only [LinuxSem.LinuxProcessSem.pure]
            · exact nomatch hpin
        | none =>
          dsimp only at H ⊢
          obtain ⟨bs, heff, hevs, hwf, hsz, hpin⟩ :=
            check_fstat_deliver_ok statbuf data.length p none eff m m' evs H
          rw [heff, hevs]
          rcases hpin with ⟨b1, hpin, hs, hm⟩ | ⟨hpin, hm⟩
          · exact nomatch hpin
          · rw [hm]
            refine bind_ok0 (choose (fun bs : List byte =>
                stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true)) _ i m bs m
              _ (with_statpin p bs m) [] (choose_ok _ bs i m ⟨hwf, hsz⟩) ?_
            refine bind_ok0 (modifySpec (with_statpin p bs)) _ i m () (with_statpin p bs m)
              _ (with_statpin p bs m) [] (modify_ok _ i m) ?_
            simp only [LinuxSem.LinuxProcessSem.pure]

theorem check_fstat_file_sound_unmodeled (i : SyscallInput) (p : Fs.path) (statbuf : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_fstat_file i p statbuf eff m = .CheckUnmodeled) :
    fstat_file_spec p statbuf i m .unmodeled := by
  unfold check_fstat_file at H
  unfold fstat_file_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H ⊢
    exact unmodeled_intro i m
  | some data =>
    dsimp only at H ⊢
    by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
    · rw [ite_eq_left ha] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    · rw [ite_eq_right ha] at H ⊢
      generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
        at H ⊢
      cases w with
      | none =>
        dsimp only at H ⊢
        exact unmodeled_intro i m
      | some w =>
        dsimp only at H ⊢
        generalize hp : statpin_lookup (m_statpins m) p = pin at H ⊢
        cases pin with
        | some b0 =>
          dsimp only at H ⊢
          by_cases hb : (!(stat_buf_wf b0)) = true
          · rw [ite_eq_left hb] at H ⊢
            exact unmodeled_intro i m
          · rw [ite_eq_right hb] at H ⊢
            exact absurd H
              (check_fstat_deliver_no_unmodeled statbuf data.length p (some b0) eff m)
        | none =>
          dsimp only at H ⊢
          exact absurd H
            (check_fstat_deliver_no_unmodeled statbuf data.length p none eff m)

theorem check_fstat_file_complete_ok (i : SyscallInput) (p : Fs.path) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : fstat_file_spec p statbuf i m (.ok eff m' evs)) :
    check_fstat_file i p statbuf eff m = .CheckOk m' evs := by
  unfold fstat_file_spec at H
  obtain ⟨i0, m1, evs1, evs2, h1, h2, h3⟩ := H
  have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i0 m1 evs1) := h1.symm
  simp only [Outcome.ok.injEq] at h1'
  obtain ⟨rfl, rfl, rfl⟩ := h1'
  simp only [List.nil_append] at h3
  simp only [getModelSpec, bind_getModel] at h2
  rw [← h3] at h2
  unfold check_fstat_file
  generalize hfs : fs_lookup (m_fs m) p = lk at h2 ⊢
  cases lk with
  | none =>
    dsimp only at h2 ⊢
    exact nomatch h2
  | some data =>
    dsimp only at h2 ⊢
    by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
    · rw [ite_eq_left ha] at h2 ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right ha] at h2 ⊢
      generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
        at h2 ⊢
      cases w with
      | none =>
        dsimp only at h2 ⊢
        exact nomatch h2
      | some w =>
        dsimp only at h2 ⊢
        generalize hp : statpin_lookup (m_statpins m) p = pin at h2 ⊢
        cases pin with
        | some b0 =>
          dsimp only at h2 ⊢
          by_cases hb : (!(stat_buf_wf b0)) = true
          · rw [ite_eq_left hb] at h2 ⊢
            exact nomatch h2
          · rw [ite_eq_right hb] at h2 ⊢
            obtain ⟨bs, hP, hcont⟩ := choose_bind_ok_inv _ _ i m eff m' evs h2
            obtain ⟨hwf, hsz, hst⟩ := hP
            simp only [LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at hcont
            obtain ⟨heff, hm, hevs⟩ := hcont
            rw [heff, hm, hevs]
            unfold check_fstat_deliver check_fstat_deliver_by
            dsimp only
            rw [ite_eq_right (by simp [bv_eqb_refl])]
            simp [hwf, hsz, hst]
        | none =>
          dsimp only at h2 ⊢
          obtain ⟨bs, hP, hcont⟩ := choose_bind_ok_inv _ _ i m eff m' evs h2
          obtain ⟨hwf, hsz⟩ := hP
          obtain ⟨heff, hm, hevs⟩ :=
            seqSpec_modify_pure_inv (with_statpin p bs)
              (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []) i m eff m' evs hcont
          rw [heff, hm, hevs]
          unfold check_fstat_deliver check_fstat_deliver_by
          dsimp only
          rw [ite_eq_right (by simp [bv_eqb_refl])]
          simp [hwf, hsz]

/-- The character-device arm, branch for branch with
    [Stat.fstat_chrdev_spec]: no [fs_lookup], the pin checked against
    both predicates, and the delivery judged under the device's [ok].
    The null and random devices below are its two instances, as the
    spec's are. -/
def check_fstat_chrdev (ok : List byte → Bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(access_okb statbuf STAT_SIZE)
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
    | none => .CheckUnmodeled
    | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
            if !(stat_buf_wf b0 && ok b0) then .CheckUnmodeled
            else check_fstat_deliver_by ok statbuf p (some b0) eff m
        | none => check_fstat_deliver_by ok statbuf p none eff m

theorem check_fstat_chrdev_sound_ok (ok : List byte → Bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_fstat_chrdev ok p i statbuf eff m = .CheckOk m' evs) :
    fstat_chrdev_spec p ok statbuf i m (.ok eff m' evs) := by
  unfold check_fstat_chrdev at H
  unfold fstat_chrdev_spec
  refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
  refine bind_ok0 getModelSpec _ i m m m _ m' evs (getModel_ok i m) ?_
  by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
  · rw [ite_eq_left ha] at H ⊢
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
    subst heff; rw [hm] at *; subst hevs
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right ha] at H ⊢
    generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
      at H ⊢
    cases w with
    | none =>
      dsimp only at H ⊢
      exact nomatch H
    | some w =>
      dsimp only at H ⊢
      generalize hp : statpin_lookup (m_statpins m) p = pin at H ⊢
      cases pin with
      | some b0 =>
        dsimp only at H ⊢
        by_cases hb : (!(stat_buf_wf b0 && ok b0)) = true
        · rw [ite_eq_left hb] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hb] at H ⊢
          obtain ⟨bs, heff, hevs, hwf, hok, hpin⟩ :=
            check_fstat_deliver_by_ok ok statbuf p (some b0) eff m m' evs H
          rw [heff, hevs]
          rcases hpin with ⟨b1, hpin, hs, hm⟩ | ⟨hpin, hm⟩
          · have hb1 : b1 = b0 := by simpa using hpin.symm
            rw [hb1] at hs
            rw [hm]
            refine bind_ok0 (choose (fun bs : List byte =>
                stat_buf_wf bs = true ∧ ok bs = true ∧
                stat_stable_eqb bs b0 = true)) _ i m bs m _ m []
              (choose_ok _ bs i m ⟨hwf, hok, hs⟩) ?_
            simp only [LinuxSem.LinuxProcessSem.pure]
          · exact nomatch hpin
      | none =>
        dsimp only at H ⊢
        obtain ⟨bs, heff, hevs, hwf, hok, hpin⟩ :=
          check_fstat_deliver_by_ok ok statbuf p none eff m m' evs H
        rw [heff, hevs]
        rcases hpin with ⟨b1, hpin, hs, hm⟩ | ⟨hpin, hm⟩
        · exact nomatch hpin
        · rw [hm]
          refine bind_ok0 (choose (fun bs : List byte =>
              stat_buf_wf bs = true ∧ ok bs = true)) _ i m bs m
            _ (with_statpin p bs m) [] (choose_ok _ bs i m ⟨hwf, hok⟩) ?_
          refine bind_ok0 (modifySpec (with_statpin p bs)) _ i m () (with_statpin p bs m)
            _ (with_statpin p bs m) [] (modify_ok _ i m) ?_
          simp only [LinuxSem.LinuxProcessSem.pure]

theorem check_fstat_chrdev_sound_unmodeled (ok : List byte → Bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m : Model)
    (H : check_fstat_chrdev ok p i statbuf eff m = .CheckUnmodeled) :
    fstat_chrdev_spec p ok statbuf i m .unmodeled := by
  unfold check_fstat_chrdev at H
  unfold fstat_chrdev_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
  · rw [ite_eq_left ha] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  · rw [ite_eq_right ha] at H ⊢
    generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
      at H ⊢
    cases w with
    | none =>
      dsimp only at H ⊢
      exact unmodeled_intro i m
    | some w =>
      dsimp only at H ⊢
      generalize hp : statpin_lookup (m_statpins m) p = pin at H ⊢
      cases pin with
      | some b0 =>
        dsimp only at H ⊢
        by_cases hb : (!(stat_buf_wf b0 && ok b0)) = true
        · rw [ite_eq_left hb] at H ⊢
          exact unmodeled_intro i m
        · rw [ite_eq_right hb] at H ⊢
          exact absurd H
            (check_fstat_deliver_by_no_unmodeled ok statbuf p (some b0) eff m)
      | none =>
        dsimp only at H ⊢
        exact absurd H
          (check_fstat_deliver_by_no_unmodeled ok statbuf p none eff m)

theorem check_fstat_chrdev_complete_ok (ok : List byte → Bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : fstat_chrdev_spec p ok statbuf i m (.ok eff m' evs)) :
    check_fstat_chrdev ok p i statbuf eff m = .CheckOk m' evs := by
  unfold fstat_chrdev_spec at H
  obtain ⟨i0, m1, evs1, evs2, h1, h2, h3⟩ := H
  have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i0 m1 evs1) := h1.symm
  simp only [Outcome.ok.injEq] at h1'
  obtain ⟨rfl, rfl, rfl⟩ := h1'
  simp only [List.nil_append] at h3
  simp only [getModelSpec, bind_getModel] at h2
  rw [← h3] at h2
  unfold check_fstat_chrdev
  by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
  · rw [ite_eq_left ha] at h2 ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right ha] at h2 ⊢
    generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
      at h2 ⊢
    cases w with
    | none =>
      dsimp only at h2 ⊢
      exact nomatch h2
    | some w =>
      dsimp only at h2 ⊢
      generalize hp : statpin_lookup (m_statpins m) p = pin at h2 ⊢
      cases pin with
      | some b0 =>
        dsimp only at h2 ⊢
        by_cases hb : (!(stat_buf_wf b0 && ok b0)) = true
        · rw [ite_eq_left hb] at h2 ⊢
          exact nomatch h2
        · rw [ite_eq_right hb] at h2 ⊢
          obtain ⟨bs, hP, hcont⟩ := choose_bind_ok_inv _ _ i m eff m' evs h2
          obtain ⟨hwf, hok, hst⟩ := hP
          simp only [LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at hcont
          obtain ⟨heff, hm, hevs⟩ := hcont
          rw [heff, hm, hevs]
          unfold check_fstat_deliver_by
          dsimp only
          rw [ite_eq_right (by simp [bv_eqb_refl])]
          simp [hwf, hok, hst]
      | none =>
        dsimp only at h2 ⊢
        obtain ⟨bs, hP, hcont⟩ := choose_bind_ok_inv _ _ i m eff m' evs h2
        obtain ⟨hwf, hok⟩ := hP
        obtain ⟨heff, hm, hevs⟩ :=
          seqSpec_modify_pure_inv (with_statpin p bs)
            (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] []) i m eff m' evs hcont
        rw [heff, hm, hevs]
        unfold check_fstat_deliver_by
        dsimp only
        rw [ite_eq_right (by simp [bv_eqb_refl])]
        simp [hwf, hok]

theorem check_fstat_chrdev_complete_unmodeled (ok : List byte → Bool) (p : Fs.path)
    (i : SyscallInput) (statbuf : word) (m : Model) (eff : SyscallEffect)
    (H : fstat_chrdev_spec p ok statbuf i m .unmodeled) :
    check_fstat_chrdev ok p i statbuf eff m = .CheckUnmodeled := by
  unfold fstat_chrdev_spec at H
  rcases H with h | ⟨i0, m1, evs1, h1, h2⟩
  · exact nomatch h
  · have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i0 m1 evs1) := h1.symm
    simp only [Outcome.ok.injEq] at h1'
    obtain ⟨rfl, rfl, rfl⟩ := h1'
    rcases h2 with h2 | ⟨m0, m2, evs3, h4, h5⟩
    · exact nomatch h2
    · have h4' : (Outcome.ok m m ([] : List event)) = (Outcome.ok m0 m2 evs3) := h4.symm
      simp only [Outcome.ok.injEq] at h4'
      obtain ⟨rfl, rfl, rfl⟩ := h4'
      unfold check_fstat_chrdev
      by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
      · simp only [ite_eq_left ha] at h5 ⊢
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at h5
        exact nomatch h5
      · simp only [ite_eq_right ha] at h5 ⊢
        generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
          at h5 ⊢
        cases w with
        | none => dsimp only at h5 ⊢
        | some w =>
          dsimp only at h5 ⊢
          generalize hp : statpin_lookup (m_statpins m) p = pin at h5 ⊢
          cases pin with
          | some b0 =>
            dsimp only at h5 ⊢
            by_cases hb : (!(stat_buf_wf b0 && ok b0)) = true
            · simp only [ite_eq_left hb] at h5 ⊢
            · simp only [ite_eq_right hb] at h5 ⊢
              exact absurd h5
                (choose_bind_no_unmodeled _ _ i m (fun bs m' =>
                  pure_no_unmodeled _ i m'))
          | none =>
            dsimp only at h5 ⊢
            exact absurd h5
              (choose_bind_no_unmodeled _ _ i m (fun bs m' =>
                seqSpec_modify_pure_no_unmodeled _ _ i m'))

/-- The two instances, and their lemmas by instantiation. -/
def check_fstat_devnull (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_chrdev stat_devnull_ok devnull_path i statbuf eff m

def check_fstat_urandom (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  check_fstat_chrdev stat_urandom_ok urandom_path i statbuf eff m

theorem check_fstat_devnull_sound_ok (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fstat_devnull i statbuf eff m = .CheckOk m' evs) :
    fstat_devnull_spec statbuf i m (.ok eff m' evs) :=
  check_fstat_chrdev_sound_ok stat_devnull_ok devnull_path i statbuf eff m m' evs H

theorem check_fstat_devnull_sound_unmodeled (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_fstat_devnull i statbuf eff m = .CheckUnmodeled) :
    fstat_devnull_spec statbuf i m .unmodeled :=
  check_fstat_chrdev_sound_unmodeled stat_devnull_ok devnull_path i statbuf eff m H

theorem check_fstat_devnull_complete_ok (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : fstat_devnull_spec statbuf i m (.ok eff m' evs)) :
    check_fstat_devnull i statbuf eff m = .CheckOk m' evs :=
  check_fstat_chrdev_complete_ok stat_devnull_ok devnull_path i statbuf eff m m' evs H

theorem check_fstat_devnull_complete_unmodeled (i : SyscallInput) (statbuf : word)
    (m : Model) (eff : SyscallEffect)
    (H : fstat_devnull_spec statbuf i m .unmodeled) :
    check_fstat_devnull i statbuf eff m = .CheckUnmodeled :=
  check_fstat_chrdev_complete_unmodeled stat_devnull_ok devnull_path i statbuf m eff H

theorem check_fstat_urandom_sound_ok (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fstat_urandom i statbuf eff m = .CheckOk m' evs) :
    fstat_urandom_spec statbuf i m (.ok eff m' evs) :=
  check_fstat_chrdev_sound_ok stat_urandom_ok urandom_path i statbuf eff m m' evs H

theorem check_fstat_urandom_sound_unmodeled (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_fstat_urandom i statbuf eff m = .CheckUnmodeled) :
    fstat_urandom_spec statbuf i m .unmodeled :=
  check_fstat_chrdev_sound_unmodeled stat_urandom_ok urandom_path i statbuf eff m H

theorem check_fstat_urandom_complete_ok (i : SyscallInput) (statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : fstat_urandom_spec statbuf i m (.ok eff m' evs)) :
    check_fstat_urandom i statbuf eff m = .CheckOk m' evs :=
  check_fstat_chrdev_complete_ok stat_urandom_ok urandom_path i statbuf eff m m' evs H

theorem check_fstat_urandom_complete_unmodeled (i : SyscallInput) (statbuf : word)
    (m : Model) (eff : SyscallEffect)
    (H : fstat_urandom_spec statbuf i m .unmodeled) :
    check_fstat_urandom i statbuf eff m = .CheckUnmodeled :=
  check_fstat_chrdev_complete_unmodeled stat_urandom_ok urandom_path i statbuf m eff H

theorem check_fstat_file_complete_unmodeled (i : SyscallInput) (p : Fs.path)
    (statbuf : word) (m : Model) (eff : SyscallEffect)
    (H : fstat_file_spec p statbuf i m .unmodeled) :
    check_fstat_file i p statbuf eff m = .CheckUnmodeled := by
  unfold fstat_file_spec at H
  rcases H with h | ⟨i0, m1, evs1, h1, h2⟩
  · exact nomatch h
  · have h1' : (Outcome.ok i m ([] : List event)) = (Outcome.ok i0 m1 evs1) := h1.symm
    simp only [Outcome.ok.injEq] at h1'
    obtain ⟨rfl, rfl, rfl⟩ := h1'
    rcases h2 with h2 | ⟨m0, m2, evs3, h4, h5⟩
    · exact nomatch h2
    · have h4' : (Outcome.ok m m ([] : List event)) = (Outcome.ok m0 m2 evs3) := h4.symm
      simp only [Outcome.ok.injEq] at h4'
      obtain ⟨rfl, rfl, rfl⟩ := h4'
      unfold check_fstat_file
      generalize hfs : fs_lookup (m_fs m) p = lk at h5 ⊢
      cases lk with
      | none => dsimp only at h5 ⊢
      | some data =>
        dsimp only at h5 ⊢
        by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
        · simp only [ite_eq_left ha] at h5 ⊢
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at h5
          exact nomatch h5
        · simp only [ite_eq_right ha] at h5 ⊢
          generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
            at h5 ⊢
          cases w with
          | none => dsimp only at h5 ⊢
          | some w =>
            dsimp only at h5 ⊢
            generalize hp : statpin_lookup (m_statpins m) p = pin at h5 ⊢
            cases pin with
            | some b0 =>
              dsimp only at h5 ⊢
              by_cases hb : (!(stat_buf_wf b0)) = true
              · simp only [ite_eq_left hb] at h5 ⊢
              · simp only [ite_eq_right hb] at h5 ⊢
                exact absurd h5
                  (choose_bind_no_unmodeled _ _ i m (fun bs m' =>
                    pure_no_unmodeled _ i m'))
            | none =>
              dsimp only at h5 ⊢
              exact absurd h5
                (choose_bind_no_unmodeled _ _ i m (fun bs m' =>
                  seqSpec_modify_pure_no_unmodeled _ _ i m'))

/-- fstat: total over [FdEntry], answering on the closed descriptor's
    -EBADF, the four file kinds, which share one inode and so one
    answer, /dev/null and /dev/urandom.  The other four decline as a
    body; see [Stat.fstat_spec] for which of [struct stat]'s twenty
    members each would have to invent, and for why the match carries no
    wildcard. -/
def check_fstat (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) => .CheckUnmodeled
  | some (.FdFile p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileW p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileA p _) => check_fstat_file i p statbuf eff m
  | some (.FdFileRW p _) => check_fstat_file i p statbuf eff m
  | some .FdDir => .CheckUnmodeled
  | some (.FdSocket _) => .CheckUnmodeled
  | some (.FdPipe _ _) => .CheckUnmodeled
  | some (.FdDevNull _ _) => check_fstat_devnull i statbuf eff m
  | some .FdUrandom => check_fstat_urandom i statbuf eff m

theorem check_fstat_sound_ok (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_fstat i fd statbuf eff m = .CheckOk m' evs) :
    fstat_spec fd statbuf i m (.ok eff m' evs) := by
  unfold check_fstat at H
  unfold fstat_spec
  refine bind_ok0 getModelSpec _ i m m m _ m' evs (getModel_ok i m) ?_
  generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H ⊢
    obtain ⟨heff, hm, hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
    subst heff; rw [hm] at *; subst hevs
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
  | some e =>
    try dsimp only at H ⊢
    cases e with
    | FdChannel n => exact nomatch H
    | FdFile p sz => exact check_fstat_file_sound_ok i p statbuf eff m m' evs H
    | FdFileW p sz => exact check_fstat_file_sound_ok i p statbuf eff m m' evs H
    | FdFileA p sz => exact check_fstat_file_sound_ok i p statbuf eff m m' evs H
    | FdFileRW p sz => exact check_fstat_file_sound_ok i p statbuf eff m m' evs H
    | FdDir => exact nomatch H
    | FdSocket s => exact nomatch H
    | FdPipe a b => exact nomatch H
    | FdDevNull a b => exact check_fstat_devnull_sound_ok i statbuf eff m m' evs H
    | FdUrandom => exact check_fstat_urandom_sound_ok i statbuf eff m m' evs H

theorem check_fstat_sound_unmodeled (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_fstat i fd statbuf eff m = .CheckUnmodeled) :
    fstat_spec fd statbuf i m .unmodeled := by
  unfold check_fstat at H
  unfold fstat_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    try dsimp only at H ⊢
    cases e with
    | FdChannel n => rfl
    | FdFile p sz => exact check_fstat_file_sound_unmodeled i p statbuf eff m H
    | FdFileW p sz => exact check_fstat_file_sound_unmodeled i p statbuf eff m H
    | FdFileA p sz => exact check_fstat_file_sound_unmodeled i p statbuf eff m H
    | FdFileRW p sz => exact check_fstat_file_sound_unmodeled i p statbuf eff m H
    | FdDir => rfl
    | FdSocket s => rfl
    | FdPipe a b => rfl
    | FdDevNull a b =>
      exact check_fstat_devnull_sound_unmodeled i statbuf eff m H
    | FdUrandom => exact check_fstat_urandom_sound_unmodeled i statbuf eff m H

theorem check_fstat_complete_ok (i : SyscallInput) (fd statbuf : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : fstat_spec fd statbuf i m (.ok eff m' evs)) :
    check_fstat i fd statbuf eff m = .CheckOk m' evs := by
  unfold fstat_spec at H
  simp only [getModelSpec, bind_getModel] at H
  unfold check_fstat
  generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  | some e =>
    try dsimp only at H ⊢
    cases e with
    | FdChannel n => exact nomatch H
    | FdFile p sz => exact check_fstat_file_complete_ok i p statbuf eff m m' evs H
    | FdFileW p sz => exact check_fstat_file_complete_ok i p statbuf eff m m' evs H
    | FdFileA p sz => exact check_fstat_file_complete_ok i p statbuf eff m m' evs H
    | FdFileRW p sz => exact check_fstat_file_complete_ok i p statbuf eff m m' evs H
    | FdDir => exact nomatch H
    | FdSocket s => exact nomatch H
    | FdPipe a b => exact nomatch H
    | FdDevNull a b => exact check_fstat_devnull_complete_ok i statbuf eff m m' evs H
    | FdUrandom => exact check_fstat_urandom_complete_ok i statbuf eff m m' evs H

theorem check_fstat_complete_unmodeled (i : SyscallInput) (fd statbuf : word)
    (m : Model) (eff : SyscallEffect)
    (H : fstat_spec fd statbuf i m .unmodeled) :
    check_fstat i fd statbuf eff m = .CheckUnmodeled := by
  unfold fstat_spec at H
  rcases H with h | ⟨m0, m1, evs1, h1, h2⟩
  · exact nomatch h
  · have h1' : (Outcome.ok m m ([] : List event)) = (Outcome.ok m0 m1 evs1) := h1.symm
    simp only [Outcome.ok.injEq] at h1'
    obtain ⟨rfl, rfl, rfl⟩ := h1'
    unfold check_fstat
    generalize hfd : fd_lookup (m_fds m) fd = lk at h2 ⊢
    cases lk with
    | none =>
      dsimp only at h2 ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at h2
      exact nomatch h2
    | some e =>
      try dsimp only at h2 ⊢
      cases e with
      | FdChannel n => rfl
      | FdFile p sz => exact check_fstat_file_complete_unmodeled i p statbuf m eff h2
      | FdFileW p sz => exact check_fstat_file_complete_unmodeled i p statbuf m eff h2
      | FdFileA p sz => exact check_fstat_file_complete_unmodeled i p statbuf m eff h2
      | FdFileRW p sz => exact check_fstat_file_complete_unmodeled i p statbuf m eff h2
      | FdDir => rfl
      | FdSocket s => rfl
      | FdPipe a b => rfl
      | FdDevNull a b =>
        exact check_fstat_devnull_complete_unmodeled i statbuf m eff h2
      | FdUrandom => exact check_fstat_urandom_complete_unmodeled i statbuf m eff h2

end LinuxSem.Checks.Sys.Fs.Stat
