/-
  * LinuxProcessSem.Checks.Sys.Kernel.Groups — the getgroups (158) and setgroups (159) checkers, and their proofs

  Answers to Linux [kernel/groups.c]: this file holds the checkers for the syscalls
  defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`).  The length of a group list is compared as an
  `Int` (`((…).length : Int)`), so the tests are the `Int` comparisons
  `n < 0` and `n = 0` — the same decision as the spec's, with the `Bool`
  unboxed, exactly as in `Sys/Kernel/Groups.lean`.

  Each proof steps the spec's model reader with `bind_getModel`, which
  rewrites `bind getModel k i m o` to `k m i m o` in one go.  The rest is
  the spec's branch order: the same `cases` chain, with `by_cases` for the
  split and `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]` to rewrite the
  branch equation everywhere.  `dsimp only` performs the beta/iota/zeta
  reduction, and a `CheckUnmodeled = CheckOk` equation is eliminated by
  `nomatch`.

  Both the spec and the checker place their branch test in front of a whole
  subtree — `getgroups_spec` is a `SysSpec`, a FUNCTION, so its body is an
  `if` at function type (`(if n < 0 then err_ret EINVAL else bind …) i m
  o`).  Lean's `whnf` on such a goal tries to reduce that `if`, which means
  deciding `sint32 gidsetsize < 0`; reducing `sint32` then needs a decision
  procedure on the still-opaque `(w &&& …).toNat`, and the reduction
  recurses without bottoming out (`maximum recursion depth`).  Nothing is
  wrong with the statements — only with `whnf`ing the goal, which
  `by_cases`/`cases` do internally.  Each proof therefore starts by
  `generalize`-ing its conclusion into a local `Q : Prop`, case-splits
  against `Q` (an opaque variable, so no reduction happens), and only then
  rewrites `Q` back into the spec/checker and discharges the branch with
  `simp only`.

  The same reduction is attempted by the `constructorNameAsVariable` linter,
  which normalises binder types; on `check_getgroups_complete_ok` and
  `check_getgroups_complete_unmodeled` — the two declarations whose
  hypothesis is the `getgroups_spec` application — it therefore fails with
  the recursion error above rather than a finding.  It is switched off for
  exactly those two declarations, and nowhere else.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Groups

namespace LinuxSem.Checks.Sys.Kernel.Groups

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
open LinuxSem.Checks.Sys.Prelude

/-! ## getgroups (158) -/

/-- [getgroups] (158): the count, or one of the two -EINVALs, and
    [CheckUnmodeled] on the writing path.  Mirrors
    [Kernel.Groups.getgroups_spec] branch for branch — read that spec
    for the kernel order the branches are in and why the [grouplist]
    pointer is not an argument here either. -/
def check_getgroups (gidsetsize : word) (eff : SyscallEffect) (m : Model) : check_result :=
  let n := sint32 gidsetsize
  if n < 0 then check_ret_only eff (errno_ret EINVAL) m []
  else
    let ng : Int := ((m_creds m).cr_groups.length : Int)
    if NGROUPS_MAX < ng then .CheckUnmodeled
    else if n = 0 then check_ret_only eff (BitVec.ofInt 64 ng) m []
    else if n < ng then check_ret_only eff (errno_ret EINVAL) m []
    else if ng = 0 then check_ret_only eff (BitVec.ofInt 64 0) m []
    else .CheckUnmodeled

theorem check_getgroups_sound_ok (gidsetsize : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_getgroups gidsetsize eff m = .CheckOk m' evs) :
    getgroups_spec gidsetsize i m (.ok eff m' evs) := by
  generalize hP : (getgroups_spec gidsetsize i m (.ok eff m' evs)) = Q at *
  simp only [check_getgroups] at H
  by_cases hneg : sint32 gidsetsize < 0
  · simp only [ite_eq_left hneg] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [getgroups_spec, getModelSpec, ite_eq_left hneg, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hneg] at H
    by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
    · simp only [ite_eq_left hmax] at H
      exact nomatch H
    · simp only [ite_eq_right hmax] at H
      by_cases hzero : sint32 gidsetsize = 0
      · simp only [ite_eq_left hzero] at H
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 ((m_creds m).cr_groups.length : Int))
            m [] m' evs).mp H
        rw [← hP]
        simp only [getgroups_spec, getModelSpec, bind_getModel, ite_eq_right hneg, ite_eq_right hmax,
          ite_eq_left hzero, ret_only, LinuxSem.LinuxProcessSem.pure]
      · simp only [ite_eq_right hzero] at H
        by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
        · simp only [ite_eq_left hsmall] at H
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          rw [← hP]
          simp only [getgroups_spec, getModelSpec, bind_getModel, ite_eq_right hneg, ite_eq_right hmax,
            ite_eq_right hzero, ite_eq_left hsmall, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
        · simp only [ite_eq_right hsmall] at H
          by_cases hempty : ((m_creds m).cr_groups.length : Int) = 0
          · simp only [ite_eq_left hempty] at H
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
            rw [← hP]
            simp only [getgroups_spec, getModelSpec, bind_getModel, ite_eq_right hneg, ite_eq_right hmax,
              ite_eq_right hzero, ite_eq_right hsmall, ite_eq_left hempty, ret_only,
              LinuxSem.LinuxProcessSem.pure]
          · simp only [ite_eq_right hempty] at H
            exact nomatch H

/-- Both declines are the writing path and the impossible-length guard;
    everything else answers. -/
theorem check_getgroups_sound_unmodeled (gidsetsize : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_getgroups gidsetsize eff m = .CheckUnmodeled) :
    getgroups_spec gidsetsize i m .unmodeled := by
  generalize hP : (getgroups_spec gidsetsize i m .unmodeled) = Q at *
  simp only [check_getgroups] at H
  by_cases hneg : sint32 gidsetsize < 0
  · simp only [ite_eq_left hneg] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · simp only [ite_eq_right hneg] at H
    by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
    · simp only [ite_eq_left hmax] at H
      rw [← hP]
      simp only [getgroups_spec, getModelSpec, bind_getModel, ite_eq_right hneg, ite_eq_left hmax,
        unmodeled]
    · simp only [ite_eq_right hmax] at H
      by_cases hzero : sint32 gidsetsize = 0
      · simp only [ite_eq_left hzero] at H
        exact absurd H
          (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 ((m_creds m).cr_groups.length : Int))
            m [])
      · simp only [ite_eq_right hzero] at H
        by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
        · simp only [ite_eq_left hsmall] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · simp only [ite_eq_right hsmall] at H
          by_cases hempty : ((m_creds m).cr_groups.length : Int) = 0
          · simp only [ite_eq_left hempty] at H
            exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
          · simp only [ite_eq_right hempty] at H
            rw [← hP]
            simp only [getgroups_spec, getModelSpec, bind_getModel, ite_eq_right hneg, ite_eq_right hmax,
              ite_eq_right hzero, ite_eq_right hsmall, ite_eq_right hempty, unmodeled]

set_option linter.constructorNameAsVariable false in
theorem check_getgroups_complete_ok (gidsetsize : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : getgroups_spec gidsetsize i m (.ok eff m' evs)) :
    check_getgroups gidsetsize eff m = .CheckOk m' evs := by
  generalize hP : (check_getgroups gidsetsize eff m = .CheckOk m' evs) = Q at *
  simp only [getgroups_spec, getModelSpec] at H
  by_cases hneg : sint32 gidsetsize < 0
  · simp only [ite_eq_left hneg] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_getgroups, ite_eq_left hneg]
    simp [check_ret_only, bv_eqb_refl]
  · simp only [ite_eq_right hneg, bind_getModel] at H
    by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
    · simp only [ite_eq_left hmax] at H
      simp only [unmodeled] at H
      exact nomatch H
    · simp only [ite_eq_right hmax] at H
      by_cases hzero : sint32 gidsetsize = 0
      · simp only [ite_eq_left hzero] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        rw [← hP]
        simp only [check_getgroups, ite_eq_right hneg, ite_eq_right hmax, ite_eq_left hzero]
        simp [check_ret_only, bv_eqb_refl]
      · simp only [ite_eq_right hzero] at H
        by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
        · simp only [ite_eq_left hsmall] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_getgroups, ite_eq_right hneg, ite_eq_right hmax, ite_eq_right hzero, ite_eq_left hsmall]
          simp [check_ret_only, bv_eqb_refl]
        · simp only [ite_eq_right hsmall] at H
          by_cases hempty : ((m_creds m).cr_groups.length : Int) = 0
          · simp only [ite_eq_left hempty] at H
            simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            rw [← hP]
            simp only [check_getgroups, ite_eq_right hneg, ite_eq_right hmax, ite_eq_right hzero, ite_eq_right hsmall,
              ite_eq_left hempty]
            simp [check_ret_only, bv_eqb_refl]
          · simp only [ite_eq_right hempty] at H
            simp only [unmodeled] at H
            exact nomatch H

set_option linter.constructorNameAsVariable false in
theorem check_getgroups_complete_unmodeled (gidsetsize : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : getgroups_spec gidsetsize i m .unmodeled) :
    check_getgroups gidsetsize eff m = .CheckUnmodeled := by
  generalize hP : (check_getgroups gidsetsize eff m = .CheckUnmodeled) = Q at *
  simp only [getgroups_spec, getModelSpec] at H
  by_cases hneg : sint32 gidsetsize < 0
  · simp only [ite_eq_left hneg] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · simp only [ite_eq_right hneg, bind_getModel] at H
    by_cases hmax : NGROUPS_MAX < ((m_creds m).cr_groups.length : Int)
    · simp only [ite_eq_left hmax] at H
      rw [← hP]
      simp only [check_getgroups, ite_eq_right hneg, ite_eq_left hmax]
    · simp only [ite_eq_right hmax] at H
      by_cases hzero : sint32 gidsetsize = 0
      · simp only [ite_eq_left hzero] at H
        simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      · simp only [ite_eq_right hzero] at H
        by_cases hsmall : sint32 gidsetsize < ((m_creds m).cr_groups.length : Int)
        · simp only [ite_eq_left hsmall] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        · simp only [ite_eq_right hsmall] at H
          by_cases hempty : ((m_creds m).cr_groups.length : Int) = 0
          · simp only [ite_eq_left hempty] at H
            simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · simp only [ite_eq_right hempty] at H
            simp only [unmodeled] at H
            rw [← hP]
            simp only [check_getgroups, ite_eq_right hneg, ite_eq_right hmax, ite_eq_right hzero, ite_eq_right hsmall,
              ite_eq_right hempty]

/-! ## setgroups (159) -/

/-- [setgroups] (159): an unprivileged caller is refused -EPERM before
    either argument is read, and a privileged one is DECLINED, because
    the model does not import the list it would write (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/groups.c, [SYSCALL_DEFINE2(setgroups)] /
    [may_setgroups]).
    [Kernel.Groups.setgroups_spec] says what accepting the successful
    half would cost and what the decline costs. -/
def check_setgroups (eff : SyscallEffect) (m : Model) : check_result :=
  if creds_privileged (m_creds m) then .CheckUnmodeled
  else check_ret_only eff (errno_ret EPERM) m []

theorem check_setgroups_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_setgroups eff m = .CheckOk m' evs) :
    setgroups_spec i m (.ok eff m' evs) := by
  generalize hP : (setgroups_spec i m (.ok eff m' evs)) = Q at *
  simp only [check_setgroups] at H
  by_cases hp : creds_privileged (m_creds m) = true
  · simp only [ite_eq_left hp] at H
    exact nomatch H
  · simp only [ite_eq_right hp] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EPERM) m [] m' evs).mp H
    rw [← hP]
    simp only [setgroups_spec, getModelSpec, bind_getModel, ite_eq_right hp, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]

/-- The privileged half is where both sides fail closed. -/
theorem check_setgroups_sound_unmodeled (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_setgroups eff m = .CheckUnmodeled) :
    setgroups_spec i m .unmodeled := by
  generalize hP : (setgroups_spec i m .unmodeled) = Q at *
  simp only [check_setgroups] at H
  by_cases hp : creds_privileged (m_creds m) = true
  · simp only [ite_eq_left hp] at H
    rw [← hP]
    simp only [setgroups_spec, getModelSpec, bind_getModel, ite_eq_left hp, unmodeled]
  · simp only [ite_eq_right hp] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EPERM) m [])

theorem check_setgroups_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : setgroups_spec i m (.ok eff m' evs)) :
    check_setgroups eff m = .CheckOk m' evs := by
  generalize hP : (check_setgroups eff m = .CheckOk m' evs) = Q at *
  simp only [setgroups_spec, getModelSpec, bind_getModel] at H
  by_cases hp : creds_privileged (m_creds m) = true
  · simp only [ite_eq_left hp] at H
    simp only [unmodeled] at H
    exact nomatch H
  · simp only [ite_eq_right hp] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_setgroups, ite_eq_right hp]
    simp [check_ret_only, bv_eqb_refl]

theorem check_setgroups_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect)
    (H : setgroups_spec i m .unmodeled) :
    check_setgroups eff m = .CheckUnmodeled := by
  generalize hP : (check_setgroups eff m = .CheckUnmodeled) = Q at *
  simp only [setgroups_spec, getModelSpec, bind_getModel] at H
  by_cases hp : creds_privileged (m_creds m) = true
  · rw [← hP]
    simp only [check_setgroups, ite_eq_left hp]
  · simp only [ite_eq_right hp] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the branch
    order the proofs above follow, one per claim the matching spec's prose
    makes: `getgroups(0, ·)` answers the count; a negative size is
    -EINVAL before anything else is read; a size too small is -EINVAL
    before any store; the zero-length list answers 0 and never touches the
    pointer; the writing arm is declined; and `setgroups` separates its two
    halves on `creds_privileged`.

    They are sanity checks, not library lemmas.  `check_result` carries no
    `DecidableEq`, so each states the branch as an equation and closes it
    by unfolding the checker and discharging the branch tests with
    `decide`. -/

/-- A model whose process has the given supplementary group list, with
    `mkModel`'s default (unprivileged) credentials: every id is
    `overflow_id`, so `creds_privileged` is false. -/
private def port_model (gs : List word) : Model :=
  with_creds
    { cr_uid := overflow_id, cr_euid := overflow_id, cr_suid := overflow_id
      cr_gid := overflow_id, cr_egid := overflow_id, cr_sgid := overflow_id
      cr_groups := gs }
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none)

/-- The same model with `euid = 0`: the one id `creds_privileged` reads. -/
private def port_model_root (gs : List word) : Model :=
  with_creds
    { cr_uid := overflow_id, cr_euid := BitVec.ofInt 64 0, cr_suid := overflow_id
      cr_gid := overflow_id, cr_egid := overflow_id, cr_sgid := overflow_id
      cr_groups := gs }
    (mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none)

/-- `getgroups(0, <anything>)` answers the count: 2 here. -/
example (eff : SyscallEffect) :
    check_getgroups 0 eff (port_model [4, 5])
      = check_ret_only eff (BitVec.ofInt 64 2) (port_model [4, 5]) [] := by
  have hlen : ((m_creds (port_model [4, 5])).cr_groups.length : Int) = 2 := by decide
  simp only [check_getgroups, hlen, NGROUPS_MAX]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A negative `gidsetsize` is -EINVAL, and it is refused FIRST: this
    model has 2 groups, and the sign check still wins. -/
example (eff : SyscallEffect) :
    check_getgroups (BitVec.ofInt 64 (-1)) eff (port_model [4, 5])
      = check_ret_only eff (errno_ret EINVAL) (port_model [4, 5]) [] := by
  simp only [check_getgroups, NGROUPS_MAX]
  rw [ite_eq_left (by decide)]

/-- A size TOO SMALL is -EINVAL BEFORE any store: 1 slot, 5 groups. -/
example (eff : SyscallEffect) :
    check_getgroups 1 eff (port_model [1, 2, 3, 4, 5])
      = check_ret_only eff (errno_ret EINVAL) (port_model [1, 2, 3, 4, 5]) [] := by
  have hlen : ((m_creds (port_model [1, 2, 3, 4, 5])).cr_groups.length : Int) = 5 := by
    decide
  simp only [check_getgroups, hlen, NGROUPS_MAX]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- The ZERO-LENGTH LIST with `gidsetsize > 0` answers 0 and never touches
    the (unmodeled, and here absent) pointer. -/
example (eff : SyscallEffect) :
    check_getgroups 64 eff (port_model [])
      = check_ret_only eff (BitVec.ofInt 64 0) (port_model []) [] := by
  have hlen : ((m_creds (port_model ([] : List word))).cr_groups.length : Int) = 0 := by
    decide
  simp only [check_getgroups, hlen, NGROUPS_MAX]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]

/-- The WRITING arm — `gidsetsize >= ngroups > 0` — is DECLINED. -/
example (eff : SyscallEffect) :
    check_getgroups 64 eff (port_model [4, 5]) = .CheckUnmodeled := by
  have hlen : ((m_creds (port_model [4, 5])).cr_groups.length : Int) = 2 := by decide
  simp only [check_getgroups, hlen, NGROUPS_MAX]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)]

/-- `setgroups` for an UNPRIVILEGED caller is -EPERM, and the checker reads
    neither argument to say so. -/
example (eff : SyscallEffect) :
    check_setgroups eff (port_model [4, 5])
      = check_ret_only eff (errno_ret EPERM) (port_model [4, 5]) [] := by
  simp only [check_setgroups]
  rw [ite_eq_right (by decide)]

/-- …and the PRIVILEGED half is declined, not faked. -/
example (eff : SyscallEffect) :
    check_setgroups eff (port_model_root [4, 5]) = .CheckUnmodeled := by
  simp only [check_setgroups]
  rw [ite_eq_left (by decide)]

end LinuxSem.Checks.Sys.Kernel.Groups
