/-
  * LinuxProcessSem.Checks.Sys.Fs.Namei — the unlinkat (35) checker, and its proofs

  Answers to Linux [fs/namei.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  `Checks.Sys.Prelude` re-exports the model/state/monad stack and supplies
  [check_result], [check_ret_only], [clear_copyins], [check_copyins_after]
  and their lemmas; `Sys.Fs.Namei` supplies [unlink_found_spec],
  [unlinkat_tmp_spec], [unlinkat_body_spec], [unlinkat_spec] and the three
  introduction lemmas, and is imported directly.

  A file-private definition is `private`: the three local checkers and the
  fifteen local lemmas below — six `_sound`, three `_ok_copyins_nil`, six
  `_complete` — are file-private.

  Four declarations below are PUBLIC and all of the same shape — "this
  checker leaves [m_vmmaps] alone", stated as
  `H : check_X … = .CheckOk m' evs → m_vmmaps m' = m_vmmaps m`: the
  `private` [check_ret_only_frame] and the PUBLIC
  [check_unlink_found_frame], [check_unlinkat_tmp_frame] and
  [check_unlinkat_body_frame].  They exist for
  [Checks/VmMapsDisjoint.lean], which must frame `check_unlinkat`: its
  accepting branch sits in one of the three `private` helpers above,
  and a private definition's equation lemmas are not nameable from
  another module, so that file cannot unfold the helper and the frame
  never closes.  The fact has to be stated HERE, where the helper's
  body is visible — and a PUBLIC theorem rather than a `private` one,
  since `private` would put the fact out of reach for the same reason.  Stating a public fact ABOUT a private definition leaks
  nothing: only the fact travels, not the name.  Each is proved by the
  checker half of the `*_sound_ok` above it.

  The four export proofs need the spec's two opening steps on both sides:
  `bind_ok0 … (input_ok i m)` then `bind_ok0 … (getModel_ok i m)` to BUILD
  the spec, and `bind_input_model_inv` to PEEL it.

  A path is `Fs.path` (`List byte`), and a length test in a `bool`
  definition is `decide (a < b)`.  An effect literal is the anonymous
  constructor pattern `⟨ret, [], [], [], [], []⟩` over `SyscallEffect`; the
  checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`, and the
  spec monad with `.ok` / `.unmodeled`.

  Each checker and its spec place the SAME tests, in the SAME order, at the
  head of a subtree, so each proof walks the two together: `unfold` the
  checker into the hypothesis and the spec into the goal, then
  `generalize … at H ⊢` + `cases` on the scrutinee (`read_cstr`, `tmp_name`,
  `fs_lookup`) so that BOTH sides reduce at once, and `by_cases` +
  `rw [ite_eq_left h] at H ⊢` / `rw [ite_eq_right h] at H ⊢` for each shared test.
  Splitting by name this way avoids the function-type-`if` footgun that
  `Checks/Sys/Kernel/Groups.lean`'s header describes: the tests are never
  decided by `whnf` on the goal, only by the split we name.  Where the two
  sides DIVERGE — the acceptor's `errno_ret_in` test and its zero test,
  which the spec has as an `alt` — the split is on the checker's side alone,
  and the spec is built with `alt_l`/`alt_r`.

  A `CheckUnmodeled`-vs-`CheckOk` equality is closed by `exact nomatch H`,
  and `dsimp only` performs the iota/zeta reduction.  The forward direction
  of `check_ret_only_ok_iff` yields the three equalities, taken by
  `obtain ⟨rfl, rfl, rfl⟩` on its result.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei

namespace LinuxSem.Checks.Sys.Fs.Namei

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Namei
open LinuxSem.Checks.Sys.Prelude

/- =========================================================================
   The acceptors
   ========================================================================= -/

/-- The acceptor for the arm of [Fs.Namei.unlink_found_spec] that can
    succeed: either an injectable errno with no state change, or the
    removal itself, returning 0.  Both take a bare return and FIVE EMPTY
    ledgers — the kernel's unlinkat writes, zeroes, unmaps and copies
    nothing — so only a forged ledger reaches the other half of the
    claim. -/
def check_unlink_result (p : Fs.path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in unlinkat_errnos ret then .CheckOk m []
      else if bv_eqb ret (BitVec.ofInt 64 0)
           then .CheckOk (with_fs (fs_remove (m_fs m) p) m) []
           else .CheckReject
  | _ => .CheckReject

/-- Mirrors [Fs.Namei.unlink_found_spec], the tail both arms share. -/
private def check_unlink_found (p c : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if unlink_rmdir flags then check_ret_only eff (errno_ret ENOTDIR) m []
  else if path_trailing_slash p
  then check_ret_only eff (errno_ret ENOTDIR) m []
  else if fd_names_path (m_fds m) c then .CheckUnmodeled
  else check_unlink_result c eff m

/-- Mirrors [Fs.Namei.unlinkat_tmp_spec]; that definition carries the
    premise, says what the absent key's -ENOENT rests on, and says what
    each decline is for. -/
private def check_unlinkat_tmp (n p c : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if unlink_rmdir flags then .CheckUnmodeled
  else if decide (NAME_MAX < n.length) then .CheckUnmodeled
  else if fs_under (m_fs m) c then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) c with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ => check_unlink_found p c flags eff m

private def check_unlinkat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | .CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | .CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if !(bv_eqb dirfd AT_FDCWD32) then .CheckUnmodeled
      else
        let c := path_strip_trailing_slashes p
        if path_eqb c [] then
          (if unlink_rmdir flags
           then check_ret_only eff (errno_ret EBUSY) m []
           else check_ret_only eff (errno_ret EISDIR) m [])
        else if path_has_slash c then
          (match tmp_name c with
           | some n => check_unlinkat_tmp n p c flags eff m
           | none => .CheckUnmodeled
           )
        else if path_eqb c dot_path then
          (if unlink_rmdir flags
           then check_ret_only eff (errno_ret EINVAL) m []
           else check_ret_only eff (errno_ret EISDIR) m [])
        else if path_eqb c dotdot_path then
          (if unlink_rmdir flags
           then check_ret_only eff (errno_ret ENOTEMPTY) m []
           else check_ret_only eff (errno_ret EISDIR) m [])
        else if decide (NAME_MAX < c.length) then .CheckUnmodeled
        else if fs_under (m_fs m) c then .CheckUnmodeled
        else
          match fs_lookup (m_fs m) c with
          | none => check_ret_only eff (errno_ret ENOENT) m []
          | some _ => check_unlink_found p c flags eff m

/-- The pathname copy-in, as [Fs.Open.check_openat] checks it: decide the
    body against the effect with the ledger cleared, then require the
    claimed ledger to be exactly that one range.  The flag arm is outside
    the wrapper because the kernel decides it before [getname()], so an
    honest -EINVAL there carries no copy-in at all. -/
def check_unlinkat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(modeled_unlink_flags flags)
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff
      (check_unlinkat_body i dirfd pathp flags (clear_copyins eff) m)

/- =========================================================================
   unlink_found: the shared tail
   ========================================================================= -/

private theorem check_unlink_found_sound_ok (i : SyscallInput) (p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlink_found p c flags eff m = .CheckOk m' evs) :
    unlink_found_spec p c flags m i m (.ok eff m' evs) := by
  unfold check_unlink_found at H
  unfold unlink_found_spec
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret ENOTDIR) m [] m' evs).mp H
    exact pure_ok (mkEffect (errno_ret ENOTDIR) [] []) i _
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret ENOTDIR) m [] m' evs).mp H
      exact pure_ok (mkEffect (errno_ret ENOTDIR) [] []) i _
    · rw [ite_eq_right hts] at H ⊢
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hfd] at H ⊢
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          simp only [check_unlink_result] at H
        case nil.nil.nil.nil.nil =>
          by_cases he : errno_ret_in unlinkat_errnos ret = true
          · rw [ite_eq_left he] at H
            cases H
            obtain ⟨e, hmem, hret⟩ := (errno_ret_in_true unlinkat_errnos ret).mp he
            subst hret
            refine alt_l _ _ i m (.ok (mkEffect (errno_ret e) [] []) m []) ?_
            refine bind_ok0 (errno_from unlinkat_errnos) (fun e' => err_ret e')
              i m e m _ m [] ?_ ?_
            · exact choose_ok (fun x => x ∈ unlinkat_errnos) e i m hmem
            · exact pure_ok (mkEffect (errno_ret e) [] []) i m
          · rw [ite_eq_right he] at H
            by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
            · rw [ite_eq_left hz] at H
              cases H
              have hret : ret = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq ret _).mp hz
              subst hret
              refine alt_r _ _ i m
                (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
                  (with_fs (fs_remove (m_fs m) c) m) []) ?_
              refine bind_ok0 (set_fs (fs_remove (m_fs m) c))
                (fun _ => ret_only (BitVec.ofInt 64 0))
                i m () (with_fs (fs_remove (m_fs m) c) m) _ _ [] ?_ ?_
              · exact modify_ok (with_fs (fs_remove (m_fs m) c)) i m
              · exact pure_ok (mkEffect (BitVec.ofInt 64 0) [] []) i _
            · rw [ite_eq_right hz] at H
              exact nomatch H
        all_goals exact nomatch H

/- -------------------------------------------------------------------------
   The `*_frame` lemmas — PUBLIC on purpose

   [Checks/VmMapsDisjoint.lean] must show that each checker leaves
   [m_vmmaps] alone.  Its `vm_frame` loop does that by unfolding the
   checker and casing the result hypothesis, and it cannot: the three
   helpers in this file are `private def`, so their equation lemmas are
   not nameable from another module and the accepting branch never
   reduces far enough to be seen through.

   The fact the frame needs is therefore stated HERE, where the helper's
   body is visible, and stated as a `theorem` rather than a `private`
   one: `private` would put the fact out of reach for exactly the same
   reason the equation lemmas already are.  Stating a public fact ABOUT a
   private definition leaks nothing — the helper's name stays unexported;
   only "this checker leaves [m_vmmaps] alone" travels.

   Each proof is the checker side of the `*_sound_ok` immediately above,
   with the spec dropped: every accepting branch is either a
   [check_ret_only] (which hands back the model it was given) or one of
   [check_unlink_result]'s two success shapes (an injected errno, or the
   removal's [with_fs], which does not touch `m_vm`).
   ------------------------------------------------------------------------- -/

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the shared tail only ever
    answers a [check_ret_only] over [m] or a [check_unlink_result] over it
    (an injected errno, or the removal's [with_fs]), so it leaves [m_vmmaps]
    alone.  Public because the helper it is about is `private`. -/
theorem check_unlink_found_frame (p c : Fs.path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlink_found p c flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_unlink_found at H
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H
    exact check_ret_only_frame eff (errno_ret ENOTDIR) m m' evs H
  · rw [ite_eq_right hrm] at H
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H
      exact check_ret_only_frame eff (errno_ret ENOTDIR) m m' evs H
    · rw [ite_eq_right hts] at H
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H
        exact nomatch H
      · rw [ite_eq_right hfd] at H
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          simp only [check_unlink_result] at H
        case nil.nil.nil.nil.nil =>
          by_cases he : errno_ret_in unlinkat_errnos ret = true
          · rw [ite_eq_left he] at H
            cases H
            rfl
          · rw [ite_eq_right he] at H
            by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
            · rw [ite_eq_left hz] at H
              cases H
              rfl
            · rw [ite_eq_right hz] at H
              exact nomatch H
        all_goals exact nomatch H

private theorem check_unlink_found_sound_unmodeled (i : SyscallInput) (p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_unlink_found p c flags eff m = .CheckUnmodeled) :
    unlink_found_spec p c flags m i m .unmodeled := by
  unfold check_unlink_found at H
  unfold unlink_found_spec
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m [])
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m [])
    · rw [ite_eq_right hts] at H ⊢
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hfd] at H ⊢
        exfalso
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          simp only [check_unlink_result] at H
        case nil.nil.nil.nil.nil =>
          by_cases he : errno_ret_in unlinkat_errnos ret = true
          · rw [ite_eq_left he] at H
            exact nomatch H
          · rw [ite_eq_right he] at H
            by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
            · rw [ite_eq_left hz] at H
              exact nomatch H
            · rw [ite_eq_right hz] at H
              exact nomatch H
        all_goals exact nomatch H

private theorem check_unlink_found_ok_copyins_nil (p c : Fs.path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlink_found p c flags eff m = .CheckOk m' evs) :
    eff.eff_copyins = [] := by
  unfold check_unlink_found at H
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H
    obtain ⟨rfl, _, _⟩ :=
      (check_ret_only_ok_iff eff (errno_ret ENOTDIR) m [] m' evs).mp H
    rfl
  · rw [ite_eq_right hrm] at H
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H
      obtain ⟨rfl, _, _⟩ :=
        (check_ret_only_ok_iff eff (errno_ret ENOTDIR) m [] m' evs).mp H
      rfl
    · rw [ite_eq_right hts] at H
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H
        exact nomatch H
      · rw [ite_eq_right hfd] at H
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
          simp only [check_unlink_result] at H
        case nil.nil.nil.nil.nil =>
          split at H
          · rfl
          · split at H
            · rfl
            · exact nomatch H
        all_goals exact nomatch H

/- =========================================================================
   unlinkat_tmp: the /tmp arm
   ========================================================================= -/

private theorem check_unlinkat_tmp_sound_ok (i : SyscallInput) (n p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlinkat_tmp n p c flags eff m = .CheckOk m' evs) :
    unlinkat_tmp_spec n p c flags m i m (.ok eff m' evs) := by
  unfold check_unlinkat_tmp at H
  unfold unlinkat_tmp_spec
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    exact nomatch H
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H ⊢
      exact nomatch H
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
        exact pure_ok (mkEffect (errno_ret EISDIR) [] []) i _
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) c = lk at H ⊢
        cases lk with
        | none =>
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
          exact pure_ok (mkEffect (errno_ret ENOENT) [] []) i _
        | some data => exact check_unlink_found_sound_ok i p c flags eff m m' evs H

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the /tmp arm only ever
    answers a [check_ret_only] over [m] or a [check_unlink_found] over it, so
    it leaves [m_vmmaps] alone.  Public because the helper it is about is
    `private`.  Unlike its [check_unlinkat_tmp_sound_ok] neighbour it takes
    no [SyscallInput]: the checker's body never reads one (only the spec
    does), so the fact does not need one either. -/
theorem check_unlinkat_tmp_frame (n p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlinkat_tmp n p c flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_unlinkat_tmp at H
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H
    exact nomatch H
  · rw [ite_eq_right hrm] at H
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H
      exact nomatch H
    · rw [ite_eq_right hnm] at H
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H
        exact check_ret_only_frame eff (errno_ret EISDIR) m m' evs H
      · rw [ite_eq_right hun] at H
        generalize hfs : fs_lookup (m_fs m) c = lk at H
        cases lk with
        | none => exact check_ret_only_frame eff (errno_ret ENOENT) m m' evs H
        | some data => exact check_unlink_found_frame p c flags eff m m' evs H

private theorem check_unlinkat_tmp_sound_unmodeled (i : SyscallInput) (n p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_unlinkat_tmp n p c flags eff m = .CheckUnmodeled) :
    unlinkat_tmp_spec n p c flags m i m .unmodeled := by
  unfold check_unlinkat_tmp at H
  unfold unlinkat_tmp_spec
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    exact unmodeled_intro i m
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) c = lk at H ⊢
        cases lk with
        | none =>
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
        | some data => exact check_unlink_found_sound_unmodeled i p c flags eff m H

private theorem check_unlinkat_tmp_ok_copyins_nil (n p c : Fs.path) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlinkat_tmp n p c flags eff m = .CheckOk m' evs) :
    eff.eff_copyins = [] := by
  unfold check_unlinkat_tmp at H
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H
    exact nomatch H
  · rw [ite_eq_right hrm] at H
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H
      exact nomatch H
    · rw [ite_eq_right hnm] at H
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H
        obtain ⟨rfl, _, _⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
        rfl
      · rw [ite_eq_right hun] at H
        generalize hfs : fs_lookup (m_fs m) c = lk at H
        cases lk with
        | none =>
          obtain ⟨rfl, _, _⟩ :=
            (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
          rfl
        | some data => exact check_unlink_found_ok_copyins_nil p c flags eff m m' evs H

/- =========================================================================
   The body
   ========================================================================= -/

private theorem check_unlinkat_body_sound_ok (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_unlinkat_body i dirfd pathp flags eff m = .CheckOk m' evs) :
    unlinkat_body_spec dirfd pathp flags i m i m (.ok eff m' evs) := by
  unfold check_unlinkat_body at H
  unfold unlinkat_body_spec
  dsimp only at H ⊢
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    dsimp only at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret ENAMETOOLONG) m [] m' evs).mp H
    exact pure_ok (mkEffect (errno_ret ENAMETOOLONG) [] []) i _
  | CstrFault =>
    dsimp only at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
    exact pure_ok (mkEffect (errno_ret EFAULT) [] []) i _
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
      exact pure_ok (mkEffect (errno_ret ENOENT) [] []) i _
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H ⊢
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H ⊢
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EBUSY) m [] m' evs).mp H
            exact pure_ok (mkEffect (errno_ret EBUSY) [] []) i _
          · rw [ite_eq_right hrm] at H ⊢
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
            exact pure_ok (mkEffect (errno_ret EISDIR) [] []) i _
        · rw [ite_eq_right hroot] at H ⊢
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H ⊢
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H ⊢
            cases tn with
            | none => exact nomatch H
            | some n =>
              exact check_unlinkat_tmp_sound_ok i n p
                (path_strip_trailing_slashes p) flags eff m m' evs H
          · rw [ite_eq_right hsl] at H ⊢
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H ⊢
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H ⊢
                obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                exact pure_ok (mkEffect (errno_ret EINVAL) [] []) i _
              · rw [ite_eq_right hrm] at H ⊢
                obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
                exact pure_ok (mkEffect (errno_ret EISDIR) [] []) i _
            · rw [ite_eq_right hdot] at H ⊢
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H ⊢
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H ⊢
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret ENOTEMPTY) m [] m' evs).mp H
                  exact pure_ok (mkEffect (errno_ret ENOTEMPTY) [] []) i _
                · rw [ite_eq_right hrm] at H ⊢
                  obtain ⟨rfl, rfl, rfl⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
                  exact pure_ok (mkEffect (errno_ret EISDIR) [] []) i _
              · rw [ite_eq_right hdd] at H ⊢
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · rw [ite_eq_left hnm] at H ⊢
                  exact nomatch H
                · rw [ite_eq_right hnm] at H ⊢
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H ⊢
                    exact nomatch H
                  · rw [ite_eq_right hun] at H ⊢
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H ⊢
                    cases lk with
                    | none =>
                      obtain ⟨rfl, rfl, rfl⟩ :=
                        (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
                      exact pure_ok (mkEffect (errno_ret ENOENT) [] []) i _
                    | some data =>
                      exact check_unlink_found_sound_ok i p
                        (path_strip_trailing_slashes p) flags eff m m' evs H

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the unlinkat body is one
    pathname read plus the /tmp and shared-tail arms behind it, so it leaves
    [m_vmmaps] alone.  Public because the helper it is about is `private`;
    the walk is the checker side of [check_unlinkat_body_sound_ok], with the
    spec dropped. -/
theorem check_unlinkat_body_frame (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_unlinkat_body i dirfd pathp flags eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_unlinkat_body at H
  dsimp only at H
  generalize hc : read_cstr i.in_mem pathp = cr at H
  cases cr with
  | CstrTooLong =>
    dsimp only at H
    exact check_ret_only_frame eff (errno_ret ENAMETOOLONG) m m' evs H
  | CstrFault =>
    dsimp only at H
    exact check_ret_only_frame eff (errno_ret EFAULT) m m' evs H
  | CstrOk p =>
    dsimp only at H
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      exact check_ret_only_frame eff (errno_ret ENOENT) m m' evs H
    · rw [ite_eq_right hpe] at H
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H
            exact check_ret_only_frame eff (errno_ret EBUSY) m m' evs H
          · rw [ite_eq_right hrm] at H
            exact check_ret_only_frame eff (errno_ret EISDIR) m m' evs H
        · rw [ite_eq_right hroot] at H
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H
            cases tn with
            | none => exact nomatch H
            | some n =>
              exact check_unlinkat_tmp_frame n p
                (path_strip_trailing_slashes p) flags eff m m' evs H
          · rw [ite_eq_right hsl] at H
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H
                exact check_ret_only_frame eff (errno_ret EINVAL) m m' evs H
              · rw [ite_eq_right hrm] at H
                exact check_ret_only_frame eff (errno_ret EISDIR) m m' evs H
            · rw [ite_eq_right hdot] at H
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H
                  exact check_ret_only_frame eff (errno_ret ENOTEMPTY) m m' evs H
                · rw [ite_eq_right hrm] at H
                  exact check_ret_only_frame eff (errno_ret EISDIR) m m' evs H
              · rw [ite_eq_right hdd] at H
                by_cases hnm :
                    decide (NAME_MAX < (path_strip_trailing_slashes p).length) = true
                · rw [ite_eq_left hnm] at H
                  exact nomatch H
                · rw [ite_eq_right hnm] at H
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H
                    exact nomatch H
                  · rw [ite_eq_right hun] at H
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H
                    cases lk with
                    | none =>
                      exact check_ret_only_frame eff (errno_ret ENOENT) m m' evs H
                    | some data =>
                      exact check_unlink_found_frame p
                        (path_strip_trailing_slashes p) flags eff m m' evs H

private theorem check_unlinkat_body_sound_unmodeled (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_unlinkat_body i dirfd pathp flags eff m = .CheckUnmodeled) :
    unlinkat_body_spec dirfd pathp flags i m i m .unmodeled := by
  unfold check_unlinkat_body at H
  unfold unlinkat_body_spec
  dsimp only at H ⊢
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENAMETOOLONG) m [])
  | CstrFault =>
    dsimp only at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hd] at H ⊢
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H ⊢
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H ⊢
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBUSY) m [])
          · rw [ite_eq_right hrm] at H ⊢
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
        · rw [ite_eq_right hroot] at H ⊢
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H ⊢
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H ⊢
            cases tn with
            | none => exact unmodeled_intro i m
            | some n =>
              exact check_unlinkat_tmp_sound_unmodeled i n p
                (path_strip_trailing_slashes p) flags eff m H
          · rw [ite_eq_right hsl] at H ⊢
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H ⊢
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H ⊢
                exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
              · rw [ite_eq_right hrm] at H ⊢
                exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
            · rw [ite_eq_right hdot] at H ⊢
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H ⊢
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H ⊢
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (errno_ret ENOTEMPTY) m [])
                · rw [ite_eq_right hrm] at H ⊢
                  exact absurd H
                    (check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [])
              · rw [ite_eq_right hdd] at H ⊢
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · rw [ite_eq_left hnm] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hnm] at H ⊢
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H ⊢
                    exact unmodeled_intro i m
                  · rw [ite_eq_right hun] at H ⊢
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H ⊢
                    cases lk with
                    | none =>
                      exact absurd H
                        (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
                    | some data =>
                      exact check_unlink_found_sound_unmodeled i p
                        (path_strip_trailing_slashes p) flags eff m H

/- =========================================================================
   0 is not an injectable errno
   ========================================================================= -/

/-- 0 is not an injectable errno, so the removal and the failure
    alternative never both accept the same return. -/
theorem errno_ret_in_unlinkat_zero :
    errno_ret_in unlinkat_errnos (BitVec.ofInt 64 0) = false := by
  apply errno_ret_in_fd
  · decide
  · decide

private theorem check_unlink_found_complete_ok (i : SyscallInput) (p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : unlink_found_spec p c flags m i m (.ok eff m' evs)) :
    check_unlink_found p c flags eff m = .CheckOk m' evs := by
  unfold unlink_found_spec at H
  unfold check_unlink_found
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hts] at H ⊢
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H ⊢
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hfd] at H ⊢
        rcases H with H1 | H2
        · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
          obtain ⟨er0, hin, heq⟩ := hc
          simp only [Outcome.ok.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          cases her
          simp only [List.nil_append] at hevs
          subst hevs
          simp only [check_unlink_result]
          rw [ite_eq_left (errno_ret_in_intro unlinkat_errnos _ hin)]
        · obtain ⟨u, m1, evs1, evs2, hset, hret, hevs⟩ := H2
          unfold set_fs modifySpec LinuxSem.LinuxProcessSem.modify at hset
          cases hset
          cases hret
          simp only [List.nil_append] at hevs
          subst hevs
          simp only [check_unlink_result]
          rw [errno_ret_in_unlinkat_zero]
          rw [ite_eq_right (by simp)]
          rw [bv_eqb_refl]
          rw [ite_eq_left rfl]

private theorem check_unlink_found_complete_unmodeled (i : SyscallInput) (p c : Fs.path)
    (flags : word) (m : Model) (eff : SyscallEffect)
    (H : unlink_found_spec p c flags m i m .unmodeled) :
    check_unlink_found p c flags eff m = .CheckUnmodeled := by
  unfold unlink_found_spec at H
  unfold check_unlink_found
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hts : path_trailing_slash p = true
    · rw [ite_eq_left hts] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right hts] at H ⊢
      by_cases hfd : fd_names_path (m_fds m) c = true
      · rw [ite_eq_left hfd] at H ⊢
      · rw [ite_eq_right hfd] at H ⊢
        rcases H with H1 | H2
        · rcases H1 with hdecl | ⟨er, m1, evs1, hc, her⟩
          · obtain ⟨er, hin, heq⟩ := hdecl
            exact nomatch heq
          · exact nomatch her
        · rcases H2 with hdecl | ⟨u, m1, evs1, hset, hret⟩
          · unfold set_fs modifySpec LinuxSem.LinuxProcessSem.modify at hdecl
            exact nomatch hdecl
          · exact nomatch hret

private theorem check_unlinkat_tmp_complete_ok (i : SyscallInput) (n p c : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : unlinkat_tmp_spec n p c flags m i m (.ok eff m' evs)) :
    check_unlinkat_tmp n p c flags eff m = .CheckOk m' evs := by
  unfold unlinkat_tmp_spec at H
  unfold check_unlinkat_tmp
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H ⊢
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H ⊢
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) c = lk at H ⊢
        cases lk with
        | none =>
          dsimp only at H ⊢
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          simp [check_ret_only, bv_eqb_refl]
        | some data =>
          exact check_unlink_found_complete_ok i p c flags eff m m' evs H

private theorem check_unlinkat_tmp_complete_unmodeled (i : SyscallInput) (n p c : Fs.path)
    (flags : word) (m : Model) (eff : SyscallEffect)
    (H : unlinkat_tmp_spec n p c flags m i m .unmodeled) :
    check_unlinkat_tmp n p c flags eff m = .CheckUnmodeled := by
  unfold unlinkat_tmp_spec at H
  unfold check_unlinkat_tmp
  by_cases hrm : unlink_rmdir flags = true
  · rw [ite_eq_left hrm] at H ⊢
  · rw [ite_eq_right hrm] at H ⊢
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · rw [ite_eq_left hnm] at H ⊢
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) c = true
      · rw [ite_eq_left hun] at H ⊢
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) c = lk at H ⊢
        cases lk with
        | none =>
          dsimp only at H ⊢
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        | some data =>
          exact check_unlink_found_complete_unmodeled i p c flags m eff H

private theorem check_unlinkat_body_complete_ok (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : unlinkat_body_spec dirfd pathp flags i m i m (.ok eff m' evs)) :
    check_unlinkat_body i dirfd pathp flags eff m = .CheckOk m' evs := by
  unfold unlinkat_body_spec at H
  unfold check_unlinkat_body
  dsimp only at H ⊢
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    dsimp only at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  | CstrFault =>
    dsimp only at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H ⊢
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H ⊢
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            simp [check_ret_only, bv_eqb_refl]
          · rw [ite_eq_right hrm] at H ⊢
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at H
            obtain ⟨rfl, rfl, rfl⟩ := H
            simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hroot] at H ⊢
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H ⊢
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H ⊢
            cases tn with
            | none =>
              simp only [unmodeled] at H
              exact nomatch H
            | some n =>
              exact check_unlinkat_tmp_complete_ok i n p
                (path_strip_trailing_slashes p) flags eff m m' evs H
          · rw [ite_eq_right hsl] at H ⊢
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H ⊢
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H ⊢
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at H
                obtain ⟨rfl, rfl, rfl⟩ := H
                simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right hrm] at H ⊢
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
                  Outcome.ok.injEq] at H
                obtain ⟨rfl, rfl, rfl⟩ := H
                simp [check_ret_only, bv_eqb_refl]
            · rw [ite_eq_right hdot] at H ⊢
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H ⊢
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H ⊢
                  simp only [err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  simp [check_ret_only, bv_eqb_refl]
                · rw [ite_eq_right hrm] at H ⊢
                  simp only [err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                  obtain ⟨rfl, rfl, rfl⟩ := H
                  simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right hdd] at H ⊢
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · rw [ite_eq_left hnm] at H ⊢
                  simp only [unmodeled] at H
                  exact nomatch H
                · rw [ite_eq_right hnm] at H ⊢
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H ⊢
                    simp only [unmodeled] at H
                    exact nomatch H
                  · rw [ite_eq_right hun] at H ⊢
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H ⊢
                    cases lk with
                    | none =>
                      simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
                      obtain ⟨rfl, rfl, rfl⟩ := H
                      simp [check_ret_only, bv_eqb_refl]
                    | some data =>
                      exact check_unlink_found_complete_ok i p
                        (path_strip_trailing_slashes p) flags eff m m' evs H

private theorem check_unlinkat_body_complete_unmodeled (i : SyscallInput)
    (dirfd pathp flags : word) (m : Model) (eff : SyscallEffect)
    (H : unlinkat_body_spec dirfd pathp flags i m i m .unmodeled) :
    check_unlinkat_body i dirfd pathp flags eff m = .CheckUnmodeled := by
  unfold unlinkat_body_spec at H
  unfold check_unlinkat_body
  dsimp only at H ⊢
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    dsimp only at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | CstrFault =>
    dsimp only at H ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
      · rw [ite_eq_right hd] at H ⊢
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H ⊢
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H ⊢
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
          · rw [ite_eq_right hrm] at H ⊢
            simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
            exact nomatch H
        · rw [ite_eq_right hroot] at H ⊢
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H ⊢
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H ⊢
            cases tn with
            | none =>
              dsimp only at H ⊢
            | some n =>
              exact check_unlinkat_tmp_complete_unmodeled i n p
                (path_strip_trailing_slashes p) flags m eff H
          · rw [ite_eq_right hsl] at H ⊢
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H ⊢
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H ⊢
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
                exact nomatch H
              · rw [ite_eq_right hrm] at H ⊢
                simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
                exact nomatch H
            · rw [ite_eq_right hdot] at H ⊢
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H ⊢
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H ⊢
                  simp only [err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure] at H
                  exact nomatch H
                · rw [ite_eq_right hrm] at H ⊢
                  simp only [err_ret, ret_only,
                    LinuxSem.LinuxProcessSem.pure] at H
                  exact nomatch H
              · rw [ite_eq_right hdd] at H ⊢
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · rw [ite_eq_left hnm] at H ⊢
                · rw [ite_eq_right hnm] at H ⊢
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H ⊢
                  · rw [ite_eq_right hun] at H ⊢
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H ⊢
                    cases lk with
                    | none =>
                      dsimp only at H ⊢
                      simp only [err_ret, ret_only,
                        LinuxSem.LinuxProcessSem.pure] at H
                      exact nomatch H
                    | some data =>
                      exact check_unlink_found_complete_unmodeled i p
                        (path_strip_trailing_slashes p) flags m eff H

/- =========================================================================
   No arm of the body claims a copy-in of its own
   ========================================================================= -/

/-- No arm of the body claims a copy-in of its own: each returns either
    through [check_ret_only], which forces every ledger empty, or through
    [check_unlink_result], which matches six empty lists.  That is what
    lets the wrapper below equate the WHOLE claimed ledger with the one
    pathname range rather than with a prefix of it. -/
private theorem check_unlinkat_body_ok_copyins_nil (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_unlinkat_body i dirfd pathp flags eff m = .CheckOk m' evs) :
    eff.eff_copyins = [] := by
  unfold check_unlinkat_body at H
  dsimp only at H
  generalize hc : read_cstr i.in_mem pathp = cr at H
  cases cr with
  | CstrTooLong =>
    dsimp only at H
    obtain ⟨rfl, _, _⟩ :=
      (check_ret_only_ok_iff eff (errno_ret ENAMETOOLONG) m [] m' evs).mp H
    rfl
  | CstrFault =>
    dsimp only at H
    obtain ⟨rfl, _, _⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
    rfl
  | CstrOk p =>
    dsimp only at H
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      obtain ⟨rfl, _, _⟩ :=
        (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
      rfl
    · rw [ite_eq_right hpe] at H
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · rw [ite_eq_left hroot] at H
          by_cases hrm : unlink_rmdir flags = true
          · rw [ite_eq_left hrm] at H
            obtain ⟨rfl, _, _⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EBUSY) m [] m' evs).mp H
            rfl
          · rw [ite_eq_right hrm] at H
            obtain ⟨rfl, _, _⟩ :=
              (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
            rfl
        · rw [ite_eq_right hroot] at H
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · rw [ite_eq_left hsl] at H
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn at H
            cases tn with
            | none => exact nomatch H
            | some n =>
              exact check_unlinkat_tmp_ok_copyins_nil n p
                (path_strip_trailing_slashes p) flags eff m m' evs H
          · rw [ite_eq_right hsl] at H
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · rw [ite_eq_left hdot] at H
              by_cases hrm : unlink_rmdir flags = true
              · rw [ite_eq_left hrm] at H
                obtain ⟨rfl, _, _⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
                rfl
              · rw [ite_eq_right hrm] at H
                obtain ⟨rfl, _, _⟩ :=
                  (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
                rfl
            · rw [ite_eq_right hdot] at H
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · rw [ite_eq_left hdd] at H
                by_cases hrm : unlink_rmdir flags = true
                · rw [ite_eq_left hrm] at H
                  obtain ⟨rfl, _, _⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret ENOTEMPTY) m [] m' evs).mp H
                  rfl
                · rw [ite_eq_right hrm] at H
                  obtain ⟨rfl, _, _⟩ :=
                    (check_ret_only_ok_iff eff (errno_ret EISDIR) m [] m' evs).mp H
                  rfl
              · rw [ite_eq_right hdd] at H
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · rw [ite_eq_left hnm] at H
                  exact nomatch H
                · rw [ite_eq_right hnm] at H
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · rw [ite_eq_left hun] at H
                    exact nomatch H
                  · rw [ite_eq_right hun] at H
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk at H
                    cases lk with
                    | none =>
                      dsimp only at H
                      obtain ⟨rfl, _, _⟩ :=
                        (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
                      rfl
                    | some data =>
                      exact check_unlink_found_ok_copyins_nil p
                        (path_strip_trailing_slashes p) flags eff m m' evs H

/- ------------------------------------------------------- the four exports

   Each is the body lemma above with the flag arm in front and the
   pathname copy-in threaded, exactly as [Fs.Open]'s four are.  The flag
   arm carries no copy-in: the kernel decides it before [getname()]. -/

theorem check_unlinkat_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_unlinkat i dirfd pathp flags eff m = .CheckOk m' evs) :
    unlinkat_spec dirfd pathp flags i m (.ok eff m' evs) := by
  unfold check_unlinkat at H
  unfold unlinkat_spec
  dsimp only at H ⊢
  refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
  refine bind_ok0 getModelSpec _ i m m m _ m' evs (getModel_ok i m) ?_
  by_cases hfl : (!(modeled_unlink_flags flags)) = true
  · rw [ite_eq_left hfl] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact pure_ok (mkEffect (errno_ret EINVAL) [] []) i _
  · rw [ite_eq_right hfl] at H ⊢
    obtain ⟨hreads, Hbody⟩ := (check_copyins_after_ok_iff _ eff _ m' evs).mp H
    exact record_copyins_clear_ok _ _ i m eff m' evs hreads
      (check_unlinkat_body_sound_ok i dirfd pathp flags (clear_copyins eff) m m' evs Hbody)

theorem check_unlinkat_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_unlinkat i dirfd pathp flags eff m = .CheckUnmodeled) :
    unlinkat_spec dirfd pathp flags i m .unmodeled := by
  unfold check_unlinkat at H
  unfold unlinkat_spec
  dsimp only at H ⊢
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  by_cases hfl : (!(modeled_unlink_flags flags)) = true
  · rw [ite_eq_left hfl] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hfl] at H ⊢
    exact record_copyins_unmodeled
      (check_unlinkat_body_sound_unmodeled i dirfd pathp flags (clear_copyins eff) m
        (check_copyins_after_unmodeled _ eff _ H))

theorem check_unlinkat_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : unlinkat_spec dirfd pathp flags i m (.ok eff m' evs)) :
    check_unlinkat i dirfd pathp flags eff m = .CheckOk m' evs := by
  unfold unlinkat_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      if !(modeled_unlink_flags flags) then err_ret EINVAL
      else record_copyins [(pathp, cstr_access_len_aux i0.in_mem pathp path_max)]
        (unlinkat_body_spec dirfd pathp flags i0 m0)) i m (.ok eff m' evs) H
  unfold check_unlinkat
  dsimp only
  by_cases hfl : (!(modeled_unlink_flags flags)) = true
  · rw [ite_eq_left hfl] at H' ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H'
    obtain ⟨rfl, rfl, rfl⟩ := H'
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hfl] at H' ⊢
    obtain ⟨core, Hcore, heff⟩ := record_copyins_ok_inv _ _ i m eff m' evs H'
    obtain ⟨cr, cw, cz, cu, cc, ck⟩ := core
    have hchk : check_unlinkat_body i dirfd pathp flags
        ⟨cr, cw, cz, cu, cc, ck⟩ m = .CheckOk m' evs :=
      check_unlinkat_body_complete_ok i dirfd pathp flags
        ⟨cr, cw, cz, cu, cc, ck⟩ m m' evs Hcore
    have hnil : ck = [] :=
      check_unlinkat_body_ok_copyins_nil i dirfd pathp flags
        ⟨cr, cw, cz, cu, cc, ck⟩ m m' evs hchk
    subst hnil
    subst heff
    rw [List.append_nil]
    rw [check_copyins_after_ok_iff]
    exact ⟨rfl, hchk⟩

theorem check_unlinkat_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : unlinkat_spec dirfd pathp flags i m .unmodeled) :
    check_unlinkat i dirfd pathp flags eff m = .CheckUnmodeled := by
  unfold unlinkat_spec at H
  simp only [inputSpec, getModelSpec] at H
  have H' := bind_input_model_inv
    (fun i0 (m0 : Model) =>
      if !(modeled_unlink_flags flags) then err_ret EINVAL
      else record_copyins [(pathp, cstr_access_len_aux i0.in_mem pathp path_max)]
        (unlinkat_body_spec dirfd pathp flags i0 m0)) i m .unmodeled H
  unfold check_unlinkat
  dsimp only
  by_cases hfl : (!(modeled_unlink_flags flags)) = true
  · rw [ite_eq_left hfl] at H' ⊢
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H'
    exact nomatch H'
  · rw [ite_eq_right hfl] at H' ⊢
    rw [check_unlinkat_body_complete_unmodeled i dirfd pathp flags m (clear_copyins eff)
      (record_copyins_unmodeled_inv _ _ i m H')]
    rfl

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs leave no `vm_compute` goal — it is the five
   checkers, their prose, and the eighteen proofs.  The checks below are
   sanity checks: each pins one branch the proofs above walk, by unfolding
   the checker and discharging the tests it turns on with `decide` or by
   the same lemma the proof uses.  `check_result` carries a `Model`, and
   `Model` has no `DecidableEq`, so every claim is an EQUATION on the
   checker's answer rather than a `by decide` goal. -/

/-- An illegal flag word is -EINVAL and claims NO copy-in — the kernel
    answers before `getname()` is evaluated, which is why the flag test
    sits outside [check_copyins_after]. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_unlinkat i AT_FDCWD32 0 1 eff m = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_unlinkat]
  rw [ite_eq_left (by decide : (!(modeled_unlink_flags (1 : word))) = true)]

/-- A pathname whose first byte is unmapped is -EFAULT: `read_cstr`'s
    fault arm, tested without any file system. -/
example (eff : SyscallEffect) (m : Model) :
    check_unlinkat_body ⟨0, [], fun _ => none, fun _ => none⟩ AT_FDCWD32 0 0 eff m
      = check_ret_only eff (errno_ret EFAULT) m [] := rfl

/-- An injectable errno is accepted by the removal's failure half, leaving
    the model alone. -/
example (p : Fs.path) (m : Model) :
    check_unlink_result p (mkEffect (errno_ret ENOMEM) [] []) m = .CheckOk m [] := by
  simp only [check_unlink_result]
  rw [ite_eq_left (errno_ret_in_intro unlinkat_errnos ENOMEM (by decide))]

/-- 0 is the removal itself: the accepted model is the file system with the
    key dropped. -/
example (p : Fs.path) (m : Model) :
    check_unlink_result p (mkEffect (BitVec.ofInt 64 0) [] []) m
      = .CheckOk (with_fs (fs_remove (m_fs m) p) m) [] := by
  simp only [check_unlink_result]
  rw [errno_ret_in_unlinkat_zero]
  rw [ite_eq_right (by simp)]
  rw [bv_eqb_refl]
  rw [ite_eq_left rfl]

/-- A forged ledger reaches neither half: the acceptor matches five empty
    lists and rejects anything else. -/
example (p : Fs.path) (m : Model) :
    check_unlink_result p ⟨0, [], [], [], [], [(0, 1)]⟩ m = .CheckReject := by
  simp only [check_unlink_result]

/-- Any return other than 0 and the injectable errnos is rejected. -/
example (p : Fs.path) (m : Model) :
    check_unlink_result p (mkEffect 7 [] []) m = .CheckReject := by
  simp only [check_unlink_result]
  rw [ite_eq_right (by decide : ¬(errno_ret_in unlinkat_errnos (7 : word) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (7 : word) (BitVec.ofInt 64 0) = true))]

/-- AT_REMOVEDIR of a model file is -ENOTDIR — `unlink_found`'s first arm,
    reached before either the trailing-separator test or the open-fd
    guard. -/
example (p c : Fs.path) (eff : SyscallEffect) (m : Model) :
    check_unlink_found p c (BitVec.ofInt 64 AT_REMOVEDIR) eff m
      = check_ret_only eff (errno_ret ENOTDIR) m [] := by
  simp only [check_unlink_found]
  rw [ite_eq_left (by decide : unlink_rmdir (BitVec.ofInt 64 AT_REMOVEDIR) = true)]

/-- The /tmp arm declines AT_REMOVEDIR rather than answering it: which of
    -ENOTEMPTY and 0 the kernel gives depends on /tmp holding a
    DIRECTORY, which the flat map cannot express. -/
example (n p c : Fs.path) (eff : SyscallEffect) (m : Model) :
    check_unlinkat_tmp n p c (BitVec.ofInt 64 AT_REMOVEDIR) eff m = .CheckUnmodeled := by
  simp only [check_unlinkat_tmp]
  rw [ite_eq_left (by decide : unlink_rmdir (BitVec.ofInt 64 AT_REMOVEDIR) = true)]

/-- An open fd that names the key is `CheckUnmodeled`, not an answered
    removal: the model records the path, not an inode.  The two tests in
    front of it are taken as hypotheses so the check does not have to
    decide them. -/
example (p c : Fs.path) (eff : SyscallEffect) (m : Model)
    (hrm : unlink_rmdir (0 : word) = false)
    (hts : path_trailing_slash p = false)
    (h : fd_names_path (m_fds m) c = true) :
    check_unlink_found p c 0 eff m = .CheckUnmodeled := by
  have h1 : ¬(unlink_rmdir (0 : word) = true) := by rw [hrm]; decide
  have h2 : ¬(path_trailing_slash p = true) := by rw [hts]; decide
  simp only [check_unlink_found]
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h]

end LinuxSem.Checks.Sys.Fs.Namei

