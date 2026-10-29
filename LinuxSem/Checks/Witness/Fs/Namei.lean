/-
  * LinuxProcessSem.Checks.Witness.Fs.Namei — the unlinkat (35) witness, and its proof

  Answers to Linux [fs/namei.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  `Checks.Witness.Prelude` re-exports the model/state/monad stack, and the
  witness's own spec — `Sys/Fs/Namei.lean`, where `unlink_found_spec`,
  `unlinkat_tmp_spec`, `unlinkat_body_spec` and `unlinkat_spec` live — is
  imported directly.

  A file-private definition is `private` in Lean: the three local witnesses
  below are file-private, and [unlinkat_witness] is the one export.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` and `outcome_copyins` come from
  `Checks.Witness.Prelude` and `Sys.Syscall`, and `ret_outcome r m` is the
  "return `r`, change nothing, emit nothing" outcome.

  Both sides read the same guards in the same order, and the witness is the
  SECOND argument of the goal while the spec is the head of it, so one
  `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]` rewrites BOTH at once.
  (`rw` is not enough here: it rewrites one occurrence, leaving the
  witness's copy of the guard behind.)  `cbv zeta` is `dsimp only`, and the
  two matches (`read_cstr`, `fs_lookup`) are peeled with `generalize … +
  cases`, so both copies reduce together.

  [unlinkat_witness_ok] opens with the two steps every arm of
  [Fs.Namei.unlinkat_spec] begins with — the input and the model — spelled
  `bind_step … (input_ok i m)` and `bind_step … (getModel_ok i m)`.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Namei

namespace LinuxSem.Checks.Witness.Fs.Namei

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Namei
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   The witnesses
   ========================================================================= -/

/-- Mirrors [Fs.Namei.unlink_found_spec]: the removal is witnessed by
    the [alt]'s LEFT branch, so the witness never builds the removed
    file system.  The deterministic errno arms and the fail-closed
    [Unmodeled] are the spec's own; only the removal could succeed, and
    there the witness takes the injectable environment failure, which
    needs no model state. -/
private def unlink_found_witness (p c : Fs.path) (flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if unlink_rmdir flags then ret_outcome (errno_ret ENOTDIR) m
  else if path_trailing_slash p then ret_outcome (errno_ret ENOTDIR) m
  else if fd_names_path (m_fds m) c then .unmodeled
  else ret_outcome (errno_ret witness_errno) m

/-- Mirrors [Fs.Namei.unlinkat_tmp_spec]. -/
private def unlinkat_tmp_witness (n p c : Fs.path) (flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if unlink_rmdir flags then .unmodeled
  else if decide (NAME_MAX < n.length) then .unmodeled
  else if fs_under (m_fs m) c then ret_outcome (errno_ret EISDIR) m
  else
    match fs_lookup (m_fs m) c with
    | none => ret_outcome (errno_ret ENOENT) m
    | some _ => unlink_found_witness p c flags m

private def unlinkat_body_witness (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | .CstrFault => ret_outcome (errno_ret EFAULT) m
  | .CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if !(bv_eqb dirfd AT_FDCWD32) then .unmodeled
      else
        let c := path_strip_trailing_slashes p
        if path_eqb c [] then
          (if unlink_rmdir flags then ret_outcome (errno_ret EBUSY) m
           else ret_outcome (errno_ret EISDIR) m)
        else if path_has_slash c then
          (match tmp_name c with
           | some n => unlinkat_tmp_witness n p c flags m
           | none => .unmodeled
           )
        else if path_eqb c dot_path then
          (if unlink_rmdir flags then ret_outcome (errno_ret EINVAL) m
           else ret_outcome (errno_ret EISDIR) m)
        else if path_eqb c dotdot_path then
          (if unlink_rmdir flags then ret_outcome (errno_ret ENOTEMPTY) m
           else ret_outcome (errno_ret EISDIR) m)
        else if decide (NAME_MAX < c.length) then .unmodeled
        else if fs_under (m_fs m) c then .unmodeled
        else
          match fs_lookup (m_fs m) c with
          | none => ret_outcome (errno_ret ENOENT) m
          | some _ => unlink_found_witness p c flags m

/-- The flag arm carries no copy-in — the kernel decides it before
    [getname()] — and every other arm carries the one pathname range
    [Fs.Namei.unlinkat_spec] records. -/
def unlinkat_witness (dirfd pathp flags : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(modeled_unlink_flags flags) then ret_outcome (errno_ret EINVAL) m
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (unlinkat_body_witness dirfd pathp flags i m)

/- =========================================================================
   The proofs
   ========================================================================= -/

private theorem unlink_found_witness_ok (p c : Fs.path) (flags : word)
    (i : SyscallInput) (m : Model) :
    unlink_found_spec p c flags m i m (unlink_found_witness p c flags m) := by
  unfold unlink_found_spec unlink_found_witness
  by_cases hrm : unlink_rmdir flags = true
  · simp only [ite_eq_left hrm, err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hrm]
    by_cases hts : path_trailing_slash p = true
    · simp only [ite_eq_left hts, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hts]
      by_cases hfd : fd_names_path (m_fds m) c = true
      · simp only [ite_eq_left hfd, unmodeled]
      · simp only [ite_eq_right hfd]
        refine alt_l _ _ i m (ret_outcome (errno_ret witness_errno) m) ?_
        refine bind_step (errno_from unlinkat_errnos) (fun e => err_ret e) i m
          witness_errno m (ret_outcome (errno_ret witness_errno) m) ?_ ?_
        · exact errno_head_witness witness_errno [EACCES, EPERM, EROFS, EBUSY] i m
        · simp only [err_ret, ret_only, ret_outcome, mkEffect,
            LinuxSem.LinuxProcessSem.pure]

private theorem unlinkat_tmp_witness_ok (n p c : Fs.path) (flags : word)
    (i : SyscallInput) (m : Model) :
    unlinkat_tmp_spec n p c flags m i m (unlinkat_tmp_witness n p c flags m) := by
  unfold unlinkat_tmp_spec unlinkat_tmp_witness
  by_cases hrm : unlink_rmdir flags = true
  · simp only [ite_eq_left hrm, unmodeled]
  · simp only [ite_eq_right hrm]
    by_cases hnm : decide (NAME_MAX < n.length) = true
    · simp only [ite_eq_left hnm, unmodeled]
    · simp only [ite_eq_right hnm]
      by_cases hun : fs_under (m_fs m) c = true
      · simp only [ite_eq_left hun, err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]
      · simp only [ite_eq_right hun]
        generalize hfs : fs_lookup (m_fs m) c = lk
        cases lk with
        | none =>
          dsimp only
          exact pure_ok (mkEffect (errno_ret ENOENT) [] []) i m
        | some data => exact unlink_found_witness_ok p c flags i m

private theorem unlinkat_body_witness_ok (dirfd pathp flags : word)
    (i : SyscallInput) (m : Model) :
    unlinkat_body_spec dirfd pathp flags i m i m
      (unlinkat_body_witness dirfd pathp flags i m) := by
  -- Both sides read the same guards in the same order, so one [simp only]
  -- per guard settles each: the spec is the head of the goal and the
  -- witness its second argument, so the rewrite hits both at once.  The
  -- body opens no binds, which is what the wrapper below peels instead.
  unfold unlinkat_body_spec unlinkat_body_witness
  try dsimp only
  generalize hc : read_cstr i.in_mem pathp = cr
  cases cr with
  | CstrTooLong =>
    try dsimp only
    exact pure_ok (mkEffect (errno_ret ENAMETOOLONG) [] []) i m
  | CstrFault =>
    try dsimp only
    exact pure_ok (mkEffect (errno_ret EFAULT) [] []) i m
  | CstrOk p =>
    try dsimp only
    by_cases hpe : path_eqb p [] = true
    · simp only [ite_eq_left hpe, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right hpe]
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · simp only [ite_eq_left hd, unmodeled]
      · simp only [ite_eq_right hd]
        by_cases hroot : path_eqb (path_strip_trailing_slashes p) [] = true
        · simp only [ite_eq_left hroot]
          by_cases hrm : unlink_rmdir flags = true
          · simp only [ite_eq_left hrm, err_ret, ret_only, ret_outcome, mkEffect,
              LinuxSem.LinuxProcessSem.pure]
          · simp only [ite_eq_right hrm, err_ret, ret_only, ret_outcome, mkEffect,
              LinuxSem.LinuxProcessSem.pure]
        · simp only [ite_eq_right hroot]
          by_cases hsl : path_has_slash (path_strip_trailing_slashes p) = true
          · simp only [ite_eq_left hsl]
            generalize htn : tmp_name (path_strip_trailing_slashes p) = tn
            cases tn with
            | none =>
              try dsimp only
              simp only [unmodeled]
            | some n =>
              try dsimp only
              exact unlinkat_tmp_witness_ok n p
                (path_strip_trailing_slashes p) flags i m
          · simp only [ite_eq_right hsl]
            by_cases hdot : path_eqb (path_strip_trailing_slashes p) dot_path = true
            · simp only [ite_eq_left hdot]
              by_cases hrm : unlink_rmdir flags = true
              · simp only [ite_eq_left hrm, err_ret, ret_only, ret_outcome, mkEffect,
                  LinuxSem.LinuxProcessSem.pure]
              · simp only [ite_eq_right hrm, err_ret, ret_only, ret_outcome, mkEffect,
                  LinuxSem.LinuxProcessSem.pure]
            · simp only [ite_eq_right hdot]
              by_cases hdd :
                  path_eqb (path_strip_trailing_slashes p) dotdot_path = true
              · simp only [ite_eq_left hdd]
                by_cases hrm : unlink_rmdir flags = true
                · simp only [ite_eq_left hrm, err_ret, ret_only, ret_outcome, mkEffect,
                    LinuxSem.LinuxProcessSem.pure]
                · simp only [ite_eq_right hrm, err_ret, ret_only, ret_outcome, mkEffect,
                    LinuxSem.LinuxProcessSem.pure]
              · simp only [ite_eq_right hdd]
                by_cases hnm : decide (NAME_MAX < (path_strip_trailing_slashes p).length)
                    = true
                · simp only [ite_eq_left hnm, unmodeled]
                · simp only [ite_eq_right hnm]
                  by_cases hun : fs_under (m_fs m) (path_strip_trailing_slashes p) = true
                  · simp only [ite_eq_left hun, unmodeled]
                  · simp only [ite_eq_right hun]
                    generalize hfs :
                      fs_lookup (m_fs m) (path_strip_trailing_slashes p) = lk
                    cases lk with
                    | none =>
                      try dsimp only
                      exact pure_ok (mkEffect (errno_ret ENOENT) [] []) i m
                    | some data =>
                      try dsimp only
                      exact unlink_found_witness_ok p
                        (path_strip_trailing_slashes p) flags i m

theorem unlinkat_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    unlinkat_spec dirfd pathp flags i m (unlinkat_witness dirfd pathp flags i m) := by
  unfold unlinkat_spec unlinkat_witness
  try dsimp only
  refine bind_step inputSpec _ i m i m _ rfl ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ rfl ?_
  try dsimp only
  by_cases hfl : (!(modeled_unlink_flags flags)) = true
  · simp only [ite_eq_left hfl, err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right hfl]
    exact record_copyins_outcome (unlinkat_body_witness_ok dirfd pathp flags i m)

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs leave no `vm_compute` goal either.  The checks
   below pin the two claims the witness's prose makes: the flag arm
   answers a bare -EINVAL, and the failure half of the removal is the
   errno that heads `unlinkat_errnos` — no model state needed. -/

/-- An illegal flag word is the bare -EINVAL outcome, with no copy-in. -/
example (i : SyscallInput) (m : Model) :
    unlinkat_witness AT_FDCWD32 0 1 i m = ret_outcome (errno_ret EINVAL) m := by
  simp only [unlinkat_witness]
  rw [ite_eq_left (by decide : (!(modeled_unlink_flags (1 : word))) = true)]

/-- The removal's witness is [witness_errno], which heads the spec's
    injectable set: `errno_from` can always draw it. -/
example (p c : Fs.path) (m : Model) (hrm : unlink_rmdir (0 : word) = false)
    (hts : path_trailing_slash p = false)
    (hfd : fd_names_path (m_fds m) c = false) :
    unlink_found_witness p c 0 m = ret_outcome (errno_ret witness_errno) m := by
  have h1 : ¬(unlink_rmdir (0 : word) = true) := by rw [hrm]; decide
  have h2 : ¬(path_trailing_slash p = true) := by rw [hts]; decide
  have h3 : ¬(fd_names_path (m_fds m) c = true) := by rw [hfd]; decide
  simp only [unlink_found_witness]
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

/-- `witness_errno` really is a member of `unlinkat_errnos`, so the
    failure half is inhabited (the witness never has to guess). -/
example : witness_errno ∈ unlinkat_errnos := by decide

end LinuxSem.Checks.Witness.Fs.Namei
