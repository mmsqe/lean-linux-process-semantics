/-
  * LinuxSem.Checks.Witness.Fs.Open — the openat (56), close (57), ftruncate (46) witnesses, and their proofs

  Answers to Linux [fs/open.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  `Checks.Witness.Prelude` re-exports the model/state/monad stack, and the
  witness's own spec — `Sys/Fs/Open.lean`, where `openat_core_spec`,
  `openat_body_spec`, `openat_resolved_spec`, the arm specs, `openat_spec`,
  `close_spec`, `ftruncate_spec`, `access_exists_spec`,
  `faccessat_body_spec`, `faccessat_spec` and `faccessat2_spec` live — is
  imported directly.

  A file-private definition or lemma is `private`; the two local witnesses
  and the two local lemmas below are file-private.  Lean has no
  or-patterns, so `ftruncate_witness`'s `FdFileW p _ | FdFileRW p _` arm is
  written out once per kind — the same term, one arm longer.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `ret_outcome` and `outcome_copyins` come from
  `Checks.Witness.Prelude` and `Sys.Syscall`.

  Both sides read the same guards in the same order, and the witness is the
  SECOND argument of the goal while the spec is the head of it, so one
  `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]` rewrites BOTH at once.
  (`rw` is not enough here: it rewrites one occurrence, leaving the
  witness's copy of the guard behind.)  The two matches (`read_cstr`,
  `fs_lookup`, `tmp_name`) are peeled with `generalize` + `cases`, so both
  copies reduce together.  The two opening steps of each proof — the input
  and the model — are spelled `bind_step … (input_ok i m)` and
  `bind_step … (getModel_ok i m)` where they are used.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Open

namespace LinuxSem.Checks.Witness.Fs.Open

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Fs.File (lowest_fd z_ldiff)
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   The witnesses
   ========================================================================= -/

private def openat_core_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(modeled_open_flags flags) then .unmodeled  -- unmodeled flag combination
  else match read_cstr i.in_mem pathp with
       | .CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  -- over-long path
       | .CstrFault => ret_outcome (errno_ret EFAULT) m          -- unreadable path
       | .CstrOk p =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m  -- empty pathname
           else if !(bv_eqb dirfd AT_FDCWD32) then .unmodeled       -- unmodeled dirfd
           -- a pathname with a separator, declined before any flag is
           -- looked at — see [Open.openat_resolved_spec]'s guard —
           -- except the one [Open.openat_sep_spec] answers
           else if path_has_slash p then
             (if path_eqb p localtime_path then
               (match fs_lookup (m_fs m) localtime_path with
               | some _ => .unmodeled
               | none =>
                   if fs_under (m_fs m) localtime_path then .unmodeled
                   else if flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT
                   then .unmodeled
                   else ret_outcome (errno_ret ENOENT) m)
             else if path_eqb p devnull_path then
               (match fs_lookup (m_fs m) devnull_path with
               | some _ => .unmodeled
               | none =>
                   if fs_under (m_fs m) devnull_path then .unmodeled
                   else
                   let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
                   if fl == 0 then ret_outcome (errno_ret witness_errno) m
                   else if fl == wr_create_flags then
                     ret_outcome (errno_ret witness_errno) m
                   else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else if fl == O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                   else if fl == append_create_flags then
                     ret_outcome (errno_ret witness_errno) m
                   else if rdwr_open_word fl then ret_outcome (errno_ret witness_errno) m
                   else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else .unmodeled)
             else if path_eqb p urandom_path then
               (match fs_lookup (m_fs m) urandom_path with
               | some _ => .unmodeled
               | none =>
                   if fs_under (m_fs m) urandom_path then .unmodeled
                   else
                   let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
                   if fl == 0 then ret_outcome (errno_ret witness_errno) m
                   else if is_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else if fl == O_DIRECTORY then ret_outcome (errno_ret ENOTDIR) m
                   else if is_rdwr_excl_create fl then ret_outcome (errno_ret EEXIST) m
                   else .unmodeled)
             else match tmp_name p with
                  | some n =>
                      if decide (NAME_MAX < n.length) then .unmodeled
                      else
                      let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
                      if fl == 0 then
                        (if fs_under (m_fs m) p then .unmodeled
                         else match fs_lookup (m_fs m) p with
                              | none => .unmodeled
                              | some _ => ret_outcome (errno_ret witness_errno) m)
                      else if fl == wr_create_flags then
                        (if path_is_dirref p || fs_under (m_fs m) p
                         then ret_outcome (errno_ret EISDIR) m
                         else ret_outcome (errno_ret witness_errno) m)
                      else .unmodeled
                  | none => .unmodeled)
           else
           let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
           if fl == 0 then
             if path_is_dirref p then
               ret_outcome (errno_ret witness_errno) m  -- "."/".." : env-failure branch
             else
             match fs_lookup (m_fs m) p with
             | none => ret_outcome (errno_ret ENOENT) m
             | some _ => ret_outcome (errno_ret witness_errno) m
           else if fl == wr_create_flags then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m  -- "."/".." or an implied directory : deterministic -EISDIR
             else
             ret_outcome (errno_ret witness_errno) m
           else if is_excl_create fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EEXIST) m  -- "."/".." or an implied directory : deterministic -EEXIST
             else
             match fs_lookup (m_fs m) p with
             | some _ => ret_outcome (errno_ret EEXIST) m  -- exists: deterministic -EEXIST
             | none => ret_outcome (errno_ret witness_errno) m  -- env-failure branch
           else if fl == O_DIRECTORY then
             -- the one arm with declines of its own: the witness follows
             -- them, since [.unmodeled] is the outcome the spec exhibits
             -- there
             if path_is_dirref p then
               ret_outcome (errno_ret witness_errno) m  -- "."/".." : env-failure branch
             else if decide (NAME_MAX < p.length) then .unmodeled
             else if fs_under (m_fs m) p then .unmodeled
             else
             match fs_lookup (m_fs m) p with
             | none => ret_outcome (errno_ret ENOENT) m
             | some _ => ret_outcome (errno_ret ENOTDIR) m
           else if fl == append_create_flags then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m  -- "."/".." or an implied directory : deterministic -EISDIR
             else
             ret_outcome (errno_ret witness_errno) m  -- env-failure branch
           else if rdwr_open_word fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EISDIR) m  -- "."/".." or an implied directory : deterministic -EISDIR
             else
             match fs_lookup (m_fs m) p with
             | none =>
                 if flag_set fl O_CREAT
                 then ret_outcome (errno_ret witness_errno) m  -- env-failure branch
                 else ret_outcome (errno_ret ENOENT) m         -- deterministic -ENOENT
             | some _ => ret_outcome (errno_ret witness_errno) m
           else if is_rdwr_excl_create fl then
             if path_is_dirref p || fs_under (m_fs m) p then
               ret_outcome (errno_ret EEXIST) m  -- "."/".." or an implied directory : deterministic -EEXIST
             else
             match fs_lookup (m_fs m) p with
             | some _ => ret_outcome (errno_ret EEXIST) m
             | none => ret_outcome (errno_ret witness_errno) m
           else .unmodeled   -- unreachable: [modeled_open_flags flags] holds here

def openat_witness (dirfd pathp flags : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  outcome_copyins
    [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (openat_core_witness dirfd pathp flags i m)

/- =========================================================================
   close (57) — deterministic: remove the fd or -EBADF
   ========================================================================= -/

def close_witness (fd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some _ => ret_outcome (BitVec.ofInt 64 0) (with_fds (fd_remove (m_fds m) fd) m)

theorem close_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    close_spec fd i m (close_witness fd m) := by
  unfold close_spec close_witness
  simp only [getModelSpec, bind_getModel]
  generalize hfs : fd_lookup (m_fds m) fd = lk
  cases lk with
  | none =>
    dsimp only
    exact pure_ok _ i m
  | some e =>
    dsimp only
    apply bind_step
    · exact modify_ok _ i m
    · exact pure_ok _ i _

/- =========================================================================
   ftruncate (46) — deterministic: set the length, or the errno for a
   non-writable / non-regular fd, a negative length or an unbuilt gap
   ========================================================================= -/

def ftruncate_witness (fd len : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if decide (len.toInt < 0) then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdSocket _) => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdPipe _ _) => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdDevNull _ _) => ret_outcome (errno_ret EINVAL) m
  | some FdEntry.FdUrandom => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdFile _ _) => ret_outcome (errno_ret EINVAL) m
  | some FdEntry.FdDir => ret_outcome (errno_ret EINVAL) m
  | some (FdEntry.FdFileW p _) =>
      (match fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          if !(modeled_truncate_gap data len) then .unmodeled
          else ret_outcome (BitVec.ofInt 64 0)
                 (with_fs (fs_set (m_fs m) p (file_truncate data len)) m))
  | some (FdEntry.FdFileRW p _) =>
      (match fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          if !(modeled_truncate_gap data len) then .unmodeled
          else ret_outcome (BitVec.ofInt 64 0)
                 (with_fs (fs_set (m_fs m) p (file_truncate data len)) m))
  | some (FdEntry.FdFileA p _) =>
      -- a writable regular file too: see [Open.ftruncate_spec]
      (match fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          if !(modeled_truncate_gap data len) then .unmodeled
          else ret_outcome (BitVec.ofInt 64 0)
                 (with_fs (fs_set (m_fs m) p (file_truncate data len)) m))

/-- Close a leaf in which both sides reduced to the bare-return shape:
    the spec's [err_ret] and the witness's [ret_outcome] are the same
    [pure] of the same [mkEffect]. -/
macro "ret_leaf" : tactic =>
  `(tactic| simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure])

theorem ftruncate_witness_ok (fd len : word) (i : SyscallInput) (m : Model) :
    ftruncate_spec fd len i m (ftruncate_witness fd len m) := by
  unfold ftruncate_spec ftruncate_witness
  by_cases hneg : decide (len.toInt < 0) = true
  · simp only [ite_eq_left hneg]
    ret_leaf
  · simp only [ite_eq_right hneg]
    simp only [getModelSpec, bind_getModel]
    generalize hfd : fd_lookup (m_fds m) fd = lk
    cases lk with
    | none =>
      dsimp only
      ret_leaf
    | some e =>
      cases e with
      | FdChannel ch =>
        dsimp only
        ret_leaf
      | FdSocket sk =>
        dsimp only
        ret_leaf
      | FdPipe id wr =>
        dsimp only
        ret_leaf
      | FdDevNull rd wr =>
        dsimp only
        ret_leaf
      | FdUrandom =>
        dsimp only
        ret_leaf
      | FdFile p cur =>
        dsimp only
        ret_leaf
      | FdDir =>
        dsimp only
        ret_leaf
      | FdFileA p cur =>
        dsimp only
        try simp only [ftruncate_file_arm]
        try dsimp only
        generalize hfs : fs_lookup (m_fs m) p = lk2
        cases lk2 with
        | none =>
          dsimp only
          exact unmodeled_intro i m
        | some data =>
          dsimp only
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · simp only [ite_eq_left hgap]
            exact unmodeled_intro i m
          · simp only [ite_eq_right hgap]
            apply bind_step
            · exact modify_ok _ i m
            · ret_leaf
      | FdFileW p cur =>
        dsimp only
        try simp only [ftruncate_file_arm]
        try dsimp only
        generalize hfs : fs_lookup (m_fs m) p = lk2
        cases lk2 with
        | none =>
          dsimp only
          exact unmodeled_intro i m
        | some data =>
          dsimp only
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · simp only [ite_eq_left hgap]
            exact unmodeled_intro i m
          · simp only [ite_eq_right hgap]
            apply bind_step
            · exact modify_ok _ i m
            · ret_leaf
      | FdFileRW p cur =>
        dsimp only
        try simp only [ftruncate_file_arm]
        try dsimp only
        generalize hfs : fs_lookup (m_fs m) p = lk2
        cases lk2 with
        | none =>
          dsimp only
          exact unmodeled_intro i m
        | some data =>
          dsimp only
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · simp only [ite_eq_left hgap]
            exact unmodeled_intro i m
          · simp only [ite_eq_right hgap]
            apply bind_step
            · exact modify_ok _ i m
            · ret_leaf

/- =========================================================================
   faccessat (48) / faccessat2 (439)
   ========================================================================= -/

/-- faccessat witness: the deterministic errno arms, the fail-closed
    [Unmodeled], or — where the path resolves — plain SUCCESS.  That is
    the [alt]'s RIGHT branch, unlike the openat and unlinkat witnesses
    which take the injectable-errno branch to avoid building a new model
    state.  Nothing has to be built here: faccessat changes no state, so
    both alternatives return the same model and the success one is the
    outcome a real run actually produces. -/
private def faccessat_body_witness (dirfd pathp : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m
  | .CstrFault => ret_outcome (errno_ret EFAULT) m
  | .CstrOk p =>
      if path_eqb p [] then ret_outcome (errno_ret ENOENT) m
      else if !(bv_eqb dirfd AT_FDCWD32) then .unmodeled
      else if path_eqb p dot_path then ret_outcome (BitVec.ofInt 64 0) m
      else if path_eqb p dotdot_path then ret_outcome (BitVec.ofInt 64 0) m
      else if path_has_slash p then .unmodeled
      else if decide (NAME_MAX < p.length) then .unmodeled
      else if fs_under (m_fs m) p then .unmodeled
      else
      match fs_lookup (m_fs m) p with
      | none => ret_outcome (errno_ret ENOENT) m
      | some _ => ret_outcome (BitVec.ofInt 64 0) m

/-- Both mode arms carry no copy-in — the kernel decides the mode before
    [user_path_at] — and every other arm carries the one pathname range
    [Fs.Open.faccessat_spec] records. -/
def faccessat_witness (dirfd pathp mode : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if !(access_mode_f_ok mode) then .unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_witness dirfd pathp i m)

private theorem faccessat_body_witness_ok (dirfd pathp : word) (i : SyscallInput)
    (m : Model) :
    faccessat_body_spec dirfd pathp i m i m (faccessat_body_witness dirfd pathp i m) := by
  unfold faccessat_body_spec faccessat_body_witness
  generalize hc : read_cstr i.in_mem pathp = cr
  cases cr with
  | CstrTooLong =>
    dsimp only
    ret_leaf
  | CstrFault =>
    dsimp only
    ret_leaf
  | CstrOk p =>
    dsimp only
    by_cases hpe : path_eqb p [] = true
    · simp only [ite_eq_left hpe]
      ret_leaf
    · simp only [ite_eq_right hpe]
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · simp only [ite_eq_left hd]
        exact unmodeled_intro i m
      · simp only [ite_eq_right hd]
        by_cases hdot : path_eqb p dot_path = true
        · simp only [ite_eq_left hdot, access_exists_spec]
          apply alt_r
          ret_leaf
        · simp only [ite_eq_right hdot]
          by_cases hdd : path_eqb p dotdot_path = true
          · simp only [ite_eq_left hdd, access_exists_spec]
            apply alt_r
            ret_leaf
          · simp only [ite_eq_right hdd]
            by_cases hsl : path_has_slash p = true
            · simp only [ite_eq_left hsl]
              exact unmodeled_intro i m
            · simp only [ite_eq_right hsl]
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · simp only [ite_eq_left hnm]
                exact unmodeled_intro i m
              · simp only [ite_eq_right hnm]
                by_cases hun : fs_under (m_fs m) p = true
                · simp only [ite_eq_left hun]
                  exact unmodeled_intro i m
                · simp only [ite_eq_right hun]
                  generalize hfs : fs_lookup (m_fs m) p = lk
                  cases lk with
                  | none =>
                    dsimp only
                    ret_leaf
                  | some data =>
                    dsimp only
                    simp only [access_exists_spec]
                    apply alt_r
                    ret_leaf

theorem faccessat_witness_ok (dirfd pathp mode : word) (i : SyscallInput) (m : Model) :
    faccessat_spec dirfd pathp mode i m (faccessat_witness dirfd pathp mode i m) := by
  unfold faccessat_spec faccessat_witness
  apply bind_step
  · exact input_ok i m
  · apply bind_step
    · exact getModel_ok i m
    · by_cases hmo : (!(modeled_access_mode mode)) = true
      · simp only [ite_eq_left hmo]
        ret_leaf
      · simp only [ite_eq_right hmo]
        by_cases hf : (!(access_mode_f_ok mode)) = true
        · simp only [ite_eq_left hf]
          exact unmodeled_intro i m
        · simp only [ite_eq_right hf]
          exact record_copyins_outcome (faccessat_body_witness_ok dirfd pathp i m)

/-- faccessat2's witness is faccessat's, under one more -EINVAL and one
    more decline: [do_faccessat] is the shared body, so past the flag
    word there is nothing new to build. -/
def faccessat2_witness (dirfd pathp mode flags : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !(modeled_access_mode mode) then ret_outcome (errno_ret EINVAL) m
  else if !(valid_access_flags flags) then ret_outcome (errno_ret EINVAL) m
  else if !(modeled_access_flags flags) then .unmodeled
  else if !(access_mode_f_ok mode) then .unmodeled
  else
    outcome_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (faccessat_body_witness dirfd pathp i m)

theorem faccessat2_witness_ok (dirfd pathp mode flags : word) (i : SyscallInput)
    (m : Model) :
    faccessat2_spec dirfd pathp mode flags i m
      (faccessat2_witness dirfd pathp mode flags i m) := by
  unfold faccessat2_spec faccessat2_witness
  apply bind_step
  · exact input_ok i m
  · apply bind_step
    · exact getModel_ok i m
    · by_cases hmo : (!(modeled_access_mode mode)) = true
      · simp only [ite_eq_left hmo]
        ret_leaf
      · simp only [ite_eq_right hmo]
        by_cases hfl : (!(valid_access_flags flags)) = true
        · simp only [ite_eq_left hfl]
          ret_leaf
        · simp only [ite_eq_right hfl]
          by_cases hmf : (!(modeled_access_flags flags)) = true
          · simp only [ite_eq_left hmf]
            exact unmodeled_intro i m
          · simp only [ite_eq_right hmf]
            by_cases hf : (!(access_mode_f_ok mode)) = true
            · simp only [ite_eq_left hf]
              exact unmodeled_intro i m
            · simp only [ite_eq_right hf]
              exact record_copyins_outcome (faccessat_body_witness_ok dirfd pathp i m)

/- =========================================================================
   openat (56) — the core witness and its proof
   ========================================================================= -/

/-- One admissible outcome of [openat_core_spec]: the guards it shares
    with the core spec decide every arm, and where an [alt] would let the
    call SUCCEED the witness takes the injectable environment failure —
    the branch that needs no model state.  The two exceptions are the
    deterministic errno arms (-EISDIR, -EEXIST, -ENOTDIR, -ENOENT), which
    the spec answers without an environment choice.

    The four `_spec` arms this function inlines are the same four the
    checker's witness follows; the comments name the kernel answer each
    one is imitating (see [Sys.Fs.Open]'s own notes on
    `openat_create_spec`, `openat_excl_spec`, `openat_dir_spec` and the
    device arms). -/
private theorem openat_core_witness_ok (dirfd pathp flags : word) (i : SyscallInput)
    (m : Model) :
    openat_core_spec dirfd pathp flags i m (openat_core_witness dirfd pathp flags i m) := by
  unfold openat_core_spec openat_core_witness
  by_cases hfl : (!(modeled_open_flags flags)) = true
  · -- unmodeled flags: declined BEFORE the pathname is fetched
    apply bind_step
    · exact input_ok i m
    · apply bind_step
      · exact getModel_ok i m
      · simp only [ite_eq_left hfl]
        exact unmodeled_intro i _
  · apply bind_step
    · exact input_ok i m
    · apply bind_step
      · exact getModel_ok i m
      · simp only [ite_eq_right hfl]
        unfold openat_body_spec
        generalize hc : read_cstr i.in_mem pathp = cr
        cases cr with
        | CstrTooLong =>
          dsimp only
          ret_leaf
        | CstrFault =>
          dsimp only
          ret_leaf
        | CstrOk p =>
          dsimp only
          by_cases hpe : path_eqb p [] = true
          · simp only [ite_eq_left hpe]
            ret_leaf
          · simp only [ite_eq_right hpe]
            by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
            · simp only [ite_eq_left hd]
              exact unmodeled_intro i m
            · simp only [ite_eq_right hd]
              try unfold openat_resolved_spec openat_sep_spec openat_localtime_spec openat_devnull_spec open_devnull openat_urandom_spec open_urandom openat_tmp_spec openat_read_spec openat_create_spec openat_excl_spec openat_dir_spec openat_append_spec openat_rdwr_spec openat_rdwr_excl_spec open_result_spec create_wronly open_append open_rdwr
              by_cases hsl : path_has_slash p = true
              · simp only [ite_eq_left hsl]
                by_cases hl : path_eqb p localtime_path = true
                · simp only [ite_eq_left hl]
                  generalize hfs : fs_lookup (m_fs m) localtime_path = lk
                  cases lk with
                  | some data =>
                    dsimp only
                    exact unmodeled_intro i m
                  | none =>
                    dsimp only
                    by_cases hu : fs_under (m_fs m) localtime_path = true
                    · simp only [ite_eq_left hu]
                      exact unmodeled_intro i m
                    · simp only [ite_eq_right hu]
                      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
                      · simp only [ite_eq_left hcr]
                        exact unmodeled_intro i m
                      · simp only [ite_eq_right hcr]
                        ret_leaf
                · simp only [ite_eq_right hl]
                  by_cases hdv : path_eqb p devnull_path = true
                  · simp only [ite_eq_left hdv]
                    generalize hfs : fs_lookup (m_fs m) devnull_path = lk
                    cases lk with
                    | some data =>
                      dsimp only
                      exact unmodeled_intro i m
                    | none =>
                      try dsimp only
                      by_cases hu : fs_under (m_fs m) devnull_path = true
                      · simp only [ite_eq_left hu]
                        exact unmodeled_intro i m
                      · simp only [ite_eq_right hu]
                        try dsimp only
                        by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
                        · simp only [ite_eq_left h0]
                          apply alt_l
                          apply bind_step
                          · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                          · ret_leaf
                        · simp only [ite_eq_right h0]
                          by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
                          · simp only [ite_eq_left hw]
                            apply alt_l
                            apply bind_step
                            · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                            · ret_leaf
                          · simp only [ite_eq_right hw]
                            by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                            · simp only [ite_eq_left hx]
                              ret_leaf
                            · simp only [ite_eq_right hx]
                              by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
                              · simp only [ite_eq_left hdir]
                                ret_leaf
                              · simp only [ite_eq_right hdir]
                                by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
                                · simp only [ite_eq_left hap]
                                  apply alt_l
                                  apply bind_step
                                  · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                  · ret_leaf
                                · simp only [ite_eq_right hap]
                                  by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                                  · simp only [ite_eq_left hrw]
                                    apply alt_l
                                    apply bind_step
                                    · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                    · ret_leaf
                                  · simp only [ite_eq_right hrw]
                                    by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                                    · simp only [ite_eq_left hrx]
                                      ret_leaf
                                    · simp only [ite_eq_right hrx]
                                      exact unmodeled_intro i m
                  · simp only [ite_eq_right hdv]
                    by_cases hu : path_eqb p urandom_path = true
                    · simp only [ite_eq_left hu]
                      generalize hfs : fs_lookup (m_fs m) urandom_path = lk
                      cases lk with
                      | some data =>
                        dsimp only
                        exact unmodeled_intro i m
                      | none =>
                        try dsimp only
                        by_cases hun : fs_under (m_fs m) urandom_path = true
                        · simp only [ite_eq_left hun]
                          exact unmodeled_intro i m
                        · simp only [ite_eq_right hun]
                          try dsimp only
                          by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
                          · simp only [ite_eq_left h0]
                            apply alt_l
                            apply bind_step
                            · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                            · ret_leaf
                          · simp only [ite_eq_right h0]
                            by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                            · simp only [ite_eq_left hx]
                              ret_leaf
                            · simp only [ite_eq_right hx]
                              by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
                              · simp only [ite_eq_left hdir]
                                ret_leaf
                              · simp only [ite_eq_right hdir]
                                by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                                · simp only [ite_eq_left hrx]
                                  ret_leaf
                                · simp only [ite_eq_right hrx]
                                  exact unmodeled_intro i m
                    · simp only [ite_eq_right hu]
                      generalize htn : tmp_name p = tn
                      cases tn with
                      | none =>
                        dsimp only
                        exact unmodeled_intro i m
                      | some n =>
                        dsimp only
                        by_cases hnm : decide (NAME_MAX < n.length) = true
                        · simp only [ite_eq_left hnm]
                          exact unmodeled_intro i m
                        · simp only [ite_eq_right hnm]
                          try dsimp only
                          by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
                          · simp only [ite_eq_left h0]
                            by_cases hun : fs_under (m_fs m) p = true
                            · simp only [ite_eq_left hun]
                              exact unmodeled_intro i m
                            · simp only [ite_eq_right hun]
                              generalize hfs : fs_lookup (m_fs m) p = lk
                              cases lk with
                              | none =>
                                dsimp only
                                exact unmodeled_intro i m
                              | some data =>
                                dsimp only
                                by_cases hdot : path_is_dirref p = true
                                · simp only [ite_eq_left hdot]
                                  apply alt_l
                                  apply bind_step
                                  · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                  · ret_leaf
                                · simp only [ite_eq_right hdot]
                                  apply alt_l
                                  apply bind_step
                                  · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                  · ret_leaf
                          · simp only [ite_eq_right h0]
                            by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
                            · simp only [ite_eq_left hw]
                              by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                              · simp only [ite_eq_left hdot]
                                ret_leaf
                              · simp only [ite_eq_right hdot]
                                apply alt_l
                                apply bind_step
                                · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                · ret_leaf
                            · simp only [ite_eq_right hw]
                              exact unmodeled_intro i m
              · simp only [ite_eq_right hsl]
                try dsimp only
                by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
                · simp only [ite_eq_left h0]
                  by_cases hdot : path_is_dirref p = true
                  · simp only [ite_eq_left hdot]
                    apply alt_l
                    apply bind_step
                    · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                    · ret_leaf
                  · simp only [ite_eq_right hdot]
                    generalize hfs : fs_lookup (m_fs m) p = lk
                    cases lk with
                    | none =>
                      dsimp only
                      ret_leaf
                    | some data =>
                      dsimp only
                      apply alt_l
                      apply bind_step
                      · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                      · ret_leaf
                · simp only [ite_eq_right h0]
                  by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
                  · simp only [ite_eq_left hw]
                    by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                    · simp only [ite_eq_left hdot]
                      ret_leaf
                    · simp only [ite_eq_right hdot]
                      apply alt_l
                      apply bind_step
                      · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                      · ret_leaf
                  · simp only [ite_eq_right hw]
                    by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                    · simp only [ite_eq_left hx]
                      by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                      · simp only [ite_eq_left hdot]
                        ret_leaf
                      · simp only [ite_eq_right hdot]
                        generalize hfs : fs_lookup (m_fs m) p = lk
                        cases lk with
                        | some data =>
                          dsimp only
                          ret_leaf
                        | none =>
                          dsimp only
                          apply alt_l
                          apply bind_step
                          · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                          · ret_leaf
                    · simp only [ite_eq_right hx]
                      by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
                      · simp only [ite_eq_left hdir]
                        by_cases hdot : path_is_dirref p = true
                        · simp only [ite_eq_left hdot]
                          apply alt_l
                          apply bind_step
                          · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                          · ret_leaf
                        · simp only [ite_eq_right hdot]
                          by_cases hnm : decide (NAME_MAX < p.length) = true
                          · simp only [ite_eq_left hnm]
                            exact unmodeled_intro i m
                          · simp only [ite_eq_right hnm]
                            by_cases hun : fs_under (m_fs m) p = true
                            · simp only [ite_eq_left hun]
                              exact unmodeled_intro i m
                            · simp only [ite_eq_right hun]
                              generalize hfs : fs_lookup (m_fs m) p = lk
                              cases lk with
                              | none =>
                                dsimp only
                                ret_leaf
                              | some data =>
                                dsimp only
                                ret_leaf
                      · simp only [ite_eq_right hdir]
                        by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
                        · simp only [ite_eq_left hap]
                          by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                          · simp only [ite_eq_left hdot]
                            ret_leaf
                          · simp only [ite_eq_right hdot]
                            apply alt_l
                            apply bind_step
                            · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                            · ret_leaf
                        · simp only [ite_eq_right hap]
                          by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                          · simp only [ite_eq_left hrw]
                            by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                            · simp only [ite_eq_left hdot]
                              ret_leaf
                            · simp only [ite_eq_right hdot]
                              generalize hfs : fs_lookup (m_fs m) p = lk
                              cases lk with
                              | some data =>
                                dsimp only
                                apply alt_l
                                apply bind_step
                                · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                · ret_leaf
                              | none =>
                                dsimp only
                                by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
                                · simp only [ite_eq_left hcr]
                                  apply alt_l
                                  apply bind_step
                                  · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                  · ret_leaf
                                · simp only [ite_eq_right hcr]
                                  ret_leaf
                          · simp only [ite_eq_right hrw]
                            by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                            · simp only [ite_eq_left hrx]
                              by_cases hdot : (path_is_dirref p || fs_under (m_fs m) p) = true
                              · simp only [ite_eq_left hdot]
                                ret_leaf
                              · simp only [ite_eq_right hdot]
                                generalize hfs : fs_lookup (m_fs m) p = lk
                                cases lk with
                                | some data =>
                                  dsimp only
                                  ret_leaf
                                | none =>
                                  dsimp only
                                  apply alt_l
                                  apply bind_step
                                  · exact errno_head_witness witness_errno [EACCES, EMFILE, ENFILE] i m
                                  · ret_leaf
                            · simp only [ite_eq_right hrx]
                              exact unmodeled_intro i m

theorem openat_witness_ok (dirfd pathp flags : word) (i : SyscallInput) (m : Model) :
    openat_spec dirfd pathp flags i m (openat_witness dirfd pathp flags i m) := by
  unfold openat_spec openat_witness
  apply bind_step
  · exact input_ok i m
  · exact record_copyins_outcome (openat_core_witness_ok dirfd pathp flags i m)
