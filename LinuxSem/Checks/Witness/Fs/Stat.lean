/-
  * LinuxProcessSem.Checks.Witness.Fs.Stat — the readlinkat (78), newfstatat (79) and fstat (80) witnesses, and their proofs

  Answers to Linux [fs/stat.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  `Checks.Witness.Prelude` re-exports the model/state/monad stack and
  supplies [ret_outcome], [bind_step] and the [srw] tactic macro;
  `Sys.Fs.Stat` supplies the specs; `Sys.Uapi` supplies the `struct stat`
  layer, including [stat_buf_wf], [stat_set_size] and the three seeds'
  predicates.  `newfstatat_core_witness_ok` is `private` — Lean's
  file-private scope, which keeps its equation lemmas unnameable outside
  the file.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`; `mkEffect ret [] []` abbreviates
  `mkEffectU ret [] [] [] [] []` (`State.lean`), and a closed branch test
  is discharged by `decide`.

  The monadic step is [bind_step]: `inputSpec …` is definitionally
  `.ok _ _ []`, so `refine bind_step inputSpec … _ (input_ok i m) ?_`
  peels it, and `dsimp only` reduces the beta/iota/zeta redexes after it.

  A scrutinee rewrite is where these proofs differ from the checker's: the
  spec's copy of each test sits UNDER the two reader `bind`s' lambdas
  while the witness's copy does not, so no single rewrite reaches both
  sides.  Each proof therefore splits the two apart — a
  `generalize … at ⊢` / `cases` on the witness's copy fixes which arm the
  witness chose, and the spec's copy is then reduced by rewriting with the
  same equation (`hR`, `hfs`, …) once the two [bind_step]s have
  beta-reduced the lambdas.  Every proof below opens with the two readers
  (`input`, then `get_model`) and only then walks the body; the one
  exception is [newfstatat_core_witness_ok], whose `read_cstr` split is
  taken before the readers precisely because it only has to constrain the
  WITNESS side.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Stat

namespace LinuxSem.Checks.Witness.Fs.Stat

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Stat
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   readlinkat (78)
   ========================================================================= -/

/-- readlinkat's witness: the fail-closed [Unmodeled] for a dirfd other
    than AT_FDCWD, and the deterministic -EINVAL otherwise.  There is no
    choice to make — [readlinkat_spec] has no [alt]. -/
def readlinkat_witness (dirfd : word) (m : Model) : Outcome SyscallEffect Model event :=
  if !(bv_eqb dirfd AT_FDCWD32) then .unmodeled
  else ret_outcome (errno_ret EINVAL) m

theorem readlinkat_witness_ok (dirfd : word) (i : SyscallInput) (m : Model) :
    readlinkat_spec dirfd i m (readlinkat_witness dirfd m) := by
  unfold readlinkat_spec readlinkat_witness
  by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
  · simp only [ite_eq_left hd]
    exact unmodeled_intro i m
  · simp only [ite_eq_right hd]
    simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]

/- =========================================================================
   newfstatat (79)
   ========================================================================= -/

/-- newfstatat: a path errno (-ENAMETOOLONG / -EFAULT / -ENOENT) or
    [Unmodeled].  Every arm is deterministic: the spec has no [alt],
    because it never reaches an arm that could succeed. -/
def newfstatat_core_witness (dirfd pathp flag : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(modeled_statat_flags flag) then .unmodeled   -- unmodeled flag word
  else match read_cstr i.in_mem pathp with
       | .CstrTooLong => ret_outcome (errno_ret ENAMETOOLONG) m  -- over-long path
       | .CstrFault => ret_outcome (errno_ret EFAULT) m          -- unreadable path
       | .CstrOk p =>
           if path_eqb p [] then ret_outcome (errno_ret ENOENT) m  -- empty pathname
           else if !(bv_eqb dirfd AT_FDCWD32) then .unmodeled   -- unmodeled dirfd
           else if path_eqb p dot_path then .unmodeled          -- directory metadata
           else match fs_lookup (m_fs m) p with
                | none => ret_outcome (errno_ret ENOENT) m        -- absent file
                | some _ => .unmodeled                            -- would succeed

/-- The pathname bytes [newfstatat_spec] records ride along on every
    outcome, exactly as [openat_witness] carries [openat]'s. -/
def newfstatat_witness (dirfd pathp flag : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  outcome_copyins
    [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    (newfstatat_core_witness dirfd pathp flag i m)

private theorem newfstatat_core_witness_ok (dirfd pathp flag : word)
    (i : SyscallInput) (m : Model) :
    newfstatat_core_spec dirfd pathp flag i m
      (newfstatat_core_witness dirfd pathp flag i m) := by
  unfold newfstatat_core_spec newfstatat_core_witness
  by_cases hfl : (!(modeled_statat_flags flag)) = true
  · simp only [ite_eq_left hfl]
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    try try try try dsimp only
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    try try try dsimp only
    exact unmodeled_intro i m
  · simp only [ite_eq_right hfl]
    generalize hR : read_cstr i.in_mem pathp = r at ⊢
    cases r with
    | CstrTooLong =>
      refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
      dsimp only
      refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
      try try try try dsimp only
      simp only [hR, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    | CstrFault =>
      refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
      dsimp only
      refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
      try try try try dsimp only
      simp only [hR, err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    | CstrOk p =>
      by_cases hpe : path_eqb p [] = true
      · refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
        dsimp only
        refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
        try try try try dsimp only
        simp only [hR, ite_eq_left hpe, err_ret, ret_only, ret_outcome, mkEffect,
          LinuxSem.LinuxProcessSem.pure]
      · by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
        · refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
          dsimp only
          refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
          try try try try dsimp only
          simp only [hR, ite_eq_right hpe, ite_eq_left hd]
          exact unmodeled_intro i m
        · by_cases hdot : path_eqb p dot_path = true
          · refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
            dsimp only
            refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
            try try try try dsimp only
            simp only [hR, ite_eq_right hpe, ite_eq_right hd, ite_eq_left hdot]
            exact unmodeled_intro i m
          · generalize hfs : fs_lookup (m_fs m) p = lk at ⊢
            cases lk with
            | none =>
              refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
              dsimp only
              refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
              try try try try dsimp only
              simp only [hR, ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs,
                err_ret, ret_only, ret_outcome, mkEffect,
                LinuxSem.LinuxProcessSem.pure]
            | some data =>
              refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
              dsimp only
              refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
              try try try try dsimp only
              simp only [hR, ite_eq_right hpe, ite_eq_right hd, ite_eq_right hdot, hfs]
              exact unmodeled_intro i m

/- =========================================================================
   fstat (80)
   ========================================================================= -/

/-- ONE [struct stat] INSIDE [Uapi.stat_buf_wf]'s ENVELOPE, and the
    smallest that is: 128 bytes, zero everywhere except [st_mode], which
    is a bare S_IFREG.  It is the SEED the witnesses below patch a
    length into, never an answer the spec prefers — [Stat.fstat_file_spec]
    chooses over the whole envelope, and progress needs one member of
    that set named, not the likeliest one.  A real [struct stat] has a
    nonzero device, inode and block size; nothing here claims otherwise.

    S_IFREG rather than one of the six other types on purpose: it is the
    arm whose [st_size] obligation actually bites, so the witness
    exercises [Uapi.stat_size_ok]'s interesting half rather than
    discharging it vacuously. -/
def stat_witness_base : List byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFREG ++ Z_to_le_bytes 108 0

/- The 128-byte seeds below are checked by full evaluation over a
   literal byte list, which outruns the default recursion depth; the
   option raises the fuel (it is not a proof principle, and every term
   it is spent on is closed — the same note `Sys/Fs/Stat.lean` carries). -/
set_option maxRecDepth 16000
theorem stat_witness_base_wf : stat_buf_wf stat_witness_base = true := by decide

theorem stat_witness_base_length : stat_witness_base.length = 128 := by decide

/-- The buffer each file arm's witness delivers: the seed above with the
    file's current length written into [st_size] on the branch that has
    no pin, and THE PIN ITSELF with the same patch on the branch that
    has one — because there the stable members are not the witness's to
    pick. -/
def fstat_witness_buf (n : Nat) (pin : Option (List byte)) : List byte :=
  match pin with
  | some b0 => stat_set_size n b0
  | none => stat_set_size n stat_witness_base

/-- fstat's file arms, mirroring [Stat.fstat_file_spec] branch for
    branch.  Deterministic even where the spec chooses: a witness names
    one admissible outcome, and these are the [choose]s resolved to
    [fstat_witness_buf]. -/
def fstat_file_witness (p : Fs.path) (statbuf : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  match fs_lookup (m_fs m) p with
  | none => .unmodeled                         -- unlinked under an open fd
  | some data =>
      if !(access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
      else
        match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
        | none => .unmodeled                   -- a partial [copy_to_user]
        | some _ =>
            match statpin_lookup (m_statpins m) p with
            | some b0 =>
                if !(stat_buf_wf b0) then .unmodeled
                else .ok (mkEffect (BitVec.ofInt 64 0)
                          [(statbuf, fstat_witness_buf data.length (some b0))] [])
                        m []
            | none =>
                let bs := fstat_witness_buf data.length none
                .ok (mkEffect (BitVec.ofInt 64 0) [(statbuf, bs)] [])
                   (with_statpin p bs m) []

theorem fstat_file_witness_ok (p : Fs.path) (statbuf : word)
    (i : SyscallInput) (m : Model) :
    fstat_file_spec p statbuf i m (fstat_file_witness p statbuf i m) := by
  unfold fstat_file_spec fstat_file_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try try try try dsimp only
  generalize hfs : fs_lookup (m_fs m) p = lk at ⊢
  cases lk with
  | none =>
    dsimp only
    exact unmodeled_intro i m
  | some data =>
    dsimp only
    by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
    · simp only [ite_eq_left ha]
      simp only [err_ret, ret_only, ret_outcome, mkEffect,
        LinuxSem.LinuxProcessSem.pure]
    · simp only [ite_eq_right ha]
      generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w
        at ⊢
      cases w with
      | none =>
        dsimp only
        exact unmodeled_intro i m
      | some w =>
        dsimp only
        generalize hp : statpin_lookup (m_statpins m) p = pin at ⊢
        cases pin with
        | some b0 =>
          dsimp only
          by_cases hb : (!(stat_buf_wf b0)) = true
          · simp only [ite_eq_left hb]
            exact unmodeled_intro i m
          · simp only [ite_eq_right hb]
            have hb' : stat_buf_wf b0 = true := by simpa using hb
            have hlen : b0.length = 128 := stat_buf_wf_length b0 hb'
            refine bind_step (choose (fun bs : List byte =>
                stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true ∧
                stat_stable_eqb bs b0 = true)) _ i m
              (stat_set_size data.length b0) m _ ?_ ?_
            · exact choose_ok _ _ i m
                ⟨stat_set_size_wf _ b0 hb', stat_set_size_size_ok _ b0 hlen,
                 stat_set_size_stable _ b0 hlen⟩
            · simp only [mkEffect, fstat_witness_buf, LinuxSem.LinuxProcessSem.pure]
        | none =>
          dsimp only
          refine bind_step (choose (fun bs : List byte =>
              stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true)) _ i m
            (stat_set_size data.length stat_witness_base) m _ ?_ ?_
          · exact choose_ok _ _ i m
              ⟨stat_set_size_wf _ _ stat_witness_base_wf,
               stat_set_size_size_ok _ _ stat_witness_base_length⟩
          · try try try dsimp only
            refine bind_step
              (modifySpec (with_statpin p (stat_set_size data.length stat_witness_base)))
              _ i m ()
              (with_statpin p (stat_set_size data.length stat_witness_base) m)
              _ (modify_ok _ i m) ?_
            try try dsimp only
            simp only [mkEffect, fstat_witness_buf, LinuxSem.LinuxProcessSem.pure]

/-- THE /dev/null SEED: [stat_witness_base] with the device's four
    members set — S_IFCHR, [st_rdev] 1:3, and the zero [st_size] and
    [st_blocks] the seed already carries — so that it satisfies
    [Uapi.stat_devnull_ok] outright.  Zero everywhere else, for the
    reason the file seed is.  [stat_urandom_witness_base] is the same
    seed with the random device's number. -/
def stat_chrdev_witness_base (rdev : Int) : List byte :=
  Z_to_le_bytes 16 0 ++ Z_to_le_bytes 4 S_IFCHR ++ Z_to_le_bytes 12 0
  ++ Z_to_le_bytes 8 rdev ++ Z_to_le_bytes 88 0

def stat_devnull_witness_base : List byte :=
  stat_chrdev_witness_base DEVNULL_RDEV

def stat_urandom_witness_base : List byte :=
  stat_chrdev_witness_base URANDOM_RDEV

theorem stat_devnull_witness_base_wf :
    stat_buf_wf stat_devnull_witness_base = true := by decide

theorem stat_devnull_witness_base_ok :
    stat_devnull_ok stat_devnull_witness_base = true := by decide

theorem stat_urandom_witness_base_wf :
    stat_buf_wf stat_urandom_witness_base = true := by decide

theorem stat_urandom_witness_base_ok :
    stat_urandom_ok stat_urandom_witness_base = true := by decide

/-- fstat's character-device arm, mirroring [Stat.fstat_chrdev_spec]
    branch for branch, with the seed [base] delivered on the unpinned
    branch.  On the pinned branch the witness delivers THE PIN ITSELF:
    the spec has just checked it against both predicates, and the
    stable comparison is reflexive — there is no [st_size] to patch,
    because the device's is asserted to be 0 already. -/
def fstat_chrdev_witness (p : Fs.path) (ok : List byte → Bool)
    (base : List byte) (statbuf : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if !(access_okb statbuf STAT_SIZE) then ret_outcome (errno_ret EFAULT) m
  else
    match read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) with
    | none => .unmodeled                   -- a partial [copy_to_user]
    | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
            if !(stat_buf_wf b0 && ok b0) then .unmodeled
            else .ok (mkEffect (BitVec.ofInt 64 0) [(statbuf, b0)] []) m []
        | none =>
            .ok (mkEffect (BitVec.ofInt 64 0) [(statbuf, base)] [])
               (with_statpin p base m) []

theorem fstat_chrdev_witness_ok (p : Fs.path) (ok : List byte → Bool)
    (base : List byte) (hwf : stat_buf_wf base = true) (hok : ok base = true)
    (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_chrdev_spec p ok statbuf i m
      (fstat_chrdev_witness p ok base statbuf i m) := by
  unfold fstat_chrdev_spec fstat_chrdev_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try try try try dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try try try dsimp only
  by_cases ha : (!(access_okb statbuf STAT_SIZE)) = true
  · simp only [ite_eq_left ha]
    simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  · simp only [ite_eq_right ha]
    generalize hw : read_bytes_map i.in_wmem statbuf (BitVec.ofInt 64 STAT_SIZE) = w at ⊢
    cases w with
    | none =>
      dsimp only
      exact unmodeled_intro i m
    | some w =>
      dsimp only
      generalize hp : statpin_lookup (m_statpins m) p = pin at ⊢
      cases pin with
      | some b0 =>
        dsimp only
        by_cases hb : (!(stat_buf_wf b0 && ok b0)) = true
        · simp only [ite_eq_left hb]
          exact unmodeled_intro i m
        · simp only [ite_eq_right hb]
          have hb' : (stat_buf_wf b0 && ok b0) = true := by simpa using hb
          simp only [Bool.and_eq_true] at hb'
          obtain ⟨hwf0, hok0⟩ := hb'
          refine bind_step (choose (fun bs : List byte =>
              stat_buf_wf bs = true ∧ ok bs = true ∧
              stat_stable_eqb bs b0 = true)) _ i m b0 m _ ?_ ?_
          · exact choose_ok _ _ i m
              ⟨hwf0, hok0, stat_stable_eqb_refl b0⟩
          · simp only [mkEffect, LinuxSem.LinuxProcessSem.pure]
      | none =>
        dsimp only
        refine bind_step (choose (fun bs : List byte =>
            stat_buf_wf bs = true ∧ ok bs = true)) _ i m base m _ ?_ ?_
        · exact choose_ok _ _ i m ⟨hwf, hok⟩
        · try try dsimp only
          refine bind_step (modifySpec (with_statpin p base)) _ i m ()
            (with_statpin p base m) _ (modify_ok _ i m) ?_
          try dsimp only
          simp only [mkEffect, LinuxSem.LinuxProcessSem.pure]

def fstat_devnull_witness (statbuf : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  fstat_chrdev_witness devnull_path stat_devnull_ok stat_devnull_witness_base
    statbuf i m

theorem fstat_devnull_witness_ok (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_devnull_spec statbuf i m (fstat_devnull_witness statbuf i m) :=
  fstat_chrdev_witness_ok devnull_path stat_devnull_ok stat_devnull_witness_base
    stat_devnull_witness_base_wf stat_devnull_witness_base_ok statbuf i m

def fstat_urandom_witness (statbuf : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  fstat_chrdev_witness urandom_path stat_urandom_ok stat_urandom_witness_base
    statbuf i m

theorem fstat_urandom_witness_ok (statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_urandom_spec statbuf i m (fstat_urandom_witness statbuf i m) :=
  fstat_chrdev_witness_ok urandom_path stat_urandom_ok stat_urandom_witness_base
    stat_urandom_witness_base_wf stat_urandom_witness_base_ok statbuf i m

/-- fstat (80) — -EBADF on a descriptor the process does not hold, a
    delivered [struct stat] on the four file kinds and on the two device
    kinds, and [Unmodeled] on the other four. -/
def fstat_witness (fd statbuf : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m   -- [vfs_fstat] resolves the fd first
  | some (.FdChannel _) => .unmodeled         -- struct stat: see [Stat.fstat_spec]
  | some (.FdFile p _) => fstat_file_witness p statbuf i m
  | some (.FdFileW p _) => fstat_file_witness p statbuf i m
  | some (.FdFileA p _) => fstat_file_witness p statbuf i m
  | some (.FdFileRW p _) => fstat_file_witness p statbuf i m
  | some .FdDir => .unmodeled
  | some (.FdSocket _) => .unmodeled
  | some (.FdPipe _ _) => .unmodeled
  | some (.FdDevNull _ _) => fstat_devnull_witness statbuf i m
  | some .FdUrandom => fstat_urandom_witness statbuf i m

theorem fstat_witness_ok (fd statbuf : word) (i : SyscallInput) (m : Model) :
    fstat_spec fd statbuf i m (fstat_witness fd statbuf i m) := by
  unfold fstat_spec fstat_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try try try try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = lk at ⊢
  cases lk with
  | none =>
    dsimp only
    simp only [err_ret, ret_only, ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]
  | some e =>
    try try try dsimp only
    cases e with
    | FdChannel n => dsimp only; exact unmodeled_intro i m
    | FdFile p sz => exact fstat_file_witness_ok p statbuf i m
    | FdFileW p sz => exact fstat_file_witness_ok p statbuf i m
    | FdFileA p sz => exact fstat_file_witness_ok p statbuf i m
    | FdFileRW p sz => exact fstat_file_witness_ok p statbuf i m
    | FdDir => dsimp only; exact unmodeled_intro i m
    | FdSocket s => dsimp only; exact unmodeled_intro i m
    | FdPipe a b => dsimp only; exact unmodeled_intro i m
    | FdDevNull a b => exact fstat_devnull_witness_ok statbuf i m
    | FdUrandom => exact fstat_urandom_witness_ok statbuf i m

theorem newfstatat_witness_ok (dirfd pathp flag : word) (i : SyscallInput)
    (m : Model) :
    newfstatat_spec dirfd pathp flag i m (newfstatat_witness dirfd pathp flag i m) := by
  unfold newfstatat_spec newfstatat_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try try try try dsimp only
  exact record_copyins_outcome (newfstatat_core_witness_ok dirfd pathp flag i m)

end LinuxSem.Checks.Witness.Fs.Stat
