/-
  * LinuxSem.Checks.Sys.Fs.Open — the openat (56), close (57), ftruncate (46) checkers, and their proofs

  Answers to Linux [fs/open.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  `Checks.Sys.Prelude` re-exports the model/state/monad stack (`BvBase`,
  `Fs`, `State`, `Monad`, `Specs`) and supplies [check_result],
  [check_ret_only], [check_ret_only_ok_iff], [check_ret_only_no_unmodeled],
  [errno_ret_in], [clear_copyins], [with_copyins], [check_copyins_after] and
  their lemmas; the checkers' own spec — `Sys/Fs/Open.lean`, where
  `open_result_spec`, `create_wronly`, the twelve `openat_*_spec` arms,
  `openat_spec`, `close_spec`, `ftruncate_spec`, `access_exists_spec`,
  `faccessat_body_spec`, `faccessat_spec` and `faccessat2_spec` live — is
  imported directly.  `Fs.ReadWrite` is not imported: nothing here cites
  anything from it except through `Sys.Fs.Open` itself (the specs
  already carry their own copies of `openat_errnos`,
  `modeled_truncate_gap` and `file_truncate`), so the import is dropped.

  A file-private definition is `private`: the eleven local checkers and the
  forty-odd local lemmas below are file-private.  Four branch-index
  eliminators are NOT stated as declarations: each of them exists only to
  keep a large branch tree from being elaborated twice, and the proofs split
  on the same guard with `by_cases` (for a `Bool`) or `cases` (for an
  `Option`/`cstr_result`) on BOTH sides at once, which is what the lemmas
  that do not need the eliminator do directly.

  SEVEN declarations below are PUBLIC and all of the same shape — "this
  checker leaves [m_vmmaps] alone", stated as
  `H : check_X … = .CheckOk m' evs → m_vmmaps m' = m_vmmaps m`: the
  `private` [check_ret_only_frame], [check_open_result_frame] and
  [check_access_exists_frame], and the PUBLIC
  [check_ftruncate_file_arm_frame], [check_open_devnull_frame],
  [check_open_urandom_frame], [check_faccessat_body_frame].  They exist for
  [Checks/VmMapsDisjoint.lean], which must frame four checkers whose
  accepting branch sits in a `private def` here: a private definition's
  equation lemmas are not nameable from another module, so that file
  cannot unfold the helper and the frame never closes.  The way in has to be
  a fact stated HERE, where the helper's body is visible — and a PUBLIC
  theorem rather than a `private` one, since `private` would put the fact
  out of reach for the same reason.  Stating a public fact ABOUT a private definition leaks
  nothing: only the fact travels, not the name.  Each is proved by the
  checker half of the `*_sound_ok` above it.

  A length test in a `bool` definition is `decide (NAME_MAX < p.length)`, a
  signed length test is `decide (len.toInt < 0)` — the test
  `ftruncate_spec` performs — and an effect literal is the anonymous
  constructor pattern `⟨ret, [], [], [], [], []⟩` over `SyscallEffect`.  The
  checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`, and the
  spec monad with `.ok` / `.unmodeled`.

  The proofs `cases` the effect's five lists and close the thirty-one dead
  shapes with `exact nomatch H` (see `Checks/Sys/Fs/File.lean`'s header for
  the same pattern).  A checker and its spec place the SAME tests in the
  SAME order, so each proof walks the two together with `by_cases` +
  `rw [ite_eq_left h] at H ⊢` (or `simp only [ite_eq_left h] at H ⊢` when the guard
  occurs on both sides), and `generalize` + `cases` on a shared scrutinee
  (`read_cstr`, `fs_lookup`, `tmp_name`).  Where the spec is a bare
  `err_ret e` and the checker a `check_ret_only eff (errno_ret e) m []`, the
  leaf is [check_ret_only_ok_iff]; where the spec is an `alt`, the branch is
  built with `alt_l`/`alt_r` and `bind_ok0`.

  TWO SMALL WIDENINGS, both local.  (1) The two `openat_resolved` lemmas and
  the two `openat_body_spec` lemmas are stated for a GENERAL effect rather
  than for `clear_copyins eff`: the caller only ever hands them
  `clear_copyins eff`, so the general statement implies the narrower one,
  and it saves a `clear_copyins (clear_copyins eff) = clear_copyins eff`
  rewrite at every call site.  (2) Lean has no or-patterns, so
  `check_ftruncate`'s shared writable-file arm is the
  [check_ftruncate_file_arm] helper called from the three file kinds, where
  one body would otherwise serve three kinds — the same term one unfolding
  further out (`Sys.Fs.Open.ftruncate_file_arm` makes the identical move).
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Open

namespace LinuxSem.Checks.Sys.Fs.Open

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Fs.File (lowest_fd z_ldiff)
open LinuxSem.Checks.Sys.Prelude

/- =========================================================================
   The allocated descriptor is out of the error-encoding window
   ========================================================================= -/

/-- [alloc_fd] never runs past its scan bound: the candidate grows by one
    per failed lookup and the fuel shrinks by one, so the answer is at
    most [cand + fuel].

    The bound is stated in `Nat` because that is the form Lean's bitvector
    arithmetic gives (`toNat` of a sum needs the modulus side condition in
    `Nat` either way), and [alloc_fd_le] — the only consumer — reads the
    same bound out of it. -/
theorem alloc_fd_aux_le (fds : List (word × FdEntry)) (cand : word) (f : Nat)
    (h : cand.toNat + f < 2 ^ 64) :
    (alloc_fd_aux fds cand f).toNat ≤ cand.toNat + f := by
  induction f generalizing cand with
  | zero => simp [alloc_fd_aux]
  | succ f ih =>
    rw [show alloc_fd_aux fds cand (f + 1) =
        (match fd_lookup fds cand with
         | none => cand
         | some _ => alloc_fd_aux fds (cand + 1) f) from rfl]
    split
    · omega
    · have h1 : cand.toNat + 1 < 2 ^ 64 := by omega
      have hsucc : (cand + 1).toNat = cand.toNat + 1 := by
        have hone : ((1 : word)).toNat = 1 := by decide
        rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt h1]
      have h2 : (cand + 1).toNat + f < 2 ^ 64 := by rw [hsucc]; omega
      have h3 := ih (cand + 1) h2
      rw [hsucc] at h3
      omega

/-- The advertised bound on a fresh descriptor: at most 4096, far below
    the error-encoding window (`two_pow_64 - 4096`). -/
theorem alloc_fd_le (fds : List (word × FdEntry)) : (alloc_fd fds).toNat ≤ 4096 := by
  unfold alloc_fd
  have h0 : (BitVec.ofInt 64 0 : word).toNat = 0 := by decide
  have h1 : (BitVec.ofInt 64 0 : word).toNat + 4096 < 2 ^ 64 := by
    rw [h0]
    decide
  simpa [h0] using alloc_fd_aux_le fds (BitVec.ofInt 64 0) 4096 h1

/-- An allocated fd never matches an injectable errno: it is at most
    4096, and every errno encodes to a value in the top 4096 words. -/
theorem alloc_fd_not_error_b (fds : List (word × FdEntry)) :
    addr_is_error_b (alloc_fd fds) = false := by
  have h := alloc_fd_le fds
  unfold addr_is_error_b
  rw [decide_eq_false_iff_not]
  unfold two_pow_64
  omega

/-- In particular an allocated fd never matches an injectable errno. -/
theorem errno_ret_in_alloc_fd (es : List Int) (fds : List (word × FdEntry))
    (Hok : errnos_ok es = true) : errno_ret_in es (alloc_fd fds) = false := by
  apply errno_ret_in_fd es (alloc_fd fds) Hok
  have h := alloc_fd_le fds
  have h2 : (4096 : Int) < 2147483648 := by decide
  show ((alloc_fd fds).toNat : Int) < 2147483648
  omega

/- =========================================================================
   Per-syscall checkers
   ========================================================================= -/

/-- The shape every call that hands back a FRESH DESCRIPTOR admits:
    either an error-encoded return drawn from [es], or the lowest free fd
    ([State.alloc_fd]) with the model [mk] builds from it.  [openat],
    [socket] and [accept4] differ only in [es] and in [mk]. -/
def check_new_fd_result (es : List Int) (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in es ret then .CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | some _ => .CheckReject
        | none => if bv_eqb ret (alloc_fd (m_fds m)) then .CheckOk (mk ret) []
                  else .CheckReject
  | _ => .CheckReject

/-- A fresh-descriptor result never declines: every shape it can see is
    either an injected errno, the allocated fd, or a rejection. -/
theorem check_new_fd_result_no_unmodeled (es : List Int) (eff : SyscallEffect)
    (m : Model) (mk : word → Model) :
    check_new_fd_result es eff m mk ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_new_fd_result] at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in es ret = true
    · rw [ite_eq_left he] at H
      exact nomatch H
    · rw [ite_eq_right he] at H
      split at H
      · exact nomatch H
      · split at H <;> exact nomatch H
  all_goals exact nomatch H

/-- [openat]'s instance: the effect must be a bare return (no writes, no
    zeros, no unmaps, no copies, no copy-ins), and the return is either
    an injectable errno or the lowest free fd, whose model [mk] builds. -/
def check_open_result (eff : SyscallEffect) (m : Model) (mk : word → Model)
    : check_result :=
  check_new_fd_result openat_errnos eff m mk

/-- The acceptor for [Open.create_wronly]: shared by the clobbering
    (O_TRUNC) and the exclusive (O_EXCL) write-create shapes, mirroring
    the one spec definition they share. -/
def check_create_wronly (p : Fs.path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p (BitVec.ofInt 64 0)))
                 (with_fs (fs_set (m_fs m) p []) m))

/-- The acceptor for [Open.open_append].  Two differences from the one
    above and no others: the fd kind is [State.FdFileA], and the file
    system change is [Open.append_open_fs], which leaves an existing
    file's bytes alone. -/
def check_open_append (p : Fs.path) (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p (BitVec.ofInt 64 0)))
                 (with_fs (append_open_fs (m_fs m) p) m))

/-- The acceptor for [Open.open_rdwr].  The fd kind is
    [State.FdFileRW]; the file-system change is whatever the arm
    computed, so it is a parameter here as it is there. -/
def check_open_rdwr (p : Fs.path) (fs' : Fs.Fs) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p (BitVec.ofInt 64 0)))
                 (with_fs fs' m))

/- ------------------------------------------------- the acceptor's proofs

   The two outcomes of [open_result_spec] are one shape each: an
   injectable errno with no state change, or the allocated fd with
   [mk]'s update.  The checker reads the same two off the effect, so the
   proofs walk the effect's five ledgers once and then split on the two
   tests.  `check_open_result_sound_ok` / `check_create_wronly_sound_ok` /
   `check_open_append_sound_ok` / `check_open_rdwr_sound_ok` are the four
   instances; each of the last three re-does the first's walk because its
   spec's success branch is one (or two) `seqSpec` deeper, and the model it
   builds differs. -/

/- The two success shapes of a fresh-descriptor spec, built once.  The same
   `bind_ok`/`bind_step` chain would otherwise appear inside each of the
   four soundness proofs, with only the model-builder changed; and Lean's
   elaborator will not accept `rfl` for the two `set_fs` / `set_fds` steps
   (`modify_ok` is the lemma that does). -/

private theorem open_alloc_step1 (i : SyscallInput) (m : Model)
    (mk : word → Model → Model)
    (hfr : fd_lookup (m_fds m) (alloc_fd (m_fds m)) = none) :
    bind (lowest_fd (m_fds m))
      (fun fd => seqSpec (modifySpec (mk fd)) (ret_only fd))
      i m (.ok (mkEffect (alloc_fd (m_fds m)) [] [])
        (mk (alloc_fd (m_fds m)) m) []) := by
  refine bind_ok0 _ _ i m (alloc_fd (m_fds m)) m
    (mkEffect (alloc_fd (m_fds m)) [] []) (mk (alloc_fd (m_fds m)) m) [] ?_ ?_
  · exact choose_ok
      (fun fd => fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m))
      _ i m ⟨hfr, rfl⟩
  · refine bind_ok (modifySpec (mk (alloc_fd (m_fds m))))
      (fun _ => ret_only (alloc_fd (m_fds m))) i m ()
      (mk (alloc_fd (m_fds m)) m) [] (mkEffect (alloc_fd (m_fds m)) [] [])
      (mk (alloc_fd (m_fds m)) m) [] ?_ ?_
    · exact modify_ok _ i m
    · exact pure_ok _ i _

private theorem open_alloc_step2 (i : SyscallInput) (m : Model)
    (fs' : Fs.Fs) (e : FdEntry)
    (hfr : fd_lookup (m_fds m) (alloc_fd (m_fds m)) = none) :
    bind (lowest_fd (m_fds m))
      (fun fd => seqSpec (modifySpec (with_fs fs'))
        (seqSpec (modifySpec (with_fds (fd_insert (m_fds m) fd e)))
          (ret_only fd)))
      i m (.ok (mkEffect (alloc_fd (m_fds m)) [] [])
        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e)
          (with_fs fs' m)) []) := by
  refine bind_ok0 _ _ i m (alloc_fd (m_fds m)) m
    (mkEffect (alloc_fd (m_fds m)) [] [])
    (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e) (with_fs fs' m)) [] ?_ ?_
  · exact choose_ok
      (fun fd => fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m))
      _ i m ⟨hfr, rfl⟩
  · refine bind_ok (modifySpec (with_fs fs'))
      (fun _ => seqSpec (modifySpec (with_fds (fd_insert (m_fds m)
        (alloc_fd (m_fds m)) e))) (ret_only (alloc_fd (m_fds m))))
      i m () (with_fs fs' m) [] _ _ [] ?_ ?_
    · exact modify_ok _ i m
    · refine bind_ok (modifySpec (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e)))
        (fun _ => ret_only (alloc_fd (m_fds m))) i (with_fs fs' m) ()
        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e) (with_fs fs' m)) []
        (mkEffect (alloc_fd (m_fds m)) [] []) _ [] ?_ ?_
      · exact modify_ok _ i _
      · exact pure_ok _ i _

private theorem check_open_result_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) (mk : word → Model → Model) (m' : Model) (evs : List event)
    (H : check_open_result eff m (fun fd => mk fd m) = .CheckOk m' evs) :
    open_result_spec m mk i m (.ok eff m' evs) := by
  generalize hP : (open_result_spec m mk i m (.ok eff m' evs)) = Q at *
  unfold check_open_result check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in openat_errnos ret = true
    · rw [ite_eq_left he] at H
      cases H
      obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true openat_errnos ret).mp he
      subst hret
      rw [← hP]
      simp only [open_result_spec]
      refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
      refine bind_ok0 (errno_from openat_errnos) (fun er' => err_ret er')
        i m er m (mkEffect (errno_ret er) [] []) m [] ?_ ?_
      · exact choose_ok (fun e => e ∈ openat_errnos) er i m hmem
      · exact pure_ok _ i m
    · rw [ite_eq_right he] at H
      cases hfr : fd_lookup (m_fds m) ret with
      | some x =>
        simp only [hfr] at H
        exact nomatch H
      | none =>
        simp only [hfr] at H
        by_cases heq : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_left heq] at H
          cases H
          have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq ret _).mp heq
          subst hret
          rw [← hP]
          simp only [open_result_spec]
          exact alt_r _ _ i m _
            (open_alloc_step1 i m (fun fd mm => mk fd mm) hfr)
        · rw [ite_eq_right heq] at H
          exact nomatch H
  all_goals exact nomatch H

/- -------------------------------------------------------------------------
   The `*_frame` lemmas — PUBLIC on purpose

   [Checks/VmMapsDisjoint.lean] must show that each checker leaves
   [m_vmmaps] alone.  Its `vm_frame` loop does that by unfolding the
   checker and casing the result hypothesis, and for five `check_*_frame`
   arms it cannot.  One of the five (`unlinkat`) is `Namei.lean`'s; the
   other four bottom out in a `private def` HERE —
   [check_ftruncate_file_arm] (reached from `check_ftruncate`),
   [check_faccessat_body] (`check_faccessat`, `check_faccessat2`) and
   [check_open_devnull] / [check_open_urandom] (under the public
   `check_openat_body`) — whose equation lemmas are not nameable from
   another module, so `simp only` cannot unfold it and the accepting shape
   never becomes visible.

   The fact those frames need is therefore stated HERE, next to the
   `*_sound_ok` that already unfolds the same helper (that is why the
   soundness proofs were never blocked), and each is a `theorem` rather
   than a `private` one: `private` would put it out of reach for exactly
   the reason the equation lemmas already are.  Stating a public fact
   ABOUT a private definition leaks nothing — the helper's name stays
   unexported; only "this checker leaves [m_vmmaps] alone" travels.

   Each proof is the checker side of its `*_sound_ok` above it, with the
   spec dropped: every accepting branch is either a [check_ret_only] or a
   [check_open_result] success, and both hand back a model whose `m_vm`
   field is the one they were given.
   ------------------------------------------------------------------------- -/

/-- An accepted [check_ret_only] hands back the model it was
    given, so it leaves [m_vmmaps] alone.  [check_ret_only_ok_iff] says
    the same thing; this is the one-projection corollary the frame lemmas
    below share. -/
private theorem check_ret_only_frame (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  rfl

/-- An accepted [check_open_result] builds its model with the
    caller's [mk], so it leaves [m_vmmaps] alone whenever [mk] does.  The
    two private /dev arms below are the instances that need it; the other
    arms that differ only in [mk] ([check_create_wronly],
    [check_open_append], [check_open_rdwr]) would follow the same way. -/
private theorem check_open_result_frame (eff : SyscallEffect) (m m' : Model)
    (mk : word → Model) (evs : List event)
    (hkeep : ∀ fd, m_vmmaps (mk fd) = m_vmmaps m)
    (H : check_open_result eff m mk = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_open_result at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_new_fd_result] at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in openat_errnos ret = true
    · rw [ite_eq_left he] at H
      cases H
      rfl
    · rw [ite_eq_right he] at H
      cases hfr : fd_lookup (m_fds m) ret with
      | some x =>
        simp only [hfr] at H
        exact nomatch H
      | none =>
        simp only [hfr] at H
        by_cases heq : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_left heq] at H
          cases H
          exact hkeep ret
        · rw [ite_eq_right heq] at H
          exact nomatch H
  all_goals exact nomatch H

private theorem check_create_wronly_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_create_wronly p eff m = .CheckOk m' evs) :
    create_wronly p m i m (.ok eff m' evs) := by
  generalize hP : (create_wronly p m i m (.ok eff m' evs)) = Q at *
  unfold check_create_wronly check_open_result check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in openat_errnos ret = true
    · rw [ite_eq_left he] at H
      cases H
      obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true openat_errnos ret).mp he
      subst hret
      rw [← hP]
      simp only [create_wronly]
      refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
      refine bind_ok0 (errno_from openat_errnos) (fun er' => err_ret er')
        i m er m (mkEffect (errno_ret er) [] []) m [] ?_ ?_
      · exact choose_ok (fun e => e ∈ openat_errnos) er i m hmem
      · exact pure_ok _ i m
    · rw [ite_eq_right he] at H
      cases hfr : fd_lookup (m_fds m) ret with
      | some x =>
        simp only [hfr] at H
        exact nomatch H
      | none =>
        simp only [hfr] at H
        by_cases heq : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_left heq] at H
          cases H
          have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq ret _).mp heq
          subst hret
          rw [← hP]
          simp only [create_wronly]
          exact alt_r _ _ i m _
            (open_alloc_step2 i m (fs_set (m_fs m) p [])
              (FdEntry.FdFileW p (BitVec.ofInt 64 0)) hfr)
        · rw [ite_eq_right heq] at H
          exact nomatch H
  all_goals exact nomatch H

private theorem check_open_append_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_open_append p eff m = .CheckOk m' evs) :
    open_append p m i m (.ok eff m' evs) := by
  generalize hP : (open_append p m i m (.ok eff m' evs)) = Q at *
  unfold check_open_append check_open_result check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in openat_errnos ret = true
    · rw [ite_eq_left he] at H
      cases H
      obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true openat_errnos ret).mp he
      subst hret
      rw [← hP]
      simp only [open_append]
      refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
      refine bind_ok0 (errno_from openat_errnos) (fun er' => err_ret er')
        i m er m (mkEffect (errno_ret er) [] []) m [] ?_ ?_
      · exact choose_ok (fun e => e ∈ openat_errnos) er i m hmem
      · exact pure_ok _ i m
    · rw [ite_eq_right he] at H
      cases hfr : fd_lookup (m_fds m) ret with
      | some x =>
        simp only [hfr] at H
        exact nomatch H
      | none =>
        simp only [hfr] at H
        by_cases heq : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_left heq] at H
          cases H
          have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq ret _).mp heq
          subst hret
          rw [← hP]
          simp only [open_append]
          exact alt_r _ _ i m _
            (open_alloc_step2 i m (append_open_fs (m_fs m) p)
              (FdEntry.FdFileA p (BitVec.ofInt 64 0)) hfr)
        · rw [ite_eq_right heq] at H
          exact nomatch H
  all_goals exact nomatch H

private theorem check_open_rdwr_sound_ok (i : SyscallInput) (p : Fs.path)
    (fs' : Fs.Fs) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_open_rdwr p fs' eff m = .CheckOk m' evs) :
    open_rdwr p fs' m i m (.ok eff m' evs) := by
  generalize hP : (open_rdwr p fs' m i m (.ok eff m' evs)) = Q at *
  unfold check_open_rdwr check_open_result check_new_fd_result at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in openat_errnos ret = true
    · rw [ite_eq_left he] at H
      cases H
      obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true openat_errnos ret).mp he
      subst hret
      rw [← hP]
      simp only [open_rdwr]
      refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
      refine bind_ok0 (errno_from openat_errnos) (fun er' => err_ret er')
        i m er m (mkEffect (errno_ret er) [] []) m [] ?_ ?_
      · exact choose_ok (fun e => e ∈ openat_errnos) er i m hmem
      · exact pure_ok _ i m
    · rw [ite_eq_right he] at H
      cases hfr : fd_lookup (m_fds m) ret with
      | some x =>
        simp only [hfr] at H
        exact nomatch H
      | none =>
        simp only [hfr] at H
        by_cases heq : bv_eqb ret (alloc_fd (m_fds m)) = true
        · rw [ite_eq_left heq] at H
          cases H
          have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq ret _).mp heq
          subst hret
          rw [← hP]
          simp only [open_rdwr]
          exact alt_r _ _ i m _
            (open_alloc_step2 i m fs' (FdEntry.FdFileRW p (BitVec.ofInt 64 0)) hfr)
        · rw [ite_eq_right heq] at H
          exact nomatch H
  all_goals exact nomatch H

/- =========================================================================
   openat (56): the arms
   ========================================================================= -/

def check_openat_read (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p then
      check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdDir) m)
  else
    match fs_lookup (m_fs m) p with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ => check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFile p (BitVec.ofInt 64 0))) m)

def check_openat_create (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then
    check_ret_only eff (errno_ret EISDIR) m []
  else check_create_wronly p eff m

def check_openat_append (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then
    check_ret_only eff (errno_ret EISDIR) m []
  else check_open_append p eff m

def check_openat_rdwr (creat trunc : Bool) (p : Fs.path)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EISDIR) m []
  else
    match fs_lookup (m_fs m) p with
    | none =>
        if creat then check_open_rdwr p (fs_set (m_fs m) p []) eff m
        else check_ret_only eff (errno_ret ENOENT) m []
    | some _ =>
        check_open_rdwr p (if trunc then fs_set (m_fs m) p [] else m_fs m) eff m

def check_openat_rdwr_excl (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else
    match fs_lookup (m_fs m) p with
    | some _ => check_ret_only eff (errno_ret EEXIST) m []
    | none => check_open_rdwr p (fs_set (m_fs m) p []) eff m

def check_openat_excl (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p || fs_under (m_fs m) p then check_ret_only eff (errno_ret EEXIST) m []
  else match fs_lookup (m_fs m) p with
       | some _ => check_ret_only eff (errno_ret EEXIST) m []
       | none => check_create_wronly p eff m

/-- The only openat arm that can DECLINE: [Open.openat_dir_spec] says
    why the two path guards it takes are free here and are not available
    to the other three. -/
def check_openat_dir (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if path_is_dirref p then
      check_open_result eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdDir) m)
  else if decide (NAME_MAX < p.length) then .CheckUnmodeled
  else if fs_under (m_fs m) p then .CheckUnmodeled
  else
    match fs_lookup (m_fs m) p with
    | none => check_ret_only eff (errno_ret ENOENT) m []
    | some _ => check_ret_only eff (errno_ret ENOTDIR) m []

/-- Mirrors [Open.openat_localtime_spec]: -ENOENT for the one absolute
    path the maintainer has declared absent from the image, fail-closed
    with O_CREAT or when the image holds the key or a key under it.
    That definition carries the assumption and its scope. -/
def check_openat_localtime (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) localtime_path with
  | some _ => .CheckUnmodeled
  | none =>
      if fs_under (m_fs m) localtime_path then .CheckUnmodeled
      else if flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT
      then .CheckUnmodeled
      else check_ret_only eff (errno_ret ENOENT) m []

/-- Mirrors [Open.open_devnull]: the shared success shape with the
    granted access mode on the entry. -/
private def check_open_devnull (rd wr : Bool) (eff : SyscallEffect)
    (m : Model) : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdDevNull rd wr)) m)

/-- Mirrors [Open.openat_devnull_spec], word for word; that definition
    carries the assumption and the kernel path. -/
def check_openat_devnull (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) devnull_path with
  | some _ => .CheckUnmodeled
  | none =>
      if fs_under (m_fs m) devnull_path then .CheckUnmodeled
      else
      let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
      if fl == 0 then check_open_devnull true false eff m
      else if fl == wr_create_flags then check_open_devnull false true eff m
      else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else if fl == O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
      else if fl == append_create_flags then check_open_devnull false true eff m
      else if rdwr_open_word fl then check_open_devnull true true eff m
      else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else .CheckUnmodeled

/-- Mirrors [Open.open_urandom]: the shared success shape with the
    read-only entry. -/
private def check_open_urandom (eff : SyscallEffect) (m : Model)
    : check_result :=
  check_open_result eff m
    (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdUrandom) m)

/-- Mirrors [Open.openat_urandom_spec], word for word; that definition
    carries the assumption, the kernel path and the declined write
    words. -/
def check_openat_urandom (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match fs_lookup (m_fs m) urandom_path with
  | some _ => .CheckUnmodeled
  | none =>
      if fs_under (m_fs m) urandom_path then .CheckUnmodeled
      else
      let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
      if fl == 0 then check_open_urandom eff m
      else if is_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else if fl == O_DIRECTORY then check_ret_only eff (errno_ret ENOTDIR) m []
      else if is_rdwr_excl_create fl then check_ret_only eff (errno_ret EEXIST) m []
      else .CheckUnmodeled

/-- Mirrors [Open.openat_tmp_spec]; that definition carries the premise,
    the three shapes and the reason each decline is a decline. -/
def check_openat_tmp (n p : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if decide (NAME_MAX < n.length) then .CheckUnmodeled
  else
  let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
  if fl == 0 then
    (if fs_under (m_fs m) p then .CheckUnmodeled
     else match fs_lookup (m_fs m) p with
          | none => .CheckUnmodeled
          | some _ => check_openat_read p eff m
          )
  else if fl == wr_create_flags then check_openat_create p eff m
  else .CheckUnmodeled

/-- Mirrors [Open.openat_sep_spec]: the separator-bearing pathnames
    that are answered, ahead of the decline. -/
def check_openat_sep (p : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_eqb p localtime_path then check_openat_localtime flags eff m
  else if path_eqb p devnull_path then check_openat_devnull flags eff m
  else if path_eqb p urandom_path then check_openat_urandom flags eff m
  else match tmp_name p with
       | some n => check_openat_tmp n p flags eff m
       | none => .CheckUnmodeled

/-- Mirrors [Open.openat_resolved_spec]'s leading guard: a pathname
    with a separator in it is declined before any flag is looked at,
    unless [check_openat_sep] answers it.  See that definition for why,
    and for why ".." is an arm instead. -/
def check_openat_resolved (p : Fs.path) (flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if path_has_slash p then check_openat_sep p flags eff m else
  let fl := z_ldiff (flags.toNat : Int) open_ignored_flags
  if fl == 0 then check_openat_read p eff m
  else if fl == wr_create_flags then check_openat_create p eff m
  else if is_excl_create fl then check_openat_excl p eff m
  else if fl == O_DIRECTORY then check_openat_dir p eff m
  else if fl == append_create_flags then check_openat_append p eff m
  else if rdwr_open_word fl then
    check_openat_rdwr (flag_set fl O_CREAT) (flag_set fl O_TRUNC) p eff m
  else if is_rdwr_excl_create fl then check_openat_rdwr_excl p eff m
  else .CheckUnmodeled

def check_openat_body (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
    | .CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
    | .CstrFault => check_ret_only eff (errno_ret EFAULT) m []
    | .CstrOk p =>
        if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
        else if !(bv_eqb dirfd AT_FDCWD32) then .CheckUnmodeled
        else check_openat_resolved p flags eff m

/-- The pathname copy-in is the prefix through the first NUL, the first
    faulting byte, or [PATH_MAX] — [State.cstr_access_len_aux].  That is
    the range the model records, not the one [getname()] loads:
    [strncpy_from_user] reads a word at a time and so runs to the end of
    the word holding the NUL, up to 7 bytes further, without moving the
    errno or the return (lib/strncpy_from_user.c, [do_strncpy_from_user];
    byte-identical v6.10 through v6.16 — the FILE is not, so the window
    belongs to the function).  The open body performs no
    later copy-in, so clear the prefix while checking the result and
    require the complete claimed list to equal that one range. -/
def check_openat (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(modeled_open_flags flags) then .CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff
      (check_openat_body i dirfd pathp flags (clear_copyins eff) m)

private def openat_nul_mem (a : word) : Option byte :=
  if bv_eqb a 0x2000 then some 102
  else if bv_eqb a 0x2001 then some 0
  else none

/-- The copy-in includes the NUL: two bytes for a one-byte name. -/
theorem openat_copyin_includes_the_nul :
    cstr_access_len_aux openat_nul_mem (0x2000 : word) path_max = 2 := by
  decide

/- --------------------------------------------------------- soundness -/

/-- A checker leaf whose spec reduced to a bare [err_ret]: the return is
    the effect's, and nothing changed. -/
private theorem check_ret_only_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (r : word) (m m' : Model) (evs : List event)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    ret_only r i m (.ok eff m' evs) := by
  obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  exact pure_ok _ i _

/-- Eliminate only the branch index.  The caller captures its aligned spec
    and checker expressions once in [P], so elaboration never duplicates
    the large openat branch trees in an eliminator's arguments and
    conclusion.

    These three eliminators are kept as declarations, but the proofs below
    do not cite them: each guard is split with `by_cases`/`cases` on BOTH
    sides at once instead.  See the header. -/
private theorem refine_if (b : Bool) (P : Bool → Prop) : P true → P false → P b := by
  intro ht hf
  cases b
  · exact hf
  · exact ht

private theorem refine_option {X : Type} (o : Option X) (P : Option X → Prop) :
    (∀ x, P (some x)) → P none → P o := by
  intro hsome hnone
  cases o with
  | none => exact hnone
  | some x => exact hsome x

private theorem refine_cstr (r : cstr_result) (P : cstr_result → Prop) :
    (∀ p, P (.CstrOk p)) → P .CstrTooLong → P .CstrFault → P r := by
  intro hok htoo hfault
  cases r with
  | CstrOk p => exact hok p
  | CstrTooLong => exact htoo
  | CstrFault => exact hfault

theorem check_openat_read_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_read p eff m = .CheckOk m' evs) :
    openat_read_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_read at H
  unfold openat_read_spec
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_open_result_sound_ok i eff m _ m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | none => exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H
    | some data => exact check_open_result_sound_ok i eff m _ m' evs H

theorem check_openat_create_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_create p eff m = .CheckOk m' evs) :
    openat_create_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_create at H
  unfold openat_create_spec
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    exact check_create_wronly_sound_ok i p eff m m' evs H

theorem check_openat_excl_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_excl p eff m = .CheckOk m' evs) :
    openat_excl_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_excl at H
  unfold openat_excl_spec
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data => exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
    | none => exact check_create_wronly_sound_ok i p eff m m' evs H

theorem check_openat_dir_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_dir p eff m = .CheckOk m' evs) :
    openat_dir_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_dir at H
  unfold openat_dir_spec
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_open_result_sound_ok i eff m _ m' evs H
  · rw [ite_eq_right hd] at H ⊢
    by_cases hnm : decide (NAME_MAX < p.length) = true
    · rw [ite_eq_left hnm] at H
      exact nomatch H
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        exact nomatch H
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H
        | some data => exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs H

theorem check_openat_append_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_append p eff m = .CheckOk m' evs) :
    openat_append_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_append at H
  unfold openat_append_spec
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    exact check_open_append_sound_ok i p eff m m' evs H

theorem check_openat_rdwr_sound_ok (i : SyscallInput) (creat trunc : Bool)
    (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_rdwr creat trunc p eff m = .CheckOk m' evs) :
    openat_rdwr_spec creat trunc p m i m (.ok eff m' evs) := by
  unfold check_openat_rdwr at H
  unfold openat_rdwr_spec
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data =>
      by_cases ht : trunc = true
      · rw [ite_eq_left ht] at H ⊢
        exact check_open_rdwr_sound_ok i p _ eff m m' evs H
      · rw [ite_eq_right ht] at H ⊢
        exact check_open_rdwr_sound_ok i p _ eff m m' evs H
    | none =>
      by_cases hc : creat = true
      · rw [ite_eq_left hc] at H ⊢
        exact check_open_rdwr_sound_ok i p _ eff m m' evs H
      · rw [ite_eq_right hc] at H ⊢
        exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H

theorem check_openat_rdwr_excl_sound_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_rdwr_excl p eff m = .CheckOk m' evs) :
    openat_rdwr_excl_spec p m i m (.ok eff m' evs) := by
  unfold check_openat_rdwr_excl at H
  unfold openat_rdwr_excl_spec
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data => exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
    | none => exact check_open_rdwr_sound_ok i p _ eff m m' evs H

theorem check_openat_localtime_sound_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_localtime flags eff m = .CheckOk m' evs) :
    openat_localtime_spec flags m i m (.ok eff m' evs) := by
  unfold check_openat_localtime at H
  unfold openat_localtime_spec
  generalize hfs : fs_lookup (m_fs m) localtime_path = lk at H ⊢
  cases lk with
  | some data => exact nomatch H
  | none =>
    dsimp only at H ⊢
    by_cases hun : fs_under (m_fs m) localtime_path = true
    · rw [ite_eq_left hun] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
      · rw [ite_eq_left hcr] at H
        exact nomatch H
      · rw [ite_eq_right hcr] at H ⊢
        exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H

private theorem check_open_devnull_sound_ok (i : SyscallInput) (rd wr : Bool)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_open_devnull rd wr eff m = .CheckOk m' evs) :
    open_devnull m rd wr i m (.ok eff m' evs) := by
  unfold check_open_devnull at H
  unfold open_devnull
  exact check_open_result_sound_ok i eff m _ m' evs H

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the /dev/null arm inserts a
    descriptor and touches nothing else, so the ledger it hands back is the
    one it was given.  Public because the helper it is about is `private`. -/
theorem check_open_devnull_frame (rd wr : Bool) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_open_devnull rd wr eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_open_devnull at H
  exact check_open_result_frame eff m m'
    (fun fd => with_fds (fd_insert (m_fds m) fd (FdEntry.FdDevNull rd wr)) m)
    evs (fun _ => rfl) H

theorem check_openat_devnull_sound_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_devnull flags eff m = .CheckOk m' evs) :
    openat_devnull_spec flags m i m (.ok eff m' evs) := by
  unfold check_openat_devnull at H
  unfold openat_devnull_spec
  generalize hfs : fs_lookup (m_fs m) devnull_path = lk at H ⊢
  cases lk with
  | some data => exact nomatch H
  | none =>
    by_cases hun : fs_under (m_fs m) devnull_path = true
    · rw [ite_eq_left hun] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H ⊢
        exact check_open_devnull_sound_ok i true false eff m m' evs H
      · rw [ite_eq_right h0] at H ⊢
        by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
        · rw [ite_eq_left hw] at H ⊢
          exact check_open_devnull_sound_ok i false true eff m m' evs H
        · rw [ite_eq_right hw] at H ⊢
          by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
          · rw [ite_eq_left hx] at H ⊢
            exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
          · rw [ite_eq_right hx] at H ⊢
            by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
            · rw [ite_eq_left hdir] at H ⊢
              exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs H
            · rw [ite_eq_right hdir] at H ⊢
              by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
              · rw [ite_eq_left hap] at H ⊢
                exact check_open_devnull_sound_ok i false true eff m m' evs H
              · rw [ite_eq_right hap] at H ⊢
                by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrw] at H ⊢
                  exact check_open_devnull_sound_ok i true true eff m m' evs H
                · rw [ite_eq_right hrw] at H ⊢
                  by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                  · rw [ite_eq_left hrx] at H ⊢
                    exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
                  · rw [ite_eq_right hrx] at H ⊢
                    exact nomatch H

private theorem check_open_urandom_sound_ok (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_open_urandom eff m = .CheckOk m' evs) :
    open_urandom m i m (.ok eff m' evs) := by
  unfold check_open_urandom at H
  unfold open_urandom
  exact check_open_result_sound_ok i eff m _ m' evs H

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the /dev/urandom arm
    inserts a descriptor and touches nothing else, so the ledger it hands
    back is the one it was given.  Public because the helper it is about is
    `private`. -/
theorem check_open_urandom_frame (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_open_urandom eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_open_urandom at H
  exact check_open_result_frame eff m m'
    (fun fd => with_fds (fd_insert (m_fds m) fd FdEntry.FdUrandom) m)
    evs (fun _ => rfl) H

theorem check_openat_urandom_sound_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_urandom flags eff m = .CheckOk m' evs) :
    openat_urandom_spec flags m i m (.ok eff m' evs) := by
  unfold check_openat_urandom at H
  unfold openat_urandom_spec
  generalize hfs : fs_lookup (m_fs m) urandom_path = lk at H ⊢
  cases lk with
  | some data => exact nomatch H
  | none =>
    by_cases hun : fs_under (m_fs m) urandom_path = true
    · rw [ite_eq_left hun] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H ⊢
        exact check_open_urandom_sound_ok i eff m m' evs H
      · rw [ite_eq_right h0] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H ⊢
          exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_ret_only_sound_ok i eff (errno_ret ENOTDIR) m m' evs H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
            · rw [ite_eq_left hrx] at H ⊢
              exact check_ret_only_sound_ok i eff (errno_ret EEXIST) m m' evs H
            · rw [ite_eq_right hrx] at H ⊢
              exact nomatch H

theorem check_openat_tmp_sound_ok (i : SyscallInput) (n p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_tmp n p flags eff m = .CheckOk m' evs) :
    openat_tmp_spec n p flags m i m (.ok eff m' evs) := by
  unfold check_openat_tmp at H
  unfold openat_tmp_spec
  by_cases hnm : decide (NAME_MAX < n.length) = true
  · rw [ite_eq_left hnm] at H
    exact nomatch H
  · rw [ite_eq_right hnm] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        exact nomatch H
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact nomatch H
        | some data => exact check_openat_read_sound_ok i p eff m m' evs H
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H ⊢
        exact check_openat_create_sound_ok i p eff m m' evs H
      · rw [ite_eq_right hw] at H ⊢
        exact nomatch H

theorem check_openat_sep_sound_ok (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_sep p flags eff m = .CheckOk m' evs) :
    openat_sep_spec p flags m i m (.ok eff m' evs) := by
  unfold check_openat_sep at H
  unfold openat_sep_spec
  by_cases hl : path_eqb p localtime_path = true
  · rw [ite_eq_left hl] at H ⊢
    exact check_openat_localtime_sound_ok i flags eff m m' evs H
  · rw [ite_eq_right hl] at H ⊢
    by_cases hd : path_eqb p devnull_path = true
    · rw [ite_eq_left hd] at H ⊢
      exact check_openat_devnull_sound_ok i flags eff m m' evs H
    · rw [ite_eq_right hd] at H ⊢
      by_cases hu : path_eqb p urandom_path = true
      · rw [ite_eq_left hu] at H ⊢
        exact check_openat_urandom_sound_ok i flags eff m m' evs H
      · rw [ite_eq_right hu] at H ⊢
        generalize htn : tmp_name p = tn at H ⊢
        cases tn with
        | none => exact nomatch H
        | some n => exact check_openat_tmp_sound_ok i n p flags eff m m' evs H

theorem check_openat_resolved_sound_ok (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_resolved p flags eff m = .CheckOk m' evs) :
    openat_resolved_spec p flags m i m (.ok eff m' evs) := by
  unfold check_openat_resolved at H
  unfold openat_resolved_spec
  by_cases hsl : path_has_slash p = true
  · rw [ite_eq_left hsl] at H ⊢
    exact check_openat_sep_sound_ok i p flags eff m m' evs H
  · rw [ite_eq_right hsl] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      exact check_openat_read_sound_ok i p eff m m' evs H
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H ⊢
        exact check_openat_create_sound_ok i p eff m m' evs H
      · rw [ite_eq_right hw] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H ⊢
          exact check_openat_excl_sound_ok i p eff m m' evs H
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_openat_dir_sound_ok i p eff m m' evs H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
            · rw [ite_eq_left hap] at H ⊢
              exact check_openat_append_sound_ok i p eff m m' evs H
            · rw [ite_eq_right hap] at H ⊢
              by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
              · rw [ite_eq_left hrw] at H ⊢
                exact check_openat_rdwr_sound_ok i _ _ p eff m m' evs H
              · rw [ite_eq_right hrw] at H ⊢
                by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrx] at H ⊢
                  exact check_openat_rdwr_excl_sound_ok i p eff m m' evs H
                · rw [ite_eq_right hrx] at H ⊢
                  exact nomatch H

theorem check_openat_body_spec_sound_ok (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat_body i dirfd pathp flags (clear_copyins eff) m = .CheckOk m' evs) :
    openat_body_spec i m dirfd pathp flags i m (.ok (clear_copyins eff) m' evs) := by
  unfold check_openat_body at H
  unfold openat_body_spec
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact check_ret_only_sound_ok i (clear_copyins eff) (errno_ret ENAMETOOLONG) m m' evs H
  | CstrFault =>
    exact check_ret_only_sound_ok i (clear_copyins eff) (errno_ret EFAULT) m m' evs H
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      exact check_ret_only_sound_ok i (clear_copyins eff) (errno_ret ENOENT) m m' evs H
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        exact check_openat_resolved_sound_ok i p flags (clear_copyins eff) m m' evs H

theorem check_openat_body_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hfl : (!(modeled_open_flags flags)) = false)
    (H : check_openat_body i dirfd pathp flags (clear_copyins eff) m = .CheckOk m' evs) :
    openat_core_spec dirfd pathp flags i m (.ok (clear_copyins eff) m' evs) := by
  unfold openat_core_spec
  apply bind_ok0
  · exact input_ok i m
  · apply bind_ok0
    · exact getModel_ok i m
    · by_cases hc : (!(modeled_open_flags flags)) = true
      · rw [ite_eq_left hc]
        rw [Hfl] at hc
        exact nomatch hc
      · rw [ite_eq_right hc]
        exact check_openat_body_spec_sound_ok i dirfd pathp flags eff m m' evs H

theorem check_openat_sound_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_openat i dirfd pathp flags eff m = .CheckOk m' evs) :
    openat_spec dirfd pathp flags i m (.ok eff m' evs) := by
  unfold check_openat at H
  by_cases hfl : (!(modeled_open_flags flags)) = true
  · rw [ite_eq_left hfl] at H
    exact nomatch H
  · rw [ite_eq_right hfl] at H
    dsimp only at H
    obtain ⟨hreads, hchecked⟩ := (check_copyins_after_ok_iff _ _ _ _ _).mp H
    have hcore := check_openat_body_sound_ok i dirfd pathp flags eff m m' evs
      (by simpa using hfl) hchecked
    unfold openat_spec
    apply bind_ok0
    · exact input_ok i m
    · exact record_copyins_clear_ok _ _ i m eff m' evs hreads hcore

/- -------------------------------------------------- unmodeled-soundness

   Every arm but one never declines; the exception, [check_openat_dir],
   gets a soundness lemma of its own below rather than an [exfalso]. -/

private theorem check_open_result_no_unmodeled (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_open_result eff m mk ≠ .CheckUnmodeled :=
  check_new_fd_result_no_unmodeled openat_errnos eff m mk

theorem check_openat_read_no_unmodeled (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_openat_read p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_read at H
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact check_open_result_no_unmodeled eff m _ H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | none => exact check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [] H
    | some data => exact check_open_result_no_unmodeled eff m _ H

theorem check_openat_create_no_unmodeled (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_openat_create p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_create at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [] H
  · rw [ite_eq_right hd] at H
    exact check_open_result_no_unmodeled eff m _ H

theorem check_openat_excl_no_unmodeled (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_openat_excl p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_excl at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [] H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data => exact check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [] H
    | none => exact check_open_result_no_unmodeled eff m _ H

/-- Unlike its three neighbours this checker CAN decline, so the
    dispatcher's unmodeled-soundness proof gets a lemma here rather than
    an [exfalso]. -/
theorem check_openat_dir_sound_unmodeled (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m : Model)
    (H : check_openat_dir p eff m = .CheckUnmodeled) :
    openat_dir_spec p m i m .unmodeled := by
  unfold check_openat_dir at H
  unfold openat_dir_spec
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact absurd H (check_open_result_no_unmodeled eff m _)
  · rw [ite_eq_right hd] at H ⊢
    by_cases hnm : decide (NAME_MAX < p.length) = true
    · rw [ite_eq_left hnm] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
        | some data =>
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m [])

theorem check_openat_append_no_unmodeled (p : Fs.path) (eff : SyscallEffect)
    (m : Model) : check_openat_append p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_append at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [] H
  · rw [ite_eq_right hd] at H
    exact check_open_result_no_unmodeled eff m _ H

private theorem check_open_rdwr_no_unmodeled (p : Fs.path) (fs' : Fs.Fs)
    (eff : SyscallEffect) (m : Model) : check_open_rdwr p fs' eff m ≠ .CheckUnmodeled := by
  intro H
  exact check_open_result_no_unmodeled eff m _ H

theorem check_openat_rdwr_no_unmodeled (creat trunc : Bool) (p : Fs.path)
    (eff : SyscallEffect) (m : Model) :
    check_openat_rdwr creat trunc p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_rdwr at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact check_ret_only_no_unmodeled eff (errno_ret EISDIR) m [] H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data =>
      by_cases ht : trunc = true
      · rw [ite_eq_left ht] at H
        exact check_open_rdwr_no_unmodeled p _ eff m H
      · rw [ite_eq_right ht] at H
        exact check_open_rdwr_no_unmodeled p _ eff m H
    | none =>
      by_cases hc : creat = true
      · rw [ite_eq_left hc] at H
        exact check_open_rdwr_no_unmodeled p _ eff m H
      · rw [ite_eq_right hc] at H
        exact check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [] H

theorem check_openat_rdwr_excl_no_unmodeled (p : Fs.path)
    (eff : SyscallEffect) (m : Model) :
    check_openat_rdwr_excl p eff m ≠ .CheckUnmodeled := by
  intro H
  unfold check_openat_rdwr_excl at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [] H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data => exact check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [] H
    | none => exact check_open_rdwr_no_unmodeled p _ eff m H

theorem check_openat_localtime_sound_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_localtime flags eff m = .CheckUnmodeled) :
    openat_localtime_spec flags m i m .unmodeled := by
  unfold check_openat_localtime at H
  unfold openat_localtime_spec
  generalize hfs : fs_lookup (m_fs m) localtime_path = lk at H ⊢
  cases lk with
  | some data => exact unmodeled_intro i m
  | none =>
    by_cases hun : fs_under (m_fs m) localtime_path = true
    · rw [ite_eq_left hun] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hun] at H ⊢
      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
      · rw [ite_eq_left hcr] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hcr] at H
        exact absurd H
          (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])

theorem check_openat_devnull_sound_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_devnull flags eff m = .CheckUnmodeled) :
    openat_devnull_spec flags m i m .unmodeled := by
  unfold check_openat_devnull at H
  unfold openat_devnull_spec
  generalize hfs : fs_lookup (m_fs m) devnull_path = lk at H ⊢
  cases lk with
  | some data => exact unmodeled_intro i m
  | none =>
    by_cases hun : fs_under (m_fs m) devnull_path = true
    · rw [ite_eq_left hun] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H
        exact absurd H (check_open_result_no_unmodeled eff m _)
      · rw [ite_eq_right h0] at H ⊢
        by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
        · rw [ite_eq_left hw] at H
          exact absurd H (check_open_result_no_unmodeled eff m _)
        · rw [ite_eq_right hw] at H ⊢
          by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
          · rw [ite_eq_left hx] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [])
          · rw [ite_eq_right hx] at H ⊢
            by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
            · rw [ite_eq_left hdir] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m [])
            · rw [ite_eq_right hdir] at H ⊢
              by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
              · rw [ite_eq_left hap] at H
                exact absurd H (check_open_result_no_unmodeled eff m _)
              · rw [ite_eq_right hap] at H ⊢
                by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrw] at H
                  exact absurd H (check_open_result_no_unmodeled eff m _)
                · rw [ite_eq_right hrw] at H ⊢
                  by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                  · rw [ite_eq_left hrx] at H
                    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [])
                  · rw [ite_eq_right hrx] at H ⊢
                    exact unmodeled_intro i m

theorem check_openat_urandom_sound_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_urandom flags eff m = .CheckUnmodeled) :
    openat_urandom_spec flags m i m .unmodeled := by
  unfold check_openat_urandom at H
  unfold openat_urandom_spec
  generalize hfs : fs_lookup (m_fs m) urandom_path = lk at H ⊢
  cases lk with
  | some data => exact unmodeled_intro i m
  | none =>
    by_cases hun : fs_under (m_fs m) urandom_path = true
    · rw [ite_eq_left hun] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H
        exact absurd H (check_open_result_no_unmodeled eff m _)
      · rw [ite_eq_right h0] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [])
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTDIR) m [])
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
            · rw [ite_eq_left hrx] at H
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EEXIST) m [])
            · rw [ite_eq_right hrx] at H ⊢
              exact unmodeled_intro i m

theorem check_openat_tmp_sound_unmodeled (i : SyscallInput) (n p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_tmp n p flags eff m = .CheckUnmodeled) :
    openat_tmp_spec n p flags m i m .unmodeled := by
  unfold check_openat_tmp at H
  unfold openat_tmp_spec
  by_cases hnm : decide (NAME_MAX < n.length) = true
  · rw [ite_eq_left hnm] at H ⊢
    exact unmodeled_intro i m
  · rw [ite_eq_right hnm] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact unmodeled_intro i m
        | some data => exact absurd H (check_openat_read_no_unmodeled p eff m)
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_openat_create_no_unmodeled p eff m)
      · rw [ite_eq_right hw] at H ⊢
        exact unmodeled_intro i m

theorem check_openat_sep_sound_unmodeled (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_sep p flags eff m = .CheckUnmodeled) :
    openat_sep_spec p flags m i m .unmodeled := by
  unfold check_openat_sep at H
  unfold openat_sep_spec
  by_cases hl : path_eqb p localtime_path = true
  · rw [ite_eq_left hl] at H ⊢
    exact check_openat_localtime_sound_unmodeled i flags eff m H
  · rw [ite_eq_right hl] at H ⊢
    by_cases hd : path_eqb p devnull_path = true
    · rw [ite_eq_left hd] at H ⊢
      exact check_openat_devnull_sound_unmodeled i flags eff m H
    · rw [ite_eq_right hd] at H ⊢
      by_cases hu : path_eqb p urandom_path = true
      · rw [ite_eq_left hu] at H ⊢
        exact check_openat_urandom_sound_unmodeled i flags eff m H
      · rw [ite_eq_right hu] at H ⊢
        generalize htn : tmp_name p = tn at H ⊢
        cases tn with
        | none => exact unmodeled_intro i m
        | some n => exact check_openat_tmp_sound_unmodeled i n p flags eff m H

theorem check_openat_resolved_sound_unmodeled (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_resolved p flags eff m = .CheckUnmodeled) :
    openat_resolved_spec p flags m i m .unmodeled := by
  unfold check_openat_resolved at H
  unfold openat_resolved_spec
  by_cases hsl : path_has_slash p = true
  · rw [ite_eq_left hsl] at H ⊢
    exact check_openat_sep_sound_unmodeled i p flags eff m H
  · rw [ite_eq_right hsl] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H
      exact absurd H (check_openat_read_no_unmodeled p eff m)
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (check_openat_create_no_unmodeled p eff m)
      · rw [ite_eq_right hw] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H
          exact absurd H (check_openat_excl_no_unmodeled p eff m)
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_openat_dir_sound_unmodeled i p eff m H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
            · rw [ite_eq_left hap] at H
              exact absurd H (check_openat_append_no_unmodeled p eff m)
            · rw [ite_eq_right hap] at H ⊢
              by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
              · rw [ite_eq_left hrw] at H
                exact absurd H (check_openat_rdwr_no_unmodeled _ _ p eff m)
              · rw [ite_eq_right hrw] at H ⊢
                by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrx] at H
                  exact absurd H (check_openat_rdwr_excl_no_unmodeled p eff m)
                · rw [ite_eq_right hrx] at H ⊢
                  exact unmodeled_intro i m

theorem check_openat_body_spec_sound_unmodeled (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m : Model)
    (H : check_openat_body i dirfd pathp flags eff m = .CheckUnmodeled) :
    openat_body_spec i m dirfd pathp flags i m .unmodeled := by
  unfold check_openat_body at H
  unfold openat_body_spec
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENAMETOOLONG) m [])
  | CstrFault =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hd] at H ⊢
        exact check_openat_resolved_sound_unmodeled i p flags eff m H

theorem check_openat_body_sound_unmodeled (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m : Model)
    (Hfl : ¬((!(modeled_open_flags flags)) = true))
    (H : check_openat_body i dirfd pathp flags eff m = .CheckUnmodeled) :
    openat_core_spec dirfd pathp flags i m .unmodeled := by
  unfold openat_core_spec
  apply bind_unmodeled2
  · exact input_ok i m
  · apply bind_unmodeled2
    · exact getModel_ok i m
    · by_cases hc : (!(modeled_open_flags flags)) = true
      · rw [ite_eq_left hc]
        exact absurd hc Hfl
      · rw [ite_eq_right hc]
        exact check_openat_body_spec_sound_unmodeled i dirfd pathp flags eff m H

theorem check_openat_sound_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_openat i dirfd pathp flags eff m = .CheckUnmodeled) :
    openat_spec dirfd pathp flags i m .unmodeled := by
  unfold check_openat at H
  by_cases hfl : (!(modeled_open_flags flags)) = true
  · rw [ite_eq_left hfl] at H
    unfold openat_spec
    apply bind_unmodeled2
    · exact input_ok i m
    · apply record_copyins_unmodeled
      unfold openat_core_spec
      apply bind_unmodeled2
      · exact input_ok i m
      · apply bind_unmodeled2
        · exact getModel_ok i m
        · rw [ite_eq_left hfl]
          exact unmodeled_intro i _
  · rw [ite_eq_right hfl] at H
    dsimp only at H
    have hbody := check_copyins_after_unmodeled _ _ _ H
    unfold openat_spec
    apply bind_unmodeled2
    · exact input_ok i m
    · apply record_copyins_unmodeled
      exact check_openat_body_sound_unmodeled i dirfd pathp flags (clear_copyins eff) m
        hfl hbody

/- -------------------------------------------------------- completeness -/

/-- The branch-index predicate: the spec's outcome forces the checker's
    answer and an empty copy-in ledger.

    This is the predicate the `refine_if`/`refine_option`/`refine_cstr`
    eliminators take, whose whole purpose is to keep a large branch tree
    from being elaborated twice.  Each guard is split with
    `by_cases`/`cases` on BOTH sides at once instead, so nothing below
    cites it; it is kept as part of the file's vocabulary. -/
private def completes_ok (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (spec : SysSpec SyscallEffect) (check : check_result) : Prop :=
  spec i m (.ok eff m' evs) → check = .CheckOk m' evs ∧ eff.eff_copyins = []

/-- Invert one `seqSpec (modifySpec f) (ret_only r)` step.  `inv_ok`
    deliberately stops at constructor injectivities, so the two shapes the
    acceptors build are stated once here. -/
private theorem seqSpec_modify_ret_only_inv (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (modifySpec f) (ret_only r) i m (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m2, evs1, evs2, hm, hr, hevs⟩ := H
  cases hm
  cases hr
  simp only [List.nil_append] at hevs
  exact ⟨rfl, rfl, hevs⟩

/-- The same, for the two-modify chain the three write-create
    acceptors build (`set_fs` then `set_fds`). -/
private theorem seqSpec_modify2_ret_only_inv (f g : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (modifySpec f) (seqSpec (modifySpec g) (ret_only r)) i m
      (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = g (f m) ∧ evs = [] := by
  unfold seqSpec at H
  obtain ⟨u, m2, evs1, evs2, hm, hr, hevs⟩ := H
  unfold modifySpec LinuxSem.LinuxProcessSem.modify at hm
  cases hm
  simp only [List.nil_append] at hevs
  subst hevs
  exact seqSpec_modify_ret_only_inv g r i (f m) eff m' _ hr

private theorem check_ret_only_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (r : word) (m m' : Model) (evs : List event)
    (H : ret_only r i m (.ok eff m' evs)) :
    check_ret_only eff r m [] = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  cases H
  exact ⟨by simp [check_ret_only, bv_eqb_refl], rfl⟩

private theorem check_open_result_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m : Model) (mk : word → Model → Model) (m' : Model) (evs : List event)
    (H : open_result_spec m mk i m (.ok eff m' evs)) :
    check_open_result eff m (fun fd => mk fd m) = .CheckOk m' evs
      ∧ eff.eff_copyins = [] := by
  unfold open_result_spec at H
  rcases H with H1 | H2
  · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
    obtain ⟨e0, hin, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, he2] at her
    rw [he3] at hevs
    cases her
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_result, check_new_fd_result]
    rw [ite_eq_left (errno_ret_in_intro openat_errnos _ hin)]
  · obtain ⟨fd, m1, evs1, evs2, hlow, hk, hevs⟩ := H2
    obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := hlow
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, hx, he2] at hk
    rw [hx] at hfree
    rw [he3] at hevs
    obtain ⟨heff, hm', hevs2⟩ :=
      seqSpec_modify_ret_only_inv (mk (alloc_fd (m_fds m))) (alloc_fd (m_fds m))
        i m eff m' evs2 hk
    subst heff
    subst hm'
    subst hevs2
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_result, check_new_fd_result]
    rw [errno_ret_in_alloc_fd openat_errnos (m_fds m) (by decide)]
    simp only [Bool.false_eq_true, ite_false]
    rw [hfree]
    dsimp only
    rw [ite_eq_left (bv_eqb_refl _)]

private theorem check_create_wronly_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : create_wronly p m i m (.ok eff m' evs)) :
    check_create_wronly p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold create_wronly at H
  rcases H with H1 | H2
  · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
    obtain ⟨e0, hin, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, he2] at her
    rw [he3] at hevs
    cases her
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_create_wronly, check_open_result, check_new_fd_result]
    rw [ite_eq_left (errno_ret_in_intro openat_errnos _ hin)]
  · obtain ⟨fd, m1, evs1, evs2, hlow, hk, hevs⟩ := H2
    obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := hlow
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, hx, he2] at hk
    rw [hx] at hfree
    rw [he3] at hevs
    obtain ⟨heff, hm', hevs2⟩ :=
      seqSpec_modify2_ret_only_inv (with_fs (fs_set (m_fs m) p []))
        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
          (FdEntry.FdFileW p (BitVec.ofInt 64 0))))
        (alloc_fd (m_fds m)) i m eff m' evs2 hk
    subst heff
    subst hm'
    subst hevs2
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_create_wronly, check_open_result, check_new_fd_result]
    rw [errno_ret_in_alloc_fd openat_errnos (m_fds m) (by decide)]
    simp only [Bool.false_eq_true, ite_false]
    rw [hfree]
    dsimp only
    rw [ite_eq_left (bv_eqb_refl _)]

private theorem check_open_append_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : open_append p m i m (.ok eff m' evs)) :
    check_open_append p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_append at H
  rcases H with H1 | H2
  · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
    obtain ⟨e0, hin, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, he2] at her
    rw [he3] at hevs
    cases her
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_append, check_open_result, check_new_fd_result]
    rw [ite_eq_left (errno_ret_in_intro openat_errnos _ hin)]
  · obtain ⟨fd, m1, evs1, evs2, hlow, hk, hevs⟩ := H2
    obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := hlow
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, hx, he2] at hk
    rw [hx] at hfree
    rw [he3] at hevs
    obtain ⟨heff, hm', hevs2⟩ :=
      seqSpec_modify2_ret_only_inv (with_fs (append_open_fs (m_fs m) p))
        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
          (FdEntry.FdFileA p (BitVec.ofInt 64 0))))
        (alloc_fd (m_fds m)) i m eff m' evs2 hk
    subst heff
    subst hm'
    subst hevs2
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_append, check_open_result, check_new_fd_result]
    rw [errno_ret_in_alloc_fd openat_errnos (m_fds m) (by decide)]
    simp only [Bool.false_eq_true, ite_false]
    rw [hfree]
    dsimp only
    rw [ite_eq_left (bv_eqb_refl _)]

private theorem check_open_rdwr_complete_ok (i : SyscallInput) (p : Fs.path)
    (fs' : Fs.Fs) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : open_rdwr p fs' m i m (.ok eff m' evs)) :
    check_open_rdwr p fs' eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_rdwr at H
  rcases H with H1 | H2
  · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
    obtain ⟨e0, hin, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, he2] at her
    rw [he3] at hevs
    cases her
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_rdwr, check_open_result, check_new_fd_result]
    rw [ite_eq_left (errno_ret_in_intro openat_errnos _ hin)]
  · obtain ⟨fd, m1, evs1, evs2, hlow, hk, hevs⟩ := H2
    obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := hlow
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, hx, he2] at hk
    rw [hx] at hfree
    rw [he3] at hevs
    obtain ⟨heff, hm', hevs2⟩ :=
      seqSpec_modify2_ret_only_inv (with_fs fs')
        (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m))
          (FdEntry.FdFileRW p (BitVec.ofInt 64 0))))
        (alloc_fd (m_fds m)) i m eff m' evs2 hk
    subst heff
    subst hm'
    subst hevs2
    simp only [List.nil_append] at hevs
    subst hevs
    refine ⟨?_, rfl⟩
    simp only [check_open_rdwr, check_open_result, check_new_fd_result]
    rw [errno_ret_in_alloc_fd openat_errnos (m_fds m) (by decide)]
    simp only [Bool.false_eq_true, ite_false]
    rw [hfree]
    dsimp only
    rw [ite_eq_left (bv_eqb_refl _)]

theorem check_openat_read_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_read_spec p m i m (.ok eff m' evs)) :
    check_openat_read p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_read_spec at H
  unfold check_openat_read
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_open_result_complete_ok i eff m _ m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | none => exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H
    | some data => exact check_open_result_complete_ok i eff m _ m' evs H

theorem check_openat_create_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_create_spec p m i m (.ok eff m' evs)) :
    check_openat_create p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_create_spec at H
  unfold check_openat_create
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    exact check_create_wronly_complete_ok i p eff m m' evs H

theorem check_openat_excl_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_excl_spec p m i m (.ok eff m' evs)) :
    check_openat_excl p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_excl_spec at H
  unfold check_openat_excl
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data => exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
    | none => exact check_create_wronly_complete_ok i p eff m m' evs H

theorem check_openat_dir_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_dir_spec p m i m (.ok eff m' evs)) :
    check_openat_dir p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_dir_spec at H
  unfold check_openat_dir
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_open_result_complete_ok i eff m _ m' evs H
  · rw [ite_eq_right hd] at H ⊢
    by_cases hnm : decide (NAME_MAX < p.length) = true
    · rw [ite_eq_left hnm] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H
        | some data =>
          exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs H

theorem check_openat_append_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_append_spec p m i m (.ok eff m' evs)) :
    check_openat_append p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_append_spec at H
  unfold check_openat_append
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    exact check_open_append_complete_ok i p eff m m' evs H

theorem check_openat_rdwr_complete_ok (i : SyscallInput) (creat trunc : Bool)
    (p : Fs.path) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_rdwr_spec creat trunc p m i m (.ok eff m' evs)) :
    check_openat_rdwr creat trunc p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_rdwr_spec at H
  unfold check_openat_rdwr
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EISDIR) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data =>
      by_cases ht : trunc = true
      · rw [ite_eq_left ht] at H ⊢
        exact check_open_rdwr_complete_ok i p _ eff m m' evs H
      · rw [ite_eq_right ht] at H ⊢
        exact check_open_rdwr_complete_ok i p _ eff m m' evs H
    | none =>
      by_cases hc : creat = true
      · rw [ite_eq_left hc] at H ⊢
        exact check_open_rdwr_complete_ok i p _ eff m m' evs H
      · rw [ite_eq_right hc] at H ⊢
        exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H

theorem check_openat_rdwr_excl_complete_ok (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_rdwr_excl_spec p m i m (.ok eff m' evs)) :
    check_openat_rdwr_excl p eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_rdwr_excl_spec at H
  unfold check_openat_rdwr_excl
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H ⊢
    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
  · rw [ite_eq_right hd] at H ⊢
    generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
    cases lk with
    | some data => exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
    | none => exact check_open_rdwr_complete_ok i p _ eff m m' evs H

theorem check_openat_localtime_complete_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_localtime_spec flags m i m (.ok eff m' evs)) :
    check_openat_localtime flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_localtime_spec at H
  unfold check_openat_localtime
  generalize hfs : fs_lookup (m_fs m) localtime_path = lk at H ⊢
  cases lk with
  | some data =>
    simp only [unmodeled] at H
    exact nomatch H
  | none =>
    by_cases hun : fs_under (m_fs m) localtime_path = true
    · rw [ite_eq_left hun] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
      · rw [ite_eq_left hcr] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hcr] at H ⊢
        exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H

private theorem check_open_devnull_complete_ok (i : SyscallInput) (rd wr : Bool)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : open_devnull m rd wr i m (.ok eff m' evs)) :
    check_open_devnull rd wr eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_devnull at H
  unfold check_open_devnull
  exact check_open_result_complete_ok i eff m _ m' evs H

theorem check_openat_devnull_complete_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_devnull_spec flags m i m (.ok eff m' evs)) :
    check_openat_devnull flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_devnull_spec at H
  unfold check_openat_devnull
  generalize hfs : fs_lookup (m_fs m) devnull_path = lk at H ⊢
  cases lk with
  | some data =>
    simp only [unmodeled] at H
    exact nomatch H
  | none =>
    by_cases hun : fs_under (m_fs m) devnull_path = true
    · rw [ite_eq_left hun] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H ⊢
        exact check_open_devnull_complete_ok i true false eff m m' evs H
      · rw [ite_eq_right h0] at H ⊢
        by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
        · rw [ite_eq_left hw] at H ⊢
          exact check_open_devnull_complete_ok i false true eff m m' evs H
        · rw [ite_eq_right hw] at H ⊢
          by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
          · rw [ite_eq_left hx] at H ⊢
            exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
          · rw [ite_eq_right hx] at H ⊢
            by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
            · rw [ite_eq_left hdir] at H ⊢
              exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs H
            · rw [ite_eq_right hdir] at H ⊢
              by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
              · rw [ite_eq_left hap] at H ⊢
                exact check_open_devnull_complete_ok i false true eff m m' evs H
              · rw [ite_eq_right hap] at H ⊢
                by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrw] at H ⊢
                  exact check_open_devnull_complete_ok i true true eff m m' evs H
                · rw [ite_eq_right hrw] at H ⊢
                  by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                  · rw [ite_eq_left hrx] at H ⊢
                    exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
                  · rw [ite_eq_right hrx] at H
                    simp only [unmodeled] at H
                    exact nomatch H

private theorem check_open_urandom_complete_ok (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : open_urandom m i m (.ok eff m' evs)) :
    check_open_urandom eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold open_urandom at H
  unfold check_open_urandom
  exact check_open_result_complete_ok i eff m _ m' evs H

theorem check_openat_urandom_complete_ok (i : SyscallInput) (flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_urandom_spec flags m i m (.ok eff m' evs)) :
    check_openat_urandom flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_urandom_spec at H
  unfold check_openat_urandom
  generalize hfs : fs_lookup (m_fs m) urandom_path = lk at H ⊢
  cases lk with
  | some data =>
    simp only [unmodeled] at H
    exact nomatch H
  | none =>
    by_cases hun : fs_under (m_fs m) urandom_path = true
    · rw [ite_eq_left hun] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H ⊢
        exact check_open_urandom_complete_ok i eff m m' evs H
      · rw [ite_eq_right h0] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H ⊢
          exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_ret_only_complete_ok i eff (errno_ret ENOTDIR) m m' evs H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
            · rw [ite_eq_left hrx] at H ⊢
              exact check_ret_only_complete_ok i eff (errno_ret EEXIST) m m' evs H
            · rw [ite_eq_right hrx] at H
              simp only [unmodeled] at H
              exact nomatch H

theorem check_openat_tmp_complete_ok (i : SyscallInput) (n p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_tmp_spec n p flags m i m (.ok eff m' evs)) :
    check_openat_tmp n p flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_tmp_spec at H
  unfold check_openat_tmp
  by_cases hnm : decide (NAME_MAX < n.length) = true
  · rw [ite_eq_left hnm] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hnm] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none =>
          simp only [unmodeled] at H
          exact nomatch H
        | some data => exact check_openat_read_complete_ok i p eff m m' evs H
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H ⊢
        exact check_openat_create_complete_ok i p eff m m' evs H
      · rw [ite_eq_right hw] at H
        simp only [unmodeled] at H
        exact nomatch H

theorem check_openat_sep_complete_ok (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_sep_spec p flags m i m (.ok eff m' evs)) :
    check_openat_sep p flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_sep_spec at H
  unfold check_openat_sep
  by_cases hl : path_eqb p localtime_path = true
  · rw [ite_eq_left hl] at H ⊢
    exact check_openat_localtime_complete_ok i flags eff m m' evs H
  · rw [ite_eq_right hl] at H ⊢
    by_cases hd : path_eqb p devnull_path = true
    · rw [ite_eq_left hd] at H ⊢
      exact check_openat_devnull_complete_ok i flags eff m m' evs H
    · rw [ite_eq_right hd] at H ⊢
      by_cases hu : path_eqb p urandom_path = true
      · rw [ite_eq_left hu] at H ⊢
        exact check_openat_urandom_complete_ok i flags eff m m' evs H
      · rw [ite_eq_right hu] at H ⊢
        generalize htn : tmp_name p = tn at H ⊢
        cases tn with
        | none =>
          simp only [unmodeled] at H
          exact nomatch H
        | some n => exact check_openat_tmp_complete_ok i n p flags eff m m' evs H

theorem check_openat_resolved_complete_ok (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_resolved_spec p flags m i m (.ok eff m' evs)) :
    check_openat_resolved p flags eff m = .CheckOk m' evs ∧ eff.eff_copyins = [] := by
  unfold openat_resolved_spec at H
  unfold check_openat_resolved
  by_cases hsl : path_has_slash p = true
  · rw [ite_eq_left hsl] at H ⊢
    exact check_openat_sep_complete_ok i p flags eff m m' evs H
  · rw [ite_eq_right hsl] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      exact check_openat_read_complete_ok i p eff m m' evs H
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H ⊢
        exact check_openat_create_complete_ok i p eff m m' evs H
      · rw [ite_eq_right hw] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H ⊢
          exact check_openat_excl_complete_ok i p eff m m' evs H
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_openat_dir_complete_ok i p eff m m' evs H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
            · rw [ite_eq_left hap] at H ⊢
              exact check_openat_append_complete_ok i p eff m m' evs H
            · rw [ite_eq_right hap] at H ⊢
              by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
              · rw [ite_eq_left hrw] at H ⊢
                exact check_openat_rdwr_complete_ok i _ _ p eff m m' evs H
              · rw [ite_eq_right hrw] at H ⊢
                by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrx] at H ⊢
                  exact check_openat_rdwr_excl_complete_ok i p eff m m' evs H
                · rw [ite_eq_right hrx] at H
                  simp only [unmodeled] at H
                  exact nomatch H

theorem check_openat_body_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_body_spec i m dirfd pathp flags i m (.ok eff m' evs)) :
    check_openat_body i dirfd pathp flags eff m = .CheckOk m' evs
      ∧ eff.eff_copyins = [] := by
  unfold openat_body_spec at H
  unfold check_openat_body
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact check_ret_only_complete_ok i eff (errno_ret ENAMETOOLONG) m m' evs H
  | CstrFault =>
    exact check_ret_only_complete_ok i eff (errno_ret EFAULT) m m' evs H
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      exact check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        exact check_openat_resolved_complete_ok i p flags eff m m' evs H

private theorem openat_core_ok_inv (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_core_spec dirfd pathp flags i m (.ok eff m' evs)) :
    (!(modeled_open_flags flags)) = false
      ∧ openat_body_spec i m dirfd pathp flags i m (.ok eff m' evs) := by
  unfold openat_core_spec at H
  have h1 : bind getModelSpec
      (fun m0 => if (!(modeled_open_flags flags)) = true then unmodeled
        else openat_body_spec i m0 dirfd pathp flags) i m (.ok eff m' evs) :=
    input_bind_ok_inv _ i m eff m' evs H
  obtain ⟨m0, m1, evs1, evs2, hget, hbody, hevs⟩ := h1
  cases hget
  simp only [List.nil_append] at hevs
  subst hevs
  by_cases hc : (!(modeled_open_flags flags)) = true
  · rw [ite_eq_left hc] at hbody
    simp only [unmodeled] at hbody
    exact nomatch hbody
  · rw [ite_eq_right hc] at hbody
    refine ⟨?_, hbody⟩
    cases hv : (!(modeled_open_flags flags)) with
    | false => rfl
    | true => exact absurd hv hc

theorem check_openat_complete_ok (i : SyscallInput) (dirfd pathp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : openat_spec dirfd pathp flags i m (.ok eff m' evs)) :
    check_openat i dirfd pathp flags eff m = .CheckOk m' evs := by
  unfold openat_spec at H
  have h1 : record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (openat_core_spec dirfd pathp flags) i m (.ok eff m' evs) :=
    input_bind_ok_inv _ i m eff m' evs H
  obtain ⟨core, hcore, hEff⟩ := record_copyins_ok_inv _ _ i m eff m' evs h1
  subst hEff
  obtain ⟨hflags, hbody⟩ := openat_core_ok_inv i dirfd pathp flags core m m' evs hcore
  obtain ⟨hchecked, hcopyins⟩ :=
    check_openat_body_complete_ok i dirfd pathp flags _ m m' evs hbody
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := core
  simp only at hcopyins
  subst hcopyins
  unfold check_openat
  rw [hflags]
  simp only [Bool.false_eq_true, ite_false]
  rw [check_copyins_after_ok_iff]
  refine ⟨?_, ?_⟩
  · simp [with_copyins]
  · simp only [clear_copyins, with_copyins]
    exact hchecked

/- ------------------------------------------------ unmodeled-completeness -/

/-- The spec's decline forces the checker's.  Like [completes_ok] it is a
    predicate the direct branch splits do not need; it is kept for the
    file's vocabulary. -/
private def completes_unmodeled (i : SyscallInput) (m : Model)
    (spec : SysSpec SyscallEffect) (check : check_result) : Prop :=
  spec i m .unmodeled → check = .CheckUnmodeled

/-- The two acceptor steps never decline. -/
private theorem modifySpec_never_unmodeled (f : Model → Model) (i : SyscallInput)
    (m : Model) : ¬ modifySpec f i m .unmodeled := by
  intro H
  exact nomatch H

private theorem ret_only_never_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  exact nomatch H

private theorem seqSpec_modify_ret_only_never_unmodeled (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (ret_only r) i m .unmodeled := by
  intro H
  rcases H with h | ⟨u, m2, evs2, h1, h2⟩
  · exact nomatch h
  · exact nomatch h2

private theorem seqSpec_modify2_ret_only_never_unmodeled (f g : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (seqSpec (modifySpec g) (ret_only r)) i m .unmodeled := by
  intro H
  rcases H with h | ⟨u, m2, evs2, h1, h2⟩
  · exact nomatch h
  · exact absurd h2 (seqSpec_modify_ret_only_never_unmodeled g r i m2)

private theorem ret_only_no_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled :=
  ret_only_never_unmodeled r i m

private theorem open_result_spec_no_unmodeled (m : Model) (mk : word → Model → Model)
    (i : SyscallInput) : ¬ open_result_spec m mk i m .unmodeled := by
  intro H
  unfold open_result_spec at H
  rcases H with H1 | H2
  · rcases H1 with hdecl | ⟨x, m1, evs1, hc, hk⟩
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · exact nomatch hk
  · rcases H2 with hdecl | ⟨fd, m1, evs1, hlow, hk⟩
    · obtain ⟨fd, -, heq⟩ := hdecl
      exact nomatch heq
    · exact absurd hk (seqSpec_modify_ret_only_never_unmodeled _ _ i m1)

private theorem create_wronly_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ create_wronly p m i m .unmodeled := by
  intro H
  unfold create_wronly at H
  rcases H with H1 | H2
  · rcases H1 with hdecl | ⟨x, m1, evs1, hc, hk⟩
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · exact nomatch hk
  · rcases H2 with hdecl | ⟨fd, m1, evs1, hlow, hk⟩
    · obtain ⟨fd, -, heq⟩ := hdecl
      exact nomatch heq
    · exact absurd hk (seqSpec_modify2_ret_only_never_unmodeled _ _ _ i m1)

private theorem openat_read_spec_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ openat_read_spec p m i m .unmodeled := by
  intro H
  unfold openat_read_spec at H
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact open_result_spec_no_unmodeled m _ i H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | none => exact ret_only_no_unmodeled (errno_ret ENOENT) i m H
    | some data => exact open_result_spec_no_unmodeled m _ i H

private theorem openat_create_spec_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ openat_create_spec p m i m .unmodeled := by
  intro H
  unfold openat_create_spec at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact ret_only_no_unmodeled (errno_ret EISDIR) i m H
  · rw [ite_eq_right hd] at H
    exact create_wronly_no_unmodeled p m i H

private theorem openat_excl_spec_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ openat_excl_spec p m i m .unmodeled := by
  intro H
  unfold openat_excl_spec at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact ret_only_no_unmodeled (errno_ret EEXIST) i m H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data => exact ret_only_no_unmodeled (errno_ret EEXIST) i m H
    | none => exact create_wronly_no_unmodeled p m i H

theorem check_openat_dir_complete_unmodeled (i : SyscallInput) (p : Fs.path)
    (eff : SyscallEffect) (m : Model)
    (H : openat_dir_spec p m i m .unmodeled) :
    check_openat_dir p eff m = .CheckUnmodeled := by
  unfold openat_dir_spec at H
  unfold check_openat_dir
  by_cases hd : path_is_dirref p = true
  · rw [ite_eq_left hd] at H
    exact absurd H (open_result_spec_no_unmodeled m _ i)
  · rw [ite_eq_right hd] at H ⊢
    by_cases hnm : decide (NAME_MAX < p.length) = true
    · rw [ite_eq_left hnm] at H ⊢
    · rw [ite_eq_right hnm] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H ⊢
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact absurd H (ret_only_no_unmodeled (errno_ret ENOENT) i m)
        | some data => exact absurd H (ret_only_no_unmodeled (errno_ret ENOTDIR) i m)

private theorem open_append_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ open_append p m i m .unmodeled := by
  intro H
  unfold open_append at H
  rcases H with H1 | H2
  · rcases H1 with hdecl | ⟨x, m1, evs1, hc, hk⟩
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · exact nomatch hk
  · rcases H2 with hdecl | ⟨fd, m1, evs1, hlow, hk⟩
    · obtain ⟨fd, -, heq⟩ := hdecl
      exact nomatch heq
    · exact absurd hk (seqSpec_modify2_ret_only_never_unmodeled _ _ _ i m1)

private theorem openat_append_spec_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ openat_append_spec p m i m .unmodeled := by
  intro H
  unfold openat_append_spec at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact ret_only_no_unmodeled (errno_ret EISDIR) i m H
  · rw [ite_eq_right hd] at H
    exact open_append_no_unmodeled p m i H

private theorem open_rdwr_no_unmodeled (p : Fs.path) (fs' : Fs.Fs) (m : Model)
    (i : SyscallInput) : ¬ open_rdwr p fs' m i m .unmodeled := by
  intro H
  unfold open_rdwr at H
  rcases H with H1 | H2
  · rcases H1 with hdecl | ⟨x, m1, evs1, hc, hk⟩
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · exact nomatch hk
  · rcases H2 with hdecl | ⟨fd, m1, evs1, hlow, hk⟩
    · obtain ⟨fd, -, heq⟩ := hdecl
      exact nomatch heq
    · exact absurd hk (seqSpec_modify2_ret_only_never_unmodeled _ _ _ i m1)

private theorem openat_rdwr_spec_no_unmodeled (creat trunc : Bool) (p : Fs.path)
    (m : Model) (i : SyscallInput) : ¬ openat_rdwr_spec creat trunc p m i m .unmodeled := by
  intro H
  unfold openat_rdwr_spec at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact ret_only_no_unmodeled (errno_ret EISDIR) i m H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data =>
      by_cases ht : trunc = true
      · rw [ite_eq_left ht] at H
        exact open_rdwr_no_unmodeled p _ m i H
      · rw [ite_eq_right ht] at H
        exact open_rdwr_no_unmodeled p _ m i H
    | none =>
      by_cases hc : creat = true
      · rw [ite_eq_left hc] at H
        exact open_rdwr_no_unmodeled p _ m i H
      · rw [ite_eq_right hc] at H
        exact ret_only_no_unmodeled (errno_ret ENOENT) i m H

private theorem openat_rdwr_excl_spec_no_unmodeled (p : Fs.path) (m : Model)
    (i : SyscallInput) : ¬ openat_rdwr_excl_spec p m i m .unmodeled := by
  intro H
  unfold openat_rdwr_excl_spec at H
  by_cases hd : (path_is_dirref p || fs_under (m_fs m) p) = true
  · rw [ite_eq_left hd] at H
    exact ret_only_no_unmodeled (errno_ret EEXIST) i m H
  · rw [ite_eq_right hd] at H
    generalize hfs : fs_lookup (m_fs m) p = lk at H
    cases lk with
    | some data => exact ret_only_no_unmodeled (errno_ret EEXIST) i m H
    | none => exact open_rdwr_no_unmodeled p _ m i H

theorem check_openat_localtime_complete_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_localtime_spec flags m i m .unmodeled) :
    check_openat_localtime flags eff m = .CheckUnmodeled := by
  unfold openat_localtime_spec at H
  unfold check_openat_localtime
  generalize hfs : fs_lookup (m_fs m) localtime_path = lk at H ⊢
  cases lk with
  | some data => rfl
  | none =>
    by_cases hun : fs_under (m_fs m) localtime_path = true
    · rw [ite_eq_left hun] at H ⊢
    · rw [ite_eq_right hun] at H ⊢
      by_cases hcr : flag_set (z_ldiff (flags.toNat : Int) open_ignored_flags) O_CREAT = true
      · rw [ite_eq_left hcr] at H ⊢
      · rw [ite_eq_right hcr] at H
        exact absurd H (ret_only_no_unmodeled (errno_ret ENOENT) i m)

private theorem open_devnull_no_unmodeled (rd wr : Bool) (m : Model) (i : SyscallInput) :
    ¬ open_devnull m rd wr i m .unmodeled := by
  intro H
  exact open_result_spec_no_unmodeled m _ i H

theorem check_openat_devnull_complete_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_devnull_spec flags m i m .unmodeled) :
    check_openat_devnull flags eff m = .CheckUnmodeled := by
  unfold openat_devnull_spec at H
  unfold check_openat_devnull
  generalize hfs : fs_lookup (m_fs m) devnull_path = lk at H ⊢
  cases lk with
  | some data => rfl
  | none =>
    by_cases hun : fs_under (m_fs m) devnull_path = true
    · rw [ite_eq_left hun] at H ⊢
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H
        exact absurd H (open_devnull_no_unmodeled true false m i)
      · rw [ite_eq_right h0] at H ⊢
        by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
        · rw [ite_eq_left hw] at H
          exact absurd H (open_devnull_no_unmodeled false true m i)
        · rw [ite_eq_right hw] at H ⊢
          by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
          · rw [ite_eq_left hx] at H
            exact absurd H (ret_only_no_unmodeled (errno_ret EEXIST) i m)
          · rw [ite_eq_right hx] at H ⊢
            by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
            · rw [ite_eq_left hdir] at H
              exact absurd H (ret_only_no_unmodeled (errno_ret ENOTDIR) i m)
            · rw [ite_eq_right hdir] at H ⊢
              by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
              · rw [ite_eq_left hap] at H
                exact absurd H (open_devnull_no_unmodeled false true m i)
              · rw [ite_eq_right hap] at H ⊢
                by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrw] at H
                  exact absurd H (open_devnull_no_unmodeled true true m i)
                · rw [ite_eq_right hrw] at H ⊢
                  by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                  · rw [ite_eq_left hrx] at H
                    exact absurd H (ret_only_no_unmodeled (errno_ret EEXIST) i m)
                  · rw [ite_eq_right hrx] at H ⊢

private theorem open_urandom_no_unmodeled (m : Model) (i : SyscallInput) :
    ¬ open_urandom m i m .unmodeled := by
  intro H
  exact open_result_spec_no_unmodeled m _ i H

theorem check_openat_urandom_complete_unmodeled (i : SyscallInput)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_urandom_spec flags m i m .unmodeled) :
    check_openat_urandom flags eff m = .CheckUnmodeled := by
  unfold openat_urandom_spec at H
  unfold check_openat_urandom
  generalize hfs : fs_lookup (m_fs m) urandom_path = lk at H ⊢
  cases lk with
  | some data => rfl
  | none =>
    by_cases hun : fs_under (m_fs m) urandom_path = true
    · rw [ite_eq_left hun] at H ⊢
    · rw [ite_eq_right hun] at H ⊢
      dsimp only at H ⊢
      by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
      · rw [ite_eq_left h0] at H
        exact absurd H (open_urandom_no_unmodeled m i)
      · rw [ite_eq_right h0] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H
          exact absurd H (ret_only_no_unmodeled (errno_ret EEXIST) i m)
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H
            exact absurd H (ret_only_no_unmodeled (errno_ret ENOTDIR) i m)
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
            · rw [ite_eq_left hrx] at H
              exact absurd H (ret_only_no_unmodeled (errno_ret EEXIST) i m)
            · rw [ite_eq_right hrx] at H ⊢

theorem check_openat_tmp_complete_unmodeled (i : SyscallInput) (n p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_tmp_spec n p flags m i m .unmodeled) :
    check_openat_tmp n p flags eff m = .CheckUnmodeled := by
  unfold openat_tmp_spec at H
  unfold check_openat_tmp
  by_cases hnm : decide (NAME_MAX < n.length) = true
  · rw [ite_eq_left hnm] at H ⊢
  · rw [ite_eq_right hnm] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H ⊢
      by_cases hun : fs_under (m_fs m) p = true
      · rw [ite_eq_left hun] at H ⊢
      · rw [ite_eq_right hun] at H ⊢
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => rfl
        | some data => exact absurd H (openat_read_spec_no_unmodeled p m i)
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (openat_create_spec_no_unmodeled p m i)
      · rw [ite_eq_right hw] at H ⊢

theorem check_openat_sep_complete_unmodeled (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_sep_spec p flags m i m .unmodeled) :
    check_openat_sep p flags eff m = .CheckUnmodeled := by
  unfold openat_sep_spec at H
  unfold check_openat_sep
  by_cases hl : path_eqb p localtime_path = true
  · rw [ite_eq_left hl] at H ⊢
    exact check_openat_localtime_complete_unmodeled i flags eff m H
  · rw [ite_eq_right hl] at H ⊢
    by_cases hd : path_eqb p devnull_path = true
    · rw [ite_eq_left hd] at H ⊢
      exact check_openat_devnull_complete_unmodeled i flags eff m H
    · rw [ite_eq_right hd] at H ⊢
      by_cases hu : path_eqb p urandom_path = true
      · rw [ite_eq_left hu] at H ⊢
        exact check_openat_urandom_complete_unmodeled i flags eff m H
      · rw [ite_eq_right hu] at H ⊢
        generalize htn : tmp_name p = tn at H ⊢
        cases tn with
        | none => rfl
        | some n => exact check_openat_tmp_complete_unmodeled i n p flags eff m H

theorem check_openat_resolved_complete_unmodeled (i : SyscallInput) (p : Fs.path)
    (flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_resolved_spec p flags m i m .unmodeled) :
    check_openat_resolved p flags eff m = .CheckUnmodeled := by
  unfold openat_resolved_spec at H
  unfold check_openat_resolved
  by_cases hsl : path_has_slash p = true
  · rw [ite_eq_left hsl] at H ⊢
    exact check_openat_sep_complete_unmodeled i p flags eff m H
  · rw [ite_eq_right hsl] at H ⊢
    dsimp only at H ⊢
    by_cases h0 : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == 0) = true
    · rw [ite_eq_left h0] at H
      exact absurd H (openat_read_spec_no_unmodeled p m i)
    · rw [ite_eq_right h0] at H ⊢
      by_cases hw : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == wr_create_flags) = true
      · rw [ite_eq_left hw] at H
        exact absurd H (openat_create_spec_no_unmodeled p m i)
      · rw [ite_eq_right hw] at H ⊢
        by_cases hx : is_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
        · rw [ite_eq_left hx] at H
          exact absurd H (openat_excl_spec_no_unmodeled p m i)
        · rw [ite_eq_right hx] at H ⊢
          by_cases hdir : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == O_DIRECTORY) = true
          · rw [ite_eq_left hdir] at H ⊢
            exact check_openat_dir_complete_unmodeled i p eff m H
          · rw [ite_eq_right hdir] at H ⊢
            by_cases hap : ((z_ldiff (flags.toNat : Int) open_ignored_flags) == append_create_flags) = true
            · rw [ite_eq_left hap] at H
              exact absurd H (openat_append_spec_no_unmodeled p m i)
            · rw [ite_eq_right hap] at H ⊢
              by_cases hrw : rdwr_open_word (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
              · rw [ite_eq_left hrw] at H
                exact absurd H (openat_rdwr_spec_no_unmodeled _ _ p m i)
              · rw [ite_eq_right hrw] at H ⊢
                by_cases hrx : is_rdwr_excl_create (z_ldiff (flags.toNat : Int) open_ignored_flags) = true
                · rw [ite_eq_left hrx] at H
                  exact absurd H (openat_rdwr_excl_spec_no_unmodeled p m i)
                · rw [ite_eq_right hrx] at H ⊢

theorem check_openat_body_spec_complete_unmodeled (i : SyscallInput)
    (dirfd pathp flags : word) (eff : SyscallEffect) (m : Model)
    (H : openat_body_spec i m dirfd pathp flags i m .unmodeled) :
    check_openat_body i dirfd pathp flags eff m = .CheckUnmodeled := by
  unfold openat_body_spec at H
  unfold check_openat_body
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact absurd H (ret_only_no_unmodeled (errno_ret ENAMETOOLONG) i m)
  | CstrFault =>
    exact absurd H (ret_only_no_unmodeled (errno_ret EFAULT) i m)
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      exact absurd H (ret_only_no_unmodeled (errno_ret ENOENT) i m)
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
      · rw [ite_eq_right hd] at H ⊢
        exact check_openat_resolved_complete_unmodeled i p flags eff m H

private theorem openat_core_unmodeled_inv (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (H : openat_core_spec dirfd pathp flags i m .unmodeled) :
    (!(modeled_open_flags flags)) = true ∨
      ((!(modeled_open_flags flags)) = false
        ∧ openat_body_spec i m dirfd pathp flags i m .unmodeled) := by
  unfold openat_core_spec at H
  have h1 : bind getModelSpec
      (fun m0 => if (!(modeled_open_flags flags)) = true then unmodeled
        else openat_body_spec i m0 dirfd pathp flags) i m .unmodeled :=
    input_bind_unmodeled_inv _ i m H
  rcases h1 with hdecl | ⟨m0, m1, evs1, hget, hbody⟩
  · exact nomatch hdecl
  · cases hget
    by_cases hc : (!(modeled_open_flags flags)) = true
    · exact Or.inl hc
    · refine Or.inr ⟨?_, ?_⟩
      · cases hv : (!(modeled_open_flags flags)) with
        | false => rfl
        | true => exact absurd hv hc
      · rw [ite_eq_right hc] at hbody
        exact hbody

theorem check_openat_complete_unmodeled (i : SyscallInput) (dirfd pathp flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : openat_spec dirfd pathp flags i m .unmodeled) :
    check_openat i dirfd pathp flags eff m = .CheckUnmodeled := by
  unfold openat_spec at H
  have h1 : record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
      (openat_core_spec dirfd pathp flags) i m .unmodeled :=
    input_bind_unmodeled_inv _ i m H
  have h2 := record_copyins_unmodeled_inv _ _ i m h1
  rcases openat_core_unmodeled_inv i dirfd pathp flags m h2 with hfl | ⟨hfl, hbody⟩
  · unfold check_openat
    rw [hfl]
    rfl
  · have hb := check_openat_body_spec_complete_unmodeled i dirfd pathp flags
      (clear_copyins eff) m hbody
    unfold check_openat
    rw [hfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [hb]
    rfl

/- ----------------------------------------------------------- close (57) -/

/-- [close] removes the descriptor, or answers the deterministic
    -EBADF: the fd table is the whole of what the syscall reads, so the
    checker needs no arm for a kind. -/
def check_close (fd : word) (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some _ => check_ret_only eff (BitVec.ofInt 64 0)
                (with_fds (fd_remove (m_fds m) fd) m) []

theorem check_close_sound_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_close fd eff m = .CheckOk m' evs) :
    close_spec fd i m (.ok eff m' evs) := by
  generalize hP : (close_spec fd i m (.ok eff m' evs)) = Q at *
  unfold check_close at H
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    simp only [hfd] at H
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
    rw [← hP]
    simp only [close_spec, getModelSpec, bind_getModel, hfd]
    exact pure_ok _ i _
  | some e =>
    simp only [hfd] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) (with_fds (fd_remove (m_fds m) fd) m)
        [] m' evs).mp H
    rw [← hP]
    simp only [close_spec, getModelSpec, bind_getModel, hfd]
    apply bind_ok0
    · exact modify_ok _ i m
    · exact pure_ok _ i _

theorem check_close_sound_unmodeled (fd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_close fd eff m = .CheckUnmodeled) :
    close_spec fd i m .unmodeled := by
  unfold check_close at H
  generalize hfs : fd_lookup (m_fds m) fd = lk at H
  cases lk with
  | none =>
    dsimp only at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    dsimp only at H
    exact absurd H
      (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
        (with_fds (fd_remove (m_fds m) fd) m) [])

theorem check_close_complete_ok (fd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : close_spec fd i m (.ok eff m' evs)) :
    check_close fd eff m = .CheckOk m' evs := by
  generalize hP : (check_close fd eff m = .CheckOk m' evs) = Q at *
  unfold close_spec at H
  simp only [getModelSpec, bind_getModel] at H
  generalize hfs : fd_lookup (m_fds m) fd = lk at H
  cases lk with
  | none =>
    dsimp only at H
    cases H
    rw [← hP]
    simp [check_close, hfs, check_ret_only, bv_eqb_refl]
  | some e =>
    dsimp only at H
    obtain ⟨heff, hm', hevs⟩ :=
      seqSpec_modify_ret_only_inv (with_fds (fd_remove (m_fds m) fd))
        (BitVec.ofInt 64 0) i m eff m' evs H
    subst heff
    subst hm'
    subst hevs
    rw [← hP]
    simp [check_close, hfs, check_ret_only, bv_eqb_refl]

theorem check_close_complete_unmodeled (fd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : close_spec fd i m .unmodeled) :
    check_close fd eff m = .CheckUnmodeled := by
  unfold close_spec at H
  simp only [getModelSpec, bind_getModel] at H
  generalize hfs : fd_lookup (m_fds m) fd = lk at H ⊢
  cases lk with
  | none =>
    dsimp only at H
    exact absurd H (ret_only_no_unmodeled (errno_ret EBADF) i m)
  | some e =>
    dsimp only at H
    exact absurd H (seqSpec_modify_ret_only_never_unmodeled _ _ i m)

/- ------------------------------------------------------ ftruncate (46) -/

/-- The two writable-file kinds' arm, shared as [Open.ftruncate_file_arm]
    is shared by the spec: a writable fd whose name is not in the image
    cannot happen (it was opened through it), and a zero-fill too large
    to build as a byte list declines.  -/
private def check_ftruncate_file_arm (p : Fs.path) (len : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fs_lookup (m_fs m) p with
  | none => .CheckUnmodeled
  | some data =>
      if !(modeled_truncate_gap data len) then .CheckUnmodeled
      else
        check_ret_only eff (BitVec.ofInt 64 0)
          (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) []

/-- Mirrors [Open.ftruncate_spec] arm for arm.  Every kind but the three
    writable-file ones gets the deterministic -EINVAL that
    `do_ftruncate`'s `!S_ISREG(inode->i_mode) || !(file->f_mode &
    FMODE_WRITE)` answers, and an unopened fd the -EBADF. -/
def check_ftruncate (fd len : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if decide (len.toInt < 0) then check_ret_only eff (errno_ret EINVAL) m []
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (FdEntry.FdChannel _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdSocket _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdPipe _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdDevNull _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some FdEntry.FdUrandom => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdFile _ _) => check_ret_only eff (errno_ret EINVAL) m []
  | some FdEntry.FdDir => check_ret_only eff (errno_ret EINVAL) m []
  | some (FdEntry.FdFileA p _) => check_ftruncate_file_arm p len eff m
  | some (FdEntry.FdFileW p _) => check_ftruncate_file_arm p len eff m
  | some (FdEntry.FdFileRW p _) => check_ftruncate_file_arm p len eff m

theorem check_ftruncate_sound_ok (fd len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_ftruncate fd len eff m = .CheckOk m' evs) :
    ftruncate_spec fd len i m (.ok eff m' evs) := by
  generalize hP : (ftruncate_spec fd len i m (.ok eff m' evs)) = Q at *
  unfold check_ftruncate at H
  by_cases hneg : decide (len.toInt < 0) = true
  · rw [ite_eq_left hneg] at H
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [ftruncate_spec]
    rw [ite_eq_left hneg]
    exact pure_ok _ i _
  · rw [ite_eq_right hneg] at H
    cases hfd : fd_lookup (m_fds m) fd with
    | none =>
      simp only [hfd] at H
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
      rw [← hP]
      simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
      exact pure_ok _ i _
    | some e =>
      cases e with
      | FdChannel ch =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdSocket sk =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdPipe id wr =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdDevNull rd wr =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdUrandom =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdFile p cur =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdDir =>
        simp only [hfd] at H
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        exact pure_ok _ i _
      | FdFileA p cur =>
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        simp only [hfd] at H
        unfold check_ftruncate_file_arm at H
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [] m' evs).mp H
            apply bind_ok0
            · exact modify_ok _ i m
            · exact pure_ok _ i _
      | FdFileW p cur =>
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd,
          ftruncate_file_arm]
        simp only [hfd] at H
        unfold check_ftruncate_file_arm at H
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [] m' evs).mp H
            apply bind_ok0
            · exact modify_ok _ i m
            · exact pure_ok _ i _
      | FdFileRW p cur =>
        rw [← hP]
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd,
          ftruncate_file_arm]
        simp only [hfd] at H
        unfold check_ftruncate_file_arm at H
        generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
        cases lk with
        | none => exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨rfl, rfl, rfl⟩ :=
              (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [] m' evs).mp H
            apply bind_ok0
            · exact modify_ok _ i m
            · exact pure_ok _ i _

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the shared writable-file
    arm only ever answers a [check_ret_only] over [with_fs … m] — or
    declines — so it leaves [m_vmmaps] alone.  Public because the helper it
    is about is `private`; the walk is the checker side of
    [check_ftruncate_sound_ok]'s three writable-file branches, with the
    spec dropped. -/
theorem check_ftruncate_file_arm_frame (p : Fs.path) (len : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ftruncate_file_arm p len eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_ftruncate_file_arm at H
  generalize hfs : fs_lookup (m_fs m) p = lk at H
  cases lk with
  | none => exact nomatch H
  | some data =>
    dsimp only at H
    by_cases hgap : (!(modeled_truncate_gap data len)) = true
    · rw [ite_eq_left hgap] at H
      exact nomatch H
    · rw [ite_eq_right hgap] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (BitVec.ofInt 64 0)
          (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [] m' evs).mp H
      rfl

theorem check_ftruncate_sound_unmodeled (fd len : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_ftruncate fd len eff m = .CheckUnmodeled) :
    ftruncate_spec fd len i m .unmodeled := by
  unfold check_ftruncate at H
  by_cases hneg : decide (len.toInt < 0) = true
  · rw [ite_eq_left hneg] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hneg] at H
    generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
    cases lk with
    | none =>
      dsimp only at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
    | some e =>
      cases e with
      | FdChannel ch =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdSocket sk =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdPipe id wr =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdDevNull rd wr =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdUrandom =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdFile p cur =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdDir =>
        dsimp only at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      | FdFileA p cur =>
        dsimp only at H
        unfold check_ftruncate_file_arm at H
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd]
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          exact unmodeled_intro i m
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            exact unmodeled_intro i m
          · rw [ite_eq_right hgap] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [])
      | FdFileW p cur =>
        dsimp only at H
        unfold check_ftruncate_file_arm at H
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd,
          ftruncate_file_arm]
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          exact unmodeled_intro i m
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            exact unmodeled_intro i m
          · rw [ite_eq_right hgap] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [])
      | FdFileRW p cur =>
        dsimp only at H
        unfold check_ftruncate_file_arm at H
        simp only [ftruncate_spec, getModelSpec, bind_getModel, ite_eq_right hneg, hfd,
          ftruncate_file_arm]
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          exact unmodeled_intro i m
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            exact unmodeled_intro i m
          · rw [ite_eq_right hgap] at H
            exact absurd H
              (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
                (with_fs (fs_set (m_fs m) p (file_truncate data len)) m) [])

theorem check_ftruncate_complete_ok (fd len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : ftruncate_spec fd len i m (.ok eff m' evs)) :
    check_ftruncate fd len eff m = .CheckOk m' evs := by
  generalize hP : (check_ftruncate fd len eff m = .CheckOk m' evs) = Q at *
  unfold ftruncate_spec at H
  by_cases hneg : decide (len.toInt < 0) = true
  · rw [ite_eq_left hneg] at H
    cases H
    rw [← hP]
    simp [check_ftruncate, hneg, check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hneg] at H
    simp only [getModelSpec, bind_getModel] at H
    generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
    cases lk with
    | none =>
      dsimp only at H
      cases H
      rw [← hP]
      simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
    | some e =>
      cases e with
      | FdChannel ch =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdSocket sk =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdPipe id wr =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdDevNull rd wr =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdUrandom =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdFile p cur =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdDir =>
        dsimp only at H
        cases H
        rw [← hP]
        simp [check_ftruncate, hneg, hfd, check_ret_only, bv_eqb_refl]
      | FdFileA p cur =>
        dsimp only at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H
          simp only [unmodeled] at H
          exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            simp only [unmodeled] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              seqSpec_modify_ret_only_inv
                (with_fs (fs_set (m_fs m) p (file_truncate data len)))
                (BitVec.ofInt 64 0) i m eff m' evs H
            subst heff
            subst hm'
            subst hevs
            simp [check_ret_only, bv_eqb_refl]
      | FdFileW p cur =>
        dsimp only at H
        simp only [ftruncate_file_arm] at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H
          simp only [unmodeled] at H
          exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            simp only [unmodeled] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              seqSpec_modify_ret_only_inv
                (with_fs (fs_set (m_fs m) p (file_truncate data len)))
                (BitVec.ofInt 64 0) i m eff m' evs H
            subst heff
            subst hm'
            subst hevs
            simp [check_ret_only, bv_eqb_refl]
      | FdFileRW p cur =>
        dsimp only at H
        simp only [ftruncate_file_arm] at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H
          simp only [unmodeled] at H
          exact nomatch H
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H
            simp only [unmodeled] at H
            exact nomatch H
          · rw [ite_eq_right hgap] at H ⊢
            obtain ⟨heff, hm', hevs⟩ :=
              seqSpec_modify_ret_only_inv
                (with_fs (fs_set (m_fs m) p (file_truncate data len)))
                (BitVec.ofInt 64 0) i m eff m' evs H
            subst heff
            subst hm'
            subst hevs
            simp [check_ret_only, bv_eqb_refl]

theorem check_ftruncate_complete_unmodeled (fd len : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : ftruncate_spec fd len i m .unmodeled) :
    check_ftruncate fd len eff m = .CheckUnmodeled := by
  generalize hP : (check_ftruncate fd len eff m = .CheckUnmodeled) = Q at *
  unfold ftruncate_spec at H
  by_cases hneg : decide (len.toInt < 0) = true
  · rw [ite_eq_left hneg] at H
    exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
  · rw [ite_eq_right hneg] at H
    simp only [getModelSpec, bind_getModel] at H
    generalize hfd : fd_lookup (m_fds m) fd = lk at H ⊢
    cases lk with
    | none =>
      dsimp only at H
      exact absurd H (ret_only_no_unmodeled (errno_ret EBADF) i m)
    | some e =>
      cases e with
      | FdChannel ch =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdSocket sk =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdPipe id wr =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdDevNull rd wr =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdUrandom =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdFile p cur =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdDir =>
        dsimp only at H
        exact absurd H (ret_only_no_unmodeled (errno_ret EINVAL) i m)
      | FdFileA p cur =>
        dsimp only at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          rfl
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            rfl
          · rw [ite_eq_right hgap] at H
            exact absurd H (seqSpec_modify_ret_only_never_unmodeled _ _ i m)
      | FdFileW p cur =>
        dsimp only at H
        simp only [ftruncate_file_arm] at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          rfl
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            rfl
          · rw [ite_eq_right hgap] at H
            exact absurd H (seqSpec_modify_ret_only_never_unmodeled _ _ i m)
      | FdFileRW p cur =>
        dsimp only at H
        simp only [ftruncate_file_arm] at H
        rw [← hP]
        simp only [check_ftruncate, hneg, hfd]
        unfold check_ftruncate_file_arm
        generalize hfs : fs_lookup (m_fs m) p = lk2 at H ⊢
        cases lk2 with
        | none =>
          dsimp only at H ⊢
          rfl
        | some data =>
          dsimp only at H ⊢
          by_cases hgap : (!(modeled_truncate_gap data len)) = true
          · rw [ite_eq_left hgap] at H ⊢
            rfl
          · rw [ite_eq_right hgap] at H
            exact absurd H (seqSpec_modify_ret_only_never_unmodeled _ _ i m)

/- ==================================================== faccessat (48) -/

/-- An effect whose copy-in ledger is empty is its own
    [with_copyins []] — what lets the wrapper's [clear_copyins] be
    dropped once the body has proved the ledger empty. -/
private theorem with_copyins_nil_eq (eff : SyscallEffect) (h : eff.eff_copyins = []) :
    with_copyins [] eff = eff := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  simp only at h
  subst h
  rfl

/-- The acceptor for the arm of [Fs.Open.faccessat_spec] that can
    succeed: either 0 or an injectable errno, with NO state change
    either way — the two alternatives write the same model, which is
    what makes this syscall a pure observation — and FIVE EMPTY LEDGERS,
    since faccessat writes, zeroes, unmaps and copies out nothing, and
    the pathname copy-in is cleared by the wrapper before the body sees
    the effect.  So only a forged ledger reaches the other half of the
    claim. -/
def check_access_exists (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in faccessat_errnos ret || bv_eqb ret (BitVec.ofInt 64 0)
      then .CheckOk m []
      else .CheckReject
  | _ => .CheckReject

private def check_faccessat_body (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match read_cstr i.in_mem pathp with
  | .CstrTooLong => check_ret_only eff (errno_ret ENAMETOOLONG) m []
  | .CstrFault => check_ret_only eff (errno_ret EFAULT) m []
  | .CstrOk p =>
      if path_eqb p [] then check_ret_only eff (errno_ret ENOENT) m []
      else if !(bv_eqb dirfd AT_FDCWD32) then .CheckUnmodeled
      else if path_eqb p dot_path then check_access_exists eff m
      else if path_eqb p dotdot_path then check_access_exists eff m
      else if path_has_slash p then .CheckUnmodeled
      else if decide (NAME_MAX < p.length) then .CheckUnmodeled
      else if fs_under (m_fs m) p then .CheckUnmodeled
      else
      match fs_lookup (m_fs m) p with
      | none => check_ret_only eff (errno_ret ENOENT) m []
      | some _ => check_access_exists eff m

/-- The pathname copy-in, as [check_openat] and
    [Checks.Sys.Fs.Namei.check_unlinkat] check it: decide the body
    against the effect with the ledger cleared, then require the claimed
    ledger to be exactly that one range.  Both mode arms are outside the
    wrapper, mirroring the spec — the kernel decides the mode before
    [user_path_at], so an honest -EINVAL carries no copy-in at all. -/
def check_faccessat (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(modeled_access_mode mode)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(access_mode_f_ok mode) then .CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff
      (check_faccessat_body i dirfd pathp (clear_copyins eff) m)

/-- 0 is not an injectable errno, so [access_exists_spec]'s two
    alternatives never both have to be justified by the same return —
    though either would do, since both leave the model alone. -/
theorem errno_ret_in_faccessat_zero :
    errno_ret_in faccessat_errnos (BitVec.ofInt 64 0) = false := by
  apply errno_ret_in_fd
  · decide
  · decide

private theorem check_access_exists_sound_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_access_exists eff m = .CheckOk m' evs) :
    access_exists_spec i m (.ok eff m' evs) := by
  generalize hP : (access_exists_spec i m (.ok eff m' evs)) = Q at *
  unfold check_access_exists at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in faccessat_errnos ret = true
    · rw [ite_eq_left (by rw [he]; rfl)] at H
      cases H
      obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true faccessat_errnos ret).mp he
      subst hret
      rw [← hP]
      simp only [access_exists_spec]
      apply alt_l
      exact bind_ok0 (errno_from faccessat_errnos) (fun e => err_ret e) i m er m _ m []
        (choose_ok _ er i m hmem) (pure_ok _ i m)
    · have hf : errno_ret_in faccessat_errnos ret = false := by
        cases hv : errno_ret_in faccessat_errnos ret with
        | false => rfl
        | true => exact absurd hv he
      by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
      · rw [ite_eq_left (by rw [hf, hz]; rfl)] at H
        cases H
        have hret : ret = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq ret _).mp hz
        subst hret
        rw [← hP]
        simp only [access_exists_spec]
        exact alt_r _ _ i m _ (pure_ok _ i m)
      · have hzf : bv_eqb ret (BitVec.ofInt 64 0) = false := by
          cases hv : bv_eqb ret (BitVec.ofInt 64 0) with
          | false => rfl
          | true => exact absurd hv hz
        rw [ite_eq_right (by rw [hf, hzf]; decide)] at H
        exact nomatch H
  all_goals exact nomatch H

private theorem check_access_exists_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_access_exists eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    simp only [check_access_exists] at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in faccessat_errnos ret = true
    · rw [ite_eq_left (by rw [he]; rfl)] at H
      exact nomatch H
    · have hf : errno_ret_in faccessat_errnos ret = false := by
        cases hv : errno_ret_in faccessat_errnos ret with
        | false => rfl
        | true => exact absurd hv he
      by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
      · rw [ite_eq_left (by rw [hf, hz]; rfl)] at H
        exact nomatch H
      · have hzf : bv_eqb ret (BitVec.ofInt 64 0) = false := by
          cases hv : bv_eqb ret (BitVec.ofInt 64 0) with
          | false => rfl
          | true => exact absurd hv hz
        rw [ite_eq_right (by rw [hf, hzf]; decide)] at H
        exact nomatch H
  all_goals exact nomatch H

private theorem check_access_exists_complete_ok (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : access_exists_spec i m (.ok eff m' evs)) :
    check_access_exists eff m = .CheckOk m' evs := by
  unfold access_exists_spec at H
  rcases H with H1 | H2
  · obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
    obtain ⟨e0, hin, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨he1, he2, he3⟩ := heq
    rw [he1, he2] at her
    rw [he3] at hevs
    cases her
    simp only [List.nil_append] at hevs
    subst hevs
    unfold check_access_exists
    dsimp only
    rw [ite_eq_left (by simp [errno_ret_in_intro faccessat_errnos _ hin])]
  · cases H2
    unfold check_access_exists
    dsimp only
    rw [ite_eq_left (by simp [bv_eqb_refl])]

private theorem check_access_exists_ok_copyins_nil (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_access_exists eff m = .CheckOk m' evs) :
    eff.eff_copyins = [] := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil => rfl
  all_goals exact nomatch H

/-- The acceptor's alternatives both leave the model alone, so neither
    can decline. -/
private theorem access_exists_no_unmodeled (i : SyscallInput) (m : Model) :
    ¬ access_exists_spec i m .unmodeled := by
  intro H
  unfold access_exists_spec at H
  rcases H with H1 | H2
  · rcases H1 with hdecl | ⟨er, m1, evs1, hc, hk⟩
    · obtain ⟨e0, -, heq⟩ := hdecl
      exact nomatch heq
    · exact nomatch hk
  · exact nomatch H2

private theorem check_faccessat_body_sound_ok (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat_body i dirfd pathp eff m = .CheckOk m' evs) :
    faccessat_body_spec dirfd pathp i m i m (.ok eff m' evs) := by
  unfold check_faccessat_body at H
  unfold faccessat_body_spec
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong => exact check_ret_only_sound_ok i eff (errno_ret ENAMETOOLONG) m m' evs H
  | CstrFault => exact check_ret_only_sound_ok i eff (errno_ret EFAULT) m m' evs H
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H ⊢
          exact check_access_exists_sound_ok i eff m m' evs H
        · rw [ite_eq_right hdot] at H ⊢
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H ⊢
            exact check_access_exists_sound_ok i eff m m' evs H
          · rw [ite_eq_right hdd] at H ⊢
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H
              exact nomatch H
            · rw [ite_eq_right hsl] at H ⊢
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H
                exact nomatch H
              · rw [ite_eq_right hnm] at H ⊢
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H
                  exact nomatch H
                · rw [ite_eq_right hun] at H ⊢
                  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
                  cases lk with
                  | none =>
                    exact check_ret_only_sound_ok i eff (errno_ret ENOENT) m m' evs H
                  | some data => exact check_access_exists_sound_ok i eff m m' evs H

/-- [check_access_exists] is a pure observation — both of its
    accepting shapes answer the model they were given — so it leaves
    [m_vmmaps] alone. -/
private theorem check_access_exists_frame (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_access_exists eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_access_exists at H
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
    try dsimp only at H
  case nil.nil.nil.nil.nil =>
    by_cases he : errno_ret_in faccessat_errnos ret = true
    · rw [ite_eq_left (by rw [he]; rfl)] at H
      cases H
      rfl
    · have hf : errno_ret_in faccessat_errnos ret = false := by
        cases hv : errno_ret_in faccessat_errnos ret with
        | false => rfl
        | true => exact absurd hv he
      by_cases hz : bv_eqb ret (BitVec.ofInt 64 0) = true
      · rw [ite_eq_left (by rw [hf, hz]; rfl)] at H
        cases H
        rfl
      · have hzf : bv_eqb ret (BitVec.ofInt 64 0) = false := by
          cases hv : bv_eqb ret (BitVec.ofInt 64 0) with
          | false => rfl
          | true => exact absurd hv hz
        rw [ite_eq_right (by rw [hf, hzf]; decide)] at H
        exact nomatch H
  all_goals exact nomatch H

/-- Frame fact for [Checks/VmMapsDisjoint.lean]: the faccessat body is the
    same pure observation behind one pathname read, so it leaves [m_vmmaps]
    alone.  Public because the helper it is about is `private`; the walk is
    the checker side of [check_faccessat_body_sound_ok], with the spec
    dropped. -/
theorem check_faccessat_body_frame (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat_body i dirfd pathp eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_faccessat_body at H
  generalize hc : read_cstr i.in_mem pathp = cr at H
  cases cr with
  | CstrTooLong =>
    exact check_ret_only_frame eff (errno_ret ENAMETOOLONG) m m' evs H
  | CstrFault =>
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
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H
          exact check_access_exists_frame eff m m' evs H
        · rw [ite_eq_right hdot] at H
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H
            exact check_access_exists_frame eff m m' evs H
          · rw [ite_eq_right hdd] at H
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H
              exact nomatch H
            · rw [ite_eq_right hsl] at H
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H
                exact nomatch H
              · rw [ite_eq_right hnm] at H
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H
                  exact nomatch H
                · rw [ite_eq_right hun] at H
                  generalize hfs : fs_lookup (m_fs m) p = lk at H
                  cases lk with
                  | none => exact check_ret_only_frame eff (errno_ret ENOENT) m m' evs H
                  | some data => exact check_access_exists_frame eff m m' evs H

private theorem check_faccessat_body_sound_unmodeled (i : SyscallInput)
    (dirfd pathp : word) (eff : SyscallEffect) (m : Model)
    (H : check_faccessat_body i dirfd pathp eff m = .CheckUnmodeled) :
    faccessat_body_spec dirfd pathp i m i m .unmodeled := by
  unfold check_faccessat_body at H
  unfold faccessat_body_spec
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENAMETOOLONG) m [])
  | CstrFault =>
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hd] at H ⊢
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H
          exact absurd H (check_access_exists_no_unmodeled eff m)
        · rw [ite_eq_right hdot] at H ⊢
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H
            exact absurd H (check_access_exists_no_unmodeled eff m)
          · rw [ite_eq_right hdd] at H ⊢
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H ⊢
              exact unmodeled_intro i m
            · rw [ite_eq_right hsl] at H ⊢
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H ⊢
                exact unmodeled_intro i m
              · rw [ite_eq_right hnm] at H ⊢
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H ⊢
                  exact unmodeled_intro i m
                · rw [ite_eq_right hun] at H ⊢
                  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
                  cases lk with
                  | none =>
                    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOENT) m [])
                  | some data =>
                    exact absurd H (check_access_exists_no_unmodeled eff m)

private theorem check_faccessat_body_complete_ok (i : SyscallInput) (dirfd pathp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : faccessat_body_spec dirfd pathp i m i m (.ok eff m' evs)) :
    check_faccessat_body i dirfd pathp eff m = .CheckOk m' evs := by
  unfold faccessat_body_spec at H
  unfold check_faccessat_body
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact (check_ret_only_complete_ok i eff (errno_ret ENAMETOOLONG) m m' evs H).1
  | CstrFault =>
    exact (check_ret_only_complete_ok i eff (errno_ret EFAULT) m m' evs H).1
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H ⊢
      exact (check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H).1
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        simp only [unmodeled] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H ⊢
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H ⊢
          exact check_access_exists_complete_ok i eff m m' evs H
        · rw [ite_eq_right hdot] at H ⊢
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H ⊢
            exact check_access_exists_complete_ok i eff m m' evs H
          · rw [ite_eq_right hdd] at H ⊢
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H
              simp only [unmodeled] at H
              exact nomatch H
            · rw [ite_eq_right hsl] at H ⊢
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H
                simp only [unmodeled] at H
                exact nomatch H
              · rw [ite_eq_right hnm] at H ⊢
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H
                  simp only [unmodeled] at H
                  exact nomatch H
                · rw [ite_eq_right hun] at H ⊢
                  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
                  cases lk with
                  | none =>
                    exact (check_ret_only_complete_ok i eff (errno_ret ENOENT) m m' evs H).1
                  | some data => exact check_access_exists_complete_ok i eff m m' evs H

private theorem check_faccessat_body_complete_unmodeled (i : SyscallInput)
    (dirfd pathp : word) (m : Model) (eff : SyscallEffect)
    (H : faccessat_body_spec dirfd pathp i m i m .unmodeled) :
    check_faccessat_body i dirfd pathp eff m = .CheckUnmodeled := by
  unfold faccessat_body_spec at H
  unfold check_faccessat_body
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    exact absurd H (ret_only_no_unmodeled (errno_ret ENAMETOOLONG) i m)
  | CstrFault =>
    exact absurd H (ret_only_no_unmodeled (errno_ret EFAULT) i m)
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      exact absurd H (ret_only_no_unmodeled (errno_ret ENOENT) i m)
    · rw [ite_eq_right hpe] at H ⊢
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H ⊢
      · rw [ite_eq_right hd] at H ⊢
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H
          exact absurd H (access_exists_no_unmodeled i m)
        · rw [ite_eq_right hdot] at H ⊢
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H
            exact absurd H (access_exists_no_unmodeled i m)
          · rw [ite_eq_right hdd] at H ⊢
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H ⊢
            · rw [ite_eq_right hsl] at H ⊢
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H ⊢
              · rw [ite_eq_right hnm] at H ⊢
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H ⊢
                · rw [ite_eq_right hun] at H ⊢
                  generalize hfs : fs_lookup (m_fs m) p = lk at H ⊢
                  cases lk with
                  | none =>
                    exact absurd H (ret_only_no_unmodeled (errno_ret ENOENT) i m)
                  | some data =>
                    exact absurd H (access_exists_no_unmodeled i m)

/-- No arm of the body claims a copy-in of its own: each returns either
    through [check_ret_only], which forces every ledger empty, or
    through [check_access_exists], which matches six empty lists.  That
    is what lets the wrapper equate the WHOLE claimed ledger with the one
    pathname range rather than with a prefix of it. -/
private theorem check_faccessat_body_ok_copyins_nil (i : SyscallInput)
    (dirfd pathp : word) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat_body i dirfd pathp eff m = .CheckOk m' evs) :
    eff.eff_copyins = [] := by
  unfold check_faccessat_body at H
  generalize hc : read_cstr i.in_mem pathp = cr at H ⊢
  cases cr with
  | CstrTooLong =>
    obtain ⟨heff, -, -⟩ :=
      (check_ret_only_ok_iff eff (errno_ret ENAMETOOLONG) m [] m' evs).mp H
    subst heff
    rfl
  | CstrFault =>
    obtain ⟨heff, -, -⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
    subst heff
    rfl
  | CstrOk p =>
    dsimp only at H ⊢
    by_cases hpe : path_eqb p [] = true
    · rw [ite_eq_left hpe] at H
      obtain ⟨heff, -, -⟩ :=
        (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
      subst heff
      rfl
    · rw [ite_eq_right hpe] at H
      by_cases hd : (!(bv_eqb dirfd AT_FDCWD32)) = true
      · rw [ite_eq_left hd] at H
        exact nomatch H
      · rw [ite_eq_right hd] at H
        by_cases hdot : path_eqb p dot_path = true
        · rw [ite_eq_left hdot] at H
          exact check_access_exists_ok_copyins_nil eff m m' evs H
        · rw [ite_eq_right hdot] at H
          by_cases hdd : path_eqb p dotdot_path = true
          · rw [ite_eq_left hdd] at H
            exact check_access_exists_ok_copyins_nil eff m m' evs H
          · rw [ite_eq_right hdd] at H
            by_cases hsl : path_has_slash p = true
            · rw [ite_eq_left hsl] at H
              exact nomatch H
            · rw [ite_eq_right hsl] at H
              by_cases hnm : decide (NAME_MAX < p.length) = true
              · rw [ite_eq_left hnm] at H
                exact nomatch H
              · rw [ite_eq_right hnm] at H
                by_cases hun : fs_under (m_fs m) p = true
                · rw [ite_eq_left hun] at H
                  exact nomatch H
                · rw [ite_eq_right hun] at H
                  generalize hfs : fs_lookup (m_fs m) p = lk at H
                  cases lk with
                  | none =>
                    obtain ⟨heff, -, -⟩ :=
                      (check_ret_only_ok_iff eff (errno_ret ENOENT) m [] m' evs).mp H
                    subst heff
                    rfl
                  | some data => exact check_access_exists_ok_copyins_nil eff m m' evs H

/- ------------------------------------------------- the four exports -/

theorem check_faccessat_sound_ok (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat i dirfd pathp mode eff m = .CheckOk m' evs) :
    faccessat_spec dirfd pathp mode i m (.ok eff m' evs) := by
  unfold check_faccessat at H
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at H
    obtain ⟨heff, hm', hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    subst heff
    subst hevs
    rw [hm'] at *
    unfold faccessat_spec
    apply bind_ok0
    · exact input_ok i m
    · apply bind_ok0
      · exact getModel_ok i m
      · rw [ite_eq_left hmo]
        exact pure_ok _ i _
  · rw [ite_eq_right hmo] at H
    by_cases hf : (!(access_mode_f_ok mode)) = true
    · rw [ite_eq_left hf] at H
      exact nomatch H
    · rw [ite_eq_right hf] at H
      dsimp only at H
      obtain ⟨hreads, hbody⟩ := (check_copyins_after_ok_iff _ _ _ _ _).mp H
      unfold faccessat_spec
      apply bind_ok0
      · exact input_ok i m
      · apply bind_ok0
        · exact getModel_ok i m
        · rw [ite_eq_right hmo, ite_eq_right hf]
          exact record_copyins_clear_ok _ _ i m eff m' evs hreads
            (check_faccessat_body_sound_ok i dirfd pathp (clear_copyins eff) m m' evs hbody)

theorem check_faccessat_sound_unmodeled (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_faccessat i dirfd pathp mode eff m = .CheckUnmodeled) :
    faccessat_spec dirfd pathp mode i m .unmodeled := by
  unfold check_faccessat at H
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hmo] at H
    by_cases hf : (!(access_mode_f_ok mode)) = true
    · rw [ite_eq_left hf] at H
      unfold faccessat_spec
      apply bind_unmodeled2
      · exact input_ok i m
      · apply bind_unmodeled2
        · exact getModel_ok i m
        · rw [ite_eq_right hmo, ite_eq_left hf]
          exact unmodeled_intro i _
    · rw [ite_eq_right hf] at H
      dsimp only at H
      have hbody := check_copyins_after_unmodeled _ _ _ H
      unfold faccessat_spec
      apply bind_unmodeled2
      · exact input_ok i m
      · apply bind_unmodeled2
        · exact getModel_ok i m
        · rw [ite_eq_right hmo, ite_eq_right hf]
          exact record_copyins_unmodeled
            (check_faccessat_body_sound_unmodeled i dirfd pathp (clear_copyins eff) m hbody)

theorem check_faccessat_complete_ok (i : SyscallInput) (dirfd pathp mode : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : faccessat_spec dirfd pathp mode i m (.ok eff m' evs)) :
    check_faccessat i dirfd pathp mode eff m = .CheckOk m' evs := by
  unfold faccessat_spec at H
  have h1 := input_bind_ok_inv _ i m eff m' evs H
  simp only [getModelSpec, bind_getModel] at h1
  unfold check_faccessat
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at h1 ⊢
    cases h1
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hmo] at h1 ⊢
    by_cases hf : (!(access_mode_f_ok mode)) = true
    · rw [ite_eq_left hf] at h1
      simp only [unmodeled] at h1
      exact nomatch h1
    · rw [ite_eq_right hf] at h1 ⊢
      dsimp only at h1 ⊢
      obtain ⟨core, hcore, hEff⟩ := record_copyins_ok_inv _ _ i m eff m' evs h1
      subst hEff
      have hchk :=
        check_faccessat_body_complete_ok i dirfd pathp core m m' evs hcore
      have hnil :=
        check_faccessat_body_ok_copyins_nil i dirfd pathp core m m' evs hchk
      rw [check_copyins_after_ok_iff]
      refine ⟨?_, ?_⟩
      · simp [with_copyins, hnil]
      · have hcc : clear_copyins (with_copyins
            ([(pathp, cstr_access_len_aux i.in_mem pathp path_max)] ++ core.eff_copyins) core)
            = core := by
          simp only [clear_copyins, with_copyins]
          exact with_copyins_nil_eq core hnil
        rw [hcc]
        exact hchk

theorem check_faccessat_complete_unmodeled (i : SyscallInput) (dirfd pathp mode : word)
    (m : Model) (eff : SyscallEffect)
    (H : faccessat_spec dirfd pathp mode i m .unmodeled) :
    check_faccessat i dirfd pathp mode eff m = .CheckUnmodeled := by
  unfold faccessat_spec at H
  have h1 := input_bind_unmodeled_inv _ i m H
  simp only [getModelSpec, bind_getModel] at h1
  unfold check_faccessat
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at h1
    exact absurd h1 (ret_only_no_unmodeled (errno_ret EINVAL) i m)
  · rw [ite_eq_right hmo] at h1 ⊢
    by_cases hf : (!(access_mode_f_ok mode)) = true
    · rw [ite_eq_left hf] at h1 ⊢
    · rw [ite_eq_right hf] at h1 ⊢
      dsimp only at h1 ⊢
      have hbody := record_copyins_unmodeled_inv _ _ i m h1
      rw [check_faccessat_body_complete_unmodeled i dirfd pathp m (clear_copyins eff) hbody]
      rfl

/- =================================================== faccessat2 (439) -/

/-- The same body, under a wrapper with one more test.  [do_faccessat]
    is the shared function, so the acceptor differs from
    [check_faccessat] only in the two flag arms: the kernel's own -EINVAL
    for a bit outside the three it accepts, and the decline for
    AT_EMPTY_PATH.  Both sit outside the copy-in wrapper, mirroring the
    spec — neither reaches [user_path_at], so neither carries a ledger. -/
def check_faccessat2 (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(modeled_access_mode mode)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(valid_access_flags flags)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(modeled_access_flags flags) then .CheckUnmodeled
  else if !(access_mode_f_ok mode) then .CheckUnmodeled
  else
    let reads := [(pathp, cstr_access_len_aux i.in_mem pathp path_max)]
    check_copyins_after reads eff
      (check_faccessat_body i dirfd pathp (clear_copyins eff) m)

theorem check_faccessat2_sound_ok (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_faccessat2 i dirfd pathp mode flags eff m = .CheckOk m' evs) :
    faccessat2_spec dirfd pathp mode flags i m (.ok eff m' evs) := by
  unfold check_faccessat2 at H
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at H
    obtain ⟨heff, hm', hevs⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    subst heff
    subst hevs
    rw [hm'] at *
    unfold faccessat2_spec
    apply bind_ok0
    · exact input_ok i m
    · apply bind_ok0
      · exact getModel_ok i m
      · rw [ite_eq_left hmo]
        exact pure_ok _ i _
  · rw [ite_eq_right hmo] at H
    by_cases hfl : (!(valid_access_flags flags)) = true
    · rw [ite_eq_left hfl] at H
      obtain ⟨heff, hm', hevs⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      subst heff
      subst hevs
      rw [hm'] at *
      unfold faccessat2_spec
      apply bind_ok0
      · exact input_ok i m
      · apply bind_ok0
        · exact getModel_ok i m
        · rw [ite_eq_right hmo, ite_eq_left hfl]
          exact pure_ok _ i _
    · rw [ite_eq_right hfl] at H
      by_cases hmf : (!(modeled_access_flags flags)) = true
      · rw [ite_eq_left hmf] at H
        exact nomatch H
      · rw [ite_eq_right hmf] at H
        by_cases hf : (!(access_mode_f_ok mode)) = true
        · rw [ite_eq_left hf] at H
          exact nomatch H
        · rw [ite_eq_right hf] at H
          dsimp only at H
          obtain ⟨hreads, hbody⟩ := (check_copyins_after_ok_iff _ _ _ _ _).mp H
          unfold faccessat2_spec
          apply bind_ok0
          · exact input_ok i m
          · apply bind_ok0
            · exact getModel_ok i m
            · rw [ite_eq_right hmo, ite_eq_right hfl, ite_eq_right hmf, ite_eq_right hf]
              exact record_copyins_clear_ok _ _ i m eff m' evs hreads
                (check_faccessat_body_sound_ok i dirfd pathp (clear_copyins eff) m m' evs hbody)

theorem check_faccessat2_sound_unmodeled (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_faccessat2 i dirfd pathp mode flags eff m = .CheckUnmodeled) :
    faccessat2_spec dirfd pathp mode flags i m .unmodeled := by
  unfold check_faccessat2 at H
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hmo] at H
    by_cases hfl : (!(valid_access_flags flags)) = true
    · rw [ite_eq_left hfl] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hfl] at H
      by_cases hmf : (!(modeled_access_flags flags)) = true
      · rw [ite_eq_left hmf] at H
        unfold faccessat2_spec
        apply bind_unmodeled2
        · exact input_ok i m
        · apply bind_unmodeled2
          · exact getModel_ok i m
          · rw [ite_eq_right hmo, ite_eq_right hfl, ite_eq_left hmf]
            exact unmodeled_intro i _
      · rw [ite_eq_right hmf] at H
        by_cases hf : (!(access_mode_f_ok mode)) = true
        · rw [ite_eq_left hf] at H
          unfold faccessat2_spec
          apply bind_unmodeled2
          · exact input_ok i m
          · apply bind_unmodeled2
            · exact getModel_ok i m
            · rw [ite_eq_right hmo, ite_eq_right hfl, ite_eq_right hmf, ite_eq_left hf]
              exact unmodeled_intro i _
        · rw [ite_eq_right hf] at H
          dsimp only at H
          have hbody := check_copyins_after_unmodeled _ _ _ H
          unfold faccessat2_spec
          apply bind_unmodeled2
          · exact input_ok i m
          · apply bind_unmodeled2
            · exact getModel_ok i m
            · rw [ite_eq_right hmo, ite_eq_right hfl, ite_eq_right hmf, ite_eq_right hf]
              exact record_copyins_unmodeled
                (check_faccessat_body_sound_unmodeled i dirfd pathp (clear_copyins eff) m hbody)

theorem check_faccessat2_complete_ok (i : SyscallInput) (dirfd pathp mode flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : faccessat2_spec dirfd pathp mode flags i m (.ok eff m' evs)) :
    check_faccessat2 i dirfd pathp mode flags eff m = .CheckOk m' evs := by
  unfold faccessat2_spec at H
  have h1 := input_bind_ok_inv _ i m eff m' evs H
  simp only [getModelSpec, bind_getModel] at h1
  unfold check_faccessat2
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at h1 ⊢
    cases h1
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hmo] at h1 ⊢
    by_cases hfl : (!(valid_access_flags flags)) = true
    · rw [ite_eq_left hfl] at h1 ⊢
      cases h1
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hfl] at h1 ⊢
      by_cases hmf : (!(modeled_access_flags flags)) = true
      · rw [ite_eq_left hmf] at h1
        simp only [unmodeled] at h1
        exact nomatch h1
      · rw [ite_eq_right hmf] at h1 ⊢
        by_cases hf : (!(access_mode_f_ok mode)) = true
        · rw [ite_eq_left hf] at h1
          simp only [unmodeled] at h1
          exact nomatch h1
        · rw [ite_eq_right hf] at h1 ⊢
          dsimp only at h1 ⊢
          obtain ⟨core, hcore, hEff⟩ := record_copyins_ok_inv _ _ i m eff m' evs h1
          subst hEff
          have hchk :=
            check_faccessat_body_complete_ok i dirfd pathp core m m' evs hcore
          have hnil :=
            check_faccessat_body_ok_copyins_nil i dirfd pathp core m m' evs hchk
          rw [check_copyins_after_ok_iff]
          refine ⟨?_, ?_⟩
          · simp [with_copyins, hnil]
          · have hcc : clear_copyins (with_copyins
                ([(pathp, cstr_access_len_aux i.in_mem pathp path_max)] ++ core.eff_copyins) core)
                = core := by
              simp only [clear_copyins, with_copyins]
              exact with_copyins_nil_eq core hnil
            rw [hcc]
            exact hchk

theorem check_faccessat2_complete_unmodeled (i : SyscallInput) (dirfd pathp mode flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : faccessat2_spec dirfd pathp mode flags i m .unmodeled) :
    check_faccessat2 i dirfd pathp mode flags eff m = .CheckUnmodeled := by
  unfold faccessat2_spec at H
  have h1 := input_bind_unmodeled_inv _ i m H
  simp only [getModelSpec, bind_getModel] at h1
  unfold check_faccessat2
  by_cases hmo : (!(modeled_access_mode mode)) = true
  · rw [ite_eq_left hmo] at h1
    exact absurd h1 (ret_only_no_unmodeled (errno_ret EINVAL) i m)
  · rw [ite_eq_right hmo] at h1 ⊢
    by_cases hfl : (!(valid_access_flags flags)) = true
    · rw [ite_eq_left hfl] at h1
      exact absurd h1 (ret_only_no_unmodeled (errno_ret EINVAL) i m)
    · rw [ite_eq_right hfl] at h1 ⊢
      by_cases hmf : (!(modeled_access_flags flags)) = true
      · rw [ite_eq_left hmf] at h1 ⊢
      · rw [ite_eq_right hmf] at h1 ⊢
        by_cases hf : (!(access_mode_f_ok mode)) = true
        · rw [ite_eq_left hf] at h1 ⊢
        · rw [ite_eq_right hf] at h1 ⊢
          dsimp only at h1 ⊢
          have hbody := record_copyins_unmodeled_inv _ _ i m h1
          rw [check_faccessat_body_complete_unmodeled i dirfd pathp m (clear_copyins eff) hbody]
          rfl
