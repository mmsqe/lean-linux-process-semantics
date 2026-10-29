/-
  * LinuxProcessSem.Checks.Sys.Fs.File — the dup (23) and dup3 (24) checkers, and their proofs

  Answers to Linux [fs/file.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The two fd-allocation facts it needs from [Fs.Open] —
  [Open.alloc_fd_le] and [Open.errno_ret_in_alloc_fd], both proved there
  beside the [openat] acceptor that first needed them — are reproved below
  in a clearly marked section, so this module takes [Checks.Sys.Prelude]
  alone.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous
  constructor pattern `⟨r, [], [], [], [], []⟩` over `SyscallEffect`.

  The proofs `cases` the effect's five lists and close the thirty-one dead
  shapes with `exact nomatch H`.  Two steps deserve their own note.  A
  branch equation is rewritten with `simp only [hfd] at H` in each branch,
  since under a `match` the rewrite is what reduces the match too.  And
  `inv_ok`, the macro of `Checks.Sys.Prelude`, deliberately stops at
  constructor injectivities and one conjunction: the `alt`/`choose`/`bind`
  bodies of the two specs produce disjunctions and nested existentials, so
  the four completeness proofs spell the same inversion out with
  `rcases`/`obtain`, helped by the three private lemmas above.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.File

namespace LinuxSem.Checks.Sys.Fs.File

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.Checks.Sys.Prelude

/-- The acceptor for [File.dup_spec]'s allocating branch: the same
    shape as [Open.check_open_result], but over [dup_errnos] rather than
    [openat_errnos] — dup takes a second reference to an existing
    [struct file], so it can exhaust the fd table but never the
    system-wide open-file limit.

    Kept separate from that acceptor rather than sharing a common one
    taking the errno set: sharing costs a second [unfold] in every proof
    that consumes either — here, in [Common/FileSim.v]'s two lemmas
    about it, in [Common/FileMixSim.v], and in [Examples/cp_ns] — which
    is churn in a shared proof library and an example for a change about
    dup.  The two are one definition apart if that trade ever stops
    being worth it. -/
def check_dup_result (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in dup_errnos ret then .CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | some _ => .CheckReject
        | none => if bv_eqb ret (alloc_fd (m_fds m)) then .CheckOk (mk ret) []
                  else .CheckReject
  | _ => .CheckReject

/-- [dup]/[dup3]: the [FdFile]/[FdFileW] arms decline, because the
    model cannot represent two fds sharing one file offset, and dup3
    declines a free [newfd] at or above [Uapi.NR_OPEN_DEFAULT], where
    the answer turns on the descriptor table's size.  Kernel citations
    live on [File.dup_spec] and [File.dup3_spec]. -/
def check_dup (oldfd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match fd_lookup (m_fds m) oldfd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      if !(dup_modeled_entry e) then .CheckUnmodeled
      else check_dup_result eff m
             (fun fd => with_fds (fd_insert (m_fds m) fd e) m)

def check_dup3 (oldfd newfd flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(dup3_flags_ok flags) then check_ret_only eff (errno_ret EINVAL) m []
  else if bv_eqb oldfd newfd then check_ret_only eff (errno_ret EINVAL) m []
  else if !(dup3_newfd_under_limit newfd m)
       then check_ret_only eff (errno_ret EBADF) m []
  else
    match fd_lookup (m_fds m) oldfd with
    | none => check_ret_only eff (errno_ret EBADF) m []
    | some e =>
        if !(dup_modeled_entry e) then .CheckUnmodeled
        else
          match fd_lookup (m_fds m) newfd with
          | none =>
              if decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT)
              then check_ret_only eff newfd
                     (with_fds (fd_insert (m_fds m) newfd e) m) []
              else .CheckUnmodeled
          | some _ =>
              check_ret_only eff newfd
                (with_fds (fd_insert (m_fds m) newfd e) m) []

/- =========================================================================
   Private helpers, the fd facts restated from `Sys.Fs.Open`
   =========================================================================

   This module's spec cites [Open.alloc_fd_le] and
   [Open.errno_ret_in_alloc_fd], and `Checks/Sys/Fs/Open.lean` defines
   both.  The copies here use the same statements and the same proofs, so
   they are kept under the local
   names; a future pass can delete them, import `Checks.Sys.Fs.Open` and
   cite `Open.*`.

   The three lemmas after them state facts the four theorems below need as
   separate statements: a `bind` over `choose`/`alt`/`modify` produces
   existentials and disjunctions that `inv_ok` deliberately does not
   touch.  They are named after what they say and are used once each. -/

/-- The failure arm of `dup` never declines, either: it draws its errno
    from a `choose` and returns it, and the success arm only writes and
    returns.  Stated here because `inv_ok` would consume it inline. -/
theorem dup_alt_unmodeled_false (fds : List (word × FdEntry)) (e : FdEntry)
    (i : SyscallInput) (m : Model) :
    ¬ alt (bind (errno_from dup_errnos) (fun er => err_ret er))
        (bind (lowest_fd fds) (fun fd =>
          seqSpec (modifySpec (with_fds (fd_insert fds fd e))) (ret_only fd)))
      i m .unmodeled := by
  intro H
  rcases H with H1 | H2
  · rcases H1 with hdecl | hrest
    · obtain ⟨er, -, heq⟩ := hdecl
      exact nomatch heq
    · obtain ⟨x, m1, evs1, hc, hk⟩ := hrest
      exact nomatch hk
  · rcases H2 with hdecl | hrest
    · obtain ⟨fd', -, heq⟩ := hdecl
      exact nomatch heq
    · obtain ⟨fd, m1, evs1, hlow, hk⟩ := hrest
      exact absurd hk (seqSpec_modify_ret_only_never_unmodeled
        (fun mm => with_fds (fd_insert fds fd e) mm) fd i m1)

/- =========================================================================
   dup (23)
   ========================================================================= -/

theorem check_dup_sound_ok (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_dup oldfd eff m = .CheckOk m' evs) :
    dup_spec oldfd i m (.ok eff m' evs) := by
  generalize hP : (dup_spec oldfd i m (.ok eff m' evs)) = Q at *
  simp only [check_dup] at H
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
    rw [← hP]
    simp only [dup_spec, getModelSpec, bind_getModel, hfd, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  | some e =>
    simp only [hfd] at H
    by_cases hk : Bool.not (dup_modeled_entry e) = true
    · rw [ite_eq_left hk] at H
      exact nomatch H
    · rw [ite_eq_right hk] at H
      obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
      cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
        simp only [check_dup_result] at H
      case nil.nil.nil.nil.nil =>
        rw [← hP]
        simp only [dup_spec, getModelSpec, bind_getModel, hfd, ite_eq_right hk]
        by_cases he : errno_ret_in dup_errnos ret = true
        · rw [ite_eq_left he] at H
          cases H
          obtain ⟨er, hmem, hret⟩ := (errno_ret_in_true dup_errnos ret).mp he
          subst hret
          refine alt_l _ _ i m (.ok (mkEffect (errno_ret er) [] []) m []) ?_
          refine bind_ok0 (errno_from dup_errnos) (fun er' => err_ret er') i m er m _ m [] ?_ ?_
          · exact choose_ok (fun e => e ∈ dup_errnos) er i m hmem
          · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
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
              refine alt_r _ _ i m (.ok (mkEffect (alloc_fd (m_fds m)) [] [])
                (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e) m) []) ?_
              refine bind_ok0 (lowest_fd (m_fds m))
                (fun fd => seqSpec (modifySpec (with_fds (fd_insert (m_fds m) fd e)))
                  (ret_only fd))
                i m (alloc_fd (m_fds m)) m (mkEffect (alloc_fd (m_fds m)) [] [])
                (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e) m) [] ?_ ?_
              · refine choose_ok
                  (fun fd => fd_lookup (m_fds m) fd = none ∧ fd = alloc_fd (m_fds m))
                  (alloc_fd (m_fds m)) i m ⟨?_, rfl⟩
                simpa using hfr
              · exact bind_ok (modifySpec
                  (with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e)))
                  (fun _ => ret_only (alloc_fd (m_fds m))) i m () _ [] _ _ [] rfl rfl
            · rw [ite_eq_right heq] at H
              exact nomatch H
      all_goals exact nomatch H

theorem check_dup_sound_unmodeled (oldfd : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_dup oldfd eff m = .CheckUnmodeled) :
    dup_spec oldfd i m .unmodeled := by
  generalize hP : (dup_spec oldfd i m .unmodeled) = Q at *
  simp only [check_dup] at H
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    simp only [hfd] at H
    by_cases hk : Bool.not (dup_modeled_entry e) = true
    · rw [ite_eq_left hk] at H
      rw [← hP]
      simp only [dup_spec, getModelSpec, bind_getModel, hfd, ite_eq_left hk, unmodeled]
    · rw [ite_eq_right hk] at H
      obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
      cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
        simp only [check_dup_result] at H
      case nil.nil.nil.nil.nil =>
        split at H
        · exact nomatch H
        · split at H
          · exact nomatch H
          · split at H <;> exact nomatch H
      all_goals exact nomatch H

theorem check_dup_complete_ok (oldfd : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : dup_spec oldfd i m (.ok eff m' evs)) :
    check_dup oldfd eff m = .CheckOk m' evs := by
  generalize hP : (check_dup oldfd eff m = .CheckOk m' evs) = Q at *
  simp only [dup_spec, getModelSpec, bind_getModel] at H
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_dup, hfd]
    simp [check_ret_only, bv_eqb_refl]
  | some e =>
    simp only [hfd] at H
    by_cases hk : Bool.not (dup_modeled_entry e) = true
    · rw [ite_eq_left hk] at H
      simp only [unmodeled] at H
      exact nomatch H
    · rw [ite_eq_right hk] at H
      rw [← hP]
      simp only [check_dup, hfd, ite_eq_right hk]
      rcases H with H1 | H2
      · -- the injected errno
        obtain ⟨er, m1, evs1, evs2, hc, her, hevs⟩ := H1
        obtain ⟨er0, hin, heq⟩ := hc
        simp only [Outcome.ok.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        cases her
        simp only [List.nil_append] at hevs
        subst hevs
        simp only [check_dup_result]
        rw [ite_eq_left (errno_ret_in_intro dup_errnos _ hin)]
      · -- success: the lowest free fd
        obtain ⟨fd, m1, evs1, evs2, hlow, hk', hevs⟩ := H2
        obtain ⟨x, ⟨hfree, hx⟩, heq⟩ := hlow
        cases heq
        subst hx
        obtain ⟨heff, hm', hevs'⟩ := seqSpec_modify_ret_only_inv
          (fun mm => with_fds (fd_insert (m_fds m) (alloc_fd (m_fds m)) e) mm)
          (alloc_fd (m_fds m)) i m eff m' evs2 hk'
        subst heff
        subst hm'
        subst hevs'
        simp only [List.nil_append] at hevs
        subst hevs
        simp only [check_dup_result]
        rw [errno_ret_in_alloc_fd dup_errnos (m_fds m) (by decide)]
        rw [ite_eq_right (by simp)]
        rw [hfree, ite_eq_left (bv_eqb_refl _)]

theorem check_dup_complete_unmodeled (oldfd : word) (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : dup_spec oldfd i m .unmodeled) :
    check_dup oldfd eff m = .CheckUnmodeled := by
  generalize hP : (check_dup oldfd eff m = .CheckUnmodeled) = Q at *
  simp only [dup_spec, getModelSpec, bind_getModel] at H
  cases hfd : fd_lookup (m_fds m) oldfd with
  | none =>
    simp only [hfd] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | some e =>
    simp only [hfd] at H
    by_cases hk : Bool.not (dup_modeled_entry e) = true
    · rw [ite_eq_left hk] at H
      rw [← hP]
      simp only [check_dup, hfd, ite_eq_left hk]
    · rw [ite_eq_right hk] at H
      exact absurd H (dup_alt_unmodeled_false (m_fds m) e i m)

/- =========================================================================
   dup3 (24)
   ========================================================================= -/

theorem check_dup3_sound_ok (oldfd newfd flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_dup3 oldfd newfd flags eff m = .CheckOk m' evs) :
    dup3_spec oldfd newfd flags i m (.ok eff m' evs) := by
  generalize hP : (dup3_spec oldfd newfd flags i m (.ok eff m' evs)) = Q at *
  simp only [check_dup3] at H
  by_cases hf : Bool.not (dup3_flags_ok flags) = true
  · rw [ite_eq_left hf] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    rw [← hP]
    simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_left hf, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure]
  · rw [ite_eq_right hf] at H
    by_cases hne : bv_eqb oldfd newfd = true
    · rw [ite_eq_left hne] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      rw [← hP]
      simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_left hne, err_ret,
        ret_only, LinuxSem.LinuxProcessSem.pure]
    · rw [ite_eq_right hne] at H
      by_cases hl : Bool.not (dup3_newfd_under_limit newfd m) = true
      · rw [ite_eq_left hl] at H
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
        rw [← hP]
        simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
          ite_eq_left hl, err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right hl] at H
        cases hfd : fd_lookup (m_fds m) oldfd with
        | none =>
          simp only [hfd] at H
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EBADF) m [] m' evs).mp H
          rw [← hP]
          simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
            ite_eq_right hl, hfd, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure]
        | some e =>
          simp only [hfd] at H
          by_cases hk : Bool.not (dup_modeled_entry e) = true
          · rw [ite_eq_left hk] at H
            exact nomatch H
          · rw [ite_eq_right hk] at H
            cases hnf : fd_lookup (m_fds m) newfd with
            | some x =>
              simp only [hnf] at H
              obtain ⟨rfl, rfl, rfl⟩ :=
                (check_ret_only_ok_iff eff newfd
                  (with_fds (fd_insert (m_fds m) newfd e) m) [] m' evs).mp H
              rw [← hP]
              simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
                ite_eq_right hl, hfd, ite_eq_right hk, hnf]
              exact bind_ok (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                (fun _ => ret_only newfd) i m () _ [] _ _ [] rfl rfl
            | none =>
              simp only [hnf] at H
              by_cases hb : decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) = true
              · rw [ite_eq_left hb] at H
                obtain ⟨rfl, rfl, rfl⟩ :=
                  (check_ret_only_ok_iff eff newfd
                    (with_fds (fd_insert (m_fds m) newfd e) m) [] m' evs).mp H
                rw [← hP]
                simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
                  ite_eq_right hl, hfd, ite_eq_right hk, hnf, ite_eq_left hb]
                exact bind_ok (modifySpec (with_fds (fd_insert (m_fds m) newfd e)))
                  (fun _ => ret_only newfd) i m () _ [] _ _ [] rfl rfl
              · rw [ite_eq_right hb] at H
                exact nomatch H

theorem check_dup3_sound_unmodeled (oldfd newfd flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_dup3 oldfd newfd flags eff m = .CheckUnmodeled) :
    dup3_spec oldfd newfd flags i m .unmodeled := by
  generalize hP : (dup3_spec oldfd newfd flags i m .unmodeled) = Q at *
  simp only [check_dup3] at H
  by_cases hf : Bool.not (dup3_flags_ok flags) = true
  · rw [ite_eq_left hf] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hf] at H
    by_cases hne : bv_eqb oldfd newfd = true
    · rw [ite_eq_left hne] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right hne] at H
      by_cases hl : Bool.not (dup3_newfd_under_limit newfd m) = true
      · rw [ite_eq_left hl] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
      · rw [ite_eq_right hl] at H
        cases hfd : fd_lookup (m_fds m) oldfd with
        | none =>
          simp only [hfd] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
        | some e =>
          simp only [hfd] at H
          by_cases hk : Bool.not (dup_modeled_entry e) = true
          · rw [ite_eq_left hk] at H
            rw [← hP]
            simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
              ite_eq_right hl, hfd, ite_eq_left hk, unmodeled]
          · rw [ite_eq_right hk] at H
            cases hnf : fd_lookup (m_fds m) newfd with
            | some x =>
              simp only [hnf] at H
              exact absurd H
                (check_ret_only_no_unmodeled eff newfd
                  (with_fds (fd_insert (m_fds m) newfd e) m) [])
            | none =>
              simp only [hnf] at H
              by_cases hb : decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) = true
              · rw [ite_eq_left hb] at H
                exact absurd H
                  (check_ret_only_no_unmodeled eff newfd
                    (with_fds (fd_insert (m_fds m) newfd e) m) [])
              · rw [ite_eq_right hb] at H
                rw [← hP]
                simp only [dup3_spec, getModelSpec, bind_getModel, ite_eq_right hf, ite_eq_right hne,
                  ite_eq_right hl, hfd, ite_eq_right hk, hnf, ite_eq_right hb, unmodeled]

theorem check_dup3_complete_ok (oldfd newfd flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : dup3_spec oldfd newfd flags i m (.ok eff m' evs)) :
    check_dup3 oldfd newfd flags eff m = .CheckOk m' evs := by
  generalize hP : (check_dup3 oldfd newfd flags eff m = .CheckOk m' evs) = Q at *
  simp only [dup3_spec, getModelSpec, bind_getModel] at H
  by_cases hf : Bool.not (dup3_flags_ok flags) = true
  · rw [ite_eq_left hf] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨rfl, rfl, rfl⟩ := H
    rw [← hP]
    simp only [check_dup3, ite_eq_left hf]
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hf] at H
    by_cases hne : bv_eqb oldfd newfd = true
    · rw [ite_eq_left hne] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      rw [← hP]
      simp only [check_dup3, ite_eq_right hf, ite_eq_left hne]
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right hne] at H
      by_cases hl : Bool.not (dup3_newfd_under_limit newfd m) = true
      · rw [ite_eq_left hl] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        rw [← hP]
        simp only [check_dup3, ite_eq_right hf, ite_eq_right hne, ite_eq_left hl]
        simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hl] at H
        cases hfd : fd_lookup (m_fds m) oldfd with
        | none =>
          simp only [hfd] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at H
          obtain ⟨rfl, rfl, rfl⟩ := H
          rw [← hP]
          simp only [check_dup3, ite_eq_right hf, ite_eq_right hne, ite_eq_right hl, hfd]
          simp [check_ret_only, bv_eqb_refl]
        | some e =>
          simp only [hfd] at H
          by_cases hk : Bool.not (dup_modeled_entry e) = true
          · rw [ite_eq_left hk] at H
            simp only [unmodeled] at H
            exact nomatch H
          · rw [ite_eq_right hk] at H
            rw [← hP]
            simp only [check_dup3, ite_eq_right hf, ite_eq_right hne, ite_eq_right hl, hfd, ite_eq_right hk]
            cases hnf : fd_lookup (m_fds m) newfd with
            | some x =>
              simp only [hnf] at H
              obtain ⟨heff, hm', hevs'⟩ := seqSpec_modify_ret_only_inv
                (fun mm => with_fds (fd_insert (m_fds m) newfd e) mm) newfd i m eff m' evs H
              subst heff
              subst hm'
              subst hevs'
              simp [check_ret_only, bv_eqb_refl]
            | none =>
              simp only [hnf] at H
              by_cases hb : decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) = true
              · rw [ite_eq_left hb] at H
                obtain ⟨heff, hm', hevs'⟩ := seqSpec_modify_ret_only_inv
                  (fun mm => with_fds (fd_insert (m_fds m) newfd e) mm) newfd i m eff m' evs H
                subst heff
                subst hm'
                subst hevs'
                rw [ite_eq_left hb]
                simp [check_ret_only, bv_eqb_refl]
              · rw [ite_eq_right hb] at H
                simp only [unmodeled] at H
                exact nomatch H

theorem check_dup3_complete_unmodeled (oldfd newfd flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : dup3_spec oldfd newfd flags i m .unmodeled) :
    check_dup3 oldfd newfd flags eff m = .CheckUnmodeled := by
  generalize hP : (check_dup3 oldfd newfd flags eff m = .CheckUnmodeled) = Q at *
  simp only [dup3_spec, getModelSpec, bind_getModel] at H
  by_cases hf : Bool.not (dup3_flags_ok flags) = true
  · rw [ite_eq_left hf] at H
    simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  · rw [ite_eq_right hf] at H
    by_cases hne : bv_eqb oldfd newfd = true
    · rw [ite_eq_left hne] at H
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    · rw [ite_eq_right hne] at H
      by_cases hl : Bool.not (dup3_newfd_under_limit newfd m) = true
      · rw [ite_eq_left hl] at H
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      · rw [ite_eq_right hl] at H
        cases hfd : fd_lookup (m_fds m) oldfd with
        | none =>
          simp only [hfd] at H
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H
          exact nomatch H
        | some e =>
          simp only [hfd] at H
          by_cases hk : Bool.not (dup_modeled_entry e) = true
          · rw [ite_eq_left hk] at H
            rw [← hP]
            simp only [check_dup3, ite_eq_right hf, ite_eq_right hne, ite_eq_right hl, hfd, ite_eq_left hk]
          · rw [ite_eq_right hk] at H
            rw [← hP]
            cases hnf : fd_lookup (m_fds m) newfd with
            | some x =>
              simp only [hnf] at H
              exact absurd H
                (seqSpec_modify_ret_only_never_unmodeled
                  (fun mm => with_fds (fd_insert (m_fds m) newfd e) mm) newfd i m)
            | none =>
              simp only [hnf] at H
              by_cases hb : decide ((newfd.toNat : Int) < NR_OPEN_DEFAULT) = true
              · rw [ite_eq_left hb] at H
                exact absurd H
                  (seqSpec_modify_ret_only_never_unmodeled
                    (fun mm => with_fds (fd_insert (m_fds m) newfd e) mm) newfd i m)
              · rw [ite_eq_right hb] at H
                simp only [check_dup3, ite_eq_right hf, ite_eq_right hne, ite_eq_right hl, hfd, ite_eq_right hk,
                  hnf, ite_eq_right hb]

/- =========================================================================
   Sanity checks (not library lemmas)
   =========================================================================

   The module's proofs contain no `vm_compute` goal — it is the three
   checkers above, their prose, and the eight proofs.  The checks below
   pin the branch order those proofs follow, one per claim the matching
   spec's prose makes: a closed fd is -EBADF, a [FdFile] entry declines,
   a modeled entry hands the answer to the acceptor, the acceptor takes
   an injectable errno or the allocator's fd, and [check_dup3] tests
   flags, equality, the limit and [oldfd] in the kernel's order.

   They are sanity checks, not library lemmas.  `check_result` carries no
   `DecidableEq`, so each states the branch as an equation and closes it
   by unfolding the checker and discharging the tests with `decide`. -/

/-- A three-descriptor table: 0 a channel, 1 a directory, 2 a regular
    file.  Descriptors 3 and up are free. -/
private def portFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdDir), (2, FdEntry.FdFile [] 0)]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt, and the default
    RLIMIT_NOFILE. -/
private def portModel : Model :=
  mkModel portFds (mkVmMaps [] [] 0 0 0) IEof []

/-- A closed `oldfd` is -EBADF. -/
example (eff : SyscallEffect) :
    check_dup 9 eff portModel = check_ret_only eff (errno_ret EBADF) portModel [] := by
  have hlook : fd_lookup (m_fds portModel) 9 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_dup, hlook]

/-- A [FdFile] entry declines: the model cannot give two fds independent
    offsets, so it answers nothing rather than something wrong. -/
example (eff : SyscallEffect) : check_dup 2 eff portModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds portModel) 2 = some (FdEntry.FdFile [] 0) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_dup, hlook]
  rw [ite_eq_left (by decide : Bool.not (dup_modeled_entry (FdEntry.FdFile [] 0)) = true)]

/-- A modeled entry hands the accepted effect to the allocating acceptor,
    with the state the caller's new fd would be installed in. -/
example (eff : SyscallEffect) :
    check_dup 0 eff portModel = check_dup_result eff portModel
      (fun fd => with_fds (fd_insert (m_fds portModel) fd (FdEntry.FdChannel 7))
        portModel) := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_dup, hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]

/-- An injectable errno is accepted, leaving the model alone. -/
example :
    check_dup_result (mkEffect (errno_ret ENOMEM) [] []) portModel
      (fun _ => portModel) = .CheckOk portModel [] := by
  simp only [check_dup_result]
  rw [ite_eq_left (errno_ret_in_intro dup_errnos ENOMEM (by decide))]

/-- The allocator's own fd is accepted, installing the duplicated entry at
    it — `dup`'s success arm. -/
example :
    check_dup_result (mkEffect 3 [] []) portModel
      (fun fd => with_fds (fd_insert (m_fds portModel) fd (FdEntry.FdChannel 7))
        portModel)
      = .CheckOk (with_fds (fd_insert (m_fds portModel) 3 (FdEntry.FdChannel 7))
        portModel) [] := by
  have hfree : fd_lookup (m_fds portModel) 3 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have halloc : alloc_fd (m_fds portModel) = 3 := by decide
  have hfalse : errno_ret_in dup_errnos (3 : word) = false :=
    errno_ret_in_fd dup_errnos 3 (by decide) (by decide)
  simp only [check_dup_result, hfalse]
  rw [ite_eq_right (by simp)]
  rw [hfree, halloc, ite_eq_left (bv_eqb_refl _)]

/-- An fd that is NOT the allocator's answer is rejected. -/
example :
    check_dup_result (mkEffect 4 [] []) portModel (fun _ => portModel) = .CheckReject := by
  have hfree : fd_lookup (m_fds portModel) 4 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have halloc : alloc_fd (m_fds portModel) = 3 := by decide
  have hfalse : errno_ret_in dup_errnos (4 : word) = false :=
    errno_ret_in_fd dup_errnos 4 (by decide) (by decide)
  have hne : bv_eqb (4 : word) (alloc_fd (m_fds portModel)) = false := by
    rw [halloc]
    decide
  simp only [check_dup_result, hfalse]
  rw [ite_eq_right (by simp)]
  rw [hfree, hne]
  simp

/-- dup3 rejects equal descriptors with -EINVAL before any validity test:
    fd 9 is closed, and `dup3 9 9 0` is still -EINVAL rather than -EBADF. -/
example (eff : SyscallEffect) :
    check_dup3 9 9 0 eff portModel = check_ret_only eff (errno_ret EINVAL) portModel [] := by
  simp only [check_dup3]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_left (by decide : bv_eqb (9 : word) 9 = true)]

/-- A flag bit other than O_CLOEXEC is -EINVAL, before the fd tests. -/
example (eff : SyscallEffect) :
    check_dup3 1 4 1 eff portModel = check_ret_only eff (errno_ret EINVAL) portModel [] := by
  simp only [check_dup3]
  rw [ite_eq_left (by decide : Bool.not (dup3_flags_ok (1 : word)) = true)]

/-- `newfd` at or above RLIMIT_NOFILE is -EBADF. -/
example (eff : SyscallEffect) :
    check_dup3 1 2000 0 eff portModel
      = check_ret_only eff (errno_ret EBADF) portModel [] := by
  simp only [check_dup3]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (1 : word) 2000 = true))]
  rw [ite_eq_left (by decide : Bool.not (dup3_newfd_under_limit (2000 : word) portModel) = true)]

/-- An open `newfd` is overwritten with `oldfd`'s entry, and `newfd` is
    returned. -/
example (eff : SyscallEffect) :
    check_dup3 0 1 0 eff portModel
      = check_ret_only eff 1
          (with_fds (fd_insert (m_fds portModel) 1 (FdEntry.FdChannel 7)) portModel) [] := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have hnew : fd_lookup (m_fds portModel) 1 = some FdEntry.FdDir := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_dup3]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (0 : word) 1 = true))]
  rw [ite_eq_right (by decide :
    ¬(Bool.not (dup3_newfd_under_limit (1 : word) portModel) = true))]
  simp only [hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]
  simp only [hnew]

/-- A free `newfd` at or above `NR_OPEN_DEFAULT` is declined, not answered:
    `expand_files` would have to consult state the model does not carry. -/
example (eff : SyscallEffect) : check_dup3 0 70 0 eff portModel = .CheckUnmodeled := by
  have hlook : fd_lookup (m_fds portModel) 0 = some (FdEntry.FdChannel 7) := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  have hnew : fd_lookup (m_fds portModel) 70 = none := by
    simp [m_fds, portModel, mkModel, portFds, fd_lookup]
  simp only [check_dup3]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup3_flags_ok (0 : word)) = true))]
  rw [ite_eq_right (by decide : ¬(bv_eqb (0 : word) 70 = true))]
  rw [ite_eq_right (by decide :
    ¬(Bool.not (dup3_newfd_under_limit (70 : word) portModel) = true))]
  simp only [hlook]
  rw [ite_eq_right (by decide : ¬(Bool.not (dup_modeled_entry (FdEntry.FdChannel 7)) = true))]
  simp only [hnew]
  rw [ite_eq_right (by decide :
    ¬(decide (((70 : word).toNat : Int) < NR_OPEN_DEFAULT) = true))]

end LinuxSem.Checks.Sys.Fs.File





