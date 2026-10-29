/-
  * LinuxProcessSem.Checks.Sys.Kernel.Fork — the set_tid_address (96), clone (220) and clone3 (435) checkers, and their proofs

  Answers to Linux [kernel/fork.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and the two range tests are
  `decide (0 < …) && decide (… < …)` — `decide` is how a `Bool` comparison
  is spelled here.  An effect literal is the anonymous constructor pattern
  `⟨r, [], [], [], [], []⟩` over `SyscallEffect`, and a singleton copy-in
  ledger `((a, n) :: nil)` is the list literal `[(a, n)]`.

  The proofs `cases` the effect's five lists and close the dead shapes with
  `exact nomatch H`.  The spec's model reader is peeled with
  `bind_getModel` (rewrite `bind getModel k i m o` to `k m i m o` in one
  go), and the monadic `alt`/`choose`/`modify` bodies are inverted with
  explicit `rcases`/`obtain`, because `inv_ok` deliberately stops at
  constructor injectivities and one conjunction.

  A handful of steps that `inv_ok` and `dsimp` perform inline elsewhere
  have no direct counterpart here: an `alt`/`choose`/`seqSpec` body
  produces existentials and disjunctions, and `if`/`match` terms only
  reduce once their scrutinee is decided.  Those steps are named and proved
  once in the section that follows the checkers, and the four theorems that
  need them cite them.  They add no public surface.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork

namespace LinuxSem.Checks.Sys.Kernel.Fork

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Prelude

/-! ## set_tid_address (96) -/

/-- [set_tid_address]: the caller's tid, either the one already recorded
    in [m_tid] or — on the first call — any positive value below
    [PID_MAX_ENVELOPE], which is then recorded.  [Kernel.Fork]'s
    [set_tid_address_spec] picks the same envelope and the same
    once-only recording, and its header says why the argument is
    ignored. -/
def check_set_tid_address (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      match m_tid m with
      | some tid => if bv_eqb ret tid then .CheckOk m [] else .CheckReject
      | none =>
          if decide (0 < (ret.toNat : Int)) &&
             decide ((ret.toNat : Int) < PID_MAX_ENVELOPE)
          then .CheckOk (with_tid ret m) [] else .CheckReject
  | _ => .CheckReject

/- =========================================================================
   Private helpers

   These name the steps performed inline elsewhere — the `inv_ok`
   reduction and the iota step — so the theorems below can share them.
   None of them leaves this file, and each is used by a proof that would
   otherwise write the whole chain out.
   ========================================================================= -/

/-- Invert one `seqSpec (modifySpec f) (ret_only r)` step: the effect is
    the single return [r], the model is [f m], and nothing is emitted. -/
theorem seqSpec_modify_ret_only_inv (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : seqSpec (modifySpec f) (ret_only r) i m (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = f m ∧ evs = [] := by
  obtain ⟨u, m2, evs1, evs2, hm, hr, hevs⟩ := H
  cases hm
  cases hr
  simp only [List.nil_append] at hevs
  exact ⟨rfl, rfl, hevs⟩

/-- …and that the same step never declines: both halves are a state write
    and a `pure`. -/
theorem seqSpec_modify_ret_only_no_unmodeled (f : Model → Model) (r : word)
    (i : SyscallInput) (m : Model) :
    ¬ seqSpec (modifySpec f) (ret_only r) i m .unmodeled := by
  intro H
  rcases H with h | ⟨u, m1, evs1, h, hk⟩
  · simp only [modifySpec, LinuxSem.LinuxProcessSem.modify] at h
    exact nomatch h
  · simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at hk
    exact nomatch hk

/-- An environment choice always answers. -/
theorem choose_no_unmodeled {A : Type} (P : A → Prop) (i : SyscallInput)
    (m : Model) :
    ¬ choose (M := Model) (I := SyscallInput) (E := event) P i m .unmodeled := by
  rintro ⟨x, -, h⟩
  exact nomatch h

/-- The `set_tid_address` checker never declines: both arms of both
    branches answer `CheckOk` or `CheckReject`. -/
theorem check_set_tid_address_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_set_tid_address eff m ≠ .CheckUnmodeled := by
  intro H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_set_tid_address] at H
  case nil.nil.nil.nil.nil =>
    cases htid : m_tid m with
    | some tid =>
      simp only [htid] at H
      by_cases hr : bv_eqb ret tid = true
      · rw [ite_eq_left hr] at H
        exact nomatch H
      · rw [ite_eq_right hr] at H
        exact nomatch H
    | none =>
      simp only [htid] at H
      by_cases hv : (decide (0 < (ret.toNat : Int)) &&
          decide ((ret.toNat : Int) < PID_MAX_ENVELOPE)) = true
      · rw [ite_eq_left hv] at H
        exact nomatch H
      · rw [ite_eq_right hv] at H
        exact nomatch H
  all_goals exact nomatch H

/-- …and neither does [set_tid_address_spec]. -/
theorem set_tid_address_spec_no_unmodeled (i : SyscallInput) (m : Model) :
    ¬ set_tid_address_spec i m .unmodeled := by
  intro H
  simp only [set_tid_address_spec, getModelSpec, bind_getModel] at H
  cases htid : m_tid m with
  | some tid =>
    simp only [htid, ret_only, LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | none =>
    simp only [htid] at H
    rcases H with h | ⟨x, m1, evs1, hc, hk⟩
    · exact absurd h (choose_no_unmodeled _ _ _)
    · obtain ⟨y, -, heq⟩ := hc
      simp only [Outcome.ok.injEq] at heq
      obtain ⟨hx, hm1, hevs1⟩ := heq
      subst x; subst m1; subst evs1
      exact absurd hk (seqSpec_modify_ret_only_no_unmodeled (with_tid y) y i m)

theorem check_set_tid_address_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_set_tid_address eff m = .CheckOk m' evs) :
    set_tid_address_spec i m (.ok eff m' evs) := by
  generalize hP : (set_tid_address_spec i m (.ok eff m' evs)) = Q at *
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    simp only [check_set_tid_address] at H
  case nil.nil.nil.nil.nil =>
    cases htid : m_tid m with
    | some tid =>
      simp only [htid] at H
      by_cases hr : bv_eqb ret tid = true
      · rw [ite_eq_left hr] at H
        obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
        subst m'; subst evs
        have hret : ret = tid := (Fs.bv_eqb_eq ret tid).mp hr
        subst ret
        rw [← hP]
        simp only [set_tid_address_spec, getModelSpec, bind_getModel, htid, ret_only,
          LinuxSem.LinuxProcessSem.pure, mkEffect]
      · rw [ite_eq_right hr] at H
        exact nomatch H
    | none =>
      simp only [htid] at H
      by_cases hv : (decide (0 < (ret.toNat : Int)) &&
          decide ((ret.toNat : Int) < PID_MAX_ENVELOPE)) = true
      · rw [ite_eq_left hv] at H
        obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
        subst m'; subst evs
        rw [← hP]
        simp only [set_tid_address_spec, getModelSpec, bind_getModel, htid]
        refine bind_ok0 (choose _) _ i m ret m (mkEffect ret [] []) (with_tid ret m) [] ?_ ?_
        · refine choose_ok _ ret i m ?_
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
          exact hv
        · exact bind_ok (modify (with_tid ret)) (fun _ => ret_only ret) i (with_tid ret m)
            () (with_tid ret m) [] (mkEffect ret [] []) (with_tid ret m) []
            (modify_ok (with_tid ret) i m) (pure_ok (mkEffect ret [] []) i (with_tid ret m))
      · rw [ite_eq_right hv] at H
        exact nomatch H
  all_goals exact nomatch H

theorem check_set_tid_address_sound_unmodeled (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_set_tid_address eff m = .CheckUnmodeled) :
    set_tid_address_spec i m .unmodeled :=
  absurd H (check_set_tid_address_no_unmodeled eff m)

theorem check_set_tid_address_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : set_tid_address_spec i m (.ok eff m' evs)) :
    check_set_tid_address eff m = .CheckOk m' evs := by
  generalize hP : (check_set_tid_address eff m = .CheckOk m' evs) = Q at *
  simp only [set_tid_address_spec, getModelSpec, bind_getModel] at H
  cases htid : m_tid m with
  | some tid =>
    simp only [htid, ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at H
    obtain ⟨heff, hm', hevs⟩ := H
    subst eff; subst m'; subst evs
    rw [← hP]
    simp only [check_set_tid_address, htid, bv_eqb_refl, ite_true]
  | none =>
    simp only [htid] at H
    rcases H with ⟨x, m1, evs1, evs2, hc, hk, hevs⟩
    obtain ⟨tid, hPmem, heq⟩ := hc
    simp only [Outcome.ok.injEq] at heq
    obtain ⟨hx, hm1, hevs1⟩ := heq
    subst x; subst m1; subst evs1
    obtain ⟨heff, hm', hevs2⟩ :=
      seqSpec_modify_ret_only_inv (with_tid tid) tid i m eff m' evs2 hk
    subst eff; subst m'; subst evs2
    simp only [List.nil_append] at hevs
    subst evs
    rw [← hP]
    simp only [check_set_tid_address, htid]
    rw [ite_eq_left (by
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true_eq.mpr hPmem.1, decide_eq_true_eq.mpr hPmem.2⟩)]

theorem check_set_tid_address_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : set_tid_address_spec i m .unmodeled) :
    check_set_tid_address eff m = .CheckUnmodeled :=
  absurd H (set_tid_address_spec_no_unmodeled i m)

/- ----------------------------------------------------------- clone/clone3 -/

/- clone / clone3: no writes, no model update.  The two arms of
   [Fork.clone_resolve] are disjoint on the observed return — every
   admissible pid is below [PID_MAX_ENVELOPE] and every member of
   [Fork.clone_errnos] reads as an unsigned value just under 2^64 — so
   this is a function of the return rather than a choice.  A return of
   0 falls through both tests to [CheckReject]: it is the CHILD's
   answer, and [Fork.clone_spec]'s header says why that is a decision.
   `Checks/ProcessCreation.lean` proves
   [clone_never_returns_zero] and `clone3_never_returns_zero`, so the
   exclusion above is pinned by theorem, not merely read off the envelope
   and the errno set. -/

/- The admitted ANSWER, shared by both entry points so the pid envelope
   and the errno set cannot drift between them.  The two differ only in
   the copy-in ledger they require, which is the whole observable
   difference between [clone] and [clone3]. -/

/- The success arm returns the model WITH the child recorded, mirroring
   [Kernel.Fork.clone_resolve]'s [with_children] on the same branch.  The
   errno arm returns [m] unchanged: it created nothing. -/
def check_clone_answer (ret : word) (m : Model) : check_result :=
  if errno_ret_in clone_errnos ret then .CheckOk m []
  else if clone_pid_ok_b m ret then .CheckOk (with_children m) []
  else .CheckReject

def check_clone_resolve (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(clone_no_shared_file_b (m_fds m)) then .CheckUnmodeled
  else match eff with
  | ⟨ret, [], [], [], [], []⟩ => check_clone_answer ret m
  | _ => .CheckReject

/-- [clone3] read [CLONE_ARGS_SIZE] bytes at [uargs] before resolving, so
    its effect must carry exactly that range and no other.  An empty
    ledger here is not a harmless omission: it is a claim that the call
    read no user memory, which would let the model admit an allocation
    the kernel refuses.  The descriptor gate is tested FIRST, so a model
    the resolution declines answers [CheckUnmodeled] whatever ledger the
    effect carries. -/
def check_clone3_resolve (uargs : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(clone_no_shared_file_b (m_fds m)) then .CheckUnmodeled
  else match eff with
  | ⟨ret, [], [], [], [], [(a, n)]⟩ =>
      if bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat)
      then check_clone_answer ret m
      else .CheckReject
  | _ => .CheckReject

def check_clone (flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if clone_fork_flags_b flags then check_clone_resolve eff m
  else .CheckUnmodeled

def check_clone3 (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE)) then .CheckUnmodeled
  else match read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
       | none => .CheckUnmodeled
       | some bs =>
           if clone3_fork_args_b bs then check_clone3_resolve uargs eff m
           else .CheckUnmodeled

/-! ## clone_pid_not_errno -/

/-- No admissible pid can be mistaken for an admissible errno.  Every
    member of [Fork.clone_errnos] reads as an unsigned 64-bit value just
    under 2^64, and every pid the spec chooses is below
    [PID_MAX_ENVELOPE], so [errno_ret_in_below] separates them whatever
    the list holds.  This is what keeps [check_clone_resolve] a function
    of the observed return, for every [Model] rather than merely every
    reachable one. -/
theorem clone_pid_not_errno (m : Model) (r : word)
    (Hok : clone_pid_ok_b m r = true) : errno_ret_in clone_errnos r = false := by
  unfold clone_pid_ok_b at Hok
  have hAB : (decide (0 < (r.toNat : Int)) &&
      decide ((r.toNat : Int) < PID_MAX_ENVELOPE)) = true :=
    (Bool.and_eq_true_iff.mp Hok).1
  have hB : decide ((r.toNat : Int) < PID_MAX_ENVELOPE) = true :=
    (Bool.and_eq_true_iff.mp hAB).2
  rw [decide_eq_true_eq] at hB
  have hp : PID_MAX_ENVELOPE = (4194304 : Int) := by decide
  have h2p : two_pow_64 = (18446744073709551616 : Int) := by decide
  have hok : errnos_ok clone_errnos = true := by decide
  apply errno_ret_in_below clone_errnos r hok
  rw [hp] at hB
  rw [h2p]
  omega

/-! ## The clone resolution -/

theorem check_clone_resolve_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_clone_resolve eff m = .CheckOk m' evs) :
    clone_resolve i m (.ok eff m' evs) := by
  generalize hP : (clone_resolve i m (.ok eff m' evs)) = Q at *
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  simp only [check_clone_resolve] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    exact nomatch H
  · rw [ite_eq_right hg] at H
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
      simp only [check_clone_answer] at H
    case nil.nil.nil.nil.nil =>
      by_cases he : errno_ret_in clone_errnos ret = true
      · rw [ite_eq_left he] at H
        obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
        subst m'; subst evs
        obtain ⟨e, hmem, hret⟩ := (errno_ret_in_true clone_errnos ret).mp he
        subst hret
        rw [← hP]
        simp only [clone_resolve, getModelSpec, bind_getModel, ite_eq_right hg]
        refine alt_l _ _ _ _ _ ?_
        refine bind_ok0 (errno_from clone_errnos) _ i m e m (mkEffect (errno_ret e) [] []) m [] ?_ ?_
        · exact choose_ok (fun e => e ∈ clone_errnos) e i m hmem
        · simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure]
      · rw [ite_eq_right he] at H
        by_cases hok : clone_pid_ok_b m ret = true
        · rw [ite_eq_left hok] at H
          obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj H
          subst m'; subst evs
          rw [← hP]
          simp only [clone_resolve, getModelSpec, bind_getModel, ite_eq_right hg]
          refine alt_r _ _ _ _ _ ?_
          refine bind_ok0 (choose (fun p => clone_pid_ok_b m p = true)) _ i m ret m
            (mkEffect ret [] []) (with_children m) [] ?_ ?_
          · exact choose_ok _ ret i m hok
          · exact bind_ok (modify with_children) (fun _ => ret_only ret) i m ()
              (with_children m) [] (mkEffect ret [] []) (with_children m) []
              (modify_ok with_children i m) (pure_ok (mkEffect ret [] []) i (with_children m))
        · rw [ite_eq_right hok] at H
          exact nomatch H
    all_goals exact nomatch H

theorem check_clone_resolve_sound_unmodeled (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_clone_resolve eff m = .CheckUnmodeled) :
    clone_resolve i m .unmodeled := by
  generalize hP : (clone_resolve i m .unmodeled) = Q at *
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  simp only [check_clone_resolve] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    rw [← hP]
    simp only [clone_resolve, getModelSpec, bind_getModel, ite_eq_left hg, unmodeled]
  · rw [ite_eq_right hg] at H
    exfalso
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
      simp only [check_clone_answer] at H
    case nil.nil.nil.nil.nil =>
      by_cases he : errno_ret_in clone_errnos ret = true
      · rw [ite_eq_left he] at H
        exact nomatch H
      · rw [ite_eq_right he] at H
        by_cases hok : clone_pid_ok_b m ret = true
        · rw [ite_eq_left hok] at H
          exact nomatch H
        · rw [ite_eq_right hok] at H
          exact nomatch H
    all_goals exact nomatch H

theorem check_clone_resolve_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : clone_resolve i m (.ok eff m' evs)) :
    check_clone_resolve eff m = .CheckOk m' evs := by
  generalize hP : (check_clone_resolve eff m = .CheckOk m' evs) = Q at *
  simp only [clone_resolve, getModelSpec, bind_getModel] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hg] at H
    rcases H with H1 | H2
    · -- an errno from [clone_errnos]: it created nothing
      obtain ⟨e, m1, evs1, evs2, hc, her, hevs⟩ := H1
      obtain ⟨e0, hmem, heq⟩ := hc
      simp only [Outcome.ok.injEq] at heq
      obtain ⟨hx, hm1, hevs1⟩ := heq
      subst e; subst m1; subst evs1
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at her
      obtain ⟨heff, hm', hevs2⟩ := her
      subst eff; subst m'; subst evs2
      simp only [List.nil_append] at hevs
      subst evs
      rw [← hP]
      simp only [check_clone_resolve, ite_eq_right hg, check_clone_answer]
      rw [ite_eq_left (errno_ret_in_intro clone_errnos e0 hmem)]
    · -- a pid: the model gains the child
      obtain ⟨p, m1, evs1, evs2, hc, hk, hevs⟩ := H2
      obtain ⟨p0, hok, heq⟩ := hc
      simp only [Outcome.ok.injEq] at heq
      obtain ⟨hx, hm1, hevs1⟩ := heq
      subst p; subst m1; subst evs1
      obtain ⟨heff, hm', hevs2⟩ :=
        seqSpec_modify_ret_only_inv with_children p0 i m eff m' evs2 hk
      subst eff; subst m'; subst evs2
      simp only [List.nil_append] at hevs
      subst evs
      rw [← hP]
      simp only [check_clone_resolve, ite_eq_right hg, check_clone_answer]
      rw [clone_pid_not_errno m p0 hok]
      simp only [Bool.false_eq_true, ite_false, ite_eq_left hok]

theorem check_clone_resolve_complete_unmodeled (m : Model) (i : SyscallInput)
    (eff : SyscallEffect) (H : clone_resolve i m .unmodeled) :
    check_clone_resolve eff m = .CheckUnmodeled := by
  generalize hP : (check_clone_resolve eff m = .CheckUnmodeled) = Q at *
  simp only [clone_resolve, getModelSpec, bind_getModel] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    rw [← hP]
    simp only [check_clone_resolve, ite_eq_left hg]
  · rw [ite_eq_right hg] at H
    exfalso
    rcases H with H1 | H2
    · rcases H1 with hdecl | ⟨e, m1, evs1, hc, hk⟩
      · obtain ⟨x, -, heq⟩ := hdecl
        exact nomatch heq
      · obtain ⟨e0, -, heq⟩ := hc
        simp only [Outcome.ok.injEq] at heq
        obtain ⟨hx, hm1, hevs1⟩ := heq
        subst e; subst m1; subst evs1
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at hk
        exact nomatch hk
    · rcases H2 with hdecl | ⟨p, m1, evs1, hc, hk⟩
      · obtain ⟨x, -, heq⟩ := hdecl
        exact nomatch heq
      · obtain ⟨p0, -, heq⟩ := hc
        simp only [Outcome.ok.injEq] at heq
        obtain ⟨hx, hm1, hevs1⟩ := heq
        subst p; subst m1; subst evs1
        exact absurd hk (seqSpec_modify_ret_only_no_unmodeled with_children p0 i m)

/-! ## The resolution with a ledger (clone3) -/

/- The same four, for the resolution that carries a ledger.  Each goes
   through the plain one on the effect with the ledger stripped, so the
   admitted answer is decided in exactly one place. -/

theorem check_clone3_resolve_sound_ok (uargs : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_clone3_resolve uargs eff m = .CheckOk m' evs) :
    clone3_resolve uargs i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  simp only [check_clone3_resolve] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    exact nomatch H
  · rw [ite_eq_right hg] at H
    cases ws <;> cases zs <;> cases us <;> cases cs
    case nil.nil.nil.nil =>
      cases ks with
      | nil => exact nomatch H
      | cons hd tl =>
        obtain ⟨a, n⟩ := hd
        cases tl with
        | nil =>
          dsimp only at H
          by_cases hl : (bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat)) = true
          · rw [ite_eq_left hl] at H
            obtain ⟨ha, hn⟩ := Bool.and_eq_true_iff.mp hl
            have ha' : a = uargs := (Fs.bv_eqb_eq a uargs).mp ha
            have hn' : n = CLONE_ARGS_SIZE_nat := beq_iff_eq.mp hn
            subst a; subst n
            have hres : clone_resolve i m (.ok (mkEffect ret [] []) m' evs) := by
              refine check_clone_resolve_sound_ok (mkEffect ret [] []) m m' evs i ?_
              simp only [check_clone_resolve, ite_eq_right hg]
              exact H
            have hrec := record_copyins_ok_empty (reads := [(uargs, CLONE_ARGS_SIZE_nat)])
              (spec := clone_resolve) (i := i) (m := m) (eff := mkEffect ret [] [])
              (m' := m') (evs := evs) rfl hres
            simpa [clone3_resolve, with_copyins] using hrec
          · rw [ite_eq_right hl] at H
            exact nomatch H
        | cons hd2 tl2 => exact nomatch H
    all_goals exact nomatch H

theorem check_clone3_resolve_sound_unmodeled (uargs : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_clone3_resolve uargs eff m = .CheckUnmodeled) :
    clone3_resolve uargs i m .unmodeled := by
  simp only [check_clone3_resolve] at H
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · rw [ite_eq_left hg] at H
    simp only [clone3_resolve]
    refine record_copyins_unmodeled ?_
    refine check_clone_resolve_sound_unmodeled eff m i ?_
    simp only [check_clone_resolve, ite_eq_left hg]
  · rw [ite_eq_right hg] at H
    exfalso
    obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
    cases ws <;> cases zs <;> cases us <;> cases cs
    case nil.nil.nil.nil =>
      cases ks with
      | nil => exact nomatch H
      | cons hd tl =>
        obtain ⟨a, n⟩ := hd
        cases tl with
        | nil =>
          dsimp only at H
          by_cases hl : (bv_eqb a uargs && (n == CLONE_ARGS_SIZE_nat)) = true
          · rw [ite_eq_left hl] at H
            simp only [check_clone_answer] at H
            by_cases he : errno_ret_in clone_errnos ret = true
            · rw [ite_eq_left he] at H
              exact nomatch H
            · rw [ite_eq_right he] at H
              by_cases hok : clone_pid_ok_b m ret = true
              · rw [ite_eq_left hok] at H
                exact nomatch H
              · rw [ite_eq_right hok] at H
                exact nomatch H
          · rw [ite_eq_right hl] at H
            exact nomatch H
        | cons hd2 tl2 => exact nomatch H
    all_goals exact nomatch H

theorem check_clone3_resolve_complete_ok (uargs : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : clone3_resolve uargs i m (.ok eff m' evs)) :
    check_clone3_resolve uargs eff m = .CheckOk m' evs := by
  generalize hP : (check_clone3_resolve uargs eff m = .CheckOk m' evs) = Q at *
  simp only [clone3_resolve] at H
  obtain ⟨e0, m0, evs0, evs2, H0, Hp, Hevs⟩ := H
  simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at Hp
  obtain ⟨heff, hm0, hevs2⟩ := Hp
  subst eff; subst m'; subst evs2
  simp only [List.append_nil] at Hevs
  subst evs
  have Hc := check_clone_resolve_complete_ok e0 m m0 evs0 i H0
  by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
  · simp only [check_clone_resolve, ite_eq_left hg] at Hc
    exact nomatch Hc
  · obtain ⟨ret, ws, zs, us, cs, ks⟩ := e0
    simp only [check_clone_resolve, ite_eq_right hg] at Hc
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks
    case nil.nil.nil.nil.nil =>
      rw [← hP]
      simp only [check_clone3_resolve, ite_eq_right hg, with_copyins]
      simpa [bv_eqb_refl] using Hc
    all_goals exact nomatch Hc

theorem check_clone3_resolve_complete_unmodeled (uargs : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : clone3_resolve uargs i m .unmodeled) :
    check_clone3_resolve uargs eff m = .CheckUnmodeled := by
  generalize hP : (check_clone3_resolve uargs eff m = .CheckUnmodeled) = Q at *
  simp only [clone3_resolve] at H
  rcases H with H0 | ⟨e0, m0, evs0, H0, Hp⟩
  · have Hc := check_clone_resolve_complete_unmodeled m i eff H0
    by_cases hg : (!(clone_no_shared_file_b (m_fds m))) = true
    · rw [← hP]
      simp only [check_clone3_resolve, ite_eq_left hg]
    · exfalso
      simp only [check_clone_resolve, ite_eq_right hg] at Hc
      obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
      cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
        simp only [check_clone_answer] at Hc
      case nil.nil.nil.nil.nil =>
        by_cases he : errno_ret_in clone_errnos ret = true
        · rw [ite_eq_left he] at Hc
          exact nomatch Hc
        · rw [ite_eq_right he] at Hc
          by_cases hok : clone_pid_ok_b m ret = true
          · rw [ite_eq_left hok] at Hc
            exact nomatch Hc
          · rw [ite_eq_right hok] at Hc
            exact nomatch Hc
      all_goals exact nomatch Hc
  · simp only [LinuxSem.LinuxProcessSem.pure] at Hp
    exact nomatch Hp

/-! ## clone (220) -/

theorem check_clone_sound_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_clone flags eff m = .CheckOk m' evs) :
    clone_spec flags i m (.ok eff m' evs) := by
  generalize hP : (clone_spec flags i m (.ok eff m' evs)) = Q at *
  simp only [check_clone] at H
  by_cases hf : clone_fork_flags_b flags = true
  · rw [ite_eq_left hf] at H
    rw [← hP]
    simp only [clone_spec, ite_eq_left hf]
    exact check_clone_resolve_sound_ok eff m m' evs i H
  · rw [ite_eq_right hf] at H
    exact nomatch H

theorem check_clone_sound_unmodeled (flags : word) (eff : SyscallEffect) (m : Model)
    (i : SyscallInput) (H : check_clone flags eff m = .CheckUnmodeled) :
    clone_spec flags i m .unmodeled := by
  generalize hP : (clone_spec flags i m .unmodeled) = Q at *
  simp only [check_clone] at H
  by_cases hf : clone_fork_flags_b flags = true
  · rw [ite_eq_left hf] at H
    rw [← hP]
    simp only [clone_spec, ite_eq_left hf]
    exact check_clone_resolve_sound_unmodeled eff m i H
  · rw [ite_eq_right hf] at H
    rw [← hP]
    simp only [clone_spec, ite_eq_right hf, unmodeled]

theorem check_clone_complete_ok (flags : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : clone_spec flags i m (.ok eff m' evs)) :
    check_clone flags eff m = .CheckOk m' evs := by
  generalize hP : (check_clone flags eff m = .CheckOk m' evs) = Q at *
  simp only [clone_spec] at H
  by_cases hf : clone_fork_flags_b flags = true
  · rw [ite_eq_left hf] at H
    rw [← hP]
    simp only [check_clone, ite_eq_left hf]
    exact check_clone_resolve_complete_ok eff m m' evs i H
  · rw [ite_eq_right hf] at H
    simp only [unmodeled] at H
    exact nomatch H

theorem check_clone_complete_unmodeled (flags : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : clone_spec flags i m .unmodeled) :
    check_clone flags eff m = .CheckUnmodeled := by
  generalize hP : (check_clone flags eff m = .CheckUnmodeled) = Q at *
  simp only [clone_spec] at H
  by_cases hf : clone_fork_flags_b flags = true
  · rw [ite_eq_left hf] at H
    rw [← hP]
    simp only [check_clone, ite_eq_left hf]
    exact check_clone_resolve_complete_unmodeled m i eff H
  · rw [ite_eq_right hf] at H
    rw [← hP]
    simp only [check_clone, ite_eq_right hf]

/-! ## clone3 (435) -/

theorem check_clone3_sound_ok (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_clone3 i uargs size eff m = .CheckOk m' evs) :
    clone3_spec uargs size i m (.ok eff m' evs) := by
  generalize hP : (clone3_spec uargs size i m (.ok eff m' evs)) = Q at *
  simp only [check_clone3] at H
  by_cases hsz : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [ite_eq_left hsz] at H
    exact nomatch H
  · rw [ite_eq_right hsz] at H
    rw [← hP]
    simp only [clone3_spec, ite_eq_right hsz]
    refine bind_ok0 inputSpec _ i m i m eff m' evs (input_ok i m) ?_
    cases hbs : read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
    | none =>
      simp only [hbs] at H
      exact nomatch H
    | some bs =>
      simp only [hbs] at H
      by_cases ha : clone3_fork_args_b bs = true
      · rw [ite_eq_left ha] at H
        simp only [ite_eq_left ha]
        exact check_clone3_resolve_sound_ok uargs eff m m' evs i H
      · rw [ite_eq_right ha] at H
        exact nomatch H

theorem check_clone3_sound_unmodeled (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_clone3 i uargs size eff m = .CheckUnmodeled) :
    clone3_spec uargs size i m .unmodeled := by
  generalize hP : (clone3_spec uargs size i m .unmodeled) = Q at *
  simp only [check_clone3] at H
  by_cases hsz : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [ite_eq_left hsz] at H
    rw [← hP]
    simp only [clone3_spec, ite_eq_left hsz, unmodeled]
  · rw [ite_eq_right hsz] at H
    rw [← hP]
    simp only [clone3_spec, ite_eq_right hsz]
    refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
    cases hbs : read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
    | none =>
      simp only [hbs] at H
      simp only [unmodeled]
    | some bs =>
      simp only [hbs] at H
      by_cases ha : clone3_fork_args_b bs = true
      · rw [ite_eq_left ha] at H
        simp only [ite_eq_left ha]
        exact check_clone3_resolve_sound_unmodeled uargs eff m i H
      · rw [ite_eq_right ha] at H
        simp only [ite_eq_right ha, unmodeled]

theorem check_clone3_complete_ok (i : SyscallInput) (uargs size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : clone3_spec uargs size i m (.ok eff m' evs)) :
    check_clone3 i uargs size eff m = .CheckOk m' evs := by
  generalize hP : (check_clone3 i uargs size eff m = .CheckOk m' evs) = Q at *
  simp only [clone3_spec] at H
  by_cases hsz : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [ite_eq_left hsz] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hsz] at H
    obtain ⟨i0, m1, evs1, evs2, hi, hk, hevs⟩ := H
    simp only [inputSpec, LinuxSem.LinuxProcessSem.input,
      Outcome.ok.injEq] at hi
    obtain ⟨hi0, hm1, hevs1⟩ := hi
    subst i0; subst m1; subst evs1
    simp only [List.nil_append] at hevs
    subst evs
    cases hbs : read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
    | none =>
      simp only [hbs] at hk
      simp only [unmodeled] at hk
      exact nomatch hk
    | some bs =>
      simp only [hbs] at hk
      by_cases ha : clone3_fork_args_b bs = true
      · rw [ite_eq_left ha] at hk
        rw [← hP]
        simp only [check_clone3, ite_eq_right hsz, hbs, ite_eq_left ha]
        exact check_clone3_resolve_complete_ok uargs eff m m' evs2 i hk
      · rw [ite_eq_right ha] at hk
        simp only [unmodeled] at hk
        exact nomatch hk

theorem check_clone3_complete_unmodeled (i : SyscallInput) (uargs size : word)
    (m : Model) (eff : SyscallEffect)
    (H : clone3_spec uargs size i m .unmodeled) :
    check_clone3 i uargs size eff m = .CheckUnmodeled := by
  generalize hP : (check_clone3 i uargs size eff m = .CheckUnmodeled) = Q at *
  simp only [clone3_spec] at H
  by_cases hsz : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [ite_eq_left hsz] at H
    rw [← hP]
    simp only [check_clone3, ite_eq_left hsz]
  · rw [ite_eq_right hsz] at H
    rcases H with hdecl | ⟨i0, m1, evs1, hc, hk⟩
    · simp only [inputSpec, LinuxSem.LinuxProcessSem.input] at hdecl
      exact nomatch hdecl
    · simp only [inputSpec, LinuxSem.LinuxProcessSem.input,
        Outcome.ok.injEq] at hc
      obtain ⟨hi0, hm1, hevs1⟩ := hc
      subst i0; subst m1; subst evs1
      cases hbs : read_bytes_map i.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
      | none =>
        simp only [hbs] at hk
        rw [← hP]
        simp only [check_clone3, ite_eq_right hsz, hbs]
      | some bs =>
        simp only [hbs] at hk
        by_cases ha : clone3_fork_args_b bs = true
        · rw [ite_eq_left ha] at hk
          rw [← hP]
          simp only [check_clone3, ite_eq_right hsz, hbs, ite_eq_left ha]
          exact check_clone3_resolve_complete_unmodeled uargs m i eff hk
        · rw [ite_eq_right ha] at hk
          rw [← hP]
          simp only [check_clone3, ite_eq_right hsz, hbs, ite_eq_right ha]

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the branch
    order the proofs above follow, one per claim the matching spec's prose
    makes: a pid inside the envelope is admitted and records the child, a
    return of 0 is REJECTED (it is the child's answer, not the parent's),
    the errno arm leaves the model alone, a thread-creating flag word is
    declined before anything else, and `clone3`'s ledger gate is exact.

    `check_result` carries no `DecidableEq`, so each states the branch as
    an equation and closes it by unfolding the checker and discharging the
    branch tests with `decide`. -/

/-- A model with the given descriptor table and recorded tid, and
    `mkModel`'s defaults everywhere else. -/
private def port_model (fds : List (word × FdEntry)) (tid : Option word) : Model :=
  mkModel fds (mkVmMaps [] [] 0 0 0) IEof [] none tid none

/-- Every member of [clone_errnos] reads as an errno. -/
example : errno_ret_in clone_errnos (errno_ret EAGAIN) = true := by decide

/-- A pid inside the envelope is admitted, and the model gains the child:
    the success arm is the only one that calls [with_children]. -/
example :
    check_clone (BitVec.ofInt 64 SIGCHLD) (mkEffect 1234 [] [])
        (port_model [] none) = .CheckOk (with_children (port_model [] none)) [] := by
  simp only [check_clone, check_clone_resolve, check_clone_answer]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- The errno arm answers the same model it was given: it created
    nothing. -/
example :
    check_clone (BitVec.ofInt 64 SIGCHLD) (mkEffect (errno_ret EAGAIN) [] [])
        (port_model [] none) = .CheckOk (port_model [] none) [] := by
  simp only [check_clone, check_clone_resolve, check_clone_answer]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A return of 0 falls through both tests to [CheckReject]: it is the
    CHILD's answer, and [Fork.clone_spec] admits no zero pid. -/
example :
    check_clone (BitVec.ofInt 64 SIGCHLD) (mkEffect 0 [] [])
        (port_model [] none) = .CheckReject := by
  simp only [check_clone, check_clone_resolve, check_clone_answer]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

/-- A thread-creating flag word is declined before the effect is read;
    the admitted set is the singleton {17}, as [Fork.clone_fork_flags_b]
    says. -/
example :
    check_clone (BitVec.ofInt 64 0x10000011) (mkEffect 1234 [] [])
        (port_model [] none) = .CheckUnmodeled := by
  simp only [check_clone]
  rw [ite_eq_right (by decide)]

/-- An empty copy-in ledger is refused by [clone3]'s resolution: the call
    claims to have read nothing, and [Fork.clone3_resolve] records the
    [CLONE_ARGS_SIZE] range. -/
example :
    check_clone3_resolve 4096 (mkEffect (errno_ret EAGAIN) [] [])
        (port_model [] none) = .CheckReject := by
  simp only [check_clone3_resolve]
  rw [ite_eq_right (by decide)]

/-- …and the recorded range with the wrong length is refused too. -/
example :
    check_clone3_resolve 4096 (with_copyins [(4096, 87)] (mkEffect (errno_ret EAGAIN) [] []))
        (port_model [] none) = .CheckReject := by
  simp only [check_clone3_resolve, with_copyins]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

/-- A `clone3` whose `size` is not the full struct is declined before the
    struct is read. -/
example :
    check_clone3 ⟨435, [], fun _ => none, fun _ => none⟩ 4096 87
      (mkEffect 1234 [] []) (port_model [] none)
      = .CheckUnmodeled := by
  simp only [check_clone3]
  rw [ite_eq_left (by decide)]

end LinuxSem.Checks.Sys.Kernel.Fork
