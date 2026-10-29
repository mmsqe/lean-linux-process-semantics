/-
  * LinuxProcessSem.Checks.Sys.Fs.Select — the pselect6 (72) and ppoll (73) checkers, and their proofs

  Answers to Linux [fs/select.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); the spec monad `Sys A` is `SysSpec A`; a witness
  answers with `Outcome A Model event` and declines as `.unmodeled`; and a
  `bool_decide` test is `decide`.  An effect literal is the anonymous
  constructor pattern `⟨r, ws, [], [], [], []⟩` over `SyscallEffect`
  (`State.lean`), whose `mkEffect r ws []` abbreviation is the same term.

  The proofs take the effect apart with `obtain`, then knock out the four
  non-`[]` shapes of each of its six lists with the same four-way `cases`,
  closing the fifteen impossible shapes with `exact nomatch H` (the
  hypothesis names the two distinct constructors of `check_result`).
  `refine bind_ok0 …` peels the prologue and `dsimp only` reduces after it.
  `sys_unfold` is not needed: the two specs here have no `Sys.Syscall`
  setter in their bodies, only `inputSpec`, `getModelSpec`, the outcome
  match and `pure`, so `bind_input_model_inv` (`Checks.Sys.Prelude`) peels
  the whole prologue and leaves the outcome match, which `generalize` +
  `cases` inverts.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Fs.Select

namespace LinuxSem.Checks.Sys.Fs.Select

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Fs.Select
open LinuxSem.Checks.Sys.Prelude

/- =========================================================================
   pselect6 (72)
   ========================================================================= -/

/-- pselect6: deterministic throughout the modeled band, so the acceptor
    is the spec's own computation plus one equality.  Everything that
    makes this syscall hard -- readiness, the timeout write-back, the
    [fdt->max_fds] clamp, a real signal mask -- is decided by
    [Select.pselect6_outcome] answering [none], which is [CheckUnmodeled]
    here. -/
def check_pselect6 (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match pselect6_outcome i m n32 inp outp exp tsp sig with
  | none => .CheckUnmodeled
  | some (r, ws) =>
      match eff with
      | ⟨r', ws', [], [], [], []⟩ =>
          if bv_eqb r' r && writes_eqb ws' ws then .CheckOk m [] else .CheckReject
      | _ => .CheckReject

theorem check_pselect6_sound_ok (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_pselect6 i n32 inp outp exp tsp sig eff m = .CheckOk m' evs) :
    pselect6_spec n32 inp outp exp tsp sig i m (.ok eff m' evs) := by
  unfold check_pselect6 at H
  unfold pselect6_spec
  refine bind_ok0 inputSpec _ i m i m eff m' evs rfl ?_
  try dsimp only
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hdef : pselect6_outcome i m n32 inp outp exp tsp sig = out at H ⊢
  cases out with
  | none => exact nomatch H
  | some p =>
    obtain ⟨r, ws⟩ := p
    obtain ⟨r', ws', zs, us, cs, ks⟩ := eff
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    · by_cases hg : (bv_eqb r' r && writes_eqb ws' ws) = true
      · rw [ite_eq_left hg] at H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨hm, hevs⟩ := H
        have h1 : bv_eqb r' r = true := (Bool.and_eq_true ..).mp hg |>.1
        have h2 : writes_eqb ws' ws = true := (Bool.and_eq_true ..).mp hg |>.2
        have hr : r' = r := (Fs.bv_eqb_eq r' r).mp h1
        have hw : ws' = ws := (writes_eqb_eq ws' ws).mp h2
        subst hr; subst hw; subst hm; subst hevs
        rfl
      · rw [ite_eq_right hg] at H
        exact nomatch H
    all_goals (exact nomatch H)

theorem check_pselect6_sound_unmodeled (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_pselect6 i n32 inp outp exp tsp sig eff m = .CheckUnmodeled) :
    pselect6_spec n32 inp outp exp tsp sig i m .unmodeled := by
  unfold check_pselect6 at H
  unfold pselect6_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
  try dsimp only
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hdef : pselect6_outcome i m n32 inp outp exp tsp sig = out at H ⊢
  cases out with
  | none => exact unmodeled_intro _ _
  | some p =>
    obtain ⟨r, ws⟩ := p
    obtain ⟨r', ws', zs, us, cs, ks⟩ := eff
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    · by_cases hg : (bv_eqb r' r && writes_eqb ws' ws) = true
      · rw [ite_eq_left hg] at H
        exact nomatch H
      · rw [ite_eq_right hg] at H
        exact nomatch H
    all_goals (exact nomatch H)

theorem check_pselect6_complete_ok (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : pselect6_spec n32 inp outp exp tsp sig i m (.ok eff m' evs)) :
    check_pselect6 i n32 inp outp exp tsp sig eff m = .CheckOk m' evs := by
  unfold check_pselect6
  unfold pselect6_spec at H
  let k : SyscallInput → Model → SysSpec SyscallEffect :=
    fun i0 m0 =>
      match pselect6_outcome i0 m0 n32 inp outp exp tsp sig with
      | none => unmodeled
      | some (r, ws) => LinuxSem.LinuxProcessSem.pure (mkEffect r ws [])
  have hbody : k i m i m (.ok eff m' evs) :=
    bind_input_model_inv k i m (.ok eff m' evs) H
  dsimp only [k] at hbody
  generalize hdef : pselect6_outcome i m n32 inp outp exp tsp sig = out at hbody ⊢
  cases out with
  | none => exact nomatch hbody
  | some p =>
    obtain ⟨r, ws⟩ := p
    dsimp only [mkEffect]
    simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hbody
    obtain ⟨hr, hm, hevs⟩ := hbody
    subst hr; subst hm; subst hevs
    dsimp only [mkEffect]
    rw [ite_eq_left (by simp [bv_eqb_refl, writes_eqb_eq])]

theorem check_pselect6_complete_unmodeled (i : SyscallInput) (n32 inp outp exp tsp sig : word)
    (m : Model) (eff : SyscallEffect)
    (H : pselect6_spec n32 inp outp exp tsp sig i m .unmodeled) :
    check_pselect6 i n32 inp outp exp tsp sig eff m = .CheckUnmodeled := by
  unfold check_pselect6
  unfold pselect6_spec at H
  let k : SyscallInput → Model → SysSpec SyscallEffect :=
    fun i0 m0 =>
      match pselect6_outcome i0 m0 n32 inp outp exp tsp sig with
      | none => unmodeled
      | some (r, ws) => LinuxSem.LinuxProcessSem.pure (mkEffect r ws [])
  have hbody : k i m i m .unmodeled :=
    bind_input_model_inv k i m .unmodeled H
  dsimp only [k] at hbody
  generalize hdef : pselect6_outcome i m n32 inp outp exp tsp sig = out at hbody ⊢
  cases out with
  | none => rfl
  | some p =>
    obtain ⟨r, ws⟩ := p
    simp only [LinuxSem.LinuxProcessSem.pure] at hbody
    exact nomatch hbody

/- =========================================================================
   ppoll (73)
   ========================================================================= -/

/-- ppoll: deterministic throughout the modeled band, exactly as
    pselect6 is above, so the acceptor is the spec's own computation
    plus one equality.  Everything that makes this syscall hard --
    readiness for a descriptor whose answer is a schedule, the timeout
    write-back, the [kmalloc] above [N_STACK_PPS], a real signal mask --
    is decided by [Select.ppoll_outcome] answering [none], which is
    [CheckUnmodeled] here. -/
def check_ppoll (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match ppoll_outcome i m ufds nfds tsp sig sigsetsize with
  | none => .CheckUnmodeled
  | some (r, ws) =>
      match eff with
      | ⟨r', ws', [], [], [], []⟩ =>
          if bv_eqb r' r && writes_eqb ws' ws then .CheckOk m [] else .CheckReject
      | _ => .CheckReject

theorem check_ppoll_sound_ok (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ppoll i ufds nfds tsp sig sigsetsize eff m = .CheckOk m' evs) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m (.ok eff m' evs) := by
  unfold check_ppoll at H
  unfold ppoll_spec
  refine bind_ok0 inputSpec _ i m i m eff m' evs rfl ?_
  try dsimp only
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hdef : ppoll_outcome i m ufds nfds tsp sig sigsetsize = out at H ⊢
  cases out with
  | none => exact nomatch H
  | some p =>
    obtain ⟨r, ws⟩ := p
    obtain ⟨r', ws', zs, us, cs, ks⟩ := eff
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    · by_cases hg : (bv_eqb r' r && writes_eqb ws' ws) = true
      · rw [ite_eq_left hg] at H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨hm, hevs⟩ := H
        have h1 : bv_eqb r' r = true := (Bool.and_eq_true ..).mp hg |>.1
        have h2 : writes_eqb ws' ws = true := (Bool.and_eq_true ..).mp hg |>.2
        have hr : r' = r := (Fs.bv_eqb_eq r' r).mp h1
        have hw : ws' = ws := (writes_eqb_eq ws' ws).mp h2
        subst hr; subst hw; subst hm; subst hevs
        rfl
      · rw [ite_eq_right hg] at H
        exact nomatch H
    all_goals (exact nomatch H)

theorem check_ppoll_sound_unmodeled (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_ppoll i ufds nfds tsp sig sigsetsize eff m = .CheckUnmodeled) :
    ppoll_spec ufds nfds tsp sig sigsetsize i m .unmodeled := by
  unfold check_ppoll at H
  unfold ppoll_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
  try dsimp only
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hdef : ppoll_outcome i m ufds nfds tsp sig sigsetsize = out at H ⊢
  cases out with
  | none => exact unmodeled_intro _ _
  | some p =>
    obtain ⟨r, ws⟩ := p
    obtain ⟨r', ws', zs, us, cs, ks⟩ := eff
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    · by_cases hg : (bv_eqb r' r && writes_eqb ws' ws) = true
      · rw [ite_eq_left hg] at H
        exact nomatch H
      · rw [ite_eq_right hg] at H
        exact nomatch H
    all_goals (exact nomatch H)

theorem check_ppoll_complete_ok (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : ppoll_spec ufds nfds tsp sig sigsetsize i m (.ok eff m' evs)) :
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = .CheckOk m' evs := by
  unfold check_ppoll
  unfold ppoll_spec at H
  let k : SyscallInput → Model → SysSpec SyscallEffect :=
    fun i0 m0 =>
      match ppoll_outcome i0 m0 ufds nfds tsp sig sigsetsize with
      | none => unmodeled
      | some (r, ws) => LinuxSem.LinuxProcessSem.pure (mkEffect r ws [])
  have hbody : k i m i m (.ok eff m' evs) :=
    bind_input_model_inv k i m (.ok eff m' evs) H
  dsimp only [k] at hbody
  generalize hdef : ppoll_outcome i m ufds nfds tsp sig sigsetsize = out at hbody ⊢
  cases out with
  | none => exact nomatch hbody
  | some p =>
    obtain ⟨r, ws⟩ := p
    dsimp only [mkEffect]
    simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hbody
    obtain ⟨hr, hm, hevs⟩ := hbody
    subst hr; subst hm; subst hevs
    dsimp only [mkEffect]
    rw [ite_eq_left (by simp [bv_eqb_refl, writes_eqb_eq])]

theorem check_ppoll_complete_unmodeled (i : SyscallInput) (ufds nfds tsp sig sigsetsize : word)
    (m : Model) (eff : SyscallEffect)
    (H : ppoll_spec ufds nfds tsp sig sigsetsize i m .unmodeled) :
    check_ppoll i ufds nfds tsp sig sigsetsize eff m = .CheckUnmodeled := by
  unfold check_ppoll
  unfold ppoll_spec at H
  let k : SyscallInput → Model → SysSpec SyscallEffect :=
    fun i0 m0 =>
      match ppoll_outcome i0 m0 ufds nfds tsp sig sigsetsize with
      | none => unmodeled
      | some (r, ws) => LinuxSem.LinuxProcessSem.pure (mkEffect r ws [])
  have hbody : k i m i m .unmodeled :=
    bind_input_model_inv k i m .unmodeled H
  dsimp only [k] at hbody
  generalize hdef : ppoll_outcome i m ufds nfds tsp sig sigsetsize = out at hbody ⊢
  cases out with
  | none => rfl
  | some p =>
    obtain ⟨r, ws⟩ := p
    simp only [LinuxSem.LinuxProcessSem.pure] at hbody
    exact nomatch hbody

end LinuxSem.Checks.Sys.Fs.Select
