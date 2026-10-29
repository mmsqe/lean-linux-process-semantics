/-
  * LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers — the clock_gettime (113) checker, and its proofs

  Answers to Linux [kernel/time/posix-timers.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`); a length test is `decide (· < ·)`; `in_wmem i` is
  the record field `i.in_wmem`; and an effect literal is the anonymous
  constructor pattern `⟨r, [(a, bs)], [], [], [], []⟩` over
  `SyscallEffect`, whose `mkEffect r ws []` abbreviation is the same term.

  Three shapes are worth recording.

  - The effect's five lists are read once, in `eff_shape_ok` /
    `eff_shape_ne_unmodeled`: ONE `split at H` closes the fifteen impossible
    shapes and reads the checker's final one-write match backwards for an
    arbitrary branch body.
  - `refine bind_ok0 inputSpec … rfl ?_` peels a reader (both readers are
    definitionally `.ok`), `try dsimp only` reduces after it, and on the
    hypothesis side the spec's steps are peeled with `input_bind_ok_inv` /
    `input_bind_unmodeled_inv` (`Checks.Sys.Prelude`) plus this file's
    `choose_bind_ok_inv` / `choose_bind_unmodeled_inv` /
    `modify_bind_ok_inv`.
  - THE MONOTONIC ARM'S `getModel` PEEL is where Lean needs care.  Its
    continuation is an `if` at FUNCTION type, so any tactic that asks for
    the whnf or the sort of `(if … then … else …) i m o` sets out to decide
    the envelope test and does not terminate.  The proofs therefore peel it
    by rewriting (`simp only [getModelSpec, bind_getModel]` on the
    hypothesis, `refine bind_ok0 getModelSpec …` on the goal) and, in
    `complete_unmodeled`, read the `bind` disjunction apart with `rcases`.
    `Checks.Sys.Kernel.Groups`'s header records the same obstacle for its
    `sint32 … < 0` branches.

  The two options at the top of the file are what that obstacle needs: 10000
  recursion depth for the shape lemmas' `obtain` patterns (the same option,
  for the same reason, as `Sys/Kernel/Time/PosixTimers.lean`), and the
  `constructorNameAsVariable` linter turned off, because it walks every
  declaration's term to a fixed depth and CRASHES — it does not complain —
  on terms this large.  It is a style lint with nothing to say here.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

namespace LinuxSem.Checks.Sys.Kernel.Time.PosixTimers

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Time.PosixTimers
open LinuxSem.Checks.Sys.Prelude

/-- clock_gettime: CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID or one of
    the per-call ids ([Kernel.Time.PosixTimers.clockid_percall_b] —
    CLOCK_REALTIME and the raw, coarse and boottime ids), only a fully
    writable 16-byte destination, and only a reading
    [Kernel.Time.PosixTimers.timespec_ok_b] (respectively
    [Kernel.Time.PosixTimers.realtime_ok_b],
    [Kernel.Time.PosixTimers.cputime_ok_b]) admits — the same booleans
    the spec chooses against, so acceptor and spec cannot drift apart.
    The effect must be exactly one write of those bytes at [tp] and
    nothing else: no zeros, no unmaps, no copies, no copy-ins.

    The three arms differ in three places, and each is the point.  Only
    the monotonic arm tests an envelope on [m_clock], because it is the
    only one that reads it, and only it answers
    [CheckOk (with_clock ...) ...] rather than [CheckOk m] — an
    accepted per-call or [CLOCK_PROCESS_CPUTIME_ID] call leaves
    the model where it was.  Those two are then separated by the
    predicate alone. -/
def check_clock_gettime (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if clockid_percall_b clkid then
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => .CheckUnmodeled
    | some _ =>
        match eff with
        | ⟨r, [(a, bs)], [], [], [], []⟩ =>
            if bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp && realtime_ok_b bs
            then .CheckOk m []
            else .CheckReject
        | _ => .CheckReject
  else if ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) then
    match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => .CheckUnmodeled
    | some _ =>
        match eff with
        | ⟨r, [(a, bs)], [], [], [], []⟩ =>
            if bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp && cputime_ok_b bs
            then .CheckOk m []
            else .CheckReject
        | _ => .CheckReject
  else if !((clkid.toNat : Int) == CLOCK_MONOTONIC) then .CheckUnmodeled
  else if !decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)
  then .CheckUnmodeled
  else
  match read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
  | none => .CheckUnmodeled
  | some _ =>
      match eff with
      | ⟨r, [(a, bs)], [], [], [], []⟩ =>
          if bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp
             && timespec_ok_b bs (m_clock m)
          then .CheckOk (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m) []
          else .CheckReject
      | _ => .CheckReject

/-! ## Inversion helpers for the effect shape

    The checker's arms all end with the same match — one write of a byte
    list at an address, and nothing else — and each of the four proofs
    below has to read that match backwards, in both answer shapes.  These
    three lemmas do it once, for an arbitrary branch body [f] (the three
    arms differ only in [f]), so that the proofs stay at the level of the
    branch condition. -/

/-- Neither answer an arm's branch body can give is [CheckUnmodeled]. -/
private theorem if_ok_or_reject_ne_unmodeled {m : Model} (c : Bool) :
    (if c then (check_result.CheckOk m []) else check_result.CheckReject) ≠
      check_result.CheckUnmodeled := by
  intro h
  split at h <;> exact nomatch h

/-- ...so the one-write match never answers [CheckUnmodeled] either: the
    branch body answers [CheckOk]/[CheckReject] and the fallback is
    [CheckReject]. -/
private theorem eff_shape_ne_unmodeled {f : word → word → List byte → check_result}
    (hf : ∀ r a bs, f r a bs ≠ .CheckUnmodeled) (eff : SyscallEffect) :
    (match eff with
     | ⟨r, [(a, bs)], [], [], [], []⟩ => f r a bs
     | _ => .CheckReject) ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro hh
  split at hh
  · exact hf _ _ _ hh
  · exact nomatch hh

/-- An accepted outcome forces the effect's shape: exactly one write, at
    some address, of some byte list — and the branch body accepted it. -/
private theorem eff_shape_ok {f : word → word → List byte → check_result}
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : (match eff with
          | ⟨r, [(a, bs)], [], [], [], []⟩ => f r a bs
          | _ => .CheckReject) = .CheckOk m' evs) :
    ∃ r a bs, eff = ⟨r, [(a, bs)], [], [], [], []⟩ ∧ f r a bs = .CheckOk m' evs := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  split at H
  · rename_i r' a' bs' heq
    exact ⟨r', a', bs', heq, H⟩
  · exact nomatch H

theorem check_clock_gettime_sound_ok (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_clock_gettime i clkid tp eff m = .CheckOk m' evs) :
    clock_gettime_spec clkid tp i m (.ok eff m' evs) := by
  unfold check_clock_gettime at H
  unfold clock_gettime_spec
  by_cases hrt : clockid_percall_b clkid = true
  · rw [ite_eq_left hrt] at H ⊢
    cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => rw [hdst] at H; exact nomatch H
    | some bs0 =>
      rw [hdst] at H
      obtain ⟨r, a, bs, heff, hcond⟩ := eff_shape_ok H
      subst heff
      by_cases hok : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp
        && realtime_ok_b bs) = true
      · rw [ite_eq_left hok] at hcond
        simp only [check_result.CheckOk.injEq] at hcond
        obtain ⟨hm, hevs⟩ := hcond
        subst hm; subst hevs
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨hr, ha⟩, hts⟩ := hok
        rw [Fs.bv_eqb_eq] at hr ha
        subst hr; subst ha
        refine bind_ok0 inputSpec _ i m i m _ m [] rfl ?_
        try dsimp only
        rw [hdst]
        refine bind_ok0 (choose (fun bs => realtime_ok_b bs = true)) _ i m bs m _ m [] ?_ ?_
        · exact choose_ok _ bs i m hts
        · exact pure_ok _ i m
      · rw [ite_eq_right hok] at hcond
        exact nomatch hcond
  · rw [ite_eq_right hrt] at H ⊢
    by_cases hcp : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
    · rw [ite_eq_left hcp] at H ⊢
      cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
      | none => rw [hdst] at H; exact nomatch H
      | some bs0 =>
        rw [hdst] at H
        obtain ⟨r, a, bs, heff, hcond⟩ := eff_shape_ok H
        subst heff
        by_cases hok : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp
          && cputime_ok_b bs) = true
        · rw [ite_eq_left hok] at hcond
          simp only [check_result.CheckOk.injEq] at hcond
          obtain ⟨hm, hevs⟩ := hcond
          subst hm; subst hevs
          simp only [Bool.and_eq_true] at hok
          obtain ⟨⟨hr, ha⟩, hts⟩ := hok
          rw [Fs.bv_eqb_eq] at hr ha
          subst hr; subst ha
          refine bind_ok0 inputSpec _ i m i m _ m [] rfl ?_
          try dsimp only
          rw [hdst]
          refine bind_ok0 (choose (fun bs => cputime_ok_b bs = true)) _ i m bs m _ m [] ?_ ?_
          · exact choose_ok _ bs i m hts
          · exact pure_ok _ i m
        · rw [ite_eq_right hok] at hcond
          exact nomatch hcond
    · rw [ite_eq_right hcp] at H ⊢
      by_cases hid : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
      · rw [ite_eq_left hid] at H
        exact nomatch H
      · rw [ite_eq_right hid] at H ⊢
        by_cases henv : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
        · rw [ite_eq_left henv] at H
          exact nomatch H
        · rw [ite_eq_right henv] at H
          cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
          | none => rw [hdst] at H; exact nomatch H
          | some bs0 =>
            rw [hdst] at H
            obtain ⟨r, a, bs, heff, hcond⟩ := eff_shape_ok H
            subst heff
            by_cases hok : (bv_eqb r (BitVec.ofInt 64 0) && bv_eqb a tp
              && timespec_ok_b bs (m_clock m)) = true
            · rw [ite_eq_left hok] at hcond
              simp only [check_result.CheckOk.injEq] at hcond
              obtain ⟨hm, hevs⟩ := hcond
              subst hm; subst hevs
              simp only [Bool.and_eq_true] at hok
              obtain ⟨⟨hr, ha⟩, hts⟩ := hok
              rw [Fs.bv_eqb_eq] at hr ha
              subst hr; subst ha
              refine bind_ok0 getModelSpec _ i m m m _ _ [] rfl ?_
              try dsimp only
              rw [ite_eq_right henv]
              refine bind_ok0 inputSpec _ i m i m _ _ [] rfl ?_
              try dsimp only
              rw [hdst]
              refine bind_ok0 (choose (fun bs => timespec_ok_b bs (m_clock m) = true))
                _ i m bs m _ _ [] ?_ ?_
              · exact choose_ok _ bs i m hts
              · refine bind_ok0 (modify (with_clock (BitVec.ofInt 64 (timespec_ns bs))))
                  _ i m () (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m) _ _ [] ?_ ?_
                · exact modify_ok _ i m
                · exact pure_ok _ i (with_clock (BitVec.ofInt 64 (timespec_ns bs)) m)
            · rw [ite_eq_right hok] at hcond
              exact nomatch hcond

/-! ## Inversion helpers for the monad

    The `complete_*` directions start from the spec, so they need to run
    its steps backwards.  `Checks.Sys.Prelude` already supplies the
    `input` and `getModel` peels; the three below are the ones this spec's
    body also uses (`choose`, and the `modify` the monotonic arm ends
    with).  Each is a plain unfolding of `bind`, local to this file. -/

/-- [bind] over the environment's [choose]: an accepted outcome names the
    chosen value and its evidence.  ([choose] has no inversion lemma, and
    the checkers need one in both outcome shapes.) -/
private theorem choose_bind_ok_inv {A B : Type} (P : A → Prop) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (y : B) (m' : Model) (evs : List event)
    (H : bind (choose P) k i m (.ok y m' evs)) :
    ∃ x, P x ∧ k x i m (.ok y m' evs) := by
  unfold LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.choose at H
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := H
  obtain ⟨x0, hP, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨hx, hm1, hevs1⟩ := hok
  subst hx; subst hm1; subst hevs1
  simp only [List.nil_append] at hevs
  subst hevs
  exact ⟨_, hP, hk⟩

/-- The same inversion in the [Unmodeled] shape: [choose] itself never
    declines, so the decline is the continuation's. -/
private theorem choose_bind_unmodeled_inv {A B : Type} (P : A → Prop) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model)
    (H : bind (choose P) k i m .unmodeled) :
    ∃ x, P x ∧ k x i m .unmodeled := by
  unfold LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.choose at H
  rcases H with h | ⟨x, m1, evs1, hc, hk⟩
  · obtain ⟨x, hP, hok⟩ := h
    exact nomatch hok
  · obtain ⟨x0, hP, hok⟩ := hc
    simp only [Outcome.ok.injEq] at hok
    obtain ⟨hx, hm1, hevs1⟩ := hok
    subst hx; subst hm1; subst hevs1
    exact ⟨_, hP, hk⟩

theorem check_clock_gettime_sound_unmodeled (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_clock_gettime i clkid tp eff m = .CheckUnmodeled) :
    clock_gettime_spec clkid tp i m .unmodeled := by
  unfold check_clock_gettime at H
  unfold clock_gettime_spec
  by_cases hrt : clockid_percall_b clkid = true
  · rw [ite_eq_left hrt] at H ⊢
    refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
    try dsimp only
    cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => exact unmodeled_intro i m
    | some bs0 =>
      rw [hdst] at H
      exact absurd H (eff_shape_ne_unmodeled
        (fun r a bs => if_ok_or_reject_ne_unmodeled _) eff)
  · rw [ite_eq_right hrt] at H ⊢
    by_cases hcp : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
    · rw [ite_eq_left hcp] at H ⊢
      refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
      try dsimp only
      cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
      | none => exact unmodeled_intro i m
      | some bs0 =>
        rw [hdst] at H
        exact absurd H (eff_shape_ne_unmodeled
          (fun r a bs => if_ok_or_reject_ne_unmodeled _) eff)
    · rw [ite_eq_right hcp] at H ⊢
      by_cases hid : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
      · rw [ite_eq_left hid] at H ⊢
        exact unmodeled_intro i m
      · rw [ite_eq_right hid] at H ⊢
        by_cases henv : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
        · rw [ite_eq_left henv] at H
          refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
          try dsimp only
          rw [ite_eq_left henv]
          exact unmodeled_intro i m
        · rw [ite_eq_right henv] at H
          cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
          | none =>
            refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
            try dsimp only
            rw [ite_eq_right henv]
            refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
            try dsimp only
            rw [hdst]
            exact unmodeled_intro i m
          | some bs0 =>
            rw [hdst] at H
            exact absurd H (eff_shape_ne_unmodeled
              (fun r a bs => if_ok_or_reject_ne_unmodeled _) eff)

/-- [bind] over a [modify]: the continuation runs on the updated model. -/
private theorem modify_bind_ok_inv {B : Type} (f : Model → Model) (k : Unit → SysSpec B)
    (i : SyscallInput) (m : Model) (y : B) (m' : Model) (evs : List event)
    (H : bind (modify f) k i m (.ok y m' evs)) :
    k () i (f m) (.ok y m' evs) := by
  unfold LinuxSem.LinuxProcessSem.bind
    LinuxSem.LinuxProcessSem.modify at H
  obtain ⟨x, m1, evs1, evs2, hc, hk, hevs⟩ := H
  cases x
  simp only [Outcome.ok.injEq, true_and] at hc
  obtain ⟨hm1, hevs1⟩ := hc
  subst hm1; subst hevs1
  simp only [List.nil_append] at hevs
  subst hevs
  exact hk

theorem check_clock_gettime_complete_ok (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : clock_gettime_spec clkid tp i m (.ok eff m' evs)) :
    check_clock_gettime i clkid tp eff m = .CheckOk m' evs := by
  unfold check_clock_gettime
  unfold clock_gettime_spec at H
  by_cases hrt : clockid_percall_b clkid = true
  · rw [ite_eq_left hrt] at H ⊢
    have hbody := input_bind_ok_inv _ i m eff m' evs H
    try dsimp only at hbody
    cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none =>
      rw [hdst] at hbody
      try dsimp only at hbody
      exact nomatch hbody
    | some bs0 =>
      rw [hdst] at hbody
      try dsimp only at hbody
      obtain ⟨bs, hP, hk⟩ := choose_bind_ok_inv _ _ _ _ _ _ _ hbody
      simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hk
      obtain ⟨heff, hm, hevs⟩ := hk
      subst heff; subst hm; subst hevs
      try dsimp only
      rw [ite_eq_left (by simp [bv_eqb_refl, hP])]
  · rw [ite_eq_right hrt] at H ⊢
    by_cases hcp : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
    · rw [ite_eq_left hcp] at H ⊢
      have hbody := input_bind_ok_inv _ i m eff m' evs H
      try dsimp only at hbody
      cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
      | none =>
        rw [hdst] at hbody
        try dsimp only at hbody
        exact nomatch hbody
      | some bs0 =>
        rw [hdst] at hbody
        try dsimp only at hbody
        obtain ⟨bs, hP, hk⟩ := choose_bind_ok_inv _ _ _ _ _ _ _ hbody
        simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hk
        obtain ⟨heff, hm, hevs⟩ := hk
        subst heff; subst hm; subst hevs
        try dsimp only
        rw [ite_eq_left (by simp [bv_eqb_refl, hP])]
    · rw [ite_eq_right hcp] at H ⊢
      by_cases hid : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
      · rw [ite_eq_left hid] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hid] at H ⊢
        simp only [LinuxSem.LinuxProcessSem.getModelSpec,
          LinuxSem.LinuxProcessSem.bind_getModel] at H
        by_cases henv : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
        · rw [ite_eq_left henv] at H
          exact nomatch H
        · rw [ite_eq_right henv] at H ⊢
          have hbody2 := input_bind_ok_inv _ i m eff m' evs H
          try dsimp only at hbody2
          cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
          | none =>
            rw [hdst] at hbody2
            try dsimp only at hbody2
            exact nomatch hbody2
          | some bs0 =>
            rw [hdst] at hbody2
            try dsimp only at hbody2
            obtain ⟨bs, hP, hk⟩ := choose_bind_ok_inv _ _ _ _ _ _ _ hbody2
            have hmod := modify_bind_ok_inv _ _ i m eff m' evs hk
            simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hmod
            obtain ⟨heff, hm, hevs⟩ := hmod
            subst heff; subst hm; subst hevs
            try dsimp only
            rw [ite_eq_left (by simp [bv_eqb_refl, hP])]

theorem check_clock_gettime_complete_unmodeled (i : SyscallInput) (clkid tp : word)
    (m : Model) (eff : SyscallEffect)
    (H : clock_gettime_spec clkid tp i m .unmodeled) :
    check_clock_gettime i clkid tp eff m = .CheckUnmodeled := by
  unfold check_clock_gettime
  unfold clock_gettime_spec at H
  by_cases hrt : clockid_percall_b clkid = true
  · rw [ite_eq_left hrt] at H ⊢
    have hbody := input_bind_unmodeled_inv _ i m H
    try dsimp only at hbody
    cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
    | none => rfl
    | some bs0 =>
      rw [hdst] at hbody
      try dsimp only at hbody
      obtain ⟨bs, hP, hk⟩ := choose_bind_unmodeled_inv _ _ _ _ hbody
      simp only [LinuxSem.LinuxProcessSem.pure] at hk
      exact nomatch hk
  · rw [ite_eq_right hrt] at H ⊢
    by_cases hcp : ((clkid.toNat : Int) == CLOCK_PROCESS_CPUTIME_ID) = true
    · rw [ite_eq_left hcp] at H ⊢
      have hbody := input_bind_unmodeled_inv _ i m H
      try dsimp only at hbody
      cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
      | none => rfl
      | some bs0 =>
        rw [hdst] at hbody
        try dsimp only at hbody
        obtain ⟨bs, hP, hk⟩ := choose_bind_unmodeled_inv _ _ _ _ hbody
        simp only [LinuxSem.LinuxProcessSem.pure] at hk
        exact nomatch hk
    · rw [ite_eq_right hcp] at H ⊢
      by_cases hid : (!((clkid.toNat : Int) == CLOCK_MONOTONIC)) = true
      · rw [ite_eq_left hid] at ⊢
      · rw [ite_eq_right hid] at H ⊢
        by_cases henv : (!decide (((m_clock m).toNat : Int) < CLOCK_NS_ENVELOPE)) = true
        · rw [ite_eq_left henv] at ⊢
        · rcases H with h | ⟨x, m1, evs1, hc, hk⟩
          · unfold LinuxSem.LinuxProcessSem.getModelSpec
              LinuxSem.LinuxProcessSem.getModel at h
            exact nomatch h
          · unfold LinuxSem.LinuxProcessSem.getModelSpec
              LinuxSem.LinuxProcessSem.getModel at hc
            simp only [Outcome.ok.injEq] at hc
            obtain ⟨hx, hm1, hevs1⟩ := hc
            rw [hx, hm1] at hk
            rw [ite_eq_right henv] at hk ⊢
            try dsimp only at hk
            have hbody2 := input_bind_unmodeled_inv _ i m hk
            try dsimp only at hbody2
            cases hdst : read_bytes_map i.in_wmem tp (BitVec.ofInt 64 16) with
            | none => rfl
            | some bs0 =>
              rw [hdst] at hbody2
              try dsimp only at hbody2
              obtain ⟨bs, hP, hk⟩ := choose_bind_unmodeled_inv _ _ _ _ hbody2
              simp only [LinuxSem.LinuxProcessSem.bind,
                LinuxSem.LinuxProcessSem.modify,
                LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq,
                reduceCtorEq, and_false, exists_false, false_or] at hk

end LinuxSem.Checks.Sys.Kernel.Time.PosixTimers
