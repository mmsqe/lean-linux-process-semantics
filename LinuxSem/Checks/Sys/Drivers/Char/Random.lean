/-
  * LinuxProcessSem.Checks.Sys.Drivers.Char.Random — the getrandom (278) checkers, and their proofs

  Answers to Linux [drivers/char/random.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`,
  spelled `.CheckOk` / `.CheckReject` / `.CheckUnmodeled`
  (`Checks.Sys.Prelude`); the spec monad `Sys A` is `SysSpec A`; a test in
  `bool` position is a `Bool` comparison (`==`, `decide (· ≤ ·)`); and an
  effect literal is the anonymous constructor pattern
  `⟨r, ws, [], [], [], []⟩` over `SyscallEffect` (`State.lean`), whose
  `mkEffect r ws []` abbreviation is the same term.

  Each proof takes the effect apart into its five lists, closes the
  impossible shapes with `exact nomatch H`, peels the prologue with
  `refine bind_ok0 …` and `dsimp only`, and inverts a spec body with an
  `obtain`/`rcases` at the call site.  Four private helpers factor out the
  arm reasoning: `small_match_ok_inv` and `large_match_ok_inv` invert the
  two arms' matches, and `small_match_ne_unmodeled` /
  `large_match_ne_unmodeled` are the "neither match can answer
  `CheckUnmodeled`" facts; alongside them stand `interrupted_ok`,
  `pure_ok_inv`, `choose_delivery_ok_inv` and `interrupted_ok_inv`.

  `modeled_rw_count` lives in `Sys/Uaccess.lean`
  (`Uaccess.modeled_rw_count`), which `Sys/Drivers/Char/Random.lean`
  already brings in, so no `ReadWrite` module is needed here.  The header
  comments mentioning `readlinkat` are kept at the foot of the file: they
  are the section dividers of the file that continues this one, not
  declarations of this file.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random

namespace LinuxSem.Checks.Sys.Drivers.Char.Random

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi (GRND_NONBLOCK GRND_RANDOM)
open LinuxSem.LinuxProcessSem.Sys.Uaccess (rw_bytes_max modeled_rw_count)
open LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
  (getrandom_errnos getrandom_small_max getrandom_spec)
open LinuxSem.Checks.Sys.Prelude

/-! ## getrandom (278) -/

/-- The zero-byte arm's acceptor, shared by both range verdicts of
    [getrandom_spec]: past a successful import, a zero-byte request either
    joins the interrupted alternative (a return in [getrandom_errnos]) or
    the canonical zero answer [r0] — `0` where `access_ok` passed,
    `errno_ret EFAULT` where it did not.  Everything else is rejected. -/
def check_getrandom_zero (r0 : word) (eff : SyscallEffect) (m : Model) :
    check_result :=
  match eff with
  | ⟨r, [], [], [], [], []⟩ =>
      if errno_ret_in getrandom_errnos r || bv_eqb r r0 then .CheckOk m []
      else .CheckReject
  | _ => .CheckReject

/-- getrandom: the flags gate, the transfer-count gate and the destination
    read are the spec's own, in the spec's order; past them the answer is
    decided by the shape of the effect.

    A NONZERO request of at most [getrandom_small_max] bytes has exactly one
    admissible shape — full delivery at [buf], the return equal to the
    delivered length — so the checker demands precisely that.  Above the
    bound two shapes are admissible: an injectable errno with no write, or
    one write at [buf] whose length is the return, at least 1 and at most
    [cap].  A ZERO-BYTE request is the range verdict alone (see
    [check_getrandom_zero]); it moves nothing, so the write list must be
    empty there. -/
def check_getrandom (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK)) then
    .CheckUnmodeled
  else
  if !modeled_rw_count cap then .CheckUnmodeled   -- see [rw_bytes_max]
  else
  match read_bytes_map i.in_wmem buf cap with
  | none => .CheckUnmodeled   -- unwritable destination buffer
  | some _ =>
      if !w_is0 cap
      then
        if decide ((cap.toNat : Int) ≤ getrandom_small_max)
        then
          -- the small request: full delivery at [buf], and nothing
          -- else — no short count, no -EINTR (see
          -- [Random.getrandom_small_max])
          match eff with
          | ⟨r, [(a, bs)], [], [], [], []⟩ =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && ((bs.length : Int) == (cap.toNat : Int))
              then .CheckOk m []
              else .CheckReject
          | _ => .CheckReject
        else
          match eff with
          | ⟨r, [], [], [], [], []⟩ =>
              if errno_ret_in getrandom_errnos r then .CheckOk m [] else .CheckReject
          | ⟨r, [(a, bs)], [], [], [], []⟩ =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && decide ((1 : Int) ≤ (bs.length : Int))
                 && decide ((bs.length : Int) ≤ (cap.toNat : Int))
              then .CheckOk m []
              else .CheckReject
          | _ => .CheckReject
      else if access_okb buf (cap.toNat : Int)
      then check_getrandom_zero (BitVec.ofInt 64 0) eff m
      else check_getrandom_zero (errno_ret EFAULT) eff m

/-! ## The interrupted alternative, as the checker's proofs use it -/

/-- One admissible interrupted outcome: the errno the spec injects is
    already the effect's return, so the delivered write list is empty. -/
private theorem interrupted_ok (e : Int) (hmem : e ∈ getrandom_errnos)
    (i : SyscallInput) (m : Model) :
    bind (errno_from getrandom_errnos) (fun e => err_ret e) i m
      (.ok (mkEffect (errno_ret e) [] []) m []) :=
  bind_ok0 (errno_from getrandom_errnos) (fun e => err_ret e) i m e m
    (mkEffect (errno_ret e) [] []) m []
    (choose_ok _ e i m hmem) (pure_ok (mkEffect (errno_ret e) [] []) i m)

/-! ## The zero-byte arm -/

/-- Every accepted zero-byte effect is either an injectable errno (the
    interrupted alternative) or exactly the zero answer [r0] the range
    verdict picked — and nothing about the model or the events changes. -/
theorem check_getrandom_zero_sound (r0 : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : check_getrandom_zero r0 eff m = .CheckOk m' evs) :
    m' = m ∧ evs = [] ∧
      ((∃ e, e ∈ getrandom_errnos ∧ eff = mkEffect (errno_ret e) [] []) ∨
        eff = mkEffect r0 [] []) := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    dsimp only [check_getrandom_zero] at H
  · by_cases he : errno_ret_in getrandom_errnos r = true
    · rw [ite_eq_left (by simp [he])] at H
      simp only [check_result.CheckOk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      obtain ⟨e, hmem, hret⟩ := (errno_ret_in_true _ _).mp he
      subst hret
      exact ⟨rfl, rfl, Or.inl ⟨e, hmem, rfl⟩⟩
    · by_cases hr : bv_eqb r r0 = true
      · rw [ite_eq_left (by simp [he, hr])] at H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        exact ⟨rfl, rfl, Or.inr (by rw [(Fs.bv_eqb_eq r r0).mp hr])⟩
      · rw [ite_eq_right (by simp [he, hr])] at H
        exact nomatch H
  all_goals exact nomatch H

/-- The zero-byte acceptor never declines the model: it answers [CheckOk]
    or [CheckReject] only. -/
theorem check_getrandom_zero_no_unmodeled (r0 : word) (eff : SyscallEffect)
    (m : Model) : check_getrandom_zero r0 eff m ≠ .CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
    dsimp only [check_getrandom_zero]
  · by_cases he : errno_ret_in getrandom_errnos r = true <;>
      by_cases hr : bv_eqb r r0 = true <;> simp [he, hr]
  all_goals simp

/-! ## The two effect shapes the nonzero arms accept -/

/-- The small-request arm's match, inverted: an accepted effect is the full
    delivery at [buf] of exactly [cap] bytes, returned as their length, and
    neither the model nor the event list moves. -/
private theorem small_match_ok_inv (buf cap : word) (m m' : Model) (evs : List event)
    (eff : SyscallEffect)
    (H : (match eff with
          | ⟨r, [(a, bs)], [], [], [], []⟩ =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && ((bs.length : Int) == (cap.toNat : Int))
              then check_result.CheckOk m []
              else check_result.CheckReject
          | _ => check_result.CheckReject) = check_result.CheckOk m' evs) :
    ∃ bs, (bs.length : Int) = (cap.toNat : Int) ∧
      eff = mkEffect (len_word bs) [(buf, bs)] [] ∧ m' = m ∧ evs = [] := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    all_goals exact nomatch H
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
      all_goals exact nomatch H
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
      · by_cases hc : (bv_eqb a buf && bv_eqb r (len_word bs)
            && ((bs.length : Int) == (cap.toNat : Int))) = true
        · rw [ite_eq_left hc] at H
          simp only [check_result.CheckOk.injEq] at H
          obtain ⟨hm, hevs⟩ := H
          have h1 := hc
          simp only [Bool.and_eq_true] at h1
          obtain ⟨⟨ha_eq, hr_eq⟩, hlen_eq⟩ := h1
          have ha : a = buf := (Fs.bv_eqb_eq a buf).mp ha_eq
          have hr : r = len_word bs := (Fs.bv_eqb_eq r (len_word bs)).mp hr_eq
          have hlen : (bs.length : Int) = (cap.toNat : Int) := by simpa using hlen_eq
          rw [← hm, ← hevs, ha, hr]
          exact ⟨bs, hlen, rfl, rfl, rfl⟩
        · rw [ite_eq_right hc] at H
          exact nomatch H
      all_goals exact nomatch H

/-- The large-request arm's match, inverted: an accepted effect is either
    an injectable errno with no write, or one nonempty delivery at [buf]
    whose length is the return and does not exceed [cap]. -/
private theorem large_match_ok_inv (buf cap : word) (m m' : Model) (evs : List event)
    (eff : SyscallEffect)
    (H : (match eff with
          | ⟨r, [], [], [], [], []⟩ =>
              if errno_ret_in getrandom_errnos r then check_result.CheckOk m []
              else check_result.CheckReject
          | ⟨r, [(a, bs)], [], [], [], []⟩ =>
              if bv_eqb a buf && bv_eqb r (len_word bs)
                 && decide ((1 : Int) ≤ (bs.length : Int))
                 && decide ((bs.length : Int) ≤ (cap.toNat : Int))
              then check_result.CheckOk m []
              else check_result.CheckReject
          | _ => check_result.CheckReject) = check_result.CheckOk m' evs) :
    ((∃ e, e ∈ getrandom_errnos ∧ eff = mkEffect (errno_ret e) [] []) ∨
      ∃ bs, (1 : Int) ≤ (bs.length : Int) ∧ (bs.length : Int) ≤ (cap.toNat : Int) ∧
        eff = mkEffect (len_word bs) [(buf, bs)] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
    · by_cases he : errno_ret_in getrandom_errnos r = true
      · rw [ite_eq_left he] at H
        simp only [check_result.CheckOk.injEq] at H
        obtain ⟨hm, hevs⟩ := H
        obtain ⟨e, hmem, hret⟩ := (errno_ret_in_true _ _).mp he
        rw [← hm, ← hevs]
        exact ⟨Or.inl ⟨e, hmem, by rw [hret]⟩, rfl, rfl⟩
      · rw [ite_eq_right he] at H
        exact nomatch H
    all_goals exact nomatch H
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
      all_goals exact nomatch H
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> dsimp only at H
      · by_cases hc : (bv_eqb a buf && bv_eqb r (len_word bs)
            && decide ((1 : Int) ≤ (bs.length : Int))
            && decide ((bs.length : Int) ≤ (cap.toNat : Int))) = true
        · rw [ite_eq_left hc] at H
          simp only [check_result.CheckOk.injEq] at H
          obtain ⟨hm, hevs⟩ := H
          have h1 := hc
          simp only [Bool.and_eq_true] at h1
          obtain ⟨⟨⟨ha_eq, hr_eq⟩, hlo_eq⟩, hhi_eq⟩ := h1
          have ha : a = buf := (Fs.bv_eqb_eq a buf).mp ha_eq
          have hr : r = len_word bs := (Fs.bv_eqb_eq r (len_word bs)).mp hr_eq
          have hlo : (1 : Int) ≤ (bs.length : Int) := of_decide_eq_true hlo_eq
          have hhi : (bs.length : Int) ≤ (cap.toNat : Int) := of_decide_eq_true hhi_eq
          rw [← hm, ← hevs, ha, hr]
          exact ⟨Or.inr ⟨bs, hlo, hhi, rfl⟩, rfl, rfl⟩
        · rw [ite_eq_right hc] at H
          exact nomatch H
      all_goals exact nomatch H

/-- Soundness, accepting side: every effect the checker accepts is one the
    spec admits.  The three gates are the spec's own, so they cannot pass
    here; what remains is the shape of the effect against the arm the gates
    select — [small_match_ok_inv] and [large_match_ok_inv] invert the two
    matches, and each inverted shape is the corresponding spec arm. -/
theorem check_getrandom_sound_ok (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getrandom i buf cap flags eff m = .CheckOk m' evs) :
    getrandom_spec buf cap flags i m (.ok eff m' evs) := by
  unfold getrandom_spec
  unfold check_getrandom at H
  by_cases hf : (!(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))) = true
  · rw [ite_eq_left hf] at H
    exact nomatch H
  · rw [ite_eq_right hf] at H ⊢
    try dsimp only
    by_cases hn : (!modeled_rw_count cap) = true
    · rw [ite_eq_left hn] at H
      simp at H
    · rw [ite_eq_right hn] at H ⊢
      try dsimp only
      refine bind_ok0 inputSpec _ i m i m eff m' evs rfl ?_
      try dsimp only
      cases hw : read_bytes_map i.in_wmem buf cap with
      | none =>
        rw [hw] at H
        dsimp only at H
        simp at H
      | some w =>
        try dsimp only
        rw [hw] at H
        dsimp only at H
        by_cases hz : w_is0 cap = true
        · -- a zero-byte request: the range verdict decides what joins -EINTR
          rw [ite_eq_right (by simp [hz])] at H ⊢
          try dsimp only
          by_cases ha : access_okb buf (cap.toNat : Int) = true
          · rw [ite_eq_left ha] at H ⊢
            try dsimp only
            obtain ⟨hm, hevs, hdis⟩ := check_getrandom_zero_sound _ eff m m' evs H
            rw [hm, hevs]
            rcases hdis with ⟨e, hmem, heff⟩ | heff
            · rw [heff]
              exact alt_l _ _ _ _ _ (interrupted_ok e hmem i m)
            · rw [heff]
              exact alt_r _ _ _ _ _ (pure_ok (mkEffect (BitVec.ofInt 64 0) [] []) i m)
          · rw [ite_eq_right ha] at H ⊢
            try dsimp only
            obtain ⟨hm, hevs, hdis⟩ := check_getrandom_zero_sound _ eff m m' evs H
            rw [hm, hevs]
            rcases hdis with ⟨e, hmem, heff⟩ | heff
            · rw [heff]
              exact alt_l _ _ _ _ _ (interrupted_ok e hmem i m)
            · rw [heff]
              exact alt_r _ _ _ _ _ (pure_ok (mkEffect (errno_ret EFAULT) [] []) i m)
        · rw [ite_eq_left (by simp [hz])] at H ⊢
          try dsimp only
          by_cases hsm : decide ((cap.toNat : Int) ≤ getrandom_small_max) = true
          · -- a small request: the full delivery, and only that
            rw [ite_eq_left hsm] at H ⊢
            try dsimp only
            obtain ⟨bs, hlen, heff, hm, hevs⟩ := small_match_ok_inv buf cap m m' evs eff H
            rw [heff, hm, hevs]
            refine bind_ok0 (choose (fun bs' : List byte => (bs'.length : Int) = (cap.toNat : Int)))
              (fun bs' => pure (mkEffect (len_word bs') [(buf, bs')] [])) i m bs m
              (mkEffect (len_word bs) [(buf, bs)] []) m [] ?_ ?_
            · exact choose_ok _ bs i m hlen
            · exact pure_ok _ _ _
          · -- a large request: the interrupted return or a nonempty delivery
            rw [ite_eq_right hsm] at H ⊢
            try dsimp only
            obtain ⟨hdis, hm, hevs⟩ := large_match_ok_inv buf cap m m' evs eff H
            rw [hm, hevs]
            rcases hdis with ⟨e, hmem, heff⟩ | ⟨bs, hlo, hhi, heff⟩
            · rw [heff]
              exact alt_l _ _ _ _ _ (interrupted_ok e hmem i m)
            · rw [heff]
              refine alt_r _ _ _ _ _ ?_
              refine bind_ok0 (choose (fun bs' : List byte =>
                  1 ≤ (bs'.length : Int) ∧ (bs'.length : Int) ≤ (cap.toNat : Int)))
                (fun bs' => pure (mkEffect (len_word bs') [(buf, bs')] [])) i m bs m
                (mkEffect (len_word bs) [(buf, bs)] []) m [] ?_ ?_
              · exact choose_ok _ bs i m ⟨hlo, hhi⟩
              · exact pure_ok _ _ _

/-! ## No unmodeled outcome past the gates -/

/-- The small-request match answers [CheckOk] or [CheckReject] only. -/
private theorem small_match_ne_unmodeled (buf cap : word) (m : Model)
    (eff : SyscallEffect) :
    (match eff with
      | ⟨r, [(a, bs)], [], [], [], []⟩ =>
          if bv_eqb a buf && bv_eqb r (len_word bs)
             && ((bs.length : Int) == (cap.toNat : Int))
          then check_result.CheckOk m []
          else check_result.CheckReject
      | _ => check_result.CheckReject) ≠ check_result.CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
    all_goals simp
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
      all_goals simp
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
      · by_cases hc : (bv_eqb a buf && bv_eqb r (len_word bs)
            && ((bs.length : Int) == (cap.toNat : Int))) = true
        · rw [ite_eq_left hc]
          simp
        · rw [ite_eq_right hc]
          simp
      all_goals simp

/-- The large-request match answers [CheckOk] or [CheckReject] only. -/
private theorem large_match_ne_unmodeled (buf cap : word) (m : Model)
    (eff : SyscallEffect) :
    (match eff with
      | ⟨r, [], [], [], [], []⟩ =>
          if errno_ret_in getrandom_errnos r then check_result.CheckOk m []
          else check_result.CheckReject
      | ⟨r, [(a, bs)], [], [], [], []⟩ =>
          if bv_eqb a buf && bv_eqb r (len_word bs)
             && decide ((1 : Int) ≤ (bs.length : Int))
             && decide ((bs.length : Int) ≤ (cap.toNat : Int))
          then check_result.CheckOk m []
          else check_result.CheckReject
      | _ => check_result.CheckReject) ≠ check_result.CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  cases ws with
  | nil =>
    cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
    · by_cases he : errno_ret_in getrandom_errnos r = true
      · rw [ite_eq_left he]
        simp
      · rw [ite_eq_right he]
        simp
    all_goals simp
  | cons hd tl =>
    obtain ⟨a, bs⟩ := hd
    cases tl with
    | cons hd2 tl2 =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
      all_goals simp
    | nil =>
      cases zs <;> cases us <;> cases cs <;> cases ks <;> try dsimp only
      · by_cases hc : (bv_eqb a buf && bv_eqb r (len_word bs)
            && decide ((1 : Int) ≤ (bs.length : Int))
            && decide ((bs.length : Int) ≤ (cap.toNat : Int))) = true
        · rw [ite_eq_left hc]
          simp
        · rw [ite_eq_right hc]
          simp
      all_goals simp

/-- Soundness, declining side: a [CheckUnmodeled] is only ever the spec's
    own decline.  Past the gates the checker has no declining arm — the two
    nonzero arms answer [CheckOk] or [CheckReject], and the zero-byte arm
    answers [CheckOk] or [CheckReject] too — so the gates and the
    destination read are the only ways in. -/
theorem check_getrandom_sound_unmodeled (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_getrandom i buf cap flags eff m = .CheckUnmodeled) :
    getrandom_spec buf cap flags i m .unmodeled := by
  unfold getrandom_spec
  unfold check_getrandom at H
  by_cases hf : (!(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))) = true
  · rw [ite_eq_left hf] at H ⊢
    exact unmodeled_intro _ _
  · rw [ite_eq_right hf] at H ⊢
    try dsimp only
    by_cases hn : (!modeled_rw_count cap) = true
    · rw [ite_eq_left hn] at H ⊢
      exact unmodeled_intro _ _
    · rw [ite_eq_right hn] at H ⊢
      try dsimp only
      cases hw : read_bytes_map i.in_wmem buf cap with
      | none =>
        rw [hw] at H
        dsimp only at H
        refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
        try dsimp only
        rw [hw]
        try dsimp only
        exact unmodeled_intro _ _
      | some w =>
        try dsimp only
        rw [hw] at H
        dsimp only at H
        refine bind_unmodeled2 inputSpec _ i m i m [] rfl ?_
        try dsimp only
        by_cases hz : w_is0 cap = true
        · rw [ite_eq_right (by simp [hz])] at H ⊢
          try dsimp only
          by_cases ha : access_okb buf (cap.toNat : Int) = true
          · rw [ite_eq_left ha] at H ⊢
            try dsimp only
            exact absurd H (check_getrandom_zero_no_unmodeled _ eff m)
          · rw [ite_eq_right ha] at H ⊢
            try dsimp only
            exact absurd H (check_getrandom_zero_no_unmodeled _ eff m)
        · rw [ite_eq_left (by simp [hz])] at H ⊢
          try dsimp only
          by_cases hsm : decide ((cap.toNat : Int) ≤ getrandom_small_max) = true
          · rw [ite_eq_left hsm] at H ⊢
            try dsimp only
            exact absurd H (small_match_ne_unmodeled buf cap m eff)
          · rw [ite_eq_right hsm] at H ⊢
            try dsimp only
            exact absurd H (large_match_ne_unmodeled buf cap m eff)

/-! ## The spec's accepting shapes, inverted -/

/-- [pure] inverted: the admitted outcome is exactly the value, the given
    model and no events. -/
private theorem pure_ok_inv {A : Type} (x : A) (i : SyscallInput) (m : Model)
    (y : A) (m' : Model) (evs : List event)
    (H : LinuxSem.LinuxProcessSem.pure x i m (.ok y m' evs)) :
    y = x ∧ m' = m ∧ evs = [] := by
  unfold LinuxSem.LinuxProcessSem.pure at H
  simpa using H

/-- A single delivered write, inverted: the spec chose a byte list of the
    predicate's length, and the effect is the one write at [buf] with its
    return equal to the delivered length. -/
private theorem choose_delivery_ok_inv (P : List byte → Prop) (buf : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : bind (choose P) (fun bs => pure (mkEffect (len_word bs) [(buf, bs)] [])) i m
      (.ok eff m' evs)) :
    ∃ bs, P bs ∧ eff = mkEffect (len_word bs) [(buf, bs)] [] ∧ m' = m ∧ evs = [] := by
  obtain ⟨bs, m1, evs1, evs2, hc, hk, hevs⟩ := H
  obtain ⟨bs0, hP, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨rfl, rfl, rfl⟩ := hok
  simp only [LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨bs, hP, rfl, rfl, by simpa using hevs⟩

/-- The interrupted alternative, inverted: an errno from the injectable set
    with no write at all. -/
private theorem interrupted_ok_inv (es : List Int) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : bind (errno_from es) (fun e => err_ret e) i m (.ok eff m' evs)) :
    ∃ e, e ∈ es ∧ eff = mkEffect (errno_ret e) [] [] ∧ m' = m ∧ evs = [] := by
  obtain ⟨e, m1, evs1, evs2, hc, hk, hevs⟩ := H
  unfold errno_from choose at hc
  obtain ⟨e0, hmem, hok⟩ := hc
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨rfl, rfl, rfl⟩ := hok
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
    Outcome.ok.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  exact ⟨e, hmem, rfl, rfl, by simpa using hevs⟩

/-- Completeness, accepting side: every outcome the spec admits is one the
    checker accepts.  The three gates are the spec's own, so nothing is
    admitted past a declined one; the remaining arms are exactly the
    shapes the two matches accept. -/
theorem check_getrandom_complete_ok (i : SyscallInput) (buf cap flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : getrandom_spec buf cap flags i m (.ok eff m' evs)) :
    check_getrandom i buf cap flags eff m = .CheckOk m' evs := by
  unfold check_getrandom
  unfold getrandom_spec at H
  simp only [inputSpec] at H
  by_cases hf : (!(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))) = true
  · rw [ite_eq_left hf] at H
    simp [unmodeled] at H
  · rw [ite_eq_right hf] at H ⊢
    try dsimp only
    by_cases hn : (!modeled_rw_count cap) = true
    · rw [ite_eq_left hn] at H
      simp [unmodeled] at H
    · rw [ite_eq_right hn] at H ⊢
      try dsimp only
      have hbody := input_bind_ok_inv _ i m eff m' evs H
      try dsimp only at hbody
      cases hw : read_bytes_map i.in_wmem buf cap with
      | none =>
        rw [hw] at hbody
        dsimp only at hbody
        simp [unmodeled] at hbody
      | some w =>
        try dsimp only at hbody ⊢
        rw [hw] at hbody
        dsimp only at hbody
        try dsimp only
        by_cases hz : w_is0 cap = true
        · -- the zero-byte arm: the range verdict picks the zero answer
          rw [ite_eq_right (by simp [hz])] at hbody ⊢
          try dsimp only at hbody ⊢
          by_cases ha : access_okb buf (cap.toNat : Int) = true
          · rw [ite_eq_left ha] at hbody ⊢
            try dsimp only at hbody ⊢
            rcases hbody with hbody | hbody
            · obtain ⟨e, hmem, heff, hm, hevs⟩ := interrupted_ok_inv _ i m eff m' evs hbody
              rw [heff, hm, hevs]
              simp [check_getrandom_zero, errno_ret_in_intro getrandom_errnos e hmem]
            · have hp := pure_ok_inv (mkEffect (BitVec.ofInt 64 0) [] []) i m eff m' evs hbody
              obtain ⟨heff, hm, hevs⟩ := hp
              rw [heff, hm, hevs]
              simp [check_getrandom_zero, bv_eqb_refl]
          · rw [ite_eq_right ha] at hbody ⊢
            try dsimp only at hbody ⊢
            rcases hbody with hbody | hbody
            · obtain ⟨e, hmem, heff, hm, hevs⟩ := interrupted_ok_inv _ i m eff m' evs hbody
              rw [heff, hm, hevs]
              simp [check_getrandom_zero, errno_ret_in_intro getrandom_errnos e hmem]
            · have hp := pure_ok_inv (mkEffect (errno_ret EFAULT) [] []) i m eff m' evs hbody
              obtain ⟨heff, hm, hevs⟩ := hp
              rw [heff, hm, hevs]
              simp [check_getrandom_zero, bv_eqb_refl]
        · rw [ite_eq_left (by simp [hz])] at hbody ⊢
          try dsimp only at hbody ⊢
          by_cases hsm : decide ((cap.toNat : Int) ≤ getrandom_small_max) = true
          · -- a small request: the full delivery, and only that
            rw [ite_eq_left hsm] at hbody ⊢
            try dsimp only at hbody ⊢
            obtain ⟨bs, hP, heff, hm, hevs⟩ :=
              choose_delivery_ok_inv _ buf i m eff m' evs hbody
            rw [heff, hm, hevs]
            simp [bv_eqb_refl, hP]
          · -- a large request: the interrupted return or a nonempty delivery
            rw [ite_eq_right hsm] at hbody ⊢
            try dsimp only at hbody ⊢
            rcases hbody with hbody | hbody
            · obtain ⟨e, hmem, heff, hm, hevs⟩ := interrupted_ok_inv _ i m eff m' evs hbody
              rw [heff, hm, hevs]
              simp [errno_ret_in_intro getrandom_errnos e hmem]
            · obtain ⟨bs, hP, heff, hm, hevs⟩ :=
                choose_delivery_ok_inv _ buf i m eff m' evs hbody
              rw [heff, hm, hevs]
              simp [bv_eqb_refl, hP]

/-- Completeness, declining side: wherever the spec leaves the modeled
    surface, the checker declines too.  Past the gates the spec is a chain
    of [choose]/[alt]/[pure], none of which can be [unmodeled]. -/
theorem check_getrandom_complete_unmodeled (i : SyscallInput) (buf cap flags : word)
    (m : Model) (eff : SyscallEffect)
    (H : getrandom_spec buf cap flags i m .unmodeled) :
    check_getrandom i buf cap flags eff m = .CheckUnmodeled := by
  unfold check_getrandom
  unfold getrandom_spec at H
  simp only [inputSpec] at H
  by_cases hf : (!(((flags.toNat : Int) == 0) || ((flags.toNat : Int) == GRND_NONBLOCK))) = true
  · rw [ite_eq_left hf] at H ⊢
  · rw [ite_eq_right hf] at H ⊢
    try dsimp only
    by_cases hn : (!modeled_rw_count cap) = true
    · rw [ite_eq_left hn] at H ⊢
    · rw [ite_eq_right hn] at H ⊢
      try dsimp only
      have hbody := input_bind_unmodeled_inv _ i m H
      try dsimp only at hbody
      cases hw : read_bytes_map i.in_wmem buf cap with
      | none => rw [hw] at hbody
      | some w =>
        try dsimp only at hbody
        rw [hw] at hbody
        dsimp only at hbody
        by_cases hz : w_is0 cap = true
        · rw [ite_eq_right (by simp [hz])] at hbody ⊢
          try dsimp only at hbody ⊢
          by_cases ha : access_okb buf (cap.toNat : Int) = true
          · rw [ite_eq_left ha] at hbody ⊢
            try dsimp only at hbody ⊢
            simp [LinuxSem.LinuxProcessSem.alt,
              LinuxSem.LinuxProcessSem.bind,
              LinuxSem.LinuxProcessSem.choose,
              LinuxSem.LinuxProcessSem.pure,
              errno_from, err_ret, ret_only] at hbody
          · rw [ite_eq_right ha] at hbody ⊢
            try dsimp only at hbody ⊢
            simp [LinuxSem.LinuxProcessSem.alt,
              LinuxSem.LinuxProcessSem.bind,
              LinuxSem.LinuxProcessSem.choose,
              LinuxSem.LinuxProcessSem.pure,
              errno_from, err_ret, ret_only] at hbody
        · rw [ite_eq_left (by simp [hz])] at hbody ⊢
          try dsimp only at hbody ⊢
          by_cases hsm : decide ((cap.toNat : Int) ≤ getrandom_small_max) = true
          · rw [ite_eq_left hsm] at hbody ⊢
            try dsimp only at hbody ⊢
            simp [LinuxSem.LinuxProcessSem.bind,
              LinuxSem.LinuxProcessSem.choose,
              LinuxSem.LinuxProcessSem.pure] at hbody
          · rw [ite_eq_right hsm] at hbody ⊢
            try dsimp only at hbody ⊢
            simp [LinuxSem.LinuxProcessSem.alt,
              LinuxSem.LinuxProcessSem.bind,
              LinuxSem.LinuxProcessSem.choose,
              LinuxSem.LinuxProcessSem.pure,
              errno_from, err_ret, ret_only] at hbody

/-! ## Sanity checks

  The library proofs carry no `vm_compute` goal here — the file is two
  checkers and their proofs — so these are the module's own checks, in the
  spirit of the ones in `Sys/Drivers/Char/Random.lean`: the zero-byte
  acceptor's two accepted shapes, its refusal of a write, and the flags
  gate's fail-closed decline. -/

/-- The canonical zero answer is accepted by the zero-byte acceptor. -/
example (m : Model) :
    check_getrandom_zero (BitVec.ofInt 64 0)
      (mkEffect (BitVec.ofInt 64 0) [] []) m = .CheckOk m [] := by
  simp [check_getrandom_zero, bv_eqb_refl]

/-- …and so is -EINTR: it is the one errno the spec injects, and the
    zero-byte arm keeps the interrupted alternative beside the range
    verdict. -/
example (m : Model) :
    check_getrandom_zero (errno_ret EFAULT)
      (mkEffect (errno_ret EINTR) [] []) m = .CheckOk m [] := by
  simp [check_getrandom_zero, errno_ret_in_intro getrandom_errnos EINTR (by decide)]

/-- A zero-byte return that carries a write is REJECTED: the zero-byte arm
    moves nothing, so no write entry belongs to it. -/
example (m : Model) :
    check_getrandom_zero (BitVec.ofInt 64 0)
      (mkEffect (BitVec.ofInt 64 0) [(0x100, [1])] []) m = .CheckReject := rfl

/-- The `GRND_NONBLOCK` bit the spec accepts is the uapi one, so `2`
    (`GRND_RANDOM`) is past the gate. -/
example :
    (!((((2 : word).toNat : Int) == 0) ||
      (((2 : word).toNat : Int) == GRND_NONBLOCK))) = true := by decide

/-- `GRND_RANDOM` — the blocking /dev/random pool — is DECLINED, not
    answered: the checker's first gate is the spec's own. -/
example (i : SyscallInput) (buf cap : word) (eff : SyscallEffect) (m : Model)
    (hg : (!((((2 : word).toNat : Int) == 0) ||
      (((2 : word).toNat : Int) == GRND_NONBLOCK))) = true) :
    check_getrandom i buf cap (2 : word) eff m = .CheckUnmodeled := by
  unfold check_getrandom
  rw [ite_eq_left hg]

end LinuxSem.Checks.Sys.Drivers.Char.Random
