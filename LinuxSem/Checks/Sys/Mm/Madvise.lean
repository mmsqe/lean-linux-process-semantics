/-
  * LinuxProcessSem.Checks.Sys.Mm.Madvise — the madvise (233) checker, and its proofs

  Answers to Linux [mm/madvise.c]: this file holds the checker for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checker here is executable, and its proofs relate it to the
  relational spec in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous constructor
  pattern `⟨r, [], zs, [], [], []⟩` over `SyscallEffect` (`State.lean`).

  The wrap test is stated as the `Prop` `two_pow_64 ≤ …` — the same
  inequality the spec's `madvise_spec` states — rather than as a `Bool` test
  over a `Z` sum.  That is why the case split on it is a `by_cases` over a
  `Prop` while every other gate is a `Bool` equation.

  The last arm's match on the effect is read backwards through
  `eff_shape_ok` (accepted) and `arm_ne_unmodeled` (declined) — the same two
  shape lemmas, for the same reason, that
  `Checks/Sys/Kernel/Time/PosixTimers.lean` records.  The spec's two monadic
  steps are peeled with `get_model_bind_ok_inv` from `Checks.Sys.Prelude`
  plus this file's `modify_bind_ok_inv`.  The `getModel` peel is done BEFORE
  the ledger gate is split: the spec's gate sits under the `bind`'s
  continuation, so the gate's model is the continuation's bound variable
  until `bind_getModel` has been rewritten away.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

namespace LinuxSem.Checks.Sys.Mm.Madvise

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Sys.Prelude

/-- The `madvise` (233) checker.

    Gate for gate the spec's order: alignment, then the advice, then the
    zero length, then the wrapping range, then the ledger.  On the
    answered shape the effect must be exactly the zero-fill of the
    page-rounded range with a zero return, and the post-model is the
    spec's `madvise_dontneed_next`.

    The first four gates answer the spec's `err_ret` / `ret_only`, and the
    advice gate declines (`CheckUnmodeled`) exactly where the spec does —
    the spec's own argument for declining an unknown advice value (the
    kernel's `madvise_behavior_valid` list depends on the configuration)
    is in `Sys/Mm/Madvise.lean`'s header. -/
def check_madvise (addr len advice : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(((addr.toNat : Int) % page_size) == 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else if !madvise_dontneed_b advice then .CheckUnmodeled
  else if w_is0 len then check_ret_only eff (BitVec.ofInt 64 0) m []
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (len.toNat : Int)
    let n := BitVec.ofInt 64 nZ
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      match eff with
      | ⟨r, [], zs, [], [], []⟩ =>
          if w_is0 r && listNN_eqb zs [(addr, n)] then
            .CheckOk (madvise_dontneed_next m addr n) []
          else .CheckReject
      | _ => .CheckReject
    else .CheckUnmodeled

/-! ## Inversion helpers for the effect shape

    The checker's answered arm ends with one match — a zero return, no
    writes, the claimed zero ranges, no unmaps, no copies, no copy-ins —
    and both `sound_*` proofs have to read it backwards, in each answer
    shape.  These two lemmas do it once, so the proofs stay at the level of
    the branch condition.  (The same two, for the same reason, head
    `Checks/Sys/Kernel/Time/PosixTimers.lean`.) -/

/-- The answered arm never answers `CheckUnmodeled`: its branch body is a
    `CheckOk`/`CheckReject` test, and the fallback is `CheckReject`.  (The
    branch body is spelled out here rather than passed as an argument, so
    that the `let`-bound range `n` stays a parameter of the statement.) -/
private theorem arm_ne_unmodeled (addr n : word) (m : Model) (eff : SyscallEffect) :
    ((match eff with
      | ⟨r, [], zs, [], [], []⟩ =>
          if w_is0 r && listNN_eqb zs [(addr, n)] then
            check_result.CheckOk (madvise_dontneed_next m addr n) []
          else check_result.CheckReject
      | _ => check_result.CheckReject) : check_result) ≠ check_result.CheckUnmodeled := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  intro hh
  split at hh
  · split at hh <;> exact nomatch hh
  · exact nomatch hh

/-- An accepted outcome forces the effect's shape: a zero return, an
    empty write list, the zero ranges, and nothing else — and the branch
    body accepted it. -/
private theorem eff_shape_ok {f : word → List (word × word) → check_result}
    {eff : SyscallEffect} {m' : Model} {evs : List event}
    (H : (match eff with
          | ⟨r, [], zs, [], [], []⟩ => f r zs
          | _ => .CheckReject) = .CheckOk m' evs) :
    ∃ r zs, eff = ⟨r, [], zs, [], [], []⟩ ∧ f r zs = .CheckOk m' evs := by
  obtain ⟨r, ws, zs, us, cs, ks⟩ := eff
  split at H
  · rename_i r' zs' heq
    exact ⟨r', zs', heq, H⟩
  · exact nomatch H

/-! ## The monad step the spec's answered arm ends with

    `Checks.Sys.Prelude` supplies the `input` and `getModel` peels; the
    `modify` one below is the other step `madvise_spec`'s answered shape
    takes, and it is the same lemma
    `Checks/Sys/Kernel/Time/PosixTimers.lean` carries privately for its
    clock update. -/

/-- `bind` over a `modify`: the continuation runs on the updated model. -/
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

/-! ## The four agreement theorems -/

section

-- The checker's last arm is a `match` on the effect nested under six
-- tests, and the proofs below drive the same test tree on both sides, so
-- the default recursion budget is not enough to unify the instantiated
-- arms.
set_option maxRecDepth 1000000

theorem check_madvise_sound_ok (addr len advice : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_madvise addr len advice eff m = .CheckOk m' evs) :
    madvise_spec addr len advice i m (.ok eff m' evs) := by
  unfold check_madvise at H
  unfold madvise_spec
  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
  · rw [ite_eq_left halign] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact pure_ok _ i _
  · rw [ite_eq_right halign] at H ⊢
    by_cases hadv : (!madvise_dontneed_b advice) = true
    · rw [ite_eq_left hadv] at H
      exact nomatch H
    · rw [ite_eq_right hadv] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ :=
          (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        exact pure_ok _ i _
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤
            (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
          exact pure_ok _ i _
        · rw [ite_eq_right hbig] at H ⊢
          dsimp only at H ⊢
          by_cases hok : madvise_dontneed_ok (m_vmmaps m) addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
          · -- the ledger gate passes: the zero return and the range's ledger
            rw [ite_eq_left hok] at H
            obtain ⟨r, zs, heff, hcond⟩ := eff_shape_ok H
            subst heff
            rw [bind_getModel]
            try dsimp only
            rw [ite_eq_left hok]
            by_cases hc : (w_is0 r && listNN_eqb zs
                [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
            · rw [ite_eq_left hc] at hcond
              simp only [check_result.CheckOk.injEq] at hcond
              obtain ⟨hm, hevs⟩ := hcond
              subst hm; subst hevs
              simp only [Bool.and_eq_true] at hc
              obtain ⟨hr, hzs⟩ := hc
              have hr0 : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r _).mp hr
              have hzs' : zs =
                  [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))] :=
                (listNN_eqb_eq zs _).mp hzs
              subst hr0; subst hzs'
              exact bind_ok0
                (modify fun _ => madvise_dontneed_next m addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))))
                (fun _ => pure (mkEffect (BitVec.ofInt 64 0) []
                  [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]))
                i m () _ _ _ [] (modify_ok _ i m) (pure_ok _ i _)
            · rw [ite_eq_right hc] at hcond
              exact nomatch hcond
          · rw [ite_eq_right hok] at H
            exact nomatch H

theorem check_madvise_sound_unmodeled (addr len advice : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_madvise addr len advice eff m = .CheckUnmodeled) :
    madvise_spec addr len advice i m .unmodeled := by
  unfold check_madvise at H
  unfold madvise_spec
  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
  · rw [ite_eq_left halign] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right halign] at H ⊢
    by_cases hadv : (!madvise_dontneed_b advice) = true
    · -- the advice gate: the checker and the spec both decline
      rw [ite_eq_left hadv] at H ⊢
      exact unmodeled_intro i m
    · rw [ite_eq_right hadv] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤
            (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · rw [ite_eq_right hbig] at H ⊢
          dsimp only at H ⊢
          rw [bind_getModel]
          try dsimp only
          by_cases hok : madvise_dontneed_ok (m_vmmaps m) addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
          · rw [ite_eq_left hok] at H ⊢
            exact absurd H (arm_ne_unmodeled addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) m eff)
          · rw [ite_eq_right hok] at H ⊢
            exact unmodeled_intro i m

theorem check_madvise_complete_ok (addr len advice : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : madvise_spec addr len advice i m (.ok eff m' evs)) :
    check_madvise addr len advice eff m = .CheckOk m' evs := by
  unfold check_madvise
  unfold madvise_spec at H
  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
  · rw [ite_eq_left halign] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right halign] at H ⊢
    by_cases hadv : (!madvise_dontneed_b advice) = true
    · rw [ite_eq_left hadv] at H ⊢
      exact nomatch H
    · rw [ite_eq_right hadv] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ := H
        simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤
            (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ := H
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hbig] at H ⊢
          dsimp only at H ⊢
          rw [bind_getModel] at H
          try dsimp only at H
          by_cases hok : madvise_dontneed_ok (m_vmmaps m) addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
          · -- the spec's answered shape: the page-rounded range, zero return
            rw [ite_eq_left hok] at H ⊢
            have hk := modify_bind_ok_inv _ _ i m eff m' evs H
            simp only [LinuxSem.LinuxProcessSem.pure,
              Outcome.ok.injEq] at hk
            obtain ⟨heff, hm, hevs⟩ := hk
            subst heff; subst hm; subst hevs
            try dsimp only
            have hw0 : w_is0 (BitVec.ofInt 64 0) = true := by
              unfold w_is0
              exact bv_eqb_refl _
            have hnn : listNN_eqb
                [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]
                [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))] = true :=
              (listNN_eqb_eq _ _).mpr rfl
            rw [ite_eq_left (by rw [hw0, hnn]; rfl)]
          · -- the spec declines here, so no `Ok` outcome exists
            rw [ite_eq_right hok] at H
            exact nomatch H

theorem check_madvise_complete_unmodeled (addr len advice : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : madvise_spec addr len advice i m .unmodeled) :
    check_madvise addr len advice eff m = .CheckUnmodeled := by
  unfold check_madvise
  unfold madvise_spec at H
  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
  · rw [ite_eq_left halign] at H ⊢
    exact nomatch H
  · rw [ite_eq_right halign] at H ⊢
    by_cases hadv : (!madvise_dontneed_b advice) = true
    · -- the checker and the spec both decline, and `rw` closes the goal
      rw [ite_eq_left hadv] at H ⊢
    · rw [ite_eq_right hadv] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤
            (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hbig] at H ⊢
          dsimp only at H ⊢
          rw [bind_getModel] at H
          try dsimp only at H
          by_cases hok : madvise_dontneed_ok (m_vmmaps m) addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
          · -- the spec's answered shape answers `ok`; it cannot be `unmodeled`
            rw [ite_eq_left hok] at H ⊢
            rcases H with h | ⟨x, m1, evs1, hc, hk⟩
            · unfold LinuxSem.LinuxProcessSem.modify at h
              exact nomatch h
            · exact nomatch hk
          · -- both sides decline
            rw [ite_eq_right hok] at H ⊢

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the checker
    and its four proofs, nothing else.  The checks below are sanity checks:
    they pin that the checker's four argument gates are the spec's, in the
    spec's order, so each answers exactly the `err_ret` / `ret_only` the
    spec does, and that a decline and the ledger gate fall where the spec
    puts them.  They are equalities of `check_result`s, not `decide`
    goals, because `check_result`'s `CheckOk` carries a `Model`, and
    `Model` has no `DecidableEq`. -/

/-- A misaligned address is the -EINVAL gate — for a known advice value. -/
example (m : Model) (eff : SyscallEffect) :
    check_madvise (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 MADV_DONTNEED) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_madvise
  rw [ite_eq_left (by decide)]

/-- Alignment is tested BEFORE the advice: an unknown advice value at a
    misaligned address is -EINVAL, not a decline — exactly the kernel's
    order (`is_valid_madvise`). -/
example (m : Model) (eff : SyscallEffect) :
    check_madvise (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 99) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_madvise
  rw [ite_eq_left (by decide)]

/-- An advice value other than MADV_DONTNEED declines at an aligned,
    nonzero-length address: the checker fails closed where the spec does,
    rather than answering -EINVAL. -/
example (m : Model) (eff : SyscallEffect) :
    check_madvise (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 99) eff m = .CheckUnmodeled := by
  unfold check_madvise
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- Zero length answers 0 — behind the alignment and advice gates, which
    is what makes the kernel's ordering observable. -/
example (m : Model) (eff : SyscallEffect) :
    check_madvise (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 MADV_DONTNEED) eff m =
      check_ret_only eff (BitVec.ofInt 64 0) m [] := by
  unfold check_madvise
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A length whose page rounding wraps is -EINVAL, again behind the earlier
    gates — `is_valid_madvise`'s two wrapping refusals in one test. -/
example (m : Model) (eff : SyscallEffect) :
    check_madvise (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 MADV_DONTNEED) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_madvise
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A range the ledger does not describe declines at the last gate — no
    state change and no errno, because a hole means both at once (see
    `Sys/Mm/Madvise.lean`'s header). -/
example (m : Model) (eff : SyscallEffect) (hm : m_vmmaps m =
    mkVmMaps [] [] (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) 0x100000) :
    check_madvise (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 MADV_DONTNEED) eff m = .CheckUnmodeled := by
  unfold check_madvise
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), hm,
    ite_eq_right (by decide)]

end LinuxSem.Checks.Sys.Mm.Madvise
