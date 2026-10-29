/-
  * LinuxProcessSem.Checks.Sys.Mm.Mprotect — the mprotect (226) checkers, and their proofs

  Answers to Linux [mm/mprotect.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `CheckOk` / `CheckReject` / `CheckUnmodeled`
  (`Checks.Sys.Prelude`), and an effect literal is the anonymous constructor
  pattern `⟨r, ws, zs, [], [], []⟩` over `SyscallEffect` (`State.lean`).

  The wrap test is stated as the `Prop` `two_pow_64 ≤ …` — the same
  inequality `Sys/Mm/Mprotect.lean`'s `mprotect_spec` states — rather than
  as a `Bool` test over a `Z` sum.  That is why the case split on it is a
  `by_cases` over a `Prop` while every other gate is a `Bool` equation.

  Where a proof needs the CHECKER's non-answer it cites
  `Prelude.check_ret_only_no_unmodeled` (`check_ret_only` never answers
  `CheckUnmodeled`).  Where it needs the SPEC's non-answer —
  `_complete_unmodeled`'s two answered branches are `alt`s whose arms are
  built from `pure` / `choose` / `modify`, none of which can answer
  `unmodeled` — that is stated once, as the four `private` lemmas below,
  instead of destructing the effect again inline.  They add no public
  surface.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect

namespace LinuxSem.Checks.Sys.Mm.Mprotect

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Sys.Prelude

/-- The `mprotect` (226) checker.

    The same four argument gates as `mprotect_spec`, in the same order,
    each of which the spec answers with one `err_ret` / `ret_only`, then
    the `prot` gate (the spec's decline becomes `CheckUnmodeled`), and
    finally the two answerable address-space shapes:

    - a range contained in one `vm_noaccess` interval AND in one `vm_maps`
      entry: the spec offers `alt (injected errno) (exposure)`.  An
      injected errno comes back as the lone ledger-free `errno_ret`, and
      must carry no zero ledger (`errno_ret_in`); the exposure is the
      budget gate plus `r = 0` plus the range's own zero ledger
      `[(addr, n)]`, and its post-state is `mprotect_model_next`.  Every
      other effect shape, and every zero ledger that is not exactly the
      range, is `CheckReject`: the spec's `alt` admits no other event;
    - a range inside a live `vm_maps` entry and clear of `vm_noaccess`:
      the already-rw no-op, which must return 0 with an empty effect and
      which the spec answers with `ret_only 0`;
    - anything else is `CheckUnmodeled`, exactly where the spec answers
      `unmodeled`. -/
def check_mprotect (addr len prot : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if mprotect_grows_conflict_b prot then
    check_ret_only eff (errno_ret EINVAL) m []
  else if !(((addr.toNat : Int) % page_size) == 0) then
    check_ret_only eff (errno_ret EINVAL) m []
  else if w_is0 len then check_ret_only eff (BitVec.ofInt 64 0) m []
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    check_ret_only eff (errno_ret ENOMEM) m []
  else if !mprotect_modeled_b prot then .CheckUnmodeled
  else
    let nZ := page_round_up_Z (len.toNat : Int)
    let n := BitVec.ofInt 64 nZ
    if map_contains (m_vmmaps m).vm_noaccess addr n &&
        map_contains (m_vmmaps m).vm_maps addr n then
      match eff with
      | ⟨r, [], zs, [], [], []⟩ =>
          if errno_ret_in mprotect_errnos r then
            match zs with
            | [] => .CheckOk m []
            | _ => .CheckReject
          else if mprotect_budget_ok m addr n && w_is0 r && listNN_eqb zs [(addr, n)] then
            .CheckOk (mprotect_model_next m addr n) []
          else .CheckReject
      | _ => .CheckReject
    else if map_contains (m_vmmaps m).vm_maps addr n &&
        region_free (m_vmmaps m).vm_noaccess addr n then
      match eff with
      | ⟨r, [], [], [], [], []⟩ => if w_is0 r then .CheckOk m [] else .CheckReject
      | _ => .CheckReject
    else .CheckUnmodeled

/-! ## Combinators that cannot answer `unmodeled`

    The spec's ambient answers (`pure`, `choose`, `modify`) and the
    `bind`s built from them never answer `unmodeled`.  That is what makes
    `_complete_unmodeled`'s two ANSWERED branches — the two `alt` arms —
    impossible as `unmodeled` outcomes, so only the fail-closed `else`
    arms can be.  Each arm would otherwise be re-destructured to see this;
    here the fact is stated once. -/

private theorem pure_ne_unmodeled (A : Type) (x : A) (i : SyscallInput) (m : Model) :
    ¬ (pure x : SysSpec A) i m .unmodeled := by
  intro h
  exact nomatch h

private theorem choose_ne_unmodeled (A : Type) (P : A → Prop) (i : SyscallInput)
    (m : Model) : ¬ (choose P : SysSpec A) i m .unmodeled := by
  rintro ⟨x, -, h⟩
  exact nomatch h

private theorem modify_ne_unmodeled (f : Model → Model) (i : SyscallInput) (m : Model) :
    ¬ (modify f : SysSpec Unit) i m .unmodeled := by
  intro h
  exact nomatch h

private theorem bind_ne_unmodeled {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model)
    (hc : ¬ c i m .unmodeled)
    (hk : ∀ (x : A) (m1 : Model), ∀ _ : List event, ¬ k x i m1 .unmodeled) :
    ¬ (bind c k : SysSpec B) i m .unmodeled := by
  rintro (h | ⟨x, m1, evs1, h1, h2⟩)
  · exact hc h
  · exact hk x m1 evs1 h2

/-! ## The four agreement theorems -/

section

-- The checker's last arm is a `match` on the effect nested under six
-- tests, and the proofs below drive the same test tree on both sides, so
-- the default recursion budget is not enough to unify the instantiated
-- arms.  (The same option guards the concrete examples in
-- `Sys/Mm/Mprotect.lean`.)
set_option maxRecDepth 1000000

theorem check_mprotect_sound_ok (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_mprotect addr len prot eff m = .CheckOk m' evs) :
    mprotect_spec addr len prot i m (.ok eff m' evs) := by
  unfold check_mprotect at H
  unfold mprotect_spec
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact pure_ok _ i _
  · rw [ite_eq_right hgrows] at H ⊢
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
      exact pure_ok _ i _
    · rw [ite_eq_right halign] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
        exact pure_ok _ i _
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ := (check_ret_only_ok_iff eff (errno_ret ENOMEM) m [] m' evs).mp H
          exact pure_ok _ i _
        · rw [ite_eq_right hbig] at H ⊢
          cases hmod : mprotect_modeled_b prot
          · -- the model does not answer this `prot`: the checker declines
            have hchk : (!mprotect_modeled_b prot) = true := by rw [hmod]; rfl
            rw [ite_eq_left hchk] at H
            exact nomatch H
          · -- the spec's body and the checker's body agree
            have hchk : (!mprotect_modeled_b prot) = false := by rw [hmod]; rfl
            rw [ite_eq_right (by rw [hchk]; simp)] at H
            dsimp only at H ⊢
            rw [ite_eq_left rfl, bind_getModel]
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · -- the covered range: the injected errno or the exposure
              rw [ite_eq_left hcover] at H
              rw [ite_eq_left hcover]
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
              · by_cases herr : errno_ret_in mprotect_errnos r = true
                · -- the injected errno, state untouched, no zero ledger
                  rw [ite_eq_left herr] at H
                  cases zs with
                  | nil =>
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    subst hm
                    subst hevs
                    obtain ⟨e, hmem, hr⟩ := (errno_ret_in_true mprotect_errnos r).mp herr
                    subst hr
                    refine Or.inl ⟨e, m, [], [], ⟨e, hmem, rfl⟩, ?_, rfl⟩
                    exact pure_ok _ i m
                  | cons z zs => exact nomatch H
                · -- the exposure, budget gate and the range's zero ledger
                  rw [ite_eq_right herr] at H
                  by_cases hbudget : (mprotect_budget_ok m addr
                      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                    w_is0 r && listNN_eqb zs
                      [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
                  · rw [ite_eq_left hbudget] at H
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    subst hm
                    subst hevs
                    obtain ⟨hb, hzs⟩ := (Bool.and_eq_true ..).mp hbudget
                    obtain ⟨hb', hr⟩ := (Bool.and_eq_true ..).mp hb
                    have hrz : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r _).mp hr
                    have hzsz : zs = [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))] :=
                      (listNN_eqb_eq zs _).mp hzs
                    subst hrz
                    subst hzsz
                    refine Or.inr ⟨(), m, [], [], choose_ok _ () i m hb', ?_, rfl⟩
                    exact ⟨(), mprotect_model_next m addr
                        (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))), [], [],
                      modify_ok _ i m, pure_ok _ i _, rfl⟩
                  · exact absurd H (by rw [ite_eq_right hbudget]; simp)
              all_goals (exact nomatch H)
            · -- the already-rw no-op, or the decline
              rw [ite_eq_right hcover] at H ⊢
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · rw [ite_eq_left hrw] at H ⊢
                obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                  dsimp only at H
                · by_cases hz : w_is0 r = true
                  · rw [ite_eq_left hz] at H
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    subst hm
                    subst hevs
                    have hr : r = BitVec.ofInt 64 0 := (Fs.bv_eqb_eq r _).mp hz
                    subst hr
                    exact pure_ok _ i m
                  · exact absurd H (by rw [ite_eq_right hz]; simp)
                all_goals (exact nomatch H)
              · rw [ite_eq_right hrw] at H
                exact nomatch H

theorem check_mprotect_sound_unmodeled (addr len prot : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_mprotect addr len prot eff m = .CheckUnmodeled) :
    mprotect_spec addr len prot i m .unmodeled := by
  unfold check_mprotect at H
  unfold mprotect_spec
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  · rw [ite_eq_right hgrows] at H ⊢
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    · rw [ite_eq_right halign] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H
        exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOMEM) m [])
        · rw [ite_eq_right hbig] at H ⊢
          cases hmod : mprotect_modeled_b prot
          · -- the checker declines exactly where the spec does
            dsimp only
            rw [ite_eq_right (by simp)]
            exact unmodeled_intro i m
          · have hchk : (!mprotect_modeled_b prot) = false := by rw [hmod]; rfl
            rw [ite_eq_right (by rw [hchk]; simp)] at H
            dsimp only at H ⊢
            rw [ite_eq_left rfl, bind_getModel]
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · -- the checker answers `CheckOk`/`CheckReject` here, never `CheckUnmodeled`
              rw [ite_eq_left hcover] at H
              exfalso
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases us <;> cases cs <;> cases copyins <;> dsimp only at H
              · by_cases herr : errno_ret_in mprotect_errnos r = true
                · rw [ite_eq_left herr] at H
                  cases zs with
                  | nil => exact nomatch H
                  | cons z zs => exact nomatch H
                · rw [ite_eq_right herr] at H
                  by_cases hbudget : (mprotect_budget_ok m addr
                      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                    w_is0 r && listNN_eqb zs
                      [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
                  · rw [ite_eq_left hbudget] at H
                    exact nomatch H
                  · rw [ite_eq_right hbudget] at H
                    exact nomatch H
              all_goals (exact nomatch H)
            · rw [ite_eq_right hcover] at H ⊢
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · rw [ite_eq_left hrw] at H
                exfalso
                obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                  dsimp only at H
                · by_cases hz : w_is0 r = true
                  · rw [ite_eq_left hz] at H
                    exact nomatch H
                  · rw [ite_eq_right hz] at H
                    exact nomatch H
                all_goals (exact nomatch H)
              · rw [ite_eq_right hrw] at H ⊢
                exact unmodeled_intro i m

theorem check_mprotect_complete_ok (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : mprotect_spec addr len prot i m (.ok eff m' evs)) :
    check_mprotect addr len prot eff m = .CheckOk m' evs := by
  unfold check_mprotect
  unfold mprotect_spec at H
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ := H
    simp [check_ret_only, bv_eqb_refl]
  · rw [ite_eq_right hgrows] at H ⊢
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H ⊢
      obtain ⟨rfl, rfl, rfl⟩ := H
      simp [check_ret_only, bv_eqb_refl]
    · rw [ite_eq_right halign] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        obtain ⟨rfl, rfl, rfl⟩ := H
        simp [check_ret_only, bv_eqb_refl]
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          obtain ⟨rfl, rfl, rfl⟩ := H
          simp [check_ret_only, bv_eqb_refl]
        · rw [ite_eq_right hbig] at H ⊢
          cases hmod : mprotect_modeled_b prot
          · -- the spec declines, so no `Ok` outcome exists
            rw [ite_eq_right (by rw [hmod]; simp)] at H
            exact nomatch H
          · rw [ite_eq_right (by decide)]
            dsimp only at H ⊢
            rw [ite_eq_left hmod, bind_getModel] at H
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · -- the covered range: the errno arm or the exposure arm
              rw [ite_eq_left hcover] at H ⊢
              rw [alt] at H
              rcases H with h1 | h2
              · -- the injected errno: no zero ledger, state untouched
                rcases h1 with ⟨e, m1, evs1, evs2, ⟨e', hmem, hx⟩, hret, hevs⟩
                simp only [Outcome.ok.injEq] at hx
                obtain ⟨heq, hm1, hevs1⟩ := hx
                rw [← heq] at hmem
                subst hm1
                subst hevs1
                obtain ⟨rfl, rfl, rfl⟩ := hret
                subst hevs
                dsimp only
                rw [ite_eq_left (errno_ret_in_intro mprotect_errnos e hmem)]
                rfl
              · -- the exposure: budget gate, the range's zero ledger, the model step
                rcases h2 with ⟨u, m1, evs1, evs2, ⟨v, hbudget, hv⟩, hk, hevs⟩
                simp only [Outcome.ok.injEq] at hv
                obtain ⟨-, hm1, hevs1⟩ := hv
                subst hm1
                subst hevs1
                rcases hk with ⟨u2, m2, evs2', evs3', hmodify, hpure, hevs2⟩
                obtain ⟨rfl, rfl, rfl⟩ := hmodify
                obtain ⟨rfl, rfl, rfl⟩ := hpure
                subst hevs2
                subst hevs
                dsimp only
                have hzero : errno_ret_in mprotect_errnos (BitVec.ofInt 64 0) = false := by
                  decide
                rw [ite_eq_right (by rw [hzero]; simp)]
                have hw0 : w_is0 (BitVec.ofInt 64 0) = true := by
                  unfold w_is0
                  exact bv_eqb_refl _
                have hnn : listNN_eqb
                    [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]
                    [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))] = true :=
                  (listNN_eqb_eq _ _).mpr rfl
                rw [ite_eq_left (by rw [hbudget, hw0, hnn]; rfl)]
                rfl
            · rw [ite_eq_right hcover] at H ⊢
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · -- the already-rw no-op
                rw [ite_eq_left hrw] at H ⊢
                obtain ⟨rfl, rfl, rfl⟩ := H
                dsimp only
                have hw0 : w_is0 (BitVec.ofInt 64 0) = true := by
                  unfold w_is0
                  exact bv_eqb_refl _
                rw [ite_eq_left hw0]
              · rw [ite_eq_right hrw] at H ⊢
                exact nomatch H

theorem check_mprotect_complete_unmodeled (addr len prot : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : mprotect_spec addr len prot i m .unmodeled) :
    check_mprotect addr len prot eff m = .CheckUnmodeled := by
  unfold check_mprotect
  unfold mprotect_spec at H
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H ⊢
    exact nomatch H
  · rw [ite_eq_right hgrows] at H ⊢
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H ⊢
      exact nomatch H
    · rw [ite_eq_right halign] at H ⊢
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H ⊢
        exact nomatch H
      · rw [ite_eq_right hlen] at H ⊢
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H ⊢
          exact nomatch H
        · rw [ite_eq_right hbig] at H ⊢
          cases hmod : mprotect_modeled_b prot
          · -- both sides decline
            rw [ite_eq_left (by decide)]
          · rw [ite_eq_right (by decide)]
            dsimp only at H ⊢
            rw [ite_eq_left hmod, bind_getModel] at H
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · -- the covered range answers `ok` or rejects; it cannot be `unmodeled`
              rw [ite_eq_left hcover] at H ⊢
              exfalso
              rw [alt] at H
              rcases H with h1 | h2
              · exact bind_ne_unmodeled _ _ i m (choose_ne_unmodeled _ _ _ _)
                  (fun e m1 evs1 => pure_ne_unmodeled _ _ _ _) h1
              · exact bind_ne_unmodeled _ _ i m (choose_ne_unmodeled _ _ _ _)
                  (fun _ m1 evs1 => bind_ne_unmodeled _ _ i m1 (modify_ne_unmodeled _ _ _)
                    (fun _ m2 evs2 => pure_ne_unmodeled _ _ _ _)) h2
            · rw [ite_eq_right hcover] at H ⊢
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · rw [ite_eq_left hrw] at H ⊢
                exact nomatch H
              · rw [ite_eq_right hrw] at H ⊢

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the checker
    and its four proofs, nothing else.  The checks below are sanity checks:
    they pin that the four argument gates are the spec's, in the spec's
    order, so each of them answers exactly the `err_ret` / `ret_only`
    the spec does.  They are equalities of `check_result`s, not `decide`
    goals, because `check_result`'s `CheckOk` carries a `Model`, and
    `Model` has no `DecidableEq`. -/

/-- A misaligned address is the -EINVAL gate — for a modeled rw `prot`. -/
example (m : Model) (eff : SyscallEffect) :
    check_mprotect (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 3) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mprotect
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- Both grows bits are -EINVAL before anything else, whatever the rest of
    `prot` holds — the grows gate is the spec's first. -/
example (m : Model) (eff : SyscallEffect) :
    check_mprotect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 (PROT_READ + PROT_WRITE + PROT_GROWSDOWN + PROT_GROWSUP)) eff m =
      check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_mprotect
  rw [ite_eq_left (by decide)]

/-- Zero length answers 0 — even for PROT_NONE, which nothing else would
    interpret: the `[!len]` gate precedes the `prot` gate. -/
example (m : Model) (eff : SyscallEffect) :
    check_mprotect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 PROT_NONE) eff m =
      check_ret_only eff (BitVec.ofInt 64 0) m [] := by
  unfold check_mprotect
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A wrapping length is -ENOMEM, again before `prot` is read. -/
example (m : Model) (eff : SyscallEffect) :
    check_mprotect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 3) eff m =
      check_ret_only eff (errno_ret ENOMEM) m [] := by
  unfold check_mprotect
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A `prot` the model does not answer declines at nonzero length, and only
    there: the `prot` gate comes last. -/
example (m : Model) (eff : SyscallEffect) :
    check_mprotect (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 PROT_NONE) eff m = .CheckUnmodeled := by
  unfold check_mprotect
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]

end LinuxSem.Checks.Sys.Mm.Mprotect
