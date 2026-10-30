/-
  * LinuxSem.Checks.NoaccessOwned.Writers — the four writers of the two
    ledgers that `brk` is not: `munmap`, `mprotect`, `mremap` and `mmap`.

    `brk` is `NoaccessOwned/Brk.lean` because it is the writer that made the
    plain `noaccess_pages_owned` fail.  These four are ordinary proof work
    on top of `NoaccessOwned/Core.lean`'s shapes, and each proof is the
    checker's OWN walk (`Chain/Writers.lean` for `vm_wf`, `MapsFit.lean` for
    the end bound) — same guards, same order, same extraction out of the
    boolean chains — with `na_inv_cut_na` / `na_inv_cut_both` /
    `na_inv_cons_both` / `na_inv_cons_maps` / `na_inv_add_owned` /
    `na_inv_munmap` / `na_inv_mremap` at the leaves.

    Three helper lemmas make the leaves read like the original's: a
    page-alignment guard that FAILS, a `w_is0` guard that fails, and the
    fact that a page-rounded length of a word length is a word (the
    accepting branches are the ones where the checker's own overflow test
    said so).
-/

import LinuxSem.Checks.NoaccessOwned.Brk

set_option autoImplicit false
set_option maxRecDepth 1000000

/- The invariant's arm shape (`arm_preserves_na`) fixes FOUR hypotheses —
  `vm_wf`, `vm_fit`, `na_inv` and the checker's answer — and a writer that
  reads only some of them still has to take all four so the
  `checked_table` enumeration can apply it uniformly.  `mprotect` reads
  neither `vm_wf` nor `vm_fit` (it cuts the protected list alone), and
  `mremap` reads no `vm_fit` (it re-records the source rather than
  re-bounding it), so the linter is off here rather than the binders being
  renamed away from the field names the enumeration uses. -/
set_option linter.unusedVariables false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.NoaccessOwned

open LinuxSem.Common.RocqSpelling

/-- The `!((x % page_size) == 0)` guard the checkers use FAILS exactly when
    `x` is page aligned. -/
theorem aligned_of_not_negb_beq (x : Int) (H : ¬ (!((x % page_size) == 0)) = true) :
    x % page_size = 0 := by
  have hbeq : ((x % page_size) == 0) = true := by
    cases h : ((x % page_size) == 0)
    · rw [h] at H
      simp at H
    · rfl
  simpa using hbeq

/-- A `w_is0` guard that fails says the word is nonzero. -/
theorem w_is0_false_of_not (w : word) (H : ¬ (w_is0 w = true)) : w_is0 w = false := by
  cases h : w_is0 w
  · rfl
  · exact absurd h H

/-! ## `mprotect` — cuts the PROTECTED list only -/

theorem check_mprotect_preserves_na (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mprotect addr len prot eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
  unfold check_mprotect at H
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hna
  · rw [ite_eq_right hgrows] at H
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hna
    · rw [ite_eq_right halign] at H
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hna
      · rw [ite_eq_right hlen] at H
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hna
        · rw [ite_eq_right hbig] at H
          have hpulen : 0 ≤ page_round_up_Z (len.toNat : Int) := by
            have := pu_ge (len.toNat : Int)
            omega
          have hlenlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by omega
          cases hmod : mprotect_modeled_b prot
          · have hchk : (!mprotect_modeled_b prot) = true := by rw [hmod]; rfl
            rw [ite_eq_left hchk] at H
            exact nomatch H
          · have hchk : (!mprotect_modeled_b prot) = false := by rw [hmod]; rfl
            rw [ite_eq_right (by rw [hchk]; simp)] at H
            dsimp only at H
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · rw [ite_eq_left hcover] at H
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases us <;> cases cs <;> cases copyins <;> try dsimp only at H
              · by_cases herr : errno_ret_in mprotect_errnos r = true
                · rw [ite_eq_left herr] at H
                  cases zs with
                  | nil =>
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    rw [hm.symm]
                    exact Hna
                  | cons z zs => exact nomatch H
                · rw [ite_eq_right herr] at H
                  by_cases hbudget : (mprotect_budget_ok m addr
                      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                    w_is0 r && listNN_eqb zs
                      [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
                  · rw [ite_eq_left hbudget] at H
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    rw [hm.symm]
                    have halv : bv_unsigned addr % page_size = 0 := by
                      refine aligned_of_not_negb_beq _ ?_
                      intro hc
                      exact halign (by rw [hc])
                    have hnv : bv_unsigned (BitVec.ofInt 64
                        (page_round_up_Z (len.toNat : Int))) % page_size = 0 := by
                      have hpu : bv_unsigned (BitVec.ofInt 64
                          (page_round_up_Z (len.toNat : Int)))
                          = page_round_up_Z (len.toNat : Int) := by
                        exact u64 _ ⟨hpulen, hlenlt⟩
                      rw [hpu]
                      exact pu_aligned _
                    rw [vmm_mprotect_next]
                    unfold na_inv
                    exact na_inv_cut_na (vm_maps (m_vmmaps m))
                      (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m)))
                      (bv_unsigned addr)
                      (bv_unsigned addr + bv_unsigned (BitVec.ofInt 64
                        (page_round_up_Z (len.toNat : Int))))
                      halv (aligned_add _ _ halv hnv) Hna
                  · exact absurd H (by rw [ite_eq_right hbudget]; simp)
              all_goals (exact nomatch H)
            · rw [ite_eq_right hcover] at H
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · rw [ite_eq_left hrw] at H
                obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins <;>
                  try dsimp only at H
                · by_cases hz : w_is0 r = true
                  · rw [ite_eq_left hz] at H
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    rw [hm.symm]
                    exact Hna
                  · exact absurd H (by rw [ite_eq_right hz]; simp)
                all_goals (exact nomatch H)
              · rw [ite_eq_right hrw] at H
                exact nomatch H


theorem check_munmap_preserves_na (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
  unfold check_munmap at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hna
  · rw [ite_eq_right hi] at H
    dsimp only at H
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hna
    · rw [ite_eq_right hbig] at H
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
      have halv : bv_unsigned addr % page_size = 0 := by
        refine aligned_of_not_negb_beq _ ?_
        intro hc
        exact hi (by rw [hc]; rfl)
      have htop : TASK_SIZE < two_pow_64 := by decide
      have hpulen : 0 ≤ page_round_up_Z (len.toNat : Int) := by
        have := pu_ge (len.toNat : Int)
        omega
      have hlenlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by omega
      have hnv : bv_unsigned n % page_size = 0 := by
        have hpu : bv_unsigned n = page_round_up_Z (len.toNat : Int) := by
          rw [← hn]
          exact u64 _ ⟨hpulen, hlenlt⟩
        rw [hpu]
        exact pu_aligned _
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr n = true
      · rw [ite_eq_left hhas] at H
        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> try dsimp only at H
        · by_cases hc : (w_is0 r && listNN_eqb us [(addr, n)]) = true
          · rw [ite_eq_left hc] at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨hm, hevs⟩ := H
            rw [hm.symm]
            rw [vmm_mmap_destroyed]
            refine na_inv_munmap (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m))
              (bv_unsigned (vm_brk (m_vmmaps m))) addr n Hwf hhas halv hnv Hna
          · exact absurd H (by rw [ite_eq_right hc]; simp)
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hna
        · rw [ite_eq_right hfree] at H
          by_cases hcut : munmap_cut_ok (m_vmmaps m) addr
              (page_round_up_Z (len.toNat : Int)) = true
          · rw [ite_eq_left hcut] at H
            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
            cases ws <;> cases zs <;> cases cs <;> cases copyins <;> try dsimp only at H
            · by_cases he : errno_ret_in munmap_errnos r = true
              · rw [ite_eq_left he] at H
                cases us with
                | nil =>
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm]
                  exact Hna
                | cons u us' => exact nomatch H
              · rw [ite_eq_right he] at H
                by_cases hc : (w_is0 r && listNN_eqb us [(addr, n)]) = true
                · rw [ite_eq_left hc] at H
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm, vmm_mmap_destroyed]
                  exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m))
                    (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr)
                    (bv_unsigned addr + bv_unsigned n) Hfit halv (aligned_add _ _ halv hnv) Hna
                · rw [ite_eq_right hc] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hcut] at H
            exact nomatch H


theorem check_mremap_preserves_na (old old_size new_size flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_mremap old old_size new_size flags eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
  unfold check_mremap at H
  dsimp only at H
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hshape] at H
    exact nomatch H
  · rw [ite_eq_right hshape] at H
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hna
    · rw [ite_eq_right halign] at H
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hna
      · rw [ite_eq_right hnew] at H
        by_cases htask : (TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)
        · rw [ite_eq_left htask] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hna
        · rw [ite_eq_right htask] at H
          by_cases hold : page_align_is0_b old_size = true
          · rw [ite_eq_left hold] at H
            exact nomatch H
          · rw [ite_eq_right hold] at H
            have hnewP := page_align_is0_false_parts new_size hnew
            have holdP := page_align_is0_false_parts old_size hold
            have hnewPos : 0 < page_round_up_Z (new_size.toNat : Int) := by
              apply page_round_up_pos
              have h := w_is0_false new_size hnewP.1
              simp only [bv_unsigned_def] at h
              omega
            have holdPos : 0 < page_round_up_Z (old_size.toNat : Int) := by
              apply page_round_up_pos
              have h := w_is0_false old_size holdP.1
              simp only [bv_unsigned_def] at h
              omega
            generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H
            generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H
            generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H
            generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H
            have hold_lt : old_nZ < two_pow_64 := by rw [← hOldN]; exact holdP.2
            have hnew_lt : new_nZ < two_pow_64 := by rw [← hNewN]; exact hnewP.2
            have hold_nn : 0 ≤ old_nZ := by
              rw [← hOldN]
              have := page_round_up_Z_ge (old_size.toNat : Int) (by omega)
              omega
            have hnew_nn : 0 ≤ new_nZ := by
              rw [← hNewN]
              have := page_round_up_Z_ge (new_size.toNat : Int) (by omega)
              omega
            have holdv : bv_unsigned old_n = old_nZ := by
              rw [← hOldW]
              exact u64 old_nZ ⟨hold_nn, hold_lt⟩
            have hnewv : bv_unsigned new_n = new_nZ := by
              rw [← hNewW]
              exact u64 new_nZ ⟨hnew_nn, hnew_lt⟩
            by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                mremap_backing_uniform_b m old old_n)) = true
            · rw [ite_eq_left hsrc] at H
              exact nomatch H
            · rw [ite_eq_right hsrc] at H
              have hsrcb : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                  mremap_backing_uniform_b m old old_n) = true := by
                cases hb : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                    mremap_backing_uniform_b m old old_n)
                · rw [hb] at hsrc
                  simp at hsrc
                · rfl
              have hsrcb' : mremap_source_b (m_vmmaps m) old old_n old_nZ = true :=
                (Bool.and_eq_true ..).mp hsrcb |>.1
              unfold mremap_source_b at hsrcb'
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hsrcb'
              have hhas : map_has (vm_maps (m_vmmaps m)) old old_n = true := hsrcb'.1.2
              have hfree : region_free (vm_noaccess (m_vmmaps m)) old old_n = true := hsrcb'.2
              have hal : bv_unsigned old % page_size = 0 := by
                refine aligned_of_not_negb_beq _ ?_
                intro hc
                exact halign (by rw [hc])
              have hnv : bv_unsigned old_n % page_size = 0 := by
                rw [holdv, ← hOldN]
                exact pu_aligned _
              by_cases heq : (old_nZ == new_nZ) = true
              · rw [ite_eq_left heq] at H
                rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                exact Hna
              · rw [ite_eq_right heq] at H
                obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                cases ws <;> cases copyins <;> try dsimp only at H
                · by_cases herr : errno_ret_in mremap_errnos r = true
                  · rw [ite_eq_left herr] at H
                    cases zs <;> cases us <;> cases cs <;> try dsimp only at H
                    · simp only [check_result.CheckOk.injEq] at H
                      obtain ⟨hm, hevs⟩ := H
                      rw [hm.symm]
                      exact Hna
                    all_goals (exact nomatch H)
                  · rw [ite_eq_right herr] at H
                    by_cases hret : bv_eqb r old = true
                    · rw [ite_eq_left hret] at H
                      by_cases hlt : new_nZ < old_nZ
                      · rw [ite_eq_left hlt] at H
                        by_cases hshrink : (listNN_eqb zs [] &&
                            listNN_eqb us
                              [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                            listCopy_eqb cs []) = true
                        · rw [ite_eq_left hshrink] at H
                          simp only [check_result.CheckOk.injEq] at H
                          obtain ⟨hm, hevs⟩ := H
                          rw [hm.symm]
                          rw [vmm_mremap_next]
                          exact na_inv_mremap (vm_maps (m_vmmaps m))
                            (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m)))
                            old old_n old new_n Hwf hhas hal hnv hfree Hna
                        · rw [ite_eq_right hshrink] at H
                          exact nomatch H
                      · rw [ite_eq_right hlt] at H
                        by_cases hgrow : mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                        · rw [ite_eq_left hgrow] at H
                          by_cases hcond : (listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) &&
                              listNN_eqb us [] && listCopy_eqb cs []) = true
                          · rw [ite_eq_left hcond] at H
                            simp only [check_result.CheckOk.injEq] at H
                            obtain ⟨hm, hevs⟩ := H
                            rw [hm.symm]
                            have hg : region_free (vm_reserved (m_vmmaps m) ++
                                map_remove (vm_maps (m_vmmaps m)) old) old new_n = true := by
                              unfold mremap_inplace_grow_b at hgrow
                              dsimp only at hgrow
                              simp only [Bool.and_eq_true] at hgrow
                              exact hgrow.1.2
                            have hceil : ((old.toNat : Int) + new_nZ ≤
                                alloc_top (m_vmmaps m)) := by
                              unfold mremap_inplace_grow_b at hgrow
                              dsimp only at hgrow
                              simp only [Bool.and_eq_true, decide_eq_true_eq] at hgrow
                              exact hgrow.1.1
                            rw [vmm_mremap_next]
                            exact na_inv_mremap (vm_maps (m_vmmaps m))
                              (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m)))
                              old old_n old new_n Hwf hhas hal hnv hfree Hna
                          · rw [ite_eq_right hcond] at H
                            exact nomatch H
                        · rw [ite_eq_right hgrow] at H
                          exact nomatch H
                    · rw [ite_eq_right hret] at H
                      by_cases hcond : (decide (old_nZ < new_nZ) &&
                          mremap_fresh_b m old_nZ new_nZ old old_n r new_n &&
                          listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ) &&
                          listNN_eqb us [(old, old_n)] &&
                          listCopy_eqb cs [MemCopy.mkCopy old r old_n]) = true
                      · rw [ite_eq_left hcond] at H
                        simp only [check_result.CheckOk.injEq] at H
                        obtain ⟨hm, hevs⟩ := H
                        rw [hm.symm]
                        have hf : mremap_fresh_b m old_nZ new_nZ old old_n r new_n = true := by
                          have h1 := hcond
                          simp only [Bool.and_eq_true] at h1
                          exact h1.1.1.1.2
                        have hg : region_free (vm_reserved (m_vmmaps m) ++
                            vm_maps (m_vmmaps m)) r new_n = true := by
                          unfold mremap_fresh_b at hf
                          dsimp only at hf
                          simp only [Bool.and_eq_true] at hf
                          exact hf.1.2
                        have hceil : ((r.toNat : Int) + new_nZ ≤ alloc_top (m_vmmaps m)) := by
                          unfold mremap_fresh_b at hf
                          dsimp only at hf
                          simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
                          exact hf.1.1.2
                        rw [vmm_mremap_next]
                        exact na_inv_mremap (vm_maps (m_vmmaps m))
                          (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m)))
                          old old_n r new_n Hwf hhas hal hnv hfree Hna
                      · rw [ite_eq_right hcond] at H
                        exact nomatch H
                all_goals (exact nomatch H)



/-- `mmap`'s preservation.  Its walk is the widest of the five: it grants
    (rw and PROT_NONE), replaces on `MAP_FIXED`, destroys under `MAP_FIXED`
    failure, and spans.  The leaves are `na_inv_cons_maps` for a grant that
    adds only to `vm_maps` (the rw arms), `na_inv_cons_both` for one that
    joins both lists (the PROT_NONE arms), `na_inv_cut_both` for a destroyed
    range, `na_inv_cut_na` for a replacement that cuts the protected list,
    and `na_inv_add_owned` for the contained PROT_NONE `MAP_FIXED`, whose
    every byte `map_contains` already says is owned. -/

theorem check_mmap_preserves_na (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mmap addr len prot flags fd off eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
  unfold check_mmap at H
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hna
    · rw [ite_eq_right hpl] at H
      exact nomatch H
  · rw [ite_eq_right hoff] at H
    by_cases hanon : (!(mmap_anon_b flags)) = true
    · rw [ite_eq_left hanon] at H
      exact nomatch H
    · rw [ite_eq_right hanon] at H
      by_cases hzlen : w_is0 len = true
      · rw [ite_eq_left hzlen] at H
        by_cases hpa : mmap_plain_anon_b flags = true
        · rw [ite_eq_left hpa] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hna
        · rw [ite_eq_right hpa] at H
          exact nomatch H
      · rw [ite_eq_right hzlen] at H
        -- every remaining arm needs a POSITIVE page-rounded length
        have hlen0 : 0 < page_round_up_Z (len.toNat : Int) := by
          apply page_round_up_pos
          have hw : w_is0 len = false := by
            cases hv : w_is0 len with
            | false => rfl
            | true => exact absurd hv hzlen
          have h := w_is0_false len hw
          simp only [bv_unsigned_def] at h
          omega
        by_cases hmod : mmap_modeled_b prot flags off = true
        · -- THE HINT-PLACED RW GRANT: the placement gate is the six
          -- conjuncts `choose` uses, so the soundness walk's own
          -- extraction applies
          rw [ite_eq_left hmod] at H
          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
          cases ws <;> cases us <;> cases cs <;> cases copyins <;> try dsimp only at H
          · by_cases herr : errno_ret_in mmap_errnos r = true
            · rw [ite_eq_left herr] at H
              cases zs with
              | nil =>
                simp only [check_result.CheckOk.injEq] at H
                obtain ⟨hm, hevs⟩ := H
                rw [hm.symm]
                exact Hna
              | cons z zs => exact nomatch H
            · rw [ite_eq_right herr] at H
              generalize hnZ : page_round_up_Z (len.toNat : Int) = nZ at H
              generalize hn : BitVec.ofInt 64 nZ = n at H
              by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                  decide (0 < (r.toNat : Int)) &&
                  decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
                  region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
                  mmap_noreserve_backed_ok flags m nZ &&
                  listNN_eqb zs [(r, n)]) = true
              · rw [ite_eq_left hguard] at H
                obtain ⟨h1, hzs⟩ := (Bool.and_eq_true ..).mp hguard
                obtain ⟨h2, hbak⟩ := (Bool.and_eq_true ..).mp h1
                obtain ⟨h3, hreg⟩ := (Bool.and_eq_true ..).mp h2
                obtain ⟨h4, hle⟩ := (Bool.and_eq_true ..).mp h3
                obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp h4
                simp only [decide_eq_true_eq] at hA hB hle
                have hnzlt : nZ < two_pow_64 := by
                  have h2 := alloc_top_lt (m_vmmaps m)
                  omega
                have hnval : (n.toNat : Int) = nZ := by
                  rw [← hn]
                  exact u64 nZ ⟨by omega, hnzlt⟩
                have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                simp only [check_result.CheckOk.injEq] at H
                obtain ⟨hm, hevs⟩ := H
                rw [hm.symm]
                rw [vmm_mmap_backing, vmm_vmmaps]
                exact na_inv_cons_maps (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (r, n) Hna
              · rw [ite_eq_right hguard] at H
                exact nomatch H
          all_goals exact nomatch H
        · rw [ite_eq_right hmod] at H
          by_cases hnoacc : mmap_noaccess_b prot flags off = true
          · -- THE PROT_NONE RESERVATION: the same gate, and the request
            -- also joins `vm_noaccess`, which `vm_wf` does not read
            rw [ite_eq_left hnoacc] at H
            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
            cases ws <;> cases zs <;> cases cs <;> cases copyins <;> try dsimp only at H
            · by_cases herr : errno_ret_in mmap_errnos r = true
              · rw [ite_eq_left herr] at H
                cases us with
                | nil =>
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm]
                  exact Hna
                | cons u us => exact nomatch H
              · rw [ite_eq_right herr] at H
                generalize hnZ : page_round_up_Z (len.toNat : Int) = nZ at H
                generalize hn : BitVec.ofInt 64 nZ = n at H
                by_cases hguard : (decide ((r.toNat : Int) % page_size = 0) &&
                    decide (0 < (r.toNat : Int)) &&
                    decide ((r.toNat : Int) + nZ ≤ alloc_top (m_vmmaps m)) &&
                    region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) r n &&
                    listNN_eqb us [(r, n)]) = true
                · rw [ite_eq_left hguard] at H
                  obtain ⟨h1, hus⟩ := (Bool.and_eq_true ..).mp hguard
                  obtain ⟨h2, hreg⟩ := (Bool.and_eq_true ..).mp h1
                  obtain ⟨h3, hle⟩ := (Bool.and_eq_true ..).mp h2
                  obtain ⟨hA, hB⟩ := (Bool.and_eq_true ..).mp h3
                  simp only [decide_eq_true_eq] at hA hB hle
                  have hnzlt : nZ < two_pow_64 := by
                    have h2 := alloc_top_lt (m_vmmaps m)
                    omega
                  have hnval : (n.toNat : Int) = nZ := by
                    rw [← hn]
                    exact u64 nZ ⟨by omega, hnzlt⟩
                  have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm]
                  rw [vmm_mmap_backing, vmm_vmmaps]
                  exact na_inv_cons_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) r n hA (by show (n.toNat : Int) % page_size = 0; rw [hnval, ← hnZ]; exact pu_aligned _) (by show 0 < (n.toNat : Int); rw [hnval, ← hnZ]; exact hlen0) (by have htop := alloc_top_lt (m_vmmaps m); show (r.toNat : Int) + (n.toNat : Int) ≤ two_pow_64; rw [hnval]; omega) Hna
                · rw [ite_eq_right hguard] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hnoacc] at H
            by_cases hfx : mmap_fixed_noaccess_b prot flags off = true
            · -- MAP_FIXED, PROT_NONE
              rw [ite_eq_left hfx] at H
              dsimp only at H
              by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
              · rw [ite_eq_left hovf] at H
                rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                exact Hna
              · rw [ite_eq_right hovf] at H
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H
                  exact nomatch H
                · rw [ite_eq_right hceil] at H
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H
                    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                    exact Hna
                  · rw [ite_eq_right halign] at H
                    by_cases hpos : ¬ (0 < (addr.toNat : Int))
                    · rw [ite_eq_left hpos] at H
                      exact nomatch H
                    · rw [ite_eq_right hpos] at H
                      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
                      have hnzlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by
                        have h := (bv_unsigned_range_u64 addr).1
                        omega
                      have hnval : (n.toNat : Int) = page_round_up_Z (len.toNat : Int) := by
                        rw [← hn]
                        exact u64 _ ⟨by omega, hnzlt⟩
                      have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                      have hhi : (addr.toNat : Int) + (n.toNat : Int) < two_pow_64 := by
                        rw [hnval]; omega
                      by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                          map_contains (m_vmmaps m).vm_maps addr n) = true
                      · -- the request is INSIDE one live mapping
                        rw [ite_eq_left hcont] at H
                        obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                        cases ws <;> cases zs <;> cases cs <;> cases copyins <;> try dsimp only at H
                        · by_cases herr : errno_ret_in mmap_errnos r = true
                          · rw [ite_eq_left herr] at H
                            cases us with
                            | nil =>
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, hevs⟩ := H
                              rw [hm.symm]
                              exact Hna
                            | cons u us =>
                              by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                              · rw [ite_eq_left hdel] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_destroyed]
                                exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                              · rw [ite_eq_right hdel] at H
                                exact nomatch H
                          · rw [ite_eq_right herr] at H
                            by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                            · rw [ite_eq_left hsuc] at H
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, hevs⟩ := H
                              rw [hm.symm]
                              rw [vmm_mmap_replacement, vmm_vmmaps]
                              unfold na_inv
                              obtain ⟨-, hcont2⟩ := (Bool.and_eq_true ..).mp hcont
                              refine na_inv_add_owned _ _ (bv_unsigned (vm_brk (m_vmmaps m))) addr n (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _) (by show 0 < (n.toNat : Int); rw [hnval]; omega) (by show (addr.toNat : Int) + (n.toNat : Int) ≤ two_pow_64; omega) ?_ ?_
                              · intro x hx
                                exact map_contains_owned _ _ _ x hcont2 hx
                              · exact na_inv_cut_na _ _ (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                            · rw [ite_eq_right hsuc] at H
                              exact nomatch H
                        all_goals exact nomatch H
                      · rw [ite_eq_right hcont] at H
                        by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                            (m_vmmaps m).vm_maps) addr n = true
                        · -- the request is CLEAR of both ledgers: a fresh grant
                          rw [ite_eq_left hfresh] at H
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                            try dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases us with
                              | nil =>
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                exact Hna
                              | cons u us => exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_backing, vmm_vmmaps]
                                exact na_inv_cons_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) addr n (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _) (by show 0 < (n.toNat : Int); rw [hnval]; omega) (by show (addr.toNat : Int) + (n.toNat : Int) ≤ two_pow_64; omega) Hna
                              · rw [ite_eq_right hsuc] at H
                                exact nomatch H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hfresh] at H
                          by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                          · -- the request meets live mappings without being
                            -- inside one: the SPANNING replacement
                            rw [ite_eq_left hspan] at H
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                              try dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil =>
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  exact Hna
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                                  · rw [ite_eq_right hdel] at H
                                    exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_replacement, vmm_vmmaps]
                                  unfold na_inv
                                  refine na_inv_cons_both _ _ (bv_unsigned (vm_brk (m_vmmaps m))) addr n ?_ ?_ ?_ ?_ ?_
                                  · exact (aligned_of_not_negb_beq _ halign)
                                  · show (n.toNat : Int) % page_size = 0
                                    rw [hnval]
                                    exact pu_aligned _
                                  · show 0 < (n.toNat : Int)
                                    rw [hnval]
                                    omega
                                  · show (addr.toNat : Int) + (n.toNat : Int) ≤ two_pow_64
                                    omega
                                  · exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hspan] at H
                            exact nomatch H
            · rw [ite_eq_right hfx] at H
              by_cases hfrw : mmap_fixed_rw_b prot flags off = true
              · -- MAP_FIXED, PROT_READ|PROT_WRITE
                rw [ite_eq_left hfrw] at H
                dsimp only at H
                by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                · rw [ite_eq_left hovf] at H
                  rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                  exact Hna
                · rw [ite_eq_right hovf] at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                      exact Hna
                    · rw [ite_eq_right halign] at H
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H
                        exact nomatch H
                      · rw [ite_eq_right hpos] at H
                        generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
                        have hnzlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by
                          have h := (bv_unsigned_range_u64 addr).1
                          omega
                        have hnval : (n.toNat : Int) = page_round_up_Z (len.toNat : Int) := by
                          rw [← hn]
                          exact u64 _ ⟨by omega, hnzlt⟩
                        have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                        have hhi : (addr.toNat : Int) + (n.toNat : Int) < two_pow_64 := by
                          rw [hnval]; omega
                        by_cases hcont : (region_free (m_vmmaps m).vm_reserved addr n &&
                            map_contains (m_vmmaps m).vm_maps addr n) = true
                        · rw [ite_eq_left hcont] at H
                          obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                          cases ws <;> cases cs <;> cases copyins <;> try dsimp only at H
                          · by_cases herr : errno_ret_in mmap_errnos r = true
                            · rw [ite_eq_left herr] at H
                              cases zs with
                              | cons z zs => exact nomatch H
                              | nil =>
                                cases us with
                                | nil =>
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  exact Hna
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                                  · rw [ite_eq_right hdel] at H
                                    exact nomatch H
                            · rw [ite_eq_right herr] at H
                              cases us with
                              | cons u us => exact nomatch H
                              | nil =>
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                    mmap_fixed_rw_budget_ok flags m addr n) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_replacement, vmm_vmmaps]
                                  unfold na_inv
                                  exact na_inv_cut_na _ _ (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                          all_goals exact nomatch H
                        · rw [ite_eq_right hcont] at H
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                              try dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases zs with
                                | nil =>
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  exact Hna
                                | cons z zs => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                    mmap_noreserve_backed_ok flags m
                                      (page_round_up_Z (len.toNat : Int))) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_backing, vmm_vmmaps]
                                  exact na_inv_cons_maps (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (addr, n) Hna
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfresh] at H
                            by_cases hspan : region_free (m_vmmaps m).vm_reserved addr n = true
                            · rw [ite_eq_left hspan] at H
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases cs <;> cases copyins <;> try dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | nil =>
                                    cases us with
                                    | nil =>
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      rw [hm.symm]
                                      exact Hna
                                    | cons u us =>
                                      by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                      · rw [ite_eq_left hdel] at H
                                        simp only [check_result.CheckOk.injEq] at H
                                        obtain ⟨hm, hevs⟩ := H
                                        rw [hm.symm]
                                        rw [vmm_mmap_destroyed]
                                        exact na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna
                                      · rw [ite_eq_right hdel] at H
                                        exact nomatch H
                                  | cons z zs => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  cases us with
                                  | cons u us => exact nomatch H
                                  | nil =>
                                    by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                        mmap_fixed_rw_span_budget_ok flags m addr n) = true
                                    · rw [ite_eq_left hsuc] at H
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      rw [hm.symm]
                                      rw [vmm_mmap_replacement, vmm_vmmaps]
                                      unfold na_inv
                                      exact na_inv_cons_maps _ _ (bv_unsigned (vm_brk (m_vmmaps m))) (addr, n) (na_inv_cut_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) Hfit (aligned_of_not_negb_beq _ halign) (aligned_add _ _ (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _)) Hna)
                                    · rw [ite_eq_right hsuc] at H
                                      exact nomatch H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hspan] at H
                              exact nomatch H
              · rw [ite_eq_right hfrw] at H
                by_cases hnrn : mmap_noreplace_noaccess_b prot flags off = true
                · -- MAP_FIXED_NOREPLACE, PROT_NONE: free range or -EEXIST
                  rw [ite_eq_left hnrn] at H
                  dsimp only at H
                  by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                  · rw [ite_eq_left hovf] at H
                    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                    exact Hna
                  · rw [ite_eq_right hovf] at H
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                        exact Hna
                      · rw [ite_eq_right halign] at H
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H
                          exact nomatch H
                        · rw [ite_eq_right hpos] at H
                          generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                            at H
                          have hnzlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by
                            have h := (bv_unsigned_range_u64 addr).1
                            omega
                          have hnval : (n.toNat : Int) = page_round_up_Z (len.toNat : Int) := by
                            rw [← hn]
                            exact u64 _ ⟨by omega, hnzlt⟩
                          have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                          by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                              (m_vmmaps m).vm_maps) addr n = true
                          · rw [ite_eq_left hfresh] at H
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases cs <;> cases copyins <;>
                              try dsimp only at H
                            · by_cases herr : errno_ret_in mmap_errnos r = true
                              · rw [ite_eq_left herr] at H
                                cases us with
                                | nil =>
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  exact Hna
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_backing, vmm_vmmaps]
                                  exact na_inv_cons_both (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) addr n (aligned_of_not_negb_beq _ halign) (by show (n.toNat : Int) % page_size = 0; rw [hnval]; exact pu_aligned _) (by show 0 < (n.toNat : Int); rw [hnval]; omega) (by show (addr.toNat : Int) + (n.toNat : Int) ≤ two_pow_64; omega) Hna
                                · rw [ite_eq_right hsuc] at H
                                  exact nomatch H
                            all_goals exact nomatch H
                          · rw [ite_eq_right hfresh] at H
                            obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                            cases ws <;> cases zs <;> cases us <;> cases cs <;>
                              cases copyins <;> try dsimp only at H
                            · by_cases hret : (errno_ret_in mmap_errnos r ||
                                  bv_eqb r (errno_ret EEXIST)) = true
                              · rw [ite_eq_left hret] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                exact Hna
                              · rw [ite_eq_right hret] at H
                                exact nomatch H
                            all_goals exact nomatch H
                · rw [ite_eq_right hnrn] at H
                  by_cases hrnr : mmap_noreplace_rw_b prot flags off = true
                  · -- MAP_FIXED_NOREPLACE, rw: the same split
                    rw [ite_eq_left hrnr] at H
                    dsimp only at H
                    by_cases hovf : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
                    · rw [ite_eq_left hovf] at H
                      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                      exact Hna
                    · rw [ite_eq_right hovf] at H
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                          exact Hna
                        · rw [ite_eq_right halign] at H
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H
                            exact nomatch H
                          · rw [ite_eq_right hpos] at H
                            generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                              at H
                            have hnzlt : page_round_up_Z (len.toNat : Int) < two_pow_64 := by
                              have h := (bv_unsigned_range_u64 addr).1
                              omega
                            have hnval : (n.toNat : Int) = page_round_up_Z (len.toNat : Int) := by
                              rw [← hn]
                              exact u64 _ ⟨by omega, hnzlt⟩
                            have hnz : (n.toNat : Int) ≠ 0 := by rw [hnval]; omega
                            by_cases hfresh : region_free ((m_vmmaps m).vm_reserved ++
                                (m_vmmaps m).vm_maps) addr n = true
                            · rw [ite_eq_left hfresh] at H
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases us <;> cases cs <;> cases copyins <;>
                                try dsimp only at H
                              · by_cases herr : errno_ret_in mmap_errnos r = true
                                · rw [ite_eq_left herr] at H
                                  cases zs with
                                  | nil =>
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    exact Hna
                                  | cons z zs => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_noreserve_backed_ok flags m
                                        (page_round_up_Z (len.toNat : Int))) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_backing, vmm_vmmaps]
                                    exact na_inv_cons_maps (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)) (bv_unsigned (vm_brk (m_vmmaps m))) (addr, n) Hna
                                  · rw [ite_eq_right hsuc] at H
                                    exact nomatch H
                              all_goals exact nomatch H
                            · rw [ite_eq_right hfresh] at H
                              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                              cases ws <;> cases zs <;> cases us <;> cases cs <;>
                                cases copyins <;> try dsimp only at H
                              · by_cases hret : (errno_ret_in mmap_errnos r ||
                                    bv_eqb r (errno_ret EEXIST)) = true
                                · rw [ite_eq_left hret] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  exact Hna
                                · rw [ite_eq_right hret] at H
                                  exact nomatch H
                              all_goals exact nomatch H
                  · rw [ite_eq_right hrnr] at H
                    exact nomatch H

end LinuxSem.Checks.NoaccessOwned
