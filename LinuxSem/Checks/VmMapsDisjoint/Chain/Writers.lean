/-
  * LinuxSem.Checks.VmMapsDisjoint.Chain.Writers — the four
    WRITER preservations: `munmap`, `mremap`, `mmap`, `mprotect` keep the
    ledger invariant.

  WHY THIS IS SEPARATE FROM `Chain/Arms.lean`.  Every other arm of
  `checked_table` leaves `vm_maps` ALONE, so its preservation is its frame
  lemma (`m_vmmaps m' = m_vmmaps m`) followed by `exact Hwf`.  These four
  REBUILD the ledger — `map_remove`, `maps_subtract`, `mremap_maps_next`,
  `mmap_fixed_rw_span_next` and friends — so each needs the algebra of
  PART 2 (`maps_wf_cons_free`, `maps_wf_subtract`, `maps_wf_filter`,
  `maps_wf_cons_sub`, `maps_subtract_region_free`, `region_free_app_r`,
  `region_free_filter`) applied at the accepting branch of its checker.
  An earlier note called this "ordinary proof work"; these
  are those four proofs.

  THE SHAPE OF EACH PROOF is the checker's OWN soundness walk
  (`check_mprotect_sound_ok` in `Checks/Sys/Mm/Mprotect.lean` and the
  three in `Checks/Sys/Mm/Mmap.lean` / `Mremap.lean`): the same guards in
  the same order, `rw [ite_eq_left h]` / `rw [ite_eq_right h]` on the hypothesis,
  the same eff-shape dispatch (`cases ws <;> … <;> try dsimp only at H`), and
  the same `check_result.CheckOk.injEq` inversion at the accepting leaf.
  Only the LEAF changes: instead of building the spec's `Outcome`, it
  reads `m'` off the checker's own answer — which is what makes these
  proofs mechanical rather than a second modelling argument.

  `brk`'s preservation is NOT here: it is `Core.lean`'s
  `check_brk_preserves`, beside `brk_grant_wf`, and it was proved when
  PART 2 landed.

  NO proof hole, no `decide` on the invariant, and no change to
  `Core.lean`.  `mprotect` is here rather than with the frames
  because it does not leave `m_vmmaps` alone either — it rewrites
  `vm_noaccess` through `maps_subtract` — even though its `vm_maps` is
  untouched; its proof is the one writer proof that ends in
  `vm_wf_of_vm_maps`.
-/

import LinuxSem.Checks.VmMapsDisjoint.Core
import LinuxSem.Checks.VmMapsDisjoint.Tactics

set_option autoImplicit false
set_option maxRecDepth 1000000

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
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Mm.Madvise
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.VmMapsDisjoint

namespace LinuxSem.Checks.VmMapsDisjoint

open LinuxSem.Common.RocqSpelling

/-! ## The four ledger shapes, and what each does to the invariant

    `vm_wf h` is `maps_wf (vm_maps h)`, so a writer's proof only ever has
    to name the list `vm_maps` its accepting branch builds.  The four
    lemmas below are that naming, each at the level of a whole `VmMaps`
    so that the leaf of a checker walk is one application. -/

/-- The invariant reads `vm_maps` and nothing else, so a step that leaves
    that list alone preserves it.  `mprotect` is the writer this is for:
    it rebuilds `vm_noaccess` (and the mt/mz backing ledgers) and carries
    `vm_maps` over verbatim. -/
theorem vm_wf_of_vm_maps {m m' : Model}
    (h : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m))
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold vm_wf at *
  rw [h]
  exact Hwf

/-- A fresh grant at `(a, n)` — the shape every `mmap`/`mremap` growth
    arm produces — keeps the invariant, PROVIDED the range was tested
    against the very list it is prepended to (`region_free`) and the size
    names at least one byte.  `maps_wf_cons_free` is the workhorse; this
    is it at the `VmMaps` the checker's answer builds.  The protected
    ledger (`noacc`) is a parameter because it is irrelevant here: it is
    not `vm_maps`. -/
theorem vm_wf_grant (h : VmMaps) (a n : word) (noacc : List (word × word))
    (Hwf : vm_wf h) (Hn : (n.toNat : Int) ≠ 0)
    (Hfree : region_free (vm_maps h) a n = true) :
    vm_wf (VmMaps.mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) noacc
      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_wf_cons_free (vm_maps h) a n Hwf Hn Hfree

/-- The same grant where the checker tested the range against
    `vm_reserved ++ vm_maps` — the `mmap` placement gate
    (`region_free (h.vm_reserved ++ h.vm_maps) a n`).  The reservation
    half cannot make the grant overlap `vm_maps`, so
    `region_free_app_r` hands back the half the invariant needs. -/
theorem vm_wf_grant_app (h : VmMaps) (a n : word) (noacc : List (word × word))
    (Hwf : vm_wf h) (Hn : (n.toNat : Int) ≠ 0)
    (Hfree : region_free (vm_reserved h ++ vm_maps h) a n = true) :
    vm_wf (VmMaps.mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) noacc
      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  vm_wf_grant h a n noacc Hwf Hn (region_free_app_r _ _ a n Hfree)

/-- A `maps_subtract` rebuild — `munmap`'s removal and `mmap`'s destroyed
    range — can only SHRINK every entry, so it preserves the invariant
    (`maps_wf_subtract`), given the range is a well-formed interval in
    the user address space. -/
theorem vm_wf_subtract_h (h : VmMaps) (lo hi : Int) (noacc : List (word × word))
    (Hwf : vm_wf h) (Hlo : 0 ≤ lo) (Hlh : lo ≤ hi) (Hhi : hi < two_pow_64) :
    vm_wf (VmMaps.mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) lo hi) noacc
      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_wf_subtract (vm_maps h) lo hi Hlo Hlh Hhi Hwf

/-- The SPANNING replacement shape (`mmap_fixed_rw_span_next`,
    `mmap_fixed_noaccess_span_next`): the request is consed onto the
    ledger AFTER the same range has been subtracted out of it.  The
    subtraction is what makes the cons safe — every remaining entry is
    byte-disjoint from the request (`maps_subtract_region_free`), which
    is stronger than the page-granularity the invariant needs. -/
theorem vm_wf_span_h (h : VmMaps) (a n : word) (noacc : List (word × word))
    (Hwf : vm_wf h) (Hn : (n.toNat : Int) ≠ 0)
    (Hhi : (a.toNat : Int) + (n.toNat : Int) < two_pow_64) :
    vm_wf (VmMaps.mkVmMapsFull (vm_reserved h)
      ((a, n) :: maps_subtract (vm_maps h) (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))
      noacc (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_wf_cons_free _ a n
    (maps_wf_subtract (vm_maps h) _ _ (bv_unsigned_range_u64 a).1
      (by have h := (bv_unsigned_range_u64 n).1; omega) Hhi Hwf)
    Hn (maps_subtract_region_free (vm_maps h) a n Hhi)

/-! ## `mprotect` — the writer whose `vm_maps` is untouched -/

/-- `mprotect` rebuilds `vm_noaccess` and leaves `vm_maps` verbatim. -/
theorem vm_maps_mprotect_next (m : Model) (addr n : word) :
    vm_maps (m_vmmaps (mprotect_model_next m addr n)) = vm_maps (m_vmmaps m) := by
  rw [vmm_mprotect_next]

theorem check_mprotect_preserves (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mprotect addr len prot eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold check_mprotect at H
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hwf
  · rw [ite_eq_right hgrows] at H
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hwf
    · rw [ite_eq_right halign] at H
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hwf
      · rw [ite_eq_right hlen] at H
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hwf
        · rw [ite_eq_right hbig] at H
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
                    exact Hwf
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
                    apply vm_wf_of_vm_maps (Hwf := Hwf)
                    exact vm_maps_mprotect_next m addr _
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
                    exact Hwf
                  · exact absurd H (by rw [ite_eq_right hz]; simp)
                all_goals (exact nomatch H)
              · rw [ite_eq_right hrw] at H
                exact nomatch H

/-! ## `munmap` — the writer that DROPS a mapping -/

theorem check_munmap_preserves (addr len : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold check_munmap at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hwf
  · rw [ite_eq_right hi] at H
    dsimp only at H
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hwf
    · rw [ite_eq_right hbig] at H
      generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
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
            exact maps_wf_filter (fun q => !(q.1 == addr)) (vm_maps (m_vmmaps m)) Hwf
          · exact absurd H (by rw [ite_eq_right hc]; simp)
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hwf
        · rw [ite_eq_right hfree] at H
          exact nomatch H

/-! ## `mremap` — move, shrink, in-place grow -/

/-- The two roundings a `page_align_is0_b` gate rejects leave: the size is
    nonzero, and its page-rounded value is a word. -/
theorem page_align_is0_false_parts (w : word) (H : ¬ page_align_is0_b w = true) :
    w_is0 w = false ∧ page_round_up_Z (w.toNat : Int) < two_pow_64 := by
  have hf : page_align_is0_b w = false := by
    cases hv : page_align_is0_b w with
    | false => rfl
    | true => exact absurd hv H
  unfold page_align_is0_b at hf
  rw [Bool.or_eq_false_iff] at hf
  obtain ⟨h1, h2⟩ := hf
  refine ⟨h1, ?_⟩
  have hp : ¬ two_pow_64 ≤ page_round_up_Z (w.toNat : Int) := by
    simpa using h2
  omega

theorem check_mremap_preserves (old old_size new_size flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mremap old old_size new_size flags eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold check_mremap at H
  dsimp only at H
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hshape] at H
    exact nomatch H
  · rw [ite_eq_right hshape] at H
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hwf
    · rw [ite_eq_right halign] at H
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hwf
      · rw [ite_eq_right hnew] at H
        by_cases hold : page_align_is0_b old_size = true
        · rw [ite_eq_left hold] at H
          exact nomatch H
        · rw [ite_eq_right hold] at H
          -- the two roundings, as the soundness walk names them
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
            by_cases heq : (old_nZ == new_nZ) = true
            · rw [ite_eq_left heq] at H
              rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
              exact Hwf
            · rw [ite_eq_right heq] at H
              obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
              cases ws <;> cases copyins <;> try dsimp only at H
              · by_cases herr : errno_ret_in mremap_errnos r = true
                · rw [ite_eq_left herr] at H
                  cases zs <;> cases us <;> cases cs <;> try dsimp only at H
                  · simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    rw [hm.symm]
                    exact Hwf
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
                        -- THE SHRINK: the source entry is replaced by a
                        -- shorter one at the same base (`maps_wf_cons_sub`)
                        have hbb : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                            mremap_backing_uniform_b m old old_n) = true := by
                          cases hb : (mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                              mremap_backing_uniform_b m old old_n)
                          · rw [hb] at hsrc
                            simp at hsrc
                          · rfl
                        have hsrcb : mremap_source_b (m_vmmaps m) old old_n old_nZ = true :=
                          (Bool.and_eq_true ..).mp hbb |>.1
                        unfold mremap_source_b at hsrcb
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsrcb
                        have hhas : map_has (vm_maps (m_vmmaps m)) old old_n = true := hsrcb.1.2
                        have Hin : (old, old_n) ∈ vm_maps (m_vmmaps m) :=
                          map_has_In _ old old_n hhas
                        have hnz : bv_unsigned new_n ≠ 0 := by
                          rw [hnewv]
                          omega
                        have hle : bv_unsigned new_n ≤ bv_unsigned old_n := by
                          rw [hnewv, holdv]
                          omega
                        rw [vmm_mremap_next]
                        exact maps_wf_cons_sub (vm_maps (m_vmmaps m)) old old_n new_n
                          Hwf hnz Hin hle
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
                          -- THE IN-PLACE GROW: the source entry reappears
                          -- LONGER at the same base, and the gate holds the
                          -- whole grown range free of everything else
                          have hg : region_free (vm_reserved (m_vmmaps m) ++
                              map_remove (vm_maps (m_vmmaps m)) old) old new_n = true := by
                            unfold mremap_inplace_grow_b at hgrow
                            dsimp only at hgrow
                            simp only [Bool.and_eq_true] at hgrow
                            exact hgrow.1.2
                          have hnz : bv_unsigned new_n ≠ 0 := by
                            rw [hnewv]
                            omega
                          rw [vmm_mremap_next]
                          exact maps_wf_cons_free (map_remove (vm_maps (m_vmmaps m)) old)
                            old new_n (maps_wf_filter _ _ Hwf) hnz
                            (region_free_app_r _ _ _ _ hg)
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
                      -- THE MOVE: the destination is a fresh page-aligned
                      -- grant, the source entry is dropped
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
                      have hnz : bv_unsigned new_n ≠ 0 := by
                        rw [hnewv]
                        omega
                      rw [vmm_mremap_next]
                      exact maps_wf_cons_free (map_remove (vm_maps (m_vmmaps m)) old)
                        r new_n (maps_wf_filter _ _ Hwf) hnz
                        (region_free_filter _ _ _ _ (region_free_app_r _ _ _ _ hg))
                    · rw [ite_eq_right hcond] at H
                      exact nomatch H
              all_goals (exact nomatch H)

/-! ## `mmap` — the writer with the widest surface: grants, destroyed
    ranges, contained replacements and spanning grants

    Seven arms, each with its own argument gate and its own effect shape;
    the walk below is `check_mmap_sound_ok`'s, branch for branch, with the
    spec-building leaves replaced by the four `maps_wf` facts above.  The
    four shapes the accepting branches can build are:

    * the untouched ledger (`with_mmap_replacement`, `-EEXIST`, the
      errno-only answers) — `exact Hwf`;
    * a FRESH grant, `(r, n)` consed on, tested by the placement gate —
      `vm_wf_grant_app`;
    * a DESTROYED range, `maps_subtract` on both ledgers —
      `vm_wf_subtract_h`;
    * a SPANNING grant, `(addr, n)` consed onto the same range subtracted
      out — `vm_wf_span_h` (the subtraction is what makes the cons safe).
-/

theorem check_mmap_preserves (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mmap addr len prot flags fd off eff m = .CheckOk m' evs)
    (Hwf : vm_wf (m_vmmaps m)) : vm_wf (m_vmmaps m') := by
  unfold check_mmap at H
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hwf
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
          exact Hwf
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
                exact Hwf
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
                exact vm_wf_grant_app (m_vmmaps m) r n _ Hwf hnz hreg
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
                  exact Hwf
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
                  exact vm_wf_grant_app (m_vmmaps m) r n _ Hwf hnz hreg
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
                exact Hwf
              · rw [ite_eq_right hovf] at H
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H
                  exact nomatch H
                · rw [ite_eq_right hceil] at H
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H
                    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                    exact Hwf
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
                              exact Hwf
                            | cons u us =>
                              by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                              · rw [ite_eq_left hdel] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_destroyed]
                                exact vm_wf_subtract_h (m_vmmaps m) (addr.toNat : Int)
                                  ((addr.toNat : Int) + (n.toNat : Int)) _ Hwf
                                  (by omega) (by omega) hhi
                              · rw [ite_eq_right hdel] at H
                                exact nomatch H
                          · rw [ite_eq_right herr] at H
                            by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                            · rw [ite_eq_left hsuc] at H
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, hevs⟩ := H
                              rw [hm.symm]
                              rw [vmm_mmap_replacement, vmm_vmmaps]
                              exact Hwf
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
                                exact Hwf
                              | cons u us => exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_backing, vmm_vmmaps]
                                exact vm_wf_grant_app (m_vmmaps m) addr n _ Hwf hnz hfresh
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
                                  exact Hwf
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact vm_wf_subtract_h (m_vmmaps m) (addr.toNat : Int)
                                      ((addr.toNat : Int) + (n.toNat : Int)) _ Hwf
                                      (by omega) (by omega) hhi
                                  · rw [ite_eq_right hdel] at H
                                    exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_replacement, vmm_vmmaps]
                                  exact vm_wf_span_h (m_vmmaps m) addr n _ Hwf hnz hhi
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
                  exact Hwf
                · rw [ite_eq_right hovf] at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                      exact Hwf
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
                                  exact Hwf
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact vm_wf_subtract_h (m_vmmaps m) (addr.toNat : Int)
                                      ((addr.toNat : Int) + (n.toNat : Int)) _ Hwf
                                      (by omega) (by omega) hhi
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
                                  apply vm_wf_of_vm_maps (Hwf := Hwf)
                                  exact vmm_fixed_rw_next (m_vmmaps m) addr n
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
                                  exact Hwf
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
                                  exact vm_wf_grant_app (m_vmmaps m) addr n _ Hwf hnz hfresh
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
                                      exact Hwf
                                    | cons u us =>
                                      by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                      · rw [ite_eq_left hdel] at H
                                        simp only [check_result.CheckOk.injEq] at H
                                        obtain ⟨hm, hevs⟩ := H
                                        rw [hm.symm]
                                        rw [vmm_mmap_destroyed]
                                        exact vm_wf_subtract_h (m_vmmaps m) (addr.toNat : Int)
                                          ((addr.toNat : Int) + (n.toNat : Int)) _ Hwf
                                          (by omega) (by omega) hhi
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
                                      exact vm_wf_span_h (m_vmmaps m) addr n _ Hwf hnz hhi
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
                    exact Hwf
                  · rw [ite_eq_right hovf] at H
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                        exact Hwf
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
                                  exact Hwf
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_backing, vmm_vmmaps]
                                  exact vm_wf_grant_app (m_vmmaps m) addr n _ Hwf hnz hfresh
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
                                exact Hwf
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
                      exact Hwf
                    · rw [ite_eq_right hovf] at H
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                          exact Hwf
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
                                    exact Hwf
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
                                    exact vm_wf_grant_app (m_vmmaps m) addr n _ Hwf hnz hfresh
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
                                  exact Hwf
                                · rw [ite_eq_right hret] at H
                                  exact nomatch H
                              all_goals exact nomatch H
                  · rw [ite_eq_right hrnr] at H
                    exact nomatch H

end LinuxSem.Checks.VmMapsDisjoint
