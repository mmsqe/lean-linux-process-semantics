/-
  * LinuxSem.Checks.MmStepFrame — what a successful mmap, mremap or brk
    leaves alone.

    Not part of the trusted specification: three facts about every `ok`
    outcome `Syscall.syscall_spec` admits for mmap (222), mremap (216) and
    brk (214), stated for a consumer that steps a run across one of them.

    - `mm_ok_keeps_halted`: the call does not change `m_halted`.  Every
      post-model these arms build is `with_vmmaps`, `with_vm_backing` or
      one of the wrappers over them (`with_brk_next`, `with_mmap_backing`,
      `with_mmap_replacement`, `with_mmap_destroyed`,
      `mremap_model_next`), and none of them rebuilds `ProcState`.
    - `mm_ok_no_accesses`: the effect names no user-memory access
      (`syscall_effect_accesses eff = []`).  No arm records a copy-in or a
      byte write: mmap is anonymous-only, the bytes a grow exposes are
      `eff_zeros`, and a move is an `eff_copies` entry — neither of which
      `syscall_effect_accesses` counts.
    - `mm_ok_step`: the two together, for a consumer of the run rule
      `Run.sstep_syscall`: from a live model the post-model is live and not
      killed, the effect names no access, and materializing no access is
      the identity on the post-model.

    Each arm is walked through its checker (`check_syscall_complete_ok`
    and the `Sys/DispatchCompute` rewrite for its number), which is a
    function of the effect, so the walk is a case split and nothing else:
    `brk`'s is three `cases` and one guard, `mremap`'s and `mmap`'s peel
    their gate chain with `by_cases` + `ite_eq_left`/`ite_eq_right` and
    reach the same five wrappers at the leaves.  `mmap`'s is written out
    gate by gate rather than by a `split at` loop because `split` runs out
    of `simp` steps on `check_mmap`'s `MAP_FIXED` chains (measured: the
    loop either stalls with the guard chain unsplit or aborts inside
    `simp`), and the same loop is what a walker would be doing anyway.

    The Rocq original proved this over `Specs.syscall_spec` with an Ltac
    walker; here the walk is over the checker, which is the same surface
    (`ExecutableSpecs.check_syscall_ok_iff`), and the two forms are the
    same statement.
-/

import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Sys.DispatchCompute

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.Sys.DispatchCompute

namespace LinuxSem.Checks.MmStepFrame

open LinuxSem.Common.RocqSpelling

/- =========================================================================
   The post-model wrappers keep `m_halted`
   ========================================================================= -/

/-- `forget_vm_ranges` forgets lazy/materialized pages only; induction over
    the list, since the recursion is inside the model argument. -/
theorem m_halted_forget_vm_ranges : ∀ (rs : List (word × word)) (m : Model),
    m_halted (forget_vm_ranges rs m) = m_halted m
  | [], _ => rfl
  | (_, _) :: rest, m => by
      simp only [forget_vm_ranges]
      rw [m_halted_forget_vm_ranges rest]
      rfl

/-- The `brk` post-state: a `with_vmmaps` nest behind `forget_vm_ranges`. -/
theorem m_halted_with_brk_next (m : Model) (req r : word) :
    m_halted (with_brk_next m req r) = m_halted m := by
  unfold with_brk_next
  rw [m_halted_forget_vm_ranges]
  rfl

/-- `MAP_NORESERVE` only adds a lazy range; both branches keep `ProcState`. -/
theorem m_halted_with_mmap_backing (flags a n : word) (m : Model) :
    m_halted (with_mmap_backing flags a n m) = m_halted m := by
  unfold with_mmap_backing
  split <;> rfl

theorem m_halted_with_mmap_replacement (flags a n : word) (m : Model) :
    m_halted (with_mmap_replacement flags a n m) = m_halted m := by
  unfold with_mmap_replacement
  rw [m_halted_with_mmap_backing]
  rfl

theorem m_halted_with_mmap_destroyed (a n : word) (h' : VmMaps) (m : Model) :
    m_halted (with_mmap_destroyed a n h' m) = m_halted m := rfl

theorem m_halted_mremap_model_next (m : Model) (old old_n dst new_n : word) :
    m_halted (mremap_model_next m old old_n dst new_n) = m_halted m := rfl

/-- Materializing no access is the identity on any model.  The upstream
    proof is a destruct of the model record and `reflexivity`, which is
    the same reduction here. -/
theorem materialize_model_accesses_none (m : Model) :
    materialize_model_accesses m [] = some m := by
  obtain ⟨fd, vm, io, fs, proc, lim, tm⟩ := m
  rfl

/-- The accepting leaf of every walk below: the checker's own post-model,
    whatever wrapper it is, keeps `ProcState`, and its effect has neither
    a write nor a copy-in. -/
macro "mm_leaf" : tactic =>
  `(tactic| refine ⟨?_, ?_⟩ <;> first
      | rfl
      | (rw [m_halted_with_brk_next]; rfl)
      | (rw [m_halted_with_mmap_backing]; rfl)
      | (rw [m_halted_with_mmap_replacement]; rfl)
      | (rw [m_halted_with_mmap_destroyed]; rfl)
      | (rw [m_halted_mremap_model_next]; rfl))

/-- A `check_ret_only` acceptance hands back the model it was given and an
    effect with no write and no copy-in (`check_ret_only_ok_iff`). -/
theorem check_ret_only_frame (eff : SyscallEffect) (r : word) (m1 : Model)
    (evs1 : List event) (m' : Model) (evs : List event)
    (H : check_ret_only eff r m1 evs1 = .CheckOk m' evs) :
    m_halted m' = m_halted m1 ∧ syscall_effect_accesses eff = [] := by
  obtain ⟨heff, hm, -⟩ := (check_ret_only_ok_iff eff r m1 evs1 m' evs).mp H
  subst heff
  subst hm
  exact ⟨rfl, rfl⟩

/-- Close a `check_ret_only` leaf: the wrapper hands back the model it was
    given, and the effect it accepted names no access. -/
macro "mm_ret_only" h:ident : tactic =>
  `(tactic| (obtain ⟨hm, hacc⟩ := check_ret_only_frame _ _ _ _ _ _ $h:ident
             rw [hm]
             exact ⟨rfl, hacc⟩))

/- =========================================================================
   brk (214)
   ========================================================================= -/

theorem check_brk_mm_frame (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_brk req eff m = .CheckOk m' evs) :
    m_halted m' = m_halted m ∧ syscall_effect_accesses eff = [] := by
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  unfold check_brk at H
  cases ws with
  | cons _ _ => exact absurd H (by simp)
  | nil =>
    cases cs with
    | cons _ _ => exact absurd H (by simp)
    | nil =>
      cases ci with
      | cons _ _ => exact absurd H (by simp)
      | nil =>
        by_cases hc : (brk_r_ok m req ret &&
            listNN_eqb zs (brk_zeros req ret (m_vmmaps m).vm_brk) &&
            listNN_eqb us (brk_unmaps ret (m_vmmaps m).vm_brk)) = true
        · simp only [hc, ite_true] at H
          obtain ⟨rfl, rfl⟩ := H
          exact ⟨by rw [m_halted_with_brk_next], by rfl⟩
        · simp only [hc] at H
          exact absurd H (by simp)

theorem check_mremap_mm_frame (old old_size new_size flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_mremap old old_size new_size flags eff m = .CheckOk m' evs) :
    m_halted m' = m_halted m ∧ syscall_effect_accesses eff = [] := by
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  unfold check_mremap at H
  dsimp only at H
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hshape] at H
    exact nomatch H
  · rw [ite_eq_right hshape] at H
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      mm_ret_only H
    · rw [ite_eq_right halign] at H
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        mm_ret_only H
      · rw [ite_eq_right hnew] at H
        by_cases htask : (TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)
        · rw [ite_eq_left htask] at H
          mm_ret_only H
        · rw [ite_eq_right htask] at H
          by_cases hold : page_align_is0_b old_size = true
          · rw [ite_eq_left hold] at H
            exact nomatch H
          · rw [ite_eq_right hold] at H
            generalize hOldN : page_round_up_Z (old_size.toNat : Int) = old_nZ at H
            generalize hNewN : page_round_up_Z (new_size.toNat : Int) = new_nZ at H
            generalize hOldW : BitVec.ofInt 64 old_nZ = old_n at H
            generalize hNewW : BitVec.ofInt 64 new_nZ = new_n at H
            by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
                mremap_backing_uniform_b m old old_n)) = true
            · rw [ite_eq_left hsrc] at H
              exact nomatch H
            · rw [ite_eq_right hsrc] at H
              by_cases heq : (old_nZ == new_nZ) = true
              · rw [ite_eq_left heq] at H
                mm_ret_only H
              · rw [ite_eq_right heq] at H
                cases ws with
                | cons _ _ => exact absurd H (by simp)
                | nil =>
                  cases ci with
                  | cons _ _ => exact absurd H (by simp)
                  | nil =>
                    dsimp only at H
                    by_cases herr : errno_ret_in mremap_errnos ret = true
                    · rw [ite_eq_left herr] at H
                      cases zs with
                      | cons _ _ => exact absurd H (by simp)
                      | nil =>
                        cases us with
                        | cons _ _ => exact absurd H (by simp)
                        | nil =>
                          cases cs with
                          | cons _ _ => exact absurd H (by simp)
                          | nil =>
                            simp only [check_result.CheckOk.injEq] at H
                            obtain ⟨hm, -⟩ := H
                            rw [hm.symm]
                            mm_leaf
                    · rw [ite_eq_right herr] at H
                      by_cases hret : bv_eqb ret old = true
                      · rw [ite_eq_left hret] at H
                        by_cases hlt : new_nZ < old_nZ
                        · rw [ite_eq_left hlt] at H
                          by_cases hshrink : (listNN_eqb zs [] &&
                              listNN_eqb us
                                [(old + new_n, BitVec.ofInt 64 (old_nZ - new_nZ))] &&
                              listCopy_eqb cs []) = true
                          · rw [ite_eq_left hshrink] at H
                            simp only [check_result.CheckOk.injEq] at H
                            obtain ⟨hm, -⟩ := H
                            rw [hm.symm]
                            mm_leaf
                          · rw [ite_eq_right hshrink] at H
                            exact nomatch H
                        · rw [ite_eq_right hlt] at H
                          by_cases hgrow :
                              mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
                          · rw [ite_eq_left hgrow] at H
                            by_cases hcond :
                                (listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ) &&
                                  listNN_eqb us [] && listCopy_eqb cs []) = true
                            · rw [ite_eq_left hcond] at H
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, -⟩ := H
                              rw [hm.symm]
                              mm_leaf
                            · rw [ite_eq_right hcond] at H
                              exact nomatch H
                          · rw [ite_eq_right hgrow] at H
                            exact nomatch H
                      · rw [ite_eq_right hret] at H
                        by_cases hcond : (decide (old_nZ < new_nZ) &&
                            mremap_fresh_b m old_nZ new_nZ old old_n ret new_n &&
                            listNN_eqb zs (mremap_tail ret old_n old_nZ new_nZ) &&
                            listNN_eqb us [(old, old_n)] &&
                            listCopy_eqb cs [MemCopy.mkCopy old ret old_n]) = true
                        · rw [ite_eq_left hcond] at H
                          simp only [check_result.CheckOk.injEq] at H
                          obtain ⟨hm, -⟩ := H
                          rw [hm.symm]
                          mm_leaf
                        · rw [ite_eq_right hcond] at H
                          exact nomatch H

/-- `mmap`'s walk.  `check_map`'s `MAP_FIXED` chains are too large for
    `split at H` (Lean's `split` runs out of `simp` steps on them), so the
    guard chain is peeled with `by_cases`/`ite_eq_left`, arm for arm, and
    only the leaf `match eff with` is left to `cases`. -/
theorem check_mmap_mm_frame (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mmap addr len prot flags fd off eff m = .CheckOk m' evs) :
    m_halted m' = m_halted m ∧ syscall_effect_accesses eff = [] := by
    unfold check_mmap at H
    by_cases hoff : (!(mmap_off_aligned_b off)) = true
    · rw [ite_eq_left hoff] at H
      by_cases hpl : mmap_pglen_ok_b len = true
      · rw [ite_eq_left hpl] at H
        mm_ret_only H
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
            mm_ret_only H
          · rw [ite_eq_right hpa] at H
            exact nomatch H
        · rw [ite_eq_right hzlen] at H
          by_cases hmod : mmap_modeled_b prot flags off = true
          · -- THE HINT-PLACED RW GRANT: an injected errno with no ledger,
            -- or the grant at an address the six-conjunct placement gate
            -- accepts, whose post-model is `with_mmap_backing`
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
                  mm_leaf
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
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm]
                  mm_leaf
                · rw [ite_eq_right hguard] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hmod] at H
            by_cases hnoacc : mmap_noaccess_b prot flags off = true
            · -- THE PROT_NONE RESERVATION: the same shape, and the request
              -- also joins `vm_noaccess`
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
                    mm_leaf
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
                    simp only [check_result.CheckOk.injEq] at H
                    obtain ⟨hm, hevs⟩ := H
                    rw [hm.symm]
                    mm_leaf
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
                  mm_ret_only H
                · rw [ite_eq_right hovf] at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      mm_ret_only H
                    · rw [ite_eq_right halign] at H
                      by_cases hpos : ¬ (0 < (addr.toNat : Int))
                      · rw [ite_eq_left hpos] at H
                        exact nomatch H
                      · rw [ite_eq_right hpos] at H
                        generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
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
                                mm_leaf
                              | cons u us =>
                                by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                · rw [ite_eq_left hdel] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  mm_leaf
                                · rw [ite_eq_right hdel] at H
                                  exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                mm_leaf
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
                                  mm_leaf
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  mm_leaf
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
                                    mm_leaf
                                  | cons u us =>
                                    by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                    · rw [ite_eq_left hdel] at H
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      rw [hm.symm]
                                      mm_leaf
                                    · rw [ite_eq_right hdel] at H
                                      exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    mm_leaf
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
                    mm_ret_only H
                  · rw [ite_eq_right hovf] at H
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        mm_ret_only H
                      · rw [ite_eq_right halign] at H
                        by_cases hpos : ¬ (0 < (addr.toNat : Int))
                        · rw [ite_eq_left hpos] at H
                          exact nomatch H
                        · rw [ite_eq_right hpos] at H
                          generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n at H
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
                                    mm_leaf
                                  | cons u us =>
                                    by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                    · rw [ite_eq_left hdel] at H
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      rw [hm.symm]
                                      mm_leaf
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
                                    mm_leaf
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
                                    mm_leaf
                                  | cons z zs => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                      mmap_noreserve_backed_ok flags m
                                        (page_round_up_Z (len.toNat : Int))) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    mm_leaf
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
                                        mm_leaf
                                      | cons u us =>
                                        by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                        · rw [ite_eq_left hdel] at H
                                          simp only [check_result.CheckOk.injEq] at H
                                          obtain ⟨hm, hevs⟩ := H
                                          rw [hm.symm]
                                          mm_leaf
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
                                        mm_leaf
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
                      mm_ret_only H
                    · rw [ite_eq_right hovf] at H
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          mm_ret_only H
                        · rw [ite_eq_right halign] at H
                          by_cases hpos : ¬ (0 < (addr.toNat : Int))
                          · rw [ite_eq_left hpos] at H
                            exact nomatch H
                          · rw [ite_eq_right hpos] at H
                            generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                              at H
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
                                    mm_leaf
                                  | cons u us => exact nomatch H
                                · rw [ite_eq_right herr] at H
                                  by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                  · rw [ite_eq_left hsuc] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    mm_leaf
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
                                  mm_leaf
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
                        mm_ret_only H
                      · rw [ite_eq_right hovf] at H
                        by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                            alloc_top (m_vmmaps m))
                        · rw [ite_eq_left hceil] at H
                          exact nomatch H
                        · rw [ite_eq_right hceil] at H
                          by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                          · rw [ite_eq_left halign] at H
                            mm_ret_only H
                          · rw [ite_eq_right halign] at H
                            by_cases hpos : ¬ (0 < (addr.toNat : Int))
                            · rw [ite_eq_left hpos] at H
                              exact nomatch H
                            · rw [ite_eq_right hpos] at H
                              generalize hn : BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)) = n
                                at H
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
                                      mm_leaf
                                    | cons z zs => exact nomatch H
                                  · rw [ite_eq_right herr] at H
                                    by_cases hsuc : (bv_eqb r addr && listNN_eqb zs [(addr, n)] &&
                                        mmap_noreserve_backed_ok flags m
                                          (page_round_up_Z (len.toNat : Int))) = true
                                    · rw [ite_eq_left hsuc] at H
                                      simp only [check_result.CheckOk.injEq] at H
                                      obtain ⟨hm, hevs⟩ := H
                                      rw [hm.symm]
                                      mm_leaf
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
                                    mm_leaf
                                  · rw [ite_eq_right hret] at H
                                    exact nomatch H
                                all_goals exact nomatch H
                    · rw [ite_eq_right hrnr] at H
                      exact nomatch H



/- =========================================================================
   Through the dispatcher
   ========================================================================= -/

/-- The frame, at the dispatcher.  `in_sysno` selects exactly one arm, so
    the three numbers' three checker rewrites
    (`Sys/DispatchCompute.check_syscall_{mmap,mremap,brk}`) turn the
    completeness direction of `check_syscall` into the arm's own walk. -/
theorem mm_ok_frame (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hin : bv_unsigned (in_sysno i) ∈ ([(222 : Int), 216, 214] : List Int))
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    m_halted m' = m_halted m ∧ syscall_effect_accesses eff = [] := by
  have Hck := check_syscall_complete_ok i eff m m' evs Hspec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with h | h | h
  · rw [check_syscall_mmap i eff m h] at Hck
    exact check_mmap_mm_frame _ _ _ _ _ _ _ _ _ _ Hck
  · rw [check_syscall_mremap i eff m h] at Hck
    exact check_mremap_mm_frame _ _ _ _ _ _ _ _ Hck
  · rw [check_syscall_brk i eff m h] at Hck
    exact check_brk_mm_frame _ _ _ _ _ Hck

/-- A successful `mmap`/`mremap`/`brk` never halts the process. -/
theorem mm_ok_keeps_halted (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hin : bv_unsigned (in_sysno i) ∈ ([(222 : Int), 216, 214] : List Int))
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    m_halted m' = m_halted m :=
  (mm_ok_frame i m eff m' evs Hin Hspec).1

/-- A successful `mmap`/`mremap`/`brk` names no user-memory access. -/
theorem mm_ok_no_accesses (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hin : bv_unsigned (in_sysno i) ∈ ([(222 : Int), 216, 214] : List Int))
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    syscall_effect_accesses eff = [] :=
  (mm_ok_frame i m eff m' evs Hin Hspec).2

/-- Both halves, in the shape a consumer of `Run.sstep_syscall` needs: from
    a live model, the post-model is still live, not killed, its effect
    names no access, and materializing no access is the identity on it. -/
theorem mm_ok_step (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hin : bv_unsigned (in_sysno i) ∈ ([(222 : Int), 216, 214] : List Int))
    (Hh : m_halted m = none)
    (Hspec : syscall_spec i m (.ok eff m' evs)) :
    m_halted m' = none ∧ m_killed m' = none ∧
      syscall_effect_accesses eff = [] ∧ materialize_model_accesses m' [] = some m' := by
  obtain ⟨Hhalt, Hacc⟩ := mm_ok_frame i m eff m' evs Hin Hspec
  rw [Hh] at Hhalt
  exact ⟨Hhalt, m_killed_of_m_halted_none m' Hhalt, Hacc,
    materialize_model_accesses_none m'⟩

end LinuxSem.Checks.MmStepFrame
