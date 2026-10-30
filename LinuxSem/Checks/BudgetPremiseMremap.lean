/-
  * LinuxSem.Checks.BudgetPremiseMremap — the mremap budget mark on
    invariant states.

    Not part of the trusted specification.  The mremap twin of
    `Checks.BudgetPremise.mmap_budget_refused_is_refusal`: where the mark
    `Mremap.mremap_budget_refused_b` fires, every outcome
    `Mremap.mremap_spec` admits is one of `Run.refusal_b`'s refusals — an
    errno in `Mremap.mremap_errnos`.  The marked request is a grow past
    every argument gate, so the spec's `ok` arms are three: the injected
    errno, the in-place grow and the move.  The in-place grow is excluded
    on every state (`Checks.BudgetPremise.mremap_budget_refused_refuses_inplace`).
    The move is excluded at every destination that carries no backing
    metadata (`Checks.BudgetPremise.mremap_budget_refused_refuses_move`),
    and on the states this file takes every fresh destination is such a
    one: `NoaccessOwned.sys_inv` gives the fit of the live mappings
    (`MapsFit.vm_fit_map_remove`) and `State.noaccess_pages_owned`, hence
    a fresh destination meets no protected byte
    (`Checks.BudgetPremiseInv.fresh_dst_avoids_noaccess`); and with both
    lazy ledgers (`m_vm_lazy`, `m_vm_materialized`) empty the two
    lazy-ledger identities hold by computation.

    THE WALK IS OVER THE CHECKER, not over the spec's `alt`/`bind` tree:
    `Checks.Sys.Mm.Mremap.check_mremap_complete_ok` turns the admitted
    outcome into `check_mremap … = .CheckOk`, the mark's own `if` chain is
    walked once to learn which gates it passed (`mremap_budget_refused_inv`)
    and which two charging gates it closed, and the checker's accepting
    branches are then read under those facts.  Every accepting branch
    either is `check_ret_only eff (errno_ret EINVAL) m []` (an
    `mremap_errnos` member), is the errno leaf of the effect match (the
    same), or needs `mremap_fresh_b`, which
    `mremap_budget_refused_no_fresh_sys_inv` refutes.  This is the same
    route `Checks/BudgetPremise.lean`'s `brk` and `mmap` pairs take; the
    original's `sys_destruct` + `errno_is_refusal` case bash is a tactic
    this tree does not have.
-/

import LinuxSem.Checks.BudgetPremiseInv

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.BudgetPremise
open LinuxSem.Checks.BudgetPremiseInv
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.BudgetPremiseMremap

open LinuxSem.Common.RocqSpelling

/-! ## The dispatcher at 216 -/

/-- The dispatcher at the mremap number IS `Mremap.mremap_spec`, the same
    fact `Checks.BudgetPremise.brk_dispatch` and `mmap_dispatch` state at
    their numbers.  The number is compared in `Nat` (the `in_sysno` word's
    `toNat`), which is the form the dispatcher's own `if` reads. -/
theorem mremap_dispatch (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (hE : i.in_sysno.toNat = 216) :
    Specs.syscall_spec i m o ↔ mremap_spec (in_arg i 0) (in_arg i 1)
      (in_arg i 2) (in_arg i 3) i m o := by
  rw [Specs.syscall_spec, Sys.Dispatch.dispatch, hE]
  rfl

/-! ## No destination is fresh -/

/-- Where the mark fires, on a `sys_inv` state with empty lazy ledgers,
    `Mremap.mremap_fresh_b` admits no destination at all.  The destination
    is universally quantified: the argument is the same at every one of
    them, which is exactly what
    `Mremap.mremap_move_charge_at_fresh` is for. -/
theorem mremap_budget_refused_no_fresh_sys_inv (old old_size new_size flags : word)
    (m : Model) (dst : word)
    (Hinv : sys_inv (m_vmmaps m))
    (Hlz : m_vm_lazy m = [])
    (Hmat : m_vm_materialized m = [])
    (Hmark : mremap_budget_refused_b old old_size new_size flags m = true) :
    mremap_fresh_b m
      (page_round_up_Z (old_size.toNat : Int))
      (page_round_up_Z (new_size.toNat : Int)) old
      (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = false := by
  obtain ⟨-, -, Hnew, -, -, -, -, -, -⟩ :=
    mremap_budget_refused_inv old old_size new_size flags m Hmark
  have Hown : noaccess_pages_owned (m_vmmaps m) := sys_inv_noaccess_pages_owned _ Hinv
  have Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64 :=
    vm_fit_map_remove _ old Hinv.2.1
  obtain ⟨hNN, hmod, hpos⟩ := mremap_new_n_shape new_size Hnew
  cases hf : mremap_fresh_b m
      (page_round_up_Z (old_size.toNat : Int))
      (page_round_up_Z (new_size.toNat : Int)) old
      (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))) dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) with
  | false => rfl
  | true =>
      exfalso
      -- the gate's own conjuncts, in the order `Mremap.mremap_fresh_b`
      -- states them
      have Hf0 := hf
      unfold mremap_fresh_b at Hf0
      dsimp only at Hf0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at Hf0
      obtain ⟨⟨⟨⟨⟨-, Hdalign⟩, -⟩, -⟩, Hdfree⟩, -⟩ := Hf0
      have hnoacc : region_free (m_vmmaps m).vm_noaccess dst
          (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true :=
        fresh_dst_avoids_noaccess (m_vmmaps m) dst
          (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))
          Hown hpos hmod Hdalign Hdfree
      have hlazy : maps_subtract
          (maps_subtract (m_vm_lazy m) (old.toNat : Int)
            ((old.toNat : Int) +
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
          (dst.toNat : Int) ((dst.toNat : Int) +
            (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat)
        = maps_subtract (m_vm_lazy m) (old.toNat : Int)
            ((old.toNat : Int) +
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat) := by
        rw [Hlz]
        rfl
      have hpages : List.filter (page_outside_range (dst.toNat : Int)
            ((dst.toNat : Int) +
              (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat))
          (List.filter (page_outside_range (old.toNat : Int)
            ((old.toNat : Int) +
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
            (m_vm_materialized m))
        = List.filter (page_outside_range (old.toNat : Int)
            ((old.toNat : Int) +
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))).toNat))
            (m_vm_materialized m) := by
        rw [Hmat]
        rfl
      have hfalse := mremap_budget_refused_refuses_move old old_size new_size flags
        m dst Hfit hnoacc hlazy hpages Hmark
      rw [hfalse] at hf
      exact absurd hf (by simp)

/-! ## Soundness over the whole arm -/

/-- SOUNDNESS over the whole arm, on invariant states: where the mark
    fires, every admitted outcome is a refusal.  The three `ok` arms of
    `Mremap.mremap_spec` past the mark's gates are the injected errno (a
    refusal by value), the in-place grow (excluded on every state by
    `Checks.BudgetPremise.mremap_budget_refused_refuses_inplace`) and the
    move (excluded at every destination by the lemma above). -/
theorem mremap_budget_refused_is_refusal_sys_inv (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hinv : sys_inv (m_vmmaps m))
    (Hlz : m_vm_lazy m = [])
    (Hmat : m_vm_materialized m = [])
    (hE : i.in_sysno.toNat = 216)
    (Hmark : alloc_budget_refused_b i m = true)
    (Hspec : Specs.syscall_spec i m (.ok eff m' evs)) :
    refusal_b i m eff.eff_ret = true := by
  have hmark : mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2)
      (in_arg i 3) m = true := by
    simp only [alloc_budget_refused_b, hE] at Hmark
    simpa using Hmark
  have hspec : mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      i m (.ok eff m' evs) := (mremap_dispatch i m _ hE).mp Hspec
  have hchk := LinuxSem.Checks.Sys.Mm.Mremap.check_mremap_complete_ok
    (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) eff m m' evs i hspec
  obtain ⟨Hfl, Hal, Hnew, Htask, Hold, Hsrc, Hgrow, Hip, Hmv⟩ :=
    mremap_budget_refused_inv (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
      m hmark
  -- the mark's gates, read in the checker's own spelling
  unfold LinuxSem.Checks.Sys.Mm.Mremap.check_mremap at hchk
  rw [ite_eq_right (by simp [Hfl])] at hchk
  rw [ite_eq_right (by simp [Hal])] at hchk
  rw [ite_eq_right (by simp [Hnew])] at hchk
  rw [ite_eq_right (by simpa using Htask)] at hchk
  rw [ite_eq_right (by simp [Hold])] at hchk
  dsimp only at hchk
  rw [ite_eq_right (by simp [Hsrc])] at hchk
  rw [ite_eq_right (by
    simp [beq_eq_false_iff_ne.mpr (by omega :
      page_round_up_Z ((in_arg i 1).toNat : Int)
        ≠ page_round_up_Z ((in_arg i 2).toNat : Int))])] at hchk
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  cases ws <;> cases ci <;> dsimp only at hchk
  · by_cases herrno : errno_ret_in mremap_errnos r = true
    · have hret : ret_in_errnos mremap_errnos r = true := by
        simpa only [ret_in_errnos, LinuxSem.Checks.Sys.Prelude.errno_ret_in] using herrno
      have harm : injected_arm 216 = some ⟨216, .FamAlloc, mremap_errnos⟩ := by decide
      simp only [refusal_b, hE, harm, ret_in_errnos]
      exact hret
    · rw [ite_eq_right (by simpa using herrno)] at hchk
      by_cases hret : bv_eqb r (in_arg i 0) = true
      · -- the source's own address: the in-place resolutions, both excluded
        rw [ite_eq_left hret] at hchk
        rw [ite_eq_right (by omega :
          ¬(page_round_up_Z ((in_arg i 2).toNat : Int)
            < page_round_up_Z ((in_arg i 1).toNat : Int)))] at hchk
        rw [ite_eq_right (by simpa using Hip)] at hchk
        exact absurd hchk (by simp)
      · -- a fresh destination: no destination is fresh under the mark
        rw [ite_eq_right hret] at hchk
        by_cases hcond : (decide (page_round_up_Z ((in_arg i 1).toNat : Int)
              < page_round_up_Z ((in_arg i 2).toNat : Int)) &&
            mremap_fresh_b m (page_round_up_Z ((in_arg i 1).toNat : Int))
              (page_round_up_Z ((in_arg i 2).toNat : Int)) (in_arg i 0)
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) r
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 2).toNat : Int))) &&
            listNN_eqb zs (mremap_tail r
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))
              (page_round_up_Z ((in_arg i 1).toNat : Int))
              (page_round_up_Z ((in_arg i 2).toNat : Int))) &&
            listNN_eqb us [(in_arg i 0,
              BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))] &&
            listCopy_eqb cs [MemCopy.mkCopy (in_arg i 0) r
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int)))]) = true
        · rw [ite_eq_left hcond] at hchk
          have hf : mremap_fresh_b m (page_round_up_Z ((in_arg i 1).toNat : Int))
              (page_round_up_Z ((in_arg i 2).toNat : Int)) (in_arg i 0)
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 1).toNat : Int))) r
              (BitVec.ofInt 64 (page_round_up_Z ((in_arg i 2).toNat : Int))) = true := by
            simp only [Bool.and_eq_true] at hcond
            exact hcond.1.1.1.2
          rw [mremap_budget_refused_no_fresh_sys_inv (in_arg i 0) (in_arg i 1)
            (in_arg i 2) (in_arg i 3) m r Hinv Hlz Hmat hmark] at hf
          exact absurd hf (by simp)
        · rw [ite_eq_right hcond] at hchk
          exact absurd hchk (by simp)
  all_goals (exact absurd hchk (by simp))

end LinuxSem.Checks.BudgetPremiseMremap
