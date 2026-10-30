/-
  * LinuxSem.Checks.BudgetPremiseInv — the move's budget gate on
    invariant states.

    Not part of the trusted specification.  `Checks/BudgetPremise.lean`'s
    `mremap_move_charge_at_fresh` — the reason the move's charge is the
    same at every fresh destination — takes four ledger hypotheses: that
    no protected range meets the destination, that every live mapping
    other than the source lies inside the address space, and the two
    "the destination carries no backing metadata" identities on the lazy
    and materialized ledgers.  The first two follow from
    `NoaccessOwned.sys_inv`, which
    `NoaccessOwned.sstep_preserves_sys_inv` carries along a run and
    `NoaccessOwned.init_config_sys_inv` establishes at the state a run
    starts from; this file states the gate fact with that one hypothesis
    in their place.

    THE ONE LEDGER HYPOTHESIS LEFT is that the lazy ledgers are empty
    (`m_vm_lazy m = []` and `m_vm_materialized m = []`): at that state
    the run holds no MAP_NORESERVE reservation and no first-touched page
    of one.  It is not a run invariant: it fails from a run's first
    successful MAP_NORESERVE reservation on, for as long as the
    reservation lives (an ASan runtime keeps its for the whole run —
    `Common/LazyFrame.lean`), so a consumer discharges it from its own
    program.  The same lemma without that hypothesis is
    `mremap_move_budget_admits_fresh`, which takes the two lazy-ledger
    identities at the destination instead, exactly as
    `Mremap.mremap_move_charge_at_fresh` states them.

    THE PLACEMENT OF `fresh_dst_avoids_noaccess`.  The original files it
    in `Checks/BudgetPremise.v`; here it is stated in this module instead,
    because the module the port already has for the same conclusion
    (`Mremap.mremap_fresh_avoids_noaccess`) takes the WHOLE of
    `mremap_fresh_b` — budget conjunct included — and the proof below
    needs the conclusion BEFORE the budget conjunct is established.  The
    argument is the same page-granularity one, on exactly the
    non-budget hypotheses; nothing else in the tree restates it.

    The last two lemmas are in `mremap_spec`'s own terms: it passes
    `new_n` as the word of `new_nZ = page_round_up_Z (new_size.toNat : Int)`
    after `page_align_is0_b new_size = false`, and
    `Mremap.mremap_fresh_b` states its bound on `new_nZ`.
    `mremap_fresh_b_intro_sys_inv` concludes `mremap_fresh_b = true` from
    the move's budget gate and the destination's own guards.

    SPELLING.  The original binds `new_nZ` with a `let` inside the
    statement of the last two lemmas; here the binding is zeta-reduced, so
    `page_round_up_Z (new_size.toNat : Int)` is written out where the
    original writes `new_nZ`.  It is the same statement — a `let` in a
    proposition is its own body — and it spares every call site an
    equation.  `bv_unsigned x` is `(x.toNat : Int)` through the
    `RocqSpelling` abbrev, as everywhere else in this tree.
-/

import LinuxSem.Checks.BudgetPremise
import LinuxSem.Checks.MapsFit
import LinuxSem.Checks.NoaccessOwned

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.BudgetPremise
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.BudgetPremiseInv

open LinuxSem.Common.RocqSpelling

/- =========================================================================
   The protected half of "fresh", from the ledger invariant alone
   ========================================================================= -/

/-- The protected ledger's half of `mremap_fresh_b`'s freeness, from
    `noaccess_pages_owned` alone: `Mremap.mremap_fresh_avoids_noaccess`
    proves the same conclusion but takes the whole gate, budget conjunct
    included, while its argument reads only the alignment of `dst`, the
    shape of `new_n` and freeness against `vm_reserved ++ vm_maps`.  A
    consumer can therefore derive the `vm_noaccess` hypothesis of
    `Mremap.mremap_move_charge_at_fresh` BEFORE it knows the gate passes.

    `0 < new_n` is kept although the argument goes through with it
    unused: it is one of the gate's own conjuncts, and a consumer
    discharging the rest of the gate has it in hand. -/
theorem fresh_dst_avoids_noaccess (h : VmMaps) (dst new_n : word)
    (Hown : noaccess_pages_owned h)
    (_Hpos : 0 < (new_n.toNat : Int))
    (Hmod : (new_n.toNat : Int) % page_size = 0)
    (Halign : (dst.toNat : Int) % page_size = 0)
    (Hrf : region_free (h.vm_reserved ++ h.vm_maps) dst new_n = true) :
    region_free h.vm_noaccess dst new_n = true := by
  -- a page-aligned request ends on a page boundary
  have Hhi : ((dst.toNat : Int) + (new_n.toNat : Int)) % page_size = 0 := by
    rw [Int.add_emod, Halign, Hmod]
    decide
  refine region_free_intro _ _ _ ?_
  intro a n Hin
  obtain ⟨Hn, Hpage⟩ := Hown a n Hin
  cases hov : iv_overlap dst new_n a n with
  | false => rfl
  | true =>
      exfalso
      unfold iv_overlap at hov
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hov
      obtain ⟨hov1, hov2⟩ := hov
      -- the protected byte the request cannot serve: the top of the two bases
      have hx : (a.toNat : Int) ≤ max (dst.toNat : Int) (a.toNat : Int) ∧
          max (dst.toNat : Int) (a.toNat : Int) <
            (a.toNat : Int) + (n.toNat : Int) := by
        constructor <;> omega
      obtain ⟨b, s, Hinm, Hb1, Hb2⟩ := Hpage _ hx
      -- its whole page is inside the request, which is page aligned
      have hxmem : (dst.toNat : Int) ≤ max (dst.toNat : Int) (a.toNat : Int) ∧
          max (dst.toNat : Int) (a.toNat : Int) <
            (dst.toNat : Int) + (new_n.toNat : Int) := by
        constructor <;> omega
      obtain ⟨Hf1, Hf2⟩ :=
        page_round_down_Z_within (dst.toNat : Int)
          ((dst.toNat : Int) + (new_n.toNat : Int))
          (max (dst.toNat : Int) (a.toNat : Int)) Halign Hhi hxmem
      -- …so that entry of `vm_maps` overlaps the destination, which the
      -- gate already refused
      have hno := region_free_In _ _ _ b s Hrf (List.mem_append_right _ Hinm)
      have hyes : iv_overlap dst new_n b s = true := by
        simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> omega
      rw [hyes] at hno
      exact absurd hno (by simp)

/- =========================================================================
   The move's charge admits every fresh destination
   ========================================================================= -/

/-- The bridge `Mremap.mremap_move_charge_at_fresh` gives, written as an
    equation between the two gates: at a destination the move's charge is
    invariant over, the destination-free gate and the in-place
    post-state's gate are the same `decide`.  (`Checks/BudgetPremise.lean`
    has this as a `private` step of
    `mremap_budget_refused_refuses_move`; it is restated here because
    that one is not visible outside its module.) -/
theorem mremap_move_budget_eq_final (m : Model) (old old_n dst new_n : word)
    (hch : vm_backing_used (mremap_model_next m old old_n dst new_n)
      = mremap_move_charge m old old_n new_n) :
    mremap_move_budget_b m old old_n new_n
    = mremap_final_budget_b m old old_n dst new_n := by
  unfold mremap_move_budget_b mremap_final_budget_b vm_backing_within_limit
  rw [mremap_model_next_limit, hch]

/-- THE MOVE'S CHARGE ADMITS EVERY FRESH DESTINATION: where the move's
    budget gate `Mremap.mremap_move_budget_b` passes, the gate
    `Mremap.mremap_final_budget_b` that `Mremap.mremap_fresh_b` reads
    passes at every destination that is page aligned, ends at or below
    `alloc_top` and is free against `vm_reserved ++ vm_maps` — the
    non-budget conjuncts of `Mremap.mremap_fresh_b` that bear on the
    charge.  The ledger hypotheses are `State.noaccess_pages_owned`, the
    fit of every live mapping other than the source, and the two
    lazy-ledger identities `Mremap.mremap_move_charge_at_fresh` takes;
    the `vm_noaccess` hypothesis of that lemma comes from
    `fresh_dst_avoids_noaccess`.  This is the converse direction of
    `Checks.BudgetPremise.mremap_budget_refused_refuses_move`.

    The two side conditions on `new_n` are what `mremap_spec` supplies at
    the call site: it passes
    `new_n = BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))`
    under `page_align_is0_b new_size = false`. -/
theorem mremap_move_budget_admits_fresh (m : Model) (old old_n dst new_n : word)
    (Hdalign : (dst.toNat : Int) % page_size = 0)
    (Hnmod : (new_n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (new_n.toNat : Int))
    (Hdtop : (dst.toNat : Int) + (new_n.toNat : Int) ≤ alloc_top (m_vmmaps m))
    (Hdfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      dst new_n = true)
    (Hown : noaccess_pages_owned (m_vmmaps m))
    (Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hlazy : maps_subtract
        (maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int)))
        (dst.toNat : Int) ((dst.toNat : Int) + (new_n.toNat : Int))
      = maps_subtract (m_vm_lazy m) (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int)))
    (Hpages : List.filter (page_outside_range (dst.toNat : Int)
          ((dst.toNat : Int) + (new_n.toNat : Int)))
        (List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m))
      = List.filter (page_outside_range (old.toNat : Int)
          ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m))
    (Hmv : mremap_move_budget_b m old old_n new_n = true) :
    mremap_final_budget_b m old old_n dst new_n = true := by
  have Hend : (dst.toNat : Int) + (new_n.toNat : Int) < two_pow_64 := by
    have h := alloc_top_lt (m_vmmaps m)
    omega
  have Hmaps : region_free (map_remove (m_vmmaps m).vm_maps old) dst new_n = true :=
    region_free_map_remove (m_vmmaps m).vm_maps old dst new_n
      (region_free_app_r _ _ dst new_n Hdfree)
  have Hnoacc : region_free (m_vmmaps m).vm_noaccess dst new_n = true :=
    fresh_dst_avoids_noaccess (m_vmmaps m) dst new_n Hown Hpos Hnmod Hdalign Hdfree
  have hch := mremap_move_charge_at_fresh m old old_n dst new_n
    Hdalign Hnmod Hpos Hend Hfit Hmaps Hnoacc Hlazy Hpages
  rw [← mremap_move_budget_eq_final m old old_n dst new_n hch]
  exact Hmv

/-- The same on a state with empty lazy ledgers (`m_vm_lazy` and
    `m_vm_materialized` both `[]`), where the two lazy-ledger identities
    hold by computation: what is left to cite is
    `State.noaccess_pages_owned` and the fit of the live mappings. -/
theorem mremap_move_budget_admits_fresh_lazyfree (m : Model)
    (old old_n dst new_n : word)
    (Hlz : m_vm_lazy m = [])
    (Hmat : m_vm_materialized m = [])
    (Hdalign : (dst.toNat : Int) % page_size = 0)
    (Hnmod : (new_n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (new_n.toNat : Int))
    (Hdtop : (dst.toNat : Int) + (new_n.toNat : Int) ≤ alloc_top (m_vmmaps m))
    (Hdfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      dst new_n = true)
    (Hown : noaccess_pages_owned (m_vmmaps m))
    (Hfit : ∀ (a sz : word), (a, sz) ∈ map_remove (m_vmmaps m).vm_maps old →
      (a.toNat : Int) + (sz.toNat : Int) ≤ two_pow_64)
    (Hmv : mremap_move_budget_b m old old_n new_n = true) :
    mremap_final_budget_b m old old_n dst new_n = true := by
  have Hlazy : maps_subtract
      (maps_subtract (m_vm_lazy m) (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int)))
      (dst.toNat : Int) ((dst.toNat : Int) + (new_n.toNat : Int))
    = maps_subtract (m_vm_lazy m) (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int)) := by
    rw [Hlz]
    rfl
  have Hpages : List.filter (page_outside_range (dst.toNat : Int)
        ((dst.toNat : Int) + (new_n.toNat : Int)))
      (List.filter (page_outside_range (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m))
    = List.filter (page_outside_range (old.toNat : Int)
        ((old.toNat : Int) + (old_n.toNat : Int))) (m_vm_materialized m) := by
    rw [Hmat]
    rfl
  exact mremap_move_budget_admits_fresh m old old_n dst new_n Hdalign Hnmod Hpos
    Hdtop Hdfree Hown Hfit Hlazy Hpages Hmv

/-- The gate fact on a `NoaccessOwned.sys_inv` state: the protected-ledger
    and fit hypotheses are `sys_inv`'s second and third conjuncts, read
    through `NoaccessOwned.sys_inv_noaccess_pages_owned` and
    `MapsFit.vm_fit_map_remove`. -/
theorem mremap_move_budget_admits_fresh_sys_inv (m : Model)
    (old old_n dst new_n : word)
    (Hinv : sys_inv (m_vmmaps m))
    (Hlz : m_vm_lazy m = [])
    (Hmat : m_vm_materialized m = [])
    (Hdalign : (dst.toNat : Int) % page_size = 0)
    (Hnmod : (new_n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (new_n.toNat : Int))
    (Hdtop : (dst.toNat : Int) + (new_n.toNat : Int) ≤ alloc_top (m_vmmaps m))
    (Hdfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      dst new_n = true)
    (Hmv : mremap_move_budget_b m old old_n new_n = true) :
    mremap_final_budget_b m old old_n dst new_n = true :=
  mremap_move_budget_admits_fresh_lazyfree m old old_n dst new_n Hlz Hmat
    Hdalign Hnmod Hpos Hdtop Hdfree
    (sys_inv_noaccess_pages_owned _ Hinv)
    (vm_fit_map_remove _ old Hinv.2.1) Hmv

/- =========================================================================
   In `mremap_spec`'s own terms
   ========================================================================= -/

/-- `mremap_spec`'s `new_n` is a positive whole number of pages, and its
    word is its `Int` value.  The first conjunct is
    `Checks.BudgetPremise.page_align_is0_b_false_word`; this lemma adds
    the two side conditions the gate lemmas above take on `new_n`. -/
theorem mremap_new_n_shape (new_size : word) (H : page_align_is0_b new_size = false) :
    let new_n : word := BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))
    (new_n.toNat : Int) = page_round_up_Z (new_size.toNat : Int) ∧
      (new_n.toNat : Int) % page_size = 0 ∧ 0 < (new_n.toNat : Int) := by
  intro new_n
  have Hw : (new_n.toNat : Int) = page_round_up_Z (new_size.toNat : Int) :=
    page_align_is0_b_false_word new_size H
  refine ⟨Hw, ?_, ?_⟩
  · rw [Hw]
    exact page_round_up_Z_mod _
  · rw [Hw]
    unfold page_align_is0_b at H
    rw [Bool.or_eq_false_iff] at H
    have hlen : 0 < new_size.toNat := w_is0_false_pos new_size H.1
    have hpos := page_round_up_Z_pos (new_size.toNat : Int) (by omega)
    have hps : (0 : Int) < page_size := by decide
    omega

/-- THE MOVE IS ADMITTED.  In `mremap_spec`'s own terms (`new_n` the word
    of `new_nZ = page_round_up_Z (new_size.toNat : Int)`, after
    `page_align_is0_b new_size = false`): on a state satisfying `sys_inv`
    with empty lazy ledgers, a destination that is not `old`, nonzero,
    page aligned, ends at or below `alloc_top` and is free against
    `vm_reserved ++ vm_maps` passes `mremap_fresh_b` whenever the move's
    budget gate `mremap_move_budget_b` passes. -/
theorem mremap_fresh_b_intro_sys_inv (m : Model) (old_nZ : Int)
    (new_size old old_n dst : word)
    (Hal : page_align_is0_b new_size = false)
    (Hinv : sys_inv (m_vmmaps m))
    (Hlz : m_vm_lazy m = [])
    (Hmat : m_vm_materialized m = [])
    (Hne : (dst == old) = false)
    (Hdpos : 0 < (dst.toNat : Int))
    (Hdalign : (dst.toNat : Int) % page_size = 0)
    (Hdtop : (dst.toNat : Int) + page_round_up_Z (new_size.toNat : Int)
      ≤ alloc_top (m_vmmaps m))
    (Hdfree : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps)
      dst (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true)
    (Hmv : mremap_move_budget_b m old old_n
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true) :
    mremap_fresh_b m old_nZ (page_round_up_Z (new_size.toNat : Int)) old old_n dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true := by
  obtain ⟨Hw, Hnmod, Hnpos⟩ := mremap_new_n_shape new_size Hal
  have Hdt : (dst.toNat : Int) +
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))).toNat
      ≤ alloc_top (m_vmmaps m) := by
    rw [Hw]
    exact Hdtop
  have Hfin : mremap_final_budget_b m old old_n dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int))) = true :=
    mremap_move_budget_admits_fresh_sys_inv m old old_n dst
      (BitVec.ofInt 64 (page_round_up_Z (new_size.toNat : Int)))
      Hinv Hlz Hmat Hdalign Hnmod Hnpos Hdt Hdfree Hmv
  unfold mremap_fresh_b
  dsimp only
  have hne : (!(dst == old)) = true := by simp [Hne]
  rw [hne, Hdfree, Hfin]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.true_and, and_true]
  exact ⟨⟨Hdalign, Hdpos⟩, Hdtop⟩

end LinuxSem.Checks.BudgetPremiseInv
