/-
  * LinuxSem.Checks.MapsFit — every live mapping ends inside the address
    space.

    Not part of the trusted specification: a ledger invariant, proved over
    the same dispatcher `Checks.VmMapsDisjoint` walks for `vm_wf`.

    `vm_fit h` says every `vm_maps` entry `(a, sz)` ends at or below
    `two_pow_64`, i.e. `bv_unsigned a + bv_unsigned sz ≤ two_pow_64`.  It
    is NOT a consequence of `VmMapsDisjoint.vm_wf`: that invariant bounds
    how many entries own a page-aligned address and that no size is zero,
    and an entry `(2^64 - 4096, 8192)` meets both — while its end is
    `2^64 + 4096`.  `oversize_entry_violates_fit` below is that entry,
    decided.

    WHAT IT IS FOR: `Sys/Mm/Mremap.lean`'s move arm charges the new length
    of a moved mapping against the budget, and the range it reconstructs is
    read off the ledger's own `word` fields — so a surviving entry whose
    end wraps past `2^64` would re-charge the wrong range.  The hypothesis
    that arm needs is stated on `map_remove (vm_maps h) old` (every
    SURVIVING entry ends inside the address space), and `vm_fit_map_remove`
    below discharges it from `vm_fit`.  That is why the invariant is stated
    over a whole `VmMaps` and preserved by every modeled syscall rather
    than assumed per call site.

    What every writer of `vm_maps` does to the list, and why each keeps the
    invariant:

    - a fresh grant (`mmap`, `brk` grow, `mremap` grow in place and move)
      conses one entry whose end the writer has bounded — by `alloc_top`
      for `mmap` and `mremap` (`alloc_top_lt` puts that below `2^64`), by a
      `word` break for `brk`;
    - a cut (`munmap`, `mremap` move's source, `brk` shrink, `MAP_FIXED`
      over live mappings) filters the list or subtracts a range from it,
      and every remnant of `iv_subtract` (`LinuxProcessSem/StateVm.lean`)
      ends no later than the entry it came from (`iv_subtract_fit`);
    - `mremap` shrink re-records the source at a smaller size
      (`maps_fit_cons_sub`).

    As with `vm_wf`, the statement is the base case (`init_model_vm_fit`,
    the ledger starts empty) and preservation by every modeled syscall
    (`check_syscall_preserves_vm_fit`, `syscall_spec_preserves_vm_fit`).
    Carrying it inside the whole-run invariant bundle is the job of the
    ledger-invariant package that follows this one; nothing here depends on
    that, and no run-level theorem is claimed in this module.

    WHY THERE IS NO KERNEL CITATION.  The bound is `two_pow_64`, the width
    of `word` — not `TASK_SIZE` and not a per-arch `TASK_SIZE_MAX`.  So the
    statement is about how the ledger ENCODES an interval (`a` and `sz` are
    both `word`, so a reconstructed end can wrap), not about any test the
    kernel applies: `mmap`'s and `munmap`'s TASK_SIZE guards are modelled
    separately (`munmap_cut_ok`, `mmap_fixed_noaccess_b`, `mmap_fixed_rw_b`),
    and those are what bound a real placement.  A `word`-spelled end that
    wraps to a small number is what this invariant rules out, and it is a
    property of the model's arithmetic rather than of a Linux function —
    hence no file:line here.
-/

import LinuxSem.Checks.VmMapsDisjoint

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
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.VmMapsDisjoint

namespace LinuxSem.Checks.MapsFit

open LinuxSem.Common.RocqSpelling

/-! ## The invariant -/

/-- Every entry `(a, sz)` of a ledger list ends at or below `2^64`. -/
def maps_fit (maps : List (word × word)) : Prop :=
  ∀ a sz, (a, sz) ∈ maps → bv_unsigned a + bv_unsigned sz ≤ two_pow_64

/-- The invariant on a whole `VmMaps`. -/
def vm_fit (h : VmMaps) : Prop := maps_fit (vm_maps h)

/-- The form `Mremap`'s move-charge lemmas take: on the list `map_remove`
    leaves behind, every entry still ends inside the address space. -/
theorem vm_fit_map_remove (h : VmMaps) (old : word) (Hfit : vm_fit h)
    (a sz : word) (Hin : (a, sz) ∈ map_remove (vm_maps h) old) :
    bv_unsigned a + bv_unsigned sz ≤ two_pow_64 := by
  unfold map_remove at Hin
  exact Hfit a sz (List.mem_filter.mp Hin).1

/-! ## Sanity checks on the definition

    `maps_fit` is a `∀` over two `word`s, so it has no `Decidable`
    instance to hand (`word` carries no `Fintype`); what is decided below
    is the arithmetic.  The counterexample is the one the module header
    names, and it is why the invariant is a second ledger invariant rather
    than a corollary of `vm_wf`. -/

/-- `(2^64 - 4096, 8192)` ends ABOVE `2^64`, so `vm_wf` alone cannot
    imply `vm_fit`.  (The entry is `vm_wf`-legal: it is page aligned and
    its size is nonzero.) -/
theorem oversize_entry_violates_fit :
    ¬ maps_fit ([(Z_to_bv 64 (-4096), Z_to_bv 64 8192)] : List (word × word)) := by
  intro H
  have h := H (Z_to_bv 64 (-4096)) (Z_to_bv 64 8192) (by simp)
  have h1 : bv_unsigned (Z_to_bv 64 (-4096)) = 18446744073709547520 := by decide
  have h2 : bv_unsigned (Z_to_bv 64 8192) = 8192 := by decide
  rw [h1, h2] at h
  have hbad : ¬ (18446744073709547520 + 8192 ≤ two_pow_64) := by
    unfold two_pow_64
    decide
  exact absurd h hbad

/-- …while a page-aligned list of ordinary grants fits, by computation. -/
theorem two_grants_fit :
    maps_fit ([(Z_to_bv 64 4096, Z_to_bv 64 4096),
               (Z_to_bv 64 8192, Z_to_bv 64 12288)] : List (word × word)) := by
  intro a sz hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  have h1 : bv_unsigned (Z_to_bv 64 4096) = 4096 := by decide
  have h2 : bv_unsigned (Z_to_bv 64 8192) = 8192 := by decide
  have h3 : bv_unsigned (Z_to_bv 64 12288) = 12288 := by decide
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h1]
    unfold two_pow_64
    decide
  · rw [h2, h3]
    unfold two_pow_64
    decide

/-! ## Closure of `maps_fit` under the ways a writer builds `vm_maps` -/

theorem maps_fit_nil : maps_fit [] := by
  intro a sz hmem
  exact absurd hmem (by simp)

theorem maps_fit_cons (maps : List (word × word)) (a n : word)
    (Hf : maps_fit maps) (Hb : bv_unsigned a + bv_unsigned n ≤ two_pow_64) :
    maps_fit ((a, n) :: maps) := by
  intro b s hmem
  rcases List.mem_cons.mp hmem with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Hb
  · exact Hf b s h

theorem maps_fit_app (l1 l2 : List (word × word))
    (H1 : maps_fit l1) (H2 : maps_fit l2) : maps_fit (l1 ++ l2) := by
  intro a sz hmem
  rcases List.mem_append.mp hmem with h | h
  · exact H1 a sz h
  · exact H2 a sz h

theorem maps_fit_filter (f : word × word → Bool) (maps : List (word × word))
    (H : maps_fit maps) : maps_fit (maps.filter f) := by
  intro a sz hmem
  exact H a sz (List.mem_filter.mp hmem).1

/-- Each remnant of a cut ends no later than the entry it came from, at
    any cut: the left remnant keeps the entry's base and shrinks its size,
    and the right remnant exists only when the cut ends inside the entry,
    so its base — `max a hi` — plus its size is the entry's own end. -/
theorem iv_subtract_fit (a sz : word) (lo hi : Int)
    (Hfit : bv_unsigned a + bv_unsigned sz ≤ two_pow_64) :
    maps_fit (iv_subtract a sz lo hi) := by
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  simp only [bv_unsigned, two_pow_64] at Hfit ha hs
  intro b s hmem
  simp only [bv_unsigned, two_pow_64]
  unfold iv_subtract at hmem
  dsimp only at hmem
  rw [List.mem_append] at hmem
  rcases hmem with h | h
  · by_cases h1 : (a.toNat : Int) < lo
    · rw [ite_eq_left h1, List.mem_singleton] at h
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
      have hz : ((BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
          = min (sz.toNat : Int) (lo - (a.toNat : Int)) :=
        u64_min_eq _ _ hs.1 hs.2 (by omega)
      rw [hz]
      have hm : min (sz.toNat : Int) (lo - (a.toNat : Int)) ≤ (sz.toNat : Int) :=
        Int.min_le_left _ _
      omega
    · rw [ite_eq_right h1] at h
      exact absurd h (by simp)
  · by_cases h2 : hi < (a.toNat : Int) + (sz.toNat : Int)
    · rw [ite_eq_left h2, List.mem_singleton] at h
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
      have hbase : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
          = max (a.toNat : Int) hi :=
        u64_max_eq _ _ ha.1 ha.2 (by omega)
      have hszv : ((BitVec.ofInt 64
            ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi)).toNat : Int)
          = (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by
        apply u64_sub_eq
        · rw [Int.max_le]
          exact ⟨by omega, by omega⟩
        · have h := Int.le_max_left (a.toNat : Int) hi
          omega
      rw [hbase, hszv]
      omega
    · rw [ite_eq_right h2] at h
      exact absurd h (by simp)

theorem maps_subtract_fit (maps : List (word × word)) (lo hi : Int)
    (H : maps_fit maps) : maps_fit (maps_subtract maps lo hi) := by
  induction maps with
  | nil => exact maps_fit_nil
  | cons hd r ih =>
    obtain ⟨a, sz⟩ := hd
    simp only [maps_subtract]
    apply maps_fit_app
    · exact iv_subtract_fit a sz lo hi (H a sz (by simp))
    · exact ih (fun b s hb => H b s (by simp [hb]))

/-- `mremap`'s in-place shrink: the source, re-recorded smaller.  The base
    is unchanged, so the new entry cannot end later than the old one did. -/
theorem maps_fit_cons_sub (maps : List (word × word)) (a n0 n : word)
    (Hf : maps_fit maps) (Hin : (a, n0) ∈ maps)
    (Hle : bv_unsigned n ≤ bv_unsigned n0) :
    maps_fit ((a, n) :: map_remove maps a) := by
  apply maps_fit_cons
  · unfold map_remove
    exact maps_fit_filter _ _ Hf
  · have h := Hf a n0 Hin
    omega

/-! ## The same shapes at the level of a whole `VmMaps`

    Each writer's accepting branch builds its post-ledger with
    `VmMaps.mkVmMapsFull`, so the list algebra above needs one application
    per shape rather than a case split at every leaf of the checker walk.
    These mirror `Chain/Writers.lean`'s `vm_wf_of_vm_maps`,
    `vm_wf_grant_app`, `vm_wf_subtract_h` and `vm_wf_span_h`; the only
    difference is what the leaf needs from the guard — `maps_fit` asks for
    the END of the granted range, `maps_wf` for its freedom.  The FRAME
    shape is here too, as `vm_fit_of_m_vmmaps`, because 85 of the 90 table
    arms are frames. -/

/-- A step that leaves the whole `VmMaps` record alone — the FRAME shape,
    `m_vmmaps m' = m_vmmaps m` — preserves the invariant, since it reads
    only `vm_maps`. -/
theorem vm_fit_of_m_vmmaps {m m' : Model} (h : m_vmmaps m' = m_vmmaps m)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  rw [h]
  exact Hfit

/-- A step that leaves `vm_maps` alone preserves the invariant. -/
theorem vm_fit_of_vm_maps {m m' : Model}
    (h : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m))
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold vm_fit at *
  rw [h]
  exact Hfit

/-- A FRESH grant `(a, n)` consed on, given the writer's own ceiling on
    the granted range (`alloc_top` for `mmap`/`mremap`, a `word` break for
    `brk`).  Unlike `vm_wf_grant_app` nothing is asked about `region_free`:
    `maps_fit` reads only the end of the range. -/
theorem vm_fit_grant (h : VmMaps) (a n : word) (noacc : List (word × word))
    (Hfit : vm_fit h) (Hb : bv_unsigned a + bv_unsigned n ≤ two_pow_64) :
    vm_fit (VmMaps.mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) noacc
      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_fit_cons (vm_maps h) a n Hfit Hb

/-- A `maps_subtract` rebuild can only shrink every entry, so it preserves
    the invariant at any interval — no bound on the interval is needed,
    which is what makes `munmap`'s partial cut free here. -/
theorem vm_fit_subtract (h : VmMaps) (lo hi : Int) (noacc : List (word × word))
    (Hfit : vm_fit h) :
    vm_fit (VmMaps.mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) lo hi) noacc
      (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_subtract_fit (vm_maps h) lo hi Hfit

/-- The SPANNING replacement shape (`mmap_fixed_rw_span_next`,
    `mmap_fixed_noaccess_span_next`): the request is consed onto the ledger
    after the same range has been subtracted out of it, so the grant only
    has to fit. -/
theorem vm_fit_span (h : VmMaps) (a n : word) (noacc : List (word × word))
    (Hfit : vm_fit h) (Hhi : bv_unsigned a + bv_unsigned n ≤ two_pow_64) :
    vm_fit (VmMaps.mkVmMapsFull (vm_reserved h)
      ((a, n) :: maps_subtract (vm_maps h) (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))
      noacc (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) :=
  maps_fit_cons _ a n (maps_subtract_fit _ _ _ Hfit) Hhi

/-! ## `brk` — the grow grant, and the writer's own walk

    `brk_grants` records `[old, r)` only when `brk_is_grow` holds, i.e. when
    `old < r` unsigned.  So `r - old` cannot wrap, and the recorded interval
    ends at the break `r` itself — a `word`, hence below `2^64`.  That is
    the whole argument, and it is why `brk_model_next_fit` needs no
    `brk_r_ok` hypothesis: unlike `vm_wf`'s proof (`brk_grant_wf`), nothing
    here reads the placement gate. -/

theorem brk_grants_fit (req r old : word)
    (Hgrow : brk_is_grow req r old = true) : maps_fit (brk_grants req r old) := by
  unfold brk_grants
  rw [ite_eq_left Hgrow]
  apply maps_fit_cons
  · exact maps_fit_nil
  · unfold brk_is_grow at Hgrow
    simp only [Bool.and_eq_true] at Hgrow
    obtain ⟨⟨_, _⟩, hlt⟩ := Hgrow
    have hlt' : (old.toNat : Int) < (r.toNat : Int) := by simpa using hlt
    have hle : old ≤ r := by
      rw [BitVec.le_def]
      bvnorm
      omega
    have Hsz : bv_unsigned (r - old) = bv_unsigned r - bv_unsigned old := by
      bvnorm
      rw [BitVec.toNat_sub_of_le hle]
      bvnorm
      omega
    rw [Hsz]
    have hr := (bv_unsigned_range_u64 r).2
    bvnorm
    omega

theorem brk_model_next_fit (h : VmMaps) (req r : word) (Hfit : vm_fit h) :
    vm_fit (brk_model_next h req r) := by
  show maps_fit (brk_maps_next h req r)
  unfold brk_maps_next
  by_cases hsh : (decide (0 < ((vm_brk h).toNat : Int)) &&
      decide ((r.toNat : Int) < ((vm_brk h).toNat : Int))) = true
  · rw [ite_eq_left hsh]
    exact maps_subtract_fit _ _ _ Hfit
  · rw [ite_eq_right hsh]
    apply maps_fit_app
    · by_cases hgrow : brk_is_grow req r (vm_brk h) = true
      · have hbg : brk_grants req r (vm_brk h) = [(vm_brk h, r - vm_brk h)] := by
          unfold brk_grants
          rw [ite_eq_left hgrow]
        rw [hbg]
        exact hbg ▸ brk_grants_fit req r (vm_brk h) hgrow
      · have hbg : brk_grants req r (vm_brk h) = [] := by
          unfold brk_grants
          rw [ite_eq_right hgrow]
        rw [hbg]
        exact maps_fit_nil
    · exact Hfit

/-- `brk`'s preservation: the checker's own walk (`Core.lean`'s
    `check_brk_preserves`), with `brk_model_next_fit` at the one accepting
    leaf.  The `brk_r_ok` conjunct of the guard is not read here. -/
theorem check_brk_preserves_fit (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_brk req eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  unfold check_brk at H
  cases ws with
  | nil =>
    cases cs with
    | nil =>
      cases ci with
      | nil =>
        by_cases hc : (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (m_vmmaps m).vm_brk)
            && listNN_eqb us (brk_unmaps ret (m_vmmaps m).vm_brk)) = true
        · simp only [hc, ite_true] at H
          obtain ⟨rfl, rfl⟩ := H
          rw [vmm_brk_next]
          exact brk_model_next_fit (m_vmmaps m) req ret Hfit
        · simp only [hc] at H
          exact absurd H (by simp)
      | cons _ _ => exact absurd H (by simp)
    | cons _ _ => exact absurd H (by simp)
  | cons _ _ => exact absurd H (by simp)

/-! ## `mprotect` — the writer whose `vm_maps` is untouched

    `mprotect` rebuilds `vm_noaccess` and the mt/mz backing ledgers and
    carries `vm_maps` over verbatim, so the invariant rides along.  This is
    `Chain/Writers.lean`'s `check_mprotect_preserves` branch for branch; only
    the two leaves differ. -/

theorem check_mprotect_preserves_fit (addr len prot : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mprotect addr len prot eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold check_mprotect at H
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · rw [ite_eq_left hgrows] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hfit
  · rw [ite_eq_right hgrows] at H
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hfit
    · rw [ite_eq_right halign] at H
      by_cases hlen : w_is0 len = true
      · rw [ite_eq_left hlen] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hfit
      · rw [ite_eq_right hlen] at H
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · rw [ite_eq_left hbig] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hfit
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
                    exact Hfit
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
                    apply vm_fit_of_vm_maps (Hfit := Hfit)
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
                    exact Hfit
                  · exact absurd H (by rw [ite_eq_right hz]; simp)
                all_goals (exact nomatch H)
              · rw [ite_eq_right hrw] at H
                exact nomatch H

/-! ## `munmap` — the writer that DROPS a mapping

    Two accepting shapes, and neither needs a bound: the whole mapping
    (`map_has` hit) filters the ledger, and a filter of a fitting list fits;
    the partial cut (`munmap_cut_ok`) subtracts a range, and no remnant of
    `iv_subtract` outlives its entry.  So `maps_subtract_fit` carries the cut
    with NO hypothesis on the interval at all.

    `Chain/Writers.lean`'s `check_munmap_preserves` is the twin, and the four
    `have`s it needs before its cut leaf (`hnval`, `hhi`, `htop`, `hbig'`) are
    the ones dropped here: they are what `maps_wf_subtract` needs, and
    `vm_fit` reads none of them.  What remains is the same guard walk. -/

theorem check_munmap_preserves_fit (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold check_munmap at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
    exact Hfit
  · rw [ite_eq_right hi] at H
    dsimp only at H
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hfit
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
            exact maps_fit_filter (fun q => !(q.1 == addr)) (vm_maps (m_vmmaps m)) Hfit
          · exact absurd H (by rw [ite_eq_right hc]; simp)
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · rw [ite_eq_left hfree] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hfit
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
                  exact Hfit
                | cons u us' => exact nomatch H
              · rw [ite_eq_right he] at H
                by_cases hc : (w_is0 r && listNN_eqb us [(addr, n)]) = true
                · rw [ite_eq_left hc] at H
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, hevs⟩ := H
                  rw [hm.symm, vmm_mmap_destroyed]
                  exact vm_fit_subtract (m_vmmaps m) (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) _ Hfit
                · rw [ite_eq_right hc] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hcut] at H
            exact nomatch H

/-! ## `mremap` — move, shrink, in-place grow

    Three accepting shapes, and each needs one bound the checker's own gate
    already carries:

    * the SHRINK re-records the source at a smaller size at the same base,
      so `maps_fit_cons_sub` applies and the fit of the source entry is
      never read;
    * the IN-PLACE GROW reappears at `(old, new_n)` and
      `mremap_inplace_grow_b`'s first conjunct bounds
      `old + new_n` by `alloc_top`;
    * the MOVE conses `(r, new_n)` on a filtered ledger and
      `mremap_fresh_b`'s fourth conjunct bounds `r + new_n` by `alloc_top`.

    `Chain/Writers.lean`'s `check_mremap_preserves` is the twin, branch for
    branch; `page_align_is0_false_parts` (there) supplies the roundings and
    the `have`s below are its guard readings, with the two ceiling ones
    (`hceil`, in the grow and the move leaf) added.  The twin's
    `region_free` readings are kept as they stand so the two walks stay in
    step, though `vm_fit` does not read them. -/

theorem check_mremap_preserves_fit (old old_size new_size flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_mremap old old_size new_size flags eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold check_mremap at H
  dsimp only at H
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · rw [ite_eq_left hshape] at H
    exact nomatch H
  · rw [ite_eq_right hshape] at H
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · rw [ite_eq_left halign] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hfit
    · rw [ite_eq_right halign] at H
      by_cases hnew : page_align_is0_b new_size = true
      · rw [ite_eq_left hnew] at H
        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
        exact Hfit
      · rw [ite_eq_right hnew] at H
        by_cases htask : (TASK_SIZE : Int) < page_round_up_Z (new_size.toNat : Int)
        · rw [ite_eq_left htask] at H
          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
          exact Hfit
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
              by_cases heq : (old_nZ == new_nZ) = true
              · rw [ite_eq_left heq] at H
                rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                exact Hfit
              · rw [ite_eq_right heq] at H
                obtain ⟨r, ws, zs, us, cs, copyins⟩ := eff
                cases ws <;> cases copyins <;> try dsimp only at H
                · by_cases herr : errno_ret_in mremap_errnos r = true
                  · rw [ite_eq_left herr] at H
                    cases zs <;> cases us <;> cases cs <;> try dsimp only at H
                    · simp only [check_result.CheckOk.injEq] at H
                      obtain ⟨hm, hevs⟩ := H
                      rw [hm.symm]
                      exact Hfit
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
                          have hle : bv_unsigned new_n ≤ bv_unsigned old_n := by
                            rw [hnewv, holdv]
                            omega
                          rw [vmm_mremap_next]
                          exact maps_fit_cons_sub (vm_maps (m_vmmaps m)) old old_n new_n
                            Hfit Hin hle
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
                            have hbnd : bv_unsigned old + bv_unsigned new_n ≤ two_pow_64 := by
                              have htop := alloc_top_lt (m_vmmaps m)
                              rw [hnewv]
                              bvnorm
                              omega
                            rw [vmm_mremap_next]
                            exact maps_fit_cons (map_remove (vm_maps (m_vmmaps m)) old)
                              old new_n (maps_fit_filter _ _ Hfit) hbnd
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
                        have hbnd : bv_unsigned r + bv_unsigned new_n ≤ two_pow_64 := by
                          have htop := alloc_top_lt (m_vmmaps m)
                          rw [hnewv]
                          bvnorm
                          omega
                        rw [vmm_mremap_next]
                        exact maps_fit_cons (map_remove (vm_maps (m_vmmaps m)) old)
                          r new_n (maps_fit_filter _ _ Hfit) hbnd
                      · rw [ite_eq_right hcond] at H
                        exact nomatch H
                all_goals (exact nomatch H)

/-! ## `mmap` — grants, destroyed ranges, contained replacements, spans

    `Chain/Writers.lean`'s `check_mmap_preserves`, branch for branch.  The
    four post-ledger shapes and what each needs here:

    * the untouched ledger — `exact Hfit`;
    * a FRESH grant, bounded by the placement gate's `alloc_top` ceiling
      (`vm_fit_grant`);
    * a DESTROYED range — `vm_fit_subtract`, which needs nothing beyond
      `vm_fit` (`maps_subtract` only shrinks);
    * a SPANNING grant, `(addr, n)` consed onto the same range subtracted
      out — `vm_fit_span`, bounded by the fixed arm's own overflow test.

    The guard extraction below is the twin's, verbatim: the same `by_cases`
    in the same order, and the same `hA`/`hB`/`hle`/`hhi` readings out of
    the boolean chains.  Only the leaves differ — the twin hands
    `vm_wf_grant_app` a `region_free` fact (which nothing here reads), while
    `vm_fit_grant` is handed the ceiling instead, read at the leaf as
    `have htop := alloc_top_lt (m_vmmaps m)`. -/

theorem check_mmap_preserves_fit (addr len prot flags fd off : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_mmap addr len prot flags fd off eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold check_mmap at H
  by_cases hoff : (!(mmap_off_aligned_b off)) = true
  · rw [ite_eq_left hoff] at H
    by_cases hpl : mmap_pglen_ok_b len = true
    · rw [ite_eq_left hpl] at H
      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
      exact Hfit
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
          exact Hfit
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
                exact Hfit
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
                exact vm_fit_grant (m_vmmaps m) r n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                  exact Hfit
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
                  exact vm_fit_grant (m_vmmaps m) r n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                exact Hfit
              · rw [ite_eq_right hovf] at H
                by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                    alloc_top (m_vmmaps m))
                · rw [ite_eq_left hceil] at H
                  exact nomatch H
                · rw [ite_eq_right hceil] at H
                  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                  · rw [ite_eq_left halign] at H
                    rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                    exact Hfit
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
                              exact Hfit
                            | cons u us =>
                              by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                              · rw [ite_eq_left hdel] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_destroyed]
                                exact vm_fit_subtract (m_vmmaps m) (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) _ Hfit
                              · rw [ite_eq_right hdel] at H
                                exact nomatch H
                          · rw [ite_eq_right herr] at H
                            by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                            · rw [ite_eq_left hsuc] at H
                              simp only [check_result.CheckOk.injEq] at H
                              obtain ⟨hm, hevs⟩ := H
                              rw [hm.symm]
                              rw [vmm_mmap_replacement, vmm_vmmaps]
                              exact Hfit
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
                                exact Hfit
                              | cons u us => exact nomatch H
                            · rw [ite_eq_right herr] at H
                              by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                              · rw [ite_eq_left hsuc] at H
                                simp only [check_result.CheckOk.injEq] at H
                                obtain ⟨hm, hevs⟩ := H
                                rw [hm.symm]
                                rw [vmm_mmap_backing, vmm_vmmaps]
                                exact vm_fit_grant (m_vmmaps m) addr n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                                  exact Hfit
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact vm_fit_subtract (m_vmmaps m) (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) _ Hfit
                                  · rw [ite_eq_right hdel] at H
                                    exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_replacement, vmm_vmmaps]
                                  exact vm_fit_span (m_vmmaps m) addr n _ Hfit (by simp only [bv_unsigned] at *; omega)
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
                  exact Hfit
                · rw [ite_eq_right hovf] at H
                  by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                      alloc_top (m_vmmaps m))
                  · rw [ite_eq_left hceil] at H
                    exact nomatch H
                  · rw [ite_eq_right hceil] at H
                    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                    · rw [ite_eq_left halign] at H
                      rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                      exact Hfit
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
                                  exact Hfit
                                | cons u us =>
                                  by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                  · rw [ite_eq_left hdel] at H
                                    simp only [check_result.CheckOk.injEq] at H
                                    obtain ⟨hm, hevs⟩ := H
                                    rw [hm.symm]
                                    rw [vmm_mmap_destroyed]
                                    exact vm_fit_subtract (m_vmmaps m) (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) _ Hfit
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
                                  apply vm_fit_of_vm_maps (Hfit := Hfit)
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
                                  exact Hfit
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
                                  exact vm_fit_grant (m_vmmaps m) addr n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                                      exact Hfit
                                    | cons u us =>
                                      by_cases hdel : listNN_eqb (u :: us) [(addr, n)] = true
                                      · rw [ite_eq_left hdel] at H
                                        simp only [check_result.CheckOk.injEq] at H
                                        obtain ⟨hm, hevs⟩ := H
                                        rw [hm.symm]
                                        rw [vmm_mmap_destroyed]
                                        exact vm_fit_subtract (m_vmmaps m) (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) _ Hfit
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
                                      exact vm_fit_span (m_vmmaps m) addr n _ Hfit (by simp only [bv_unsigned] at *; omega)
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
                    exact Hfit
                  · rw [ite_eq_right hovf] at H
                    by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                        alloc_top (m_vmmaps m))
                    · rw [ite_eq_left hceil] at H
                      exact nomatch H
                    · rw [ite_eq_right hceil] at H
                      by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                      · rw [ite_eq_left halign] at H
                        rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                        exact Hfit
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
                                  exact Hfit
                                | cons u us => exact nomatch H
                              · rw [ite_eq_right herr] at H
                                by_cases hsuc : (bv_eqb r addr && listNN_eqb us [(addr, n)]) = true
                                · rw [ite_eq_left hsuc] at H
                                  simp only [check_result.CheckOk.injEq] at H
                                  obtain ⟨hm, hevs⟩ := H
                                  rw [hm.symm]
                                  rw [vmm_mmap_backing, vmm_vmmaps]
                                  exact vm_fit_grant (m_vmmaps m) addr n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                                exact Hfit
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
                      exact Hfit
                    · rw [ite_eq_right hovf] at H
                      by_cases hceil : ¬ ((addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤
                          alloc_top (m_vmmaps m))
                      · rw [ite_eq_left hceil] at H
                        exact nomatch H
                      · rw [ite_eq_right hceil] at H
                        by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
                        · rw [ite_eq_left halign] at H
                          rw [check_ret_only_model (m' := m') (evs := evs) (H := H)]
                          exact Hfit
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
                                    exact Hfit
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
                                    exact vm_fit_grant (m_vmmaps m) addr n _ Hfit (by have htop := alloc_top_lt (m_vmmaps m); simp only [bv_unsigned] at *; omega)
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
                                  exact Hfit
                                · rw [ite_eq_right hret] at H
                                  exact nomatch H
                              all_goals exact nomatch H
                  · rw [ite_eq_right hrnr] at H
                    exact nomatch H

/-! ## The invariant over the whole dispatcher

    The base case is `execve`'s empty ledger; the step is
    `checked_table`'s 90 arms.  Every arm but five leaves `vm_maps` alone
    (its `*_frame` lemma), and the five writers — `brk`, `munmap`,
    `mremap`, `mmap`, `mprotect` — are the `*_preserves_fit` lemmas above.
    Nothing is re-proved per arm: this is `Chain.lean`'s table induction
    with a different predicate, arm for arm in `checked_table`'s own
    order. -/

/-- `execve` establishes it: the ledger starts empty. -/
theorem init_model_vm_fit (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) :
    vm_fit (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) := by
  have hv : vm_maps (m_vmmaps (init_model reserved brk0 mbase sp lim inp)) = [] := rfl
  unfold vm_fit
  rw [hv]
  exact maps_fit_nil

/-- THE ARM INVARIANT: the arm's checker leaves `vm_fit` alone.  Stated over
    the `ca_check` FIELD, as `arm_preserves_vm` is, so the table statement
    can be a `Forall` over `checked_table`. -/
def arm_preserves_fit (c : CheckedArm) : Prop :=
  ∀ (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event),
    c.ca_check i eff m = .CheckOk m' evs →
    vm_fit (m_vmmaps m) → vm_fit (m_vmmaps m')

/-- THE TABLE, all 90 arms in `checked_table`'s own order.  `repeat'
    constructor` peels the `Forall` and leaves one goal per arm in table
    order, so the count has to close: an arm cannot be silently dropped.

    Each arm is `Chain/Arms.lean`'s three steps — `simp only [arm_X] at H`
    (the arm record's TERM-level equation), the frame, and the invariant —
    with `vm_fit` in place of `vm_wf`.  The `simp only` must be `simp only`:
    a bare `unfold arm_X at H` leaves the `ca_check` PROJECTION of the record
    literal unreduced, and the frame's word arguments (which occur only in
    `H`) then cannot be inferred — measured on `arm_listen`, whose
    `check_listen_frame` takes an explicit `backlog`. -/
theorem checked_table_preserves_fit : Forall arm_preserves_fit checked_table := by
  simp only [checked_table]
  repeat' constructor
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getcwd] at H
    exact check_getcwd_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_eventfd2] at H
    exact check_eventfd2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_epoll_create1] at H
    exact check_epoll_create1_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_epoll_ctl] at H
    exact check_epoll_ctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_epoll_pwait] at H
    exact check_epoll_pwait_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_dup] at H
    exact check_dup_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_dup3] at H
    exact check_dup3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_fcntl] at H
    exact check_fcntl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_ioctl] at H
    exact check_ioctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_flock] at H
    exact check_flock_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_unlinkat] at H
    exact check_unlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_ftruncate] at H
    exact check_ftruncate_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_faccessat] at H
    exact check_faccessat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_openat] at H
    exact check_openat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_close] at H
    exact check_close_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_pipe2] at H
    exact check_pipe2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getdents64] at H
    exact check_getdents64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_lseek] at H
    exact check_lseek_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_read] at H
    exact check_read_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_write] at H
    exact check_write_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_readv] at H
    exact check_readv_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_writev] at H
    exact check_writev_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_pread64] at H
    exact check_pread64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_pwrite64] at H
    exact check_pwrite64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_pselect6] at H
    exact check_pselect6_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_ppoll] at H
    exact check_ppoll_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_readlinkat] at H
    exact check_readlinkat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_newfstatat] at H
    exact check_newfstatat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_fstat] at H
    exact check_fstat_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_fsync] at H
    exact check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_fdatasync] at H
    exact check_fsync_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_timerfd_create] at H
    exact check_timerfd_create_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_exit] at H
    exact check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_exit_group] at H
    exact check_exit_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_set_tid_address] at H
    exact check_set_tid_address_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_futex] at H
    exact check_futex_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_nanosleep] at H
    exact check_nanosleep_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_clock_gettime] at H
    exact check_clock_gettime_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sched_setscheduler] at H
    exact check_sched_setscheduler_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sched_getaffinity] at H
    exact check_sched_getaffinity_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sched_yield] at H
    exact check_sched_yield_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_tkill] at H
    exact check_tkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_tgkill] at H
    exact check_tgkill_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sigaltstack] at H
    exact check_sigaltstack_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_rt_sigaction] at H
    exact check_rt_sigaction_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_rt_sigprocmask] at H
    exact LinuxSem.Checks.VmMapsDisjoint.check_rt_sigprocmask_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setgid] at H
    exact check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setuid] at H
    exact check_setid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setresuid] at H
    exact check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setresgid] at H
    exact check_setresid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setsid] at H
    exact check_setsid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getgroups] at H
    exact check_getgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setgroups] at H
    exact check_setgroups_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_uname] at H
    exact check_uname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_prctl] at H
    exact check_prctl_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_gettimeofday] at H
    exact check_gettimeofday_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getpid] at H
    exact check_getpid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getuid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_geteuid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getgid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getegid] at H
    exact check_getid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_gettid] at H
    exact check_gettid_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_socket] at H
    exact check_socket_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_socketpair] at H
    exact check_socketpair_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_bind] at H
    exact check_bind_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_listen] at H
    exact check_listen_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_accept] at H
    exact check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_connect] at H
    exact check_connect_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getsockname] at H
    exact check_getsockname_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getpeername] at H
    exact check_getpeername_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sendto] at H
    exact check_sendto_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_recvfrom] at H
    exact check_recvfrom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_setsockopt] at H
    exact check_setsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getsockopt] at H
    exact check_getsockopt_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_shutdown] at H
    exact check_shutdown_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_sendmsg] at H
    exact check_sendmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_recvmsg] at H
    exact check_recvmsg_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    simp only [arm_brk] at H
    exact check_brk_preserves_fit (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hfit := Hfit)
  · intro i eff m m' evs H Hfit
    simp only [arm_munmap] at H
    exact check_munmap_preserves_fit (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hfit := Hfit)
  · intro i eff m m' evs H Hfit
    simp only [arm_mremap] at H
    exact check_mremap_preserves_fit (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hfit := Hfit)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_clone] at H
    exact check_clone_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    simp only [arm_mmap] at H
    exact check_mmap_preserves_fit (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hfit := Hfit)
  · intro i eff m m' evs H Hfit
    simp only [arm_mprotect] at H
    exact check_mprotect_preserves_fit (eff := eff) (m := m) (m' := m') (evs := evs) (H := H) (Hfit := Hfit)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_madvise] at H
    exact check_madvise_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_accept4] at H
    exact check_accept4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_wait4] at H
    exact check_wait4_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_prlimit64] at H
    exact check_prlimit64_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_getrandom] at H
    exact check_getrandom_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_clone3] at H
    exact check_clone3_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)
  · intro i eff m m' evs H Hfit
    refine vm_fit_of_m_vmmaps (Hfit := Hfit) ?_
    simp only [arm_faccessat2] at H
    exact check_faccessat2_frame (eff := eff) (m := m) (m' := m') (evs := evs) (H := H)

/-- The table in the membership form a lookup produces (`lookup_ca_In`). -/
theorem checked_table_preserves_fit_mem : ∀ c ∈ checked_table, arm_preserves_fit c :=
  forall_mem_of_forall checked_table_preserves_fit

/-- THE CHECKER-SIDE THEOREM: if `checked_table` ACCEPTS this syscall then
    the ledger still ends inside the address space.  An unmodelled number
    makes the hypothesis impossible (`CheckUnmodeled` is not `CheckOk`), so
    the statement needs no coverage premise. -/
theorem check_syscall_preserves_vm_fit (i : SyscallInput) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : CheckedTable.check_syscall i eff m = .CheckOk m' evs)
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') := by
  unfold CheckedTable.check_syscall at H
  unfold LinuxSem.Checks.Sys.Dispatch.check_syscall at H
  cases hlook : lookup_ca checked_table (i.in_sysno.toNat : Int) with
  | none =>
    rw [hlook] at H
    exact absurd H (by simp)
  | some c =>
    rw [hlook] at H
    exact checked_table_preserves_fit_mem c (lookup_ca_In checked_table _ c hlook)
      i eff m m' evs H Hfit

/-- THE SPEC-SIDE RESULT: the same statement for the RELATIONAL spec,
    through the completeness direction, so the invariant is a property of
    ADMITTED syscalls and not only of the checker's answers. -/
theorem syscall_spec_preserves_vm_fit (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event) (H : Specs.syscall_spec i m (.ok eff m' evs))
    (Hfit : vm_fit (m_vmmaps m)) : vm_fit (m_vmmaps m') :=
  check_syscall_preserves_vm_fit i eff m m' evs
    (CheckedTable.check_syscall_complete_ok i eff m m' evs H) Hfit

end LinuxSem.Checks.MapsFit
