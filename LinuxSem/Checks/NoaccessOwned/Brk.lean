/-
  * LinuxSem.Checks.NoaccessOwned.Brk — the `brk` writer, and the state the
    invariant exists for.

    `State.noaccess_pages_owned` is not inductive BECAUSE of `brk`: a shrink
    to a break that is not page aligned frees nothing in `Mmap.brk_unmaps`
    (the page-rounded interval is empty) while `brk_maps_next` cuts the
    byte-granular tail `[r, b)` out of `vm_maps`.  If the only witness of a
    protected page had been a grant inside that tail, the page is left
    protected and unowned.

    `na_cover` answers exactly that: the bytes of the orphan slice
    `[b, PAGE_ALIGN b)` may be unowned, provided the FIRST BYTE of the
    break's page is owned.  A shrink can cut the slice out — it cannot cut
    the page's first byte out as well, because `maps_subtract` cuts a range
    and `zone_same_page` says a page-aligned range that holds any byte of
    the slice holds the page's start too (so if the start left, the whole
    slice left).  `brk_shrink_cover` is that argument per protected byte.
-/

import LinuxSem.Checks.NoaccessOwned.Core

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.MapsFit
open LinuxSem.Checks.NoaccessOwned

namespace LinuxSem.Checks.NoaccessOwned

open LinuxSem.Common.RocqSpelling

/-- What a resolution other than "unchanged" says about the request: either
    the break did not move, or it moved to the request and the request was
    a real one (nonzero). -/
theorem brk_r_ok_cases (m : Model) (req r : word)
    (H : brk_r_ok m req r = true) :
    r = vm_brk (m_vmmaps m) ∨ (r = req ∧ w_is0 req = false) := by
  unfold brk_r_ok at H
  dsimp only at H
  by_cases h1 : (w_is0 req ||
      decide ((req.toNat : Int) < ((min_brk (m_vmmaps m)).toNat : Int))) = true
  · rw [ite_eq_left h1] at H
    exact Or.inl (by simpa only [beq_iff_eq] using H)
  · rw [ite_eq_right h1] at H
    have hw0 : w_is0 req = false := by
      cases h : w_is0 req with
      | false => rfl
      | true => rw [h] at h1; simp at h1
    by_cases h2 : decide ((req.toNat : Int) < ((vm_brk (m_vmmaps m)).toNat : Int)) = true
    · rw [ite_eq_left h2] at H
      rcases (Bool.or_eq_true ..).mp H with h | h
      · exact Or.inr ⟨by simpa only [beq_iff_eq] using h, hw0⟩
      · exact Or.inl (by simpa only [beq_iff_eq] using h)
    · rw [ite_eq_right h2] at H
      obtain ⟨h, _⟩ := (Bool.and_eq_true ..).mp H
      rcases (Bool.or_eq_true ..).mp h with h | h
      · exact Or.inr ⟨by simpa only [beq_iff_eq] using h, hw0⟩
      · exact Or.inl (by simpa only [beq_iff_eq] using h)

/-- Normalise the two places a term is written twice — the `bv_unsigned` /
    `vm_brk` `abbrev`s and their bodies — in the goal and every hypothesis,
    then close by `omega`.  `omega` treats the two spellings as distinct
    atoms, and a writer's own walk reintroduces the body spelling every time
    it unfolds a `def` whose body projects a field. -/
macro "na_omega" : tactic =>
  `(tactic| (try simp only [bv_unsigned, vm_brk] at *; omega))

/-- A page-rounded value never exceeds `2^64`: the break is a `word`, and the
    next multiple of the page above `2^64` is out of reach of one that
    started below it. -/
theorem pu_le_two_pow (z : Int) (_H0 : 0 ≤ z) (Hlt : z < two_pow_64) :
    page_round_up_Z z ≤ two_pow_64 := by
  have htwo : two_pow_64 = 4096 * 2 ^ 52 := by unfold two_pow_64; decide
  have hal := pu_aligned z
  unfold page_size at hal
  have hq : page_round_up_Z z = 4096 * (page_round_up_Z z / 4096) := by
    have h := Int.mul_ediv_add_emod (page_round_up_Z z) 4096
    omega
  have hlt2 : page_round_up_Z z < z + 4096 := pu_lt z
  have hq2 : page_round_up_Z z / 4096 ≤ 2 ^ 52 := by omega
  rw [hq]
  omega

/-- THE SHRINK, one protected byte at a time.  `x` survived the cut of the
    protected list, which is `[PAGE_ALIGN r, PAGE_ALIGN b)` (empty for a
    same-page shrink); `vm_maps` lost `[r, b)`.

    Three positions for `x`, and each one is why a remnant is where it is:
    below the new break it is untouched; in the dropped tail it becomes an
    orphan byte, and the page start it re-wraps to is the byte the old
    cover owned, carried out of the cut by `zone_floor` (it lies below
    `r`, so `maps_subtract` keeps it); at or above the old break the old
    orphan byte's page start survives the same way. -/
theorem brk_shrink_cover (maps na : List (word × word)) (b r : Int)
    (a n : word) (x : Int) (Hf : maps_fit maps) (Hsh : na_shape na)
    (Hcov : na_cover maps na b) (Hlt : r < b) (Hin : (a, n) ∈ na)
    (Hx : bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned n)
    (Hcut : ¬ (page_round_up_Z r ≤ x ∧ x < page_round_up_Z b)) :
    owned (maps_subtract maps r b) x ∨
      ((r ≤ x ∧ x < page_round_up_Z r) ∧
        owned (maps_subtract maps r b) (page_round_down_Z r)) := by
  have hps : (0 : Int) < page_size := by unfold page_size; omega
  by_cases hxr : x < r
  · rcases Hcov a n x Hin Hx with ho | ⟨hz, _⟩
    · exact Or.inl (owned_subtract maps r b x Hf ho (by intro hc; omega))
    · exfalso; omega
  · by_cases hxb : x < b
    · -- inside the dropped tail: the new orphan slice, page start preserved
      have hxpu : x < page_round_up_Z r := by
        by_cases h : x < page_round_up_Z r
        · exact h
        · exact absurd ⟨Int.not_lt.mp h, by have := pu_ge b; omega⟩ Hcut
      have hzr : r ≤ x ∧ x < page_round_up_Z r := ⟨by omega, hxpu⟩
      have hfrlt : page_round_down_Z r < r := (zone_floor r x hzr).2
      have hfl : page_round_down_Z x = page_round_down_Z r := (zone_floor r x hzr).1
      refine Or.inr ⟨hzr, ?_⟩
      rw [← hfl]
      obtain ⟨ha1, hn1, -, -⟩ := Hsh a n Hin
      have hhi : (bv_unsigned a + bv_unsigned n) % page_size = 0 := aligned_add _ _ ha1 hn1
      have hwin := page_round_down_Z_within (bv_unsigned a)
        (bv_unsigned a + bv_unsigned n) x ha1 hhi Hx
      have hmem : bv_unsigned a ≤ page_round_down_Z x ∧
          page_round_down_Z x < bv_unsigned a + bv_unsigned n := by
        refine ⟨hwin.1, ?_⟩
        have := hwin.2
        omega
      rcases Hcov a n (page_round_down_Z x) Hin hmem with ho2 | ⟨hz2, _⟩
      · refine owned_subtract maps r b (page_round_down_Z x) Hf ho2 ?_
        intro hc
        omega
      · exfalso; omega
    · -- at or above the old break: the old orphan byte's page start
      rcases Hcov a n x Hin Hx with ho | ⟨hz, ho⟩
      · exact Or.inl (owned_subtract maps r b x Hf ho (by intro hc; omega))
      · have hxpu : x < page_round_up_Z r := by
          by_cases h : x < page_round_up_Z r
          · exact h
          · exact absurd ⟨Int.not_lt.mp h, hz.2⟩ Hcut
        have hzr : r ≤ x ∧ x < page_round_up_Z r := ⟨by omega, hxpu⟩
        have hfrlt : page_round_down_Z r < r := (zone_floor r x hzr).2
        have hfr : page_round_down_Z x = page_round_down_Z r := (zone_floor r x hzr).1
        have hfb : page_round_down_Z x = page_round_down_Z b := (zone_floor b x hz).1
        have hpr : page_round_down_Z r = page_round_down_Z b := by rw [← hfr, ← hfb]
        refine Or.inr ⟨hzr, ?_⟩
        rw [hpr]
        refine owned_subtract maps r b (page_round_down_Z b) Hf ho ?_
        intro hc
        omega


/-- Page rounding up is monotone. -/
theorem pu_mono (x y : Int) (H : x ≤ y) : page_round_up_Z x ≤ page_round_up_Z y := by
  have hx := pu_aligned x
  have hy := pu_aligned y
  have h1 := pu_lt x
  have h2 := pu_ge y
  have h3 := pu_lt y
  unfold page_size at *
  have hqx : page_round_up_Z x = 4096 * (page_round_up_Z x / 4096) := by
    have h := Int.mul_ediv_add_emod (page_round_up_Z x) 4096
    omega
  have hqy : page_round_up_Z y = 4096 * (page_round_up_Z y / 4096) := by
    have h := Int.mul_ediv_add_emod (page_round_up_Z y) 4096
    omega
  rw [hqx, hqy]
  have : page_round_up_Z x / 4096 ≤ page_round_up_Z y / 4096 := by omega
  omega

/-- THE SHRINK RESOLUTION OF `brk_r_ok`, and the three shapes it can leave.

    - `r < b`: the break shrank.  The resolution must be the REQUEST (a
      failed shrink keeps `r = b`), `vm_maps` loses `[r, b)`, and the
      protected list loses the page-rounded interval (which may be empty).
    - `r = b`: nothing moved.
    - `b < r`: the break grew.  Again `r = req`; `vm_maps` gains the
      granted `[b, r)` when `brk_is_grow` fires, and the protected list is
      untouched (a grow frees nothing).

    The two `decide`s in `brk_maps_next` are the shrink test; each case
    evaluates them from the ordering of the two break values alone. -/
theorem brk_model_next_na_inv (m : Model) (req r : word)
    (Hok : brk_r_ok m req r = true) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (brk_model_next (m_vmmaps m) req r) := by
  obtain ⟨hsh, hcov⟩ := Hna
  simp only [bv_unsigned, vm_brk] at *
  have hcases := brk_r_ok_cases m req r Hok
  have hbrk0 : 0 ≤ ((vm_brk (m_vmmaps m)).toNat : Int) := (bv_unsigned_range_u64 _).1
  have hbrk1 : ((vm_brk (m_vmmaps m)).toNat : Int) < two_pow_64 :=
    (bv_unsigned_range_u64 _).2
  show na_inv' (brk_maps_next (m_vmmaps m) req r)
    (maps_subtract_ranges (vm_noaccess (m_vmmaps m))
      (brk_unmaps r (vm_brk (m_vmmaps m)))) (bv_unsigned r)
  rcases Int.lt_trichotomy (r.toNat : Int) ((vm_brk (m_vmmaps m)).toNat : Int) with
    hlt | heq | hgt
  · -- SHRINK
    have hreq0 : w_is0 req = false := by
      rcases hcases with h | ⟨-, h⟩
      · rw [h] at hlt; na_omega
      · exact h
    have hrr : r = req := by
      rcases hcases with h | ⟨h, -⟩
      · rw [h] at hlt; na_omega
      · exact h
    have hbpos : 0 < ((vm_brk (m_vmmaps m)).toNat : Int) := by na_omega
    have hrn : (r.toNat : Int) = (req.toNat : Int) := by rw [hrr]
    have hrpos : 0 < (r.toNat : Int) := by
      have h := w_is0_false req hreq0
      simp only [bv_unsigned] at h
      have hge := (bv_unsigned_range_u64 req).1
      rw [hrn]
      na_omega
    have hguard : (decide (0 < ((vm_brk (m_vmmaps m)).toNat : Int)) &&
        decide ((r.toNat : Int) < ((vm_brk (m_vmmaps m)).toNat : Int))) = true := by
      rw [Bool.and_eq_true]
      exact ⟨by simpa using hbpos, by simpa using hlt⟩
    have hmaps : brk_maps_next (m_vmmaps m) req r
        = maps_subtract (vm_maps (m_vmmaps m)) (r.toNat : Int)
            ((vm_brk (m_vmmaps m)).toNat : Int) := by
      unfold brk_maps_next
      rw [ite_eq_left hguard]
    have hna : brk_unmaps r (vm_brk (m_vmmaps m))
        = brk_page_range (page_round_up_Z (r.toNat : Int))
            (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)) := by
      unfold brk_unmaps
      dsimp only
      rw [ite_eq_left hbpos]
    rw [hmaps, hna]
    have hpupos : 0 < page_round_up_Z (r.toNat : Int) := page_round_up_pos _ hrpos
    have hpub : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) ≤ two_pow_64 :=
      pu_le_two_pow _ hbrk0 hbrk1
    by_cases hcut : page_round_up_Z (r.toNat : Int)
        < page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
    · have hpr0 : 0 ≤ page_round_up_Z (r.toNat : Int) := by
        have := pu_ge (r.toNat : Int)
        na_omega
      have hpr1 : page_round_up_Z (r.toNat : Int) < two_pow_64 :=
        Int.lt_of_lt_of_le hcut hpub
      have hdiff0 : 0 ≤ page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
          - page_round_up_Z (r.toNat : Int) := by na_omega
      have hdiff1 : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
          - page_round_up_Z (r.toNat : Int) < two_pow_64 := by na_omega
      have hlo : ((BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int))).toNat : Int)
          = page_round_up_Z (r.toNat : Int) :=
        u64 _ ⟨hpr0, hpr1⟩
      have hsz : ((BitVec.ofInt 64 (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
            - page_round_up_Z (r.toNat : Int))).toNat : Int)
          = page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
            - page_round_up_Z (r.toNat : Int) :=
        u64 _ ⟨hdiff0, hdiff1⟩
      have hrange : brk_page_range (page_round_up_Z (r.toNat : Int))
            (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int))
          = [(BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int)),
              BitVec.ofInt 64 (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
                - page_round_up_Z (r.toNat : Int)))] := by
        unfold brk_page_range
        rw [ite_eq_left hcut]
      rw [hrange]
      have hranges : maps_subtract_ranges (vm_noaccess (m_vmmaps m))
            [(BitVec.ofInt 64 (page_round_up_Z (r.toNat : Int)),
              BitVec.ofInt 64 (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
                - page_round_up_Z (r.toNat : Int)))]
          = maps_subtract (vm_noaccess (m_vmmaps m)) (page_round_up_Z (r.toNat : Int))
              (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)) := by
        unfold maps_subtract_ranges
        simp only [List.foldl_cons, List.foldl_nil]
        rw [hlo, hsz]
        have : page_round_up_Z (r.toNat : Int)
            + (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)
              - page_round_up_Z (r.toNat : Int))
            = page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) := by na_omega
        rw [this]
      rw [hranges]
      refine ⟨maps_subtract_shape _ _ _ hsh (pu_aligned _) (pu_aligned _), ?_⟩
      intro a' n' x Hin Hx
      obtain ⟨a, n, Hin0, Hx0, Hc⟩ :=
        maps_subtract_bytes _ _ _ a' n' x (na_shape_fit _ hsh) Hin Hx
      exact brk_shrink_cover _ _ _ _ a n x Hfit hsh hcov hlt Hin0 Hx0 Hc
    · have hrange : brk_page_range (page_round_up_Z (r.toNat : Int))
          (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)) = [] := by
        unfold brk_page_range
        rw [ite_eq_right hcut]
      rw [hrange]
      have hranges : maps_subtract_ranges (vm_noaccess (m_vmmaps m))
          ([] : List (word × word)) = vm_noaccess (m_vmmaps m) := rfl
      rw [hranges]
      refine ⟨hsh, ?_⟩
      intro a' n' x Hin Hx
      refine brk_shrink_cover _ _ _ _ a' n' x Hfit hsh hcov hlt Hin Hx ?_
      intro hc
      na_omega
  · -- UNCHANGED: the break did not move
    have hrb : r = vm_brk (m_vmmaps m) := by
      apply BitVec.eq_of_toNat_eq
      na_omega
    rw [hrb]
    have hguard : (decide (0 < ((vm_brk (m_vmmaps m)).toNat : Int)) &&
        decide (((vm_brk (m_vmmaps m)).toNat : Int)
          < ((vm_brk (m_vmmaps m)).toNat : Int))) = false := by
      have h : decide (((vm_brk (m_vmmaps m)).toNat : Int)
          < ((vm_brk (m_vmmaps m)).toNat : Int)) = false := by
        rw [decide_eq_false_iff_not]
        na_omega
      rw [h, Bool.and_false]
    have hmaps : brk_maps_next (m_vmmaps m) req (vm_brk (m_vmmaps m))
        = vm_maps (m_vmmaps m) := by
      unfold brk_maps_next
      rw [ite_eq_right (by rw [hguard]; simp)]
      have hg : brk_grants req (vm_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) = [] := by
        unfold brk_grants brk_is_grow
        have hlt' : decide (((vm_brk (m_vmmaps m)).toNat : Int)
            < ((vm_brk (m_vmmaps m)).toNat : Int)) = false := by
          rw [decide_eq_false_iff_not]
          na_omega
        rw [hlt', Bool.and_false]
        rfl
      rw [hg, List.nil_append]
    have hna : brk_unmaps (vm_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) = [] := by
      unfold brk_unmaps brk_page_range
      dsimp only
      by_cases hbz : 0 < ((vm_brk (m_vmmaps m)).toNat : Int)
      · rw [ite_eq_left hbz]
        rw [ite_eq_right (by na_omega)]
      · rw [ite_eq_right hbz]
    rw [hmaps, hna]
    exact ⟨hsh, hcov⟩
  · -- GROW: the break moved up
    have hreq0 : w_is0 req = false := by
      rcases hcases with h | ⟨-, h⟩
      · rw [h] at hgt; na_omega
      · exact h
    have hrr : r = req := by
      rcases hcases with h | ⟨h, -⟩
      · rw [h] at hgt; na_omega
      · exact h
    -- a grow frees no page: the protected list is unchanged either way
    have hna' : maps_subtract_ranges (vm_noaccess (m_vmmaps m))
        (brk_unmaps r (vm_brk (m_vmmaps m))) = vm_noaccess (m_vmmaps m) := by
      unfold brk_unmaps
      dsimp only
      by_cases hbz : 0 < ((vm_brk (m_vmmaps m)).toNat : Int)
      · rw [ite_eq_left hbz]
        rw [show brk_page_range (page_round_up_Z (r.toNat : Int))
              (page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int)) = [] from by
          unfold brk_page_range
          rw [ite_eq_right (by
            have hp := pu_mono _ _ (by na_omega : ((vm_brk (m_vmmaps m)).toNat : Int)
              ≤ (r.toNat : Int))
            na_omega)]]
        rfl
      · rw [ite_eq_right hbz]
        rfl
    rw [hna']
    have hmaps : brk_maps_next (m_vmmaps m) req r
        = brk_grants req r (vm_brk (m_vmmaps m)) ++ vm_maps (m_vmmaps m) := by
      unfold brk_maps_next
      rw [ite_eq_right]
      intro hcon
      rw [Bool.and_eq_true] at hcon
      simp only [decide_eq_true_eq] at hcon
      na_omega
    rw [hmaps]
    by_cases hgrow : brk_is_grow req r (vm_brk (m_vmmaps m)) = true
    · have hgr : brk_grants req r (vm_brk (m_vmmaps m))
          = [(vm_brk (m_vmmaps m), r - vm_brk (m_vmmaps m))] := by
        unfold brk_grants
        rw [ite_eq_left hgrow]
      rw [hgr]
      have hsz : bv_unsigned (r - vm_brk (m_vmmaps m))
          = bv_unsigned r - bv_unsigned (vm_brk (m_vmmaps m)) := by
        have hle : vm_brk (m_vmmaps m) ≤ r := by
          rw [BitVec.le_def]
          na_omega
        have hle' : (vm_brk (m_vmmaps m)).toNat ≤ r.toNat := by na_omega
        simp only [bv_unsigned]
        rw [BitVec.toNat_sub_of_le hle, Int.natCast_sub hle']
      refine ⟨hsh, ?_⟩
      intro a n x Hin Hx
      rcases hcov a n x Hin Hx with ho | ⟨hz, ho⟩
      · exact Or.inl (owned_cons _ _ x ho)
      · by_cases hxr : x < (r.toNat : Int)
        · refine Or.inl ⟨vm_brk (m_vmmaps m), r - vm_brk (m_vmmaps m),
            List.mem_cons_self .., ?_, ?_⟩
          · na_omega
          · na_omega
        · have hz' : (r.toNat : Int) ≤ x ∧ x < page_round_up_Z (r.toNat : Int) := by
            have : r.toNat = req.toNat := by rw [hrr]
            have hp := pu_mono _ _ (by na_omega : ((vm_brk (m_vmmaps m)).toNat : Int) ≤ (r.toNat : Int))
            na_omega
          refine Or.inr ⟨hz', ?_⟩
          have hfr : page_round_down_Z x = page_round_down_Z (r.toNat : Int) :=
            (zone_floor _ x hz').1
          have hfb : page_round_down_Z x
              = page_round_down_Z ((vm_brk (m_vmmaps m)).toNat : Int) :=
            (zone_floor _ x hz).1
          rw [← hfr, hfb]
          exact owned_cons _ _ _ ho
    · have hgr : brk_grants req r (vm_brk (m_vmmaps m)) = [] := by
        unfold brk_grants
        rw [ite_eq_right hgrow]
      rw [hgr, List.nil_append]
      refine ⟨hsh, ?_⟩
      intro a n x Hin Hx
      rcases hcov a n x Hin Hx with ho | ⟨hz, ho⟩
      · exact Or.inl ho
      · exfalso
        -- no grant means the old break was 0, and no orphan slice exists then
        have hlt' : decide (((vm_brk (m_vmmaps m)).toNat : Int)
            < (r.toNat : Int)) = true := by
          rw [decide_eq_true_eq]
          na_omega
        unfold brk_is_grow at hgrow
        simp only [hreq0, Bool.not_false, Bool.true_and] at hgrow
        rw [hlt', Bool.and_true] at hgrow
        have hnb : ¬ (0 < ((vm_brk (m_vmmaps m)).toNat : Int)) := by
          intro hpos
          exact hgrow (by rw [decide_eq_true_eq]; exact hpos)
        have hb0 : ((vm_brk (m_vmmaps m)).toNat : Int) = 0 := by na_omega
        have hzgb : page_round_up_Z ((vm_brk (m_vmmaps m)).toNat : Int) = 0 := by
          rw [hb0]
          exact pu_of_aligned 0 (by unfold page_size; simp)
        rw [hzgb] at hz
        na_omega

/-- `brk`'s preservation: `Core.lean`'s `check_brk_preserves` walk, with
    `brk_model_next_na_inv` at the one accepting leaf. -/
theorem check_brk_preserves_na (req : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (H : check_brk req eff m = .CheckOk m' evs)
    (_Hwf : vm_wf (m_vmmaps m)) (Hfit : vm_fit (m_vmmaps m))
    (Hna : na_inv (m_vmmaps m)) : na_inv (m_vmmaps m') := by
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
          rw [Bool.and_eq_true] at hc
          obtain ⟨hok, _⟩ := hc
          rw [Bool.and_eq_true] at hok
          obtain ⟨hok, _⟩ := hok
          rw [vmm_brk_next]
          exact brk_model_next_na_inv m req ret hok Hfit Hna
        · simp only [hc] at H
          exact absurd H (by simp)
      | cons _ _ => exact absurd H (by simp)
    | cons _ _ => exact absurd H (by simp)
  | cons _ _ => exact absurd H (by simp)

end LinuxSem.Checks.NoaccessOwned
