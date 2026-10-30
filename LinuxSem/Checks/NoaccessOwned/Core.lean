/-
  * LinuxSem.Checks.NoaccessOwned.Core — `State.noaccess_pages_owned`,
    strengthened to something inductive.

    Not part of the trusted specification: the preservation half of the
    ledger invariant `State.noaccess_pages_owned`, which
    `Mremap.mremap_fresh_avoids_noaccess` takes as a hypothesis (the model
    does not prove placement disjoint from `vm_noaccess` from nothing, it
    takes this predicate's guarantee).

    WHY THE INVARIANT IS NOT PROVED ON ITS OWN.  `noaccess_pages_owned` is
    NOT inductive.  A state can satisfy it with the only witness of a
    protected page being a byte-granular brk grant that starts in the
    middle of that page; a later brk shrink to below that grant's base cuts
    the grant out of `vm_maps` while `Mmap.brk_unmaps` (page rounded, and
    empty for a same-page shrink) leaves the protection whole.  Such a
    state is not reachable, and what makes it unreachable is a STRONGER
    statement, `na_inv` below:

    - every protected entry is page aligned, a whole number of pages,
      nonempty, and ends inside the address space (`na_shape`); and
    - every protected byte is OWNED, byte for byte, by a live mapping —
      except the bytes of the brk orphan, the slice
      `[vm_brk, PAGE_ALIGN vm_brk)` that a shrink to a break which is not
      page aligned leaves protected, and for those the first byte of the
      break's page is owned (`na_cover`).

    `na_inv_noaccess_pages_owned` derives `noaccess_pages_owned` from it.
    `na_inv` is preserved together with `VmMapsDisjoint.vm_wf` (the base of
    a `map_has` hit names one entry, so `munmap` and `mremap` remove
    exactly the entry they matched) and `MapsFit.vm_fit` (a cut leaves
    remnants that re-enter `word` losslessly); `sys_inv` is the three
    together, `init_model_sys_inv` the base case,
    `check_syscall_preserves_sys_inv` / `syscall_spec_preserves_sys_inv`
    the system-call step, and `sstep_preserves_sys_inv` /
    `star_preserves_sys_inv` / `star_cfg_preserves_sys_inv` the whole run.

    THIS MODULE holds the definitions, the page arithmetic, the `owned`
    algebra, the shape lemmas each writer's leaf applies, and the two
    re-recordings `munmap` and `mremap` perform (`na_inv_munmap`,
    `na_inv_mremap`) — plus `na_inv_noaccess_pages_owned`, which is what a
    consumer actually cites.  The brk case is `NoaccessOwned/Brk.lean`, the
    other four writers `NoaccessOwned/Writers.lean`, the `checked_table`
    enumeration `NoaccessOwned/Arms.lean`, and the run-level lifts
    `NoaccessOwned/Run.lean`; `Checks/NoaccessOwned.lean` imports the five.
-/

import LinuxSem.Checks.MapsFit
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
open LinuxSem.Checks.VmMapsDisjoint
open LinuxSem.Checks.MapsFit

namespace LinuxSem.Checks.NoaccessOwned

open LinuxSem.Common.RocqSpelling

/-! ## The strengthened invariant -/

/-- Byte `x` lies inside some entry of `maps`. -/
def owned (maps : List (word × word)) (x : Int) : Prop :=
  ∃ b s, (b, s) ∈ maps ∧ bv_unsigned b ≤ x ∧ x < bv_unsigned b + bv_unsigned s

/-- Every protected entry is page aligned, a whole number of pages,
    nonempty, and ends inside the address space. -/
def na_shape (na : List (word × word)) : Prop :=
  ∀ a n, (a, n) ∈ na →
    bv_unsigned a % page_size = 0 ∧ bv_unsigned n % page_size = 0 ∧
      0 < bv_unsigned n ∧ bv_unsigned a + bv_unsigned n ≤ two_pow_64

/-- Every protected byte is owned — except the brk orphan slice
    `[brk, PAGE_ALIGN brk)`, for which the first byte of the break's page
    is owned.  `brk` is the break as an `Int`, so the slice's upper end is
    representable even when the break is at the very top of the space. -/
def na_cover (maps na : List (word × word)) (brk : Int) : Prop :=
  ∀ a n x, (a, n) ∈ na →
    bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned n →
    owned maps x ∨ ((brk ≤ x ∧ x < page_round_up_Z brk) ∧
      owned maps (page_round_down_Z brk))

def na_inv' (maps na : List (word × word)) (brk : Int) : Prop :=
  na_shape na ∧ na_cover maps na brk

def na_inv (h : VmMaps) : Prop :=
  na_inv' (vm_maps h) (vm_noaccess h) (bv_unsigned (vm_brk h))

/-- The whole-ledger invariant: the page-granular disjointness
    (`VmMapsDisjoint.vm_wf`), the end-inside-the-space bound
    (`MapsFit.vm_fit`) and the protected-byte cover above. -/
def sys_inv (h : VmMaps) : Prop := vm_wf h ∧ vm_fit h ∧ na_inv h

/-! ## Page arithmetic

    The port keeps these as named lemmas rather than an `omega`-only
    prelude: every one of them is used at a writer's leaf, and the two that
    talk about a page-aligned WINDOW (`pd_eq_of_window`, `zone_same_page`)
    are what turns "this byte is inside a protected range" into "the whole
    page it is on is" — the step that survives the brk orphan.

    The original's `pgf` tactic (a `Z.div_mod` + `Z.mod_pos_bound` pair
    handed to `lia`) has no Lean counterpart; here every division fact
    comes from `Int.mul_ediv_add_emod` plus the two `Int.emod` bounds, which
    is what `State.page_round_down_Z_within` already does. -/

/-- A page-aligned value is its own page start. -/
theorem pd_of_aligned (z : Int) (H : z % page_size = 0) : page_round_down_Z z = z := by
  unfold page_round_down_Z page_size at *
  have h := Int.mul_ediv_add_emod z 4096
  omega

/-- A rounded-down value is page aligned. -/
theorem pd_aligned (z : Int) : page_round_down_Z z % page_size = 0 := by
  unfold page_round_down_Z page_size
  exact Int.emod_eq_zero_of_dvd ⟨z / 4096, by rw [Int.mul_comm]⟩

/-- A page-rounded-up value is page aligned. -/
theorem pu_aligned (z : Int) : page_round_up_Z z % page_size = 0 := by
  unfold page_round_up_Z page_size
  exact Int.emod_eq_zero_of_dvd ⟨(z + 4096 - 1) / 4096, by rw [Int.mul_comm]⟩

/-- …and is at or above its argument. -/
theorem pu_ge (z : Int) : z ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  have h := Int.mul_ediv_add_emod (z + 4096 - 1) 4096
  have h0 := Int.emod_nonneg (z + 4096 - 1) (by omega : (4096 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos (z + 4096 - 1) (by omega : (0 : Int) < 4096)
  omega

/-- …and is inside the page that follows it. -/
theorem pu_lt (z : Int) : page_round_up_Z z < z + page_size := by
  unfold page_round_up_Z page_size
  have h := Int.mul_ediv_add_emod (z + 4096 - 1) 4096
  have h0 := Int.emod_nonneg (z + 4096 - 1) (by omega : (4096 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos (z + 4096 - 1) (by omega : (0 : Int) < 4096)
  omega

/-- Rounding down never exceeds its argument. -/
theorem pd_le (z : Int) : page_round_down_Z z ≤ z := by
  unfold page_round_down_Z page_size
  have h := Int.mul_ediv_add_emod z 4096
  have h0 := Int.emod_nonneg z (by omega : (4096 : Int) ≠ 0)
  omega

/-- …and the next page boundary is above it. -/
theorem pd_page (z : Int) : z < page_round_down_Z z + page_size := by
  unfold page_round_down_Z page_size
  have h := Int.mul_ediv_add_emod z 4096
  have h1 := Int.emod_lt_of_pos z (by omega : (0 : Int) < 4096)
  omega

/-- Rounding up never reaches a page beyond the page start: it is the page
    start itself, or the next one. -/
theorem pu_le_pd (z : Int) : page_round_up_Z z ≤ page_round_down_Z z + page_size := by
  unfold page_round_up_Z page_round_down_Z page_size
  have hb := Int.mul_ediv_add_emod z 4096
  have hu := Int.mul_ediv_add_emod (z + 4095) 4096
  have h0 := Int.emod_nonneg z (by omega : (4096 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by omega : (0 : Int) < 4096)
  have h2 := Int.emod_nonneg (z + 4095) (by omega : (4096 : Int) ≠ 0)
  have h3 := Int.emod_lt_of_pos (z + 4095) (by omega : (0 : Int) < 4096)
  omega

/-- THE WINDOW LEMMA: a page-aligned `d` that `x` sits at or above, within
    one page of, is `x`'s page start. -/
theorem pd_eq_of_window (d x : Int) (Hd : d % page_size = 0)
    (H1 : d ≤ x) (H2 : x < d + page_size) : page_round_down_Z x = d := by
  unfold page_round_down_Z page_size at *
  have hx := Int.mul_ediv_add_emod x 4096
  have hd := Int.mul_ediv_add_emod d 4096
  have h0 := Int.emod_nonneg x (by omega : (4096 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos x (by omega : (0 : Int) < 4096)
  omega

/-- Rounding up a page-aligned value changes nothing. -/
theorem pu_of_aligned (z : Int) (H : z % page_size = 0) : page_round_up_Z z = z := by
  have hpual := pu_aligned z
  have h1 : page_round_down_Z (page_round_up_Z z) = page_round_up_Z z :=
    pd_of_aligned _ hpual
  have h2 : page_round_down_Z (page_round_up_Z z) = z :=
    pd_eq_of_window z (page_round_up_Z z) H (pu_ge z) (pu_lt z)
  rw [← h1, h2]

/-- A byte in the orphan slice of a break is on the break's page, and that
    page starts strictly below the break (so the slice is nonempty). -/
theorem zone_floor (brk x : Int) (Hx : brk ≤ x ∧ x < page_round_up_Z brk) :
    page_round_down_Z x = page_round_down_Z brk ∧ page_round_down_Z brk < brk := by
  have hd : page_round_down_Z brk % page_size = 0 := pd_aligned brk
  have h1 : page_round_down_Z brk ≤ x := by
    have := pd_le brk
    omega
  have h2 : x < page_round_down_Z brk + page_size := by
    have := pu_le_pd brk
    omega
  have hx : page_round_down_Z x = page_round_down_Z brk :=
    pd_eq_of_window _ x hd h1 h2
  refine ⟨hx, ?_⟩
  by_cases h : page_round_down_Z brk < brk
  · exact h
  · exfalso
    have heq : page_round_down_Z brk = brk :=
      Int.le_antisymm (pd_le brk) (Int.not_lt.mp h)
    have hb : brk % page_size = 0 := by rw [← heq]; exact pd_aligned brk
    rw [pu_of_aligned brk hb] at Hx
    omega

/-- A page-aligned window holding the first byte of the break's page holds
    every byte of the orphan slice. -/
theorem zone_same_page (lo hi brk x : Int) (Hlo : lo % page_size = 0)
    (Hhi : hi % page_size = 0) (Hx : brk ≤ x ∧ x < page_round_up_Z brk)
    (HP : lo ≤ page_round_down_Z brk ∧ page_round_down_Z brk < hi) :
    lo ≤ x ∧ x < hi := by
  have hfloor := (zone_floor brk x Hx).1
  have hwin := page_round_down_Z_within lo hi (page_round_down_Z brk) Hlo Hhi HP
  have hfix : page_round_down_Z (page_round_down_Z brk) = page_round_down_Z brk :=
    pd_of_aligned _ (pd_aligned brk)
  rw [hfix] at hwin
  have h3 : page_round_down_Z x ≤ x := pd_le x
  have h4 : x < page_round_down_Z x + page_size := pd_page x
  exact ⟨by omega, by omega⟩

/-- Two page-aligned values add to a page-aligned value. -/
theorem aligned_add (x y : Int) (Hx : x % page_size = 0) (Hy : y % page_size = 0) :
    (x + y) % page_size = 0 := by
  unfold page_size at *
  rw [Int.add_emod, Hx, Hy]
  simp


/-! ## `owned` under the ways a writer builds `vm_maps` -/

theorem owned_cons (maps : List (word × word)) (e : word × word) (x : Int)
    (H : owned maps x) : owned (e :: maps) x := by
  obtain ⟨b, s, hmem, h1, h2⟩ := H
  exact ⟨b, s, List.mem_cons_of_mem _ hmem, h1, h2⟩

theorem owned_app_l (l1 l2 : List (word × word)) (x : Int) (H : owned l1 x) :
    owned (l1 ++ l2) x := by
  obtain ⟨b, s, hmem, h1, h2⟩ := H
  exact ⟨b, s, List.mem_append_left _ hmem, h1, h2⟩

theorem owned_app_r (l1 l2 : List (word × word)) (x : Int) (H : owned l2 x) :
    owned (l1 ++ l2) x := by
  obtain ⟨b, s, hmem, h1, h2⟩ := H
  exact ⟨b, s, List.mem_append_right _ hmem, h1, h2⟩

/-- A byte outside a cut keeps its owner's remnant: below `lo` the entry's
    own base with a shrunken size, at or above `hi` the shifted base with
    the shifted size — and in both cases the end is the entry's own end. -/
theorem iv_subtract_owned (a s : word) (lo hi x : Int)
    (Hf : bv_unsigned a + bv_unsigned s ≤ two_pow_64)
    (Hx : bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned s)
    (Hc : ¬ (lo ≤ x ∧ x < hi)) : owned (iv_subtract a s lo hi) x := by
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 s
  simp only [bv_unsigned, two_pow_64] at Hf Hx ha hs
  by_cases hlo : x < lo
  · have hfires : (a.toNat : Int) < lo := by omega
    have hpos : 0 ≤ lo - (a.toNat : Int) := by omega
    have hz : ((BitVec.ofInt 64 (min (s.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
        = min (s.toNat : Int) (lo - (a.toNat : Int)) :=
      u64_min_eq _ _ hs.1 hs.2 hpos
    refine ⟨a, BitVec.ofInt 64 (min (s.toNat : Int) (lo - (a.toNat : Int))),
      ?_, ?_, ?_⟩
    · unfold iv_subtract
      dsimp only
      rw [ite_eq_left hfires]
      exact List.mem_append_left _ (by simp)
    · simpa only [bv_unsigned] using Hx.1
    · have hm : min (s.toNat : Int) (lo - (a.toNat : Int)) ≤ (s.toNat : Int) :=
        Int.min_le_left _ _
      simp only [bv_unsigned]
      omega
  · have hxlo : lo ≤ x := Int.not_lt.mp hlo
    have hhi : hi ≤ x := by omega
    have hfires : hi < (a.toNat : Int) + (s.toNat : Int) := by omega
    have hmax : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
        = max (a.toNat : Int) hi :=
      u64_max_eq _ _ ha.1 ha.2 (by omega)
    have hsz : ((BitVec.ofInt 64
          ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi)).toNat : Int)
        = (a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi := by
      apply u64_sub_eq
      · rw [Int.max_le]
        exact ⟨by omega, by omega⟩
      · have := Int.le_max_left (a.toNat : Int) hi
        omega
    refine ⟨BitVec.ofInt 64 (max (a.toNat : Int) hi),
      BitVec.ofInt 64 ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi),
      ?_, ?_, ?_⟩
    · unfold iv_subtract
      dsimp only
      by_cases h1 : (a.toNat : Int) < lo
      · rw [ite_eq_left h1, ite_eq_left hfires]
        exact List.mem_append_right _ (by simp)
      · rw [ite_eq_right h1, ite_eq_left hfires]
        exact List.mem_append_right _ (by simp)
    · have hm : max (a.toNat : Int) hi ≤ x := by omega
      simp only [bv_unsigned]
      omega
    · simp only [bv_unsigned]
      omega

theorem owned_subtract (maps : List (word × word)) (lo hi : Int) (x : Int)
    (Hf : maps_fit maps) (Ho : owned maps x) (Hc : ¬ (lo ≤ x ∧ x < hi)) :
    owned (maps_subtract maps lo hi) x := by
  induction maps with
  | nil =>
    obtain ⟨b, s, hmem, _, _⟩ := Ho
    exact absurd hmem (by simp)
  | cons hd r ih =>
    obtain ⟨a, s⟩ := hd
    obtain ⟨b, t, hmem, h1, h2⟩ := Ho
    simp only [maps_subtract]
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      rw [heq.1] at h1 h2
      rw [heq.2] at h2
      exact owned_app_l _ _ x
        (iv_subtract_owned a s lo hi x (Hf a s (by simp)) ⟨h1, h2⟩ Hc)
    · exact owned_app_r _ _ x
        (ih (fun c u h => Hf c u (by simp [h])) ⟨b, t, hmem, h1, h2⟩)

/-- Removing the entries based at `addr` keeps every byte some OTHER entry
    owns; when the base names one entry, that is every byte outside it. -/
theorem owned_map_remove (maps : List (word × word)) (addr n : word) (x : Int)
    (Hu : ∀ s, (addr, s) ∈ maps → s = n) (Ho : owned maps x)
    (Hc : ¬ (bv_unsigned addr ≤ x ∧ x < bv_unsigned addr + bv_unsigned n)) :
    owned (map_remove maps addr) x := by
  obtain ⟨b, s, hmem, h1, h2⟩ := Ho
  by_cases hb : (b == addr) = true
  · have hba : b = addr := by simpa using hb
    rw [hba] at hmem h1 h2
    rw [Hu s hmem] at h2
    exact absurd ⟨h1, h2⟩ Hc
  · have hb' : (b == addr) = false := by
      cases h : (b == addr)
      · rfl
      · exact absurd h hb
    refine ⟨b, s, ?_, h1, h2⟩
    unfold map_remove
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [hb']
    rfl

/-- At a page-aligned base, a `map_has` hit pins the entry's SIZE: no two
    entries with that base disagree about it.  This is `base_entry_unique`
    read one size at a time. -/
theorem map_has_unique (maps : List (word × word)) (addr n : word)
    (Hwf : maps_wf maps) (Ha : bv_unsigned addr % page_size = 0)
    (Hhas : map_has maps addr n = true) (s : word) (Hin : (addr, s) ∈ maps) :
    s = n := by
  have Hu := base_entry_unique maps addr n Hwf Ha Hhas
  have hf : (addr, s) ∈ List.filter (fun q => bv_eqb q.1 addr) maps := by
    rw [List.mem_filter]
    exact ⟨Hin, by simp [bv_eqb]⟩
  rw [Hu] at hf
  rcases List.mem_cons.mp hf with h | h
  · have : s = n := by simpa using h
    exact this
  · exact absurd h (by simp)

/-- A `map_contains` hit owns every byte of the contained range. -/
theorem map_contains_owned (maps : List (word × word)) (lo n : word) (x : Int)
    (H : map_contains maps lo n = true)
    (Hx : (lo.toNat : Int) ≤ x ∧ x < (lo.toNat : Int) + (n.toNat : Int)) :
    owned maps x := by
  unfold map_contains at H
  rw [List.any_eq_true] at H
  obtain ⟨⟨b, s⟩, hmem, hb⟩ := H
  dsimp only at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨b, s, hmem, ?_, ?_⟩
  · simp only [bv_unsigned]
    omega
  · simp only [bv_unsigned]
    omega


/-! ## The protected list under a cut

    Two more alignment helpers, then the four facts a cut leaf needs: a
    remnant's bytes come from its entry, a remnant keeps the shape, and
    `na_shape` alone already gives `maps_fit`. -/

/-- The pointwise minimum of two page-aligned values is page aligned. -/
theorem aligned_min (x y : Int) (Hx : x % page_size = 0) (Hy : y % page_size = 0) :
    min x y % page_size = 0 := by
  rcases Int.le_total x y with h | h
  · rw [Int.min_eq_left h]; exact Hx
  · rw [Int.min_eq_right h]; exact Hy

/-- …and so is the maximum. -/
theorem aligned_max (x y : Int) (Hx : x % page_size = 0) (Hy : y % page_size = 0) :
    max x y % page_size = 0 := by
  rcases Int.le_total x y with h | h
  · rw [Int.max_eq_right h]; exact Hy
  · rw [Int.max_eq_left h]; exact Hx

/-- …and so is the difference. -/
theorem aligned_sub (x y : Int) (Hx : x % page_size = 0) (Hy : y % page_size = 0) :
    (x - y) % page_size = 0 := by
  have hx := Int.mul_ediv_add_emod x page_size
  have hy := Int.mul_ediv_add_emod y page_size
  have hxe : x = page_size * (x / page_size) := by omega
  have hye : y = page_size * (y / page_size) := by omega
  rw [hxe, hye, ← Int.mul_sub]
  exact Int.emod_eq_zero_of_dvd ⟨_, rfl⟩

/-- `na_shape` is stronger than `maps_fit`: the fourth conjunct is it. -/
theorem na_shape_fit (na : List (word × word)) (H : na_shape na) : maps_fit na :=
  fun a n Hin => (H a n Hin).2.2.2

/-- Every byte a remnant owns came from its entry, and lies outside the
    cut: the remnants partition the entry around `[lo, hi)`. -/
theorem iv_subtract_bytes (a s : word) (lo hi : Int) (a' s' : word) (x : Int)
    (Hf : bv_unsigned a + bv_unsigned s ≤ two_pow_64)
    (Hin : (a', s') ∈ iv_subtract a s lo hi)
    (Hx : bv_unsigned a' ≤ x ∧ x < bv_unsigned a' + bv_unsigned s') :
    (bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned s) ∧ ¬ (lo ≤ x ∧ x < hi) := by
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 s
  simp only [bv_unsigned, two_pow_64] at Hf Hx ha hs ⊢
  unfold iv_subtract at Hin
  dsimp only at Hin
  rcases List.mem_append.mp Hin with hmem | hmem
  · by_cases h1 : (a.toNat : Int) < lo
    · rw [ite_eq_left h1, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      have hzL : ((BitVec.ofInt 64 (min (s.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
          = min (s.toNat : Int) (lo - (a.toNat : Int)) :=
        u64_min_eq _ _ hs.1 hs.2 (by omega)
      rw [hmem.1] at Hx
      rw [hmem.2, hzL] at Hx
      refine ⟨⟨Hx.1, ?_⟩, ?_⟩
      · have := Int.min_le_left (s.toNat : Int) (lo - (a.toNat : Int))
        omega
      · intro hc
        have := Int.min_le_right (s.toNat : Int) (lo - (a.toNat : Int))
        omega
    · rw [ite_eq_right h1] at hmem
      exact absurd hmem (by simp)
  · by_cases h2 : hi < (a.toNat : Int) + (s.toNat : Int)
    · rw [ite_eq_left h2, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      have hzR : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
          = max (a.toNat : Int) hi :=
        u64_max_eq _ _ ha.1 ha.2 (by omega)
      have hzRS : ((BitVec.ofInt 64
            ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi)).toNat : Int)
          = (a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi := by
        apply u64_sub_eq
        · rw [Int.max_le]
          exact ⟨by omega, by omega⟩
        · have := Int.le_max_left (a.toNat : Int) hi
          omega
      rw [hmem.1, hzR] at Hx
      rw [hmem.2, hzRS] at Hx
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := Int.le_max_right (a.toNat : Int) hi
        omega
      · omega
      · intro hc
        omega
    · rw [ite_eq_right h2] at hmem
      exact absurd hmem (by simp)

/-- The same fact for a whole list: a remnant's byte was owned by some
    entry of the original list, and lies outside the cut. -/
theorem maps_subtract_bytes (l : List (word × word)) (lo hi : Int)
    (a' s' : word) (x : Int) (Hf : maps_fit l)
    (Hin : (a', s') ∈ maps_subtract l lo hi)
    (Hx : bv_unsigned a' ≤ x ∧ x < bv_unsigned a' + bv_unsigned s') :
    ∃ a s, (a, s) ∈ l ∧ (bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned s) ∧
      ¬ (lo ≤ x ∧ x < hi) := by
  induction l with
  | nil => exact absurd Hin (by simp [maps_subtract])
  | cons hd r ih =>
    obtain ⟨a, s⟩ := hd
    simp only [maps_subtract] at Hin
    rcases List.mem_append.mp Hin with hmem | hmem
    · obtain ⟨hb, hc⟩ :=
        iv_subtract_bytes a s lo hi a' s' x (Hf a s (by simp)) hmem Hx
      exact ⟨a, s, by simp, hb, hc⟩
    · obtain ⟨b, t, hmem', hb, hc⟩ :=
        ih (fun c u h => Hf c u (by simp [h])) hmem
      exact ⟨b, t, by simp [hmem'], hb, hc⟩

/-- A cut leaves the list's shape alone: each remnant of an entry is page
    aligned, a whole number of pages, nonempty, and ends where its entry
    did. -/
theorem iv_subtract_shape (a s : word) (lo hi : Int) (a' s' : word)
    (Ha : bv_unsigned a % page_size = 0) (Hs : bv_unsigned s % page_size = 0)
    (Hpos : 0 < bv_unsigned s) (Hf : bv_unsigned a + bv_unsigned s ≤ two_pow_64)
    (Hlo : lo % page_size = 0) (Hhi : hi % page_size = 0)
    (Hin : (a', s') ∈ iv_subtract a s lo hi) :
    bv_unsigned a' % page_size = 0 ∧ bv_unsigned s' % page_size = 0 ∧
      0 < bv_unsigned s' ∧ bv_unsigned a' + bv_unsigned s' ≤ two_pow_64 := by
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 s
  simp only [bv_unsigned, two_pow_64, page_size] at Ha Hs Hpos Hf Hlo Hhi ha hs ⊢
  unfold iv_subtract at Hin
  dsimp only at Hin
  rcases List.mem_append.mp Hin with hmem | hmem
  · by_cases h1 : (a.toNat : Int) < lo
    · rw [ite_eq_left h1, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      have hla : (lo - (a.toNat : Int)) % 4096 = 0 := aligned_sub _ _ Hlo Ha
      have hzL : ((BitVec.ofInt 64 (min (s.toNat : Int) (lo - (a.toNat : Int)))).toNat : Int)
          = min (s.toNat : Int) (lo - (a.toNat : Int)) :=
        u64_min_eq _ _ hs.1 hs.2 (by omega)
      rw [hmem.1, hmem.2, hzL]
      have hmin : min (s.toNat : Int) (lo - (a.toNat : Int)) % 4096 = 0 :=
        aligned_min _ _ Hs hla
      have hp : 0 < min (s.toNat : Int) (lo - (a.toNat : Int)) := by
        have h1' := Int.min_le_left (s.toNat : Int) (lo - (a.toNat : Int))
        have h2' := Int.min_le_right (s.toNat : Int) (lo - (a.toNat : Int))
        omega
      have he : (a.toNat : Int) + min (s.toNat : Int) (lo - (a.toNat : Int)) ≤ 2 ^ 64 := by
        have := Int.min_le_left (s.toNat : Int) (lo - (a.toNat : Int))
        omega
      exact ⟨Ha, hmin, hp, he⟩
    · rw [ite_eq_right h1] at hmem
      exact absurd hmem (by simp)
  · by_cases h2 : hi < (a.toNat : Int) + (s.toNat : Int)
    · rw [ite_eq_left h2, List.mem_singleton] at hmem
      simp only [Prod.mk.injEq] at hmem
      have hzR : ((BitVec.ofInt 64 (max (a.toNat : Int) hi)).toNat : Int)
          = max (a.toNat : Int) hi :=
        u64_max_eq _ _ ha.1 ha.2 (by omega)
      have hzRS : ((BitVec.ofInt 64
            ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi)).toNat : Int)
          = (a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi := by
        apply u64_sub_eq
        · rw [Int.max_le]
          exact ⟨by omega, by omega⟩
        · have := Int.le_max_left (a.toNat : Int) hi
          omega
      rw [hmem.1, hmem.2, hzR, hzRS]
      have hsum : ((a.toNat : Int) + (s.toNat : Int)) % 4096 = 0 := aligned_add _ _ Ha Hs
      have hmax : max (a.toNat : Int) hi % 4096 = 0 := aligned_max _ _ Ha Hhi
      have hsub : ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi) % 4096 = 0 :=
        aligned_sub _ _ hsum hmax
      have hp : 0 < (a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi := by
        have := Int.le_max_left (a.toNat : Int) hi
        omega
      have he : max (a.toNat : Int) hi
          + ((a.toNat : Int) + (s.toNat : Int) - max (a.toNat : Int) hi) ≤ 2 ^ 64 := by
        omega
      exact ⟨hmax, hsub, hp, he⟩
    · rw [ite_eq_right h2] at hmem
      exact absurd hmem (by simp)

/-- A cut of a shaped list keeps its shape. -/
theorem maps_subtract_shape (na : List (word × word)) (lo hi : Int)
    (Hsh : na_shape na) (Hlo : lo % page_size = 0) (Hhi : hi % page_size = 0) :
    na_shape (maps_subtract na lo hi) := by
  intro b t Hin
  induction na with
  | nil => exact absurd Hin (by simp [maps_subtract])
  | cons hd r ih =>
    obtain ⟨a, s⟩ := hd
    obtain ⟨Ha, Hs, Hpos, Hf⟩ := Hsh a s (by simp)
    have Hr : na_shape r := fun c u h => Hsh c u (by simp [h])
    simp only [maps_subtract] at Hin
    rcases List.mem_append.mp Hin with hmem | hmem
    · exact iv_subtract_shape a s lo hi b t Ha Hs Hpos Hf Hlo Hhi hmem
    · exact ih Hr hmem


/-! ## `na_inv'` under each shape a writer's ledger takes

    Six shapes cover the nine writers: a grant that adds no protection
    (`na_inv_mono`/`na_inv_cons_maps`), a page-aligned cut of the
    protected list alone (`mprotect`, the contained `MAP_FIXED`), the same
    cut of both lists (the destructive `MAP_FIXED` failure, the cut half of
    a spanning `MAP_FIXED`), a request newly owned and newly protected
    (the `PROT_NONE` grants), a request newly protected whose bytes are
    already owned (the contained `PROT_NONE` `MAP_FIXED`), and the two
    re-recordings `munmap` and `mremap` do. -/

theorem na_inv_mono (maps maps' na : List (word × word)) (brk : Int)
    (Hm : ∀ x, owned maps x → owned maps' x) (H : na_inv' maps na brk) :
    na_inv' maps' na brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  refine ⟨Hsh, ?_⟩
  intro a n x Hin Hx
  rcases Hcov a n x Hin Hx with ho | ⟨hz, ho⟩
  · exact Or.inl (Hm x ho)
  · exact Or.inr ⟨hz, Hm _ ho⟩

theorem na_inv_cons_maps (maps na : List (word × word)) (brk : Int) (e : word × word)
    (H : na_inv' maps na brk) : na_inv' (e :: maps) na brk :=
  na_inv_mono _ _ _ _ (fun x => owned_cons maps e x) H

/-- A page-aligned cut of the protected list alone: `mprotect` and the
    contained rw `MAP_FIXED`. -/
theorem na_inv_cut_na (maps na : List (word × word)) (brk : Int) (lo hi : Int)
    (Hlo : lo % page_size = 0) (Hhi : hi % page_size = 0) (H : na_inv' maps na brk) :
    na_inv' maps (maps_subtract na lo hi) brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  refine ⟨maps_subtract_shape na lo hi Hsh Hlo Hhi, ?_⟩
  intro a' n' x Hin Hx
  obtain ⟨a, n, Hin0, Hx0, _⟩ :=
    maps_subtract_bytes na lo hi a' n' x (na_shape_fit _ Hsh) Hin Hx
  exact Hcov a n x Hin0 Hx0

/-- The same page-aligned cut of both lists: the destructive `MAP_FIXED`
    failure and the cut half of a spanning `MAP_FIXED`.  The orphan
    disjunct survives because `zone_same_page` carries a byte of the
    break's page with the page: the cut is page aligned, so it cannot take
    part of a page. -/
theorem na_inv_cut_both (maps na : List (word × word)) (brk : Int) (lo hi : Int)
    (Hmf : maps_fit maps) (Hlo : lo % page_size = 0) (Hhi : hi % page_size = 0)
    (H : na_inv' maps na brk) :
    na_inv' (maps_subtract maps lo hi) (maps_subtract na lo hi) brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  refine ⟨maps_subtract_shape na lo hi Hsh Hlo Hhi, ?_⟩
  intro a' n' x Hin Hx
  obtain ⟨a, n, Hin0, Hx0, Hcut⟩ :=
    maps_subtract_bytes na lo hi a' n' x (na_shape_fit _ Hsh) Hin Hx
  rcases Hcov a n x Hin0 Hx0 with ho | ⟨hz, ho⟩
  · exact Or.inl (owned_subtract maps lo hi x Hmf ho Hcut)
  · exact Or.inr ⟨hz, owned_subtract maps lo hi _ Hmf ho (by
      intro hp
      exact Hcut (zone_same_page _ _ brk x Hlo Hhi hz hp))⟩

/-- A request newly owned and newly protected: the `PROT_NONE` grants. -/
theorem na_inv_cons_both (maps na : List (word × word)) (brk : Int) (a n : word)
    (Ha : bv_unsigned a % page_size = 0) (Hn : bv_unsigned n % page_size = 0)
    (Hpos : 0 < bv_unsigned n) (Hf : bv_unsigned a + bv_unsigned n ≤ two_pow_64)
    (H : na_inv' maps na brk) : na_inv' ((a, n) :: maps) ((a, n) :: na) brk := by
  obtain ⟨Hsh, Hcov⟩ := na_inv_cons_maps maps na brk (a, n) H
  refine ⟨?_, ?_⟩
  · intro b s hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · rw [Prod.mk.injEq] at heq
      rw [heq.1, heq.2]
      exact ⟨Ha, Hn, Hpos, Hf⟩
    · exact Hsh b s hmem
  · intro b s x hmem hx
    rcases List.mem_cons.mp hmem with heq | hmem
    · rw [Prod.mk.injEq] at heq
      rw [heq.1, heq.2] at hx
      exact Or.inl ⟨a, n, List.mem_cons_self .., hx.1, hx.2⟩
    · exact Hcov b s x hmem hx

/-- A request newly protected whose every byte is already owned: the
    contained `PROT_NONE` `MAP_FIXED`. -/
theorem na_inv_add_owned (maps na : List (word × word)) (brk : Int) (a n : word)
    (Ha : bv_unsigned a % page_size = 0) (Hn : bv_unsigned n % page_size = 0)
    (Hpos : 0 < bv_unsigned n) (Hf : bv_unsigned a + bv_unsigned n ≤ two_pow_64)
    (Hown : ∀ x, (bv_unsigned a ≤ x ∧ x < bv_unsigned a + bv_unsigned n) → owned maps x)
    (H : na_inv' maps na brk) : na_inv' maps ((a, n) :: na) brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  refine ⟨?_, ?_⟩
  · intro b s hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · rw [Prod.mk.injEq] at heq
      rw [heq.1, heq.2]
      exact ⟨Ha, Hn, Hpos, Hf⟩
    · exact Hsh b s hmem
  · intro b s x hmem hx
    rcases List.mem_cons.mp hmem with heq | hmem
    · rw [Prod.mk.injEq] at heq
      rw [heq.1, heq.2] at hx
      exact Or.inl (Hown x hx)
    · exact Hcov b s x hmem hx

/-- `munmap` of the whole mapping a page-aligned base names: the entry is
    dropped, and so is the protected range it spanned.  `map_has_unique` is
    what makes `map_remove`'s base-only removal and `map_has`'s
    `(base, size)` test name the same mapping. -/
theorem na_inv_munmap (maps na : List (word × word)) (brk : Int) (addr n : word)
    (Hwf : maps_wf maps) (Hhas : map_has maps addr n = true)
    (Ha : bv_unsigned addr % page_size = 0) (Hn : bv_unsigned n % page_size = 0)
    (H : na_inv' maps na brk) :
    na_inv' (map_remove maps addr)
      (maps_subtract na (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  have Hu := map_has_unique maps addr n Hwf Ha Hhas
  have Hhi : (bv_unsigned addr + bv_unsigned n) % page_size = 0 := aligned_add _ _ Ha Hn
  refine ⟨maps_subtract_shape na _ _ Hsh Ha Hhi, ?_⟩
  intro a' n' x Hin Hx
  obtain ⟨a, nn, Hin0, Hx0, Hcut⟩ :=
    maps_subtract_bytes na _ _ a' n' x (na_shape_fit _ Hsh) Hin Hx
  rcases Hcov a nn x Hin0 Hx0 with ho | ⟨hz, ho⟩
  · exact Or.inl (owned_map_remove maps addr n x Hu ho Hcut)
  · exact Or.inr ⟨hz, owned_map_remove maps addr n _ Hu ho (by
      intro hp
      exact Hcut (zone_same_page _ _ brk x Ha Hhi hz hp))⟩

/-- `mremap` re-records its source, which no protected byte meets:
    `region_free` puts the source OUTSIDE the protected list, so the
    re-recorded entry and the filtered ledger cover the same bytes. -/
theorem na_inv_mremap (maps na : List (word × word)) (brk : Int)
    (old old_n d k : word) (Hwf : maps_wf maps) (Hhas : map_has maps old old_n = true)
    (Ha : bv_unsigned old % page_size = 0) (Hn : bv_unsigned old_n % page_size = 0)
    (Hfree : region_free na old old_n = true) (H : na_inv' maps na brk) :
    na_inv' ((d, k) :: map_remove maps old) na brk := by
  obtain ⟨Hsh, Hcov⟩ := H
  have Hu := map_has_unique maps old old_n Hwf Ha Hhas
  have Hhi : (bv_unsigned old + bv_unsigned old_n) % page_size = 0 :=
    aligned_add _ _ Ha Hn
  refine ⟨Hsh, ?_⟩
  intro a n x Hin Hx
  have Hxs : ¬ (bv_unsigned old ≤ x ∧ x < bv_unsigned old + bv_unsigned old_n) := by
    intro hxs
    have hno := region_free_In na old old_n a n Hfree Hin
    unfold iv_overlap at hno
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hno
    simp only [bv_unsigned] at Hx hxs
    rcases hno with h | h
    · omega
    · omega
  rcases Hcov a n x Hin Hx with ho | ⟨hz, ho⟩
  · exact Or.inl (owned_cons _ _ x (owned_map_remove maps old old_n x Hu ho Hxs))
  · exact Or.inr ⟨hz, owned_cons _ _ _ (owned_map_remove maps old old_n _ Hu ho (by
      intro hp
      exact Hxs (zone_same_page _ _ brk x Ha Hhi hz hp)))⟩

/-! ## What the invariant is for -/

/-- `na_inv` gives `State.noaccess_pages_owned`: each protected entry is
    nonempty, and every protected byte's PAGE is met by a live mapping —
    for an ordinary byte because the owner of the byte meets the page, for
    an orphan byte because the owner of the break's page start does. -/
theorem na_inv_noaccess_pages_owned (h : VmMaps) (H : na_inv h) :
    noaccess_pages_owned h := by
  unfold na_inv at H
  obtain ⟨Hsh, Hcov⟩ := H
  have hps : (0 : Int) < page_size := by unfold page_size; omega
  intro a n Hin
  obtain ⟨-, -, Hpos, -⟩ := Hsh a n Hin
  simp only [bv_unsigned] at Hpos ⊢
  refine ⟨Hpos, ?_⟩
  intro x Hx
  rcases Hcov a n x Hin Hx with ⟨b, s, hb, ho1, ho2⟩ | ⟨hz, b, s, hb, ho1, ho2⟩
  · simp only [bv_unsigned] at ho1 ho2 ⊢
    refine ⟨b, s, hb, ?_, ?_⟩
    · have := pd_page x
      omega
    · have := pd_le x
      omega
  · simp only [bv_unsigned] at ho1 ho2 hz ⊢
    have hfl := (zone_floor _ x hz).1
    refine ⟨b, s, hb, ?_, ?_⟩
    · omega
    · omega

end LinuxSem.Checks.NoaccessOwned
