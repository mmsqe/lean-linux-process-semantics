/-
  * LinuxSem.Checks.MunmapCut — what a partial `munmap` leaves.

    Not part of the trusted specification.  When `Mmap.munmap_spec` answers
    0 to a partial unmap, it cuts both ledgers with `maps_subtract` over the
    page-rounded range (`Mmap.mmap_fixed_destroyed_next`).  This module
    states what that cut does, so a reader of the arm need not re-derive it:

    - `maps_subtract_owned`: `maps_subtract` leaves EXACTLY the bytes
      outside the cut (`maps_subtract_keeps` is the completeness half,
      citing `Core.lean`'s `owned_subtract`);
    - `check_munmap_zero_args`: a 0 answer passed both argument gates, so
      the range is page aligned at its base and ends at or below
      `TASK_SIZE` (`zero_ne_einval` is why the two `-EINVAL` answers are not
      mistaken for it);
    - `check_munmap_zero_owned`: after a 0 answer that is not the exact
      arm, `vm_maps` owns exactly the old bytes outside the page-rounded
      range.  The two ways a 0 answer reaches `vm_maps` are the free-range
      no-op, where `munmap_free_ok`'s `region_free` puts no live mapping in
      the range at all (`owned_outside_of_region_free`), and the cut, where
      the statement is one `maps_subtract_owned`;
    - `page_owned` and `check_munmap_zero_pages`, the page-granular form of
      the same: `p` is page aligned, so the page at `p` is inside the range
      whole or not at all;
    - `check_munmap_unmap_backing`: every answer that unmaps, whole or
      partial, cuts the lazy and materialized ledgers by the same range, so
      the backing charge of the range is released the same way.

    Nothing in this module is stated and left unproved.

    The ledger invariants are `NoaccessOwned.sys_inv`, and
    `NoaccessOwned.check_syscall_preserves_sys_inv` covers the partial arm;
    nothing here re-proves that.

    SPELLING.  The callers are this port's `check_munmap`, whose range end
    is `page_round_up_Z (len.toNat : Int)` (the original writes
    `bv_unsigned len` — the same value through the `bv_unsigned` abbrev).
    The word carrying it is `BitVec.ofInt 64 nZ`; `munmap_n_word` is why its
    `toNat` is that integer, which is what lets the ledger arithmetic be
    stated in `.toNat` and in `bv_unsigned` interchangeably.  The original
    spells the same fact with its own `u64`.
-/

import LinuxSem.Checks.NoaccessOwned

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
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

namespace LinuxSem.Checks.MunmapCut

open LinuxSem.Common.RocqSpelling

/-! ## The cut, as a set of bytes -/

/-- A byte of an entry outside the cut is still owned after it: the cut only
    divides entries, and `Core.lean`'s `owned_subtract` is that argument.
    (The original factors an `iv_subtract_keeps` step first; here the
    division is already inside `iv_subtract_owned`, so this is a
    citation.) -/
theorem maps_subtract_keeps (l : List (word × word)) (lo hi : Int) (x : Int)
    (Hf : maps_fit l) (Ho : owned l x) (Hc : ¬ (lo ≤ x ∧ x < hi)) :
    owned (maps_subtract l lo hi) x :=
  owned_subtract l lo hi x Hf Ho Hc

/-- `maps_subtract` leaves EXACTLY the bytes outside the cut: soundness is
    `Core.lean`'s `maps_subtract_bytes` (a remnant's byte came from its
    entry and lies outside the range) and completeness is the lemma above. -/
theorem maps_subtract_owned (l : List (word × word)) (lo hi : Int) (x : Int)
    (Hf : maps_fit l) :
    owned (maps_subtract l lo hi) x ↔ owned l x ∧ ¬ (lo ≤ x ∧ x < hi) := by
  refine ⟨?_, fun ⟨Ho, Hc⟩ => maps_subtract_keeps l lo hi x Hf Ho Hc⟩
  rintro ⟨a', s', Hin, h1, h2⟩
  obtain ⟨a, s, Hin0, ⟨h3, h4⟩, Hc⟩ :=
    maps_subtract_bytes l lo hi a' s' x Hf Hin ⟨h1, h2⟩
  exact ⟨⟨a, s, Hin0, h3, h4⟩, Hc⟩

/-! ## The checker's 0 answers -/

/-- 0 is not `-EINVAL`: the two errno answers cannot be mistaken for the
    success one. -/
theorem zero_ne_einval : (0 : word) ≠ errno_ret EINVAL := by decide

/-- An `-EINVAL` answer is not a 0 answer: the checker's two errno arms
    cannot be mistaken for the success arm. -/
theorem ret_only_einval_ne (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_ret_only eff (errno_ret EINVAL) m [] = .CheckOk m' evs)
    (Hr : eff.eff_ret = 0) : False := by
  obtain ⟨heff, -⟩ := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
  have hret : eff.eff_ret = errno_ret EINVAL := by rw [heff]
  rw [hret] at Hr
  exact zero_ne_einval Hr.symm

/-- A 0 answer passed both argument gates: the range is page aligned at its
    base and ends at or below `TASK_SIZE`. -/
theorem check_munmap_zero_args (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_munmap addr len eff m = .CheckOk m' evs) (Hr : eff.eff_ret = 0) :
    bv_unsigned addr % page_size = 0 ∧
      bv_unsigned addr + page_round_up_Z (len.toNat : Int) ≤ TASK_SIZE := by
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  have Hr' : ret = 0 := Hr
  unfold check_munmap at H
  by_cases h1 : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left h1] at H
    exact (ret_only_einval_ne ⟨ret, ws, zs, us, cs, ci⟩ m m' evs H Hr).elim
  · rw [ite_eq_right h1] at H
    dsimp only at H
    by_cases h2 : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left h2] at H
      exact (ret_only_einval_ne ⟨ret, ws, zs, us, cs, ci⟩ m m' evs H Hr).elim
    · rw [ite_eq_right h2] at H
      refine ⟨?_, ?_⟩
      · refine aligned_of_not_negb_beq _ ?_
        intro hc
        exact h1 (by rw [hc]; simp)
      · exact Int.not_lt.mp h2

/-! ## The two ledgers of an unmapping answer -/

/-- A `check_ret_only` acceptance carries no unmap ledger: the wrapper only
    admits the lone ledger-free effect (`check_ret_only_ok_iff`). -/
theorem ret_only_unmaps_nil (eff : SyscallEffect) (r : word) (m1 : Model)
    (evs1 : List event) (m' : Model) (evs : List event)
    (H : check_ret_only eff r m1 evs1 = .CheckOk m' evs) : eff.eff_unmaps = [] := by
  obtain ⟨heff, -, -⟩ := (check_ret_only_ok_iff eff r m1 evs1 m' evs).mp H
  rw [heff]

/-- The page-rounded length, as the word the checker hands to
    `map_has`/`with_mmap_destroyed`: wherever a `0` answer passed the
    `TASK_SIZE` gate, the rounding is a whole `u64` and the word reads back
    as that integer. -/
theorem munmap_n_word (addr len : word)
    (Hb : bv_unsigned addr + page_round_up_Z (bv_unsigned len) ≤ TASK_SIZE) :
    (BitVec.ofInt 64 (page_round_up_Z (bv_unsigned len))).toNat
      = page_round_up_Z (bv_unsigned len) := by
  -- the two unsigned values as `omega` atoms, each with its lower bound
  have hlen : (0 : Int) ≤ bv_unsigned len := by
    show (0 : Int) ≤ (len.toNat : Int)
    exact Int.natCast_nonneg _
  have haddr : (0 : Int) ≤ bv_unsigned addr := by
    show (0 : Int) ≤ (addr.toNat : Int)
    exact Int.natCast_nonneg _
  have hnn : (0 : Int) ≤ page_round_up_Z (bv_unsigned len) := by
    have h := page_round_up_Z_ge (bv_unsigned len) (by omega)
    omega
  have hlt : page_round_up_Z (bv_unsigned len) < two_pow_64 := by
    have hT : TASK_SIZE < two_pow_64 := by decide
    omega
  exact u64 _ ⟨hnn, hlt⟩

/-- A byte owned by a live mapping lies outside every range `region_free`
    covers: `region_free` says the range misses each live entry, and an
    entry that meets the range would put the byte inside it.

    The range end is given as a word `n` and read back with `(n.toNat : Int)`
    so that the two `word` ledgers and `iv_overlap` are compared on one
    carrier: `owned` and `iv_overlap` spell the same unsigned value two
    ways, and `omega` will not identify the two spellings on its own. -/
theorem owned_outside_of_region_free (res maps : List (word × word)) (lo n : word)
    (Hfree : region_free (res ++ maps) lo n = true) (x : Int) (Ho : owned maps x) :
    ¬ (bv_unsigned lo ≤ x ∧ x < bv_unsigned lo + (n.toNat : Int)) := by
  intro Hin
  obtain ⟨b, s, Hbs, hb1, hb2⟩ := Ho
  -- restate the four facts in one spelling and drop the originals:
  -- `owned`/`bv_unsigned` is opaque to `omega`, `iv_overlap`/`toNat` is not
  have hx : (lo.toNat : Int) ≤ x := Hin.1
  have hx2 : x < (lo.toNat : Int) + (n.toNat : Int) := Hin.2
  have hb : (b.toNat : Int) ≤ x := hb1
  have hb2' : x < (b.toNat : Int) + (s.toNat : Int) := hb2
  clear Hin hb1 hb2
  have hyes : iv_overlap lo n b s = true := by
    simp only [iv_overlap, Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  have hno := region_free_In _ _ _ b s Hfree (List.mem_append_right _ Hbs)
  rw [hyes] at hno
  exact absurd hno (by simp)

/-- After a `0` answer that is NOT the exact arm — the free-range no-op or
    the cut — `vm_maps` owns exactly the bytes it owned outside the
    page-rounded range.  The two branches are the two ways a `0` answer
    reaches `vm_maps`: untouched (`munmap_free_ok`, whose `region_free`
    puts no live mapping in the range at all) or cut by
    `mmap_fixed_destroyed_next`, where `maps_subtract_owned` is the whole
    statement.

    `map_has … = false` is the hypothesis that excludes the exact arm: a
    whole-mapping answer, not a partial one. -/
theorem check_munmap_zero_owned (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (Hfit : vm_fit (m_vmmaps m))
    (Hhas : map_has (m_vmmaps m).vm_maps addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false)
    (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hr : eff.eff_ret = 0) :
    ∀ x, owned (m_vmmaps m').vm_maps x ↔
      owned (m_vmmaps m).vm_maps x ∧
        ¬ (bv_unsigned addr ≤ x ∧
            x < bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := by
  intro x
  obtain ⟨-, Hb⟩ := check_munmap_zero_args addr len eff m m' evs H Hr
  have Hn := munmap_n_word addr len Hb
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  have Hr' : r = 0 := Hr
  subst Hr'
  unfold check_munmap at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    exact (ret_only_einval_ne ⟨0, ws, zs, us, cs, ci⟩ m m' evs H rfl).elim
  · rw [ite_eq_right hi] at H
    dsimp only at H
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      exact (ret_only_einval_ne ⟨0, ws, zs, us, cs, ci⟩ m m' evs H rfl).elim
    · rw [ite_eq_right hbig] at H
      try dsimp only at H
      -- the exact arm is excluded: no live mapping is the request itself
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr
          (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
      · rw [hhas] at Hhas
        exact absurd Hhas (by simp)
      · rw [ite_eq_right hhas] at H
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · -- THE FREE RANGE: nothing is owned in it, and nothing changes
          rw [ite_eq_left hfree] at H
          obtain ⟨-, hm, -⟩ :=
            (check_ret_only_ok_iff ⟨0, ws, zs, us, cs, ci⟩ 0 m [] m' evs).mp H
          rw [hm]
          unfold munmap_free_ok at hfree
          rw [Bool.and_eq_true] at hfree
          refine ⟨fun Ho => ⟨Ho, ?_⟩, fun ⟨Ho, _⟩ => Ho⟩
          intro Hin
          have hout := owned_outside_of_region_free (m_vmmaps m).vm_reserved
            (m_vmmaps m).vm_maps addr
            (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) hfree.1 x Ho
          rw [Hn] at hout
          exact hout Hin
        · -- THE CUT: `maps_subtract_owned` over the page-rounded range.
          -- `0` is not in `munmap_errnos`, so the arm's errno leaf is dead
          rw [ite_eq_right hfree] at H
          by_cases hcut : munmap_cut_ok (m_vmmaps m) addr
              (page_round_up_Z (len.toNat : Int)) = true
          · rw [ite_eq_left hcut] at H
            cases ws <;> cases zs <;> cases cs <;> cases ci <;> try dsimp only at H
            · by_cases he : errno_ret_in munmap_errnos (0 : word) = true
              · rw [ite_eq_left he] at H
                rw [show errno_ret_in munmap_errnos (0 : word) = false from by decide] at he
                exact absurd he (by simp)
              · rw [ite_eq_right he] at H
                by_cases hc : (w_is0 (0 : word) && listNN_eqb us
                    [(addr, BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
                · rw [ite_eq_left hc] at H
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, -⟩ := H
                  rw [hm.symm]
                  dsimp only [with_mmap_destroyed, vm_forget_range,
                    mmap_fixed_destroyed_next, m_vmmaps, with_vmmaps, with_vm_backing]
                  rw [Hn]
                  exact maps_subtract_owned _ _ _ _ Hfit
                · rw [ite_eq_right hc] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hcut] at H
            exact nomatch H

/-- Every byte of the page at `p` is owned. -/
def page_owned (maps : List (word × word)) (p : Int) : Prop :=
  ∀ x, p ≤ x ∧ x < p + page_size → owned maps x

/-- The page-granular form of `check_munmap_zero_owned`: `p` is page
    aligned, so the page at `p` is inside the range whole or not at all. -/
theorem check_munmap_zero_pages (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (p : Int)
    (Hfit : vm_fit (m_vmmaps m))
    (Hhas : map_has (m_vmmaps m).vm_maps addr
      (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = false)
    (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hr : eff.eff_ret = 0)
    (Hp : p % page_size = 0) :
    page_owned (m_vmmaps m').vm_maps p ↔
      page_owned (m_vmmaps m).vm_maps p ∧
        ¬ (bv_unsigned addr ≤ p ∧
            p < bv_unsigned addr + page_round_up_Z (bv_unsigned len)) := by
  obtain ⟨Ha, -⟩ := check_munmap_zero_args addr len eff m m' evs H Hr
  have Hx := check_munmap_zero_owned addr len eff m m' evs Hfit Hhas H Hr
  -- the two constants `omega` needs, as equations it can substitute
  have hps : page_size = 4096 := rfl
  have hnmod : page_round_up_Z (bv_unsigned len) % page_size = 0 := by
    unfold page_round_up_Z
    exact Int.emod_eq_zero_of_dvd ⟨_, by rw [Int.mul_comm]⟩
  rw [hps] at Ha Hp hnmod
  constructor
  · intro Hall
    unfold page_owned at Hall
    refine ⟨fun y Hy => ((Hx y).mp (Hall y Hy)).1, fun Hin => ?_⟩
    have hmem : p ≤ p ∧ p < p + page_size := ⟨by omega, by omega⟩
    exact ((Hx p).mp (Hall p hmem)).2 Hin
  · rintro ⟨Hall, Hc⟩ y Hy
    unfold page_owned at Hall
    refine (Hx y).mpr ⟨Hall y Hy, fun Hin => ?_⟩
    obtain ⟨h1, h2⟩ := Hin
    exact Hc ⟨by omega, by omega⟩


/-- EVERY UNMAPPING ANSWER CUTS THE BACKING LEDGERS by the same
    page-rounded range, whole or partial: both accepting effect shapes end
    in `with_mmap_destroyed`, which is `vm_forget_range` over the range, and
    a `check_ret_only` answer (the free-range no-op, an `-EINVAL`, the cut
    arm's injected `-ENOMEM`) carries no unmap ledger at all. -/
theorem check_munmap_unmap_backing (addr len : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event)
    (H : check_munmap addr len eff m = .CheckOk m' evs)
    (Hus : eff.eff_unmaps ≠ []) :
    m_vm_lazy m' = maps_subtract (m_vm_lazy m) (bv_unsigned addr)
        (bv_unsigned addr + page_round_up_Z (bv_unsigned len))
    ∧ m_vm_materialized m' = List.filter
        (page_outside_range (bv_unsigned addr)
          (bv_unsigned addr + page_round_up_Z (bv_unsigned len)))
        (m_vm_materialized m) := by
  obtain ⟨r, ws, zs, us, cs, ci⟩ := eff
  have Hus' : us ≠ [] := Hus
  -- the two argument gates decline with an `-EINVAL`, which unmaps nothing
  unfold check_munmap at H
  by_cases hi : (!(((addr.toNat : Int) % page_size) == 0) || w_is0 len) = true
  · rw [ite_eq_left hi] at H
    exact absurd (ret_only_unmaps_nil _ _ _ _ _ _ H) Hus'
  · rw [ite_eq_right hi] at H
    dsimp only at H
    by_cases hbig : TASK_SIZE < (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
    · rw [ite_eq_left hbig] at H
      exact absurd (ret_only_unmaps_nil _ _ _ _ _ _ H) Hus'
    · rw [ite_eq_right hbig] at H
      try dsimp only at H
      -- the range is a whole `u64`, so the word is its rounded length
      have hbig' : (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) ≤ TASK_SIZE := by
        omega
      have Hn : (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))).toNat
          = page_round_up_Z (len.toNat : Int) := by
        have h := munmap_n_word addr len (by rw [show bv_unsigned len = (len.toNat : Int) from rfl]; exact hbig')
        simpa [bv_unsigned] using h
      by_cases hhas : map_has (m_vmmaps m).vm_maps addr
          (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
      · -- THE EXACT ARM: the whole mapping, cut by the range
        rw [ite_eq_left hhas] at H
        cases ws <;> cases zs <;> cases cs <;> cases ci <;> try dsimp only at H
        · by_cases hc : (w_is0 r && listNN_eqb us [(addr,
              BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
          · rw [ite_eq_left hc] at H
            simp only [check_result.CheckOk.injEq] at H
            obtain ⟨hm, -⟩ := H
            rw [hm.symm]
            refine ⟨?_, ?_⟩ <;>
              dsimp only [with_mmap_destroyed, vm_forget_range, m_vm_lazy,
                m_vm_materialized, m_vmmaps, with_vmmaps, with_vm_backing]
            · rw [Hn]
            · rw [Hn]
          · rw [ite_eq_right hc] at H
            exact nomatch H
        all_goals exact nomatch H
      · rw [ite_eq_right hhas] at H
        by_cases hfree : munmap_free_ok (m_vmmaps m) addr
            (page_round_up_Z (len.toNat : Int)) = true
        · -- THE FREE RANGE: a no-op, so it unmaps nothing
          rw [ite_eq_left hfree] at H
          exact absurd (ret_only_unmaps_nil _ _ _ _ _ _ H) Hus'
        · rw [ite_eq_right hfree] at H
          by_cases hcut : munmap_cut_ok (m_vmmaps m) addr
              (page_round_up_Z (len.toNat : Int)) = true
          · -- THE CUT
            rw [ite_eq_left hcut] at H
            cases ws <;> cases zs <;> cases cs <;> cases ci <;> try dsimp only at H
            · by_cases he : errno_ret_in munmap_errnos r = true
              · -- -ENOMEM exists only beside `us = []`, which `Hus` forbids
                rw [ite_eq_left he] at H
                cases us with
                | nil => exact absurd rfl Hus'
                | cons u us' => exact nomatch H
              · rw [ite_eq_right he] at H
                by_cases hc : (w_is0 r && listNN_eqb us [(addr,
                    BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))]) = true
                · rw [ite_eq_left hc] at H
                  simp only [check_result.CheckOk.injEq] at H
                  obtain ⟨hm, -⟩ := H
                  rw [hm.symm]
                  refine ⟨?_, ?_⟩ <;>
                    dsimp only [with_mmap_destroyed, vm_forget_range, m_vm_lazy,
                      m_vm_materialized, mmap_fixed_destroyed_next, m_vmmaps,
                      with_vmmaps, with_vm_backing]
                  · rw [Hn]
                  · rw [Hn]
                · rw [ite_eq_right hc] at H
                  exact nomatch H
            all_goals exact nomatch H
          · rw [ite_eq_right hcut] at H
            exact nomatch H

end LinuxSem.Checks.MunmapCut
