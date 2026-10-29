/-
  * Common.MemsetLib — image-INDEPENDENT theory for the generic musl [memset]
    summary.

  - [cfill mem0 d n c L]: memory [mem0] with the constant byte [c] written
    at every offset [i] of [[0,n)] (relative to [d]) that is covered by one
    of the (offset,length) intervals of [L].  Every store of the routine
    conses one interval ([cfill_store]); at the end a CHAIN argument
    ([ms_chain]/[cfill_full_chain]) shows the whole range is covered, so the
    overlay is [wbytes mem0 d (repeat c n)] (functional extensionality, a
    permitted postulate — Lean's [funext]).
  - the replicated fill patterns: [c32 cv] / [c64 cv] and the facts that
    the code's [mulhu]/[slli]/[srli]/[or] sequence computes them and that
    [sw]/[sd] of them store 4 / 8 copies of [cbyte cv];
  - small ALU facts ([negw]+[andi 3], [andi -4], [andi 4]);
  - [_at]-style step wrappers for [subw]/[mulhu]/[or];
  - step wrappers for [sb]/[sw]/[sd] over a [cfill] memory, in a Section
    over an arbitrary segment list.

  ------------------------------------------------------------------
  NOTES.

  * Conventions: `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` →
    `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)` (the spelling
    `Common/PropExec.lean` and `Common/CatExec.lean` use),
    `Z.land`/`Z.lor` → [zland]/[zlor] over `Nat` (the encoding those files
    use; exact on non-negative integers, the only place they occur here),
    `bool_decide` → `decide`, `repeat a n` → `List.replicate n a`,
    `nth k l d` → `l.getD k d`, `firstn` → `List.take`, `In` → `∈`,
    `incl` → pointwise membership, `lia` → `omega`.

  * The  file imports the whole `Common/` proof library.  The
    declarations below are stated over its vocabulary; the parts of that
    vocabulary the tree already proves are imported rather than restated:

      `Common/PropExec.lean`  mkst, getr, regupd, getr_same/getr_other,
                              regupd_same, v_addi/v_add/v_sub/v_andi/
                              v_slli/v_srli/v_or/v_subw/v_mulhu,
                              bv_wrap/bv_swrap, zland/zlor,
                              bv_wrap8_mod/bv_wrap64_mod, u64_range,
                              bv_eqb_neq, b_addsext, step_pipeline, and
                              the per-instruction step lemmas
                              step_subw/step_mulhu/step_or;
      `Common/CatExec.lean`   wbytes, wbytes_above/wbytes_below,
                              write_to_mem_wbytes, length_N_to_le_bytes,
                              toNat_add_one, step_sd;
      `Common/SeqExec.lean`   step_sb, step_sw_at, step_sd_at (the
                              VALUE-precise store steps the store lemmas
                              [cf_sb]/[cf_sw]/[cf_sd] feed to
                              [cfill_store]) and N_to_le_bytes_1_small.
 Those declarations are restated VERBATIM in
    the "Prerequisites" section below, each labelled with the file it
    comes from, so that every lemma of THIS file keeps its  type.
    When those modules land, delete the corresponding block and open the
    module instead.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec

namespace LinuxSem.Common.MemsetLib

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec

/-- `Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0`:
    the step lemmas below are stated at the FP state of process entry. -/
local instance asanreflect_fx : FPState := fx0

-- Same linter discipline as the prerequisite modules: Lean adds a section
-- variable to a lemma's type only when the statement mentions it, and this
-- tree makes that explicit.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! -/

/-! ### Round trips of [Z_to_bv 64] (StepTac, PropExec) -/

/-- `((2^n : Nat) : Int) = 2^n` — the cast shape the `BitVec` lemmas use. -/
theorem two_pow_natCast (n : Nat) : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by
  rw [Int.natCast_pow]; rfl

/-- `2^n` is positive in `Int`. -/
theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  rw [two_pow_natCast]; exact Int.pow_pos (by decide)

/-- `bv_unsigned (Z_to_bv 64 z)` collapses to `z` when in range . -/
theorem u_Z2bv (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z := by
  rw [BitVec.toNat_ofInt]
  rw [show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from two_pow_natCast 64]
  rw [Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

/-- The general form: `bv_unsigned (Z_to_bv n z) = z mod 2^n`. -/
theorem toNat_ofInt_emod {n : Nat} (z : Int) :
    ((BitVec.ofInt n z).toNat : Int) = z % (2 : Int) ^ n := by
  rw [BitVec.toNat_ofInt,
    show ((2 ^ n : Nat) : Int) = (2 : Int) ^ n from two_pow_natCast n,
    Int.toNat_of_nonneg]
  have h : (0 : Int) < ((2 ^ n : Nat) : Int) := two_pow_pos_int n
  omega

/-- The `Nat`-level form of [toNat_ofInt_emod] (goals that keep the `toNat`
    at type `Nat`, as the `BitVec` comparisons below do). -/
theorem toNat_ofInt_emod_nat {n : Nat} (z : Int) :
    (BitVec.ofInt n z).toNat = (z % (2 : Int) ^ n).toNat := by
  rw [BitVec.toNat_ofInt, two_pow_natCast]

/-- Adding one does not wrap, so the unsigned value advances by one. -/
theorem u_add1 (a : word) (h : (a.toNat : Int) + 1 < 2 ^ 64) :
    ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := by
  have h1 : a.toNat + 1 < 2 ^ 64 := by exact_mod_cast h
  have h2 := toNat_add_one a h1
  rw [h2]
  simp

/-- `(z - 1).toNat = z.toNat - 1` for a positive integer `z` (the list
    index advances by one per stored byte). -/
theorem toNat_sub_one {z : Int} (h : 1 ≤ z) : (z - 1).toNat = z.toNat - 1 := by
  have h1 : (((z - 1).toNat : Nat) : Int) = z - 1 := Int.toNat_of_nonneg (by omega)
  have h2 : ((z.toNat : Nat) : Int) = z := Int.toNat_of_nonneg (by omega)
  omega

/-! ### Address arithmetic (Hoare)

  [at_ base d] is [base + d], the address of the instruction at byte offset
  [d] of a relocatable code blob loaded at [base].  All the lemmas about it
  are wrap-around-free BY CONSTRUCTION (the underlying [Z_to_bv] wraps), so
  an address-parametric summary needs NO bound on [base].

  [at_] belongs to `Common/Hoare`.  When this file was written that
  module was not yet stated, so [at_] is restated here (and nothing else
  of [Hoare] is).  **`Common/Hoare.lean` has since landed** and defines
  [at_] identically, so this copy is redundant; it is kept to avoid an
  import edge from `MemsetLib` up to `Hoare`, and can be replaced by
  `Hoare.at_` where that edge already exists. -/

/-- `base + d`, the address of byte [d] of a blob loaded at [base]. -/
def at_ (base : word) (d : Int) : word :=
  BitVec.ofInt 64 ((base.toNat : Int) + d)

/-- [at_] of an in-range offset: the unsigned value is the offset sum. -/
theorem at_u (a : word) (d : Int) (h0 : 0 ≤ (a.toNat : Int) + d)
    (h1 : (a.toNat : Int) + d < 2 ^ 64) :
    ((at_ a d).toNat : Int) = (a.toNat : Int) + d :=
  u_Z2bv _ h0 h1

/-- [at_ base 0 = base]. -/
theorem at_0 (base : word) : at_ base 0 = base := by
  unfold at_
  rw [show (base.toNat : Int) + 0 = (base.toNat : Int) by omega]
  apply BitVec.eq_of_toNat_eq
  have h := u_Z2bv (base.toNat : Int) (u64_range base).1 (u64_range base).2
  exact_mod_cast h

/-- [at_] composes.   -/
theorem at_at (base : word) (d e : Int) : at_ (at_ base d) e = at_ base (d + e) := by
  unfold at_
  apply BitVec.eq_of_toNat_eq
  have h1 : ((BitVec.ofInt 64 ((base.toNat : Int) + d)).toNat : Int)
      = ((base.toNat : Int) + d) % (2 : Int) ^ 64 := toNat_ofInt_emod _
  have h2 : ((BitVec.ofInt 64
        (((BitVec.ofInt 64 ((base.toNat : Int) + d)).toNat : Int) + e)).toNat : Int)
      = ((((base.toNat : Int) + d) % (2 : Int) ^ 64) + e) % (2 : Int) ^ 64 := by
    rw [toNat_ofInt_emod, h1]
  have h3 : ((BitVec.ofInt 64 ((base.toNat : Int) + (d + e))).toNat : Int)
      = ((base.toNat : Int) + (d + e)) % (2 : Int) ^ 64 := toNat_ofInt_emod _
  have h4 : ((((base.toNat : Int) + d) % (2 : Int) ^ 64) + e) % (2 : Int) ^ 64
      = ((base.toNat : Int) + (d + e)) % (2 : Int) ^ 64 := by
    rw [Int.emod_add_emod]; congr 1; omega
  have h := h2.trans (h4.trans h3.symm)
  exact_mod_cast h

/-! ### Overlay growth and the machine-store bound (StoreOk)

  [store_ok] only ever asks whether a byte is DEFINED, so the relevant
  order on overlays is definedness, not equality: writing bytes, or
  zero-filling a grant, can only add. -/

/-- Definedness order on memory overlays. -/
def mem_grows (m m' : word → Option byte) : Prop :=
  ∀ x, m x ≠ none → m' x ≠ none

theorem mem_grows_refl (m : word → Option byte) : mem_grows m m :=
  fun _ h => h

theorem mem_grows_trans {m1 m2 m3 : word → Option byte}
    (h12 : mem_grows m1 m2) (h23 : mem_grows m2 m3) : mem_grows m1 m3 :=
  fun x hx => h23 x (h12 x hx)

/-- [wview]'s segment fallback does not depend on the overlay, so a byte
    that was writable stays writable however the overlay grows. -/
theorem wview_grows (segs : List Segment) {m m' : word → Option byte}
    (hg : mem_grows m m') (x : word) (hx : wview segs m x ≠ none) :
    wview segs m' x ≠ none := by
  cases hm2 : m' x with
  | some b => unfold wview; rw [hm2]; simp
  | none =>
    have hm : m x = none := by
      cases hm1 : m x with
      | none => rfl
      | some b => exact absurd hm2 (hg x (by rw [hm1]; simp))
    simp only [wview, hm2, hm] at hx ⊢
    exact hx

/-- An earlier [store_ok] survives any growth of the overlay. -/
theorem store_ok_mono (segs : List Segment) :
    ∀ (n : Nat) (m m' : word → Option byte) (a : word),
      mem_grows m m' → store_ok segs m a n = true → store_ok segs m' a n = true := by
  intro n
  induction n with
  | zero => intro m m' a _ _; rfl
  | succ n ih =>
    intro m m' a hg hok
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    have hstep' : store_ok segs m' a (n + 1)
        = (match wview segs m' a with
           | some _ => store_ok segs m' (a + 1) n
           | none => false) := rfl
    rw [hstep] at hok
    rw [hstep']
    cases hw : wview segs m a with
    | none => rw [hw] at hok; exact absurd hok (by simp)
    | some b =>
      rw [hw] at hok
      have hw' : wview segs m' a ≠ none := wview_grows segs hg a (by rw [hw]; simp)
      cases hw2 : wview segs m' a with
      | none => exact absurd hw2 hw'
      | some b' => exact ih m m' (a + 1) hg hok

/-- Every byte in the range is writable, from a successful [store_ok]. -/
theorem store_ok_all (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word), (a.toNat : Int) + (n : Int) ≤ 2 ^ 64 →
      store_ok segs m a n = true →
      ∀ x, (a.toNat : Int) ≤ (x.toNat : Int) →
        (x.toNat : Int) < (a.toNat : Int) + (n : Int) → wview segs m x ≠ none := by
  intro n
  induction n with
  | zero =>
    intro a _ _ x hx1 hx2
    omega
  | succ n ih =>
    intro a hb hok x hx1 hx2
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast] at hb hx2
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep] at hok
    cases hw : wview segs m a with
    | none => rw [hw] at hok; exact absurd hok (by simp)
    | some b =>
      rw [hw] at hok
      by_cases hxa : (x.toNat : Int) = (a.toNat : Int)
      · have hxaeq : x = a := by
          apply BitVec.eq_of_toNat_eq
          exact_mod_cast hxa
        rw [hxaeq]
        rw [hw]
        simp
      · by_cases hlt : (a.toNat : Int) + 1 < 2 ^ 64
        · have hu : ((a + 1).toNat : Int) = (a.toNat : Int) + 1 := u_add1 a hlt
          exact ih (a + 1) (by omega) hok x (by omega) (by omega)
        · -- the first byte sits at the very last address, so the range is
          -- one byte long and [x] is it
          have hn0 : n = 0 := by omega
          subst hn0
          have hxa2 : (x.toNat : Int) = (a.toNat : Int) := by omega
          have hxaeq : x = a := by
            apply BitVec.eq_of_toNat_eq
            exact_mod_cast hxa2
          rw [hxaeq]
          rw [hw]
          simp

/-- The converse: a range every byte of which is writable passes
    [store_ok]. -/
theorem store_ok_of_all (segs : List Segment) (m : word → Option byte) :
    ∀ (n : Nat) (a : word), (a.toNat : Int) + (n : Int) ≤ 2 ^ 64 →
      (∀ x, (a.toNat : Int) ≤ (x.toNat : Int) →
        (x.toNat : Int) < (a.toNat : Int) + (n : Int) → wview segs m x ≠ none) →
      store_ok segs m a n = true := by
  intro n
  induction n with
  | zero => intro a _ _; rfl
  | succ n ih =>
    intro a hb hcov
    have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
    rw [hcast] at hb
    have hstep : store_ok segs m a (n + 1)
        = (match wview segs m a with
           | some _ => store_ok segs m (a + 1) n
           | none => false) := rfl
    rw [hstep]
    have hwa : wview segs m a ≠ none := hcov a (by omega) (by omega)
    cases hwv : wview segs m a with
    | none => exact absurd hwv hwa
    | some b =>
      apply ih (a + 1)
      · by_cases hlt : (a.toNat : Int) + 1 < 2 ^ 64
        · have hu := u_add1 a hlt; omega
        · have hn0 : n = 0 := by omega
          subst hn0
          have hb' := (u64_range (a + 1)).2
          simp only [Int.natCast_zero, Int.add_zero]
          exact Int.le_of_lt hb'
      · intro x hx1 hx2
        by_cases hlt : (a.toNat : Int) + 1 < 2 ^ 64
        · have hu := u_add1 a hlt
          exact hcov x (by omega) (by omega)
        · omega

/-- A sub-range of a writable range is writable . -/
theorem store_ok_sub (segs : List Segment) (m : word → Option byte)
    (lo a : word) (N n : Nat)
    (hnw : (lo.toNat : Int) + (N : Int) ≤ 2 ^ 64)
    (hok : store_ok segs m lo N = true)
    (hl : (lo.toNat : Int) ≤ (a.toNat : Int))
    (hh : (a.toNat : Int) + (n : Int) ≤ (lo.toNat : Int) + (N : Int)) :
    store_ok segs m a n = true := by
  apply store_ok_of_all
  · omega
  · intro x hx1 hx2
    exact store_ok_all segs m N lo hnw hok x (by omega) (by omega)

/-! ### The pointwise description of [wbytes] (MemSplit) -/

/-- The byte [wbytes] leaves at an address inside the written range. -/
theorem wbytes_inside (bs : List byte) (m : word → Option byte) (a x : word)
    (hnw : (a.toNat : Int) + (bs.length : Int) ≤ 2 ^ 64)
    (hx : (a.toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < (a.toNat : Int) + (bs.length : Int)) :
    wbytes m a bs x
      = some (bs.getD ((x.toNat : Int) - (a.toNat : Int)).toNat (BitVec.ofInt 8 0)) := by
  induction bs generalizing m a with
  | nil =>
    simp only [List.length_nil] at hx
    omega
  | cons b rest ih =>
    simp only [wbytes, List.length_cons, Int.natCast_add, Int.natCast_one] at hnw hx ⊢
    by_cases heq : (x.toNat : Int) = (a.toNat : Int)
    · -- [x] is the head: the head store decides it, the tail misses it.
      have hxa : x = a := by
        apply BitVec.eq_of_toNat_eq
        exact_mod_cast heq
      subst hxa
      have hzero : ((x.toNat : Int) - (x.toNat : Int)).toNat = 0 := by omega
      rw [hzero]
      have hne : bv_eqb x x = true := by
        unfold bv_eqb; simp
      cases rest with
      | nil =>
        simp only [wbytes, hne, ite_true, List.getD_cons_zero]
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw ⊢
        have hlt : (x.toNat : Int) + 1 < 2 ^ 64 := by omega
        have hu := u_add1 x hlt
        rw [wbytes_below (b' :: rest')
          (fun y => if bv_eqb y x then some b else m y) (x + 1) x
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)
          (by omega)]
        simp only [hne, ite_true, List.getD_cons_zero]
    · -- [x] is past the head: the head store misses it, the tail decides it.
      have hgt : (a.toNat : Int) < (x.toNat : Int) := by omega
      have hne : bv_eqb x a = false :=
        bv_eqb_neq x a (by
          intro hc
          have hx' : (x.toNat : Int) = (a.toNat : Int) := by rw [hc]
          omega)
      cases rest with
      | nil =>
        simp only [List.length_nil, Int.natCast_zero, Int.add_zero] at hx
        omega
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw hx ⊢
        have hlt : (a.toNat : Int) + 1 < 2 ^ 64 := by omega
        have hu := u_add1 a hlt
        have hk : ((x.toNat : Int) - (a.toNat : Int)).toNat
            = ((x.toNat : Int) - ((a + 1).toNat : Int)).toNat + 1 := by
          have hsub : (x.toNat : Int) - ((a + 1).toNat : Int)
              = ((x.toNat : Int) - (a.toNat : Int)) - 1 := by omega
          rw [hsub]
          have h1 : 1 ≤ (x.toNat : Int) - (a.toNat : Int) := by omega
          rw [toNat_sub_one h1]
          omega
        rw [hk]
        simp only [hne, Bool.false_eq_true, ite_false, List.getD_cons_succ]
        rw [ih (fun y => if bv_eqb y a then some b else m y) (a + 1)
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)
          (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)]

/-- [nth] of a [replicate] below its length . -/
theorem nth_repeat_lt {α : Type} (a d : α) (m j : Nat) (h : j < m) :
    (List.replicate m a).getD j d = a := by
  simp [List.getD, List.getElem?_replicate, h]

/-- [length (repeat a m) = m]. -/
theorem repeat_length {α : Type} (a : α) (m : Nat) :
    (List.replicate m a).length = m :=
  List.length_replicate

/-! ## Coverage lists -/

/-- An interval is (offset, length) relative to the destination. -/
def ms_inb (i : Int) (iv : Int × Int) : Bool :=
  decide (iv.1 ≤ i) && decide (i < iv.1 + iv.2)

/-- Is [i] covered by one of the intervals of [L]? -/
def ms_cov (L : List (Int × Int)) (i : Int) : Bool :=
  L.any (ms_inb i)

/-- Membership in a single interval, unfolded. -/
theorem ms_inb_true (i o m : Int) :
    ms_inb i (o, m) = true ↔ o ≤ i ∧ i < o + m := by
  simp [ms_inb, Bool.and_eq_true]

/-- Non-membership, in the shape the [cfill] case analysis uses. -/
theorem ms_inb_false (i o m : Int) (h : ¬ (o ≤ i ∧ i < o + m)) :
    ms_inb i (o, m) = false := by
  unfold ms_inb
  have h1 : ¬ (o ≤ i) ∨ ¬ (i < o + m) := by
    by_cases h' : o ≤ i
    · right; intro h2; exact h ⟨h', h2⟩
    · left; exact h'
  rcases h1 with h1 | h1
  · rw [decide_eq_false_iff_not.mpr h1]; rfl
  · rw [decide_eq_false_iff_not.mpr h1, Bool.and_false]

/-- Coverage of a cons unfolds to a disjunction. -/
theorem ms_cov_cons (iv : Int × Int) (L : List (Int × Int)) (i : Int) :
    ms_cov (iv :: L) i = (ms_inb i iv || ms_cov L i) := rfl

/-- Coverage of an append distributes. -/
theorem ms_cov_app (L1 L2 : List (Int × Int)) (i : Int) :
    ms_cov (L1 ++ L2) i = (ms_cov L1 i || ms_cov L2 i) := by
  unfold ms_cov
  rw [List.any_append]

/-- An interval of the list covers [i] outright. -/
theorem ms_cov_In (L : List (Int × Int)) (i o m : Int)
    (hin : (o, m) ∈ L) (hi : o ≤ i ∧ i < o + m) : ms_cov L i = true := by
  unfold ms_cov
  rw [List.any_eq_true]
  exact ⟨(o, m), hin, (ms_inb_true i o m).mpr hi⟩

/-- [ms_chain frm to L]: assuming everything below [frm] is covered, the
    intervals of [L], in this order, extend the covered prefix to [to].
-/
def ms_chain : Int → Int → List (Int × Int) → Prop
  | frm, to, [] => to ≤ frm
  | frm, to, (o, m) :: L' => o ≤ frm ∧ ms_chain (o + m) to L'

/-- A chain covers everything in its range. -/
theorem ms_chain_cov (L : List (Int × Int)) (frm to i : Int)
    (hc : ms_chain frm to L) (hi : frm ≤ i ∧ i < to) :
    ∃ o m, (o, m) ∈ L ∧ o ≤ i ∧ i < o + m := by
  induction L generalizing frm to i with
  | nil =>
    simp only [ms_chain] at hc
    omega
  | cons hd tl ih =>
    obtain ⟨o, m⟩ := hd
    simp only [ms_chain] at hc
    obtain ⟨ho, hc⟩ := hc
    by_cases hlt : i < o + m
    · exact ⟨o, m, by simp, by omega, hlt⟩
    · have hge : o + m ≤ i := by omega
      obtain ⟨o', m', hin, ho', hi'⟩ := ih (o + m) to i hc ⟨hge, hi.2⟩
      exact ⟨o', m', List.mem_cons_of_mem _ hin, ho', hi'⟩

/-- The form used at every exit: pick a sub-list [L'] of the stores done,
    in address order, and check the [ms_chain] conditions (all linear). -/
theorem ms_cov_by_chain (L L' : List (Int × Int)) (n : Int)
    (hincl : ∀ iv, iv ∈ L' → iv ∈ L) (hc : ms_chain 0 n L') (i : Int)
    (hi : 0 ≤ i ∧ i < n) : ms_cov L i = true := by
  obtain ⟨o, m, hin, hom⟩ := ms_chain_cov L' 0 n i hc hi
  exact ms_cov_In L i o m (hincl _ hin) hom

/-! =====================================================================
    [cfill]
    ===================================================================== -/

/-- [cfill mem0 d n c L]: [mem0] with the byte [c] written at every offset
    [i] of `[0,n)` (relative to [d]) covered by one of the intervals of
    [L].  This is the whole memory effect of the memset loop, accumulated
    one store at a time ([cfill_store]). -/
def cfill (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (L : List (Int × Int)) : word → Option byte :=
  fun x =>
    if decide ((d.toNat : Int) ≤ (x.toNat : Int)) &&
       decide ((x.toNat : Int) < (d.toNat : Int) + n) &&
       ms_cov L ((x.toNat : Int) - (d.toNat : Int))
    then some c else mem0 x

/-- No stores done yet: the overlay is untouched. -/
theorem cfill_nil (mem0 : word → Option byte) (d : word) (n : Int) (c : byte) :
    cfill mem0 d n c [] = mem0 := by
  funext x
  simp [cfill, ms_cov]

/-- The overlay only ever grows. -/
theorem cfill_grows (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (L : List (Int × Int)) : mem_grows mem0 (cfill mem0 d n c L) := by
  intro x hx
  unfold cfill
  split
  · simp
  · exact hx

/-- Two lists with the same coverage of `[0,n)` give the same memory. -/
theorem cfill_ext (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (L1 L2 : List (Int × Int))
    (h : ∀ i, 0 ≤ i → i < n → ms_cov L1 i = ms_cov L2 i) :
    cfill mem0 d n c L1 = cfill mem0 d n c L2 := by
  funext x
  unfold cfill
  by_cases h1 : (d.toNat : Int) ≤ (x.toNat : Int)
  · by_cases h2 : (x.toNat : Int) < (d.toNat : Int) + n
    · rw [h ((x.toNat : Int) - (d.toNat : Int)) (by omega) (by omega)]
    · rw [decide_eq_true_eq.mpr h1, decide_eq_false_iff_not.mpr h2]
      simp
  · rw [decide_eq_false_iff_not.mpr h1]
    simp

/-- Pointwise: consing an interval changes [cfill] only by adding that
    interval to the coverage disjunction — the "hit" case. -/
theorem cfill_cons_hit {mem0 : word → Option byte} {d : word} {n : Int} {c : byte}
    {L : List (Int × Int)} {o m : Int} {x : word}
    (h1 : (d.toNat : Int) ≤ (x.toNat : Int))
    (h2 : (x.toNat : Int) < (d.toNat : Int) + n)
    (hb : ms_inb ((x.toNat : Int) - (d.toNat : Int)) (o, m) = true) :
    cfill mem0 d n c ((o, m) :: L) x = some c := by
  unfold cfill
  rw [ms_cov_cons, hb, decide_eq_true_eq.mpr h1, decide_eq_true_eq.mpr h2]
  simp

/-- Pointwise: the "miss" case, when the first two conditions already fail. -/
theorem cfill_cons_miss {mem0 : word → Option byte} {d : word} {n : Int} {c : byte}
    {L : List (Int × Int)} {o m : Int} {x : word}
    (h : ¬ ((d.toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < (d.toNat : Int) + n)) :
    cfill mem0 d n c L x = cfill mem0 d n c ((o, m) :: L) x := by
  unfold cfill
  rw [ms_cov_cons]
  by_cases h1 : (d.toNat : Int) ≤ (x.toNat : Int)
  · have h2 : ¬ ((x.toNat : Int) < (d.toNat : Int) + n) := by
      intro h2'; exact h ⟨h1, h2'⟩
    rw [decide_eq_true_eq.mpr h1, decide_eq_false_iff_not.mpr h2]
    simp
  · rw [decide_eq_false_iff_not.mpr h1]
    simp

/-- Pointwise: the "not this interval" case, when the first two conditions
    hold but the consed interval does not cover [x]. -/
theorem cfill_cons_apply {mem0 : word → Option byte} {d : word} {n : Int} {c : byte}
    {L : List (Int × Int)} {o m : Int} {x : word}
    (h1 : (d.toNat : Int) ≤ (x.toNat : Int))
    (h2 : (x.toNat : Int) < (d.toNat : Int) + n)
    (hb : ms_inb ((x.toNat : Int) - (d.toNat : Int)) (o, m) = false) :
    cfill mem0 d n c L x = cfill mem0 d n c ((o, m) :: L) x := by
  unfold cfill
  rw [ms_cov_cons, hb, decide_eq_true_eq.mpr h1,
    decide_eq_true_eq.mpr h2]
  simp

/-- A store of [m] copies of [c] at offset [o] conses the interval. -/
theorem cfill_store (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (L : List (Int × Int)) (o : Int) (m : Nat)
    (ho : 0 ≤ o) (hm : o + (m : Int) ≤ n) :
    wbytes (cfill mem0 d n c L) (at_ d o) (List.replicate m c)
      = cfill mem0 d n c ((o, (m : Int)) :: L) := by
  funext x
  have hd := u64_range d
  have hx := u64_range x
  have hA : ((at_ d o).toNat : Int) = (d.toNat : Int) + o :=
    at_u d o (by omega) (by omega)
  have hlen : (List.replicate m c).length = m := repeat_length c m
  by_cases hlo : (x.toNat : Int) < (d.toNat : Int) + o
  · -- below the stored interval: the store misses [x]
    rw [wbytes_below (List.replicate m c) (cfill mem0 d n c L) (at_ d o) x
      (by rw [hlen, hA]; omega) (by rw [hA]; omega)]
    by_cases hdx : (d.toNat : Int) ≤ (x.toNat : Int)
    · exact cfill_cons_apply hdx (by omega) (ms_inb_false _ o (m : Int) (by omega))
    · exact cfill_cons_miss (by omega)
  · by_cases hin : (x.toNat : Int) < (d.toNat : Int) + o + (m : Int)
    · -- inside the stored interval: the store writes [c]
      have hidx : ((x.toNat : Int) - ((d.toNat : Int) + o)).toNat < m := by
        have h0 : 0 ≤ (x.toNat : Int) - ((d.toNat : Int) + o) := by omega
        have hcast : (((x.toNat : Int) - ((d.toNat : Int) + o)).toNat : Int)
            = (x.toNat : Int) - ((d.toNat : Int) + o) := Int.toNat_of_nonneg h0
        have h3 : (((x.toNat : Int) - ((d.toNat : Int) + o)).toNat : Int) < (m : Int) := by
          rw [hcast]; omega
        exact_mod_cast h3
      rw [wbytes_inside (List.replicate m c) (cfill mem0 d n c L) (at_ d o) x
        (by rw [hlen, hA]; omega) ⟨by rw [hA]; omega, by rw [hlen, hA]; omega⟩]
      rw [hA, nth_repeat_lt c (BitVec.ofInt 8 0) m _ hidx]
      have hdx : (d.toNat : Int) ≤ (x.toNat : Int) := by omega
      rw [cfill_cons_hit hdx (by omega)
        ((ms_inb_true _ o (m : Int)).mpr (by omega))]
    · -- above the stored interval: the store misses [x]
      rw [wbytes_above (List.replicate m c) (cfill mem0 d n c L) (at_ d o) x
        (by rw [hlen, hA]; omega)]
      by_cases hdx : (d.toNat : Int) ≤ (x.toNat : Int)
      · by_cases h2 : (x.toNat : Int) < (d.toNat : Int) + n
        · exact cfill_cons_apply hdx h2 (ms_inb_false _ o (m : Int) (by omega))
        · exact cfill_cons_miss (by omega)
      · exact cfill_cons_miss (by omega)

/-- Full coverage: the overlay is one constant fill of the range. -/
theorem cfill_full (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (L : List (Int × Int))
    (hcov : ∀ i, 0 ≤ i → i < n → ms_cov L i = true) :
    cfill mem0 d n c L = wbytes mem0 d (List.replicate n.toNat c) := by
  funext x
  have hd := u64_range d
  have hx := u64_range x
  have hn' : (n.toNat : Int) = n := Int.toNat_of_nonneg hn
  have hlen : (List.replicate n.toNat c).length = n.toNat := repeat_length c n.toNat
  unfold cfill
  by_cases h1 : (d.toNat : Int) ≤ (x.toNat : Int)
  · by_cases h2 : (x.toNat : Int) < (d.toNat : Int) + n
    · rw [decide_eq_true_eq.mpr h1, decide_eq_true_eq.mpr h2]
      rw [hcov ((x.toNat : Int) - (d.toNat : Int)) (by omega) (by omega)]
      rw [wbytes_inside (List.replicate n.toNat c) mem0 d x
        (by rw [hlen, hn']; omega) ⟨h1, by rw [hlen, hn']; omega⟩]
      have hidx : ((x.toNat : Int) - (d.toNat : Int)).toNat < n.toNat := by
        have h0 : 0 ≤ (x.toNat : Int) - (d.toNat : Int) := by omega
        have hcast : (((x.toNat : Int) - (d.toNat : Int)).toNat : Int)
            = (x.toNat : Int) - (d.toNat : Int) := Int.toNat_of_nonneg h0
        have h3 : (((x.toNat : Int) - (d.toNat : Int)).toNat : Int) < (n.toNat : Int) := by
          rw [hcast, hn']; omega
        exact_mod_cast h3
      rw [nth_repeat_lt c (BitVec.ofInt 8 0) n.toNat _ hidx]
      simp
    · rw [decide_eq_false_iff_not.mpr h2]
      rw [wbytes_above (List.replicate n.toNat c) mem0 d x (by rw [hlen, hn']; omega)]
      simp
  · rw [decide_eq_false_iff_not.mpr h1]
    rw [wbytes_below (List.replicate n.toNat c) mem0 d x
      (by rw [hlen, hn']; omega) (by omega)]
    simp

/-- The exit form: a chain of the stores done covers `[0,n)`, so the
    overlay is the constant fill. -/
theorem cfill_full_chain (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (L L' : List (Int × Int))
    (hincl : ∀ iv, iv ∈ L' → iv ∈ L) (hc : ms_chain 0 n L') :
    cfill mem0 d n c L = wbytes mem0 d (List.replicate n.toNat c) :=
  cfill_full mem0 d n c hn hnw L
    (fun i h1 h2 => ms_cov_by_chain L L' n hincl hc i ⟨h1, h2⟩)

/-- The destination stays writable through the fill. -/
theorem cfill_store_ok (mem0 : word → Option byte) (d : word) (n : Int) (c : byte)
    (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (segs : List Segment) (L : List (Int × Int)) (o : Int) (m : Nat)
    (hok : store_ok segs mem0 d n.toNat = true)
    (ho : 0 ≤ o) (hm : o + (m : Int) ≤ n) :
    store_ok segs (cfill mem0 d n c L) (at_ d o) m = true := by
  have hd := u64_range d
  have hn' : (n.toNat : Int) = n := Int.toNat_of_nonneg hn
  apply store_ok_mono segs m mem0 (cfill mem0 d n c L) (at_ d o)
  · exact cfill_grows mem0 d n c L
  · apply store_ok_sub segs mem0 d (at_ d o) n.toNat m
    · rw [hn']; omega
    · exact hok
    · rw [at_u d o (by omega) (by omega)]; omega
    · rw [at_u d o (by omega) (by omega), hn']; omega


/-! =====================================================================
    The replicated fill patterns
    ===================================================================== -/

/-- Reducing a modulus by a divisor of the outer one: `j ≤ k` makes
    `2^j` divide `2^k`. -/
theorem mod4_mod_pow2_gen (t : Int) (k j : Nat) (hjk : j ≤ k) :
    (t % (2 : Int) ^ k) % (2 : Int) ^ j = t % (2 : Int) ^ j := by
  rw [← two_pow_natCast k, ← two_pow_natCast j]
  refine Int.emod_emod_of_dvd t ⟨((2 ^ (k - j) : Nat) : Int), ?_⟩
  rw [← Int.natCast_mul]
  congr 1
  rw [← Nat.pow_add]
  congr 1
  omega

/-- The byte an [sb] of register value [cv] stores. -/
def cbyte (cv : word) : byte := BitVec.ofInt 8 (cv.toNat : Int)

/-- Its numeric value. -/
def cbz (cv : word) : Int := (cv.toNat : Int) % 256

/-- `c32 = 0x01010101 * c` (zero-extended in a 64-bit register). -/
def c32 (cv : word) : word := BitVec.ofInt 64 (cbz cv * 16843009)

/-- `c32 << 32`. -/
def c32h (cv : word) : word := BitVec.ofInt 64 (cbz cv * 16843009 * 2 ^ 32)

/-- `c64 = c32 | c32 << 32 = 0x0101010101010101 * c`. -/
def c64 (cv : word) : word := BitVec.ofInt 64 (cbz cv * 72340172838076673)

/-- The byte value is in range. -/
theorem cbz_range (cv : word) : 0 ≤ cbz cv ∧ cbz cv < 256 := by
  unfold cbz
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

/-- Taking the byte of an already-reduced value changes nothing. -/
theorem cbyte_mod (cv : word) : BitVec.ofInt 8 (cbz cv) = cbyte cv := by
  unfold cbyte cbz
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt,
    show ((2 ^ 8 : Nat) : Int) = 256 from by decide]
  congr 1
  exact Int.emod_emod _ 256

/-- [cbyte] through [cbz]. -/
theorem cbyte_cbz (cv : word) : cbyte cv = BitVec.ofInt 8 (cbz cv) :=
  (cbyte_mod cv).symm

/-- `ms_repl k = 1 + 256 + ... + 256^(k-1)`. -/
def ms_repl : Nat → Int
  | 0 => 0
  | k + 1 => 1 + 256 * ms_repl k

theorem ms_repl_nonneg (k : Nat) : 0 ≤ ms_repl k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [ms_repl]; omega

/-- The little-endian byte list of `z * ms_repl k` is [k] copies of [z] (for
    a byte value [z]). -/
theorem Z_to_le_bytes_ms_repl (k : Nat) (z : Int) (hz0 : 0 ≤ z) (hz1 : z < 256) :
    Z_to_le_bytes k (z * ms_repl k) = List.replicate k (BitVec.ofInt 8 z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ms_repl, Z_to_le_bytes, List.replicate_succ]
    have hshape : z * (1 + 256 * ms_repl k) = z + (z * ms_repl k) * 256 := by
      rw [Int.mul_add, Int.mul_one]
      congr 1
      ac_rfl
    have hhead : BitVec.ofInt 8 (z * (1 + 256 * ms_repl k)) = BitVec.ofInt 8 z := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt,
        show ((2 ^ 8 : Nat) : Int) = 256 from by decide]
      congr 1
      have hone : (1 + 256 * ms_repl k) % 256 = 1 := by
        have h0 : (256 * ms_repl k) % 256 = 0 := by
          rw [Int.mul_emod]
          simp
        rw [Int.add_emod, h0, Int.add_zero]
        exact Int.emod_eq_of_lt (by decide) (by decide)
      rw [Int.mul_emod, hone, Int.mul_one, Int.emod_emod]
    have htail : (z * (1 + 256 * ms_repl k)) >>> 8 = z * ms_repl k := by
      rw [hshape, Int.shiftRight_eq_div_pow,
        show ((2 ^ 8 : Nat) : Int) = 256 from by decide,
        Int.add_mul_ediv_right z (z * ms_repl k) (by decide),
        Int.ediv_eq_zero_of_lt hz0 hz1, Int.zero_add]
    rw [hhead, htail, ih]

/-- The unsigned value of [c32]. -/
theorem u_c32 (cv : word) : ((c32 cv).toNat : Int) = cbz cv * 16843009 := by
  unfold c32
  apply u_Z2bv <;> have h := cbz_range cv <;> omega

/-- The unsigned value of [c32h]. -/
theorem u_c32h (cv : word) :
    ((c32h cv).toNat : Int) = cbz cv * 16843009 * 2 ^ 32 := by
  unfold c32h
  apply u_Z2bv <;> have h := cbz_range cv <;> omega

/-- The unsigned value of [c64]. -/
theorem u_c64 (cv : word) :
    ((c64 cv).toNat : Int) = cbz cv * 72340172838076673 := by
  unfold c64
  apply u_Z2bv <;> have h := cbz_range cv <;> omega

/-- `sw` of [c32] stores four copies of the byte. -/
theorem wleb4_c32 (cv : word) :
    word_to_le_bytes 4 (c32 cv) = List.replicate 4 (cbyte cv) := by
  unfold word_to_le_bytes
  rw [u_c32, cbyte_cbz, show (16843009 : Int) = ms_repl 4 from by decide]
  exact Z_to_le_bytes_ms_repl 4 (cbz cv) (cbz_range cv).1 (cbz_range cv).2

/-- `sd` of [c64] stores eight copies of the byte. -/
theorem wleb8_c64 (cv : word) :
    word_to_le_bytes 8 (c64 cv) = List.replicate 8 (cbyte cv) := by
  unfold word_to_le_bytes
  rw [u_c64, cbyte_cbz, show (72340172838076673 : Int) = ms_repl 8 from by decide]
  exact Z_to_le_bytes_ms_repl 8 (cbz cv) (cbz_range cv).1 (cbz_range cv).2

/-- `(a * 2^k) mod 2^m` factors through `a mod 2^(m-k)`. -/
theorem nat_mul_pow_emod (A k m : Nat) (hkm : k ≤ m) :
    (A * 2 ^ k) % 2 ^ m = (A % 2 ^ (m - k)) * 2 ^ k := by
  rw [show 2 ^ m = 2 ^ (m - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega]
  exact Nat.mul_mod_mul_right _ _ _

/-- The integer form of [nat_mul_pow_emod] (`2^k` as a `Nat` cast, the shape
    `zshiftl`/`zshiftr` produce). -/
theorem mul_pow_emod (A : Int) (hA : 0 ≤ A) (k m : Nat) (hkm : k ≤ m) :
    (A * ((2 ^ k : Nat) : Int)) % ((2 ^ m : Nat) : Int)
      = (A % ((2 ^ (m - k) : Nat) : Int)) * ((2 ^ k : Nat) : Int) := by
  have hA' : ((A.toNat : Nat) : Int) = A := Int.toNat_of_nonneg hA
  have hlhs : A * ((2 ^ k : Nat) : Int) = ↑(A.toNat * 2 ^ k) := by
    rw [Int.natCast_mul, hA']
  have hrhs : (A % ((2 ^ (m - k) : Nat) : Int)) * ((2 ^ k : Nat) : Int)
      = ↑((A.toNat % 2 ^ (m - k)) * 2 ^ k) := by
    rw [Int.natCast_mul, Int.natCast_emod, hA']
  rw [hlhs, hrhs, ← Int.natCast_emod, nat_mul_pow_emod A.toNat k m hkm]

/-! ### The code's [slli]/[mulhu]/[srli]/[or] sequence computes the patterns -/

/-- `slli a6,cv,56`: only the low byte survives. -/
theorem u_slli56 (cv : word) : ((v_slli cv 56).toNat : Int) = cbz cv * 2 ^ 56 := by
  unfold v_slli zshiftl cbz
  rw [show (Int.toNat 56) = 56 from by decide, toNat_ofInt_emod, ← two_pow_natCast 64]
  rw [mul_pow_emod (cv.toNat : Int) (Int.natCast_nonneg _) 56 64 (by decide)]
  rw [show ((2 ^ (64 - 56) : Nat) : Int) = 256 from by decide, two_pow_natCast 56]

/-- `mulhu a2, cv<<56, 0x101010100 = c32`. -/
theorem mulhu_c32 (cv : word) (m : word) (hm : (m.toNat : Int) = 4311810304) :
    v_mulhu (v_slli cv 56) m = c32 cv := by
  unfold v_mulhu zshiftr c32
  rw [u_slli56 cv, hm, two_pow_natCast 64]
  have e : cbz cv * (2 : Int) ^ 56 * 4311810304
      = (cbz cv * 16843009) * (2 : Int) ^ 64 := by
    rw [Int.mul_assoc,
      show (2 : Int) ^ 56 * 4311810304 = 16843009 * (2 : Int) ^ 64 from by decide,
      ← Int.mul_assoc]
  rw [e, Int.mul_ediv_cancel _ (by decide)]

/-- `slli (c32), 32 = c32h`. -/
theorem slli32_c32 (cv : word) : v_slli (c32 cv) 32 = c32h cv := by
  unfold v_slli zshiftl c32h
  rw [show (Int.toNat 32) = 32 from by decide, u_c32, two_pow_natCast 32]

/-- `srli (c32h), 32 = c32`. -/
theorem srli32_c32h (cv : word) : v_srli (c32h cv) 32 = c32 cv := by
  unfold v_srli zshiftr c32
  rw [show (Int.toNat 32) = 32 from by decide, u_c32h, two_pow_natCast 32]
  rw [Int.mul_ediv_cancel _ (by decide)]

/-- Bitwise or of shifted-in non-overlapping halves. -/
theorem lor_disjoint_shift32 (a b : Int) (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hb1 : b < 2 ^ 32) : zlor (a * 2 ^ 32) b = a * 2 ^ 32 + b := by
  unfold zlor
  have ha' : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg ha
  have hb' : ((b.toNat : Nat) : Int) = b := Int.toNat_of_nonneg hb0
  have hcast : a * (2 : Int) ^ 32 = ((a.toNat * 2 ^ 32 : Nat) : Int) := by
    rw [Int.natCast_mul, ha', two_pow_natCast]
  have hx : (a * (2 : Int) ^ 32).toNat = a.toNat * 2 ^ 32 := by
    rw [hcast, Int.toNat_natCast]
  have hbnd : b.toNat < 2 ^ 32 := by
    have h : ((b.toNat : Nat) : Int) < ((2 ^ 32 : Nat) : Int) := by
      rw [hb', two_pow_natCast]; exact hb1
    exact_mod_cast h
  have hor : a.toNat * 2 ^ 32 ||| b.toNat = a.toNat * 2 ^ 32 + b.toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.mul_comm a.toNat,
      Nat.testBit_two_pow_mul_add (a.toNat) hbnd i, Nat.testBit_two_pow_mul]
    by_cases hi : i < 32
    · rw [ite_eq_left hi]
      have hge : ¬ (i ≥ 32) := by omega
      simp [hge]
    · rw [ite_eq_right hi]
      have hge : i ≥ 32 := by omega
      have hbit : b.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbnd (Nat.pow_le_pow_right (by decide) hge))
      rw [hbit]
      simp [hge]
  rw [hx, hor, Int.natCast_add, Int.natCast_mul, ha', hb', two_pow_natCast]

/-- `or (c32h, c32) = c64`. -/
theorem or_c64 (cv : word) : v_or (c32h cv) (c32 cv) = c64 cv := by
  have hz := cbz_range cv
  unfold v_or c64
  rw [u_c32h, u_c32]
  have hb : cbz cv * 16843009 < 2 ^ 32 := by omega
  rw [lor_disjoint_shift32 (cbz cv * 16843009) (cbz cv * 16843009) (by omega) (by omega) hb]
  have e1 : cbz cv * 16843009 * (2 : Int) ^ 32 + cbz cv * 16843009
      = cbz cv * (16843009 * (2 : Int) ^ 32) + cbz cv * 16843009 := by
    rw [Int.mul_assoc]
  have e2 : cbz cv * (16843009 * (2 : Int) ^ 32) + cbz cv * 16843009
      = cbz cv * (16843009 * (2 : Int) ^ 32 + 16843009) := by
    rw [← Int.mul_add]
  have e3 : (16843009 : Int) * (2 : Int) ^ 32 + 16843009 = 72340172838076673 := by
    decide
  rw [e1, e2, e3]

/-! =====================================================================
    ALU facts
    ===================================================================== -/

/-- The `andi -4` mask in the `mod 4` form. -/
theorem mod4_mod_pow2' (t : Int) (k : Nat) (hk : 2 ≤ k) :
    (t % (2 : Int) ^ k) % 4 = t % 4 := by
  rw [show (4 : Int) = (2 : Int) ^ 2 from by decide]
  exact mod4_mod_pow2_gen t k 2 hk

/-- `neg_mod4_range`: the alignment padding is a residue. -/
theorem neg_mod4_range (u : Int) : 0 ≤ (-u) % 4 ∧ (-u) % 4 ≤ 3 :=
  ⟨Int.emod_nonneg _ (by decide),
    by have := Int.emod_lt_of_pos (-u) (by decide : (0 : Int) < 4); omega⟩

/-- `neg_mod4_aligns`: the padded address is 4-aligned. -/
theorem neg_mod4_aligns (u : Int) : (u + (-u) % 4) % 4 = 0 := by
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod, show u + -u = 0 by omega,
    Int.zero_emod]

/-- Generic `Z_to_bv 64` arithmetic closers. -/
theorem ms_v_add_Z (x : word) (z : Int) (hz0 : 0 ≤ z) (hz1 : z < 2 ^ 64) :
    v_add x (BitVec.ofInt 64 z) = at_ x z := by
  unfold v_add at_
  rw [u_Z2bv z hz0 hz1]

theorem ms_v_sub_ZZ (a b : Int) (h0 : 0 ≤ b) (h1 : b ≤ a) (h2 : a < 2 ^ 64) :
    v_sub (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = BitVec.ofInt 64 (a - b) := by
  unfold v_sub
  rw [u_Z2bv a (by omega) h2, u_Z2bv b h0 (by omega)]

theorem ms_v_addi_Z (a i : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 64) :
    v_addi (BitVec.ofInt 64 a) i = BitVec.ofInt 64 (a + i) := by
  unfold v_addi
  rw [u_Z2bv a ha0 ha1]

/-- [bv_swrap] only depends on its argument modulo the divisors of `2^(n-1)`. -/
theorem bv_swrap_emod (n : Nat) (z : Int) (k : Int)
    (hk : k ∣ ((2 ^ n : Nat) : Int)) (hk' : k ∣ ((2 ^ (n - 1) : Nat) : Int)) :
    bv_swrap n z % k = z % k := by
  unfold bv_swrap
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, Int.zero_dvd] at hk
    have hp := two_pow_pos_int n
    omega
  rw [Int.sub_emod]
  have hA : ((z + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int)) % k
      = (z + ((2 ^ (n - 1) : Nat) : Int)) % k := Int.emod_emod_of_dvd _ hk
  have hH : ((2 ^ (n - 1) : Nat) : Int) % k = 0 := Int.emod_eq_zero_of_dvd hk'
  rw [hA, hH, Int.sub_zero, Int.emod_emod, Int.add_emod, hH, Int.add_zero,
    Int.emod_emod]

/-- `negw a3,a0; andi a3,a3,3`: the distance to the next 4-aligned address. -/
theorem negw_and3 (x : word) :
    v_andi (v_subw (BitVec.ofInt 64 0) x) 3
      = BitVec.ofInt 64 ((-(x.toNat : Int)) % 4) := by
  have h4_64 : (4 : Int) ∣ ((2 ^ 64 : Nat) : Int) := ⟨((2 ^ 62 : Nat) : Int), by decide⟩
  have h4_32 : (4 : Int) ∣ ((2 ^ 32 : Nat) : Int) := ⟨((2 ^ 30 : Nat) : Int), by decide⟩
  have h4_31 : (4 : Int) ∣ ((2 ^ (32 - 1) : Nat) : Int) := ⟨((2 ^ 29 : Nat) : Int), by decide⟩
  have hW : ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat : Int)
      = bv_swrap 32 (0 - (x.toNat : Int)) % ((2 ^ 64 : Nat) : Int) := toNat_ofInt_emod _
  have hmod : ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat : Int) % 4
      = (-(x.toNat : Int)) % 4 := by
    rw [hW, Int.emod_emod_of_dvd _ h4_64]
    simpa only [Int.zero_sub] using
      bv_swrap_emod 32 (0 - (x.toNat : Int)) 4 h4_32 h4_31
  have hland : zland ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat : Int) 3
      = (-(x.toNat : Int)) % 4 := by
    have h1 : ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat &&& 3)
        = ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat) % 4 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod
        ((BitVec.ofInt 64 (bv_swrap 32 (0 - (x.toNat : Int)))).toNat) 2
    unfold zland
    rw [Int.toNat_natCast, show Int.toNat 3 = 3 from by decide, h1, Int.natCast_emod]
    exact hmod
  unfold v_andi v_subw
  rw [show ((BitVec.ofInt 64 0).toNat : Int) = 0 from by decide,
    show bv_wrap 64 3 = 3 from by decide, hland]

/-- Generic `Z_to_bv 64` arithmetic closer. -/
theorem ms_v_add_at_Z (x : word) (o z : Int) (hz0 : 0 ≤ z) (hz1 : z < 2 ^ 64) :
    v_add (at_ x o) (BitVec.ofInt 64 z) = at_ x (o + z) := by
  rw [ms_v_add_Z (at_ x o) z hz0 hz1, at_at]

/-! =====================================================================
    [_at] step wrappers missing from SeqExec
    ===================================================================== -/

/-- `subw rd, rs1, rs2`, stated at an arbitrary segment list. -/
theorem ms_step_subw_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op32 .SUB rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_subw (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- `mulhu rd, rs1, rs2`, stated at an arbitrary segment list. -/
theorem ms_step_mulhu_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.mul .MULHU rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_mulhu (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- `or rd, rs1, rs2`, stated at an arbitrary segment list. -/
theorem ms_step_or_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op .OR rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_or (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-!  One step of [sb]/[sw]/[sd] into the
    [cfill] overlay conses the stored interval, provided the destination
    stays writable along it ([cfill_store_ok]).  The step lemmas are
    `Common/SeqExec.lean`'s VALUE-precise store steps; [cf_sb] needs no
    [word_to_le_bytes] hypothesis because an [sb] already stores the byte
    [cbyte cv] ([N_to_le_bytes_1_small]).
    ===================================================================== -/

/-- `sb` over a [cfill] memory. -/
theorem cf_sb (segs : List Segment) (mem0 : word → Option byte) (d : word)
    (n : Int) (cv : word) (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (hok : store_ok segs mem0 d n.toNat = true) :
    ∀ (regs : BvMap word) (pc : word) (rom : word → Option byte) (w : BitVec 32)
      (rs1 rs2 : reg) (imm : BitVec 12) (L : List (Int × Int)) (o0 o : Int),
      fetch_word segs pc = some w → is_ecall w = false →
      decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4) →
      getr regs rs1 = at_ d o0 → (o0 + imm.toInt = o) →
      getr regs rs2 = cv → 0 ≤ o → o + 1 ≤ n →
      RiscvSemantics.step segs (mkst regs pc (cfill mem0 d n (cbyte cv) L) rom) =
        .MachineOk (mkst regs (v_addi pc 4)
          (cfill mem0 d n (cbyte cv) ((o, 1) :: L)) rom) := by
  intro regs pc rom w rs1 rs2 imm L o0 o Hf He Hd Hrs1 Ho Hrs2 H0 H1
  have hA : v_addi (at_ d o0) imm.toInt = at_ d o := by
    rw [show v_addi (at_ d o0) imm.toInt = at_ (at_ d o0) imm.toInt from rfl, at_at, Ho]
  have hok0 : store_ok segs (cfill mem0 d n (cbyte cv) L) (at_ d o) 1 = true :=
    cfill_store_ok mem0 d n (cbyte cv) hn hnw segs L o 1 hok H0 (by omega)
  have hok' : store_ok segs (cfill mem0 d n (cbyte cv) L)
      (v_addi (getr regs rs1) imm.toInt) 1 = true := by
    rw [Hrs1, hA]; exact hok0
  have hbytes : word_to_le_bytes 1 cv = List.replicate 1 (cbyte cv) := by
    rw [N_to_le_bytes_1_small]; rfl
  rw [step_sb segs regs pc (cfill mem0 d n (cbyte cv) L) rom w rs1 rs2 imm Hf He Hd hok',
    Hrs1, hA, Hrs2, hbytes, cfill_store mem0 d n (cbyte cv) hnw L o 1 H0 (by omega)]
  rfl

/-- `sw` over a [cfill] memory. -/
theorem cf_sw (segs : List Segment) (mem0 : word → Option byte) (d : word)
    (n : Int) (cv : word) (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (hok : store_ok segs mem0 d n.toNat = true) :
    ∀ (regs : BvMap word) (pc : word) (rom : word → Option byte) (w : BitVec 32)
      (rs1 rs2 : reg) (imm : BitVec 12) (L : List (Int × Int)) (o0 o : Int) (v : word),
      fetch_word segs pc = some w → is_ecall w = false →
      decodeAny w = some (Instr.store .SZ4 rs1 rs2 imm, 4) →
      getr regs rs1 = at_ d o0 → (o0 + imm.toInt = o) →
      getr regs rs2 = v → word_to_le_bytes 4 v = List.replicate 4 (cbyte cv) →
      0 ≤ o → o + 4 ≤ n →
      RiscvSemantics.step segs (mkst regs pc (cfill mem0 d n (cbyte cv) L) rom) =
        .MachineOk (mkst regs (v_addi pc 4)
          (cfill mem0 d n (cbyte cv) ((o, 4) :: L)) rom) := by
  intro regs pc rom w rs1 rs2 imm L o0 o v Hf He Hd Hrs1 Ho Hrs2 Hv H0 H1
  have hA : v_addi (getr regs rs1) imm.toInt = at_ d o := by
    rw [Hrs1]
    rw [show v_addi (at_ d o0) imm.toInt = at_ (at_ d o0) imm.toInt from rfl, at_at, Ho]
  have hok0 : store_ok segs (cfill mem0 d n (cbyte cv) L) (at_ d o) 4 = true :=
    cfill_store_ok mem0 d n (cbyte cv) hn hnw segs L o 4 hok H0 (by omega)
  rw [step_sw_at segs regs pc (cfill mem0 d n (cbyte cv) L) rom w rs1 rs2 imm
    (at_ d o) v Hf He Hd hA Hrs2 hok0, Hv,
    cfill_store mem0 d n (cbyte cv) hnw L o 4 H0 (by omega)]
  rfl

/-- `sd` over a [cfill] memory. -/
theorem cf_sd (segs : List Segment) (mem0 : word → Option byte) (d : word)
    (n : Int) (cv : word) (hn : 0 ≤ n) (hnw : (d.toNat : Int) + n < 2 ^ 64)
    (hok : store_ok segs mem0 d n.toNat = true) :
    ∀ (regs : BvMap word) (pc : word) (rom : word → Option byte) (w : BitVec 32)
      (rs1 rs2 : reg) (imm : BitVec 12) (L : List (Int × Int)) (o0 o : Int) (v : word),
      fetch_word segs pc = some w → is_ecall w = false →
      decodeAny w = some (Instr.store .SZ8 rs1 rs2 imm, 4) →
      getr regs rs1 = at_ d o0 → (o0 + imm.toInt = o) →
      getr regs rs2 = v → word_to_le_bytes 8 v = List.replicate 8 (cbyte cv) →
      0 ≤ o → o + 8 ≤ n →
      RiscvSemantics.step segs (mkst regs pc (cfill mem0 d n (cbyte cv) L) rom) =
        .MachineOk (mkst regs (v_addi pc 4)
          (cfill mem0 d n (cbyte cv) ((o, 8) :: L)) rom) := by
  intro regs pc rom w rs1 rs2 imm L o0 o v Hf He Hd Hrs1 Ho Hrs2 Hv H0 H1
  have hA : v_addi (getr regs rs1) imm.toInt = at_ d o := by
    rw [Hrs1]
    rw [show v_addi (at_ d o0) imm.toInt = at_ (at_ d o0) imm.toInt from rfl, at_at, Ho]
  have hok0 : store_ok segs (cfill mem0 d n (cbyte cv) L) (at_ d o) 8 = true :=
    cfill_store_ok mem0 d n (cbyte cv) hn hnw segs L o 8 hok H0 (by omega)
  rw [step_sd_at segs regs pc (cfill mem0 d n (cbyte cv) L) rom w rs1 rs2 imm
    (at_ d o) v Hf He Hd hA Hrs2 hok0, Hv,
    cfill_store mem0 d n (cbyte cv) hnw L o 8 H0 (by omega)]
  rfl

/-! =====================================================================
    Register preservation: everything but a1..a6
    ===================================================================== -/

/-- The registers the memset summary may clobber: a1..a6. -/
def ms_clob : List reg := [11, 12, 13, 14, 15, 16]

/-- The registers a leaf routine must preserve for its C caller . -/
def callee_kept : List reg :=
  [1, 2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- [keeps regs regs']: every callee-kept register reads the same. -/
def keeps (regs regs' : BvMap word) : Prop :=
  ∀ r, r ∈ callee_kept → getr regs' r = getr regs r

/-- Two register files agree outside a register set . -/
def regs_agree (C : reg → Prop) (regs regs' : BvMap word) : Prop :=
  ∀ r, ¬ C r → getr regs' r = getr regs r

theorem regs_agree_refl (C : reg → Prop) (regs : BvMap word) :
    regs_agree C regs regs :=
  fun _ _ => rfl

theorem regs_agree_trans (C : reg → Prop) {r1 r2 r3 : BvMap word}
    (h12 : regs_agree C r1 r2) (h23 : regs_agree C r2 r3) : regs_agree C r1 r3 :=
  fun r hr => (h23 r hr).trans (h12 r hr)

theorem regs_agree_upd (C : reg → Prop) {regs regs' : BvMap word} (r : reg) (v : word)
    (hin : C r) (h : regs_agree C regs regs') : regs_agree C regs (regupd regs' r v) := by
  intro s hs
  rw [getr_other regs' r v s (by intro hsr; subst hsr; exact hs hin)]
  exact h s hs

theorem keeps_refl (regs : BvMap word) : keeps regs regs :=
  fun _ _ => rfl

theorem keeps_trans {r1 r2 r3 : BvMap word}
    (h12 : keeps r1 r2) (h23 : keeps r2 r3) : keeps r1 r3 :=
  fun r hr => (h23 r hr).trans (h12 r hr)

/-- Two register files agree outside [ms_clob]. -/
def ms_agree (regs regs' : BvMap word) : Prop :=
  regs_agree (fun r => r ∈ ms_clob) regs regs'

theorem ms_agree_refl (regs : BvMap word) : ms_agree regs regs :=
  regs_agree_refl _ regs

theorem ms_agree_trans {r1 r2 r3 : BvMap word}
    (h12 : ms_agree r1 r2) (h23 : ms_agree r2 r3) : ms_agree r1 r3 :=
  regs_agree_trans _ h12 h23

theorem ms_agree_upd {regs regs' : BvMap word} (rd : reg) (v : word)
    (h : ms_agree regs regs') (hin : rd ∈ ms_clob) :
    ms_agree regs (regupd regs' rd v) :=
  regs_agree_upd _ rd v hin h

theorem ms_agree_getr {regs regs' : BvMap word} (r : reg)
    (h : ms_agree regs regs') (hn : r ∉ ms_clob) : getr regs' r = getr regs r :=
  h r hn

/-- [ms_clob] and [callee_kept] are disjoint (checked by computation on the
    two literal lists). -/
theorem ms_clob_not_callee_kept : ∀ r : reg, r ∈ ms_clob → r ∉ callee_kept := by
  intro r h1 h2
  simp only [ms_clob, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd h2 (by decide)

theorem ms_agree_keeps {regs regs' : BvMap word} (h : ms_agree regs regs') :
    keeps regs regs' := by
  intro r hr
  exact h r (fun hc => ms_clob_not_callee_kept r hc hr)

/-- `in_clob`: prove `r ∈ ms_clob` for a literal register . -/
macro "in_clob" : tactic => `(tactic| decide)

/-- `solve_ms_agree`: close `ms_agree regs (regupd .. -/
macro "solve_ms_agree" : tactic =>
  `(tactic|
    (repeat (apply ms_agree_upd)) <;>
      first
        | exact ms_agree_refl _
        | assumption
        | decide)

/-- Sanity check of the macro, mirroring  usage shape. -/
example (regs regs' : BvMap word) (v1 v2 : word) (h : ms_agree regs regs') :
    ms_agree regs (regupd (regupd regs' 11 v1) 12 v2) := by
  solve_ms_agree


theorem cbyte_Z (z : Int) : cbyte (BitVec.ofInt 64 z) = BitVec.ofInt 8 z := by
  unfold cbyte
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  rw [show (((z % ((2 ^ 64 : Nat) : Int)).toNat) : Int) = z % ((2 ^ 64 : Nat) : Int)
    from Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rw [show ((2 ^ 64 : Nat) : Int) = ((2 ^ 8 : Nat) : Int) * ((2 ^ 56 : Nat) : Int) from by
    rw [← Int.natCast_mul, show 2 ^ 8 * 2 ^ 56 = 2 ^ 64 by rw [← Nat.pow_add]]]
  congr 1
  exact Int.emod_emod_of_dvd z ⟨((2 ^ 56 : Nat) : Int), rfl⟩


/-- `andi x, 4` is 0 or 4. -/
theorem land_4_cases (a : Int) (ha : 0 ≤ a) : zland a 4 = 0 ∨ zland a 4 = 4 := by
  unfold zland
  rw [show (Int.toNat (4 : Int)) = 4 from by decide]
  have hbit : ∀ i, (4 : Nat).testBit i = decide (i = 2) := by
    intro i
    rw [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]
  have hmain : a.toNat &&& 4 = if a.toNat.testBit 2 then 4 else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, hbit i]
    by_cases hi : i = 2
    · subst hi
      by_cases hb : a.toNat.testBit 2 = true
      · rw [ite_eq_left hb]
        simp [hbit, hb]
      · rw [ite_eq_right hb]
        simp [hbit, hb, Nat.zero_testBit]
    · rw [decide_eq_false_iff_not.mpr hi, Bool.and_false]
      by_cases hb : a.toNat.testBit 2 = true
      · rw [ite_eq_left hb]
        simp [hbit, decide_eq_false_iff_not.mpr hi]
      · rw [ite_eq_right hb]
        simp [Nat.zero_testBit]
  rw [hmain]
  by_cases hb : a.toNat.testBit 2 = true
  · right; rw [ite_eq_left hb]; rfl
  · left; rw [ite_eq_right hb]; rfl

/-- `andi x, 4` is 0 or 4, in word form. -/
theorem andi_4_cases (x : word) :
    ∃ s4 : Int, v_andi x 4 = BitVec.ofInt 64 s4 ∧ (s4 = 0 ∨ s4 = 4) := by
  refine ⟨zland (x.toNat : Int) 4, ?_, land_4_cases _ (Int.natCast_nonneg _)⟩
  unfold v_andi
  rw [show bv_wrap 64 4 = 4 from by decide]


/-- `andi x, -4` truncates to a multiple of 4 (Nat form, by bit
    extensionality). -/
theorem nat_land_trunc4 (A : Nat) (hA : A < 2 ^ 64) : A &&& (2 ^ 64 - 4) = A - A % 4 := by
  have hmask : ∀ i, (2 ^ 64 - 4).testBit i = decide (2 ≤ i ∧ i < 64) := by
    intro i
    have hsub : (2 ^ 64 - 4 : Nat) = 2 ^ 64 - (3 + 1) := by omega
    rw [hsub, Nat.testBit_two_pow_sub_succ (by decide : 3 < 2 ^ 64) i,
      show (3 : Nat).testBit i = decide (i < 2) from Nat.testBit_two_pow_sub_one 2 i]
    by_cases h2 : i < 2
    · have h64 : i < 64 := by omega
      simp [h2, h64]
    · by_cases h64 : i < 64
      · simp [h2, h64]; omega
      · have hnot : ¬ (2 ≤ i ∧ i < 64) := by omega
        rw [decide_eq_false_iff_not.mpr hnot, decide_eq_false_iff_not.mpr h64]
        simp
  have hsplit : A - A % 4 = 2 ^ 2 * (A / 4) := by
    have := Nat.div_add_mod A 4
    omega
  have hdecomp : A = 2 ^ 2 * (A / 4) + A % 4 := by
    have := Nat.div_add_mod A 4
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hsplit, Nat.testBit_two_pow_mul, Nat.testBit_and, hmask i,
    show A.testBit i = (2 ^ 2 * (A / 4) + A % 4).testBit i from by rw [← hdecomp],
    Nat.testBit_two_pow_mul_add (A / 4) (b := A % 4) (by omega) i]
  by_cases h2 : i < 2
  · have h2' : ¬ (2 ≤ i) := by omega
    simp [h2, h2']
  · have h2' : 2 ≤ i := by omega
    by_cases h64 : i < 64
    · simp [h2, h64, h2']
    · have h64' : ¬ (i < 64) := h64
      have hqi : A / 4 < 2 ^ (i - 2) := by
        have hq : A / 4 < 2 ^ 62 := by
          have h4 : 2 ^ 62 * 4 = 2 ^ 64 := by decide
          omega
        exact Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega))
      simp [h2, h64, h2', Nat.testBit_lt_two_pow hqi]


/-- `andi x, -4` truncates to a multiple of 4. -/
theorem land_trunc4 (a : Int) (ha0 : 0 ≤ a) (ha1 : a < 2 ^ 64) :
    zland a (2 ^ 64 - 4) = a - a % 4 := by
  have ha : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg ha0
  have hA : a.toNat < 2 ^ 64 := by omega
  have hmask : ((2 : Int) ^ 64 - 4) = (((2 ^ 64 - 4 : Nat)) : Int) := by
    rw [Int.natCast_sub (by decide), two_pow_natCast]
    simp
  unfold zland
  rw [hmask]
  rw [show (Int.toNat (((2 ^ 64 - 4 : Nat)) : Int)) = (2 ^ 64 - 4 : Nat) from by simp]
  rw [nat_land_trunc4 a.toNat hA, Int.natCast_sub (by omega), Int.natCast_emod, ← ha]
  rw [show (((4 : Nat)) : Int) = 4 from rfl]
  simp only [Int.toNat_natCast]

/-- `andi m, -4` on a `Z_to_bv 64` value. -/
theorem andi_m4 (m : Int) (hm0 : 0 ≤ m) (hm1 : m < 2 ^ 64) :
    v_andi (BitVec.ofInt 64 m) (-4) = BitVec.ofInt 64 (m - m % 4) := by
  unfold v_andi
  rw [show ((BitVec.ofInt 64 m).toNat : Int) = m from u_Z2bv m hm0 hm1,
    show bv_wrap 64 (-4) = 2 ^ 64 - 4 from by decide, land_trunc4 m hm0 hm1]

end LinuxSem.Common.MemsetLib
