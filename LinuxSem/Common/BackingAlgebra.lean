/-
  * LinuxSem.Common.BackingAlgebra — a counting-measure semantics
    for the backed-memory meter `State.vm_backing_used`, and the budget bounds
    the memory-syscall nodes need.

  Image-INDEPENDENT; depends only on the specification.

  `vm_backing_used m = live_bytes (maps_subtract_all (maps_subtract_all
  maps noaccess) lazy) + 4096 * |materialized|`.  Every anonymous-memory
  arm rewrites `noaccess` / `lazy` / `materialized` by interval
  subtraction (`maps_subtract`) and consing; comparing the meter before
  and after STRUCTURALLY is hopeless (the lists are re-split), so this
  file reads `live_bytes (maps_subtract_all l cuts)` SEMANTICALLY:

    live_bytes (maps_subtract_all l cuts) = Σ_{I ∈ l} #{x ∈ I | x ∉ ∪cuts}

  (`live_msa`, under the well-formedness every reachable ledger has:
  interval ends at most 2^64), with # the finite count `zcount`.  The
  bounds follow by pointwise reasoning on the cover predicates:

  - `backing_forget_commit_le`  (rw MAP_FIXED commit without NORESERVE,
    row E, and its cousin `backing_mprotect_le`, row M): exposing
    `[lo, hi)` costs at most the bytes of `vm_maps` inside `[lo, hi)`
    (`overlap_sum`), i.e. at most `hi - lo` when only one tracked mapping
    meets the range;
  - `backing_recommit_lazy_le` (rw MAP_FIXED|NORESERVE over a tracked
    mapping, row F): the meter does not increase.

  NOTES (deviations, all notation only unless stated):

  - Values are `Int`, counts `Nat`, words/bytes `BitVec n`; a word read as
    an `Int` is `(w.toNat : Int)` and `BitVec.ofInt 64 z` makes one from an
    `Int`.  `!` is `Bool.not`, `&&`/`||` are the Bool connectives, the
    comparisons are `decide (· = ·)` / `decide (· < ·)` / `decide (· ≤ ·)`,
    and the list side is `min`/`max`/`.toNat`, `List.any`, `List.filter`.
  - `in_rng_tf` is not a tactic here: it is replaced by the pointwise
    lemmas `in_rng_eq_false_of_lt` / `_of_le` / `_empty` and
    `in_rng_eq_true` (with `in_rng_true_iff` / `in_rng_false_iff` for the
    boolean cover identities), each used at exactly the same places.  The
    `destruct …; congruence` steps at the end of the cover proofs become
    the small Bool lemmas `not_or_or_both`, `not_or_or_left` and
    `recommit_cover_le`, and the point-set identity behind
    `iv_subtract`'s third clause is named `covered_iv_subtract_pts`.
  - The twelve projection lemmas below are `@[simp]` (they are `rfl`), so
    steps that would be written `simp only [model_proj]` are `simp`/`rfl`.
  - Two `toNat` round trips are named here: `ofInt_toNat`
    (`ofInt 64 w.toNat = w`) and `toNat_ofInt_le` (`ofInt` never increases
    a non-negative value), which is what `lazy_interior_wf` uses instead of
    an exact no-wrap argument.
  - `init_sp_ok` comes from `Common/AsanCeil.lean`; the fourth conjunct of
    `model_ivs_wf` is that invariant, and the two lemmas that carry it are
    `init_sp_ok_same` / `init_sp_ok_init_model`.
-/
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.StateInit
import LinuxSem.Common.AsanCeil
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Run

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect

namespace LinuxSem.Common.BackingAlgebra

/- =========================================================================
   Finite counting
   ========================================================================= -/

/-- The number of integers in `[lo, lo + n)` on which `P` holds.

    A COUNT rather than a length: `live_bytes` measures bytes, and a ledger
    entry's byte extent is a `Z` (`bv_unsigned`), so the pieces the interval
    algebra produces have to be counted in `Z` too. -/
def zcount (P : Int → Bool) (lo : Int) (n : Nat) : Int :=
  match n with
  | 0 => 0
  | k + 1 => (if P lo then 1 else 0) + zcount P (lo + 1) k

theorem zcount_nonneg (P : Int → Bool) (lo : Int) (n : Nat) : 0 ≤ zcount P lo n := by
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have := ih (lo + 1)
      simp only [zcount]
      split <;> omega

theorem zcount_le_len (P : Int → Bool) (lo : Int) (n : Nat) :
    zcount P lo n ≤ (n : Int) := by
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have := ih (lo + 1)
      simp only [zcount]
      split <;> omega

theorem zcount_mono (P Q : Int → Bool) (lo : Int) (n : Nat)
    (H : ∀ x, lo ≤ x → x < lo + (n : Int) → P x = true → Q x = true) :
    zcount P lo n ≤ zcount Q lo n := by
  -- the per-point step, as a Bool fact, so the induction stays arithmetic
  have key : ∀ p q : Bool, (p = true → q = true) →
      (if p = true then (1 : Int) else 0) ≤ (if q = true then 1 else 0) := by
    intro p q hb
    cases p <;> cases q <;> simp_all
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have hk := ih (lo + 1) (fun x h1 h2 hP => H x (by omega) (by omega) hP)
      have hstep := key (P lo) (Q lo) (H lo (by omega) (by omega))
      simp only [zcount]
      omega

theorem zcount_ext (P Q : Int → Bool) (lo : Int) (n : Nat)
    (H : ∀ x, lo ≤ x → x < lo + (n : Int) → P x = Q x) :
    zcount P lo n = zcount Q lo n := by
  have h1 := zcount_mono P Q lo n (fun x h1 h2 hP => by rw [← H x h1 h2]; exact hP)
  have h2 := zcount_mono Q P lo n (fun x h1 h2 hQ => by rw [H x h1 h2]; exact hQ)
  omega

/-- Union bound / disjoint additivity. -/
theorem zcount_or_le (P Q : Int → Bool) (lo : Int) (n : Nat) :
    zcount (fun x => P x || Q x) lo n ≤ zcount P lo n + zcount Q lo n := by
  have key : ∀ p q : Bool,
      (if (p || q) = true then (1 : Int) else 0)
        ≤ (if p = true then 1 else 0) + (if q = true then 1 else 0) := by
    intro p q
    cases p <;> cases q <;> decide
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have hk := ih (lo + 1)
      have hstep := key (P lo) (Q lo)
      simp only [zcount]
      omega

theorem zcount_and_split (P Q : Int → Bool) (lo : Int) (n : Nat) :
    zcount P lo n
      = zcount (fun x => P x && Q x) lo n + zcount (fun x => P x && !(Q x)) lo n := by
  have key : ∀ p q : Bool,
      (if p = true then (1 : Int) else 0)
        = (if (p && q) = true then 1 else 0) + (if (p && !q) = true then 1 else 0) := by
    intro p q
    cases p <;> cases q <;> decide
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have hk := ih (lo + 1)
      have hstep := key (P lo) (Q lo)
      simp only [zcount]
      omega

theorem zcount_const_false (lo : Int) (n : Nat) : zcount (fun _ => false) lo n = 0 := by
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih => simp [zcount, ih]

theorem zcount_const_true (lo : Int) (n : Nat) :
    zcount (fun _ => true) lo n = (n : Int) := by
  induction n generalizing lo with
  | zero => simp [zcount]
  | succ k ih => simp [zcount, ih]; omega

theorem zcount_false (P : Int → Bool) (lo : Int) (n : Nat)
    (H : ∀ x, lo ≤ x → x < lo + (n : Int) → P x = false) :
    zcount P lo n = 0 := by
  rw [zcount_ext P (fun _ => false) lo n H]
  exact zcount_const_false lo n

theorem zcount_true (P : Int → Bool) (lo : Int) (n : Nat)
    (H : ∀ x, lo ≤ x → x < lo + (n : Int) → P x = true) :
    zcount P lo n = (n : Int) := by
  rw [zcount_ext P (fun _ => true) lo n H]
  exact zcount_const_true lo n

/-- Splitting the range. -/
theorem zcount_split (P : Int → Bool) (lo : Int) (n1 n2 : Nat) :
    zcount P lo (n1 + n2) = zcount P lo n1 + zcount P (lo + (n1 : Int)) n2 := by
  induction n1 generalizing lo with
  | zero => simp [zcount]
  | succ k ih =>
      have hk := ih (lo + 1)
      have hcast : lo + ((k + 1 : Nat) : Int) = lo + 1 + (k : Int) := by omega
      rw [Nat.succ_add, hcast]
      simp only [zcount]
      rw [hk]
      omega

/- =========================================================================
   Intervals as predicates
   ========================================================================= -/

/-- Base address of a ledger interval, read unsigned. -/
def B (p : word × word) : Int := (p.1.toNat : Int)

/-- Size of a ledger interval, read unsigned. -/
def S (p : word × word) : Int := (p.2.toNat : Int)

/-- Membership of `x` in the half-open range `[lo, hi)`. -/
def in_rng (lo hi x : Int) : Bool := decide (lo ≤ x) && decide (x < hi)

/-- Membership of `x` in a ledger interval. -/
def in_iv (p : word × word) (x : Int) : Bool := in_rng (B p) (B p + S p) x

/-- Membership of `x` in the union of a ledger. -/
def covered (C : List (word × word)) (x : Int) : Bool := C.any (fun c => in_iv c x)

/-- The count of an interval's points satisfying `P`. -/
def iv_count (P : Int → Bool) (p : word × word) : Int := zcount P (B p) (S p).toNat

/-- Well-formed interval: its end does not pass 2^64 (every reachable ledger
    entry ends at or below `alloc_ceiling`). -/
def iv_wf (p : word × word) : Prop := B p + S p ≤ 2 ^ 64

theorem B_range (p : word × word) : 0 ≤ B p ∧ B p < 2 ^ 64 :=
  bv_unsigned_range_u64 p.1

theorem S_range (p : word × word) : 0 ≤ S p ∧ S p < 2 ^ 64 :=
  bv_unsigned_range_u64 p.2

theorem fg_lit (z : Int) (hz : 0 ≤ z ∧ z < 2 ^ 64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  bv_unsigned_Z_to_bv_u64 z (by simpa [two_pow_64] using hz)

/- -------------------------------------------------------------------------
   live_bytes as a count
   ------------------------------------------------------------------------- -/

theorem live_bytes_app (l1 l2 : List (word × word)) :
    live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2 := by
  induction l1 with
  | nil => simp [live_bytes]
  | cons hd tl ih =>
      obtain ⟨a, s⟩ := hd
      simp only [List.cons_append, live_bytes]
      rw [ih]
      omega

theorem maps_subtract_app (l1 l2 : List (word × word)) (lo hi : Int) :
    maps_subtract (l1 ++ l2) lo hi
      = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi := by
  induction l1 with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      simp only [List.cons_append, maps_subtract, ih, List.append_assoc]

theorem maps_subtract_all_app :
    ∀ (C l1 l2 : List (word × word)),
      maps_subtract_all (l1 ++ l2) C
        = maps_subtract_all l1 C ++ maps_subtract_all l2 C := by
  intro C
  induction C with
  | nil => intro l1 l2; rfl
  | cons hd C ih =>
      obtain ⟨a, n⟩ := hd
      intro l1 l2
      simp only [maps_subtract_all]
      rw [maps_subtract_app]
      exact ih _ _

theorem maps_subtract_all_nil_l (C : List (word × word)) :
    maps_subtract_all [] C = [] := by
  induction C with
  | nil => rfl
  | cons hd C ih =>
      obtain ⟨a, n⟩ := hd
      simp only [maps_subtract_all]
      exact ih

theorem maps_subtract_all_cons_l (p : word × word) (l C : List (word × word)) :
    maps_subtract_all (p :: l) C = maps_subtract_all [p] C ++ maps_subtract_all l C := by
  have h : (p :: l) = [p] ++ l := rfl
  rw [h]
  exact maps_subtract_all_app C [p] l

/-- Sums of counts over a ledger. -/
def sum_count (P : Int → Bool) (l : List (word × word)) : Int :=
  match l with
  | [] => 0
  | q :: r => iv_count P q + sum_count P r

theorem sum_count_app (P : Int → Bool) (l1 l2 : List (word × word)) :
    sum_count P (l1 ++ l2) = sum_count P l1 + sum_count P l2 := by
  induction l1 with
  | nil => simp [sum_count]
  | cons hd tl ih =>
      simp only [List.cons_append, sum_count]
      rw [ih]
      omega

theorem sum_count_nonneg (P : Int → Bool) (l : List (word × word)) :
    0 ≤ sum_count P l := by
  induction l with
  | nil => simp [sum_count]
  | cons a l ih =>
      have := zcount_nonneg P (B a) (S a).toNat
      simp only [sum_count, iv_count]
      omega

theorem sum_count_mono (P Q : Int → Bool) (l : List (word × word))
    (H : ∀ x, P x = true → Q x = true) : sum_count P l ≤ sum_count Q l := by
  induction l with
  | nil => simp [sum_count]
  | cons a l ih =>
      have hh : iv_count P a ≤ iv_count Q a := by
        unfold iv_count
        exact zcount_mono P Q (B a) (S a).toNat (fun x _ _ hx => H x hx)
      simp only [sum_count]
      omega

theorem sum_count_ext (P Q : Int → Bool) (l : List (word × word))
    (H : ∀ x, P x = Q x) : sum_count P l = sum_count Q l := by
  induction l with
  | nil => simp [sum_count]
  | cons a l ih =>
      have hh : iv_count P a = iv_count Q a := by
        unfold iv_count
        exact zcount_ext P Q (B a) (S a).toNat (fun x _ _ => H x)
      simp only [sum_count]
      rw [hh, ih]

theorem sum_count_or_le (P Q : Int → Bool) (l : List (word × word)) :
    sum_count (fun x => P x || Q x) l ≤ sum_count P l + sum_count Q l := by
  induction l with
  | nil => simp [sum_count]
  | cons a l ih =>
      have hh : iv_count (fun x => P x || Q x) a ≤ iv_count P a + iv_count Q a := by
        unfold iv_count
        exact zcount_or_le P Q (B a) (S a).toNat
      simp only [sum_count]
      omega

theorem live_bytes_sum_count (l : List (word × word)) :
    live_bytes l = sum_count (fun _ => true) l := by
  induction l with
  | nil => simp [live_bytes, sum_count]
  | cons hd l ih =>
      obtain ⟨b, s⟩ := hd
      have hs : (((s.toNat : Int)).toNat : Int) = (s.toNat : Int) :=
        Int.toNat_of_nonneg (by omega)
      simp only [live_bytes, sum_count, iv_count, B, S, zcount_const_true, hs]
      rw [ih]

/-- Every interval of a ledger is well formed. -/
def ivs_wf (l : List (word × word)) : Prop := ∀ q, q ∈ l → iv_wf q

theorem ivs_wf_nil : ivs_wf ([] : List (word × word)) := by
  intro q hq
  simp at hq

theorem ivs_wf_cons (p : word × word) (l : List (word × word))
    (Hp : iv_wf p) (Hl : ivs_wf l) : ivs_wf (p :: l) := by
  intro q hq
  rcases List.mem_cons.mp hq with h | h
  · rw [h]; exact Hp
  · exact Hl q h

theorem ivs_wf_cons_inv (p : word × word) (l : List (word × word))
    (H : ivs_wf (p :: l)) : iv_wf p ∧ ivs_wf l := by
  refine ⟨H p (by simp), ?_⟩
  intro q hq
  exact H q (by simp [hq])

theorem ivs_wf_app (l1 l2 : List (word × word))
    (H1 : ivs_wf l1) (H2 : ivs_wf l2) : ivs_wf (l1 ++ l2) := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact H1 q h
  · exact H2 q h

theorem ivs_wf_app_inv (l1 l2 : List (word × word))
    (H : ivs_wf (l1 ++ l2)) : ivs_wf l1 ∧ ivs_wf l2 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    exact H q (List.mem_append.mpr (Or.inl hq))
  · intro q hq
    exact H q (List.mem_append.mpr (Or.inr hq))

theorem ivs_wf_filter (f : word × word → Bool) (l : List (word × word))
    (H : ivs_wf l) : ivs_wf (List.filter f l) := by
  intro q hq
  exact H q (List.mem_filter.mp hq).1

theorem iv_wf_intro (a n : word)
    (H : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) : iv_wf (a, n) := H


/- -------------------------------------------------------------------------
   Pointwise facts about `in_rng`
   ------------------------------------------------------------------------- -/

theorem in_rng_true_iff (lo hi x : Int) : in_rng lo hi x = true ↔ lo ≤ x ∧ x < hi := by
  unfold in_rng
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

theorem in_rng_false_iff (lo hi x : Int) : in_rng lo hi x = false ↔ ¬(lo ≤ x ∧ x < hi) := by
  unfold in_rng
  rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  constructor <;> intro h <;> omega

theorem in_rng_eq_false_of_lt {lo hi x : Int} (h : x < lo) : in_rng lo hi x = false :=
  in_rng_false_iff lo hi x |>.mpr (by omega)

theorem in_rng_eq_false_of_le {lo hi x : Int} (h : hi ≤ x) : in_rng lo hi x = false :=
  in_rng_false_iff lo hi x |>.mpr (by omega)

theorem in_rng_eq_true {lo hi x : Int} (h1 : lo ≤ x) (h2 : x < hi) :
    in_rng lo hi x = true :=
  in_rng_true_iff lo hi x |>.mpr ⟨h1, h2⟩

/-- `min`/`max` at the `Z` level, as the two `<>=-`-free facts the cover
    identities need (Lean core has `Int.lt_min` but not these). -/
theorem max_le_iff (a b c : Int) : max b c ≤ a ↔ b ≤ a ∧ c ≤ a := by
  rw [Int.max_def]; split <;> omega

theorem lt_min_iff (a b c : Int) : a < min b c ↔ a < b ∧ a < c := Int.lt_min

/-- Counting the points of `[A, A+Z)` outside `[lo, hi)`.

    The two pieces of a subtraction are exactly the parts below `lo` and
    above `hi`, so the count of the remnant is a sum of two counts of
    sub-ranges.  This is the arithmetic behind `iv_subtract`'s counting
    clause, and it is stated in `min`/`max` form so that it matches the two
    `if`s of `iv_subtract` syntactically.

    `_HZ` is the hypothesis that the extent is non-negative.  The
    case analysis below derives each piece's non-negativity from the branch
    assumptions (the `toNat` splits), so the hypothesis is kept only to
    preserve the signature. -/
theorem count_outside_gen (P : Int → Bool) (lo hi A Z_ : Int)
    (_HZ : 0 ≤ Z_) (Hlh : lo ≤ hi) :
    zcount (fun x => P x && !(in_rng lo hi x)) A Z_.toNat
      = (if A < lo then zcount P A (min Z_ (lo - A)).toNat else 0)
        + (if hi < A + Z_ then zcount P (max A hi) (A + Z_ - max A hi).toNat else 0) := by
  by_cases hEl : A < lo
  · by_cases hEr : hi < A + Z_
    · -- both: the remnants are `[A, lo)` and `[hi, A+Z)`
      have hm1 : 0 ≤ lo - A := by omega
      have hm2 : 0 ≤ hi - lo := by omega
      have hm3 : 0 ≤ A + Z_ - hi := by omega
      have hmn : min Z_ (lo - A) = lo - A := by
        rw [Int.min_def]; split <;> omega
      have hmx : max A hi = hi := by
        rw [Int.max_def]; split <;> omega
      have hZeq : Z_ = (lo - A) + ((hi - lo) + (A + Z_ - hi)) := by omega
      have htoNat : Z_.toNat
          = (lo - A).toNat + ((hi - lo).toNat + (A + Z_ - hi).toNat) := by
        calc Z_.toNat
            = ((lo - A) + ((hi - lo) + (A + Z_ - hi))).toNat :=
                congrArg Int.toNat (by omega)
          _ = (lo - A).toNat + ((hi - lo) + (A + Z_ - hi)).toNat :=
                Int.toNat_add hm1 (by omega)
          _ = (lo - A).toNat + ((hi - lo).toNat + (A + Z_ - hi).toNat) := by
                rw [Int.toNat_add (by omega) (by omega)]
      have h1 : ((lo - A).toNat : Int) = lo - A := Int.toNat_of_nonneg hm1
      have h2 : ((hi - lo).toNat : Int) = hi - lo := Int.toNat_of_nonneg hm2
      have hb2 : A + ((lo - A).toNat : Int) = lo := by rw [h1]; omega
      have hb3 : lo + ((hi - lo).toNat : Int) = hi := by rw [h2]; omega
      have e1 : zcount (fun x => P x && !(in_rng lo hi x)) A (lo - A).toNat
          = zcount P A (lo - A).toNat := by
        apply zcount_ext
        intro x hx1 hx2
        rw [h1] at hx2
        rw [in_rng_eq_false_of_lt (by omega)]
        simp
      have e2 : zcount (fun x => P x && !(in_rng lo hi x)) lo (hi - lo).toNat = 0 := by
        apply zcount_false
        intro x hx1 hx2
        rw [h2] at hx2
        rw [in_rng_eq_true hx1 (by omega)]
        simp
      have e3 : zcount (fun x => P x && !(in_rng lo hi x)) hi (A + Z_ - hi).toNat
          = zcount P hi (A + Z_ - hi).toNat := by
        apply zcount_ext
        intro x hx1 hx2
        rw [in_rng_eq_false_of_le hx1]
        simp
      rw [htoNat, zcount_split, zcount_split, hb2, hb3,
        ite_eq_left hEl, ite_eq_left hEr, hmn, hmx, e1, e2, e3]
      omega
    · by_cases h2a : A + Z_ ≤ lo
      · -- left only, entirely below `lo`: nothing was cut
        have hmn : min Z_ (lo - A) = Z_ := by
          rw [Int.min_def]; split <;> omega
        have e1 : zcount (fun x => P x && !(in_rng lo hi x)) A Z_.toNat
            = zcount P A Z_.toNat := by
          apply zcount_ext
          intro x hx1 hx2
          rw [in_rng_eq_false_of_lt (by omega)]
          simp
        rw [ite_eq_left hEl, ite_eq_right hEr, hmn, e1]
        omega
      · -- left only, crossing `lo`: `[A, lo)` survives, `[lo, A+Z)` is cut
        have hm2 : 0 ≤ A + Z_ - lo := by omega
        have hmn : min Z_ (lo - A) = lo - A := by
          rw [Int.min_def]; split <;> omega
        have hZeq : Z_ = (lo - A) + (A + Z_ - lo) := by omega
        have htoNat : Z_.toNat = (lo - A).toNat + (A + Z_ - lo).toNat := by
          calc Z_.toNat
              = ((lo - A) + (A + Z_ - lo)).toNat := congrArg Int.toNat (by omega)
            _ = (lo - A).toNat + (A + Z_ - lo).toNat := Int.toNat_add (by omega) hm2
        have h1 : ((lo - A).toNat : Int) = lo - A := Int.toNat_of_nonneg (by omega)
        have h2 : ((A + Z_ - lo).toNat : Int) = A + Z_ - lo :=
          Int.toNat_of_nonneg hm2
        have hb2 : A + ((lo - A).toNat : Int) = lo := by rw [h1]; omega
        have e1 : zcount (fun x => P x && !(in_rng lo hi x)) A (lo - A).toNat
            = zcount P A (lo - A).toNat := by
          apply zcount_ext
          intro x hx1 hx2
          rw [h1] at hx2
          rw [in_rng_eq_false_of_lt (by omega)]
          simp
        have e2 : zcount (fun x => P x && !(in_rng lo hi x)) lo (A + Z_ - lo).toNat = 0 := by
          apply zcount_false
          intro x hx1 hx2
          rw [h2] at hx2
          rw [in_rng_eq_true hx1 (by omega)]
          simp
        rw [htoNat, zcount_split, hb2, ite_eq_left hEl, ite_eq_right hEr, hmn, e1, e2]
  · by_cases hEr : hi < A + Z_
    · by_cases h3a : hi ≤ A
      · -- right only, entirely above `hi`: nothing was cut
        have hmx : max A hi = A := by
          rw [Int.max_def]; split <;> omega
        have hdiff : A + Z_ - A = Z_ := by omega
        have e1 : zcount (fun x => P x && !(in_rng lo hi x)) A Z_.toNat
            = zcount P A Z_.toNat := by
          apply zcount_ext
          intro x hx1 hx2
          rw [in_rng_eq_false_of_le (by omega)]
          simp
        rw [ite_eq_right hEl, ite_eq_left hEr, hmx, hdiff, e1]
        omega
      · -- right only, starting below `hi`: `[hi, A+Z)` survives
        have hmx : max A hi = hi := by
          rw [Int.max_def]; split <;> omega
        have hZeq : Z_ = (hi - A) + (A + Z_ - hi) := by omega
        have htoNat : Z_.toNat = (hi - A).toNat + (A + Z_ - hi).toNat := by
          calc Z_.toNat
              = ((hi - A) + (A + Z_ - hi)).toNat := congrArg Int.toNat (by omega)
            _ = (hi - A).toNat + (A + Z_ - hi).toNat := Int.toNat_add (by omega) (by omega)
        have h2 : ((hi - A).toNat : Int) = hi - A := Int.toNat_of_nonneg (by omega)
        have hb2 : A + ((hi - A).toNat : Int) = hi := by rw [h2]; omega
        have e1 : zcount (fun x => P x && !(in_rng lo hi x)) A (hi - A).toNat = 0 := by
          apply zcount_false
          intro x hx1 hx2
          rw [h2] at hx2
          rw [in_rng_eq_true (by omega) (by omega)]
          simp
        have e2 : zcount (fun x => P x && !(in_rng lo hi x)) hi (A + Z_ - hi).toNat
            = zcount P hi (A + Z_ - hi).toNat := by
          apply zcount_ext
          intro x hx1 hx2
          rw [in_rng_eq_false_of_le hx1]
          simp
        rw [htoNat, zcount_split, hb2, ite_eq_right hEl, ite_eq_left hEr, hmx, e1, e2]
    · -- inside `[lo, hi)` throughout: everything is cut
      have e0 : zcount (fun x => P x && !(in_rng lo hi x)) A Z_.toNat = 0 := by
        apply zcount_false
        intro x hx1 hx2
        rw [in_rng_eq_true (by omega) (by omega)]
        simp
      rw [ite_eq_right hEl, ite_eq_right hEr, e0]
      omega

/-- An interval's points inside `[lo, hi)` are at most `hi - lo`. -/
theorem count_inside (lo hi A Z_ : Int) (HZ : 0 ≤ Z_) (Hlh : lo ≤ hi) :
    zcount (in_rng lo hi) A Z_.toNat ≤ hi - lo := by
  have Hsplit := zcount_and_split (fun _ : Int => true) (in_rng lo hi) A Z_.toNat
  rw [zcount_const_true, Int.toNat_of_nonneg HZ] at Hsplit
  rw [count_outside_gen (fun _ : Int => true) lo hi A Z_ HZ Hlh] at Hsplit
  have h1 : zcount (fun x => true && in_rng lo hi x) A Z_.toNat
      = zcount (in_rng lo hi) A Z_.toNat := by
    apply zcount_ext; intro x _ _; simp
  rw [h1] at Hsplit

  by_cases hEl : A < lo
  · by_cases hEr : hi < A + Z_
    · have hm1 : 0 ≤ lo - A := by omega
      have hm2 : 0 ≤ A + Z_ - hi := by omega
      have hmn : min Z_ (lo - A) = lo - A := by rw [Int.min_def]; split <;> omega
      have hmx : max A hi = hi := by rw [Int.max_def]; split <;> omega
      rw [ite_eq_left hEl, ite_eq_left hEr, hmn, hmx] at Hsplit
      simp only [zcount_const_true] at Hsplit
      rw [Int.toNat_of_nonneg hm1, Int.toNat_of_nonneg hm2] at Hsplit
      omega
    · by_cases h2a : A + Z_ ≤ lo
      · have hmn : min Z_ (lo - A) = Z_ := by rw [Int.min_def]; split <;> omega
        rw [ite_eq_left hEl, ite_eq_right hEr, hmn, zcount_const_true] at Hsplit
        rw [Int.toNat_of_nonneg HZ] at Hsplit
        omega
      · have hm1 : 0 ≤ lo - A := by omega
        have hmn : min Z_ (lo - A) = lo - A := by rw [Int.min_def]; split <;> omega
        rw [ite_eq_left hEl, ite_eq_right hEr, hmn] at Hsplit
        simp only [zcount_const_true] at Hsplit
        rw [Int.toNat_of_nonneg hm1] at Hsplit
        omega
  · by_cases hEr : hi < A + Z_
    · by_cases h3a : hi ≤ A
      · have hmx : max A hi = A := by rw [Int.max_def]; split <;> omega
        have hdiff : A + Z_ - A = Z_ := by omega
        rw [ite_eq_right hEl, ite_eq_left hEr, hmx, hdiff, zcount_const_true] at Hsplit
        rw [Int.toNat_of_nonneg HZ] at Hsplit
        omega
      · have hm2 : 0 ≤ A + Z_ - hi := by omega
        have hmx : max A hi = hi := by rw [Int.max_def]; split <;> omega
        rw [ite_eq_right hEl, ite_eq_left hEr, hmx] at Hsplit
        simp only [zcount_const_true] at Hsplit
        rw [Int.toNat_of_nonneg hm2] at Hsplit
        omega
    · rw [ite_eq_right hEl, ite_eq_right hEr] at Hsplit
      omega


/-- An inverted range is empty. -/
theorem in_rng_eq_false_of_empty {lo hi x : Int} (h : hi ≤ lo) : in_rng lo hi x = false :=
  in_rng_false_iff lo hi x |>.mpr (by omega)

/-- The cover identity behind `iv_subtract`'s third clause: what is left of
    `[A, A+Z)` after cutting `[lo, hi)` is `[A, min (A+Z) lo)` together with
    `[max A hi, A+Z)`, and those are exactly the points of the interval that
    the cut misses. -/
theorem covered_iv_subtract_pts (A Z_ lo hi x : Int) (_Hlh : lo ≤ hi) :
    (in_rng A (min (A + Z_) lo) x || in_rng (max A hi) (A + Z_) x)
      = (in_rng A (A + Z_) x && !(in_rng lo hi x)) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  simp only [in_rng_true_iff, in_rng_false_iff, max_le_iff, lt_min_iff]
  constructor <;> intro h <;> omega

/- -------------------------------------------------------------------------
   maps_subtract / maps_subtract_all, semantically
   ------------------------------------------------------------------------- -/

/-- The pieces of `iv_subtract`: well-formed, counting exactly the points
    of `I` outside `[lo,hi)`, and covering exactly `I \ [lo,hi)`. -/
theorem iv_subtract_sem (a sz : word) (lo hi : Int)
    (Hwf : iv_wf (a, sz)) (Hlh : lo ≤ hi) :
    (∀ q, q ∈ iv_subtract a sz lo hi → iv_wf q)
      ∧ (∀ P, sum_count P (iv_subtract a sz lo hi)
            = iv_count (fun x => P x && !(in_rng lo hi x)) (a, sz))
      ∧ (∀ x, covered (iv_subtract a sz lo hi) x
            = (in_iv (a, sz) x && !(in_rng lo hi x))) := by
  have ha := bv_unsigned_range_u64 a
  have hs := bv_unsigned_range_u64 sz
  have ha1 : 0 ≤ (a.toNat : Int) := ha.1
  have ha2 : (a.toNat : Int) < 2 ^ 64 := ha.2
  have hs1 : 0 ≤ (sz.toNat : Int) := hs.1
  have hs2 : (sz.toNat : Int) < 2 ^ 64 := hs.2
  have hwf : (a.toNat : Int) + (sz.toNat : Int) ≤ 2 ^ 64 := Hwf
  unfold iv_subtract
  dsimp only
  by_cases hEl : (a.toNat : Int) < lo
  · -- the left remnant exists in both `hi` cases; record its facts once
    have hm1 : 0 ≤ min (sz.toNat : Int) (lo - (a.toNat : Int)) := by rw [Int.min_def]; split <;> omega
    have hm1u : min (sz.toNat : Int) (lo - (a.toNat : Int)) < 2 ^ 64 := by rw [Int.min_def]; split <;> omega
    have hmin : min (sz.toNat : Int) (lo - (a.toNat : Int)) ≤ (sz.toNat : Int) := by rw [Int.min_def]; split <;> omega
    have h1 : (a.toNat : Int) + min (sz.toNat : Int) (lo - (a.toNat : Int)) = min ((a.toNat : Int) + (sz.toNat : Int)) lo := by
      rw [Int.min_def, Int.min_def]; split <;> split <;> omega
    have hwfl : iv_wf (a, BitVec.ofInt 64 (min (sz.toNat : Int) (lo - (a.toNat : Int)))) := by
      apply iv_wf_intro
      rw [fg_lit (min (sz.toNat : Int) (lo - (a.toNat : Int))) ⟨hm1, hm1u⟩]
      omega
    by_cases hEr : hi < (a.toNat : Int) + (sz.toNat : Int)
    · -- both remnants survive
      rw [ite_eq_left hEl, ite_eq_left hEr]
      have hm2 : 0 ≤ max (a.toNat : Int) hi := by rw [Int.max_def]; split <;> omega
      have hm2u : max (a.toNat : Int) hi < 2 ^ 64 := by rw [Int.max_def]; split <;> omega
      have hm3 : 0 ≤ (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by rw [Int.max_def]; split <;> omega
      have hm3u : (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi < 2 ^ 64 := by rw [Int.max_def]; split <;> omega
      have h2 : max (a.toNat : Int) hi + ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) = (a.toNat : Int) + (sz.toNat : Int) := by omega
      have hwfr : iv_wf (BitVec.ofInt 64 (max (a.toNat : Int) hi),
          BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi)) := by
        apply iv_wf_intro
        rw [fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩]
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | hq
        · rw [hq]; exact hwfl
        · rw [hq]; exact hwfr
      · intro P
        rw [sum_count_app]
        simp only [sum_count, iv_count, B, S]
        rw [fg_lit (min (sz.toNat : Int) (lo - (a.toNat : Int))) ⟨hm1, hm1u⟩,
          fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩]
        rw [count_outside_gen P lo hi (a.toNat : Int) (sz.toNat : Int) (by omega) Hlh, ite_eq_left hEl, ite_eq_left hEr]
        omega
      · intro x
        simp only [covered, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false, in_iv, B, S, fg_lit (min (sz.toNat : Int) (lo - (a.toNat : Int))) ⟨hm1, hm1u⟩,
          fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩, h1, h2]
        exact covered_iv_subtract_pts (a.toNat : Int) (sz.toNat : Int) lo hi x Hlh
    · -- only the left remnant survives
      rw [ite_eq_left hEl, ite_eq_right hEr]
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp only [List.append_nil, List.mem_singleton] at hq
        rw [hq]; exact hwfl
      · intro P
        simp only [sum_count, List.append_nil, iv_count, B, S]
        rw [fg_lit (min (sz.toNat : Int) (lo - (a.toNat : Int))) ⟨hm1, hm1u⟩]
        rw [count_outside_gen P lo hi (a.toNat : Int) (sz.toNat : Int) (by omega) Hlh, ite_eq_left hEl, ite_eq_right hEr]
      · intro x
        simp only [covered, List.any_append, List.any_cons, List.any_nil,
          Bool.or_false, in_iv, B, S, fg_lit (min (sz.toNat : Int) (lo - (a.toNat : Int))) ⟨hm1, hm1u⟩, h1]
        rw [← covered_iv_subtract_pts (a.toNat : Int) (sz.toNat : Int) lo hi x Hlh,
          in_rng_eq_false_of_empty (lo := max (a.toNat : Int) hi) (hi := (a.toNat : Int) + (sz.toNat : Int)) (x := x)
            (by omega),
          Bool.or_false]
  · by_cases hEr : hi < (a.toNat : Int) + (sz.toNat : Int)
    · -- only the right remnant survives
      rw [ite_eq_right hEl, ite_eq_left hEr]
      have hm2 : 0 ≤ max (a.toNat : Int) hi := by rw [Int.max_def]; split <;> omega
      have hm2u : max (a.toNat : Int) hi < 2 ^ 64 := by rw [Int.max_def]; split <;> omega
      have hm3 : 0 ≤ (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi := by rw [Int.max_def]; split <;> omega
      have hm3u : (a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi < 2 ^ 64 := by rw [Int.max_def]; split <;> omega
      have h2 : max (a.toNat : Int) hi + ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) = (a.toNat : Int) + (sz.toNat : Int) := by omega
      have hwfr : iv_wf (BitVec.ofInt 64 (max (a.toNat : Int) hi),
          BitVec.ofInt 64 ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi)) := by
        apply iv_wf_intro
        rw [fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩]
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp only [List.nil_append, List.mem_singleton] at hq
        rw [hq]; exact hwfr
      · intro P
        simp only [sum_count, List.nil_append, iv_count, B, S]
        rw [fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩]
        rw [count_outside_gen P lo hi (a.toNat : Int) (sz.toNat : Int) (by omega) Hlh, ite_eq_right hEl, ite_eq_left hEr]
        omega
      · intro x
        simp only [covered, List.any_append, List.any_cons, List.any_nil, Bool.false_or,
          Bool.or_false, in_iv, B, S, fg_lit (max (a.toNat : Int) hi) ⟨hm2, hm2u⟩,
          fg_lit ((a.toNat : Int) + (sz.toNat : Int) - max (a.toNat : Int) hi) ⟨hm3, hm3u⟩, h2]
        rw [← covered_iv_subtract_pts (a.toNat : Int) (sz.toNat : Int) lo hi x Hlh,
          in_rng_eq_false_of_empty (lo := (a.toNat : Int)) (hi := min ((a.toNat : Int) + (sz.toNat : Int)) lo) (x := x)
            (by omega),
          Bool.false_or]
    · -- nothing survives
      rw [ite_eq_right hEl, ite_eq_right hEr]
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        simp at hq
      · intro P
        simp only [sum_count, List.nil_append, iv_count, B, S]
        rw [count_outside_gen P lo hi (a.toNat : Int) (sz.toNat : Int) (by omega) Hlh, ite_eq_right hEl, ite_eq_right hEr]
        omega
      · intro x
        simp only [covered, List.any_append, List.any_nil,
          Bool.or_false, in_iv, B, S]
        rw [← covered_iv_subtract_pts (a.toNat : Int) (sz.toNat : Int) lo hi x Hlh,
          in_rng_eq_false_of_empty (lo := max (a.toNat : Int) hi) (hi := (a.toNat : Int) + (sz.toNat : Int)) (x := x)
            (by omega),
          in_rng_eq_false_of_empty (lo := (a.toNat : Int)) (hi := min ((a.toNat : Int) + (sz.toNat : Int)) lo) (x := x)
            (by omega),
          Bool.false_or]


/-- Cutting one interval, in semantic form: `maps_subtract` keeps every entry
    well formed, its byte count is exactly the points of `l` outside
    `[lo, hi)`, and it covers exactly those points. -/
theorem maps_subtract_sem :
    ∀ (l : List (word × word)) (lo hi : Int), ivs_wf l → lo ≤ hi →
      ivs_wf (maps_subtract l lo hi)
      ∧ (∀ P, sum_count P (maps_subtract l lo hi)
            = sum_count (fun x => P x && !(in_rng lo hi x)) l)
      ∧ (∀ x, covered (maps_subtract l lo hi) x
            = (covered l x && !(in_rng lo hi x))) := by
  intro l
  induction l with
  | nil =>
      intro lo hi _ _
      refine ⟨ivs_wf_nil, ?_, ?_⟩
      · intro P; simp [maps_subtract, sum_count]
      · intro x; simp [maps_subtract, covered]
  | cons hd tl ih =>
      obtain ⟨a, sz⟩ := hd
      intro lo hi Hwf Hlh
      obtain ⟨Ha, Hl⟩ := ivs_wf_cons_inv (a, sz) tl Hwf
      obtain ⟨W, Sm, Cv⟩ := ih lo hi Hl Hlh
      obtain ⟨W1, Sm1, Cv1⟩ := iv_subtract_sem a sz lo hi Ha Hlh
      refine ⟨?_, ?_, ?_⟩
      · exact ivs_wf_app _ _ W1 W
      · intro P
        simp only [maps_subtract]
        rw [sum_count_app, Sm1, Sm]
        rfl
      · intro x
        rw [show maps_subtract ((a, sz) :: tl) lo hi
              = iv_subtract a sz lo hi ++ maps_subtract tl lo hi from rfl]
        rw [show covered (iv_subtract a sz lo hi ++ maps_subtract tl lo hi) x
              = (covered (iv_subtract a sz lo hi) x
                  || covered (maps_subtract tl lo hi) x)
            from by simp [covered, List.any_append]]
        rw [Cv1, Cv]
        show ((in_iv (a, sz) x && !(in_rng lo hi x))
              || (covered tl x && !(in_rng lo hi x)))
          = ((in_iv (a, sz) x || covered tl x) && !(in_rng lo hi x))
        cases in_iv (a, sz) x <;> cases covered tl x <;> cases in_rng lo hi x <;> rfl

theorem maps_subtract_wf (l : List (word × word)) (lo hi : Int)
    (H : ivs_wf l) (Hlh : lo ≤ hi) : ivs_wf (maps_subtract l lo hi) :=
  (maps_subtract_sem l lo hi H Hlh).1

theorem covered_app (l1 l2 : List (word × word)) (x : Int) :
    covered (l1 ++ l2) x = (covered l1 x || covered l2 x) := by
  simp [covered, List.any_append]

theorem maps_subtract_all_app_cuts :
    ∀ (l C1 C2 : List (word × word)),
      maps_subtract_all l (C1 ++ C2)
        = maps_subtract_all (maps_subtract_all l C1) C2 := by
  intro l C1
  revert l
  induction C1 with
  | nil => intro l C2; rfl
  | cons hd C1 ih =>
      obtain ⟨a, n⟩ := hd
      intro l C2
      simp only [maps_subtract_all, List.cons_append]
      exact ih _ _

/-- THE SEMANTICS: what is left of each interval after all cuts. -/
theorem live_msa :
    ∀ (C l : List (word × word)), ivs_wf l →
      live_bytes (maps_subtract_all l C) = sum_count (fun x => !(covered C x)) l
      ∧ ivs_wf (maps_subtract_all l C) := by
  intro C
  induction C with
  | nil =>
      intro l Hwf
      refine ⟨?_, ?_⟩
      · simp only [maps_subtract_all, covered, List.any_nil]
        rw [live_bytes_sum_count]
        apply sum_count_ext
        intro x
        simp
      · exact Hwf
  | cons hd C ih =>
      obtain ⟨a, n⟩ := hd
      intro l Hwf
      obtain ⟨W, Sm, _Cv⟩ :=
        maps_subtract_sem l (a.toNat : Int)
          ((a.toNat : Int) + (n.toNat : Int)) Hwf (by omega)
      obtain ⟨Hl, Hw⟩ :=
        ih (maps_subtract l (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int))) W
      refine ⟨?_, ?_⟩
      · rw [show maps_subtract_all l ((a, n) :: C)
              = maps_subtract_all
                  (maps_subtract l (a.toNat : Int)
                    ((a.toNat : Int) + (n.toNat : Int))) C from rfl]
        rw [Hl, Sm]
        apply sum_count_ext
        intro x
        simp only [covered, List.any_cons]
        have hunf : in_iv (a, n) x
            = in_rng (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) x := rfl
        rw [hunf]
        cases in_rng (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) x <;>
          cases List.any C (fun c => in_iv c x) <;> rfl
      · exact Hw

/- =========================================================================
   The meter and its bounds
   ========================================================================= -/

/-- Projections of the model transformers: they are `rfl` and `@[simp]`, so
    `model_proj` below is a plain `simp only`. -/
@[simp] theorem m_vmmaps_with_vmmaps (h : VmMaps) (m : Model) :
    m_vmmaps (with_vmmaps h m) = h := rfl

@[simp] theorem m_vm_lazy_with_vmmaps (h : VmMaps) (m : Model) :
    m_vm_lazy (with_vmmaps h m) = m_vm_lazy m := rfl

@[simp] theorem m_vm_materialized_with_vmmaps (h : VmMaps) (m : Model) :
    m_vm_materialized (with_vmmaps h m) = m_vm_materialized m := rfl

@[simp] theorem m_vmmaps_with_vm_backing (l : List (word × word)) (p : List word)
    (m : Model) : m_vmmaps (with_vm_backing l p m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_with_vm_backing (l : List (word × word)) (p : List word)
    (m : Model) : m_vm_lazy (with_vm_backing l p m) = l := rfl

@[simp] theorem m_vm_materialized_with_vm_backing (l : List (word × word))
    (p : List word) (m : Model) : m_vm_materialized (with_vm_backing l p m) = p := rfl

@[simp] theorem m_vmmaps_vm_forget_range (lo hi : Int) (m : Model) :
    m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m := rfl

@[simp] theorem m_vm_lazy_vm_forget_range (lo hi : Int) (m : Model) :
    m_vm_lazy (vm_forget_range lo hi m) = maps_subtract (m_vm_lazy m) lo hi := rfl

@[simp] theorem m_vm_materialized_vm_forget_range (lo hi : Int) (m : Model) :
    m_vm_materialized (vm_forget_range lo hi m)
      = List.filter (page_outside_range lo hi) (m_vm_materialized m) := rfl

@[simp] theorem m_vmmaps_vm_add_lazy (a n : word) (m : Model) :
    m_vmmaps (vm_add_lazy a n m) = m_vmmaps m := by
  unfold vm_add_lazy with_vm_backing m_vmmaps
  rfl

@[simp] theorem m_vm_lazy_vm_add_lazy (a n : word) (m : Model) :
    m_vm_lazy (vm_add_lazy a n m) = lazy_interior a n ++ m_vm_lazy m := by
  /- Via `m_vm_lazy_with_vm_backing`, not by `rfl` on the whole term: the
     kernel's `whnf` has to push the projection through
     `with_vm_backing`, meet the `++` that `lazy_interior` sits under, and
     start reducing `List.append` -- which forces the `if` inside
     `lazy_interior` and so the `Int` comparison behind it, the wall
     `Checks/Cases`' `sint32` note measures.  `unfold` + `rw` stops at
     the projection. -/
  unfold vm_add_lazy
  rw [m_vm_lazy_with_vm_backing]

@[simp] theorem m_vm_materialized_vm_add_lazy (a n : word) (m : Model) :
    m_vm_materialized (vm_add_lazy a n m) = m_vm_materialized m := by
  unfold vm_add_lazy
  rw [m_vm_materialized_with_vm_backing]

/-- Reduce the model transformers through their projections. -/
macro "model_proj" : tactic =>
  `(tactic| simp only [m_vmmaps_vm_add_lazy, m_vm_lazy_vm_add_lazy,
      m_vm_materialized_vm_add_lazy, m_vmmaps_vm_forget_range,
      m_vm_lazy_vm_forget_range, m_vm_materialized_vm_forget_range,
      m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, m_vm_materialized_with_vmmaps,
      m_vmmaps_with_vm_backing, m_vm_lazy_with_vm_backing,
      m_vm_materialized_with_vm_backing])

/-- Well-formed model ledgers: every interval of `vm_maps`, `vm_noaccess`
    and the lazy ledger ends at or below 2^64.  (Invariant of reachable
    states: every recorded end is at most `alloc_ceiling`.)

    The fourth conjunct is `AsanCeil.init_sp_ok`: the ledger stack pointer
    is admissible, so `AsanCeil.alloc_ceiling <= alloc_top`. -/
def model_ivs_wf (m : Model) : Prop :=
  ivs_wf (m_vmmaps m).vm_maps ∧ ivs_wf (m_vmmaps m).vm_noaccess
    ∧ ivs_wf (m_vm_lazy m)
    ∧ AsanCeil.init_sp_ok (m_vmmaps m)

/-- Bytes of `l` inside `[lo, hi)` — what exposing that range can cost. -/
def overlap_sum (l : List (word × word)) (lo hi : Int) : Int :=
  sum_count (in_rng lo hi) l

theorem overlap_sum_app (l1 l2 : List (word × word)) (lo hi : Int) :
    overlap_sum (l1 ++ l2) lo hi = overlap_sum l1 lo hi + overlap_sum l2 lo hi :=
  sum_count_app (in_rng lo hi) l1 l2

theorem overlap_sum_cons (p : word × word) (l : List (word × word)) (lo hi : Int) :
    overlap_sum (p :: l) lo hi = iv_count (in_rng lo hi) p + overlap_sum l lo hi := rfl

theorem overlap_sum_nil (lo hi : Int) : overlap_sum [] lo hi = 0 := rfl

theorem iv_count_in_rng_le (p : word × word) (lo hi : Int) (H : lo ≤ hi) :
    iv_count (in_rng lo hi) p ≤ hi - lo := by
  unfold iv_count
  exact count_inside lo hi (B p) (S p) (S_range p).1 H

theorem iv_count_in_rng_disjoint (p : word × word) (lo hi : Int)
    (H : B p + S p ≤ lo ∨ hi ≤ B p) : iv_count (in_rng lo hi) p = 0 := by
  unfold iv_count
  apply zcount_false
  intro x hx1 hx2
  have hs : (((S p).toNat : Int)) = S p := Int.toNat_of_nonneg (S_range p).1
  rw [hs] at hx2
  rcases H with H | H
  · rw [in_rng_eq_false_of_lt (lo := lo) (hi := hi) (x := x) (by omega)]
  · rw [in_rng_eq_false_of_le (lo := lo) (hi := hi) (x := x) (by omega)]

/-- A range `region_free` against `l` costs nothing from `l`. -/
theorem overlap_sum_region_free :
    ∀ (l : List (word × word)) (lo n : word), region_free l lo n = true →
      overlap_sum l (lo.toNat : Int) ((lo.toNat : Int) + (n.toNat : Int)) = 0 := by
  intro l
  induction l with
  | nil => intro lo n _; rfl
  | cons hd tl ih =>
      obtain ⟨b, s⟩ := hd
      intro lo n H
      simp only [region_free, Bool.and_eq_true] at H
      obtain ⟨H1, H2⟩ := H
      rw [overlap_sum_cons, ih lo n H2, iv_count_in_rng_disjoint]
      · omega
      · have hH1 : iv_overlap lo n b s = false := by simpa using H1
        unfold iv_overlap at hH1
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not] at hH1
        dsimp only [B, S]
        rcases hH1 with h | h <;> omega

/-- ... and one containing interval costs at most the range. -/
theorem overlap_sum_single_le (p : word × word) (lo hi : Int) (H : lo ≤ hi) :
    overlap_sum [p] lo hi ≤ hi - lo := by
  rw [overlap_sum_cons, overlap_sum_nil]
  have := iv_count_in_rng_le p lo hi H
  omega

/-- `vm_backing_used`, read semantically. -/
theorem vm_backing_used_sem_maps (m : Model)
    (Wm : ivs_wf (m_vmmaps m).vm_maps) :
    vm_backing_used m
      = sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps
        + (m_vm_materialized m).length * page_size := by
  unfold vm_backing_used vm_backed_maps
  rw [← maps_subtract_all_app_cuts]
  rw [(live_msa ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) (m_vmmaps m).vm_maps Wm).1]

theorem vm_backing_used_sem (m : Model) (H : model_ivs_wf m) :
    vm_backing_used m
      = sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
          (m_vmmaps m).vm_maps
        + (m_vm_materialized m).length * page_size :=
  vm_backing_used_sem_maps m H.1

theorem filter_length_le {α : Type} (f : α → Bool) (l : List α) :
    (List.filter f l).length ≤ l.length :=
  List.length_filter_le f l



/-- The Bool algebra the two cover inequalities below need: a point that is
    outside `p`-minus-the-cut and outside `q`-minus-the-cut is either outside
    both originals, or inside the cut. -/
theorem not_or_or_both (p q r : Bool) :
    (!(p || q) || r) = !((p && !r) || (q && !r)) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- The same step with only `p` cut (mprotect touches just `vm_noaccess`).
    Only the implication holds, which is all the cover inequality needs. -/
theorem not_or_or_left (p q r : Bool) (h : (!((p && !r) || q)) = true) :
    (!(p || q) || r) = true := by
  revert h
  cases p <;> cases q <;> cases r <;> decide

/-- ROW E (rw MAP_FIXED commit, no NORESERVE) — the post-model is
    `vm_forget_range lo hi (with_vmmaps h' m)` with `h'` = `h` except
    `vm_noaccess := maps_subtract (vm_noaccess h) lo hi`: exposing `[lo,hi)`
    costs at most the bytes of `vm_maps` inside it. -/
theorem backing_forget_commit_le (m : Model) (h' : VmMaps) (lo hi : Int)
    (Hwf : model_ivs_wf m) (Hlh : lo ≤ hi)
    (Hmaps : h'.vm_maps = (m_vmmaps m).vm_maps)
    (Hna : h'.vm_noaccess = maps_subtract (m_vmmaps m).vm_noaccess lo hi) :
    vm_backing_used (vm_forget_range lo hi (with_vmmaps h' m))
      ≤ vm_backing_used m + overlap_sum (m_vmmaps m).vm_maps lo hi := by
  have Hparts := Hwf
  obtain ⟨Wm, Wn, Wl, _Wsp⟩ := Hparts
  have Hwf' : ivs_wf (m_vmmaps (vm_forget_range lo hi (with_vmmaps h' m))).vm_maps := by
    model_proj
    rw [Hmaps]
    exact Wm
  rw [vm_backing_used_sem_maps _ Hwf', vm_backing_used_sem _ Hwf]
  model_proj
  rw [Hmaps, Hna]
  obtain ⟨_, _, Cn⟩ := maps_subtract_sem (m_vmmaps m).vm_noaccess lo hi Wn Hlh
  obtain ⟨_, _, Cl⟩ := maps_subtract_sem (m_vm_lazy m) lo hi Wl Hlh
  have hfilt := filter_length_le (page_outside_range lo hi) (m_vm_materialized m)
  have hstep :
      sum_count (fun x => !(covered (maps_subtract (m_vmmaps m).vm_noaccess lo hi
                ++ maps_subtract (m_vm_lazy m) lo hi) x)) (m_vmmaps m).vm_maps
        ≤ sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x)
                || in_rng lo hi x) (m_vmmaps m).vm_maps := by
    apply sum_count_mono
    intro x hx
    rw [covered_app] at hx ⊢
    rw [Cn, Cl] at hx
    rw [not_or_or_both]
    exact hx
  have hor := sum_count_or_le
    (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
    (in_rng lo hi) (m_vmmaps m).vm_maps
  unfold overlap_sum
  unfold page_size at *
  omega

/-- ROW M (mprotect rw over PROT_NONE) — only `vm_noaccess` shrinks. -/
theorem backing_mprotect_le (m : Model) (h' : VmMaps) (lo hi : Int)
    (Hwf : model_ivs_wf m) (Hlh : lo ≤ hi)
    (Hmaps : h'.vm_maps = (m_vmmaps m).vm_maps)
    (Hna : h'.vm_noaccess = maps_subtract (m_vmmaps m).vm_noaccess lo hi) :
    vm_backing_used (with_vmmaps h' m)
      ≤ vm_backing_used m + overlap_sum (m_vmmaps m).vm_maps lo hi := by
  have Hparts := Hwf
  obtain ⟨Wm, Wn, _Wl, _Wsp⟩ := Hparts
  have Hwf' : ivs_wf (m_vmmaps (with_vmmaps h' m)).vm_maps := by
    model_proj
    rw [Hmaps]
    exact Wm
  rw [vm_backing_used_sem_maps _ Hwf', vm_backing_used_sem _ Hwf]
  model_proj
  rw [Hmaps, Hna]
  obtain ⟨_, _, Cn⟩ := maps_subtract_sem (m_vmmaps m).vm_noaccess lo hi Wn Hlh
  have hstep :
      sum_count (fun x => !(covered (maps_subtract (m_vmmaps m).vm_noaccess lo hi
                ++ m_vm_lazy m) x)) (m_vmmaps m).vm_maps
        ≤ sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x)
                || in_rng lo hi x) (m_vmmaps m).vm_maps := by
    apply sum_count_mono
    intro x hx
    rw [covered_app] at hx ⊢
    rw [Cn] at hx
    exact not_or_or_left _ _ _ hx
  have hor := sum_count_or_le
    (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
    (in_rng lo hi) (m_vmmaps m).vm_maps
  unfold overlap_sum
  omega



/-- A `word` is the `ofInt` of its own unsigned value (the `Z_to_bv` round
    trip the remnant arithmetic needs). -/
theorem ofInt_toNat (w : word) : BitVec.ofInt 64 ((w.toNat : Int)) = w := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp

/-- `lazy_interior` of a page-aligned, page-rounded, nonempty range is the
    range itself. -/
theorem lazy_interior_aligned (a n : word)
    (Ha : (a.toNat : Int) % page_size = 0)
    (Hn : (n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (n.toNat : Int))
    (_Hwf : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) :
    lazy_interior a n = [(a, n)] := by
  have ha := bv_unsigned_range_u64 a
  have hn := bv_unsigned_range_u64 n
  have hdvd_a : (4096 : Int) ∣ (a.toNat : Int) := by
    apply Int.dvd_of_emod_eq_zero
    simpa [page_size] using Ha
  have hdvd_n : (4096 : Int) ∣ (n.toNat : Int) := by
    apply Int.dvd_of_emod_eq_zero
    simpa [page_size] using Hn
  have hlo : ((a.toNat : Int)) / 4096 * 4096 = (a.toNat : Int) :=
    Int.ediv_mul_cancel hdvd_a
  have hstep : ((a.toNat : Int) + 4096 - 1) / 4096 = ((a.toNat : Int)) / 4096 := by
    have h1 : ((a.toNat : Int) + 4096 - 1)
        = 4095 + 4096 * (((a.toNat : Int)) / 4096) := by
      rw [← hlo]; omega
    rw [h1, Int.add_mul_ediv_left 4095 (b := 4096) (((a.toNat : Int)) / 4096)
      (by decide)]
    rw [show (4095 : Int) / 4096 = 0 from by decide]
    omega
  have e1 : ((a.toNat : Int) + page_size - 1) / page_size * page_size
      = (a.toNat : Int) := by
    rw [show page_size = (4096 : Int) from rfl, hstep, hlo]
  have e2 : ((a.toNat : Int) + (n.toNat : Int)) / page_size * page_size
      = (a.toNat : Int) + (n.toNat : Int) := by
    rw [show page_size = (4096 : Int) from rfl]
    exact Int.ediv_mul_cancel (Int.dvd_add hdvd_a hdvd_n)
  unfold lazy_interior
  dsimp only
  rw [e1, e2]
  have hlt : (a.toNat : Int) < (a.toNat : Int) + (n.toNat : Int) := by omega
  rw [ite_eq_left hlt]
  have hdiff : ((a.toNat : Int) + (n.toNat : Int)) - (a.toNat : Int)
      = (n.toNat : Int) := by omega
  rw [hdiff, ofInt_toNat, ofInt_toNat]

/-- The Bool core of the recommit inequality: cutting `[lo,hi)` out of both
    ledgers and then re-adding it lazily never loses a covered point. -/
theorem recommit_cover_le (p q r : Bool)
    (h : (!((p && !r) || (r || (q && !r)))) = true) : ((!(p || q)) = true) := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- ROW F (rw MAP_FIXED|NORESERVE over a tracked mapping) — the post-model
    is `vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m))` with
    `lo = a`, `hi = a + n`: the slice stays lazy, its materialized pages are
    dropped, so the meter does not increase. -/
theorem backing_recommit_lazy_le (m : Model) (h' : VmMaps) (a n : word)
    (Hwf : model_ivs_wf m)
    (Hal : (a.toNat : Int) % page_size = 0)
    (Hnl : (n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (n.toNat : Int))
    (Hend : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64)
    (Hmaps : h'.vm_maps = (m_vmmaps m).vm_maps)
    (Hna : h'.vm_noaccess
      = maps_subtract (m_vmmaps m).vm_noaccess (a.toNat : Int)
          ((a.toNat : Int) + (n.toNat : Int))) :
    vm_backing_used
        (vm_add_lazy a n
          (vm_forget_range (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int))
            (with_vmmaps h' m)))
      ≤ vm_backing_used m := by
  have Hparts := Hwf
  obtain ⟨Wm, Wn, Wl, _Wsp⟩ := Hparts
  have Hlh : (a.toNat : Int) ≤ (a.toNat : Int) + (n.toNat : Int) := by omega
  have Hli := lazy_interior_aligned a n Hal Hnl Hpos Hend
  have Hwf' : ivs_wf
      (m_vmmaps (vm_add_lazy a n
        (vm_forget_range (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int))
          (with_vmmaps h' m)))).vm_maps := by
    model_proj
    rw [Hmaps]
    exact Wm
  rw [vm_backing_used_sem_maps _ Hwf', vm_backing_used_sem _ Hwf]
  model_proj
  rw [Hmaps, Hna, Hli]
  obtain ⟨_, _, Cn⟩ := maps_subtract_sem (m_vmmaps m).vm_noaccess
    (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) Wn Hlh
  obtain ⟨_, _, Cl⟩ := maps_subtract_sem (m_vm_lazy m)
    (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)) Wl Hlh
  have hmats : (List.filter (page_outside_range (a.toNat : Int)
        ((a.toNat : Int) + (n.toNat : Int))) (m_vm_materialized m)).length * page_size
      ≤ (m_vm_materialized m).length * page_size := by
    have h := filter_length_le
      (page_outside_range (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))
      (m_vm_materialized m)
    unfold page_size
    omega
  have hsum :
      sum_count (fun x => !(covered (maps_subtract (m_vmmaps m).vm_noaccess
                (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int))
              ++ ([(a, n)] ++ maps_subtract (m_vm_lazy m)
                (a.toNat : Int) ((a.toNat : Int) + (n.toNat : Int)))) x))
          (m_vmmaps m).vm_maps
        ≤ sum_count (fun x => !(covered ((m_vmmaps m).vm_noaccess ++ m_vm_lazy m) x))
            (m_vmmaps m).vm_maps := by
    apply sum_count_mono
    intro x hx
    have hp : covered [(a, n)] x
        = in_rng ((a.toNat : Int)) ((a.toNat : Int) + (n.toNat : Int)) x := by
      simp [covered, in_iv, B, S]
    rw [covered_app, covered_app] at hx
    rw [hp] at hx
    rw [Cn, Cl] at hx
    rw [covered_app]
    exact recommit_cover_le _ _ _ hx
  omega



/- =========================================================================
   The spec's budget booleans, discharged
   ========================================================================= -/

theorem vm_limit_with_vmmaps (h : VmMaps) (m : Model) :
    (m_vmmaps (with_vmmaps h m)).vm_limit = h.vm_limit := rfl

/-- Row E: rw MAP_FIXED commit WITHOUT MAP_NORESERVE inside a tracked
    mapping.  `overlap_sum (vm_maps h) lo hi` is `hi - lo` when exactly one
    tracked mapping meets the range (`overlap_sum_app` / `_region_free` /
    `_single_le`). -/
theorem mmap_fixed_rw_budget_ok_commit_intro (flags : word) (m : Model)
    (addr n : word)
    (Hnr : mmap_noreserve_b flags = false)
    (Hwf : model_ivs_wf m)
    (Hb : vm_backing_used m
        + overlap_sum (m_vmmaps m).vm_maps (addr.toNat : Int)
            ((addr.toNat : Int) + (n.toNat : Int))
        ≤ (m_vmmaps m).vm_limit) :
    mmap_fixed_rw_budget_ok flags m addr n = true := by
  unfold mmap_fixed_rw_budget_ok vm_backing_within_limit with_mmap_replacement
    with_mmap_backing
  rw [Hnr, ite_eq_right (by simp), decide_eq_true_iff]
  have Hle := backing_forget_commit_le m (mmap_fixed_rw_next (m_vmmaps m) addr n)
    (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) Hwf (by omega) rfl rfl
  have hlim : (m_vmmaps (vm_forget_range (addr.toNat : Int)
        ((addr.toNat : Int) + (n.toNat : Int))
        (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m))).vm_limit
      = (m_vmmaps m).vm_limit := by
    model_proj
    rfl
  rw [hlim]
  omega

/-- Row F: rw MAP_FIXED|MAP_NORESERVE re-commit inside a tracked mapping:
    never over budget if the current state is within budget. -/
theorem mmap_fixed_rw_budget_ok_recommit_intro (flags : word) (m : Model)
    (addr n : word)
    (Hnr : mmap_noreserve_b flags = true)
    (Hwf : model_ivs_wf m)
    (Hal : (addr.toNat : Int) % page_size = 0)
    (Hnl : (n.toNat : Int) % page_size = 0)
    (Hpos : 0 < (n.toNat : Int))
    (Hend : (addr.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64)
    (Hb : vm_backing_used m ≤ (m_vmmaps m).vm_limit) :
    mmap_fixed_rw_budget_ok flags m addr n = true := by
  unfold mmap_fixed_rw_budget_ok vm_backing_within_limit with_mmap_replacement
    with_mmap_backing
  rw [Hnr, ite_eq_left rfl, decide_eq_true_iff]
  have Hle := backing_recommit_lazy_le m (mmap_fixed_rw_next (m_vmmaps m) addr n)
    addr n Hwf Hal Hnl Hpos Hend rfl rfl
  have hlim : (m_vmmaps (vm_add_lazy addr n (vm_forget_range (addr.toNat : Int)
        ((addr.toNat : Int) + (n.toNat : Int))
        (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)))).vm_limit
      = (m_vmmaps m).vm_limit := by
    model_proj
    rfl
  rw [hlim]
  omega

/-- Row M: mprotect rw over a PROT_NONE range. -/
theorem mprotect_budget_ok_intro_gen (m : Model) (addr n : word)
    (Hwf : model_ivs_wf m)
    (Hb : vm_backing_used m
        + overlap_sum (m_vmmaps m).vm_maps (addr.toNat : Int)
            ((addr.toNat : Int) + (n.toNat : Int))
        ≤ (m_vmmaps m).vm_limit) :
    mprotect_budget_ok m addr n = true := by
  unfold mprotect_budget_ok vm_backing_within_limit mprotect_model_next
  dsimp only
  rw [decide_eq_true_iff]
  have Hle := backing_mprotect_le m
    (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
      (maps_subtract (m_vmmaps m).vm_noaccess (addr.toNat : Int)
        ((addr.toNat : Int) + (n.toNat : Int)))
      (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
      (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp)
    (addr.toNat : Int) ((addr.toNat : Int) + (n.toNat : Int)) Hwf (by omega) rfl rfl
  have hlim : (m_vmmaps (with_vmmaps
        (VmMaps.mkVmMapsFull (m_vmmaps m).vm_reserved (m_vmmaps m).vm_maps
          (maps_subtract (m_vmmaps m).vm_noaccess (addr.toNat : Int)
            ((addr.toNat : Int) + (n.toNat : Int)))
          (m_vmmaps m).vm_start_brk (m_vmmaps m).vm_brk (m_vmmaps m).vm_limit
          (m_vmmaps m).vm_mmap_base (m_vmmaps m).vm_init_sp) m)).vm_limit
      = (m_vmmaps m).vm_limit := by
    model_proj
  rw [hlim]
  omega

/- =========================================================================
   Keeping `model_ivs_wf`
   ========================================================================= -/

/-- `ofInt` never increases a non-negative value: the stored `toNat` is the
    value modulo 2^64, and a non-negative value is at least its remainder. -/
theorem toNat_ofInt_le {z : Int} (hz : 0 ≤ z) :
    ((BitVec.ofInt 64 z).toNat : Int) ≤ z := by
  have h2 : (0 : Int) < (2 : Int) ^ 64 := by decide
  rw [BitVec.toNat_ofInt]
  have hmod : (((2 : Nat) ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by decide
  rw [hmod, Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))]
  have hzdiv : 0 ≤ z / (2 : Int) ^ 64 := Int.ediv_nonneg hz (by omega)
  have h := Int.mul_ediv_add_emod z ((2 : Int) ^ 64)
  omega

theorem lazy_interior_wf (a n : word)
    (H : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) :
    ivs_wf (lazy_interior a n) := by
  have ha := bv_unsigned_range_u64 a
  have hn := bv_unsigned_range_u64 n
  have hpos : (0 : Int) < page_size := by decide
  have hi_le : ((a.toNat : Int) + (n.toNat : Int)) / page_size * page_size
      ≤ (a.toNat : Int) + (n.toNat : Int) :=
    Int.ediv_mul_le _ (by omega)
  have lo_ge : 0 ≤ ((a.toNat : Int) + page_size - 1) / page_size * page_size := by
    have h1 : 0 ≤ ((a.toNat : Int) + page_size - 1) / page_size :=
      Int.ediv_nonneg (by omega) (by omega)
    exact Int.mul_nonneg h1 (by omega)
  unfold lazy_interior
  dsimp only
  by_cases hlt : ((a.toNat : Int) + page_size - 1) / page_size * page_size
      < ((a.toNat : Int) + (n.toNat : Int)) / page_size * page_size
  · rw [ite_eq_left hlt]
    intro q hq
    rw [List.mem_singleton] at hq
    rw [hq]
    apply iv_wf_intro
    have hb1 : ((BitVec.ofInt 64 (((a.toNat : Int) + page_size - 1)
        / page_size * page_size)).toNat : Int) ≤ ((a.toNat : Int) + page_size - 1)
        / page_size * page_size := toNat_ofInt_le lo_ge
    have hb2 : ((BitVec.ofInt 64 (((a.toNat : Int) + (n.toNat : Int))
        / page_size * page_size - ((a.toNat : Int) + page_size - 1)
          / page_size * page_size)).toNat : Int)
        ≤ ((a.toNat : Int) + (n.toNat : Int)) / page_size * page_size
          - ((a.toNat : Int) + page_size - 1) / page_size * page_size :=
      toNat_ofInt_le (by omega)
    omega
  · rw [ite_eq_right hlt]
    exact ivs_wf_nil

theorem model_ivs_wf_intro (m : Model)
    (H1 : ivs_wf (m_vmmaps m).vm_maps)
    (H2 : ivs_wf (m_vmmaps m).vm_noaccess)
    (H3 : ivs_wf (m_vm_lazy m))
    (H4 : AsanCeil.init_sp_ok (m_vmmaps m)) :
    model_ivs_wf m := ⟨H1, H2, H3, H4⟩

theorem model_ivs_wf_with_vmmaps (h : VmMaps) (m : Model)
    (Hwf : model_ivs_wf m) (Hm : ivs_wf h.vm_maps) (Hn : ivs_wf h.vm_noaccess)
    (Hsp : h.vm_init_sp = (m_vmmaps m).vm_init_sp) :
    model_ivs_wf (with_vmmaps h m) := by
  obtain ⟨_Wm, _Wn, Wl, Wsp⟩ := Hwf
  refine ⟨Hm, Hn, Wl, ?_⟩
  exact AsanCeil.init_sp_ok_same (m_vmmaps m) h Hsp Wsp

theorem model_ivs_wf_vm_forget_range (lo hi : Int) (m : Model) (Hlh : lo ≤ hi)
    (Hwf : model_ivs_wf m) : model_ivs_wf (vm_forget_range lo hi m) := by
  obtain ⟨Wm, Wn, Wl, Wsp⟩ := Hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ivs_wf (m_vmmaps (vm_forget_range lo hi m)).vm_maps
    rw [m_vmmaps_vm_forget_range]; exact Wm
  · show ivs_wf (m_vmmaps (vm_forget_range lo hi m)).vm_noaccess
    rw [m_vmmaps_vm_forget_range]; exact Wn
  · show ivs_wf (m_vm_lazy (vm_forget_range lo hi m))
    rw [m_vm_lazy_vm_forget_range]
    exact maps_subtract_wf _ _ _ Wl Hlh
  · show AsanCeil.init_sp_ok (m_vmmaps (vm_forget_range lo hi m))
    rw [m_vmmaps_vm_forget_range]; exact Wsp

theorem model_ivs_wf_vm_add_lazy (a n : word) (m : Model)
    (H : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) (Hwf : model_ivs_wf m) :
    model_ivs_wf (vm_add_lazy a n m) := by
  obtain ⟨Wm, Wn, Wl, Wsp⟩ := Hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ivs_wf (m_vmmaps (vm_add_lazy a n m)).vm_maps
    rw [m_vmmaps_vm_add_lazy]; exact Wm
  · show ivs_wf (m_vmmaps (vm_add_lazy a n m)).vm_noaccess
    rw [m_vmmaps_vm_add_lazy]; exact Wn
  · show ivs_wf (m_vm_lazy (vm_add_lazy a n m))
    rw [m_vm_lazy_vm_add_lazy]
    exact ivs_wf_app _ _ (lazy_interior_wf a n H) Wl
  · show AsanCeil.init_sp_ok (m_vmmaps (vm_add_lazy a n m))
    rw [m_vmmaps_vm_add_lazy]; exact Wsp

theorem model_ivs_wf_with_mmap_backing (flags a n : word) (m : Model)
    (H : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) (Hwf : model_ivs_wf m) :
    model_ivs_wf (with_mmap_backing flags a n m) := by
  unfold with_mmap_backing
  by_cases h : mmap_noreserve_b flags
  · rw [ite_eq_left h]
    exact model_ivs_wf_vm_add_lazy a n m H Hwf
  · rw [ite_eq_right h]
    exact Hwf

theorem model_ivs_wf_with_mmap_replacement (flags a n : word) (m : Model)
    (H : (a.toNat : Int) + (n.toNat : Int) ≤ 2 ^ 64) (Hwf : model_ivs_wf m) :
    model_ivs_wf (with_mmap_replacement flags a n m) := by
  unfold with_mmap_replacement
  apply model_ivs_wf_with_mmap_backing
  · exact H
  · apply model_ivs_wf_vm_forget_range
    · omega
    · exact Hwf

/-- The initial model's ledgers are well formed when the image's reserved
    list is (checked per image by computation) — `vm_maps`, `vm_noaccess`
    and the lazy ledger start empty. -/
theorem model_ivs_wf_init (reserved : List (word × word)) (brk0 mbase sp : word)
    (lim : Int) (inp : ProcInput) (Hsp : Run.valid_sp sp) :
    model_ivs_wf (init_model reserved brk0 mbase sp lim inp) := by
  have hm : (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_maps = [] := rfl
  have hn : (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).vm_noaccess = [] := rfl
  have hl : m_vm_lazy (init_model reserved brk0 mbase sp lim inp) = [] := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]; exact ivs_wf_nil
  · rw [hn]; exact ivs_wf_nil
  · rw [hl]; exact ivs_wf_nil
  · exact AsanCeil.init_sp_ok_init_model reserved brk0 mbase sp lim inp Hsp

/- =========================================================================
   Sanity checks

   These pin the encodings the counting lemmas read, so a slip in `zcount` /
   `in_rng` / `in_iv` / `covered` shows up immediately.
   ========================================================================= -/

example : zcount (fun x => decide (x < 2)) 0 4 = 2 := by decide

example : zcount (fun _ => true) (-3) 5 = 5 := by decide

example : in_rng 2 5 3 = true := by decide

example : in_rng 2 5 5 = false := by decide

example : in_iv ((BitVec.ofInt 64 8), (BitVec.ofInt 64 4)) 10 = true := by decide

example : covered [(BitVec.ofInt 64 8, BitVec.ofInt 64 4),
    (BitVec.ofInt 64 20, BitVec.ofInt 64 4)] 21 = true := by decide

example : covered [(BitVec.ofInt 64 8, BitVec.ofInt 64 4)] 3 = false := by decide

example : iv_wf ((BitVec.ofInt 64 8), (BitVec.ofInt 64 4)) := by
  unfold iv_wf B S
  decide

example : overlap_sum [(BitVec.ofInt 64 0, BitVec.ofInt 64 8)] 2 4 = 2 := by decide

end LinuxSem.Common.BackingAlgebra
