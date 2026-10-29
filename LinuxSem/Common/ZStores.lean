/-
  * Common.ZStores — a chain of zero-filling stores that covers a range
      equals one zero-fill of the range.  Image-INDEPENDENT.

    Used to summarize musl's [memset(d, 0, n)]: its stores (bytes, words,
    doublewords, in a non-monotone order, some overlapping) all write
    zeros at [d + off]; once every offset below [n] is covered the
    overlay is [wbytes m d (repeat 0 n)].

    ---------------------------------------------------------------------
    NOTES
    ---------------------------------------------------------------------

    * Values are `Int` and counts `Nat`; `bv_unsigned w` is
      `(w.toNat : Int)` (the spelling `Common/PropExec.lean` and
      `Common/CatExec.lean` use), `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
      `Z_to_bv 8 0` is `BitVec.ofInt 8 0`, `Z.of_nat n` is `(n : Int)`,
      `repeat b n` is `List.replicate n b`, `nth k l d` is `l.getD k d`,
      `forallb` is `List.all`, `existsb` is `List.any`, and `In x l` is
      `x ∈ l`.

    * The `(0 <=? a) && (b <=? c)` / `(a <? b)` tests are `decide` of the
      corresponding `Int` propositions, which yields the same `Bool`
      values.  [covers_off_true]/[ws_inb_true] below are the propositional
      readings of the two tests, so a proof rewrites a bound test into its
      proposition instead of unfolding the `Bool`.

    * `segs` is an EXPLICIT first argument of every `rdn` lemma (the `rdn`
      here is `PropExec.rdn segs mem a n`), so the segment list stays
      visible in each statement.

    * `List.Forall`-free: the "for all elements" side conditions are the
      `∀ x, x ∈ l → …` shape.

    * The section `Cover`'s variables [d]/[N] and hypothesis [Hnw] are
      explicit parameters of the three lemmas, in the order the proofs use
      them.

    Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.MemSplit

namespace LinuxSem.Common.ZStores

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.MemSplit
open LinuxSem.Common.StepTac

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-- The `FPState` instance the `PropExec`/`MemSplit` bound lemmas carry an
    unused section argument for (see `MemSplit`'s notes).  No statement
    below mentions the FP state. -/
local instance zstores_fx : FPState := fx0

/-- `repeat (Z_to_bv 8 0) n`: `n` zero bytes. -/
def zeros (n : Nat) : List byte := List.replicate n (BitVec.ofInt 8 0)

/-- A chain of zero-filling stores: each `(o, n)` writes `n` zero bytes at
    `d + o`, in the given (possibly non-monotone, possibly overlapping)
    order. -/
def zstores (m : word → Option byte) (d : word) (ws : List (Int × Nat)) :
    word → Option byte :=
  match ws with
  | [] => m
  | (o, n) :: ws' =>
    zstores (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + o)) (zeros n)) d ws'

/-- Does the store `(o, n)` write the offset `i`? -/
def covers_off (i : Int) (on : Int × Nat) : Bool :=
  decide (on.1 ≤ i) && decide (i < on.1 + (on.2 : Int))

/-- Every store in `ws` lies inside `[0, N)`. -/
def ws_inb (ws : List (Int × Nat)) (N : Int) : Bool :=
  ws.all (fun on => decide (0 ≤ on.1) && decide (on.1 + (on.2 : Int) ≤ N))

/-- The integer interval `[i, i + k)`. -/
def iota_Z (i : Int) (k : Nat) : List Int :=
  match k with
  | 0 => []
  | k' + 1 => i :: iota_Z (i + 1) k'

/-- The stores in `ws` cover every offset below `N`. -/
def ws_cover (ws : List (Int × Nat)) (N : Nat) : Bool :=
  (iota_Z 0 N).all (fun i => ws.any (covers_off i))

/-- The two spellings of `2^64` (`Nat`-power cast and `Int` power), which
    `omega` treats as different atoms. -/
theorem two_pow64_cast : ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := by omega

/-- The propositional reading of [covers_off]: its `Bool` conjunction of two
    `Int` comparisons decides exactly the two bounds. -/
theorem covers_off_true (i : Int) (on : Int × Nat) :
    covers_off i on = true ↔ on.1 ≤ i ∧ i < on.1 + (on.2 : Int) := by
  simp only [covers_off, Bool.and_eq_true, decide_eq_true_eq]

/-- The propositional reading of [ws_inb]: every interval starts at or
    above `0` and ends at or below `N`. -/
theorem ws_inb_true (ws : List (Int × Nat)) (N : Int) :
    ws_inb ws N = true ↔
      ∀ on, on ∈ ws → 0 ≤ on.1 ∧ on.1 + (on.2 : Int) ≤ N := by
  simp only [ws_inb, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-! ## `Bool` list plumbing -/

/-- A `Bool`-valued predicate true on every element is true of any member. -/
theorem forallb_In {A : Type} (f : A → Bool) :
    ∀ (l : List A) (x : A), l.all f = true → x ∈ l → f x = true := by
  intro l
  induction l with
  | nil =>
    intro x H Hin
    simp at Hin
  | cons y l ih =>
    intro x H Hin
    rw [List.all_cons, Bool.and_eq_true] at H
    rcases List.mem_cons.mp Hin with rfl | Hin
    · exact H.1
    · exact ih x H.2 Hin

/-- Every integer of `[i, i + k)` is in `iota_Z i k`. -/
theorem iota_Z_In : ∀ (k : Nat) (i z : Int),
    i ≤ z → z < i + (k : Int) → z ∈ iota_Z i k := by
  intro k
  induction k with
  | zero =>
    intro i z H1 H2
    omega
  | succ k ih =>
    intro i z H1 H2
    show z ∈ i :: iota_Z (i + 1) k
    by_cases h : i = z
    · subst h
      exact List.mem_cons_self ..
    · rw [List.mem_cons]
      right
      exact ih (i + 1) z (by omega) (by omega)

/-- A `Bool`-valued predicate false at every element is false of any member.
    (`List.any_eq_false` gives the pointwise reading.) -/
theorem existsb_false_forall {A : Type} (f : A → Bool) (l : List A) :
    l.any f = false → ∀ x, x ∈ l → f x = false :=
  fun H x Hx => by
    have h := List.any_eq_false.mp H x Hx
    simpa using h

/-- A true `any` has a witness.  (`List.any_eq_true`.) -/
theorem existsb_true_exists {A : Type} (f : A → Bool) (l : List A) :
    l.any f = true → ∃ x, x ∈ l ∧ f x = true :=
  fun H => List.any_eq_true.mp H

/-! ## The zero list -/

/-- The zero list has the requested length. -/
theorem length_zeros (n : Nat) : (zeros n).length = n :=
  List.length_replicate

/-- Every element of the zero list is the zero byte. -/
theorem nth_zeros (n k : Nat) :
    (zeros n).getD k (BitVec.ofInt 8 0) = BitVec.ofInt 8 0 := by
  rw [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : k < n
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    rfl

/-- Reading `n` bytes back out of a zero-filled `N`-byte range gives the
    `n` zero bytes. -/
theorem rdn_wbytes_zeros_in (segs : List Segment) (m : word → Option byte)
    (d a : word) (N n : Nat)
    (Hnw : (d.toNat : Int) + (N : Int) < ((2 ^ 64 : Nat) : Int))
    (Hlo : (d.toNat : Int) ≤ (a.toNat : Int))
    (Hhi : (a.toNat : Int) + (n : Int) ≤ (d.toNat : Int) + (N : Int)) :
    rdn segs (wbytes m d (zeros N)) a n = some (zeros n) := by
  refine rdn_const segs (wbytes m d (zeros N)) a n (BitVec.ofInt 8 0) (by omega) ?_
  intro x hx1 hx2
  have hb : (d.toNat : Int) + (((zeros N).length) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [length_zeros]
    exact Int.le_of_lt Hnw
  have hx : (d.toNat : Int) ≤ (x.toNat : Int) ∧
      (x.toNat : Int) < (d.toNat : Int) + (((zeros N).length) : Int) := by
    rw [length_zeros]
    exact ⟨by omega, by omega⟩
  rw [wbytes_inside (zeros N) m d x hb hx, nth_zeros]

/-- Zero bytes read back as the integer zero. -/
theorem bytes_le_to_Z_zeros (n : Nat) : bytes_le_to_Z (zeros n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zeros, List.replicate_succ]
    show (((BitVec.ofInt 8 0).toNat
      ||| (bytes_le_to_Nat (List.replicate n (BitVec.ofInt 8 0)) <<< 8) : Nat) : Int) = 0
    have hz : (BitVec.ofInt 8 0).toNat = 0 := by decide
    have hrest : bytes_le_to_Nat (List.replicate n (BitVec.ofInt 8 0)) = 0 := by
      have h := ih
      unfold bytes_le_to_Z at h
      exact Int.ofNat.inj h
    rw [hz, hrest]
    rfl

/-! ## The covering chain -/

section Cover

variable (d : word) (N : Int)

/-- A store chain that misses `x` leaves `x` alone: `x` is outside every
    written range.  ([Hnw] is an explicit parameter: the proof uses it.) -/
theorem zstores_miss (Hnw : (d.toNat : Int) + N < ((2 ^ 64 : Nat) : Int))
    (ws : List (Int × Nat)) (m : word → Option byte) (x : word)
    (Hinb : ws_inb ws N = true)
    (Hno : ∀ on, on ∈ ws →
      covers_off ((x.toNat : Int) - (d.toNat : Int)) on = false) :
    zstores m d ws x = m x := by
  induction ws generalizing m with
  | nil => rfl
  | cons on ws' ih =>
    show zstores (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) (zeros on.2))
      d ws' x = m x
    obtain ⟨hob, hnb⟩ := (ws_inb_true _ _).mp Hinb on (List.mem_cons_self ..)
    have hrest : ws_inb ws' N = true := by
      rw [ws_inb_true]
      intro on' hon'
      exact (ws_inb_true _ _).mp Hinb on' (List.mem_cons_of_mem _ hon')
    have h64 : (d.toNat : Int) + on.1 < (2 : Int) ^ 64 := by
      rw [← two_pow64_cast]
      omega
    have hd' : ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
        = (d.toNat : Int) + on.1 :=
      u_Z2bv ((d.toNat : Int) + on.1) (by omega) h64
    rw [ih (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) (zeros on.2)) hrest
      (fun on' hin' => Hno on' (List.mem_cons_of_mem _ hin'))]
    have hc0 : ¬ (covers_off ((x.toNat : Int) - (d.toNat : Int)) on = true) := by
      have h := Hno on (List.mem_cons_self ..)
      rw [h]
      simp
    have hc : ¬ (on.1 ≤ (x.toNat : Int) - (d.toNat : Int) ∧
        (x.toNat : Int) - (d.toNat : Int) < on.1 + (on.2 : Int)) :=
      fun h => hc0 ((covers_off_true _ _).mpr h)
    have hbound : ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
        + ((zeros on.2).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
      rw [length_zeros, hd']
      have h2 : (d.toNat : Int) + on.1 + (on.2 : Int) ≤ (d.toNat : Int) + N := by
        omega
      exact Int.le_trans h2 (Int.le_of_lt Hnw)
    refine wbytes_outside (zeros on.2) m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) x
      hbound ?_
    by_cases hx : ((x.toNat : Int) - (d.toNat : Int)) < on.1
    · refine Or.inl ?_
      rw [hd']
      omega
    · refine Or.inr ?_
      have hA : on.1 ≤ (x.toNat : Int) - (d.toNat : Int) := by omega
      have hB : ¬ ((x.toNat : Int) - (d.toNat : Int) < on.1 + (on.2 : Int)) :=
        fun hB => hc ⟨hA, hB⟩
      rw [length_zeros, hd']
      omega

/-- A store chain that hits `x` writes the zero byte there.  (As with
    [zstores_miss], [Hnw] is explicit: the proof uses it.) -/
theorem zstores_hit (Hnw : (d.toNat : Int) + N < ((2 ^ 64 : Nat) : Int))
    (ws : List (Int × Nat)) (m : word → Option byte) (x : word)
    (Hinb : ws_inb ws N = true)
    (Hex : ∃ on, on ∈ ws ∧
      covers_off ((x.toNat : Int) - (d.toNat : Int)) on = true) :
    zstores m d ws x = some (BitVec.ofInt 8 0) := by
  induction ws generalizing m with
  | nil =>
    obtain ⟨on, hin, _⟩ := Hex
    exact absurd hin (by simp)
  | cons on ws' ih =>
    show zstores (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) (zeros on.2))
      d ws' x = some (BitVec.ofInt 8 0)
    obtain ⟨hob, hnb⟩ := (ws_inb_true _ _).mp Hinb on (List.mem_cons_self ..)
    have hrest : ws_inb ws' N = true := by
      rw [ws_inb_true]
      intro on' hon'
      exact (ws_inb_true _ _).mp Hinb on' (List.mem_cons_of_mem _ hon')
    have h64 : (d.toNat : Int) + on.1 < (2 : Int) ^ 64 := by
      rw [← two_pow64_cast]
      omega
    have hd' : ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
        = (d.toNat : Int) + on.1 :=
      u_Z2bv ((d.toNat : Int) + on.1) (by omega) h64
    by_cases hany : ws'.any (covers_off ((x.toNat : Int) - (d.toNat : Int))) = true
    · rw [ih (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) (zeros on.2)) hrest
        (existsb_true_exists _ _ hany)]
    · rw [zstores_miss d N Hnw ws'
        (wbytes m (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) (zeros on.2)) x hrest
        (fun on' hin' => existsb_false_forall _ _ (by simpa using hany) on' hin')]
      obtain ⟨on', hin', hcov⟩ := Hex
      rcases List.mem_cons.mp hin' with heq | hin'
      · subst on'
        obtain ⟨hc1, hc2⟩ := (covers_off_true _ _).mp hcov
        have hbound : ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
            + ((zeros on.2).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
          rw [length_zeros, hd']
          have h2 : (d.toNat : Int) + on.1 + (on.2 : Int) ≤ (d.toNat : Int) + N := by
            omega
          exact Int.le_trans h2 (Int.le_of_lt Hnw)
        have hx : ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
              ≤ (x.toNat : Int) ∧
            (x.toNat : Int) < ((BitVec.ofInt 64 ((d.toNat : Int) + on.1)).toNat : Int)
              + ((zeros on.2).length : Int) := by
          rw [length_zeros, hd']
          omega
        rw [wbytes_inside (zeros on.2) m
          (BitVec.ofInt 64 ((d.toNat : Int) + on.1)) x hbound hx, nth_zeros]
      · have hfalse := existsb_false_forall _ _ (by simpa using hany) on' hin'
        rw [hfalse] at hcov
        exact absurd hcov (by simp)

/-- A chain whose stores lie in `[0, N)` and cover every offset below
    `N = n` is one zero-fill of `n` bytes. -/
theorem zstores_cover (Hnw : (d.toNat : Int) + N < ((2 ^ 64 : Nat) : Int))
    (ws : List (Int × Nat)) (m : word → Option byte) (n : Nat)
    (HnN : (n : Int) = N)
    (Hinb : ws_inb ws N = true)
    (Hcov : ws_cover ws n = true) :
    zstores m d ws = wbytes m d (zeros n) := by
  funext x
  have hbn : (d.toNat : Int) + ((zeros n).length : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
    rw [length_zeros, HnN]
    exact Int.le_of_lt Hnw
  by_cases hlt : (x.toNat : Int) < (d.toNat : Int)
  · rw [wbytes_outside (zeros n) m d x hbn (Or.inl hlt)]
    refine zstores_miss d N Hnw ws m x Hinb (fun on hon => ?_)
    have hb := (ws_inb_true _ _).mp Hinb on hon
    have hc : ¬ (covers_off ((x.toNat : Int) - (d.toNat : Int)) on = true) := by
      rw [covers_off_true]
      omega
    simpa using hc
  · by_cases hin : (x.toNat : Int) < (d.toNat : Int) + N
    · have hx : (d.toNat : Int) ≤ (x.toNat : Int) ∧
          (x.toNat : Int) < (d.toNat : Int) + ((zeros n).length : Int) := by
        rw [length_zeros, HnN]
        exact ⟨by omega, by omega⟩
      rw [wbytes_inside (zeros n) m d x hbn hx, nth_zeros]
      refine zstores_hit d N Hnw ws m x Hinb ?_
      have hi : (x.toNat : Int) - (d.toNat : Int) ∈ iota_Z 0 n := by
        apply iota_Z_In
        · omega
        · omega
      exact existsb_true_exists _ _
        (forallb_In (fun i => ws.any (covers_off i)) (iota_Z 0 n) _ Hcov hi)
    · have hge : (d.toNat : Int) + ((zeros n).length : Int) ≤ (x.toNat : Int) := by
        rw [length_zeros, HnN]
        omega
      rw [wbytes_outside (zeros n) m d x hbn (Or.inr hge)]
      refine zstores_miss d N Hnw ws m x Hinb (fun on hon => ?_)
      have hb := (ws_inb_true _ _).mp Hinb on hon
      have hc : ¬ (covers_off ((x.toNat : Int) - (d.toNat : Int)) on = true) := by
        rw [covers_off_true]
        omega
      simpa using hc

end Cover

/-! ## Sanity checks (the decidable tests, by computation) -/

example : covers_off 3 ((0, 4) : Int × Nat) = true := by decide
example : covers_off 4 ((0, 4) : Int × Nat) = false := by decide
example : ws_inb [((0, 4) : Int × Nat)] 4 = true := by decide
example : ws_inb [((0, 4) : Int × Nat)] 3 = false := by decide
example : ws_cover [((0, 4) : Int × Nat)] 4 = true := by decide
example : ws_cover [((0, 4) : Int × Nat)] 5 = false := by decide
example : (zeros 3).length = 3 := by decide
