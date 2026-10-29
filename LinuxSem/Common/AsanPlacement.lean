/-
  placement lower bound for NULL-hint grants (ledger_split, kHighMemBeg);
  generic over the spec.

  * AsanPlacement — the PLACEMENT half only: the free-gap lemma
    `free_gap_of_totals`, ledger_split / null_hint_grant_above / kHighMemBeg.
    The spec keeps the ENOMEM arm at every anonymous mmap / mprotect, so no
    grant is forced; this file bounds only WHERE a grant lands.

    Image-INDEPENDENT; depends only on the specification.

  NOTES.  Notation, imports, and proof strategy only; no definition is
  weakened and no statement is changed beyond the parameter/binder shape
  noted below.

  - Values are `Int`, counts `Nat`, words `word = BitVec 64`;
    `BitVec.ofInt 64 z` makes a word from an `Int` and `(w.toNat : Int)`
    reads one unsigned.  Division and modulus are `Int.ediv` (`/`) and
    `Int.emod` (`%`); Lean 4.31 has no `Int.min`, so the minimum is `min`
    (with its `Int` instance), whose `Int.min_eq_left`/`Int.min_eq_right`
    are the min lemmas used below.
  - `!` is `Bool.not`, `&&` is `Bool.and`, a bound test is `decide (· < ·)`
    or `decide (· ≤ ·)`, and a decidable proposition is `decide`.
  - `Section Gap`'s variables (`L`, `nZ`, `HnZ`) are explicit parameters of
    `scan_inv`/`gap_at`/`scan_ok_or_step`/`scan`/`free_gap_of_slack` here:
    the section exists only to parameterize, and Lean's section variables
    would land in the argument list in the same order anyway.
  - The matching steps here are `List.mem_cons`/`List.mem_append`/
    `List.mem_filter`/`Bool.and_eq_false_iff`/`decide_eq_false`/
    `Int.mul_emod_left`.
  - `null_hint_grant_step` writes `min Y ((a.toNat : Int))` out rather than
    binding `Y'` with a `let`: a `let` in a Lean statement is
    definitionally its body, and naming it only obscures the six conjuncts.
  - `filter_live_mono` is a PRIVATE helper extracted from the `assert (Hle : …)`
    inside `live_weight_step` (same proof, same context; it is used nowhere
    else).  It is a consequence of the definitions, not a new assumption.
  - `two_pow_64`, `page_size`, `alloc_ceiling`, `bottomup_floor` are
    definitions here, so the `_val`/literal rewrites below unfold them
    where the arithmetic would otherwise see opaque constants; `omega`
    never needs them where the argument is purely order-theoretic.
-/

import LinuxSem.Common.AsanCeil
import LinuxSem.Common.PlacementSearch

set_option autoImplicit false

/- `omega` is asked below for bounds over `(w.toNat : Int)` sums, and the
    terms it builds for them are deeper than the default `maxRecDepth`.
    On this toolchain the KERNEL spends the same budget: the declaration
    is rejected with "(kernel) deep recursion detected" before any tactic
    gets to answer, so the option is not a speed knob here — 1024 is the
    first value that admits `scan_ok_or_step`, and 4096 leaves headroom.
    This is a TERM-DEPTH budget, not the divergence `Checks/Cases`'
    `sint32` note measures: raising it never rescues a proof that loops. -/
set_option maxRecDepth 4096

open LinuxSem.Riscv

namespace LinuxSem.Common.AsanPlacement

open LinuxSem.LinuxProcessSem
open LinuxSem.Common.PlacementSearch
open LinuxSem.Common.AsanCeil

/- =========================================================================
   Small facts
   ========================================================================= -/

theorem fg_u64_lit (z : Int) (h0 : 0 ≤ z) (h1 : z < two_pow_64) :
    ((BitVec.ofInt 64 z).toNat : Int) = z :=
  bv_unsigned_Z_to_bv_u64 z ⟨h0, h1⟩

theorem fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000 :=
  alloc_ceiling_val

theorem fg_u64_range (x : word) :
    0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < two_pow_64 :=
  bv_unsigned_range_u64 x

/-- `lia` is dramatically slower (minutes, cold cache) when the context
    holds `_ mod _ = 0` facts it does not need; the page facts below are
    therefore kept out of arithmetic side goals (`clear` before `lia`).

    `page_size` is a definition, so the literal `4096` appears by unfolding
    it, and `omega` stays linear. -/
theorem page_multiple_eq (z : Int) (Hz : z % page_size = 0) : z = z / 4096 * 4096 := by
  unfold page_size at Hz
  have h := Int.mul_ediv_add_emod z 4096
  rw [Hz, Int.add_zero, Int.mul_comm] at h
  omega

theorem fg_region_free_false (maps : List (word × word)) (lo n : word)
    (H : region_free maps lo n = false) :
    ∃ b s, (b, s) ∈ maps ∧ iv_overlap lo n b s = true := by
  induction maps with
  | nil => simp [region_free] at H
  | cons hd r ih =>
      obtain ⟨b0, s0⟩ := hd
      simp only [region_free, Bool.and_eq_false_iff] at H
      rcases H with H | H
      · exact ⟨b0, s0, by simp, by simpa using H⟩
      · obtain ⟨b, s, Hin, Hov⟩ := ih H
        exact ⟨b, s, by simp [Hin], Hov⟩

/-- The slack a ledger consumes for a request of `nZ` bytes: each interval
    can push the scan past itself (its size), past the window it spoiled
    (`nZ`) and up to the next page boundary (4095). -/
def gap_weight (nZ : Int) : List (word × word) → Int
  | [] => 0
  | (_, s) :: r => (s.toNat : Int) + nZ + 4095 + gap_weight nZ r

theorem gap_weight_app (nZ : Int) (l1 l2 : List (word × word)) :
    gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2 := by
  induction l1 with
  | nil => simp [gap_weight]
  | cons hd l1 ih =>
      obtain ⟨b, s⟩ := hd
      simp only [List.cons_append, gap_weight, ih]
      omega

theorem gap_weight_nonneg (nZ : Int) (l : List (word × word)) (HnZ : 0 ≤ nZ) :
    0 ≤ gap_weight nZ l := by
  induction l with
  | nil => simp [gap_weight]
  | cons hd l ih =>
      obtain ⟨b, s⟩ := hd
      have hs := (fg_u64_range s).1
      simp only [gap_weight]
      omega

/-- The LIVE part of the ledger at scan position `c`: intervals ending
    strictly above `c` (the only ones that can still overlap a window
    starting at or above `c`). -/
def live_at (c : Int) (p : word × word) : Bool :=
  decide (c < (p.1.toNat : Int) + (p.2.toNat : Int))

theorem gap_weight_filter_le (nZ : Int) (f : word × word → Bool)
    (l : List (word × word)) (HnZ : 0 ≤ nZ) :
    gap_weight nZ (List.filter f l) ≤ gap_weight nZ l := by
  induction l with
  | nil => simp [gap_weight]
  | cons hd l ih =>
      obtain ⟨b, s⟩ := hd
      have hs := (fg_u64_range s).1
      cases hf : f (b, s) with
      | true =>
          rw [List.filter_cons_of_pos hf]
          simp only [gap_weight]
          omega
      | false =>
          rw [List.filter_cons_of_neg (by simp [hf])]
          simp only [gap_weight]
          omega

/-- With `c ≤ c'`, the live-at-`c'` sub-ledger is contained in the
    live-at-`c` one, so its weight and its length are no larger.  Stated
    once (it is used once). -/
private theorem filter_live_mono (nZ : Int) (l : List (word × word)) (c c' : Int)
    (HnZ : 0 ≤ nZ)
    (Hmono : ∀ p, live_at c' p = true → live_at c p = true) :
    gap_weight nZ (List.filter (live_at c') l) ≤ gap_weight nZ (List.filter (live_at c) l) ∧
    (List.filter (live_at c') l).length ≤ (List.filter (live_at c) l).length := by
  induction l with
  | nil => simp
  | cons hd l ih =>
      obtain ⟨x, y⟩ := hd
      have hy := (fg_u64_range y).1
      cases h' : live_at c' (x, y) with
      | true =>
          have h : live_at c (x, y) = true := Hmono _ h'
          rw [List.filter_cons_of_pos h', List.filter_cons_of_pos h]
          simp only [gap_weight, List.length_cons]
          omega
      | false =>
          cases h : live_at c (x, y) with
          | true =>
              rw [List.filter_cons_of_neg (by simp [h']), List.filter_cons_of_pos h]
              simp only [gap_weight, List.length_cons]
              omega
          | false =>
              rw [List.filter_cons_of_neg (by simp [h']),
                List.filter_cons_of_neg (by simp [h])]
              exact ih

/-- Moving the scan position up keeps a sub-ledger live; moving it past
    the end of a live interval `(b, s)` drops that interval's weight. -/
theorem live_weight_step (nZ : Int) (l : List (word × word)) :
    ∀ (c c' : Int) (b s : word),
      0 ≤ nZ → c ≤ c' → (b, s) ∈ l → live_at c (b, s) = true →
      live_at c' (b, s) = false →
      gap_weight nZ (List.filter (live_at c') l) + ((s.toNat : Int) + nZ + 4095)
        ≤ gap_weight nZ (List.filter (live_at c) l)
      ∧ (List.filter (live_at c') l).length < (List.filter (live_at c) l).length := by
  induction l with
  | nil =>
      intro c c' b s _ _ Hin
      simp at Hin
  | cons hd tl ih =>
      intro c c' b s HnZ Hcc' Hin Hlive Hdead
      obtain ⟨b0, s0⟩ := hd
      have Hmono : ∀ p, live_at c' p = true → live_at c p = true := by
        intro p hp
        obtain ⟨x, y⟩ := p
        simp only [live_at] at hp ⊢
        rw [decide_eq_true_eq] at hp ⊢
        omega
      have Hle := filter_live_mono nZ tl c c' HnZ Hmono
      have hs0 := (fg_u64_range s0).1
      rcases List.mem_cons.mp Hin with Heq | Hin
      · -- the interval that dies IS the head
        cases Heq
        rw [List.filter_cons_of_neg (by simp [Hdead]), List.filter_cons_of_pos Hlive]
        simp only [gap_weight, List.length_cons]
        omega
      · -- the interval that dies is in the tail
        obtain ⟨Hw, Hlen⟩ := ih c c' b s HnZ Hcc' Hin Hlive Hdead
        cases h' : live_at c' (b0, s0) with
        | true =>
            have h : live_at c (b0, s0) = true := Hmono _ h'
            rw [List.filter_cons_of_pos h', List.filter_cons_of_pos h]
            simp only [gap_weight, List.length_cons]
            omega
        | false =>
            cases h : live_at c (b0, s0) with
            | true =>
                rw [List.filter_cons_of_neg (by simp [h']), List.filter_cons_of_pos h]
                simp only [gap_weight, List.length_cons]
                omega
            | false =>
                rw [List.filter_cons_of_neg (by simp [h']),
                  List.filter_cons_of_neg (by simp [h])]
                exact ⟨Hw, Hlen⟩

/- =========================================================================
   The free-gap lemma, EXISTENCE form (the spec has no vm_find_base).
   Section Gap: scan candidate bases upward from the
   floor; a blocked candidate is overlapped by a live interval whose rounded
   end is the next candidate.
   ========================================================================= -/

/-- The scan invariant at position `c`. -/
def scan_inv (L : List (word × word)) (nZ : Int) (c : Int) : Prop :=
  c % page_size = 0 ∧ bottomup_floor ≤ c
    ∧ c + nZ + gap_weight nZ (List.filter (live_at c) L) ≤ alloc_ceiling

def gap_at (L : List (word × word)) (nZ : Int) (c : Int) : Prop :=
  c % page_size = 0 ∧ bottomup_floor ≤ c ∧ c + nZ ≤ alloc_ceiling
    ∧ region_free L (BitVec.ofInt 64 c) (BitVec.ofInt 64 nZ) = true

theorem scan_ok_or_step (L : List (word × word)) (nZ : Int) (HnZ : 0 ≤ nZ) (c : Int)
    (Hinv : scan_inv L nZ c) :
    gap_at L nZ c
    ∨ ∃ c', scan_inv L nZ c'
        ∧ (List.filter (live_at c') L).length < (List.filter (live_at c) L).length := by
  obtain ⟨Hal, Hfl, Hw⟩ := Hinv
  have Hcv : alloc_ceiling = 0x7fff7f800000 := fg_alloc_ceiling_val
  have Hfv : bottomup_floor = 0x2aaaaaaab000 := bottomup_floor_val
  have Hw0 : 0 ≤ gap_weight nZ (List.filter (live_at c) L) :=
    gap_weight_nonneg nZ _ HnZ
  have h264 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have Hc64 : 0 ≤ c ∧ c < two_pow_64 := by
    unfold two_pow_64
    rw [h264]
    rw [Hcv] at Hw
    rw [Hfv] at Hfl
    omega
  have Hcu : ((BitVec.ofInt 64 c).toNat : Int) = c := fg_u64_lit c Hc64.1 Hc64.2
  have Hnu : ((BitVec.ofInt 64 nZ).toNat : Int) = nZ := by
    refine fg_u64_lit nZ HnZ ?_
    unfold two_pow_64
    rw [h264]
    rw [Hcv] at Hw
    rw [Hfv] at Hfl
    omega
  cases Hfree : region_free L (BitVec.ofInt 64 c) (BitVec.ofInt 64 nZ) with
  | true => exact Or.inl ⟨Hal, Hfl, by omega, Hfree⟩
  | false =>
      obtain ⟨b, s, Hin, Hov⟩ := fg_region_free_false L _ _ Hfree
      unfold iv_overlap at Hov
      rw [Hcu, Hnu] at Hov
      rw [Bool.and_eq_true] at Hov
      obtain ⟨H1, H2⟩ := Hov
      have H1' : c < (b.toNat : Int) + (s.toNat : Int) := of_decide_eq_true H1
      have H2' : (b.toNat : Int) < c + nZ := of_decide_eq_true H2
      have Hge := page_round_up_Z_ge ((b.toNat : Int) + (s.toNat : Int))
      have Hle : page_round_up_Z ((b.toNat : Int) + (s.toNat : Int))
          ≤ (b.toNat : Int) + (s.toNat : Int) + 4095 := by
        unfold page_round_up_Z page_size
        have hdm := Int.mul_ediv_add_emod
          ((b.toNat : Int) + (s.toNat : Int) + 4096 - 1) 4096
        have h0 := Int.emod_nonneg ((b.toNat : Int) + (s.toNat : Int) + 4096 - 1)
          (b := 4096) (by decide)
        have hlt := Int.emod_lt_of_pos ((b.toNat : Int) + (s.toNat : Int) + 4096 - 1)
          (b := 4096) (by decide)
        omega
      have Hlive : live_at c (b, s) = true := by
        simp only [live_at]
        exact decide_eq_true (by simpa using H1')
      have Hdead : live_at (page_round_up_Z ((b.toNat : Int) + (s.toNat : Int))) (b, s)
          = false := by
        simp only [live_at]
        exact decide_eq_false (by omega)
      obtain ⟨Hws, Hlen⟩ :=
        live_weight_step nZ L c _ b s HnZ (by omega) Hin Hlive Hdead
      exact Or.inr
        ⟨page_round_up_Z ((b.toNat : Int) + (s.toNat : Int)),
          ⟨page_round_up_Z_aligned _, by omega, by omega⟩, Hlen⟩

theorem scan (L : List (word × word)) (nZ : Int) (HnZ : 0 ≤ nZ) :
    ∀ (k : Nat) (c : Int),
      (List.filter (live_at c) L).length ≤ k → scan_inv L nZ c → ∃ g, gap_at L nZ g := by
  intro k
  induction k with
  | zero =>
      intro c Hk Hinv
      rcases scan_ok_or_step L nZ HnZ c Hinv with Hok | ⟨c', _, Hlt⟩
      · exact ⟨c, Hok⟩
      · omega
  | succ k ih =>
      intro c Hk Hinv
      rcases scan_ok_or_step L nZ HnZ c Hinv with Hok | ⟨c', Hinv', Hlt⟩
      · exact ⟨c, Hok⟩
      · exact ih c' (by omega) Hinv'

/-- THE GAP LEMMA (existence form). -/
theorem free_gap_of_slack (L : List (word × word)) (nZ : Int) (HnZ : 0 ≤ nZ)
    (Hslack : bottomup_floor + nZ + gap_weight nZ L ≤ alloc_ceiling) :
    ∃ g, g % page_size = 0 ∧ bottomup_floor ≤ g ∧ g + nZ ≤ alloc_ceiling
      ∧ region_free L (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true := by
  have Hinv : scan_inv L nZ bottomup_floor := by
    refine ⟨?_, by exact Int.le_refl _, ?_⟩
    · rw [bottomup_floor_val]
      decide
    · have h := gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ
      omega
  exact scan L nZ HnZ _ bottomup_floor (Nat.le_refl _) Hinv

/-- Count/size instance: at most `C` intervals of at most `N` bytes each.

    The size bound is stated as the per-entry `∀ p ∈ l`: Lean 4.31's core
    has no `List.Forall`, and the induction is on the list.  The `0 <= nZ`
    hypothesis is unused in the proof (the bound holds for either sign); it
    is kept, anonymous, so the statement is unchanged. -/
theorem gap_weight_bound (nZ N : Int) (l : List (word × word)) (_HnZ : 0 ≤ nZ)
    (H : ∀ p, p ∈ l → (p.2.toNat : Int) ≤ N) :
    gap_weight nZ l ≤ (l.length : Int) * (N + nZ + 4095) := by
  induction l with
  | nil => simp [gap_weight]
  | cons hd tl ih =>
      obtain ⟨b, s⟩ := hd
      have hs : (s.toNat : Int) ≤ N := H (b, s) (by simp)
      have htl : ∀ p, p ∈ tl → (p.2.toNat : Int) ≤ N :=
        fun p hp => H p (by simp [hp])
      have hih := ih htl
      have hQ : (s.toNat : Int) + nZ + 4095 ≤ N + nZ + 4095 := by omega
      rw [gap_weight, List.length_cons]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      calc (s.toNat : Int) + nZ + 4095 + gap_weight nZ tl
          ≤ (N + nZ + 4095) + (tl.length : Int) * (N + nZ + 4095) :=
            Int.add_le_add hQ hih
        _ = (tl.length : Int) * (N + nZ + 4095) + (N + nZ + 4095) := by omega

/-- The form the plan checker's `gap_ok` test provides: total size + count. -/
def gw_sizes : List (word × word) → Int
  | [] => 0
  | iv :: r => (iv.2.toNat : Int) + gw_sizes r

theorem gap_weight_sizes (nZ : Int) (l : List (word × word)) :
    gap_weight nZ l = gw_sizes l + (l.length : Int) * (nZ + 4095) := by
  induction l with
  | nil => simp [gap_weight, gw_sizes]
  | cons hd l ih =>
      obtain ⟨b, s⟩ := hd
      rw [gap_weight, gw_sizes, List.length_cons, ih]
      push_cast
      rw [Int.add_mul, Int.one_mul]
      omega

theorem free_gap_of_totals (h : VmMaps) (nZ tot : Int)
    (HnZ : 0 ≤ nZ)
    (Htot : gw_sizes (h.vm_reserved ++ h.vm_maps) ≤ tot)
    (Hband : bottomup_floor + nZ + tot
      + ((h.vm_reserved ++ h.vm_maps).length : Int) * (nZ + 4095) ≤ alloc_ceiling) :
    ∃ g, g % page_size = 0 ∧ bottomup_floor ≤ g ∧ g + nZ ≤ alloc_ceiling
      ∧ region_free (h.vm_reserved ++ h.vm_maps) (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true
      ∧ hint_placement_ok_b (BitVec.ofInt 64 0) h g nZ = true := by
  obtain ⟨g, Hal, Hfl, Hc, Hfree⟩ :=
    free_gap_of_slack (h.vm_reserved ++ h.vm_maps) nZ HnZ (by
      rw [gap_weight_sizes]
      omega)
  exact ⟨g, Hal, Hfl, Hc, Hfree, hint_placement_ok_b_of_floor _ h g nZ Hfl⟩

/- =========================================================================
   NULL-hint placement: where a kernel-placed grant can land
   ========================================================================= -/

/-- What the `choose` guard of a NULL-hint grant says (`Mmap.placement_ok`):
    the base is at or above `bottomup_floor`, or no page-aligned free window
    of the same size lies between the grant's end and `vm_mmap_base`.  The
    ASan proof needs a LOWER BOUND on such a base (every application address
    must be >= kHighMemBeg = 0x10007fff8000, the end of the high shadow).
    The invariant that yields it: the ledger is SPLIT — every interval
    either ends at or below a low mark `K` or starts at or above a high
    mark `Y` <= vm_mmap_base — with at least two windows of slack
    (`K + 2 nZ <= Y`).  Then `[Y - nZ, Y)` is a free aligned window, so a
    top-down placement must END above `Y - nZ`, i.e. start above
    `Y - 2 nZ`; a bottom-up one is above the floor anyway.  Adding the
    grant keeps the ledger split with the high mark lowered to
    `min Y a` — so the mark drops by less than twice the total size of the
    NULL-hint grants made, starting from `min bottomup_floor vm_mmap_base`
    >= `State.mmap_base_min` = 0x154555557000, which leaves 0x544d555f000
    (~5.3 TiB) of descent before kHighMemBeg. -/
def ledger_split (l : List (word × word)) (K Y : Int) : Prop :=
  ∀ b s, (b, s) ∈ l → (b.toNat : Int) + (s.toNat : Int) ≤ K ∨ Y ≤ (b.toNat : Int)

theorem ledger_split_nil (K Y : Int) : ledger_split [] K Y := by
  intro b s Hin
  simp at Hin

theorem ledger_split_mono (l : List (word × word)) (K Y Y' : Int)
    (H : ledger_split l K Y) (HY : Y' ≤ Y) : ledger_split l K Y' := by
  intro b s Hin
  rcases H b s Hin with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem ledger_split_cons (l : List (word × word)) (K Y : Int) (b s : word)
    (H : ledger_split l K Y)
    (Hbs : (b.toNat : Int) + (s.toNat : Int) ≤ K ∨ Y ≤ (b.toNat : Int)) :
    ledger_split ((b, s) :: l) K Y := by
  intro b' s' Hin
  rcases List.mem_cons.mp Hin with Heq | Hin
  · cases Heq
    exact Hbs
  · exact H b' s' Hin

theorem ledger_split_app (l1 l2 : List (word × word)) (K Y : Int)
    (H1 : ledger_split l1 K Y) (H2 : ledger_split l2 K Y) :
    ledger_split (l1 ++ l2) K Y := by
  intro b s Hin
  rcases List.mem_append.mp Hin with h | h
  · exact H1 b s h
  · exact H2 b s h

theorem ledger_split_app_inv (l1 l2 : List (word × word)) (K Y : Int)
    (H : ledger_split (l1 ++ l2) K Y) :
    ledger_split l1 K Y ∧ ledger_split l2 K Y := by
  constructor
  · intro b s Hin
    exact H b s (List.mem_append.mpr (Or.inl Hin))
  · intro b s Hin
    exact H b s (List.mem_append.mpr (Or.inr Hin))

/-- Sub-ledgers (munmap's `map_remove` is a `filter`) stay split. -/
theorem ledger_split_incl (l l' : List (word × word)) (K Y : Int)
    (H : ledger_split l K Y) (Hincl : List.Subset l' l) : ledger_split l' K Y := by
  intro b s Hin
  exact H b s (Hincl Hin)

theorem ledger_split_filter (f : word × word → Bool) (l : List (word × word)) (K Y : Int)
    (H : ledger_split l K Y) : ledger_split (List.filter f l) K Y := by
  refine ledger_split_incl l (List.filter f l) K Y H ?_
  intro x hx
  exact (List.mem_filter.mp hx).1

/-- The free window under the high mark. -/
theorem ledger_split_window_free (l : List (word × word)) (K Y nZ : Int)
    (HK : 0 ≤ K) (HnZ : 0 < nZ) (HY : K + 2 * nZ ≤ Y) (HY64 : Y < two_pow_64)
    (Hsplit : ledger_split l K Y) :
    region_free l (BitVec.ofInt 64 (Y - nZ)) (BitVec.ofInt 64 nZ) = true := by
  refine region_free_intro l _ _ ?_
  intro b s Hin
  unfold iv_overlap
  rw [fg_u64_lit (Y - nZ) (by omega) (by omega), fg_u64_lit nZ (by omega) (by omega)]
  rw [Bool.and_eq_false_iff]
  rcases Hsplit b s Hin with h | h
  · left
    rw [decide_eq_false_iff_not]
    omega
  · right
    rw [decide_eq_false_iff_not]
    omega

/-- THE PLACEMENT BOUND.  A NULL-hint grant `a` of rounded length `nZ`
    into a split ledger lands above the floor or above `Y - 2 nZ`. -/
theorem null_hint_grant_above (h : VmMaps) (a : word) (nZ K Y : Int)
    (HnZ : 0 < nZ) (HnAl : nZ % page_size = 0)
    (HaAl : (a.toNat : Int) % page_size = 0)
    (HYal : Y % page_size = 0) (HYB : Y ≤ (h.vm_mmap_base).toNat)
    (HK : 0 ≤ K) (HY : K + 2 * nZ ≤ Y)
    (Hsplit : ledger_split (h.vm_reserved ++ h.vm_maps) K Y)
    (Hpl : placement_ok_b h (a.toNat : Int) nZ = true) :
    bottomup_floor ≤ (a.toNat : Int) ∨ Y - 2 * nZ < (a.toNat : Int) := by
  have Ha := fg_u64_range a
  have HB := fg_u64_range h.vm_mmap_base
  have h264 : (2 : Int) ^ 64 = 18446744073709551616 := by decide
  have HY64 : Y < two_pow_64 := by
    unfold two_pow_64
    rw [h264]
    omega
  have HgAl : (Y - nZ) % page_size = 0 := by
    rw [Int.sub_emod, HYal, HnAl]
    simp [page_size]
  have Hfree := ledger_split_window_free (h.vm_reserved ++ h.vm_maps) K Y nZ
    HK HnZ HY HY64 Hsplit
  rw [placement_ok_b_iff h (a.toNat : Int) nZ Ha.1 HnZ HaAl HnAl] at Hpl
  rcases Hpl with Hfl | Hnhf
  · exact Or.inl Hfl
  · by_cases hlt : Y - 2 * nZ < (a.toNat : Int)
    · exact Or.inr hlt
    · exfalso
      have H1 : (a.toNat : Int) + nZ ≤ Y - nZ := by omega
      have H2 : Y - nZ + nZ ≤ (h.vm_mmap_base).toNat := by omega
      have Hno := Hnhf (Y - nZ) HgAl H1 H2
      rw [Hfree] at Hno
      exact Bool.noConfusion Hno

/-- Packaged for a grant step: the grant is above `K` (strictly: by at
    least a page, being aligned above `Y - 2nZ` >= K), and the extended
    ledger is split at the lowered high mark `Z.min Y (bv_unsigned a)`
    (page-aligned, <= vm_mmap_base, and >= Y - 2 nZ + page or >= the floor).

    The statement writes `min Y ((a.toNat : Int))` out rather than binding
    `Y'` with a `let`: a `let` in a Lean statement is definitionally its body.
    The three quotients are named by the equations `E1`/`E2`/`E3`. -/
theorem null_hint_grant_step (h : VmMaps) (a n : word) (nZ K Y : Int)
    (HnZ : 0 < nZ) (HnAl : nZ % page_size = 0)
    (HaAl : (a.toNat : Int) % page_size = 0)
    (HYal : Y % page_size = 0) (HYB : Y ≤ (h.vm_mmap_base).toNat)
    (HK : 0 ≤ K) (HKfl : K < bottomup_floor) (HY : K + 2 * nZ ≤ Y)
    (Hsplit : ledger_split (h.vm_reserved ++ h.vm_maps) K Y)
    (Hpl : placement_ok_b h (a.toNat : Int) nZ = true) :
    K < (a.toNat : Int)
    ∧ (bottomup_floor ≤ min Y (a.toNat : Int)
        ∨ Y - 2 * nZ + page_size ≤ min Y (a.toNat : Int))
    ∧ min Y (a.toNat : Int) ≤ Y
    ∧ min Y (a.toNat : Int) % page_size = 0
    ∧ min Y (a.toNat : Int) ≤ (h.vm_mmap_base).toNat
    ∧ ledger_split (h.vm_reserved ++ (a, n) :: h.vm_maps) K (min Y (a.toNat : Int)) := by
  have Habove :=
    null_hint_grant_above h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl
  -- page arithmetic: name the quotients so everything is linear
  have E1 : (a.toNat : Int) = (a.toNat : Int) / 4096 * 4096 := page_multiple_eq _ HaAl
  have E2 : Y = Y / 4096 * 4096 := page_multiple_eq _ HYal
  have E3 : nZ = nZ / 4096 * 4096 := page_multiple_eq _ HnAl
  have Hqn : 1 ≤ nZ / 4096 := by omega
  have Hpage : bottomup_floor ≤ (a.toNat : Int)
      ∨ Y - 2 * nZ + 4096 ≤ (a.toNat : Int) := by
    rcases Habove with hfl | hlt
    · exact Or.inl hfl
    · right
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- K < bv_unsigned a
    rcases Habove with hfl | hlt <;> omega
  · -- the new high mark
    rcases Int.le_total Y (a.toNat : Int) with hle | hge
    · rw [Int.min_eq_left hle]
      right
      show Y - 2 * nZ + 4096 ≤ Y
      omega
    · rw [Int.min_eq_right hge]
      rcases Hpage with h | h
      · exact Or.inl h
      · exact Or.inr h
  · exact Int.min_le_left _ _
  · rcases Int.le_total Y (a.toNat : Int) with hle | hge
    · rw [Int.min_eq_left hle]
      exact HYal
    · rw [Int.min_eq_right hge, E1, page_size]
      exact Int.mul_emod_left _ 4096
  · exact Int.le_trans (Int.min_le_left _ _) HYB
  · obtain ⟨Hr, Hm⟩ := ledger_split_app_inv _ _ _ _ Hsplit
    refine ledger_split_app _ _ _ _ ?_ ?_
    · exact ledger_split_mono _ K Y (min Y (a.toNat : Int)) Hr (by omega)
    · refine ledger_split_cons _ K (min Y (a.toNat : Int)) a n ?_ ?_
      · exact ledger_split_mono _ K Y (min Y (a.toNat : Int)) Hm (by omega)
      · right
        omega

/-- The numbers for the ASan layout: kHighMemBeg and the descent room. -/
def kHighMemBeg : Int := 0x10007fff8000

theorem kHighMemBeg_below_mmap_base_min :
    kHighMemBeg + 0x544d555f000 = mmap_base_min ∧ mmap_base_min < bottomup_floor := by
  unfold kHighMemBeg mmap_base_min bottomup_floor
  constructor <;> decide

/-- Instance: with the high mark at least `kHighMemBeg + 2 nZ`, a NULL-hint
    grant is at or above `kHighMemBeg + page_size`. -/
theorem kHighMemBeg_le (h : VmMaps) (a : word) (nZ Y : Int)
    (HnZ : 0 < nZ) (HnAl : nZ % page_size = 0)
    (HaAl : (a.toNat : Int) % page_size = 0)
    (HYal : Y % page_size = 0) (HYB : Y ≤ (h.vm_mmap_base).toNat)
    (HY : kHighMemBeg + 2 * nZ ≤ Y)
    (Hsplit : ledger_split (h.vm_reserved ++ h.vm_maps) kHighMemBeg Y)
    (Hpl : placement_ok_b h (a.toNat : Int) nZ = true) :
    kHighMemBeg < (a.toNat : Int) := by
  have HK : 0 ≤ kHighMemBeg := by unfold kHighMemBeg; decide
  rcases null_hint_grant_above h a nZ kHighMemBeg Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl
    with Hfl | Hlt
  · rw [bottomup_floor_val] at Hfl
    unfold kHighMemBeg at *
    omega
  · unfold kHighMemBeg at *
    omega

/-! ## Sanity checks (decidable checks) -/

example : gap_weight 0 [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x2000)]
    = 0x2000 + 4095 := by decide

example : gap_weight 4096 [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x2000)]
    = 0x2000 + 4096 + 4095 := by decide

example : gw_sizes [(BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x2000),
    (BitVec.ofInt 64 0x4000, BitVec.ofInt 64 0x1000)] = 0x3000 := by decide

example : live_at 0x1000 (BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000) = true := by
  decide

example : live_at 0x2000 (BitVec.ofInt 64 0x1000, BitVec.ofInt 64 0x1000) = false := by
  decide

example : gap_weight 0 ([(BitVec.ofInt 64 0, BitVec.ofInt 64 0x1000)] ++
    [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)])
    = gap_weight 0 [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x1000)]
      + gap_weight 0 [(BitVec.ofInt 64 0, BitVec.ofInt 64 0x2000)] := by decide

example : kHighMemBeg = 0x10007fff8000 := rfl

end LinuxSem.Common.AsanPlacement
