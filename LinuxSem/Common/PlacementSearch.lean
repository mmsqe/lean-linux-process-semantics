/-
  * Common.PlacementSearch — deciding "is there a free gap here?"

  UNTRUSTED.  Nothing in [EquivalenceDefinition/] or
  [LinuxProcessSem/] depends on this file; it is proof-library
  machinery, and the trusted spec must not name it.

  [Mmap.mmap_spec] says three things about a preference-free
  placement — page-aligned, inside the user address space, disjoint
  from every recorded mapping — and leaves the choice to the
  nondeterminism monad (see that file's placement section for why).
  A proof strategy that wants ONE concrete address instead of a
  quantifier needs two things the spec deliberately does not provide:
  an executable placement function, and a reason the admissible set is
  nonempty.  THIS FILE HAS THE FIRST AND NOT THE SECOND, and the
  asymmetry is not an omission — see [place_complete].

  Both reduce to the same question — does a free gap of [nZ] bytes
  exist in a given interval of the ledger? — and this file answers it
  decidably, with the completeness argument proved.  The trusted spec
  does not use it.

  NOTHING IMPORTS IT, AND THAT IS DELIBERATE.  Its consumer is a
  computational proof strategy that nobody has written; the file keeps
  the completeness argument so that nobody has to re-derive it later.
  A proved decision procedure waiting for its caller is an ordinary
  thing to find in this tier, and it should not be tidied away as
  residue.

  The candidate argument, which is what makes the question decidable
  at all: if ANY fitting free gap exists in an interval, then one
  exists whose base is either the interval's own floor or the
  page-rounded end of some ledger entry — slide the gap down until it
  rests on one or the other.  So a finite list of candidates suffices,
  one per ledger interval plus one.

  Notation only, plus the imports this tree's split of
  `State` forces; no definition is weakened and no statement changed.

  - `Z` → `Int`: `Z.modulo` → `Int.emod` (`%`), `Z.div` → `Int.ediv`
    (`/`), `Z.max` → `max`, `Z.le`/`Z.lt` → `≤`/`<`, `Z.eqb` → `==`,
    `Z.leb` → `decide (· ≤ ·)`, `andb` → `&&`, `negb` → `!`.
  - `bv 64` → `word` (`BitVec 64`); `Z_to_bv 64 z` → `BitVec.ofInt 64 z`;
    `bv_unsigned w` → `(w.toNat : Int)`.   - `list` → `List`; `find f l` → `l.find? f`; `existsb f l` →
    `l.any f` (note Lean's argument order); `filter` → `List.filter`;
    `in_map_iff` → `List.mem_map`; `filter_In` → `List.mem_filter`;
    `find_some` → `List.find?_some`; `existsb_exists` → `List.any_eq_true`;
    `Z.max_spec` → `Int.max_eq_left`/`Int.max_eq_right` chosen by
    `Int.le_total`.
  - This file imports `BvBase State` .  This tree splits `State`
    into `State` (numeric helpers, `VmMaps`), `StateLedger` (`alloc_top`,
    `mkVmMaps`, `alloc_top_lt`, `alloc_top_mkVmMaps`) and `StateVm`
    (`iv_overlap`, `region_free` and its three lemmas,
    `bv_unsigned_Z_to_bv_u64`), so all four modules are imported.
  - `page_size` is a `def`, not an opaque parameter, so the proofs below
    `unfold page_size` to the literal `4096` where the arithmetic needs
    it.  The  note about micromega choking on the four
    `_ mod page_size = 0` hypotheses therefore does not apply verbatim
    (Lean's `omega` sees the literal); the note is still carried below,
    since it explains the shape of the arithmetic steps around `g'`.
  - `Example … Proof. vm_compute. reflexivity. Qed.` → `theorem … := by
    decide`.  All four  examples are named, and are kept named.
 This is forced by
    Lean's block-comment lexer, which treats a double dash as starting a
    line comment, so a closing delimiter later on the same line would be
    swallowed and the comment reported unterminated.
  - Two PRIVATE helpers, `iv_overlap_eq_true_of` and
    `iv_overlap_eq_false_of_not`, restate `iv_overlap`'s unfolding as a
    predicate on the two `∧`-conditions. -/

import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateVm

open LinuxSem.Riscv

namespace LinuxSem.Common.PlacementSearch

open LinuxSem.LinuxProcessSem

/-- No free region of [nZ] bytes lies wholly above [aZ + nZ] and at or
    below [baseZ].  Quantified over [Z] with the range conditions
    keeping [g] inside [word]; the page-alignment premise matches the
    kernel, which only ever considers page-aligned placements. -/
def no_higher_fit (maps : List (word × word)) (aZ nZ baseZ : Int) : Prop :=
  ∀ g : Int,
    g % page_size = 0 →
    aZ + nZ ≤ g →
    g + nZ ≤ baseZ →
    region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = false

/-- The candidate list: one entry per ledger interval, plus the
    interval's own floor. -/
def fit_candidates (maps : List (word × word)) (aZ nZ : Int) : List Int :=
  (aZ + nZ) :: maps.map (fun p => page_round_up_Z ((p.1.toNat : Int) + (p.2.toNat : Int)))

def higher_fit_b (maps : List (word × word)) (aZ nZ baseZ : Int) : Bool :=
  (fit_candidates maps aZ nZ).any (fun g =>
    (g % page_size == 0) && decide (aZ + nZ ≤ g) && decide (g + nZ ≤ baseZ)
      && region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ))

theorem page_round_up_Z_aligned (z : Int) : page_round_up_Z z % page_size = 0 := by
  unfold page_round_up_Z
  rw [Int.mul_comm]
  exact Int.mul_emod_right page_size ((z + page_size - 1) / page_size)

theorem page_round_up_Z_ge (z : Int) : z ≤ page_round_up_Z z := by
  unfold page_round_up_Z page_size
  have hdm := Int.mul_ediv_add_emod (z + 4096 - 1) 4096
  have h0 := Int.emod_nonneg (z + 4096 - 1) (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos (z + 4096 - 1) (b := 4096) (by decide)
  omega

/-- The round-up is the LEAST page multiple at or above its argument. -/
theorem page_round_up_Z_le (z b : Int) (hzb : z ≤ b) (hb : b % page_size = 0) :
    page_round_up_Z z ≤ b := by
  unfold page_round_up_Z page_size at *
  have hdm := Int.mul_ediv_add_emod b 4096
  have h0 := Int.emod_nonneg b (b := 4096) (by decide)
  have hlt := Int.emod_lt_of_pos b (b := 4096) (by decide)
  have hbq : b = 4096 * (b / 4096) := by omega
  have h1 : (z + 4096 - 1) / 4096 < b / 4096 + 1 := by
    rw [Int.ediv_lt_iff_lt_mul (by decide : (0 : Int) < 4096)]
    omega
  omega

theorem fold_max_ge_seed (l : List Int) (s : Int) : s ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
      simp only [List.foldl_cons]
      exact Int.le_trans (Int.le_max_left s x) (ih (max s x))

theorem fold_max_ge_in (l : List Int) (s x : Int) (hx : x ∈ l) :
    x ≤ l.foldl max s := by
  induction l generalizing s with
  | nil => simp at hx
  | cons y l ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans (Int.le_max_right s x) (fold_max_ge_seed l (max s x))
      · exact ih (max s y) hx

theorem fold_max_le (l : List Int) (s b : Int) (hs : s ≤ b)
    (hl : ∀ x, x ∈ l → x ≤ b) : l.foldl max s ≤ b := by
  induction l generalizing s with
  | nil => simpa using hs
  | cons y l ih =>
      simp only [List.foldl_cons]
      exact ih (max s y) (Int.max_le.mpr ⟨hs, hl y (by simp)⟩)
        (fun x hx => hl x (by simp [hx]))

theorem fold_max_in_or_seed (l : List Int) (s : Int) :
    l.foldl max s = s ∨ l.foldl max s ∈ l := by
  induction l generalizing s with
  | nil => exact Or.inl rfl
  | cons y l ih =>
      simp only [List.foldl_cons]
      rcases ih (max s y) with h | h
      · rw [h]
        rcases Int.le_total s y with hsy | hys
        · right
          rw [Int.max_eq_right hsy]
          exact List.mem_cons_self ..
        · left
          exact Int.max_eq_left hys
      · right
        exact List.mem_cons_of_mem y h

/-- `iv_overlap` is true exactly when both interval
    conditions hold. -/
private theorem iv_overlap_eq_true_of (a1 n1 a2 n2 : word)
    (h : (a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int) ∧
         (a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int)) :
    iv_overlap a1 n1 a2 n2 = true := by
  unfold iv_overlap
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact h

/--  reaches for `andb_false_iff` and `Z.ltb_ge` here; this
    is the same step stated once: `iv_overlap` is false as soon as the two
    interval conditions are not BOTH true. -/
private theorem iv_overlap_eq_false_of_not (a1 n1 a2 n2 : word)
    (h : ¬ ((a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int) ∧
            (a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int))) :
    iv_overlap a1 n1 a2 n2 = false := by
  unfold iv_overlap
  by_cases hA : (a1.toNat : Int) < (a2.toNat : Int) + (n2.toNat : Int)
  · have hB : ¬ ((a2.toNat : Int) < (a1.toNat : Int) + (n1.toNat : Int)) :=
      fun hB => h ⟨hA, hB⟩
    simp [hA, hB]
  · simp [hA]

/- COMPLETENESS of the candidate scan: any page-aligned fitting free
    gap yields a candidate that is free and fitting.  This is the
    sliding argument: take the largest candidate at or below the given
    gap's base; every ledger entry ending at or below the given base has
    its page-rounded end among the candidates (so cannot reach past the
    chosen one), and every entry ending above it starts at or above the
    given gap's end (else it would have overlapped the given free gap).
    So the chosen candidate's window is free, and it inherits both
    bounds. -/

/-- THE FLOOR HYPOTHESIS IS [0 <= aZ + nZ], NOT [0 <= aZ], and the
    difference is load-bearing rather than cosmetic — leave it weak.

    [aZ] enters this lemma only through [aZ + nZ]: it is the floor of the
    search expressed as a grant's END, and the proof below never needs
    the floor's own sign.  Strengthening it back to [0 <= aZ] costs a
    caller that reduces to this lemma at [aZ := loZ - nZ] the side
    condition [nZ <= loZ], which at a floor of [page_size] silently
    forces [nZ = 4096] — turning a general completeness claim into one
    about single-page requests while still typechecking.  That is how
    [place_complete] below was first written, and it is the reason this
    hypothesis is stated in the form the proof actually uses. -/
theorem higher_fit_b_complete (maps : List (word × word)) (aZ nZ baseZ g : Int)
    (HaPos : 0 ≤ aZ + nZ) (HnPos : 0 < nZ)
    (HaAl : aZ % page_size = 0) (HnAl : nZ % page_size = 0)
    (Hbase : baseZ < two_pow_64)
    (HgAl : g % page_size = 0) (Hglo : aZ + nZ ≤ g) (Hghi : g + nZ ≤ baseZ)
    (Hgfree : region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true) :
    higher_fit_b maps aZ nZ baseZ = true := by
  /- The three [<=] steps over [g'] below are spelled as explicit
     transitivity terms rather than [lia].  The context carries four
     [_ mod page_size = 0] hypotheses; [page_size] is an opaque constant
     to micromega, so its div/mod preprocessing turns each one into a
     product [page_size * q] and the certificate search goes nonlinear.
     Blind [lia] took 231 s, 100 s and 90 s on those three goals — 97% of
     this file's compile time — where each is one application of
     [Z.le_trans].  Do not put [lia] back without clearing HaAl, HnAl,
     HgAl and Hg'Al first.
-/
  have Hg0 : 0 ≤ g := by omega
  have Hn0 : 0 ≤ nZ := by omega
  have Hnlt : nZ < two_pow_64 := by omega
  have HgW : ((BitVec.ofInt 64 g).toNat : Int) = g :=
    bv_unsigned_Z_to_bv_u64 g ⟨Hg0, by omega⟩
  have HnW : ((BitVec.ofInt 64 nZ).toNat : Int) = nZ :=
    bv_unsigned_Z_to_bv_u64 nZ ⟨Hn0, Hnlt⟩
  -- `cs` is `List.filter (fun c => (c <=? g)%Z) (fit_candidates maps aZ nZ)`
  -- and `g'` is `fold_left Z.max cs (aZ + nZ)%Z`, kept as local definitions.
  let cs : List Int := (fit_candidates maps aZ nZ).filter (fun c => decide (c ≤ g))
  let g' : Int := cs.foldl max (aZ + nZ)
  have hcs : cs = (fit_candidates maps aZ nZ).filter (fun c => decide (c ≤ g)) := rfl
  have hg' : g' = cs.foldl max (aZ + nZ) := rfl
  have hlo : aZ + nZ ≤ g' := by
    rw [hg']
    exact fold_max_ge_seed cs (aZ + nZ)
  have hhi : g' ≤ g := by
    rw [hg']
    refine fold_max_le cs (aZ + nZ) g (by omega) ?_
    intro x hx
    rw [hcs] at hx
    exact of_decide_eq_true (List.mem_filter.mp hx).2
  have hcand : g' ∈ fit_candidates maps aZ nZ := by
    have h := fold_max_in_or_seed cs (aZ + nZ)
    rw [← hg'] at h
    rcases h with h | h
    · rw [h]
      exact List.mem_cons_self ..
    · rw [hcs] at h
      exact (List.mem_filter.mp h).1
  have hcand' : g' ∈ (aZ + nZ) :: maps.map
      (fun p => page_round_up_Z ((p.1.toNat : Int) + (p.2.toNat : Int))) := hcand
  have hg'0 : 0 ≤ g' := Int.le_trans HaPos hlo
  have hg'lt : g' < two_pow_64 := by omega
  have Hg'W : ((BitVec.ofInt 64 g').toNat : Int) = g' :=
    bv_unsigned_Z_to_bv_u64 g' ⟨hg'0, hg'lt⟩
  have hg'al : g' % page_size = 0 := by
    rcases List.mem_cons.mp hcand' with h | h
    · rw [h, Int.add_emod, HaAl, HnAl]
      simp [page_size]
    · obtain ⟨p, -, hp⟩ := List.mem_map.mp h
      rw [← hp]
      exact page_round_up_Z_aligned _
  have hg'free : region_free maps (BitVec.ofInt 64 g') (BitVec.ofInt 64 nZ) = true := by
    apply region_free_intro
    intro b s hmem
    have hno := region_free_In maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) b s Hgfree hmem
    by_cases hcase : (b.toNat : Int) + (s.toNat : Int) ≤ g
    · -- entry ends at or below g: its rounded end is a candidate <= g
      have hc : page_round_up_Z ((b.toNat : Int) + (s.toNat : Int))
          ∈ fit_candidates maps aZ nZ := by
        simp only [fit_candidates]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(b, s), hmem, rfl⟩)
      have hcle : page_round_up_Z ((b.toNat : Int) + (s.toNat : Int)) ≤ g :=
        page_round_up_Z_le _ _ hcase HgAl
      have hmemcs : page_round_up_Z ((b.toNat : Int) + (s.toNat : Int)) ∈ cs := by
        rw [hcs]
        exact List.mem_filter.mpr ⟨hc, by simpa using hcle⟩
      have hge : page_round_up_Z ((b.toNat : Int) + (s.toNat : Int)) ≤ g' := by
        rw [hg']
        exact fold_max_ge_in cs (aZ + nZ) _ hmemcs
      have hround : (b.toNat : Int) + (s.toNat : Int) ≤ g' :=
        Int.le_trans (page_round_up_Z_ge _) hge
      apply iv_overlap_eq_false_of_not
      rw [Hg'W, HnW]
      omega
    · -- entry ends above g: it must start at or above g + nZ
      have hgB : g < (b.toNat : Int) + (s.toNat : Int) := by omega
      have hBge : g + nZ ≤ (b.toNat : Int) := by
        rw [← Int.not_lt]
        intro hB
        have ht : iv_overlap (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) b s = true := by
          apply iv_overlap_eq_true_of
          rw [HgW, HnW]
          exact ⟨hgB, hB⟩
        rw [ht] at hno
        exact Bool.noConfusion hno
      apply iv_overlap_eq_false_of_not
      rw [Hg'W, HnW]
      omega
  unfold higher_fit_b
  rw [List.any_eq_true]
  refine ⟨g', hcand, ?_⟩
  have hg'base : g' + nZ ≤ baseZ := by omega
  have h1 : (g' % page_size == 0) = true := by
    rw [beq_iff_eq]
    exact hg'al
  have h2 : decide (aZ + nZ ≤ g') = true := by simpa using hlo
  have h3 : decide (g' + nZ ≤ baseZ) = true := by simpa using hg'base
  rw [h1, h2, h3, hg'free]
  rfl

/-- The easy direction, stated so this file proves an [iff] rather than
    half of one: a candidate the decision procedure accepts really is a
    page-aligned free gap inside the interval. -/
theorem higher_fit_b_sound (maps : List (word × word)) (aZ nZ baseZ : Int)
    (H : higher_fit_b maps aZ nZ baseZ = true) :
    ∃ g, g % page_size = 0 ∧ aZ + nZ ≤ g ∧ g + nZ ≤ baseZ ∧
      region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true := by
  rw [higher_fit_b, List.any_eq_true] at H
  obtain ⟨g, -, Hg⟩ := H
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at Hg
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := Hg
  exact ⟨g, beq_iff_eq.mp h1, of_decide_eq_true h2, of_decide_eq_true h3, h4⟩

/-- …and the two together: [higher_fit_b] decides [no_higher_fit]. -/
theorem no_higher_fit_iff (maps : List (word × word)) (aZ nZ baseZ : Int)
    (HaPos : 0 ≤ aZ) (HnPos : 0 < nZ)
    (HaAl : aZ % page_size = 0) (HnAl : nZ % page_size = 0)
    (Hbase : baseZ < two_pow_64) :
    (higher_fit_b maps aZ nZ baseZ = false ↔ no_higher_fit maps aZ nZ baseZ) := by
  constructor
  · intro Hf g HgAl Hglo Hghi
    cases hfr : region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) with
    | false => rfl
    | true =>
        exfalso
        have hc := higher_fit_b_complete maps aZ nZ baseZ g (by omega) HnPos
          HaAl HnAl Hbase HgAl Hglo Hghi hfr
        rw [hc] at Hf
        exact Bool.noConfusion Hf
  · intro H
    cases hf : higher_fit_b maps aZ nZ baseZ with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨g, hgal, hglo, hghi, hfree⟩ := higher_fit_b_sound maps aZ nZ baseZ hf
        rw [H g hgal hglo hghi] at hfree
        exact Bool.noConfusion hfree

/- =========================================================================
   THE PLACEMENT WITNESS — one concrete address, for proofs that want one

   [Mmap.mmap_spec] constrains a preference-free placement by admissibility
   alone and leaves the choice to the nondeterminism monad, which is right
   for the spec and unhelpful for a proof strategy that wants to compute.
   This is the instance that closes that gap: an executable search, a
   soundness lemma against the spec's own conditions, and a completeness
   lemma saying the search finds an address whenever one exists.

   IT IS KERNEL-*LIKE*, NOT KERNEL-PINNED, and the difference is the whole
   reason it lives here rather than in the spec.  Linux's real answer
   depends on the full VMA set, on a per-exec random base, and on a
   process-controlled layout policy; none of that is recoverable from the
   model's ledger, so no function over the ledger is Linux's function.
   What this one is instead is A correct kernel's answer: every address it
   returns is one the spec admits, which is all a witness has to be.

   Determinism IS claimed here, and may be: [find] returns the first
   fitting candidate in the candidate list's order, so [place] is a
   function of its arguments.  That claim is about this function, not
   about any kernel.
   ========================================================================= -/

/-- The candidate list for a search from a floor, rather than from a
    grant's end.  Same shape as [fit_candidates] — the floor itself, plus
    the page-rounded end of every ledger entry — and
    [higher_fit_b_as_place] below records that it IS the same list, so the
    completeness argument transfers instead of being redone. -/
def search_candidates (maps : List (word × word)) (loZ : Int) : List Int :=
  loZ :: maps.map (fun p => page_round_up_Z ((p.1.toNat : Int) + (p.2.toNat : Int)))

/-- Is [g] a placement this search may return?  These are exactly
    [Mmap.mmap_spec]'s conditions, with the user range given as an
    interval: page-aligned, at or above [loZ], ending at or below [hiZ],
    and disjoint from every recorded mapping. -/
def place_fits (maps : List (word × word)) (loZ hiZ nZ : Int) (g : Int) : Bool :=
  (g % page_size == 0) && decide (loZ ≤ g) && decide (g + nZ ≤ hiZ)
    && region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ)

def place (maps : List (word × word)) (loZ hiZ nZ : Int) : Option Int :=
  (search_candidates maps loZ).find? (place_fits maps loZ hiZ nZ)

/-! ## Soundness: what comes out satisfies the spec's conditions. -/

theorem place_sound (maps : List (word × word)) (loZ hiZ nZ a : Int)
    (H : place maps loZ hiZ nZ = some a) :
    a % page_size = 0 ∧ loZ ≤ a ∧ a + nZ ≤ hiZ ∧
      region_free maps (BitVec.ofInt 64 a) (BitVec.ofInt 64 nZ) = true := by
  unfold place at H
  have Hf := List.find?_some H
  rw [place_fits, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at Hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := Hf
  exact ⟨beq_iff_eq.mp h1, of_decide_eq_true h2, of_decide_eq_true h3, h4⟩

/-! ## Completeness: if any address fits, the search returns one. -/

theorem existsb_find {A : Type} (f : A → Bool) (l : List A)
    (H : l.any f = true) : ∃ x, l.find? f = some x := by
  induction l with
  | nil => simp at H
  | cons y l ih =>
      rw [List.any_cons] at H
      cases hy : f y with
      | true => exact ⟨y, List.find?_cons_of_pos hy⟩
      | false =>
          rw [hy] at H
          simp only [Bool.false_or] at H
          obtain ⟨x, hx⟩ := ih H
          refine ⟨x, ?_⟩
          rw [List.find?_cons_of_neg (p := f) (a := y) (by rw [hy]; simp), hx]

/-- The candidate list a search from [loZ] walks is the one
    [fit_candidates] builds for a grant ending at [loZ], and the two
    fitting tests agree on it.  Stated so [higher_fit_b_complete]'s
    sliding argument carries over rather than being proved twice. -/
theorem higher_fit_b_as_place (maps : List (word × word)) (loZ hiZ nZ : Int) :
    higher_fit_b maps (loZ - nZ) nZ hiZ
      = (search_candidates maps loZ).any (place_fits maps loZ hiZ nZ) := by
  unfold higher_fit_b place_fits search_candidates fit_candidates
  have h : loZ - nZ + nZ = loZ := by omega
  rw [h]

/-- THE NONEMPTINESS OBLIGATION, and it is stated where it cannot compute
    away: quantified over the ledger and over a witness address, so no
    instance of it reduces to a triviality.  It says the search FINDS
    something whenever something is there — not that some particular
    concrete call happens to succeed, which a computation could discharge
    without the search being any good.

    IT IS CONDITIONAL, and the unconditional form is not available.  "The
    admissible set is nonempty" is FALSE for an arbitrary ledger: a full
    one has no gap, which is what [place_finds_nothing_when_full] below
    exhibits.  The honest unconditional statement would be a COUNTING
    argument — the occupied extent plus [nZ] fitting inside the range
    implies a gap exists — and that is not proved here.

    Nobody currently needs it, which is why.  A computational proof
    strategy arrives with a CONCRETE ledger and can exhibit a gap, so
    this is the shape it uses; and the spec's own anti-vacuity does not
    rest on this file at all, since [Mmap.mmap_spec]'s
    [alt (errno_from mmap_errnos) (choose ...)] collapses onto the errno
    arm when no address satisfies the guard, which makes an exhausted
    address space a modeled behaviour rather than a gap.  The counting
    argument is the stronger statement, and it is still open. -/
theorem place_complete (maps : List (word × word)) (loZ hiZ nZ g : Int)
    (Hlo0 : 0 ≤ loZ) (Hn : 0 < nZ)
    (Hloal : loZ % page_size = 0) (Hnal : nZ % page_size = 0)
    (Hhi : hiZ < two_pow_64)
    (HgAl : g % page_size = 0) (Hglo : loZ ≤ g) (Hghi : g + nZ ≤ hiZ)
    (Hfree : region_free maps (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true) :
    ∃ a, place maps loZ hiZ nZ = some a := by
  unfold place
  apply existsb_find
  rw [← higher_fit_b_as_place]
  have Hsubal : (loZ - nZ) % page_size = 0 := by
    rw [Int.sub_emod, Hloal, Hnal]
    simp [page_size]
  exact higher_fit_b_complete maps (loZ - nZ) nZ hiZ g (by omega) Hn Hsubal Hnal Hhi
    HgAl (by omega) Hghi Hfree

/-! ## The two together, at the spec's own interval. -/

/-- The search a caller actually wants: over the whole user address space
    the model describes, against the ledger the spec checks.  [page_size]
    as the floor is what gives the spec's [0 < a]; a caller that wants a
    kernel-like bottom-up base passes it instead, and everything above
    still applies. -/
def place_in_model (h : VmMaps) (nZ : Int) : Option Int :=
  place (h.vm_reserved ++ h.vm_maps) page_size (alloc_top h) nZ

/-- SOUNDNESS AGAINST THE SPEC'S GUARD, and the conclusion is stated at
    [bv_unsigned (Z_to_bv 64 a)] rather than at [a] ON PURPOSE.

    The guard's conditions are about a [word]: [mmap_spec] quantifies
    over [a : word] and constrains [bv_unsigned a].  This search works in
    [Z], so a conclusion phrased about [a : Z] is the guard's conditions
    TRANSPORTED, not the guard's conditions — they coincide only where
    [bv_unsigned (Z_to_bv 64 a) = a], which needs [0 <= a < 2 ^ 64] and
    does not follow from [place_sound] alone.  Saying "conjunct for
    conjunct" of the [Z] form would overstate by exactly that coercion
    step.

    [0 <= nZ] is what closes it, and every caller has it for free:
    [nZ] is [page_round_up_Z (bv_unsigned len)] at each use site.  The
    round-trip is stated as the first conjunct rather than assumed, so a
    caller gets the bridge along with the conditions.

    Below [0 <= nZ] the search is not wrong, merely unconstrained by this
    lemma — no divergence is reachable, since a negative length makes the
    ceiling test pass on candidates the [region_free] test then rejects —
    but an unreachable gap in a statement is still a gap in the
    statement.

    Still minus the budget, which is the caller's to discharge because it
    depends on the model rather than on the ledger. -/
theorem place_in_model_admissible (h : VmMaps) (nZ a : Int) (Hn : 0 ≤ nZ)
    (H : place_in_model h nZ = some a) :
    ((BitVec.ofInt 64 a).toNat : Int) = a ∧
    (((BitVec.ofInt 64 a).toNat : Int) % page_size = 0) ∧
    (0 < ((BitVec.ofInt 64 a).toNat : Int)) ∧
    (((BitVec.ofInt 64 a).toNat : Int) + nZ ≤ alloc_top h) ∧
    region_free (h.vm_reserved ++ h.vm_maps)
      (BitVec.ofInt 64 a) (BitVec.ofInt 64 nZ) = true := by
  unfold place_in_model at H
  obtain ⟨Hal, Hlo, Hhi, Hfree⟩ := place_sound _ _ _ _ _ H
  have Htop := alloc_top_lt h
  have Halo : page_size ≤ a := Hlo
  have Hrt : ((BitVec.ofInt 64 a).toNat : Int) = a := by
    apply bv_unsigned_Z_to_bv_u64
    unfold page_size at Halo
    omega
  rw [Hrt]
  exact ⟨rfl, Hal, by unfold page_size at Halo; omega, Hhi, Hfree⟩

/-- …and [0 <= nZ] is a real hypothesis rather than decoration, which is
    only visible if someone shows the search without it.  Nothing in
    [place] checks the length's sign: at a negative one the ceiling test
    passes trivially and the floor itself is returned.  No caller can
    reach this — every use site passes [page_round_up_Z (bv_unsigned
    len)] — but the lemma above cannot transport its conditions to
    [word] without ruling it out, and this is what stops the hypothesis
    being deleted as an unused premise later. -/
theorem place_accepts_a_negative_length :
    place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = some 4096 := by
  decide

theorem place_in_model_complete (h : VmMaps) (nZ g : Int)
    (Hn : 0 < nZ) (Hnal : nZ % page_size = 0)
    (HgAl : g % page_size = 0) (Hglo : page_size ≤ g)
    (Hghi : g + nZ ≤ alloc_top h)
    (Hfree : region_free (h.vm_reserved ++ h.vm_maps)
      (BitVec.ofInt 64 g) (BitVec.ofInt 64 nZ) = true) :
    ∃ a, place_in_model h nZ = some a := by
  unfold place_in_model
  exact place_complete _ _ _ _ g (by unfold page_size; omega) Hn
    (by unfold page_size; simp) Hnal (alloc_top_lt h) HgAl Hglo Hghi Hfree

/-! ## That the completeness lemma is not vacuous. -/

/-- [place_complete] concludes [exists a, place … = Some a], which cannot
    hold for a reason other than the search returning something — the
    only way it could be hollow is if its HYPOTHESES were unsatisfiable,
    which no reader can see by inspection.  These three instances settle
    that, and they are computations rather than assumptions: the first
    two exhibit ledgers meeting every premise, and the third exhibits one
    that does not, so the function is visibly partial rather than
    trivially total. -/
def witness_ledger : List (word × word) :=
  [(BitVec.ofInt 64 4096, BitVec.ofInt 64 8192)]

/-- The top a hand-built ledger stands under ([State.mkVmMaps] seeds the
    stack pointer at the bottom of the SP window), so the instances
    below are stated at the same bound every other concrete case in the
    tree uses. -/
def demo_top : Int := alloc_top (mkVmMaps [] [] 0 0 0)

/-- The search SKIPS an occupied candidate.  [page_size] is a candidate
    and is inside the entry, so the answer is the entry's page-rounded
    end — not the first thing in the list. -/
theorem place_skips_the_occupied_floor :
    place witness_ledger page_size demo_top 4096 = some 12288 := by
  decide

/-- …and the premises of [place_complete] are met at that instance, by a
    witness the search did not have to be told about: the address it
    returns is itself one. -/
theorem place_complete_premises_are_satisfiable :
    (0 ≤ page_size) ∧ (0 < 4096) ∧
    (page_size % page_size = 0) ∧ (4096 % page_size = 0) ∧
    (demo_top < two_pow_64) ∧
    (12288 % page_size = 0) ∧ (page_size ≤ 12288) ∧
    (12288 + 4096 ≤ demo_top) ∧
    region_free witness_ledger (BitVec.ofInt 64 12288) (BitVec.ofInt 64 4096) = true := by
  unfold page_size demo_top two_pow_64
  rw [alloc_top_mkVmMaps]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- THE PARTIALITY: a ledger with nothing left returns [None].  A search
    that always succeeded would make [place_complete] true and useless,
    which is what this rules out.

    It says nothing about the SPEC's errno arm.  [Mmap.mmap_spec]'s
    [alt (errno_from mmap_errnos) (choose ...)] makes -ENOMEM available
    unconditionally, whatever this file does — see [place_complete]'s
    note above.  What is partial here is the WITNESS, not the spec. -/
def full_ledger : List (word × word) :=
  [(BitVec.ofInt 64 4096, BitVec.ofInt 64 (demo_top - 4096))]

theorem place_finds_nothing_when_full :
    place full_ledger page_size demo_top 4096 = none := by
  decide

end LinuxSem.Common.PlacementSearch
