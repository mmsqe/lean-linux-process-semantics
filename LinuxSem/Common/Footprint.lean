/-
  * Common.Footprint — concrete address regions and their disjointness.

  EXPLORATION / PROTOTYPE.

  This is the SHARED VOCABULARY for "these two memory accesses cannot
  interfere".  It is deliberately tiny, deliberately CONCRETE (a region is
  a pair of [Z] bounds on [bv_unsigned], not a symbolic expression), and
  deliberately independent of [Common.SymExec]: the reflective executor
  discharges its cross-base [SCDisjoint] obligations through it, and a
  Hoare-style frame rule can use exactly the same [region] / [rg_disj]
  pair for its separating conjunction, without either importing the other.

  THE INTERFACE, in three lines:

  - [region] = a half-open byte interval [[rg_lo, rg_hi)] of the 64-bit
    address space, with [rg_lo <= rg_hi] and [0 <= rg_lo],
    [rg_hi <= 2^64] carried as the well-formedness predicate [rg_wf];
  - [covers r a n] = "the [n] bytes at address [a] lie inside [r]";
  - [rg_disj r1 r2] = "[r1] and [r2] do not overlap".

  Everything else is one [lia].  The point is not the theory (there is
  none) but that a per-binary proof states its memory layout ONCE, as a
  handful of [region]s with pairwise [rg_disj] facts, instead of
  re-deriving an address inequality at every load.

  The three regions every one of the examples has are built here:
  [stack_rg] (the [rsp - K .. rsp] frame window), [seg_rg] (a writable
  ELF segment: .data/.sbss/.bss), and [heap_rg] (a brk/mmap grant
  [[base, cur)]).  A bump allocator moving [cur] keeps the SAME region
  name with a larger [rg_hi]: [covers] is monotone in the region
  ([covers_mono]), so nothing downstream re-proves.
  - The record `region := Rg { rg_lo : Z; rg_hi : Z }` becomes the
    structure `region`; Lean names the constructor `region.mk`, so the
     `Rg lo hi` spelling is kept as the abbreviation `Rg`.
  - `lia` is `omega`; the `auto` of `covers_same_disj` is a direct
    hypothesis.
  - `Forall rg_wf rs` is spelled `∀ r ∈ rs, rg_wf r`, the repo-wide
    convention for `List.Forall` (the Lean 4.31 core library has no
    `List.Forall`; same predicate, same places).
-/
import LinuxSem.LinuxProcessSem.BvBase

namespace LinuxSem.Common.Footprint

open LinuxSem.Riscv

/-! ## 1. Regions -/

/-- A concrete half-open byte interval `[rg_lo, rg_hi)` of the 64-bit
    address space. -/
structure region where
  rg_lo : Int
  rg_hi : Int
  deriving DecidableEq, Repr

/-- The  constructor `Rg lo hi` (Lean structures are built with
    `region.mk`). -/
abbrev Rg (rg_lo rg_hi : Int) : region := ⟨rg_lo, rg_hi⟩

/-- Well-formedness: non-negative lower bound, ordered bounds, and an upper
    bound inside the address space. -/
def rg_wf (r : region) : Prop :=
  0 ≤ r.rg_lo ∧ r.rg_lo ≤ r.rg_hi ∧ r.rg_hi ≤ 2 ^ 64

/-- [n] bytes at [a] are inside [r].  Stated on [bv_unsigned] so that the
    caller's arithmetic facts ([sp_window_lo <= bv_unsigned rsp], an
    image's segment bounds) apply directly. -/
def covers (r : region) (a : word) (n : Nat) : Prop :=
  r.rg_lo ≤ (a.toNat : Int) ∧ (a.toNat : Int) + (n : Int) ≤ r.rg_hi

/-- Two regions do not overlap. -/
def rg_disj (r1 r2 : region) : Prop :=
  r1.rg_hi ≤ r2.rg_lo ∨ r2.rg_hi ≤ r1.rg_lo

theorem rg_disj_sym (r1 r2 : region) (H : rg_disj r1 r2) : rg_disj r2 r1 := by
  rcases H with H | H
  · exact Or.inr H
  · exact Or.inl H

/-- Growing a region (a bump allocator raising [cur]) preserves coverage. -/
theorem covers_mono (r r' : region) (a : word) (n : Nat)
    (H : covers r a n) (Hl : r'.rg_lo ≤ r.rg_lo) (Hh : r.rg_hi ≤ r'.rg_hi) :
    covers r' a n := by
  obtain ⟨H1, H2⟩ := H
  exact ⟨by omega, by omega⟩

/-! ## 2. The three consequences a memory proof actually needs -/

/-- (a) No-overflow: an access inside a well-formed region does not wrap
    the address space.  This is the [SCFit] obligation of [SymExec]. -/
theorem covers_nowrap (r : region) (a : word) (n : Nat)
    (Hwf : rg_wf r) (H : covers r a n) :
    (a.toNat : Int) + (n : Int) ≤ 2 ^ 64 := by
  obtain ⟨_, _, Hhi⟩ := Hwf
  obtain ⟨_, H2⟩ := H
  omega

/-- (b) Disjointness of two accesses in disjoint regions, in exactly the
    [rdn_wbytes_disjoint] / [rdn_wbytes_below] shape. -/
theorem covers_disj (r1 r2 : region) (a1 : word) (n1 : Nat) (a2 : word) (n2 : Nat)
    (Hd : rg_disj r1 r2) (H1 : covers r1 a1 n1) (H2 : covers r2 a2 n2) :
    (a1.toNat : Int) + (n1 : Int) ≤ (a2.toNat : Int) ∨
    (a2.toNat : Int) + (n2 : Int) ≤ (a1.toNat : Int) := by
  obtain ⟨H11, H12⟩ := H1
  obtain ⟨H21, H22⟩ := H2
  rcases Hd with H | H
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- (c) Two accesses in the SAME region are disjoint when their offsets
    say so.  This is the case the reflective executor decides by [Z]
    arithmetic; the region supplies only the no-wrap fact. -/
theorem covers_same_disj (r : region) (a1 : word) (n1 : Nat) (a2 : word) (n2 : Nat)
    (_H1 : covers r a1 n1) (_H2 : covers r a2 n2)
    (H : (a1.toNat : Int) + (n1 : Int) ≤ (a2.toNat : Int) ∨
         (a2.toNat : Int) + (n2 : Int) ≤ (a1.toNat : Int)) :
    (a1.toNat : Int) + (n1 : Int) ≤ (a2.toNat : Int) ∨
    (a2.toNat : Int) + (n2 : Int) ≤ (a1.toNat : Int) :=
  H

/-! ## 3. The regions the examples have -/

/-- The current frame window: [K] bytes below [sp], plus the [above]
    bytes at and above it that the startup image occupies (argv/envp).
    Splitting the two is what lets a [sd] into the frame be disjoint from
    a [ld] of [argc] at [sp] without any extra hypothesis. -/
def stack_rg (sp : word) (below above : Int) : region :=
  Rg ((sp.toNat : Int) - below) ((sp.toNat : Int) + above)

/-- A writable ELF segment (.data / .sbss / .bss): plain literal bounds. -/
def seg_rg (lo hi : Int) : region := Rg lo hi

/-- A heap grant [[base, cur)].  [base] is symbolic (an mmap/brk result),
    [cur] moves as a bump allocator allocates. -/
def heap_rg (base : word) (cur : Int) : region :=
  Rg (base.toNat : Int) ((base.toNat : Int) + cur)

theorem heap_rg_bump (base : word) (cur cur' : Int) (a : word) (n : Nat)
    (Hle : cur ≤ cur') (H : covers (heap_rg base cur) a n) :
    covers (heap_rg base cur') a n := by
  refine covers_mono (heap_rg base cur) (heap_rg base cur') a n H ?_ ?_
  · simp [heap_rg]
  · simp [heap_rg]
    omega

/-- A layout is a list of regions that are pairwise disjoint and
    well-formed.  This is the thing a per-binary proof states once. -/
def layout_wf (rs : List region) : Prop :=
  (∀ r ∈ rs, rg_wf r) ∧
  ∀ i j, i < j → j < rs.length →
    rg_disj (rs.getD i (Rg 0 0)) (rs.getD j (Rg 0 0))

/-! -/

example : covers (seg_rg 0 16) (8 : word) 8 := by unfold covers; decide

example : ¬ covers (seg_rg 0 16) (16 : word) 1 := by unfold covers; decide

example : rg_disj (seg_rg 0 16) (seg_rg 16 32) := by unfold rg_disj; decide

example : stack_rg (8 : word) 4 4 = Rg 4 12 := by decide

example : heap_rg (16 : word) 32 = Rg 16 48 := by decide

end LinuxSem.Common.Footprint
