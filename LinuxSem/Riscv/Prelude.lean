/-
  * Prelude: bitvector helpers and a tiny keyed map.

  `word` and `reg` are fixed-width abbreviations: `word` is `BitVec 64`
  and `reg` is `BitVec 5`.

  The keyed map exposes [bvmap], [bvmap_get], [bvmap_set], [bvmap_empty]
  and the [bvmap_get_set_same]/[bvmap_get_set_other] lemmas, backed by an
  association list rather than a radix tree.  The two are
  *extensionally identical* — the map is only ever used as an abstract
  finite map over register indices — and the association-list lemmas are
  shorter and less brittle.  If extraction performance of the eventual
  interpreter matters, a radix tree can go in behind the same interface;
  nothing outside this file depends on the representation.
-/
namespace LinuxSem.Riscv

/-- A 64-bit machine word (register value, address, syscall argument...). -/
abbrev word := BitVec 64

/-- A 5-bit register index (`x0` .. `x31`). -/
abbrev reg := BitVec 5

/-- A memory / file / event byte.

  It lives here rather than in `LinuxProcessSem.BvBase` so that modules
  which only need bytes (e.g. `Fs`) can depend on the ISA prelude alone.
  `BvBase` re-exports it. -/
abbrev byte := BitVec 8

/-- Unsigned `≤` as a boolean (unsigned `<` is `bv_ltu`). -/
def bv_leu {n : Nat} (a b : BitVec n) : Bool := decide (a.toNat ≤ b.toNat)

/-! ## Bit extraction and extension -/

/-- Extract `len` bits starting at `lo` (inclusive): out-of-range bits
  read as zero. -/
def bits {n : Nat} (lo len : Nat) (w : BitVec n) : BitVec len :=
  w.extractLsb' lo len

/-- Sign-extend a bitvector to width `m`. -/
def sext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m :=
  b.signExtend m

/-- Zero-extend a bitvector to width `m`. -/
def zext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m :=
  b.zeroExtend m

/-- Untyped bit test, used by the decoder. -/
def bit {n : Nat} (i : Nat) (w : BitVec n) : Bool :=
  w.getLsbD i

/-! ## Signedness-explicit wrappers

Most `bv` operations mean the same thing under a signed or unsigned
reading, but comparisons and the high half of a full-width product do
not.  Those are isolated here so that every use site names the
interpretation it wants. -/

/-- Signed `<`. -/
def bv_lts {n : Nat} (a b : BitVec n) : Bool := decide (a.toInt < b.toInt)

/-- Unsigned `<`. -/
def bv_ltu {n : Nat} (a b : BitVec n) : Bool := decide (a.toNat < b.toNat)

/-- Equality is signedness-independent; included for uniformity. -/
def bv_eqb {n : Nat} (a b : BitVec n) : Bool := a == b

/-- High `n` bits of the exact 2n-bit signed-by-signed product. -/
def bv_mulhss {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n ((a.toInt * b.toInt) >>> n)

/-- High `n` bits of the exact 2n-bit signed-by-unsigned product. -/
def bv_mulhsu {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n ((a.toInt * (b.toNat : Int)) >>> n)

/-- High `n` bits of the exact 2n-bit unsigned-by-unsigned product. -/
def bv_mulhuu {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n (((a.toNat : Int) * (b.toNat : Int)) >>> n)

/-! ## A tiny keyed map

The key is the unsigned value `bv_key k`, a `Nat`, and the map is an
association list that keeps the most recent binding first. -/

/-- Map a bitvector key (register index, address) to a `Nat` key.  The
  `+ 1` shifts the key space off zero, so every key is positive. -/
def bv_key {n : Nat} (b : BitVec n) : Nat := b.toNat + 1

theorem bv_key_inj {n : Nat} {b1 b2 : BitVec n} (h : bv_key b1 = bv_key b2) : b1 = b2 := by
  unfold bv_key at h
  have : b1.toNat = b2.toNat := by omega
  exact BitVec.eq_of_toNat_eq this

/-- A finite map from bitvector keys to values. -/
abbrev BvMap (α : Type) := List (Nat × α)

/-- Look a key up; the most recent binding wins. -/
def bvmap_get {α : Type} (k : Nat) (m : BvMap α) : Option α :=
  (m.find? (fun p => p.1 == k)).map (·.2)

/-- Bind a key.  Lookup takes the most recent binding, so older ones are
    shadowed but kept.  That is fine for the model (the map is only read
    through `bvmap_get`), but a long-running extracted interpreter would
    grow the list on every register write; add a compaction or restore the
    radix tree before extracting one. -/
def bvmap_set {α : Type} (k : Nat) (x : α) (m : BvMap α) : BvMap α :=
  (k, x) :: m

/-- The empty map. -/
def bvmap_empty {α : Type} : BvMap α := []

theorem bvmap_get_set_same {α : Type} (k : Nat) (x : α) (m : BvMap α) :
    bvmap_get k (bvmap_set k x m) = some x := by
  simp [bvmap_get, bvmap_set]

theorem bvmap_get_set_other {α : Type} (k k' : Nat) (x : α) (m : BvMap α)
    (h : k ≠ k') : bvmap_get k' (bvmap_set k x m) = bvmap_get k' m := by
  have hb : (k == k') = false := by
    have : (k == k') = true ↔ k = k' := beq_iff_eq
    by_cases hh : (k == k') = true
    · exact absurd (this.mp hh) h
    · simpa using hh
  simp [bvmap_get, bvmap_set, hb]

/-- Look up by a bitvector key (the form the ISA semantics uses). -/
def bvmapGet {n : Nat} {α : Type} (k : BitVec n) (m : BvMap α) : Option α :=
  bvmap_get (bv_key k) m

/-- Bind by a bitvector key. -/
def bvmapSet {n : Nat} {α : Type} (k : BitVec n) (x : α) (m : BvMap α) : BvMap α :=
  bvmap_set (bv_key k) x m

theorem bvmapGet_set_same {n : Nat} {α : Type} (k : BitVec n) (x : α) (m : BvMap α) :
    bvmapGet k (bvmapSet k x m) = some x :=
  bvmap_get_set_same _ _ _

theorem bvmapGet_set_other {n : Nat} {α : Type} (k k' : BitVec n) (x : α) (m : BvMap α)
    (h : k ≠ k') : bvmapGet k' (bvmapSet k x m) = bvmapGet k' m :=
  bvmap_get_set_other _ _ _ _ (fun hk => h (bv_key_inj hk))

end LinuxSem.Riscv
