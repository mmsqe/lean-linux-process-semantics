/-
  * Common.MuslStrlen — musl's word-at-a-time `strlen`, shared machinery

    gcc 15 no longer inlines `strlen`: where gcc 9 recognized the C
    source's hand-written length loops and emitted them inline, gcc 15
    emits `jal strlen` and the link pulls in musl's implementation.  So
    every `-Os` musl binary in this repo that measures a string now
    contains the SAME routine, and every source-side proof has to reason
    about it.  This module holds the part of that reasoning that does not
    depend on where the routine was linked.

    ** What musl's `strlen` does

    Given `s`, with `ONES = 0x0101010101010101` and
    `HIGHS = 0x8080808080808080`:

      1. byte scan from `s` until the pointer is 8-aligned, stopping
         early if a NUL is found;
      2. from there, load a full aligned 8-byte word `x` at a time and
         test `haszero(x) = (x - ONES) & ~x & HIGHS`, stopping at the
         first word for which the test is nonzero;
      3. byte scan inside that word down to the NUL;
      4. return (found pointer) - s.

    ** Why the has-zero test is exact (module `HZ`)

    `HZ` proves the test EXACT at word granularity, as the pair

      `Tz_nozero`  : all eight bytes of `x` nonzero  ->  `Tz x = 0`
      `Tz_haszero` : byte `i` of `x` is zero and every LOWER byte is
                     nonzero                          ->  `Tz x ≠ 0`

    over plain `Int` (`zb x i` is byte `i` of `x`; `Tz` is the machine's
    test word as an `Int` function, matched to the actual instruction
    sequence by `v_haszero` below).

    The subtlety the second statement encodes: the test is NOT byte-wise
    exact.  Subtracting `ONES` propagates a borrow upwards, so a byte
    equal to 1 can be turned into 0x00 -> 0xff by an incoming borrow and
    register as a false positive.  But a borrow can only START at a byte
    that is already zero, so a false positive at byte `i` implies a
    genuine zero byte strictly below `i`.  Hence the WORD-level verdict
    "some byte is zero" is exact, which is all the loop needs: it exits
    the word loop and then re-scans the word byte by byte.  That is why
    `Tz_haszero` is stated with the "all lower bytes nonzero" side
    condition rather than for an arbitrary zero byte.

    ** The over-read past the NUL, and exactly what makes it sound

    READ THIS BEFORE REUSING `read_word_stack` / `argv_word_readable`.

    Step 2 loads a whole aligned word.  When the NUL sits in the middle
    of that word, the `ld` reads up to 7 bytes PAST the NUL — bytes that
    are not part of the string at all.  Real musl relies on the fact that
    an aligned 8-byte load cannot cross a page boundary; our model has no
    pages, so the load must be shown to land inside mapped memory or the
    machine faults and the proof dies.

    The argument here is specific to ARGV/ENVP STRINGS in the INITIAL
    STACK IMAGE.  `StackLayout.build_stack_bytes` lays out the argv/envp
    string blob and then ALWAYS appends `pad ++ at_random_bytes` — at
    least 16 further readable bytes — so there are >= 16 readable bytes
    after the last argv string's NUL.  `bsb_len_lower` states that lower
    bound on the image length, `total_arg_bytes_firstn_S` locates string
    `k` inside the blob, `bsb_word_k` splits the image just before byte
    `m` of string `k` leaving >= 8 bytes, and `read_word_stack` turns
    that split into a total 8-byte `rdn`.  `argv_word_readable` is the
    same fact stated over `wrap_mem`.

    WARNING.  This soundness argument does NOT transfer to:

      - a string in a heap/brk or mmap buffer — there is no analogue of
        the AT_RANDOM tail, and a string ending at the last byte of the
        break or of an mmap region over-reads into unmapped memory;
      - a string ending at the top of ITS OWN mapping, for the same
        reason;
      - a caller-chosen buffer whose length is not tied to the layout.

    In those cases the over-read is a genuine fault in the model (and,
    on hardware, is only saved by page granularity).  Any example that
    calls musl `strlen` on a non-argv string needs its own readability
    lemma; only the `HZ` arithmetic and the `bytes_le_to_Z`/`v_haszero`
    bridge below carry over unchanged.

    ** What is NOT here: the walk itself

    The per-instruction walk over the routine (align scan, word loop,
    final byte scan, `a0 := a5 - a0` tail) stays in the example.  It is
    pinned to CONCRETE addresses: every step cites that binary's
    `SF_<addr>`/`SD_<addr>` fetch/decode lemmas, and the whole chaining
    machinery in `Common/StepTac` (`wlit`/`wlits`/`norm_pc`) normalizes
    pc values by computation on a CLOSED word literal.  Abstracting the
    entry address into a section variable would break every one of those
    ~30 normalizations at once, so the walk is left per-example; it is a
    mechanical address-shift of the `grep_args_ns` copy, which calls into
    this file for all of its content.

    Reference consumer: `Examples/grep_args_ns/Proof`.

    NOTES.

    - `Z` → `Int`, `nat` → `Nat`, `list` → `List`, `Z_of_nat` →
      `(· : Nat) → Int` coercions.  `Z_to_bv 8 0` → `BitVec.ofInt 8 0`,
      `bv_unsigned w` → `(w.toNat : Int)`.
    - `Z.land` / `Z.lxor` / `Z.shiftr` have no `Int` counterpart in Lean
      core (the same situation as `Sys/Uapi`'s `z_lor`/`zland`), so this
      file carries the three ops it needs — `zland`, `zlxor`,
      `z_shiftr` — defined through `Nat`, which agrees with the `Z`
      versions whenever the operands are non-negative.  Every `HZ`
      lemma that CONSUMES one of them (`zb_land`, `zb_lxor`) therefore
      takes the non-negativity of its operands explicitly, and `zb`
      itself is `Nat`-division based (`x.toNat`), which agrees with the
      `Z` original on `0 <= x` — the only values any caller passes.  The
      arithmetic statements themselves are unchanged.
    - `vm_compute`-sealed byte computations become `decide`; the
      `Z`-literal arithmetic of `Tz_nozero`/`sum_byte_255` is done with
      `omega` over the same explicit digit identities.
    - `Section ArgvWord`'s variables stay explicit parameters (Lean has
      no section-hypothesis discharge), the same shape `CatExec`/
      `SeqExec` use for their `WithFP` sections.       That explicitness, plus the `Nat` core of the byte algebra
      (`zbN`/`zdigN` and the cast plumbing around them), is why this tree
      is longer than the 802-line original.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac

set_option autoImplicit false
set_option maxRecDepth 10000
-- Same rationale as `PropExec`/`CatExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.MuslStrlen

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac

/-! ## `Int` bitwise ops through `Nat`

    Lean core has no `Int.land`/`Int.lxor`/`Int.shiftr`; `Sys/Uapi` takes
    the same route for `Z.land`/`Z.lor`.  The definitions agree with the
    `Z` originals on non-negative operands, which is every use site in
    this file. -/

/-! The bitwise vocabulary is `PropExec`'s (`zland`, `zlxor`, `zlor`, all
    `Nat`-backed, agreeing with `Z.land`/`Z.lxor`/`Z.lor` on non-negative
    arguments); only the right shift is new here, because `HZ`'s byte
    extraction needs it. -/

/-- Logical shift right of an `Int`, read through `Nat`. -/
def z_shiftr (a : Int) (n : Nat) : Int := ((a.toNat >>> n : Nat) : Int)

/- ######################################################################### -/
/- musl's word-at-a-time zero-byte test                                      -/
/-                                                                           -/
/-   haszero(x) = (x - 0x0101..01) & ~x & 0x8080..80                         -/
/-                                                                           -/
/- This module proves that test EXACT -- zero iff no byte of [x] is zero --  -/
/- by byte-wise arithmetic over [Int] (the borrow chain of the subtraction   -/
/- starts only at a zero byte, so a false positive at byte [i] implies a     -/
/- real zero byte below [i]).  It is self-contained [Int] reasoning;         -/
/- [zb x i] is byte [i] of [x] and [zdig] is the little-endian digit sum.    -/
/- ######################################################################### -/

namespace HZ

/- byte i of x -/
def zb (x : Int) (i : Nat) : Int := ((x.toNat / 2 ^ (8 * i)) % 256 : Nat)

def zdig : List Int → Int
  | [] => 0
  | d :: r => d + 256 * zdig r

@[simp] theorem zdig_nil : zdig [] = 0 := rfl
@[simp] theorem zdig_cons (d : Int) (r : List Int) : zdig (d :: r) = d + 256 * zdig r := rfl

theorem pow2_8i_pos (i : Nat) : (0 : Int) < 2 ^ (8 * i) := by
  have h2 : (0 : Int) < 2 := by decide
  exact Int.pow_pos h2

theorem zb_bound (x : Int) (i : Nat) : 0 ≤ zb x i ∧ zb x i < 256 := by
  unfold zb
  refine ⟨Int.natCast_nonneg _, ?_⟩
  exact Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))

theorem zb_0 (i : Nat) : zb 0 i = 0 := by
  simp [zb]

/- ---------- bitwise distribution ---------- -/

theorem land_land_m (a b m : Int) :
    zland (zland a b) m = zland (zland a m) (zland b m) := by
  simp only [zland, Int.toNat_natCast]
  congr 1
  ac_rfl

theorem land_lxor_m (a b m : Int) :
    zland (zlxor a b) m = zlxor (zland a m) (zland b m) := by
  simp only [zland, zlxor, Int.toNat_natCast]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.toNat.testBit n <;> cases b.toNat.testBit n <;> cases m.toNat.testBit n <;> rfl

theorem lxor_lt64 (a b : Int) (Ha : 0 ≤ a ∧ a < 2 ^ 64) (Hb : 0 ≤ b ∧ b < 2 ^ 64) :
    0 ≤ zlxor a b ∧ zlxor a b < 2 ^ 64 := by
  have ha : a.toNat < 2 ^ 64 := by
    have h : ((a.toNat : Int)) < 2 ^ 64 := by rw [Int.toNat_of_nonneg Ha.1]; exact Ha.2
    exact Int.ofNat_lt.mp h
  have hb : b.toNat < 2 ^ 64 := by
    have h : ((b.toNat : Int)) < 2 ^ 64 := by rw [Int.toNat_of_nonneg Hb.1]; exact Hb.2
    exact Int.ofNat_lt.mp h
  refine ⟨Int.natCast_nonneg _, ?_⟩
  exact Int.ofNat_lt.mpr (Nat.xor_lt_two_pow ha hb)

/-- `a % 256` is the low byte of `a` (`255` is `2^8 - 1`,  `Z.ones 8`). -/
theorem nat_mod_256_and (a : Nat) : a % 256 = a &&& 255 := by
  have h := Nat.and_two_pow_sub_one_eq_mod a 8
  simpa using h.symm

/-- `Int.toNat` of the `Int` literal `255` (the `zland` mask below). -/
theorem toNat_255 : (Int.toNat (255 : Int)) = 255 := rfl
theorem toNat_128 : (Int.toNat (128 : Int)) = 128 := rfl

/-- `&&&` distributes over `^^^` —  `Z.land_lxor`, at `Nat`. -/
theorem nat_and_xor_distrib (a b m : Nat) :
    (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit n <;> cases b.testBit n <;> cases m.testBit n <;> rfl

theorem zb_alt (x : Int) (i : Nat) : zb x i = zland (z_shiftr x (8 * i)) 255 := by
  simp only [zb, zland, z_shiftr, Int.toNat_natCast, toNat_255, Nat.shiftRight_eq_div_pow]
  rw [nat_mod_256_and]

theorem zb_land (u w : Int) (i : Nat) :
    zb (zland u w) i = zland (zb u i) (zb w i) := by
  rw [zb_alt, zb_alt u i, zb_alt w i]
  simp only [zland, z_shiftr, Int.toNat_natCast, toNat_255]
  congr 1
  rw [Nat.shiftRight_and_distrib]
  ac_rfl

theorem zb_lxor (u w : Int) (i : Nat) :
    zb (zlxor u w) i = zlxor (zb u i) (zb w i) := by
  rw [zb_alt, zb_alt u i, zb_alt w i]
  simp only [zland, zlxor, z_shiftr, Int.toNat_natCast, toNat_255]
  congr 1
  rw [Nat.shiftRight_xor_distrib, nat_and_xor_distrib]

/-! ### `Nat`-level core of the byte algebra

    Every `HZ` value is a byte, a digit sum or a word of `Nat` digits, so
    the arithmetic lives at `Nat` and the `Int` statements above it are
    restated through the coercions. -/

/-- [zb] at `Nat`. -/
def zbN (x i : Nat) : Nat := x / 2 ^ (8 * i) % 256

/-- [zdig] at `Nat`. -/
def zdigN : List Nat → Nat
  | [] => 0
  | d :: r => d + 256 * zdigN r

@[simp] theorem zdigN_nil : zdigN [] = 0 := rfl
@[simp] theorem zdigN_cons (d : Nat) (r : List Nat) : zdigN (d :: r) = d + 256 * zdigN r := rfl

theorem zb_eq_zbN (x : Int) (i : Nat) : zb x i = (zbN x.toNat i : Int) := rfl

theorem zdigN_nonneg (ds : List Nat) : 0 ≤ zdigN ds := Nat.zero_le _

theorem zdig_nonneg : ∀ (ds : List Int),
    (∀ d ∈ ds, 0 ≤ d ∧ d < 256) → 0 ≤ zdig ds
  | [], _ => by simp [zdig]
  | d :: r, H => by
    have hd : 0 ≤ d := (H d (List.mem_cons_self ..)).1
    have hr : ∀ x ∈ r, 0 ≤ x ∧ x < 256 := fun x hx => H x (List.mem_cons_of_mem _ hx)
    have hz := zdig_nonneg r hr
    show 0 ≤ d + 256 * zdig r
    omega

theorem zdigN_lt : ∀ ds : List Nat, (∀ d ∈ ds, d < 256) → zdigN ds < 2 ^ (8 * ds.length)
  | [], _ => by simp [zdigN]
  | d :: r, h => by
    have hd : d < 256 := h d (List.mem_cons_self ..)
    have hr : ∀ x ∈ r, x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih := zdigN_lt r hr
    have hpow : 2 ^ (8 * (r.length + 1)) = 256 * 2 ^ (8 * r.length) := by
      rw [show 8 * (r.length + 1) = 8 + 8 * r.length by omega, Nat.pow_add]
    show d + 256 * zdigN r < 2 ^ (8 * (d :: r).length)
    rw [List.length_cons, hpow]
    omega

theorem forall_map_toNat_lt (ds : List Int)
    (H : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) :
    ∀ d ∈ ds.map Int.toNat, d < 256 := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have h := H e he
  have h' : ((e.toNat : Int)) < 256 := by rw [Int.toNat_of_nonneg h.1]; exact h.2
  exact Int.ofNat_lt.mp h'

/-- The `Int` digit sum is the `Nat` one on bytes. -/
theorem zdig_eq_zdigN (ds : List Int) (H : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) :
    zdig ds = (zdigN (ds.map Int.toNat) : Int) := by
  induction ds with
  | nil => rfl
  | cons d r ih =>
    have hd := H d (List.mem_cons_self ..)
    have hr : ∀ x ∈ r, 0 ≤ x ∧ x < 256 := fun x hx => H x (List.mem_cons_of_mem _ hx)
    show d + 256 * zdig r = _
    rw [ih hr, ← Int.toNat_of_nonneg hd.1,
      show ((256 : Int)) = ((256 : Nat) : Int) from rfl,
      ← Int.natCast_mul, ← Int.natCast_add]
    rfl

theorem zdig_lt (ds : List Int) (H : ∀ d ∈ ds, 0 ≤ d ∧ d < 256) :
    zdig ds < 2 ^ (8 * ds.length) := by
  rw [zdig_eq_zdigN ds H]
  have hnat := zdigN_lt (ds.map Int.toNat) (forall_map_toNat_lt ds H)
  have hlen : (ds.map Int.toNat).length = ds.length := List.length_map ..
  rw [hlen] at hnat
  have h' : ((2 ^ (8 * ds.length) : Nat) : Int) = 2 ^ (8 * ds.length) := by
    rw [Int.natCast_pow]; rfl
  rw [← h']
  exact Int.ofNat_lt.mpr hnat

/- ---------- byte extraction from a digit sum ---------- -/

theorem zbN_zdigN : ∀ (ds : List Nat) (i : Nat), (∀ d ∈ ds, d < 256) → i < ds.length →
    zbN (zdigN ds) i = ds[i]?.getD 0
  | [], i, _, hi => by simp at hi
  | d :: r, i, h, hi => by
    have hd : d < 256 := h d (List.mem_cons_self ..)
    have hr : ∀ x ∈ r, x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases i with
    | zero =>
      show (d + 256 * zdigN r) / 2 ^ (8 * 0) % 256 = _
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getElem?_cons_zero,
        Option.getD_some]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ j =>
      have hpow : 2 ^ (8 * (j + 1)) = 256 * 2 ^ (8 * j) := by
        rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add]
      show (d + 256 * zdigN r) / 2 ^ (8 * (j + 1)) % 256 = _
      rw [hpow, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt hd, Nat.zero_add]
      show zbN (zdigN r) j = r[j]?.getD 0
      exact zbN_zdigN r j hr (by simp only [List.length_cons] at hi; omega)

theorem zb_zdig (ds : List Int) (H : ∀ d ∈ ds, 0 ≤ d ∧ d < 256)
    (i : Nat) (Hi : i < ds.length) :
    zb (zdig ds) i = ds[i]?.getD 0 := by
  rw [zdig_eq_zdigN ds H, zb_eq_zbN, Int.toNat_natCast]
  rw [zbN_zdigN (ds.map Int.toNat) i (forall_map_toNat_lt ds H)
    (by rw [List.length_map]; exact Hi)]
  rw [List.getElem?_map]
  cases h : ds[i]? with
  | none => simp [h]
  | some d =>
    have hd := H d (List.mem_of_getElem? h)
    simp only [Option.map_some, Option.getD_some]
    rw [Int.toNat_of_nonneg hd.1]

/-- Base-`256` digit expansion: a number below `2^(8k)` is the digit sum
    of its own `k` low bytes. -/
theorem zdigN_digits : ∀ (k n : Nat), n < 2 ^ (8 * k) →
    zdigN ((List.range k).map (fun j => n / 2 ^ (8 * j) % 256)) = n
  | 0, n, h => by
    have hn : n = 0 := by simpa using h
    subst hn; rfl
  | k + 1, n, h => by
    have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    rw [hpow] at h
    have hdecomp : n = n % 256 + 256 * (n / 256) := by
      have := Nat.div_add_mod n 256
      omega
    have hq_lt : n / 256 < 2 ^ (8 * k) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    have hmap : (List.range (k + 1)).map (fun j => n / 2 ^ (8 * j) % 256)
        = n % 256 :: (List.range k).map (fun j => n / 256 / 2 ^ (8 * j) % 256) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · show n / 2 ^ (8 * 0) % 256 = n % 256
        rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
      · apply List.map_congr_left
        intro j _
        show n / 2 ^ (8 * (j + 1)) % 256 = n / 256 / 2 ^ (8 * j) % 256
        have hp2 : 2 ^ (8 * (j + 1)) = 256 * 2 ^ (8 * j) := by
          rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add]
        rw [hp2, ← Nat.div_div_eq_div_mul]
    rw [hmap, zdigN_cons, zdigN_digits k (n / 256) hq_lt]
    omega

theorem zdig_recon8 (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    x = zdig [zb x 0, zb x 1, zb x 2, zb x 3, zb x 4, zb x 5, zb x 6, zb x 7] := by
  have hx8 : x.toNat < 2 ^ (8 * 8) := by
    have h : ((x.toNat : Int)) < 2 ^ 64 := by rw [Int.toNat_of_nonneg Hx.1]; exact Hx.2
    have h' : x.toNat < 2 ^ 64 := Int.ofNat_lt.mp h
    have h2 : (2 : Nat) ^ (8 * 8) = 2 ^ 64 := by decide
    omega
  have hF : ∀ d ∈ [zb x 0, zb x 1, zb x 2, zb x 3, zb x 4, zb x 5, zb x 6, zb x 7],
      0 ≤ d ∧ d < 256 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact zb_bound x _
  have hexp : (List.range 8).map (fun j => x.toNat / 2 ^ (8 * j) % 256)
      = [x.toNat / 2 ^ (8*0) % 256, x.toNat / 2 ^ (8*1) % 256,
         x.toNat / 2 ^ (8*2) % 256, x.toNat / 2 ^ (8*3) % 256,
         x.toNat / 2 ^ (8*4) % 256, x.toNat / 2 ^ (8*5) % 256,
         x.toNat / 2 ^ (8*6) % 256, x.toNat / 2 ^ (8*7) % 256] := rfl
  have hlist2 : ([zb x 0, zb x 1, zb x 2, zb x 3, zb x 4, zb x 5, zb x 6, zb x 7].map
      Int.toNat)
      = [x.toNat / 2 ^ (8*0) % 256, x.toNat / 2 ^ (8*1) % 256,
         x.toNat / 2 ^ (8*2) % 256, x.toNat / 2 ^ (8*3) % 256,
         x.toNat / 2 ^ (8*4) % 256, x.toNat / 2 ^ (8*5) % 256,
         x.toNat / 2 ^ (8*6) % 256, x.toNat / 2 ^ (8*7) % 256] := rfl
  have hstep : zdigN [x.toNat / 2 ^ (8*0) % 256, x.toNat / 2 ^ (8*1) % 256,
         x.toNat / 2 ^ (8*2) % 256, x.toNat / 2 ^ (8*3) % 256,
         x.toNat / 2 ^ (8*4) % 256, x.toNat / 2 ^ (8*5) % 256,
         x.toNat / 2 ^ (8*6) % 256, x.toNat / 2 ^ (8*7) % 256] = x.toNat := by
    rw [← hexp]
    exact zdigN_digits 8 x.toNat hx8
  rw [zdig_eq_zdigN _ hF, hlist2, hstep, Int.toNat_of_nonneg Hx.1]

theorem zb_eq0 (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64)
    (H : ∀ i, i < 8 → zb x i = 0) : x = 0 := by
  rw [zdig_recon8 x Hx]
  have h0 : zb x 0 = 0 := H 0 (by omega)
  have h1 : zb x 1 = 0 := H 1 (by omega)
  have h2 : zb x 2 = 0 := H 2 (by omega)
  have h3 : zb x 3 = 0 := H 3 (by omega)
  have h4 : zb x 4 = 0 := H 4 (by omega)
  have h5 : zb x 5 = 0 := H 5 (by omega)
  have h6 : zb x 6 = 0 := H 6 (by omega)
  have h7 : zb x 7 = 0 := H 7 (by omega)
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp [zdig]

theorem zb_neq0 (x : Int) (i : Nat) (H : zb x i ≠ 0) : x ≠ 0 := by
  intro Hc
  subst Hc
  exact H (zb_0 i)

/- ---------- the musl has-zero-byte test ---------- -/

/-- musl's `ONES` (`0x0101010101010101`) negated mod `2^64`:
    `0xFEFEFEFEFEFEFEFF`. -/
def ONESNEG : Int := 18374403900871474943
/-- `0x8080808080808080`: the high bit of every byte. -/
def HIGHS : Int := 9259542123273814144
/-- `2^64 - 1`. -/
def ALLONES : Int := 18446744073709551615

/-- The machine's has-zero test word, as an `Int` function. -/
def Tz (x : Int) : Int :=
  zland (zland ((x + ONESNEG) % 2 ^ 64) (zlxor x ALLONES)) HIGHS

theorem land_le_r (a b : Int) (Hb : 0 ≤ b) : zland a b ≤ b := by
  have h1 : (zland a b).toNat ≤ b.toNat := by
    simp only [zland, Int.toNat_natCast]
    exact Nat.and_le_right
  have hz : 0 ≤ zland a b := Int.natCast_nonneg (a.toNat &&& b.toNat)
  rw [← Int.toNat_of_nonneg hz, ← Int.toNat_of_nonneg Hb]
  exact Int.ofNat_le.mpr h1

theorem land_le_l (a b : Int) (Ha : 0 ≤ a) : zland a b ≤ a := by
  have h1 : (zland a b).toNat ≤ a.toNat := by
    simp only [zland, Int.toNat_natCast]
    exact Nat.and_le_left
  have hz : 0 ≤ zland a b := Int.natCast_nonneg (a.toNat &&& b.toNat)
  rw [← Int.toNat_of_nonneg hz, ← Int.toNat_of_nonneg Ha]
  exact Int.ofNat_le.mpr h1

theorem Tz_range (x : Int) : 0 ≤ Tz x ∧ Tz x < 2 ^ 64 := by
  constructor
  · exact Int.natCast_nonneg _
  · have h := land_le_r (zland ((x + ONESNEG) % 2 ^ 64) (zlxor x ALLONES)) HIGHS
      (by decide : (0 : Int) ≤ HIGHS)
    have hH : HIGHS < 2 ^ 64 := by decide
    show zland (zland ((x + ONESNEG) % 2 ^ 64) (zlxor x ALLONES)) HIGHS < 2 ^ 64
    omega

/-- The eight cases of  `Ltac by8`, at the level of the index. -/
theorem lt_eight_cases (i : Nat) (Hi : i < 8) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega

theorem zb_ALLONES (i : Nat) (Hi : i < 8) : zb ALLONES i = 255 := by
  rcases lt_eight_cases i Hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem zb_HIGHS (i : Nat) (Hi : i < 8) : zb HIGHS i = 128 := by
  rcases lt_eight_cases i Hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Tz_byte (x : Int) (i : Nat) (Hi : i < 8) :
    zb (Tz x) i
      = zland (zland (zb ((x + ONESNEG) % 2 ^ 64) i) (zlxor (zb x i) 255)) 128 := by
  unfold Tz
  have h1 := zb_land (zland ((x + ONESNEG) % 2 ^ 64) (zlxor x ALLONES)) HIGHS i
  have h2 := zb_land ((x + ONESNEG) % 2 ^ 64) (zlxor x ALLONES) i
  have h3 := zb_lxor x ALLONES i
  rw [h1, h2, h3, zb_ALLONES i Hi, zb_HIGHS i Hi]

/- ---------- cast plumbing ---------- -/

theorem toNat_pow_two (k : Nat) : ((2 : Int) ^ k).toNat = 2 ^ k := by
  have h2 : ((2 : Int)) = ((2 : Nat) : Int) := rfl
  rw [h2, ← Int.natCast_pow]
  exact Int.toNat_natCast _

/-- `Int.ofNat_lt` with the right-hand side in the `Int`-power spelling. -/
theorem ofNat_lt_two_pow (n k : Nat) : ((n : Int) < (2 : Int) ^ k ↔ n < 2 ^ k) := by
  have h2 : ((2 : Int)) = ((2 : Nat) : Int) := rfl
  rw [h2, ← Int.natCast_pow]
  exact Int.ofNat_lt

theorem toNat_256 : (Int.toNat (256 : Int)) = 256 := rfl

theorem emod_natCast (m n : Nat) : ((m : Int) % (n : Int)) = ((m % n : Nat) : Int) :=
  (Int.natCast_emod m n).symm

/- ---------- byte split ---------- -/

/-- Adding a multiple of `256` shifted to digit `i` does not change digit
    `i`: `Z.div_add` / `Z.mod_add` step, at `Nat`. -/
theorem zbN_add_shift (a m i : Nat) :
    zbN (a + 2 ^ (8 * i) * (256 * m)) i = zbN a i := by
  show (a + 2 ^ (8 * i) * (256 * m)) / 2 ^ (8 * i) % 256
    = a / 2 ^ (8 * i) % 256
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.add_mul_mod_self_left]

theorem zbN_split (lo hi i : Nat) (hlo : lo < 2 ^ (8 * i)) :
    zbN (lo + 2 ^ (8 * i) * hi) i = hi % 256 := by
  show (lo + 2 ^ (8 * i) * hi) / 2 ^ (8 * i) % 256 = hi % 256
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hlo,
    Nat.zero_add]

theorem zbN_split_255 (v lo Q i p : Nat) (Hp : p = 2 ^ (8 * i))
    (Hv : v = lo + p * (255 + 256 * Q)) (Hlo : lo < p) : zbN v i = 255 := by
  subst Hp Hv
  rw [zbN_split lo (255 + 256 * Q) i Hlo, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by decide : 255 < 256)]

theorem zb_split (lo hi : Int) (i : Nat) (Hlo : 0 ≤ lo ∧ lo < 2 ^ (8 * i)) (Hhi : 0 ≤ hi) :
    zb (lo + 2 ^ (8 * i) * hi) i = hi % 256 := by
  have hp : 0 ≤ (2 : Int) ^ (8 * i) := by
    have := pow2_8i_pos i; omega
  have h1 : (lo + 2 ^ (8 * i) * hi).toNat = lo.toNat + 2 ^ (8 * i) * hi.toNat := by
    rw [Int.toNat_add Hlo.1 (Int.mul_nonneg hp Hhi), Int.toNat_mul hp Hhi, toNat_pow_two]
  rw [zb_eq_zbN, h1,
    zbN_split lo.toNat hi.toNat i ((ofNat_lt_two_pow _ _).mp (by
      rw [Int.toNat_of_nonneg Hlo.1]; exact Hlo.2)),
    ← Int.toNat_of_nonneg Hhi, ← emod_natCast, Int.toNat_natCast]
  rfl

theorem zb_split_255 (v lo Q : Int) (i : Nat) (p : Int) (Hp : p = 2 ^ (8 * i))
    (Hv : v = lo + p * (255 + 256 * Q)) (Hlo : 0 ≤ lo ∧ lo < p) (HQ : 0 ≤ Q) :
    zb v i = 255 := by
  have hp : 0 ≤ p := by rw [Hp]; have := pow2_8i_pos i; omega
  have hx : 0 ≤ 255 + 256 * Q := by
    have : (0:Int) ≤ 256 * Q := Int.mul_nonneg (by decide) HQ
    omega
  have hv : v.toNat = lo.toNat + p.toNat * (255 + 256 * Q).toNat := by
    rw [Hv, Int.toNat_add Hlo.1 (Int.mul_nonneg hp hx), Int.toNat_mul hp hx]
  have hq : (255 + 256 * Q).toNat = 255 + 256 * Q.toNat := by
    rw [Int.toNat_add (by decide) (Int.mul_nonneg (by decide) HQ),
      Int.toNat_mul (by decide : (0 : Int) ≤ 256) HQ, toNat_255, toNat_256]
  have hpn : p.toNat = 2 ^ (8 * i) := by rw [Hp, toNat_pow_two]
  have hlo : lo.toNat < p.toNat := by
    have h2 : ((lo.toNat : Int)) < 2 ^ (8 * i) := by
      have h0 : ((lo.toNat : Int)) = lo := Int.toNat_of_nonneg Hlo.1
      rw [h0, ← Hp]
      exact Hlo.2
    have h3 : lo.toNat < 2 ^ (8 * i) := (ofNat_lt_two_pow lo.toNat (8 * i)).mp h2
    omega
  rw [zb_eq_zbN, hv, hq]
  have hkey : zbN (lo.toNat + p.toNat * (255 + 256 * Q.toNat)) i = 255 :=
    zbN_split_255 _ lo.toNat Q.toNat i p.toNat hpn rfl hlo
  rw [hkey]
  rfl

/-- Digit `i` of a number only depends on its low `64` bits, for `i < 8`. -/
theorem zbN_mod64 (y i : Nat) (hi : i < 8) (hy : y < 2 ^ 65) :
    zbN (y % 2 ^ 64) i = zbN y i := by
  have h64 : 2 ^ (8 * i) * (256 * 2 ^ (64 - 8 * i - 8)) = 2 ^ 64 := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  by_cases h : y < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h]
  · have hyge : 2 ^ 64 ≤ y := Nat.le_of_not_lt h
    have hsub : y - 2 ^ 64 < 2 ^ 64 := by omega
    have hmod : y % 2 ^ 64 = y - 2 ^ 64 := by
      calc y % 2 ^ 64
          = ((y - 2 ^ 64) + 2 ^ 64) % 2 ^ 64 := by
              rw [show (y - 2 ^ 64) + 2 ^ 64 = y from by omega]
        _ = ((y - 2 ^ 64) + 2 ^ 64 * 1) % 2 ^ 64 := by rw [Nat.mul_one]
        _ = (y - 2 ^ 64) % 2 ^ 64 := by rw [Nat.add_mul_mod_self_left]
        _ = y - 2 ^ 64 := Nat.mod_eq_of_lt hsub
    rw [hmod]
    have e2 : y = (y - 2 ^ 64) + 2 ^ (8 * i) * (256 * 2 ^ (64 - 8 * i - 8)) := by
      rw [← h64]; omega
    have e2' : zbN y i
        = zbN ((y - 2 ^ 64) + 2 ^ (8 * i) * (256 * 2 ^ (64 - 8 * i - 8))) i :=
      congrArg (fun t => zbN t i) e2
    rw [e2', zbN_add_shift]

theorem zb_mod64 (y : Int) (i : Nat) (Hi : i < 8) (Hy : 0 ≤ y ∧ y < 2 ^ 65) :
    zb (y % 2 ^ 64) i = zb y i := by
  have hp : (0 : Int) ≤ 2 ^ 64 := by have := pow2_8i_pos 8; omega
  have hlt : y.toNat < 2 ^ 65 :=
    (ofNat_lt_two_pow _ _).mp (by rw [Int.toNat_of_nonneg Hy.1]; exact Hy.2)
  rw [zb_eq_zbN, zb_eq_zbN, Int.toNat_emod Hy.1 hp, toNat_pow_two]
  rw [zbN_mod64 y.toNat i Hi hlt]

/-- Flat `2^8` expansion of the eight-byte digit sum (the form `omega` can
    use; `zdig`'s own nested `d + 256 * zdig r` is not linear). -/
theorem zdig_flat8 (b0 b1 b2 b3 b4 b5 b6 b7 : Int) :
    zdig [b0, b1, b2, b3, b4, b5, b6, b7]
      = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4
        + 1099511627776 * b5 + 281474976710656 * b6 + 72057594037927936 * b7 := by
  simp only [zdig_cons, zdig_nil, Int.mul_add, Int.mul_comm, Int.mul_left_comm]
  omega

/-- Byte `i` of `x + ONESNEG` is `0xff` when byte `i` of `x` is the first
    zero byte: the borrow chain runs up from byte 0 and stops there. -/
theorem sum_byte_255 (x : Int) (i : Nat) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hi : i < 8)
    (Hz : zb x i = 0) (Hlow : ∀ j, j < i → zb x j ≠ 0) :
    zb (x + ONESNEG) i = 255 := by
  have hxflat : x = zb x 0 + 256 * zb x 1 + 65536 * zb x 2 + 16777216 * zb x 3
      + 4294967296 * zb x 4 + 1099511627776 * zb x 5 + 281474976710656 * zb x 6
      + 72057594037927936 * zb x 7 :=
    (zdig_recon8 x Hx).trans (zdig_flat8 _ _ _ _ _ _ _ _)
  rcases lt_eight_cases i Hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- byte 0
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    refine zb_split_255 (x + ONESNEG) (0)
      (zb x 1
        + zb x 2 * 256
        + zb x 3 * 65536
        + zb x 4 * 16777216
        + zb x 5 * 4294967296
        + zb x 6 * 1099511627776
        + zb x 7 * 281474976710656 + 71775015237779198)
      0 1 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 1
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1))
      (zb x 2
        + zb x 3 * 256
        + zb x 4 * 65536
        + zb x 5 * 16777216
        + zb x 6 * 4294967296
        + zb x 7 * 1099511627776 + 280371153272574)
      1 256 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 2
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256)
      (zb x 3
        + zb x 4 * 256
        + zb x 5 * 65536
        + zb x 6 * 16777216
        + zb x 7 * 4294967296 + 1095199817470)
      2 65536 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 3
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    have e2 : 1 ≤ zb x 2 := by
      have h := Hlow 2 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256
      + (zb x 2 - 1) * 65536)
      (zb x 4
        + zb x 5 * 256
        + zb x 6 * 65536
        + zb x 7 * 16777216 + 4278124286)
      3 16777216 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 4
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    have e2 : 1 ≤ zb x 2 := by
      have h := Hlow 2 (by omega)
      omega
    have e3 : 1 ≤ zb x 3 := by
      have h := Hlow 3 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256
      + (zb x 2 - 1) * 65536
      + (zb x 3 - 1) * 16777216)
      (zb x 5
        + zb x 6 * 256
        + zb x 7 * 65536 + 16711422)
      4 4294967296 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 5
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    have e2 : 1 ≤ zb x 2 := by
      have h := Hlow 2 (by omega)
      omega
    have e3 : 1 ≤ zb x 3 := by
      have h := Hlow 3 (by omega)
      omega
    have e4 : 1 ≤ zb x 4 := by
      have h := Hlow 4 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256
      + (zb x 2 - 1) * 65536
      + (zb x 3 - 1) * 16777216
      + (zb x 4 - 1) * 4294967296)
      (zb x 6
        + zb x 7 * 256 + 65278)
      5 1099511627776 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 6
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    have e2 : 1 ≤ zb x 2 := by
      have h := Hlow 2 (by omega)
      omega
    have e3 : 1 ≤ zb x 3 := by
      have h := Hlow 3 (by omega)
      omega
    have e4 : 1 ≤ zb x 4 := by
      have h := Hlow 4 (by omega)
      omega
    have e5 : 1 ≤ zb x 5 := by
      have h := Hlow 5 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256
      + (zb x 2 - 1) * 65536
      + (zb x 3 - 1) * 16777216
      + (zb x 4 - 1) * 4294967296
      + (zb x 5 - 1) * 1099511627776)
      (zb x 7 + 254)
      6 281474976710656 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega
  · -- byte 7
    have g0 : 0 ≤ zb x 0 := (zb_bound x 0).1
    have g1 : 0 ≤ zb x 1 := (zb_bound x 1).1
    have g2 : 0 ≤ zb x 2 := (zb_bound x 2).1
    have g3 : 0 ≤ zb x 3 := (zb_bound x 3).1
    have g4 : 0 ≤ zb x 4 := (zb_bound x 4).1
    have g5 : 0 ≤ zb x 5 := (zb_bound x 5).1
    have g6 : 0 ≤ zb x 6 := (zb_bound x 6).1
    have g7 : 0 ≤ zb x 7 := (zb_bound x 7).1
    have f0 : zb x 0 < 256 := (zb_bound x 0).2
    have f1 : zb x 1 < 256 := (zb_bound x 1).2
    have f2 : zb x 2 < 256 := (zb_bound x 2).2
    have f3 : zb x 3 < 256 := (zb_bound x 3).2
    have f4 : zb x 4 < 256 := (zb_bound x 4).2
    have f5 : zb x 5 < 256 := (zb_bound x 5).2
    have f6 : zb x 6 < 256 := (zb_bound x 6).2
    have f7 : zb x 7 < 256 := (zb_bound x 7).2
    have e0 : 1 ≤ zb x 0 := by
      have h := Hlow 0 (by omega)
      omega
    have e1 : 1 ≤ zb x 1 := by
      have h := Hlow 1 (by omega)
      omega
    have e2 : 1 ≤ zb x 2 := by
      have h := Hlow 2 (by omega)
      omega
    have e3 : 1 ≤ zb x 3 := by
      have h := Hlow 3 (by omega)
      omega
    have e4 : 1 ≤ zb x 4 := by
      have h := Hlow 4 (by omega)
      omega
    have e5 : 1 ≤ zb x 5 := by
      have h := Hlow 5 (by omega)
      omega
    have e6 : 1 ≤ zb x 6 := by
      have h := Hlow 6 (by omega)
      omega
    refine zb_split_255 (x + ONESNEG) ((zb x 0 - 1)
      + (zb x 1 - 1) * 256
      + (zb x 2 - 1) * 65536
      + (zb x 3 - 1) * 16777216
      + (zb x 4 - 1) * 4294967296
      + (zb x 5 - 1) * 1099511627776
      + (zb x 6 - 1) * 281474976710656)
      (0)
      7 72057594037927936 rfl ?_ ⟨by omega, by omega⟩ (by omega)
    simp only [ONESNEG]
    omega

/-- The 8-bit fact behind the trick, checked by reflection over all 255
    nonzero byte values. -/
theorem byte_nozero (c : Int) (Hc : 1 ≤ c ∧ c ≤ 255) :
    zland (zland (c - 1) (zlxor c 255)) 128 = 0 := by
  have hcheck : (List.range 256).all
      (fun n => decide ((n - 1) &&& (n ^^^ 255) &&& 128 = 0)) = true := by decide
  have hmem : c.toNat ∈ List.range 256 := by
    rw [List.mem_range]; omega
  have h := List.all_eq_true.mp hcheck c.toNat hmem
  have h' : ((c.toNat - 1) &&& (c.toNat ^^^ 255)) &&& 128 = 0 := of_decide_eq_true h
  have hEq : zland (zland (c - 1) (zlxor c 255)) 128
      = ((((c.toNat - 1) &&& (c.toNat ^^^ 255)) &&& 128 : Nat) : Int) := by
    simp only [zland, zlxor, Int.toNat_natCast,
      Int.toNat_sub'' (a := c) (b := 1) (by omega) (by omega), toNat_255, toNat_128]
    rfl
  rw [hEq, h']
  rfl

/- ---------- the no-borrow direction ---------- -/

/-- `0x0101010101010101`: musl's `ONES`, the subtrahend of the test. -/
def ONES : Int := 72340172838076673

/-- `ONES` at `Nat`. -/
def onesK : Nat → Nat
  | 0 => 0
  | k + 1 => 1 + 256 * onesK k

theorem onesK_eight : onesK 8 = 72340172838076673 := by decide

theorem toNat_ONESNEG : (Int.toNat ONESNEG) = 18374403900871474943 := rfl

theorem zbN_lt (x i : Nat) : zbN x i < 256 := Nat.mod_lt _ (by decide)

theorem zbN_nonneg (x i : Nat) : 0 ≤ zbN x i := Nat.zero_le _

/-- `2^64` is a multiple of digit weight `256^i` times `256`, for `i < 8`. -/
theorem two_pow64_shift (i : Nat) (hi : i < 8) :
    2 ^ 64 = 2 ^ (8 * i) * (256 * 2 ^ (64 - 8 * i - 8)) := by
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

/-- Subtracting `1` from every byte of a digit list subtracts `ONES` from
    its value (no borrows: every byte is at least `1`). -/
theorem zdigN_sub_one : ∀ (ds : List Nat), (∀ d ∈ ds, 1 ≤ d) →
    zdigN (ds.map (fun d => d - 1)) + onesK ds.length = zdigN ds
  | [], _ => rfl
  | d :: r, h => by
    have hd : 1 ≤ d := h d (List.mem_cons_self ..)
    have hr : ∀ x ∈ r, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih := zdigN_sub_one r hr
    show zdigN ((d - 1) :: r.map (fun d => d - 1)) + onesK (r.length + 1) = zdigN (d :: r)
    simp only [zdigN_cons, onesK, List.length_cons, List.map_cons]
    omega

/-- [zbN] of the sum with `ONESNEG`, when no byte is zero: byte `i` of the
    sum is byte `i` of `x` minus one (the borrow chain never starts). -/
theorem zbN_sum_sub_one (n i : Nat) (hn : n < 2 ^ 64) (hi : i < 8)
    (hnz : ∀ j, j < 8 → zbN n j ≠ 0) :
    zbN (n + 18374403900871474943) i = zbN n i - 1 := by
  have h1 : ∀ d ∈ (List.range 8).map (fun j => zbN n j), 1 ≤ d := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    have h := hnz j (List.mem_range.mp hj)
    have := zbN_nonneg n j
    omega
  have h2 : ∀ d ∈ (List.range 8).map (fun j => zbN n j), d < 256 := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact zbN_lt n j
  have hbs_zdig : zdigN ((List.range 8).map (fun j => zbN n j)) = n := by
    show zdigN ((List.range 8).map (fun j => n / 2 ^ (8 * j) % 256)) = n
    exact zdigN_digits 8 n hn
  have hzd : zdigN ((List.range 8).map (fun j => zbN n j - 1)) + 72340172838076673 = n := by
    have h := zdigN_sub_one ((List.range 8).map (fun j => zbN n j)) h1
    rw [List.length_map, List.length_range, onesK_eight, hbs_zdig] at h
    simpa [List.map_map, Function.comp_def] using h
  have hF : ∀ d ∈ (List.range 8).map (fun j => zbN n j - 1), d < 256 := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    have h1' : 1 ≤ zbN n e := h1 _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    have h2' : zbN n e < 256 := h2 _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    omega
  have hdi : ((List.range 8).map (fun j => zbN n j - 1))[i]?.getD 0 = zbN n i - 1 := by
    rcases lt_eight_cases i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hkey : n + 18374403900871474943 = zdigN ((List.range 8).map (fun j => zbN n j - 1)) + 2 ^ 64 := by
    have hONES : (2 : Nat) ^ 64 = 72340172838076673 + 18374403900871474943 := by decide
    omega
  rw [hkey, two_pow64_shift i hi, zbN_add_shift,
    zbN_zdigN ((List.range 8).map (fun j => zbN n j - 1)) i hF
      (by rw [List.length_map, List.length_range]; omega),
    hdi]

/-- [sum_byte_255]'s no-borrow twin: when NO byte of `x` is zero, byte `i`
    of `x + ONESNEG` is byte `i` of `x` minus one. -/
theorem zb_sum_sub_one (x : Int) (i : Nat) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hi : i < 8)
    (Hnz : ∀ j, j < 8 → zb x j ≠ 0) :
    zb (x + ONESNEG) i = zb x i - 1 := by
  have hONES : (0 : Int) ≤ ONESNEG := by decide
  have hn : x.toNat < 2 ^ 64 :=
    (ofNat_lt_two_pow _ _).mp (by rw [Int.toNat_of_nonneg Hx.1]; exact Hx.2)
  have hb0 : ∀ j, j < 8 → zbN x.toNat j ≠ 0 := by
    intro j hj h
    exact Hnz j hj (by rw [zb_eq_zbN, h]; rfl)
  have h := zbN_sum_sub_one x.toNat i hn Hi hb0
  have h1 : 1 ≤ zbN x.toNat i := by
    have := zbN_nonneg x.toNat i
    have : zbN x.toNat i ≠ 0 := hb0 i Hi
    omega
  rw [zb_eq_zbN, Int.toNat_add Hx.1 hONES, toNat_ONESNEG, h,
    show zb x i = (zbN x.toNat i : Int) from zb_eq_zbN x i]
  omega

/-- Range of `x + ONESNEG` for a word `x` (the `zb_mod64` side conditions). -/
theorem sum_bounds (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64) :
    0 ≤ x + ONESNEG ∧ x + ONESNEG < 2 ^ 65 := by
  have hO : (0 : Int) ≤ ONESNEG := by decide
  have hO2 : ONESNEG < 2 ^ 64 := by decide
  have hp : (2 : Int) ^ 65 = 2 ^ 64 * 2 := by decide
  omega

/-- No zero byte: the test word is 0, so the loop keeps going. -/
theorem Tz_nozero (x : Int) (Hx : 0 ≤ x ∧ x < 2 ^ 64)
    (Hnz : ∀ i, i < 8 → zb x i ≠ 0) : Tz x = 0 := by
  apply zb_eq0 (Tz x) (Tz_range x)
  intro i hi
  rw [Tz_byte x i hi]
  have hbnd := sum_bounds x Hx
  rw [show zb ((x + ONESNEG) % 2 ^ 64) i = zb (x + ONESNEG) i from
    zb_mod64 (x + ONESNEG) i hi hbnd]
  rw [zb_sum_sub_one x i Hx hi Hnz]
  refine byte_nozero (zb x i) ⟨?_, ?_⟩
  · have h := (zb_bound x i).1
    have := Hnz i hi
    omega
  · have h := (zb_bound x i).2
    omega

/-- A zero byte: the test word is nonzero, so the loop stops. -/
theorem Tz_haszero (x : Int) (i : Nat) (Hx : 0 ≤ x ∧ x < 2 ^ 64) (Hi : i < 8)
    (Hz : zb x i = 0) (Hlow : ∀ j, j < i → zb x j ≠ 0) : Tz x ≠ 0 := by
  apply zb_neq0 (i := i)
  rw [Tz_byte x i Hi]
  have hbnd := sum_bounds x Hx
  rw [show zb ((x + ONESNEG) % 2 ^ 64) i = zb (x + ONESNEG) i from
    zb_mod64 (x + ONESNEG) i Hi hbnd]
  rw [sum_byte_255 x i Hx Hi Hz Hlow, Hz]
  decide

/- ------------------------------------------------------------------ -/
/- Bridge: the bytes an 8-byte load returns are the bytes of the value -/
/- ------------------------------------------------------------------ -/

theorem u8_zero : ((BitVec.ofInt 8 0).toNat : Int) = 0 := by decide

/-- `0 <= b < 256` for a byte (a local copy: `PropExec.u8_range` carries the
    `WithFP` section's `FPState` instance). -/
theorem u8_range' (b : byte) : 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) < 256 := by
  have h := b.isLt
  have h2 : (2 : Nat) ^ 8 = 256 := by decide
  omega

/-- The bytes of a little-endian word are `0 <= b < 256`. -/
theorem forall_map_unsigned (bs : List byte) :
    ∀ d ∈ bs.map (fun b => (b.toNat : Int)), 0 ≤ d ∧ d < 256 := by
  intro d hd
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
  exact u8_range' b

/-- `Z.lor a (Z.shiftl y 8) = a + 256 * y` for a byte `a`: the little-endian
    byte algebra of the digit sum. -/
theorem lor_shiftl8 (a y : Int) (Ha : 0 ≤ a ∧ a < 256) (Hy : 0 ≤ y) :
    zlor a (zshiftl y 8) = a + 256 * y := by
  have ha : a.toNat < 2 ^ 8 :=
    (ofNat_lt_two_pow a.toNat 8).mp (by rw [Int.toNat_of_nonneg Ha.1]; exact Ha.2)
  have hbl : (zshiftl y 8).toNat = y.toNat * 256 := by
    unfold zshiftl
    rw [show ((2 ^ 8 : Nat) : Int) = 256 by decide]
    exact Int.toNat_mul Hy (by decide)
  have hkey : (a.toNat ||| (y.toNat * 256)) = a.toNat + 256 * y.toNat := by
    have hs : y.toNat * 256 = y.toNat <<< 8 := by
      rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by decide]
    rw [hs, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) ha, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 8 = 256 by decide]
    omega
  rw [zlor, hbl, hkey, ← Int.toNat_of_nonneg Ha.1, ← Int.toNat_of_nonneg Hy,
    show ((256 : Int)) = ((256 : Nat) : Int) from rfl, ← Int.natCast_mul, ← Int.natCast_add]
  rfl

/-- The `Nat` disjunct of [lor_shiftl8], as the `Int` cast the digit-sum
    induction needs. -/
theorem natCast_or_shift (a bl : Nat) :
    ((a ||| (bl <<< 8) : Nat) : Int)
      = zlor ((a : Nat) : Int) (zshiftl ((bl : Nat) : Int) 8) := by
  have hb : (zshiftl ((bl : Nat) : Int) 8).toNat = bl * 256 := by
    unfold zshiftl
    rw [show ((2 ^ 8 : Nat) : Int) = 256 by decide,
      Int.toNat_mul (Int.natCast_nonneg bl) (by decide : (0 : Int) ≤ 256),
      Int.toNat_natCast, toNat_256]
  have hb' : bl * 256 = bl <<< 8 := by
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by decide]
  rw [zlor, hb, Int.toNat_natCast, hb']

/-- Every byte list's value is the digit sum of its bytes. -/
theorem bytes_le_to_Z_zdig (bs : List byte) :
    bytes_le_to_Z bs = HZ.zdig (bs.map (fun b => (b.toNat : Int))) := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb := u8_range' b
    have hz : 0 ≤ HZ.zdig (rest.map (fun b => (b.toNat : Int))) :=
      HZ.zdig_nonneg _ (forall_map_unsigned rest)
    show bytes_le_to_Z (b :: rest) = HZ.zdig ((b :: rest).map (fun b => (b.toNat : Int)))
    rw [show bytes_le_to_Z (b :: rest)
        = (((b.toNat : Int)) + 256 * ((bytes_le_to_Nat rest : Nat) : Int)) from by
      rw [bytes_le_to_Z, bytes_le_to_Nat, natCast_or_shift]
      exact lor_shiftl8 _ _ hb (Int.natCast_nonneg _),
      List.map_cons, HZ.zdig_cons, ← ih]
    rfl

/-- Byte `i` of a little-endian byte list is byte `i` of its value. -/
theorem zb_of_bytes (bs : List byte) (i : Nat) (Hi : i < bs.length) :
    HZ.zb (bytes_le_to_Z bs) i = ((bs[i]?.getD (BitVec.ofInt 8 0)).toNat : Int) := by
  rw [bytes_le_to_Z_zdig,
    HZ.zb_zdig (bs.map (fun b => (b.toNat : Int))) (forall_map_unsigned bs) i
      (by simpa using Hi),
    List.getElem?_map]
  cases h : bs[i]? with
  | none => simp [h]
  | some b =>
    have := u8_range' b
    simp only [Option.map_some, Option.getD_some]

/-- An eight-byte value is a `64`-bit number. -/
theorem bytes_le_to_Z_range (bs : List byte) (Hl : bs.length = 8) :
    0 ≤ bytes_le_to_Z bs ∧ bytes_le_to_Z bs < 2 ^ 64 := by
  have hF : ∀ d ∈ bs.map (fun b => (b.toNat : Int)), 0 ≤ d ∧ d < 256 :=
    forall_map_unsigned bs
  rw [bytes_le_to_Z_zdig]
  refine ⟨HZ.zdig_nonneg _ hF, ?_⟩
  have h := HZ.zdig_lt _ hF
  rwa [List.length_map, Hl] at h

/-- `BitVec.ofInt` at a value already in range: the `Int` `toNat` is the
    value itself. -/
theorem toNat_ofInt_of_range (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by rw [Int.natCast_pow]; exact h1)]

/-- `z < 2^64` from its `Nat` representative (for `0 <= z`). -/
theorem lt_two_pow_of_toNat_lt {z : Int} (h0 : 0 ≤ z) (h : z.toNat < 2 ^ 64) :
    z < 2 ^ 64 := by
  have h1 : ((z.toNat : Int)) < 2 ^ 64 := (ofNat_lt_two_pow z.toNat 64).mpr h
  rwa [Int.toNat_of_nonneg h0] at h1

theorem toNat_18446744073709551615 : (Int.toNat 18446744073709551615) = 18446744073709551615 := rfl
theorem toNat_9259542123273814144 : (Int.toNat 9259542123273814144) = 9259542123273814144 := rfl

theorem toNat_v_add (x y : word) : (v_add x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  have hpow : (((2 : Nat) ^ 64 : Nat) : Int) = (2 : Int) ^ 64 := (Int.natCast_pow 2 64).symm
  unfold v_add
  rw [BitVec.toNat_ofInt, hpow,
    Int.toNat_emod (x := (x.toNat : Int) + (y.toNat : Int)) (y := (2 : Int) ^ 64)
      (by omega) (by decide : (0 : Int) ≤ 2 ^ 64),
    toNat_pow_two, Int.toNat_add (Int.natCast_nonneg x.toNat) (Int.natCast_nonneg y.toNat),
    Int.toNat_natCast, Int.toNat_natCast]

theorem toNat_v_and (x y : word) : (v_and x y).toNat = x.toNat &&& y.toNat := by
  have hz : 0 ≤ zland (x.toNat : Int) (y.toNat : Int) := Int.natCast_nonneg _
  have hval : (zland (x.toNat : Int) (y.toNat : Int)).toNat = x.toNat &&& y.toNat := by
    simp only [zland, Int.toNat_natCast]
  have hlt : zland (x.toNat : Int) (y.toNat : Int) < 2 ^ 64 := by
    apply lt_two_pow_of_toNat_lt hz
    rw [hval]
    exact Nat.and_lt_two_pow _ (by have := y.isLt; simpa using this)
  unfold v_and
  rw [toNat_ofInt_of_range _ hz hlt, hval]

theorem toNat_v_xori_m1 (x : word) :
    (v_xori x (-1)).toNat = x.toNat ^^^ 18446744073709551615 := by
  have hw : bv_wrap 64 (-1) = 18446744073709551615 := by decide
  have hz : 0 ≤ zlxor (x.toNat : Int) (bv_wrap 64 (-1)) := Int.natCast_nonneg _
  have hval : (zlxor (x.toNat : Int) (bv_wrap 64 (-1))).toNat
      = x.toNat ^^^ 18446744073709551615 := by
    simp only [zlxor, hw, Int.toNat_natCast, toNat_18446744073709551615]
  have hlt : zlxor (x.toNat : Int) (bv_wrap 64 (-1)) < 2 ^ 64 := by
    apply lt_two_pow_of_toNat_lt hz
    rw [hval]
    exact Nat.xor_lt_two_pow (by have := x.isLt; simpa using this)
      (by decide : 18446744073709551615 < 2 ^ 64)
  unfold v_xori
  rw [toNat_ofInt_of_range _ hz hlt, hval]

/-- `Tz` at `Nat`: the machine's test word with no `Int` in the way. -/
def TzN (n : Nat) : Nat :=
  ((n + 18374403900871474943) % 2 ^ 64) &&& (n ^^^ 18446744073709551615)
    &&& 9259542123273814144

/-- [Tz] only sees the `Nat` value of its argument. -/
theorem Tz_natCast (n : Nat) : HZ.Tz ((n : Nat) : Int) = (TzN n : Int) := by
  have hO : (0 : Int) ≤ ONESNEG := by decide
  have hA : ((((n : Int) + ONESNEG) % 2 ^ 64)).toNat = (n + 18374403900871474943) % 2 ^ 64 := by
    rw [Int.toNat_emod (x := (n : Int) + ONESNEG) (y := (2 : Int) ^ 64)
        (by omega) (by decide : (0 : Int) ≤ 2 ^ 64),
      Int.toNat_add (a := (n : Int)) (b := ONESNEG) (Int.natCast_nonneg n) hO,
      Int.toNat_natCast, toNat_pow_two, toNat_ONESNEG]
  have hB : (zlxor ((n : Nat) : Int) ALLONES).toNat = n ^^^ 18446744073709551615 := by
    simp only [zlxor, ALLONES, Int.toNat_natCast, toNat_18446744073709551615]
  unfold HZ.Tz
  rw [zland, zland, Int.toNat_natCast]
  rw [hA, hB]
  rfl

/-- The machine's test word, as the `Int` predicate `HZ.Tz`. -/
theorem v_haszero (v : word) :
    ((v_and (v_and (v_add v (BitVec.ofInt 64 ONESNEG)) (v_xori v (-1)))
      (BitVec.ofInt 64 HIGHS)).toNat : Int) = HZ.Tz ((v.toNat : Int)) := by
  rw [Tz_natCast]
  congr 1
  rw [toNat_v_and, toNat_v_and, toNat_v_add, toNat_v_xori_m1]
  rfl

/- ------------------------------------------------------------------ -/
/- An 8-byte load anywhere inside an argv string                       -/
/-                                                                     -/
/- musl's strlen reads a whole aligned word, so the load can straddle   -/
/- the NUL terminator.  The stack image always ends with the 16         -/
/- AT_RANDOM bytes (after the pad), so there are at least 16 readable   -/
/- bytes past the last argv string's NUL and such a read never faults.  -/
/- See the over-read warning in this file's header.                     -/
/- ------------------------------------------------------------------ -/

section ArgvStack

variable [fx : FPState]

theorem total_arg_bytes_firstn_S (l : List (List byte)) (k : Nat) (Hk : k < l.length) :
    total_arg_bytes_nat (l.take (k + 1))
      = total_arg_bytes_nat (l.take k) + (l[k]?.getD []).length + 1 := by
  induction l generalizing k with
  | nil => simp at Hk
  | cons s rest ih =>
    cases k with
    | zero => simp [total_arg_bytes_nat]
    | succ k =>
      have hk : k < rest.length := by simpa using Hk
      rw [List.take_succ_cons, List.take_succ_cons, total_arg_bytes_cons, total_arg_bytes_cons,
        List.getElem?_cons_succ, ih k hk]
      omega

/-- The image always keeps at least `cat_struct_size + total_arg_bytes + 16`
    bytes: the 16 are the alignment pad plus the AT_RANDOM tail. -/
theorem bsb_len_lower (ph : PhdrInfo) (sp : word) (a e : List (List byte))
    (uid hw : word) (rnd : EntryDraw) :
    cat_struct_size a e + total_arg_bytes_nat a + 16
      ≤ (build_stack_bytes ph sp a e uid hw rnd).length := by
  simp only [build_stack_bytes, cat_struct_size, length_string_addrs_fst,
    length_flat_map_le8, length_n_to_le_8, length_auxv_bytes, length_flatten_strings,
    auxv_size, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    length_at_random_bytes]
  omega

/-- Re-associate a `take`/`drop` split of the tail. -/
theorem take_drop_append (s1 post : List byte) (m : Nat) :
    s1.take m ++ (s1.drop m ++ post) = s1 ++ post := by
  rw [← List.append_assoc, List.take_append_drop]

/-- [build_stack_bytes] split just before byte [m] of argv string [k],
    with at least 8 readable bytes left. -/
theorem bsb_word_k (ph : PhdrInfo) (sp : word) (a e : List (List byte)) (k m : Nat)
    (uid hw : word) (rnd : EntryDraw) (Hk : k < a.length)
    (Hm : m ≤ (a[k]?.getD []).length) :
    ∃ pre post,
      build_stack_bytes ph sp a e uid hw rnd = pre ++ post
      ∧ pre.length = cat_struct_size a e + total_arg_bytes_nat (a.take k) + m
      ∧ 8 ≤ post.length := by
  obtain ⟨pre0, post0, E, Hlen0⟩ := bsb_byte_k ph sp a e k uid hw rnd Hk
  have Hlow := bsb_len_lower ph sp a e uid hw rnd
  have Hmono := total_arg_bytes_firstn_le (k + 1) a
  have Hstep := total_arg_bytes_firstn_S a k Hk
  have Hs1 : (a[k]?.getD [] ++ [BitVec.ofInt 8 0]).length
      = (a[k]?.getD []).length + 1 := by simp
  have Hpost0 : 16 ≤ post0.length := by
    have Hl : (build_stack_bytes ph sp a e uid hw rnd).length
        = pre0.length + (a[k]?.getD [] ++ [BitVec.ofInt 8 0]).length + post0.length := by
      rw [E]
      simp only [List.length_append]
    omega
  refine ⟨pre0 ++ (a[k]?.getD [] ++ [BitVec.ofInt 8 0]).take m,
    (a[k]?.getD [] ++ [BitVec.ofInt 8 0]).drop m ++ post0, ?_, ?_, ?_⟩
  · rw [E]
    simp only [List.append_assoc]
    congr 1
    rw [take_drop_append, ← List.append_assoc]
  · rw [List.length_append, Hlen0, List.length_take]
    omega
  · rw [List.length_append, List.length_drop]
    omega

/-- A total 8-byte load at byte [m] of argv string [k], inside the initial
    stack image. -/
theorem read_word_stack (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (a e : List (List byte)) (k m : Nat) (uid hw : word) (rnd : EntryDraw)
    (Hk : k < a.length) (Hm : m ≤ (a[k]?.getD []).length)
    (Hnw : (sp.toNat : Int)
      + ((build_stack_bytes ph sp a e uid hw rnd).length : Int) < 2 ^ 64) :
    ∃ bs, bs.length = 8 ∧
      rdn segs (stack_to_mem sp (entry_stack_image ph sp a e uid hw rnd))
          (cat_argv_ptr sp a e k + nat_to_word m) 8 = some bs := by
  obtain ⟨pre, post, E, Hlen, Hpost⟩ := bsb_word_k ph sp a e k m uid hw rnd Hk Hm
  refine ⟨post.take 8, by rw [List.length_take]; omega, ?_⟩
  have hptr : cat_argv_ptr sp a e k + nat_to_word m = sp + nat_to_word pre.length := by
    rw [Hlen, cat_argv_ptr_offset sp a e k Hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge, nat_to_word_add_merge]
    congr 2
    omega
  rw [hptr]
  exact read_at_offset_image segs ph sp a e uid hw rnd pre (post.take 8) (post.drop 8) 8
    (by rw [E]; simp only [List.append_assoc]; congr 1; rw [List.take_append_drop])
    (by rw [List.length_take]; omega) Hnw

/-- The bytes an 8-byte load returned, as far as the NUL: given ANY memory
    whose single-byte reads along the string agree with [byte_at s], byte
    [j] of the loaded word is [byte_at s (m + j)]. -/
theorem word_bytes_nth (segs : List Segment) (mem : word → Option byte) (ptr : word)
    (s : List byte) (m : Nat) (bs : List byte) (j : Nat)
    (Hr : rdn segs mem (ptr + nat_to_word m) 8 = some bs)
    (Hb : ∀ i, i ≤ s.length →
      rdn segs mem (ptr + nat_to_word i) 1 = some [byte_at s i])
    (Hj : j < 8) (Hmj : m + j ≤ s.length) :
    bs[j]?.getD (BitVec.ofInt 8 0) = byte_at s (m + j) := by
  have H1 := rdn_nth segs mem 8 (ptr + nat_to_word m) bs j Hr Hj
  rw [nat_to_word_add_merge] at H1
  rw [Hb (m + j) Hmj] at H1
  simp only [Option.some.injEq, List.singleton_inj] at H1
  exact H1.symm

/- ------------------------------------------------------------------ -/
/- Section form: readability of the strlen word load over [wrap_mem]    -/
/-                                                                     -/
/- Same shape as [Common/ArgvEnv]: the ambient startup hypotheses     -/
/- [(segs, ph, sp, av, ev)] are explicit parameters here, so a          -/
/- per-binary file instantiates each lemma with one [apply ...;         -/
/- assumption].                                                         -/
/- ------------------------------------------------------------------ -/

/-- sp-window lower bound as raw hex (the [rsp_lo_num] twin; kept under an
    [mstr_] name so importing this file and [ArgvEnv] never clashes). -/
theorem mstr_sp_lo (sp : word) (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int)) :
    (0x7fff80000000 : Int) ≤ (sp.toNat : Int) := Hsp_lo

/-- sp-window upper bound as raw hex. -/
theorem mstr_sp_hi (sp : word) (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi) :
    (sp.toNat : Int) ≤ 0x800000000000 := Hsp_hi

/-- The image never reaches the top of the address space. -/
theorem mstr_bsb_nw (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ 0x800000000000) :
    (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) < 2 ^ 64 := by
  have h1 := bsb_bound ph sp av ev uid hw rnd Hva Hve
  omega

/-- Room for a whole word past ANY offset inside argv string [k]: the
    stack image always keeps 16 more bytes (pad + AT_RANDOM) after the
    last argv string's NUL.  This is the quantitative form of the
    over-read soundness argument. -/
theorem argv_ptr_room (ph : PhdrInfo) (sp : word) (av ev : List (List byte))
    (uid hw : word) (rnd : EntryDraw) (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int))
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k : Nat) (Hk : k < av.length) :
    ((cat_argv_ptr sp av ev k).toNat : Int) + ((av[k]?.getD []).length : Int) + 17
      ≤ (sp.toNat : Int) + ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) := by
  have Hlow := bsb_len_lower ph sp av ev uid hw rnd
  have Hmono := total_arg_bytes_firstn_le (k + 1) av
  have Hstep := total_arg_bytes_firstn_S av k Hk
  have Hnw := mstr_bsb_nw ph sp av ev uid hw rnd Hva Hve (mstr_sp_hi sp Hsp_hi)
  have Hptr : cat_argv_ptr sp av ev k
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k Hk]
    unfold cat_string_base
    rw [nat_to_word_add_merge]
  have hn_le : ((cat_struct_size av ev + total_arg_bytes_nat (av.take k) : Nat) : Int)
      ≤ ((build_stack_bytes ph sp av ev uid hw rnd).length : Int) := by
    have h2 : (total_arg_bytes_nat (av.take k) : Int) ≤ (total_arg_bytes_nat av : Int) := by
      have h3 := Int.ofNat_le.mpr Hmono
      omega
    omega
  rw [Hptr, word_add_nat,
    u_Z2bv _ (by omega) (by omega)]
  omega

/-- Address bounds for the [k]-th argv pointer (the [source_ptr_bounds]
    twin; restated here so this file is self-contained). -/
theorem mstr_argv_ptr_bounds (sp : word) (av ev : List (List byte))
    (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_hi : (sp.toNat : Int) ≤ 0x800000000000)
    (k : Nat) (Hk : k < av.length) :
    ((sp.toNat : Int) ≤ ((cat_argv_ptr sp av ev k).toNat : Int))
    ∧ (((cat_argv_ptr sp av ev k).toNat : Int)
        + ((av[k]?.getD []).length : Int) + 1 < 2 ^ 64) := by
  have h := argv_ptr_bounds sp av ev k Hva Hve Hk (by
    unfold argv_layout_slack
    omega)
  exact h

/-- THE load-bearing readability fact: an 8-byte load at ANY offset [m]
    within argv string [k] (including [m = length s], i.e. starting at
    the NUL) is total over the initial wrapped memory. -/
theorem argv_word_readable (ph : PhdrInfo) (segs : List Segment) (sp : word)
    (av ev : List (List byte)) (uid hw : word) (rnd : EntryDraw)
    (Hva : valid_argv av) (Hve : valid_envp ev)
    (Hsp_lo : sp_window_lo ≤ (sp.toNat : Int))
    (Hsp_hi : (sp.toNat : Int) ≤ sp_window_hi)
    (k m : Nat) (Hk : k < av.length) (Hm : m ≤ (av[k]?.getD []).length) :
    ∃ bs, bs.length = 8 ∧
      rdn segs (wrap_mem ph sp av ev uid hw rnd)
          (cat_argv_ptr sp av ev k + nat_to_word m) 8 = some bs := by
  have Hlo := mstr_sp_lo sp Hsp_lo
  have Hhi := mstr_sp_hi sp Hsp_hi
  obtain ⟨Hge, Hup⟩ := mstr_argv_ptr_bounds sp av ev Hva Hve Hhi k Hk
  have Hroom := argv_ptr_room ph sp av ev uid hw rnd Hva Hve Hsp_lo Hsp_hi k Hk
  have Hnw := mstr_bsb_nw ph sp av ev uid hw rnd Hva Hve Hhi
  have Hu : ((cat_argv_ptr sp av ev k + nat_to_word m).toNat : Int)
      = ((cat_argv_ptr sp av ev k).toNat : Int) + (m : Int) := by
    rw [word_add_nat]
    rw [u_Z2bv _ (by omega) (by omega)]
  obtain ⟨bs, Hl, Hr⟩ := read_word_stack ph segs sp av ev k m uid hw rnd Hk Hm Hnw
  refine ⟨bs, Hl, ?_⟩
  rw [rdn_wrap_stack_above segs ph sp av ev _ 8 uid hw rnd]
  · exact Hr
  · rw [Hu]; omega
  · rw [Hu]; omega

end ArgvStack
