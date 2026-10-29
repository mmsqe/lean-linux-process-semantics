/-
  * Common.RefMemcpyLib — binary-agnostic lemmas for byte-copy loop proofs

  Vocabulary for proving a forward byte/word copy routine (musl's C `memcpy`)
  correct at the byte level:

  - `sub bs j k`     = the `k` bytes of `bs` starting at offset `j`
  - `wbytes_app`     : two consecutive forward writes are ONE write of the
                       appended byte lists (Leibniz equality, no funext)
  - `rdn_sub`        : reading a sub-range of a readable range
  - `lez`/byte lemmas: `bytes_le_to_Z` of sublists, shifts, truncations,
                       and the `lw`/`sw`/`lbu`/`sb` value round trips
  - `store_ok` range helpers.

  Everything is stated over an arbitrary segment list `segs`.

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  * Conventions: `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` →
    `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)`,
    `firstn`→`List.take`, `skipn`→`List.drop`, `nth k l d` →
    `l.getD k d`, `In` → `∈`, `repeat a n` → `List.replicate n a`,
    `lia` → `omega`, `vm_compute; reflexivity` → `by decide`.

  * `callee_kept`/`keeps`/`keeps_refl`/`keeps_trans` also live, as a
    stand-in, in `Common/MemsetLib.lean`'s namespace (that file was written up
    first and needed them); this file is their home and their
    statements here are the same.  The two copies do not interact.

  * `wbytes_app`: offsets the second write by
    `at_ a (Z.of_nat (length bs1))`; this tree proves that form (the
    `nat_to_word` form lives in `Common/AllocSim.lean`, and `at_nat` below is
    the bridge between the two).

  * `rdn_skipn`/`rdn_sub`: `Common/SeqExec.lean` already carries both
    statements in the `a + nat_to_word k` address form; this tree restates
    them at the `at_` addresses this file works with and derives each in one
    step through `at_nat` and `SeqExec.rdn_skipn`/`SeqExec.rdn_firstn`.

  * `Int.testBit` does not exist at Lean v4.31.0 (`Nat.testBit` does, but
    only on `Nat`, so it cannot see the sign-extended `LWv` the merge
    shifts).  Byte by byte, how each lemma is proved here:

                                 here
      -------------------------------    -----------------------------------
      `testbit_u_vor`                    `testbit_u_vor` (`toNat` of `v_or`
                                         is `|||` of the two `toNat`s)
      `testbit_u_LWv`                    `testbit_u_LWv` / `zbN_bytes`
      `testbit_lez_app`                  `testbit_lez_app` +
                                         `zbN_app_{left,right}`
      `testbit_lez_skipn`                `testbit_lez_skipn`
      `testbit_lez_firstn`               `testbit_lez_firstn` +
                                         `zbN_take_{lt,ge}`
      `testbit_u_srliw_LWv`              `sb_byte_srli_LWv` (byte `q` of the
                                         `v_srli (LWv l) (8q)` form) and
                                         `v_srliw_toNat_mod32` (the low 32
                                         bits of the `v_srliw` form the
                                         merge actually shifts)
      `testbit_u_slli_LWv`               `v_slli_toNat_mod32` (the low 32
                                         bits of `v_slli x t`, at the byte
                                         boundary `t = 32 - 8q`)
      `sw_bytes_merge`, `_merge'`        `sw_bytes_merge`, `sw_bytes_merge'`
                                         — value-level rather than per-bit;
                                         see the section after
                                         `testbit_u_vor`
    An earlier version of this paragraph claimed that `srliw_LWv`,
    `slli_LWv` and `vor_toNat` carried those facts (none of the three
    names existed) and that `sw_bytes_merge` "keeps its  statement
    verbatim" (no such declaration existed).  Both claims are corrected
    above —is the reason the correction lives here.
    The value-level lemmas that DO exist — `u_vlw_mod32`, `sw_bytes_LWv`
    (the `q = 0` / `q = 4` case of the merge), `sb_byte_srli_LWv`,
    `testbit_u_vor` — are the same facts about the same words; nothing
    that is present is weakened.
    A LATER version still said the two merge theorems were DEFERRED,
    because `(x ||| y) % 2^k` and `(a ||| b) <<< k` were "absent here and
    in core".  That was measured wrong: the FACTS are core
    (`Nat.or_mod_two_pow`, `Nat.shiftLeft_or_distrib`,
    `Nat.shiftLeft_add_eq_or_of_lt` — `PropExec.bytes_le_to_Nat_app` and
    `AxSymExec3Sound.two_mul_or` in this very tree already use them); what
    is absent is the older spelling of those names.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.Hoare
import LinuxSem.Common.StoreOk
import LinuxSem.Common.MuslStrlen

namespace LinuxSem.Common.RefMemcpyLib

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.StepTac
open LinuxSem.Common.Hoare
open LinuxSem.Common.StoreOk
open LinuxSem.Common.MuslStrlen.HZ

/-- The address-arithmetic vocabulary (`at_` of `Hoare`, `u_Z2bv` of
    `StepTac`, the value shapes of `PropExec`) is declared in sections over an
    ambient `FPState` instance even where it does not mention it; supplying
    `fx0` locally (the device `Common/MemsetLib.lean` and
    `Common/StoreOk.lean` use) keeps this file's own statements FP-free, as
    the ones are. -/
local instance refmemcpy_fx : FPState := fx0

/-! =====================================================================
    Lists: `sub`, `take`/`drop` arithmetic
    ===================================================================== -/

/-- The `k` bytes of `bs` starting at offset `j`. -/
def sub {A : Type} (bs : List A) (j k : Nat) : List A := (bs.drop j).take k

/-- `firstn (a + b) l = firstn a l ++ firstn b (skipn a l)`.
-/
theorem firstn_add {A : Type} (l : List A) (a b : Nat) :
    l.take (a + b) = l.take a ++ (l.drop a).take b :=
  List.take_add

/-- A taken prefix followed by a sub-range is the longer prefix. -/
theorem firstn_sub_app {A : Type} (bs : List A) (j k : Nat) :
    bs.take j ++ sub bs j k = bs.take (j + k) :=
  (List.take_add (l := bs) (i := j) (j := k)).symm

/-- `skipn (a + b) l = skipn b (skipn a l)` (`List.drop_drop`, reversed). -/
theorem skipn_add {A : Type} (l : List A) (a b : Nat) :
    l.drop (a + b) = (l.drop a).drop b :=
  (List.drop_drop (l := l) (i := b) (j := a)).symm

/-- A sub-range inside the list has exactly the requested length. -/
theorem sub_length {A : Type} (bs : List A) (j k : Nat) (H : j + k ≤ bs.length) :
    (sub bs j k).length = k := by
  unfold sub
  rw [List.length_take, List.length_drop]
  omega

/-- A sub-range splits at an inner offset. -/
theorem sub_split {A : Type} (bs : List A) (j a b : Nat) :
    sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b := by
  unfold sub
  rw [List.take_add, List.drop_drop]

/-- The whole list is the sub-range at offset `0`. -/
theorem sub_0_all {A : Type} (bs : List A) : sub bs 0 bs.length = bs := by
  unfold sub
  simp

/-- A prefix of the full length is the list itself. -/
theorem length_firstn_id {A : Type} (bs : List A) (k : Nat) (H : k = bs.length) :
    bs.take k = bs := by
  subst H
  exact List.take_of_length_le (by omega)

/-- A one-byte sub-range is the `j`-th byte (default `0` off the end). -/
theorem sub_nth (bs : List byte) (j : Nat) (H : j < bs.length) :
    sub bs j 1 = [bs.getD j (BitVec.ofInt 8 0)] := by
  unfold sub
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem H]
  have hpos : 0 < (bs.drop j).length := by
    rw [List.length_drop]; omega
  cases hd : bs.drop j with
  | nil => rw [hd] at hpos; simp at hpos
  | cons x t =>
    have hx : x = bs[j] := by
      have h := List.getElem?_drop (xs := bs) (i := j) (j := 0)
      rw [hd, Nat.add_zero, List.getElem?_eq_getElem H] at h
      exact Option.some.inj h
    rw [hx]
    simp

/-! =====================================================================
    `at_` addressing helpers
    ===================================================================== -/

/-- Stepping an `at_` address by one stays inside the `at_` normal form. -/
theorem at_succ (a : word) (d : Int) : at_ a d + 1 = at_ a (d + 1) := by
  unfold at_
  bv_omega

/-- `a + 1` is `at_ a 1` (the address step of every `wbytes`/`rdn` walk). -/
theorem word_succ_at (a : word) : a + 1 = at_ a 1 := by
  unfold at_
  bv_omega

/-- `at_` of an in-range offset: the unsigned value is the offset sum. -/
theorem at_u (a : word) (d : Int) (H1 : 0 ≤ (a.toNat : Int) + d)
    (H2 : (a.toNat : Int) + d < ((2 ^ 64 : Nat) : Int)) :
    ((at_ a d).toNat : Int) = (a.toNat : Int) + d :=
  u_Z2bv _ H1 H2

/-- `a + nat_to_word j = at_ a j`: the bridge between the `nat_to_word`
    offset form (used by `CatExec`/`SeqExec`) and the `at_` form used here. -/
theorem at_nat (a : word) (j : Nat) : a + nat_to_word j = at_ a (j : Int) := by
  unfold at_ nat_to_word
  bv_omega

/-! =====================================================================
    `wbytes`: consecutive forward writes compose
    ===================================================================== -/

/-- Two consecutive forward writes are ONE write of the appended byte
    lists. -/
theorem wbytes_app (bs1 bs2 : List byte) (m : word → Option byte) (a : word) :
    wbytes m a (bs1 ++ bs2)
      = wbytes (wbytes m a bs1) (at_ a (bs1.length : Int)) bs2 := by
  induction bs1 generalizing m a with
  | nil =>
    simp only [List.nil_append, wbytes, List.length_nil]
    rw [← at_nat, word_add_0]
  | cons b bs ih =>
    simp only [List.cons_append, wbytes, List.length_cons]
    rw [ih, word_succ_at, at_at]
    congr 2
    omega

/-- The form used by the copy invariant: memory after copying `j` then `k`
    more bytes of `bs` to `dst`. -/
theorem wbytes_extend (m : word → Option byte) (dst : word) (bs : List byte)
    (j k : Nat) :
    wbytes (wbytes m dst (bs.take j)) (at_ dst (j : Int)) (sub bs j k)
        = wbytes m dst (bs.take (j + k)) ∨ bs.length < j := by
  by_cases H : j ≤ bs.length
  · left
    conv => rhs; rw [← firstn_sub_app bs j k]
    rw [wbytes_app]
    congr 2
    rw [List.length_take, Nat.min_eq_left H]
  · right; omega

/-- [wbytes_extend] with the side condition as a hypothesis. -/
theorem wbytes_extend' (m : word → Option byte) (dst : word) (bs : List byte)
    (j k : Nat) (H : j ≤ bs.length) :
    wbytes (wbytes m dst (bs.take j)) (at_ dst (j : Int)) (sub bs j k)
      = wbytes m dst (bs.take (j + k)) := by
  rcases wbytes_extend m dst bs j k with E | E
  · exact E
  · omega

/-! =====================================================================
    `rdn` of sub-ranges and through disjoint writes
    ===================================================================== -/

/-- Reading `n - j` bytes at `at_ a j` after reading `n` bytes at `a`
    yields the dropped suffix. -/
theorem rdn_skipn (segs : List Segment) (mem : word → Option byte) (n : Nat)
    (a : word) (bs : List byte) (j : Nat)
    (H : rdn segs mem a n = some bs) (Hj : j ≤ n) :
    rdn segs mem (at_ a (j : Int)) (n - j) = some (bs.drop j) := by
  rw [← at_nat]
  exact SeqExec.rdn_skipn segs mem n a bs j H Hj

/-- Reading a sub-range of an `n`-byte readable range. -/
theorem rdn_sub (segs : List Segment) (mem : word → Option byte) (n : Nat)
    (a : word) (bs : List byte) (j k : Nat)
    (H : rdn segs mem a n = some bs) (Hjk : j + k ≤ n) :
    rdn segs mem (at_ a (j : Int)) k = some (sub bs j k) := by
  unfold sub
  refine SeqExec.rdn_firstn segs mem (n - j) (at_ a (j : Int)) _ k ?_ (by omega)
  exact rdn_skipn segs mem n a bs j H (by omega)



/-! =====================================================================
    `bytes_le_to_Z` ("lez") bit-level facts and load/store value lemmas
    ===================================================================== -/

/-- `lez` abbreviation. -/
abbrev lez := bytes_le_to_Z

def LWv (l : List byte) : word := BitVec.ofInt 64 (bv_swrap 32 (lez l))

theorem bytes_le_to_Nat_app_add (xs ys : List byte) :
    bytes_le_to_Nat (xs ++ ys)
      = bytes_le_to_Nat xs + bytes_le_to_Nat ys * 2 ^ (8 * xs.length) := by
  rw [bytes_le_to_Nat_app, Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_eq,
    Nat.add_comm]
  exact (Nat.shiftLeft_add_eq_or_of_lt (bytes_le_to_Nat_bound xs) (bytes_le_to_Nat ys)).symm

theorem bytes_le_to_Nat_split (bs : List byte) (q : Nat) (hq : q ≤ bs.length) :
    bytes_le_to_Nat bs
      = bytes_le_to_Nat (bs.take q) + bytes_le_to_Nat (bs.drop q) * 2 ^ (8 * q) := by
  conv => lhs; rw [← List.take_append_drop q bs]
  rw [bytes_le_to_Nat_app_add, List.length_take, Nat.min_eq_left hq]

theorem bytes_le_to_Nat_take (bs : List byte) (q : Nat) (hq : q ≤ bs.length) :
    bytes_le_to_Nat (bs.take q) = bytes_le_to_Nat bs % 2 ^ (8 * q) := by
  have hsplit := bytes_le_to_Nat_split bs q hq
  have hlt : bytes_le_to_Nat (bs.take q) < 2 ^ (8 * q) := by
    have h := bytes_le_to_Nat_bound (bs.take q)
    rw [List.length_take, Nat.min_eq_left hq] at h
    exact h
  rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

theorem bytes_le_to_Nat_drop (bs : List byte) (q : Nat) (hq : q ≤ bs.length) :
    bytes_le_to_Nat (bs.drop q) = bytes_le_to_Nat bs / 2 ^ (8 * q) := by
  have hsplit := bytes_le_to_Nat_split bs q hq
  have hlt : bytes_le_to_Nat (bs.take q) < 2 ^ (8 * q) := by
    have h := bytes_le_to_Nat_bound (bs.take q)
    rw [List.length_take, Nat.min_eq_left hq] at h
    exact h
  rw [hsplit, Nat.mul_comm (bytes_le_to_Nat (bs.drop q)) (2 ^ (8 * q)),
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem zbN_mod_pow (k i : Nat) (a : Nat) (hi : i < k) :
    zbN (a % 2 ^ (8 * k)) i = zbN a i := by
  have hpow : 2 ^ (8 * k) = 2 ^ (8 * i) * (256 * 2 ^ (8 * k - 8 * i - 8)) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hN : 2 ^ (8 * i) * (256 * (2 ^ (8 * k - 8 * i - 8) * (a / 2 ^ (8 * k))))
      = 2 ^ (8 * k) * (a / 2 ^ (8 * k)) := by
    rw [← Nat.mul_assoc (2 ^ (8 * i)) 256 (2 ^ (8 * k - 8 * i - 8) * (a / 2 ^ (8 * k))),
      ← Nat.mul_assoc (2 ^ (8 * i) * 256) (2 ^ (8 * k - 8 * i - 8)) (a / 2 ^ (8 * k)),
      Nat.mul_assoc (2 ^ (8 * i)) 256 (2 ^ (8 * k - 8 * i - 8)), ← hpow]
  have hdecomp : a = a % 2 ^ (8 * k)
      + 2 ^ (8 * i) * (256 * (2 ^ (8 * k - 8 * i - 8) * (a / 2 ^ (8 * k)))) := by
    rw [hN]
    exact (Nat.mod_add_div a (2 ^ (8 * k))).symm
  conv => rhs; rw [hdecomp]
  rw [zbN_add_shift]

theorem zbN_mod32 (a i : Nat) (hi : i < 4) : zbN (a % 2 ^ 32) i = zbN a i := by
  rw [show (32 : Nat) = 8 * 4 from rfl]
  exact zbN_mod_pow 4 i a hi

theorem bv_swrap32_mod (z : Int) :
    bv_swrap 32 z % ((2 ^ 32 : Nat) : Int) = z % ((2 ^ 32 : Nat) : Int) := by
  unfold bv_swrap
  rw [Int.emod_sub_emod]
  congr 1
  omega

theorem bv_swrap32_small (z : Int) (h0 : 0 ≤ z) (h1 : z < ((2 ^ 31 : Nat) : Int)) :
    bv_swrap 32 z = z := by
  unfold bv_swrap
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.add_sub_cancel]

/-- `LWv l` is  `v_lw (Z_to_bv 64 (lez l))` for `l` of at most 8
    bytes (this file uses 4-byte words throughout). -/
theorem LWv_eq (l : List byte) (H : l.length ≤ 8) :
    LWv l = v_lw (BitVec.ofInt 64 (lez l)) := by
  have hl : 0 ≤ lez l := bytes_le_to_Z_nonneg l
  have hlt : lez l < ((2 ^ 64 : Nat) : Int) := by
    show bytes_le_to_Z l < ((2 ^ 64 : Nat) : Int)
    have h := bytes_le_to_Z_bound l
    have h8 : 8 * l.length ≤ 64 := by omega
    have h2 : (((2 : Nat) ^ (8 * l.length) : Nat) : Int) ≤ ((2 ^ 64 : Nat) : Int) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide) h8
    omega
  have hx : (((BitVec.ofInt 64 (lez l)).toNat : Int)) = lez l := by
    rw [BitVec.toNat_ofInt, Int.toNat_emod hl (by omega), Int.toNat_natCast,
      Int.natCast_emod, Int.toNat_of_nonneg hl, Int.emod_eq_of_lt hl hlt]
  unfold LWv v_lw
  rw [hx]

theorem lez_bound_len (bs : List byte) (k : Nat) (H : bs.length = k) :
    0 ≤ lez bs ∧ lez bs < ((2 ^ (8 * k) : Nat) : Int) := by
  subst H
  exact ⟨bytes_le_to_Z_nonneg bs, bytes_le_to_Z_bound bs⟩

theorem lez4_range (l : List byte) (H : l.length = 4) :
    0 ≤ lez l ∧ lez l < ((2 ^ 32 : Nat) : Int) := by
  have h := lez_bound_len l 4 H
  rw [show 8 * 4 = 32 from rfl] at h
  exact h

theorem u_lez4 (l : List byte) (H : l.length = 4) :
    ((BitVec.ofInt 64 (lez l)).toNat : Int) = lez l := by
  have h := lez4_range l H
  exact u_Z2bv _ h.1 (by omega)

theorem u_vlw_mod32 (l : List byte) (H : l.length = 4) :
    (LWv l).toNat % 2 ^ 32 = bytes_le_to_Nat l := by
  have hb := lez4_range l H
  generalize hx : (LWv l).toNat = x
  have hz : ((x : Nat) : Int) = bv_swrap 32 (lez l) % ((2 ^ 64 : Nat) : Int) := by
    rw [← hx]
    unfold LWv
    rw [BitVec.toNat_ofInt]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hkey : (((x % 2 ^ 32 : Nat)) : Int) = (bytes_le_to_Nat l : Int) := by
    have s1 : (((x % 2 ^ 32 : Nat)) : Int) = (x : Int) % ((2 ^ 32 : Nat) : Int) :=
      Int.natCast_emod _ _
    have s2 : (x : Int) % ((2 ^ 32 : Nat) : Int)
        = (bv_swrap 32 (lez l) % ((2 ^ 64 : Nat) : Int)) % ((2 ^ 32 : Nat) : Int) := by
      rw [hz]
    have s3 : bv_swrap 32 (lez l) % ((2 ^ 64 : Nat) : Int) % ((2 ^ 32 : Nat) : Int)
        = bv_swrap 32 (lez l) % ((2 ^ 32 : Nat) : Int) :=
      Int.emod_emod_of_dvd _ (by
        refine ⟨((2 ^ 32 : Nat) : Int), ?_⟩
        rw [← Int.natCast_mul, ← Nat.pow_add])
    have s4 : bv_swrap 32 (lez l) % ((2 ^ 32 : Nat) : Int) = lez l := by
      rw [bv_swrap32_mod, Int.emod_eq_of_lt hb.1 hb.2]
    have s5 : lez l = (bytes_le_to_Nat l : Int) := (Int.toNat_of_nonneg hb.1).symm
    rw [s1, s2, s3, s4, s5]
  exact Int.natCast_inj.mp hkey

theorem testbit_u_LWv (l : List byte) (i : Nat) (H : l.length = 4) (Hi : i < 4) :
    zbN ((LWv l).toNat % 2 ^ 32) i = zbN (bytes_le_to_Nat l) i := by
  rw [u_vlw_mod32 l H]

theorem lez_cons (b : byte) (bs : List byte) :
    lez (b :: bs) = zlor ((b.toNat : Int)) (zshiftl (lez bs) 8) := by
  have h1 : ((b.toNat : Int)).toNat = b.toNat := rfl
  have h2 : (zshiftl (lez bs) 8).toNat = bytes_le_to_Nat bs * 2 ^ 8 := by
    have hb : 0 ≤ lez bs := bytes_le_to_Z_nonneg bs
    unfold zshiftl
    rw [Int.toNat_mul hb (by decide : (0 : Int) ≤ ((2 ^ 8 : Nat) : Int)),
      Int.toNat_natCast]
    rfl
  unfold zlor
  rw [h2, h1]
  show (((b.toNat ||| (bytes_le_to_Nat bs <<< 8)) : Nat) : Int)
      = (((b.toNat ||| (bytes_le_to_Nat bs * 2 ^ 8)) : Nat) : Int)
  rw [Nat.shiftLeft_eq]

theorem zbN_bytes : ∀ (bs : List byte) (i : Nat), i < bs.length →
    zbN (bytes_le_to_Nat bs) i = (bs.getD i (BitVec.ofInt 8 0)).toNat
  | [], i, hi => by simp at hi
  | b :: bs, i, hi => by
    have hb : b.toNat < 256 := b.isLt
    have hor : (b.toNat ||| (bytes_le_to_Nat bs <<< 8))
        = b.toNat + bytes_le_to_Nat bs * 2 ^ 8 := by
      conv => rhs; rw [← Nat.shiftLeft_eq]
      rw [Nat.or_comm, Nat.add_comm]
      exact (Nat.shiftLeft_add_eq_or_of_lt (show b.toNat < 2 ^ 8 from hb)
        (bytes_le_to_Nat bs)).symm
    cases i with
    | zero =>
      show (b.toNat ||| (bytes_le_to_Nat bs <<< 8)) / 2 ^ (8 * 0) % 256 = b.toNat
      rw [show 8 * 0 = 0 from rfl, Nat.pow_zero, Nat.div_one, hor,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    | succ j =>
      show (b.toNat ||| (bytes_le_to_Nat bs <<< 8)) / 2 ^ (8 * (j + 1)) % 256
        = ((b :: bs).getD (j + 1) (BitVec.ofInt 8 0)).toNat
      rw [hor, List.getD_cons_succ]
      have h8 : 2 ^ (8 * (j + 1)) = 2 ^ 8 * 2 ^ (8 * j) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h8, ← Nat.div_div_eq_div_mul, Nat.mul_comm (bytes_le_to_Nat bs) (2 ^ 8),
        Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 8), Nat.div_eq_of_lt hb,
        Nat.zero_add]
      exact zbN_bytes bs j (by simpa using hi)

theorem zbN_lez (bs : List byte) (i : Nat) :
    zbN (bytes_le_to_Nat bs) i
      = if i < bs.length then (bs.getD i (BitVec.ofInt 8 0)).toNat else 0 := by
  by_cases h : i < bs.length
  · rw [ite_eq_left h]; exact zbN_bytes bs i h
  · rw [ite_eq_right h]
    have hz : bytes_le_to_Nat bs < 2 ^ (8 * bs.length) := bytes_le_to_Nat_bound bs
    have hle : 8 * bs.length ≤ 8 * i := by omega
    show (bytes_le_to_Nat bs / 2 ^ (8 * i)) % 256 = 0
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) hle)),
      Nat.zero_mod]

theorem bytes_le_inj {bs1 bs2 : List byte} (hlen : bs1.length = bs2.length)
    (h : lez bs1 = lez bs2) : bs1 = bs2 := by
  have hN : bytes_le_to_Nat bs1 = bytes_le_to_Nat bs2 := by
    have h1 : ((bytes_le_to_Nat bs1 : Nat) : Int) = ((bytes_le_to_Nat bs2 : Nat) : Int) := h
    exact Int.natCast_inj.mp h1
  apply List.ext_getElem?
  intro i
  by_cases hi : i < bs1.length
  · have hi2 : i < bs2.length := by omega
    have hd : bs1.getD i (BitVec.ofInt 8 0) = bs2.getD i (BitVec.ofInt 8 0) := by
      apply BitVec.eq_of_toNat_eq
      rw [← zbN_bytes bs1 i hi, ← zbN_bytes bs2 i hi2, hN]
    have e1 : bs1[i]? = some (bs1.getD i (BitVec.ofInt 8 0)) := by
      rw [List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
      rfl
    have e2 : bs2[i]? = some (bs2.getD i (BitVec.ofInt 8 0)) := by
      rw [List.getElem?_eq_getElem hi2, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi2]
      rfl
    rw [e1, e2, hd]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem testbit_lez_high (bs : List byte) (i : Nat) (Hi : bs.length ≤ i) :
    zbN (bytes_le_to_Nat bs) i = 0 := by
  rw [zbN_lez, ite_eq_right (by omega)]

theorem testbit_lez_skipn (q : Nat) (bs : List byte) (i : Nat) :
    zbN (bytes_le_to_Nat (bs.drop q)) i = zbN (bytes_le_to_Nat bs) (i + q) := by
  rw [zbN_lez (bs.drop q) i, zbN_lez bs (i + q)]
  simp only [List.length_drop, List.getD_eq_getElem?_getD]
  have hq : (bs.drop q)[i]? = bs[i + q]? := by
    rw [List.getElem?_drop, Nat.add_comm q i]
  rw [hq]
  by_cases h : i < bs.length - q
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem zbN_take_lt (q : Nat) (bs : List byte) (i : Nat) (h : i < q) :
    zbN (bytes_le_to_Nat (bs.take q)) i = zbN (bytes_le_to_Nat bs) i := by
  have hminl : min q bs.length ≤ q := Nat.min_le_left _ _
  rw [zbN_lez (bs.take q) i, zbN_lez bs i]
  simp only [List.length_take, List.getD_eq_getElem?_getD]
  rw [List.getElem?_take]
  by_cases hl : i < bs.length
  · rw [ite_eq_left (Nat.lt_min.mpr ⟨h, hl⟩), ite_eq_left h, ite_eq_left hl]
  · rw [ite_eq_right (by omega), ite_eq_right hl]

theorem zbN_take_ge (q : Nat) (bs : List byte) (i : Nat) (h : q ≤ i) :
    zbN (bytes_le_to_Nat (bs.take q)) i = 0 := by
  have hlen : (bs.take q).length ≤ i := by
    rw [List.length_take]
    have := Nat.min_le_left q bs.length
    omega
  exact testbit_lez_high (bs.take q) i hlen

theorem testbit_lez_firstn (q : Nat) (bs : List byte) (i : Nat) :
    zbN (bytes_le_to_Nat (bs.take q)) i
      = if i < q then zbN (bytes_le_to_Nat bs) i else 0 := by
  by_cases h : i < q
  · rw [ite_eq_left h]; exact zbN_take_lt q bs i h
  · rw [ite_eq_right h]; exact zbN_take_ge q bs i (by omega)

theorem zbN_app_left (xs ys : List byte) (i : Nat) (h : i < xs.length) :
    zbN (bytes_le_to_Nat (xs ++ ys)) i = zbN (bytes_le_to_Nat xs) i := by
  rw [zbN_lez (xs ++ ys) i, zbN_lez xs i, List.length_append]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [ite_eq_left (by omega), ite_eq_left h, ite_eq_left h]

theorem zbN_app_right (xs ys : List byte) (i : Nat) (h : ¬ i < xs.length) :
    zbN (bytes_le_to_Nat (xs ++ ys)) i = zbN (bytes_le_to_Nat ys) (i - xs.length) := by
  rw [zbN_lez (xs ++ ys) i, zbN_lez ys (i - xs.length), List.length_append]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [ite_eq_right h]
  by_cases h2 : i - xs.length < ys.length
  · rw [ite_eq_left (by omega), ite_eq_left h2]
  · rw [ite_eq_right (by omega), ite_eq_right h2]

theorem testbit_lez_app (xs ys : List byte) (i : Nat) :
    zbN (bytes_le_to_Nat (xs ++ ys)) i
      = if i < xs.length then zbN (bytes_le_to_Nat xs) i
        else zbN (bytes_le_to_Nat ys) (i - xs.length) := by
  by_cases h : i < xs.length
  · rw [ite_eq_left h]; exact zbN_app_left xs ys i h
  · rw [ite_eq_right h]; exact zbN_app_right xs ys i h

theorem testbit_nth_lez (l : List byte) (q : Nat) (Hq : q < l.length) :
    zbN (bytes_le_to_Nat l) q = (l.getD q (BitVec.ofInt 8 0)).toNat :=
  zbN_bytes l q Hq

theorem Z_to_le_bytes_lez (bs : List byte) :
    Z_to_le_bytes bs.length (lez bs) = bs := by
  have hlen : (Z_to_le_bytes bs.length (lez bs)).length = bs.length :=
    LinuxProcessSem.length_Z_to_le_bytes _ _
  refine bytes_le_inj hlen ?_
  show bytes_le_to_Z (Z_to_le_bytes bs.length (bytes_le_to_Z bs)) = bytes_le_to_Z bs
  rw [bytes_le_Z_to_le bs.length (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)]
  have hz : bytes_le_to_Nat bs < 2 ^ (8 * bs.length) := by
    have h1 : (bytes_le_to_Nat bs : Int) = lez bs :=
      Int.toNat_of_nonneg (bytes_le_to_Z_nonneg bs)
    exact Int.ofNat_lt.mp (by rw [h1]; exact bytes_le_to_Z_bound bs)
  rw [show (bytes_le_to_Z bs).toNat = bytes_le_to_Nat bs from rfl, Nat.mod_eq_of_lt hz]
  rfl

theorem ofInt8_eq_of_emod (z : Int) (b : byte) (h : z % 256 = ((b.toNat : Nat) : Int)) :
    BitVec.ofInt 8 z = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have h256 : (((2 ^ 8 : Nat)) : Int) = 256 := rfl
  rw [h256, h, Int.toNat_natCast]

theorem word_to_le_bytes_4_eq (v : word) (l : List byte) (Hl : l.length = 4)
    (Hb : ((v.toNat : Int)) % ((2 ^ 32 : Nat) : Int) = lez l) :
    word_to_le_bytes 4 v = l := by
  have hlen : (word_to_le_bytes 4 v).length = l.length := by
    unfold word_to_le_bytes
    rw [LinuxProcessSem.length_Z_to_le_bytes, Hl]
  refine bytes_le_inj hlen ?_
  show bytes_le_to_Z (Z_to_le_bytes 4 ((v.toNat : Int))) = bytes_le_to_Z l
  rw [bytes_le_Z_to_le 4 ((v.toNat : Int)) (by omega)]
  rw [show 8 * 4 = 32 from rfl]
  rw [Int.toNat_natCast, Int.natCast_emod]
  exact Hb

/-- The `Nat` `% 2^32` identity as the `Int` one
    `word_to_le_bytes_4_eq` takes. -/
theorem int_mod32_of {x : Nat} {z : Int} (h : x % 2 ^ 32 = z.toNat) (hz : 0 ≤ z) :
    (x : Int) % ((2 ^ 32 : Nat) : Int) = z := by
  rw [← Int.natCast_emod, h, Int.toNat_of_nonneg hz]

theorem sw_bytes_LWv (l : List byte) (H : l.length = 4) :
    word_to_le_bytes 4 (LWv l) = l := by
  exact word_to_le_bytes_4_eq (LWv l) l H
    (int_mod32_of (u_vlw_mod32 l H) (bytes_le_to_Z_nonneg l))

def LBv (b : byte) : word := BitVec.ofInt 64 ((b.toNat : Int))

theorem sb_byte_LBv (b : byte) : BitVec.ofInt 8 ((LBv b).toNat : Int) = b := by
  refine ofInt8_eq_of_emod _ b ?_
  unfold LBv
  rw [u_Z2bv _ (by omega) (by have := b.isLt; omega)]
  show ((b.toNat : Int)) % 256 = ((b.toNat : Nat) : Int)
  rw [Int.emod_eq_of_lt (by omega) (by have := b.isLt; omega)]

theorem sb_byte_eq (v : word) (b : byte)
    (Hb : ((v.toNat : Int)) % 256 = ((b.toNat : Nat) : Int)) :
    BitVec.ofInt 8 ((v.toNat : Int)) = b :=
  ofInt8_eq_of_emod _ b Hb

theorem sb_byte_srli_LWv (l : List byte) (q : Nat) (H : l.length = 4) (Hq : q ≤ 3) :
    BitVec.ofInt 8 ((v_srli (LWv l) ((8 * q : Nat) : Int)).toNat : Int)
      = l.getD q (BitVec.ofInt 8 0) := by
  have hmod := u_vlw_mod32 l H
  have hb := lez4_range l H
  have hlt : bytes_le_to_Nat l < 2 ^ 32 := by omega
  have hq4 : q < 4 := by omega
  generalize hx : (LWv l).toNat = x
  have hxmod : x % 2 ^ 32 = bytes_le_to_Nat l := by rw [← hx]; exact hmod
  refine ofInt8_eq_of_emod _ _ ?_
  have hsmall : x / 2 ^ (8 * q) < 2 ^ 64 := by
    have h1 : x / 2 ^ (8 * q) ≤ x := Nat.div_le_self _ _
    have h2 : x < 2 ^ 64 := by rw [← hx]; exact (LWv l).isLt
    omega
  have hval : ((v_srli (LWv l) ((8 * q : Nat) : Int)).toNat : Int)
      = ((x / 2 ^ (8 * q) : Nat) : Int) := by
    unfold v_srli zshiftr
    rw [hx, BitVec.toNat_ofInt,
      show ((((8 * q : Nat) : Int))).toNat = 8 * q from Int.toNat_natCast (8 * q),
      ← Int.natCast_ediv, Int.toNat_emod (Int.natCast_nonneg _) (by omega),
      Int.toNat_natCast, Int.toNat_natCast, Nat.mod_eq_of_lt hsmall]
  have h1 : zbN x q = zbN (bytes_le_to_Nat l) q := by
    refine (zbN_mod32 x q hq4).symm.trans ?_
    rw [hxmod]
  have key : x / 2 ^ (8 * q) % 256 = (l.getD q (BitVec.ofInt 8 0)).toNat :=
    h1.trans (zbN_bytes l q (by omega))
  rw [hval]
  have e : ((x / 2 ^ (8 * q) : Nat) : Int) % 256
      = (((x / 2 ^ (8 * q)) % 256 : Nat) : Int) := (Int.natCast_emod _ _).symm
  rw [e, key]
theorem testbit_u_vor (x y : word) :
    (v_or x y).toNat = x.toNat ||| y.toNat := by
  have hx : ((x.toNat : Int)).toNat = x.toNat := rfl
  have hy : ((y.toNat : Int)).toNat = y.toNat := rfl
  unfold v_or zlor
  rw [hx, hy, BitVec.toNat_ofInt, ← Int.natCast_emod,
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.isLt y.isLt), Int.toNat_natCast]


/-! =====================================================================
    The merged word of the misaligned-destination loops
    ===================================================================== -/

/-   proves `sw_bytes_merge` with a per-`Z.testbit` walk: bit `i`
    of `v_or`, then `Z.lor_spec` / `Z.shiftl_spec` on `v_slli`/`v_srliw`,
    then one `Z.ltb_spec` case per byte.  Lean v4.31.0 has no
    `Int.testBit`, so the walk is replaced by a VALUE computation at
    `Nat` — and both value identities it needs are in this toolchain's
    CORE, so no new bit primitive is introduced:

      `Nat.or_mod_two_pow`   `(a ||| b) % 2^n = a % 2^n ||| b % 2^n`
                             — the "mod through `|||`" step, at `n = 32`
                             (a whole number of bytes, so the byte kit
                             below can read the result back);
      `Nat.shiftLeft_add_eq_or_of_lt`
                             `b < 2^i → a <<< i + b = a <<< i ||| b`
                             — the shifted half of the merge has its low
                             `i` bits clear, so the `|||` is an addition.
                             (`Nat.shiftLeft_or_distrib` is core too, but
                             the disjoint-addition form is the one used.
                             The tree already uses both:
                             `PropExec.bytes_le_to_Nat_app` and
                             `AxSymExec3Sound.two_mul_or`.)

    The rest is this file's own byte kit: `u_vlw_mod32` (a word's low 32
    bits are its four bytes), `bytes_le_to_Nat_{take,drop,app_add}` (the
    RHS algebra) and `word_to_le_bytes_4_eq` (a `List byte` is determined
    by the value of its four bytes).

    An earlier version of this file recorded both theorems as DEFERRED,
    on the grounds that `(x ||| y) % 2^k` and `(a ||| b) <<< k` "exist
    neither here nor in core".  That was measured WRONG: what does not
    exist is the name (`Nat.land_lor_distrib`, `Nat.lor_shiftLeft`,
    `Nat.testbit_lor`) — the facts are core, under the names above.  This
    is's pattern again: the lemma was one layer up.
-/

/-- `2^32` divides `2^64`: the two windows a `word` value is read through. -/
theorem pow32_dvd_pow64 : ((2 ^ 32 : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
  refine ⟨((2 ^ 32 : Nat) : Int), ?_⟩
  rw [← Int.natCast_mul, ← Nat.pow_add]

/-- The low 32 bits of a `word` built by `BitVec.ofInt 64` are the `Int`'s
    own `% 2^32`, whatever the sign of the `Int` (so the sign extension
    `v_srliw` performs below cannot disturb them). -/
theorem ofInt64_toNat_mod32 (z : Int) :
    (BitVec.ofInt 64 z).toNat % 2 ^ 32 = (z % ((2 ^ 32 : Nat) : Int)).toNat := by
  rw [BitVec.toNat_ofInt]
  have h32 : (0 : Int) ≤ ((2 ^ 32 : Nat) : Int) := Int.natCast_nonneg _
  have h := Int.toNat_emod (x := z % ((2 ^ 64 : Nat) : Int)) (y := ((2 ^ 32 : Nat) : Int))
    (Int.emod_nonneg z (by decide)) h32
  rw [Int.toNat_natCast] at h
  rw [← h, Int.emod_emod_of_dvd _ pow32_dvd_pow64]

/-- Low 32 bits of `v_slli x t`: `x`'s low `32 - t` bits, shifted up. -/
theorem v_slli_toNat_mod32 (x : word) (t : Nat) (ht : t ≤ 32) :
    (v_slli x ((t : Nat) : Int)).toNat % 2 ^ 32 = (x.toNat % 2 ^ (32 - t)) * 2 ^ t := by
  unfold v_slli zshiftl
  rw [Int.toNat_natCast, ofInt64_toNat_mod32, ← Int.natCast_mul, ← Int.natCast_emod,
    Int.toNat_natCast]
  have hpow : (2 : Nat) ^ (32 - t) * 2 ^ t = 2 ^ 32 := by
    rw [← Nat.pow_add, Nat.sub_add_cancel ht]
  rw [← hpow]
  exact Nat.mul_mod_mul_right _ _ _

/-- Low 32 bits of `v_srliw x s`: `x`'s low 32 bits, shifted right.  The
    32-bit sign extension `v_srliw` adds in bits 32..63 does not survive
    the `% 2^32`. -/
theorem v_srliw_toNat_mod32 (x : word) (s : Nat) :
    (v_srliw x ((s : Nat) : Int)).toNat % 2 ^ 32 = x.toNat % 2 ^ 32 / 2 ^ s := by
  unfold v_srliw zshiftr
  rw [Int.toNat_natCast, ofInt64_toNat_mod32, bv_swrap32_mod, bv_wrap,
    ← Int.natCast_emod, ← Int.natCast_ediv]
  have hV : (x.toNat % 2 ^ 32) / 2 ^ s < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hV), Int.toNat_natCast]

/-- `v_or` commutes. -/
theorem v_or_comm (x y : word) : v_or x y = v_or y x := by
  apply BitVec.eq_of_toNat_eq
  rw [testbit_u_vor, testbit_u_vor, Nat.or_comm]

/-- The merged word of the misaligned-destination loops: for `1 <= q <= 3`,
    `(x << 8(4-q)) | (w >>32 8q)` stores bytes `q..3` of `l1` (the word `w`)
    followed by bytes `0..q-1` of `l2` (the word `x`). -/
theorem sw_bytes_merge (l1 l2 : List byte) (q : Nat) (v : word)
    (H1 : l1.length = 4) (H2 : l2.length = 4) (Hq1 : 1 ≤ q) (Hq3 : q ≤ 3)
    (Hv : v = v_or (v_slli (LWv l2) (32 - 8 * (q : Int)))
                   (v_srliw (LWv l1) (8 * (q : Int)))) :
    word_to_le_bytes 4 v = l1.drop q ++ l2.take q := by
  have hs : 8 * q ≤ 32 := by omega
  have hcast1 : (32 : Int) - 8 * (q : Int) = ((32 - 8 * q : Nat) : Int) := by omega
  have hcast2 : (8 : Int) * (q : Int) = ((8 * q : Nat) : Int) := by omega
  have hdvd : 2 ^ (8 * q) ∣ 2 ^ 32 := ⟨2 ^ (32 - 8 * q), by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hs]⟩
  -- the merged value, at its low four bytes
  have hval : v.toNat % 2 ^ 32 = bytes_le_to_Nat (l1.drop q ++ l2.take q) := by
    rw [Hv, testbit_u_vor, Nat.or_mod_two_pow, hcast1,
      v_slli_toNat_mod32 _ _ (by omega), hcast2, v_srliw_toNat_mod32]
    have ht : 32 - (32 - 8 * q) = 8 * q := by omega
    rw [ht]
    have hmod2 : (LWv l2).toNat % 2 ^ (8 * q) = bytes_le_to_Nat l2 % 2 ^ (8 * q) := by
      have h := Nat.mod_mod_of_dvd (c := 2 ^ (8 * q)) (b := 2 ^ 32) (LWv l2).toNat hdvd
      rw [u_vlw_mod32 l2 H2] at h
      exact h.symm
    have hmod1 : (LWv l1).toNat % 2 ^ 32 / 2 ^ (8 * q)
        = bytes_le_to_Nat l1 / 2 ^ (8 * q) := by
      rw [u_vlw_mod32 l1 H1]
    rw [hmod2, hmod1]
    -- the two halves are disjoint, so `|||` is `+`
    have hlt : bytes_le_to_Nat l1 / 2 ^ (8 * q) < 2 ^ (32 - 8 * q) := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [← Nat.pow_add, Nat.add_sub_cancel' hs]
      simpa [H1] using bytes_le_to_Nat_bound l1
    have hor : (bytes_le_to_Nat l2 % 2 ^ (8 * q)) * 2 ^ (32 - 8 * q)
        ||| (bytes_le_to_Nat l1 / 2 ^ (8 * q))
        = bytes_le_to_Nat (l1.drop q) + bytes_le_to_Nat (l2.take q) * 2 ^ (8 * (4 - q)) := by
      rw [← Nat.shiftLeft_eq,
        ← Nat.shiftLeft_add_eq_or_of_lt (i := 32 - 8 * q)
          (b := bytes_le_to_Nat l1 / 2 ^ (8 * q)) hlt (bytes_le_to_Nat l2 % 2 ^ (8 * q))]
      rw [Nat.shiftLeft_eq, bytes_le_to_Nat_drop l1 q (by omega),
        bytes_le_to_Nat_take l2 q (by omega), show 8 * (4 - q) = 32 - 8 * q from by omega,
        Nat.add_comm]
    rw [hor]
    have hlen : (l1.drop q).length = 4 - q := by rw [List.length_drop, H1]
    rw [← hlen, ← bytes_le_to_Nat_app_add]
  refine word_to_le_bytes_4_eq v (l1.drop q ++ l2.take q) ?_ ?_
  · rw [List.length_append, List.length_drop, List.length_take, H1, H2]
    omega
  · exact int_mod32_of hval (bytes_le_to_Z_nonneg _)

/-- The same with the `|||` operands commuted (the compiler emits both). -/
theorem sw_bytes_merge' (l1 l2 : List byte) (q : Nat) (v : word)
    (H1 : l1.length = 4) (H2 : l2.length = 4) (Hq1 : 1 ≤ q) (Hq3 : q ≤ 3)
    (Hv : v = v_or (v_srliw (LWv l1) (8 * (q : Int)))
                   (v_slli (LWv l2) (32 - 8 * (q : Int)))) :
    word_to_le_bytes 4 v = l1.drop q ++ l2.take q :=
  sw_bytes_merge l1 l2 q v H1 H2 Hq1 Hq3 (by rw [Hv, v_or_comm])


/-! =====================================================================
    `store_ok` on a sub-range, lifted through the writes done so far
    ===================================================================== -/

/-- A writable range survives the writes `wbytes m dst bsw` did on top of it,
    and any sub-range of it is writable. -/
theorem store_ok_at (segs : List Segment) (m : word → Option byte) (dst : word)
    (N : Nat) (bsw : List byte) (j k : Nat)
    (Hnw : (dst.toNat : Int) + (N : Int) ≤ ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs m dst N = true)
    (Hj : 0 ≤ j) (Hk : j + (k : Int) ≤ (N : Int)) :
    store_ok segs (wbytes m dst bsw) (at_ dst j) k = true := by
  cases k with
  | zero => rfl
  | succ k' =>
    have hu : ((at_ dst j).toNat : Int) = (dst.toNat : Int) + j := by
      exact at_u dst j (by omega) (by omega)
    refine store_ok_mono segs (k' + 1) m _ (at_ dst j) (wbytes_grows bsw m dst) ?_
    refine store_ok_sub segs m dst (at_ dst j) N (k' + 1) Hnw Hok ?_ ?_
    · omega
    · omega

/-! =====================================================================
    Register preservation across a summary
    ===================================================================== -/

/-- The registers a leaf routine built from a0..a7/t0..t6 temporaries must
    preserve for its C caller (and `a0`, which memcpy returns unchanged):
    ra sp gp tp s0 s1 a0 s2..s11. -/
def callee_kept : List reg := [1, 2, 3, 4, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- [keeps regs regs']: every callee-kept register reads the same. -/
def keeps (regs regs' : BvMap word) : Prop :=
  ∀ r : reg, r ∈ callee_kept → getr regs' r = getr regs r

theorem keeps_refl (regs : BvMap word) : keeps regs regs :=
  fun _ _ => rfl

theorem keeps_trans {r1 r2 r3 : BvMap word} (h12 : keeps r1 r2) (h23 : keeps r2 r3) :
    keeps r1 r3 :=
  fun r hr => (h23 r hr).trans (h12 r hr)

/-- One update of a scratch register keeps the callee-kept set. -/
theorem keeps_upd (regs regs' : BvMap word) (rd : reg) (v : word)
    (K : keeps regs regs') (Hn : rd ∉ callee_kept) : keeps regs (regupd regs' rd v) := by
  intro r hr
  rw [getr_other regs' rd v r (by intro h; exact Hn (h ▸ hr))]
  exact K r hr

/-- Using a `keeps` fact for one register. -/
theorem keeps_getr (regs regs' : BvMap word) (r : reg) (K : keeps regs regs')
    (Hr : r ∈ callee_kept) : getr regs' r = getr regs r :=
  K r Hr

/-- Close `r ∈ callee_kept` for a literal register by computation. -/
macro "kept_reg" : tactic => `(tactic| decide)

/-- Decide non-membership of a literal register by computation . -/
macro "not_kept" : tactic => `(tactic| decide)

/-- Close `keeps regs (regupd (regupd ... regs ...) ..)` for a concrete chain
    of scratch-register updates. -/
macro "solve_keeps" : tactic =>
  `(tactic|
    (repeat (first
      | apply keeps_upd
      | apply keeps_refl
      | assumption))
    <;> (first | decide | assumption))
theorem keeps_sp_example (regs regs' : BvMap word) (K : keeps regs regs') :
    getr regs' 2 = getr regs 2 := by
  exact keeps_getr regs regs' 2 K (by decide)

/-- Sanity check for [solve_keeps]: a two-update chain of scratch registers. -/
theorem keeps_chain_example (regs : BvMap word) :
    keeps regs (regupd (regupd regs 11 0) 12 1) := by
  solve_keeps

/-! =====================================================================
    Composing block summaries stated with an existential register file
    ===================================================================== -/

theorem runs_trans (segs : List Segment) (s0 : machine_state)
    (st1 : BvMap word → machine_state) (P1 : BvMap word → Prop)
    (st2 : BvMap word → machine_state) (P2 : BvMap word → Prop)
    (H1 : ∃ r1, msteps segs s0 (st1 r1) ∧ P1 r1)
    (K : ∀ r1, P1 r1 → ∃ r2, msteps segs (st1 r1) (st2 r2) ∧ P2 r2) :
    ∃ r2, msteps segs s0 (st2 r2) ∧ P2 r2 := by
  obtain ⟨r1, R1, Hp⟩ := H1
  obtain ⟨r2, R2, H2⟩ := K r1 Hp
  exact ⟨r2, msteps_trans segs s0 (st1 r1) (st2 r2) R1 R2, H2⟩

/-! =====================================================================
    Callee-SAVED preservation (for routines whose a0 is a result)
    ===================================================================== -/

def callee_saved : List reg := [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def keeps_cs (regs regs' : BvMap word) : Prop :=
  ∀ r : reg, r ∈ callee_saved → getr regs' r = getr regs r

theorem keeps_cs_refl (regs : BvMap word) : keeps_cs regs regs :=
  fun _ _ => rfl

theorem keeps_cs_trans {r1 r2 r3 : BvMap word} (h12 : keeps_cs r1 r2) (h23 : keeps_cs r2 r3) :
    keeps_cs r1 r3 :=
  fun r hr => (h23 r hr).trans (h12 r hr)

theorem keeps_cs_upd (regs regs' : BvMap word) (rd : reg) (v : word)
    (K : keeps_cs regs regs') (Hn : rd ∉ callee_saved) : keeps_cs regs (regupd regs' rd v) := by
  intro r hr
  rw [getr_other regs' rd v r (by intro h; exact Hn (h ▸ hr))]
  exact K r hr

/-- Writing back the entry value of a saved register (epilogue reloads). -/
theorem keeps_cs_upd_same (regs regs' : BvMap word) (rd : reg) (v : word)
    (K : keeps_cs regs regs') (Hv : getr regs rd = v) (Hnz : rd ≠ 0) :
    keeps_cs regs (regupd regs' rd v) := by
  intro r hr
  by_cases h : r = rd
  · subst h
    rw [getr_same regs' r v Hnz, Hv]
  · rw [getr_other regs' rd v r h]
    exact K r hr

theorem keeps_keeps_cs (regs regs' : BvMap word) (K : keeps regs regs') :
    keeps_cs regs regs' := by
  intro r hr
  refine K r ?_
  simp only [callee_saved, callee_kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl
  all_goals simp

theorem keeps_cs_getr (regs regs' : BvMap word) (r : reg) (K : keeps_cs regs regs')
    (Hr : r ∈ callee_saved) : getr regs' r = getr regs r :=
  K r Hr

/-- Close a `keeps_cs` chain for concrete scratch updates . -/
macro "solve_keeps_cs" : tactic =>
  `(tactic|
    (repeat (first
      | apply keeps_cs_upd
      | apply keeps_cs_refl
      | assumption))
    <;> (first | decide | assumption | (apply keeps_keeps_cs; assumption)))

/-! ## Sanity checks -/

example : callee_kept.length = 17 := by decide
example : callee_saved.length = 16 := by decide
example : (2 : reg) ∈ callee_kept := by decide
example : (11 : reg) ∉ callee_kept := by decide
example : LWv [BitVec.ofInt 8 1, BitVec.ofInt 8 2, BitVec.ofInt 8 3, BitVec.ofInt 8 4]
    = BitVec.ofInt 64 0x04030201 := by decide
example : LBv (BitVec.ofInt 8 0xab) = BitVec.ofInt 64 0xab := by decide
example : sub [0, 1, 2, 3, 4] 2 2 = [2, 3] := by decide

/-! ### `sw_bytes_merge` at the three shift amounts, as concrete instances

    The theorems themselves are proved above, in their  position
    right after `testbit_u_vor`.  The first three instances below are
    `by decide` — kernel checks of the STATEMENT against this tree's
    `v_or`/`v_slli`/`v_srliw`/`LWv`/`word_to_le_bytes`, independent of the
    proof — including the sign-extended case (`0x84`/`0xf5` high bytes, so
    `LWv` is negative) and all three shifts `q = 1, 2, 3`.  The last two
    are the theorems APPLIED to the same concrete words, so the statement
    and its proof are checked against one and the same value (and
    `sw_bytes_merge'` is exercised at its own operand order). -/

example :
    let l1 : List byte := [1, 2, 3, 0x84]
    let l2 : List byte := [0xf5, 6, 7, 8]
    let v : word :=
      v_or (v_slli (LWv l2) (32 - 8 * (1 : Int))) (v_srliw (LWv l1) (8 * (1 : Int)))
    word_to_le_bytes 4 v = l1.drop 1 ++ l2.take 1 := by decide

example :
    let l1 : List byte := [1, 2, 3, 0x84]
    let l2 : List byte := [0xf5, 6, 7, 8]
    let v : word :=
      v_or (v_slli (LWv l2) (32 - 8 * (2 : Int))) (v_srliw (LWv l1) (8 * (2 : Int)))
    word_to_le_bytes 4 v = l1.drop 2 ++ l2.take 2 := by decide

example :
    let l1 : List byte := [1, 2, 3, 0x84]
    let l2 : List byte := [0xf5, 6, 7, 8]
    let v : word :=
      v_or (v_slli (LWv l2) (32 - 8 * (3 : Int))) (v_srliw (LWv l1) (8 * (3 : Int)))
    word_to_le_bytes 4 v = l1.drop 3 ++ l2.take 3 := by decide

example :
    let l1 : List byte := [1, 2, 3, 0x84]
    let l2 : List byte := [0xf5, 6, 7, 8]
    word_to_le_bytes 4
        (v_or (v_slli (LWv l2) (32 - 8 * (1 : Int))) (v_srliw (LWv l1) (8 * (1 : Int))))
      = l1.drop 1 ++ l2.take 1 :=
  sw_bytes_merge _ _ 1 _ rfl rfl (by decide) (by decide) rfl

example :
    let l1 : List byte := [1, 2, 3, 0x84]
    let l2 : List byte := [0xf5, 6, 7, 8]
    word_to_le_bytes 4
        (v_or (v_srliw (LWv l1) (8 * (3 : Int))) (v_slli (LWv l2) (32 - 8 * (3 : Int))))
      = l1.drop 3 ++ l2.take 3 :=
  sw_bytes_merge' _ _ 3 _ rfl rfl (by decide) (by decide) rfl
