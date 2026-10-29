/-
  * Common.MallocDefs — shared pure definitions for the musl mallocng
    summaries (enframe / malloc side and free side).  No proofs about
    code here, only the arithmetic model.

  Layout reminders (reference binary): `size_classes = u16[48]` at rodata
  `0x103b0`; `struct meta`: `+16` mem (group address `M`), `+24` avail_mask
  (u32), `+28` freed_mask (u32), `+32` packed word `W` = last_idx[0..4] |
  freeable[5] | sizeclass[6..11] | maplen[12..63]; group: `*(u64*)M = meta`,
  slots start at `M+16` ("storage"), slot `[idx]` at `M + 16 + stride*idx`,
  its `[end]` = `start + stride - 4`; user pointer `p = start + 16*off`;
  in-band header: `p[-2..-1] = (p - M - 16)/16` (u16 "offset"),
  `p[-3] = idx + 32*min(reserved,5)`, `p[-4] = 0`.  `UNIT = 16`, `IB = 4`.

   is stdlib-only (`ZArith List Lia Bool`).
  Lean's core `Int` library has no bitwise or/and (only `~~~` and the two
  shifts), while `smear` below is defined with `Z.lor`/`Z.land`.  This tree
  therefore imports `Sys.Uapi` and uses its `z_lor`/`z_land`, which are the
  `Nat`-backed encodings used throughout this tree: they agree with
  `Z.lor`/`Z.land` on NONNEGATIVE operands, and every argument `smear`
  receives is a nonnegative byte count (`slack_of` on a real request).
  See `Sys/Uapi.lean` for the same note at the definition site.
 `nth (Z.to_nat sc) l 0`
  is `l.getD sc.toNat 0`.  `negb (x =? 0)` is `!(x == 0)`, `Z.ltb`/`Z.leb`
  are `<`/`≤` on `Int` (decidable propositions, so they sit in `if`).
-/
import LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.Common.MallocDefs

open LinuxSem.LinuxProcessSem.Sys.Uapi (z_land z_lor)

def UNIT : Int := 16

def IB : Int := 4

/-- musl's `size_classes` table (units of 16 bytes), 48 entries. -/
def size_classes : List Int :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 20, 25, 31, 36, 42, 50, 63, 72, 84, 102, 127,
   146, 170, 204, 255, 292, 340, 409, 511, 584, 682, 818, 1023, 1169, 1364, 1637, 2047,
   2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191]

/-- `size_class sc` is the table entry at index `sc` (0 when out of range). -/
def size_class (sc : Int) : Int :=
  size_classes.getD sc.toNat 0

/-! ### Fields of the packed meta word `W` (meta+32) -/

def w_lastidx (W : Int) : Int := W % 32

def w_freeable (W : Int) : Int := (W / 32) % 2

def w_sizeclass (W : Int) : Int := (W / 64) % 64

def w_maplen (W : Int) : Int := W / 4096

/-- `get_stride`: a single-slot mmapped group spans its whole map. -/
def slot_stride (maplen lastidx sc : Int) : Int :=
  if (!(maplen == 0)) && (lastidx == 0) then maplen * 4096 - UNIT else UNIT * size_class sc

/-! ### Slot geometry for group memory `M` -/

def slot_start (M stride idx : Int) : Int := M + UNIT + stride * idx

def slot_end (M stride idx : Int) : Int := slot_start M stride idx + stride - IB

/-- : `forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191`.
-/
theorem size_class_pos : ∀ sc : Int, 0 ≤ sc → sc < 48 → 1 ≤ size_class sc ∧ size_class sc ≤ 8191 := by
  have htab : ∀ k : Fin 48, 1 ≤ size_classes.getD k.val 0 ∧ size_classes.getD k.val 0 ≤ 8191 := by
    decide
  intro sc h0 h48
  unfold size_class
  exact htab ⟨sc.toNat, by omega⟩

/-! ---------------------------------------------------------------------
    enframe: slot-offset cycling and the in-band sizes
    --------------------------------------------------------------------- -/

/-- `slack` = number of spare 16-byte units in the slot for a request of `n`
    bytes: `(stride - IB - n) / UNIT`. -/
def slack_of (stride n : Int) : Int := (stride - IB - n) / UNIT

/-- musl's `m |= m>>1; m |= m>>2; m |= m>>4` on `slack`. -/
def smear (slack : Int) : Int :=
  let m1 := z_lor slack (slack / 2)
  let m2 := z_lor m1 (m1 / 4)
  z_lor m2 (m2 / 16)

/-- The offset (in UNITs) finally used by `enframe`, from the candidate
    `off0` = (`p[-3]` <> 0 ? u16 `p[-2]` + 1 : ctr) mod 256.
    Always `0 <= enframe_off slack off0 <= slack` (RefEnframeArith). -/
def enframe_off (slack off0 : Int) : Int :=
  if off0 ≤ slack then off0
  else let om := z_land off0 (smear slack)
       if slack < om then om - slack - 1 else om

/-- `reserved` = end - p - n for the user pointer `p = start + UNIT*off`;
    the 3-bit code kept in `p[-3]` is `min reserved 5`. -/
def reserved_of (stride n off : Int) : Int := stride - IB - n - UNIT * off

def res_code (reserved : Int) : Int := if reserved < 5 then reserved else 5

/-- In-band u16 "offset" field of the user pointer: `(p - M - 16)/16`. -/
def inband_off (stride idx off : Int) : Int := (stride * idx) / UNIT + off

/-! -/

example : size_class 0 = 1 := by decide
example : size_class 11 = 15 := by decide
example : size_class 47 = 8191 := by decide
example : size_class 48 = 0 := by decide

example : w_lastidx 0 = 0 := by decide
example : w_lastidx 33 = 1 := by decide
example : w_freeable 32 = 1 := by decide
example : w_sizeclass 64 = 1 := by decide
example : w_maplen 4096 = 1 := by decide

-- a packed word's four fields read back (last_idx=1, freeable=1, sizeclass=3,
-- maplen=2: 1 + 32*1 + 64*3 + 4096*2 = 8417)
example : w_lastidx 8417 = 1 := by decide
example : w_freeable 8417 = 1 := by decide
example : w_sizeclass 8417 = 3 := by decide
example : w_maplen 8417 = 2 := by decide

example : slot_stride 1 0 5 = 4080 := by decide
example : slot_stride 0 3 5 = 16 * size_class 5 := by decide

example : slot_start 100 32 2 = 180 := by decide
example : slot_end 100 32 2 = 208 := by decide

example : slack_of 64 16 = 2 := by decide
example : smear 0 = 0 := by decide
example : smear 1 = 1 := by decide
example : smear 4 = 7 := by decide
example : enframe_off 7 3 = 3 := by decide
-- the cycling arm: off0 > slack, masked down by `smear 8 = 15`
example : smear 8 = 15 := by decide
example : enframe_off 8 9 = 0 := by decide
example : reserved_of 64 16 1 = 28 := by decide
example : res_code 3 = 3 := by decide
example : res_code 7 = 5 := by decide
example : inband_off 32 2 3 = 7 := by decide

end LinuxSem.Common.MallocDefs
