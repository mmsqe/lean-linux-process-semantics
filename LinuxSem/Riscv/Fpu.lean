/-
  * Fpu: IEEE-754 binary arithmetic with RISC-V exception flags

  TRUST BOUNDARY: this file is part of the trusted specification.

  `Sem` needs FP operations that return BOTH a result and the five
  IEEE exception flags, because in RISC-V the flags are
  architectural: they accrue into fcsr[4:0], a program can read them
  with `csrr fflags`, and a compiler is free to branch on them.  A
  semantics that produced only the value would be unsound the moment
  a binary looked at fflags.

  The value half is not reinvented here.  Rounding is
  `binaryRoundAux`, the rounding kernel of the Flocq library's
  binary-float development: it takes a sign, an unrounded mantissa,
  an exponent and a LOCATION (where the exact value sits relative to
  the two candidate mantissas), and returns the correctly rounded
  `SpecFloat` — the payload-free IEEE datum of the standard
  library's `SpecFloat`.  Flocq proves that kernel equal to
  real-number rounding, and `round_aux_value` below pins our
  flag-carrying restatement to it definitionally, so the value this
  file computes is exactly the value Flocq's theorem is about.

  The flag half is ours, and it is derived from the same
  intermediate the kernel rounds from:

  - NX (inexact): the location after aligning the operand to the
    target's canonical exponent is not `loc_Exact`.  That is
    literally "some bits were discarded", i.e. the rounded result
    differs from the exact one.
  - OF (overflow): the rounded exponent exceeds `emax - prec`, the
    same test the kernel uses to choose between a finite result and
    `binaryOverflow`.  Overflow always implies NX.  Which of ±inf
    and ±MAXFLOAT comes out is `binaryOverflow`'s business and is
    rounding-mode dependent (RTZ never produces an infinity; RDN/RUP
    produce one only on the side they round away to).
  - UF (underflow): TINY AND INEXACT, with tininess detected AFTER
    rounding — the IEEE option RISC-V mandates.  "After rounding"
    means rounding to `prec` bits AS THOUGH THE EXPONENT RANGE WERE
    UNBOUNDED and asking whether that magnitude stays strictly below
    the smallest normal.  That is NOT the same as "the delivered
    result is subnormal": just below the smallest normal the
    unbounded grid is twice as fine as the subnormal grid, so a
    value in the lower part of that last gap can carry up to the
    smallest normal under the real (bounded) rounding while the
    unbounded-range rounding stays tiny — UF is raised even though
    the delivered result is normal.  `round_tiny` implements the
    unbounded-range rounding.

  RISC-V specifics that this file, not the IEEE kernel, decides:

  - Every NaN RESULT is the canonical quiet NaN (sign 0, exponent
    all ones, mantissa = the quiet bit alone).  RISC-V does not
    propagate payloads, which is why `SpecFloat`'s payload-free
    `S754_nan` is the right datum and why NaN-ness alone is not
    enough state to carry: signalling-ness has to be read off the
    BIT PATTERN before decoding (`is_snan`), since decoding forgets
    it.
  - fmin/fmax return the non-NaN operand when exactly one operand
    is NaN, and raise NV only for a SIGNALLING NaN; −0 is ordered
    below +0, which a bitwise comparison would get wrong.
  - feq is a QUIET compare (NV only on a signalling NaN); flt/fle
    are SIGNALLING (NV on any NaN).

  Everything here is a computation over `Z` on RAW BIT PATTERNS of
  the format's width (32 or 64).  Register width, NaN boxing and
  the fcsr update belong to `Sem`; this file never sees a
  bitvector.

  The Flocq kernel lives in `LinuxSem/Flocq/`.  Two
  representation choices show through here: `spec_float`'s finite
  mantissa is a `Nat` rather than a `positive`, and Lean's `Int` has no
  bitwise operations, so the
  `Z.land`/`Z.lor`/`Z.lxor`/`Z.testbit`/`Z.ones` uses go through the
  `Flocq.Bits` shim (`zland`, `zlxor`, `ztestBit`, `zones`, `ztrunc`).
-/
import LinuxSem.Flocq.SpecFloat
import LinuxSem.Flocq.Bits

namespace LinuxSem.Riscv

open LinuxSem.Flocq

/-! ## Formats

    A binary format is pinned by `prec` (significand bits, including
    the implicit leading one) and `emax` (the exponent of the
    infinities); every other constant is derived, so there is one
    place to look and no way for the two formats to disagree about
    their own layout.  `fp_emin` is the exponent of the SMALLEST
    SUBNORMAL, which is the exponent `SpecFloat` gives every
    subnormal datum — not the smallest normal exponent. -/

/-- A binary interchange format. -/
structure format where
  /-- Significand bits, including the implicit leading one. -/
  fp_prec : Int
  /-- The exponent of the infinities. -/
  fp_emax : Int
  deriving DecidableEq, Repr

/-- Smart constructor `Fmt`. -/
abbrev Fmt (fp_prec fp_emax : Int) : format := ⟨fp_prec, fp_emax⟩

open format

def fmt_single : format := Fmt 24 128
def fmt_double : format := Fmt 53 1024

/-- `Z.log2`: the floor of the base-2 logarithm, `0` on non-positive
  inputs.  Only ever called on `fp_emax`, which is positive. -/
def zlog2 (z : Int) : Int := if z ≤ 0 then 0 else (Nat.log2 z.toNat : Int)

/-- Mantissa field width. -/
def fp_mw (f : format) : Int := fp_prec f - 1
/-- Exponent field width. -/
def fp_ew (f : format) : Int := zlog2 (fp_emax f) + 1
def fp_emin (f : format) : Int := 3 - fp_emax f - fp_prec f

/-! ## Exception flags

    The five IEEE flags, in the fcsr[4:0] bit order RISC-V assigns
    them.  Kept as a record rather than a bitmask so that every
    operation below has to name the flags it raises; `fflags_bits` is
    the single place the encoding is spelled. -/

structure fflags where
  /-- Invalid operation. -/
  fl_nv : Bool
  /-- Divide by zero. -/
  fl_dz : Bool
  /-- Overflow. -/
  fl_of : Bool
  /-- Underflow. -/
  fl_uf : Bool
  /-- Inexact. -/
  fl_nx : Bool
  deriving DecidableEq, Repr

/-- Smart constructor `Fflags`. -/
abbrev Fflags (nv dz of_ uf nx : Bool) : fflags := ⟨nv, dz, of_, uf, nx⟩

def no_flags : fflags := Fflags false false false false false
def nv_flag : fflags := Fflags true false false false false
def dz_flag : fflags := Fflags false true false false false
def nx_flag : fflags := Fflags false false false false true

def fflags_bits (fl : fflags) : Int :=
  let b (p : Bool) (i : Int) : Int := if p then (1 : Int) <<< i.toNat else 0
  b (fl.fl_nx) 0 + b (fl.fl_uf) 1 + b (fl.fl_of) 2
  + b (fl.fl_dz) 3 + b (fl.fl_nv) 4

/-! ## Rounding modes

    The five architectural modes.  The instruction's 3-bit rm field
    also has the DYNAMIC encoding 7 (use fcsr's frm) and two RESERVED
    encodings, 5 and 6; `rmode_of_field` returns `none` for those, and
    for a dynamic rm whose frm is itself reserved.  `none` is an
    ILLEGAL INSTRUCTION at the `Sem` level, not a defaulted mode:
    executing a reserved rounding mode as if it were round-to-nearest
    would give a wrong answer silently, where trapping is what real
    hardware does. -/

inductive rmode : Type
  | RNE | RTZ | RDN | RUP | RMM
  deriving DecidableEq, Repr

def rmode_of_Z (z : Int) : Option rmode :=
  if z == 0 then some .RNE
  else if z == 1 then some .RTZ
  else if z == 2 then some .RDN
  else if z == 3 then some .RUP
  else if z == 4 then some .RMM
  else none

/-- `rm` is the instruction field, `frm` the fcsr rounding mode. -/
def rmode_of_field (rm frm : Int) : Option rmode :=
  if rm == 7 then rmode_of_Z frm else rmode_of_Z rm

def flocq_mode (m : rmode) : Mode :=
  match m with
  | .RNE => .NE
  | .RTZ => .ZR
  | .RDN => .DN
  | .RUP => .UP
  | .RMM => .NA

/-! ## Bit patterns

    Decode and encode the interchange format by hand: the standard
    library's `spec_float` is an abstract datum with no layout, and
    the layout is exactly what an ISA semantics has to be explicit
    about.  `Pos.size` is the number of significant bits of a
    positive, which is how a subnormal RESULT is recognized on the way
    out (fewer than `prec` significant bits, which for a canonical
    datum can only happen at the minimum exponent). -/

def fp_sign_bit (f : format) (x : Int) : Bool :=
  ztestBit x (fp_mw f + fp_ew f).toNat

def fp_exp_field (f : format) (x : Int) : Int :=
  zland (x >>> (fp_mw f).toNat) (zones (fp_ew f))

def fp_man_field (f : format) (x : Int) : Int :=
  zland x (zones (fp_mw f))

def fp_decode (f : format) (x : Int) : SpecFloat :=
  let s := fp_sign_bit f x
  let e := fp_exp_field f x
  let m := fp_man_field f x
  if e == 0 then
    (if m > 0 then .finite s m.toNat (fp_emin f)
     else .zero s)
  else if e == zones (fp_ew f) then
    (if m == 0 then .infinity s else .nan)
  else
    let t := ((1 : Int) <<< (fp_mw f).toNat) + m
    (if t > 0 then .finite s t.toNat (e + fp_emin f - 1)
     else .nan)   -- unreachable: the implicit bit makes this positive

/-- The one NaN this semantics ever produces. -/
def fp_canonical_nan (f : format) : Int :=
  (zones (fp_ew f) <<< (fp_mw f).toNat) + ((1 : Int) <<< (fp_mw f - 1).toNat)

def fp_encode (f : format) (x : SpecFloat) : Int :=
  let sb (s : Bool) : Int := if s then (1 : Int) <<< (fp_mw f + fp_ew f).toNat else 0
  match x with
  | .nan => fp_canonical_nan f
  | .zero s => sb s
  | .infinity s => sb s + (zones (fp_ew f) <<< (fp_mw f).toNat)
  | .finite s m e =>
      if (digits2Pos m : Int) < fp_prec f
      then sb s + (m : Int)                                   -- subnormal
      else sb s + ((e - fp_emin f + 1) <<< (fp_mw f).toNat)
           + ((m : Int) - ((1 : Int) <<< (fp_mw f).toNat))

/-- A signalling NaN is a NaN whose leading mantissa bit is CLEAR.
    Read off the bit pattern, because `fp_decode` collapses every NaN
    to `S754_nan` and the distinction only matters for raising NV. -/
def fp_is_snan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == zones (fp_ew f))
    && (!(fp_man_field f x == 0)
        && !(ztestBit x (fp_mw f - 1).toNat))

def fp_is_nan (f : format) (x : Int) : Bool :=
  (fp_exp_field f x == zones (fp_ew f))
    && (!(fp_man_field f x == 0))

/-- Flip the sign bit — the negation fused-multiply-add's variants and
    fsub are defined by, and NOT an arithmetic negation: it leaves
    NaN-ness and signalling-ness alone, which is what makes
    `fp_sub`-as-`fp_add`-of-a-negated-operand raise exactly the flags
    a native subtraction would. -/
def fp_neg (f : format) (x : Int) : Int :=
  zlxor x ((1 : Int) <<< (fp_mw f + fp_ew f).toNat)

/-! ## The rounding kernel, with flags

    The body is `binaryRoundAux`'s, with the
    intermediate location and exponent kept instead of discarded:
    `l1` (the location after aligning `mx` to the canonical exponent)
    IS inexactness, and `e2` against `emax - prec` IS overflow.  The
    second `shr_fexp` is the carry-out normalization for the case
    where rounding up overflowed the mantissa; it is exact, so it
    cannot change `l1`.

    `round_aux_value` states the coincidence with Flocq's kernel, so
    a reader can check the value against Flocq's correctness theorem
    without re-reading this body. -/

def mk_round_flags (of_ uf nx : Bool) : fflags :=
  Fflags false false of_ uf nx

/-- Tininess detected after rounding: round the SAME intermediate to
    `prec` bits as though the exponent range were unbounded — the
    target exponent is `digits − prec` below the operand's, with no
    `emin` floor — and the value is tiny when that magnitude ends up
    strictly below the smallest normal, 2^(emin + prec − 1).  The
    magnitude comparison reads off the rounded mantissa's digit count:
    m·2^e < 2^k for a canonical (or carried, `prec`+1-digit) mantissa
    exactly when digits(m) + e ≤ k.

    The operand contract is `round_aux`'s own: an inexact location
    only ever arrives on a mantissa of at least `prec` digits (the
    div/sqrt cores construct that many; exact operands carry
    `loc_Exact`), so the right shift below never has to invent bits it
    cannot see. -/
def round_tiny (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : Location) : Bool :=
  let (mrs, e') := shr (shrRecordOfLoc mx lx) ex (Zdigits2 mx - fp_prec f)
  let m' := choiceMode (flocq_mode md) sx mrs.m (locOfShrRecord mrs)
  decide (Zdigits2 m' + e' ≤ fp_emin f + fp_prec f - 1)

def round_aux (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : Location) : SpecFloat × fflags :=
  -- The format parameters are written out in full (`fp_prec f`,
  -- `fp_emax f`) at each use rather than bound to locals first, so that
  -- this body is syntactically the rounding kernel's — which is what
  -- lets `round_aux_value` line the two up node by node.
  let (mrs1, e1) := shrFexp (fp_prec f) (fp_emax f) mx ex lx
  let l1 := locOfShrRecord mrs1
  let nx := match l1 with
            | .exact => false
            | _ => true
  let (mrs2, e2) :=
    shrFexp (fp_prec f) (fp_emax f)
      (choiceMode (flocq_mode md) sx mrs1.m l1) e1 .exact
  match mrs2.m with
  | 0 => (.zero sx, mk_round_flags false nx nx)
  | mz =>
      if mz > 0 then
        (if e2 ≤ fp_emax f - fp_prec f
         then (.finite sx mz.toNat e2,
               mk_round_flags false (nx && round_tiny f md sx mx ex lx) nx)
         else (binaryOverflow (fp_prec f) (fp_emax f) (flocq_mode md) sx,
               mk_round_flags true false true))
      else (.nan, no_flags)   -- unreachable: mantissas are non-negative

/-- `round_aux`'s kernel can only shift a mantissa RIGHT, so it
    assumes the operand is already at or below the target's canonical
    exponent.  Products, quotients and square roots arrive that way by
    construction, but an EXACT operand need not: a cancelling sum
    (1 − (1 − 2^-52)) or a widening conversion (a single-precision
    datum read in double precision) has far fewer significant bits
    than the format's precision at an exponent well above the minimum.
    Left-aligning first (`shl_align` to the canonical exponent, which
    is a no-op when the operand is already canonical) is what keeps
    the RESULT canonical — and the result's canonicity is exactly what
    `fp_encode` reads to tell a subnormal from a normal. -/
def round_exact (f : format) (md : rmode) (sx : Bool)
    (mx : Nat) (ex : Int) : SpecFloat × fflags :=
  let (mz, ez) :=
    shlAlign (mx : Int) ex (fexp (fp_prec f) (fp_emax f)
                              ((digits2Pos mx : Int) + ex))
  round_aux f md sx mz ez .exact

/-- `round_aux`'s value half is exactly Flocq's `binary_round_aux`:
    the flags ride along in the second component, the rounding path is
    untouched. -/
theorem round_aux_value (f : format) (md : rmode) (sx : Bool)
    (mx ex : Int) (lx : Location) :
    (round_aux f md sx mx ex lx).1
      = binaryRoundAux (fp_prec f) (fp_emax f) (flocq_mode md)
          sx mx ex lx := by
  unfold round_aux binaryRoundAux binaryFitAux
  dsimp only
  -- The two `shrFexp` nodes are shared by both sides; case on them once
  -- so that the `let`-bound pairs reduce in both at the same time, and
  -- then the only discrimination left is the sign/overflow dispatch.
  cases h1 : shrFexp (fp_prec f) (fp_emax f) mx ex lx with
  | mk mrs1 e1 =>
    cases h2 : shrFexp (fp_prec f) (fp_emax f)
        (choiceMode (flocq_mode md) sx mrs1.m (locOfShrRecord mrs1)) e1 .exact with
    | mk mrs2 e2 =>
      dsimp only
      -- What is left is the sign/zero/overflow dispatch, on both sides
      -- and over the same `mrs2.m` and `e2`; split it to the leaves,
      -- where the value component is the kernel's expression verbatim.
      repeat first | rfl | split
      all_goals simp_all
      all_goals split
      all_goals first | rfl | (split <;> rfl)

/-! ## Exact operands as scaled integers

    Addition and fused multiply-add both need the EXACT sum of two
    scaled integers before any rounding happens.  Representing a
    finite datum as (signed mantissa, exponent) and aligning to the
    smaller exponent makes that a single integer addition; zero is
    (0, 0), which is the additive unit and so needs no case of its
    own.  The alignment shift is bounded by the format's exponent
    range (about 2100 bits for binary64), so the intermediate is a
    bignum but a small one. -/

def sf_scaled (x : SpecFloat) : Int × Int :=
  match x with
  | .finite s m e => ((if s then -((m : Int)) else (m : Int)), e)
  | _ => (0, 0)

def scaled_add (a b : Int × Int) : Int × Int :=
  let (ma, ea) := a
  let (mb, eb) := b
  let e := min ea eb
  ((ma <<< (ea - e).toNat) + (mb <<< (eb - e).toNat), e)

def sf_sign (x : SpecFloat) : Bool :=
  match x with
  | .zero s | .infinity s | .finite s _ _ => s
  | .nan => false

/-- The sign of an EXACTLY ZERO sum.  IEEE: when two operands of
    opposite sign cancel exactly the result is +0, except under
    round-toward-negative where it is −0; when the signs agree the
    result keeps that sign (so −0 + −0 = −0, and x + x keeps x's sign
    even at zero). -/
def zero_sign (md : rmode) (sa sb : Bool) : Bool :=
  if (sa == sb) then sa
  else match md with
       | .RDN => true
       | _ => false

/-- Round an exact scaled integer, using `szero` for the sign of a
    zero result (the kernel's sign argument is the sign of a NONZERO
    value, so a cancelling sum has to supply its own). -/
def round_scaled (f : format) (md : rmode) (szero : Bool)
    (v : Int × Int) : SpecFloat × fflags :=
  let (m, e) := v
  match m with
  | 0 => (.zero szero, no_flags)
  | _ => if m > 0 then round_exact f md false m.toNat e
         else round_exact f md true m.natAbs e

/-! ## NaN pre-pass

    Every arithmetic operation starts the same way: a signalling NaN
    operand raises NV, any NaN operand makes the result the canonical
    NaN, and only then do the infinity/zero special cases matter.
    Factoring it out keeps each operation's own dispatch to the cases
    that are actually about that operation. -/

def nan_pass1 (f : format) (a : Int) : Option (Int × fflags) :=
  if fp_is_nan f a
  then some (fp_canonical_nan f,
             if fp_is_snan f a then nv_flag else no_flags)
  else none

def nan_pass2 (f : format) (a b : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || fp_is_nan f b
  then some (fp_canonical_nan f,
             if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)
  else none

def nan_pass3 (f : format) (a b c : Int) : Option (Int × fflags) :=
  if fp_is_nan f a || fp_is_nan f b || fp_is_nan f c
  then some (fp_canonical_nan f,
             if fp_is_snan f a || fp_is_snan f b || fp_is_snan f c
             then nv_flag else no_flags)
  else none

def enc (f : format) (r : SpecFloat × fflags) : Int × fflags :=
  (fp_encode f r.1, r.2)

/-! ## Addition, subtraction, multiplication, division, square root -/

def fp_add (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    let x := fp_decode f a
    let y := fp_decode f b
    match x, y with
    | .infinity sa, .infinity sb =>
        (if (sa == sb)
         then (fp_encode f (.infinity sa), no_flags)
         else (fp_canonical_nan f, nv_flag))   -- inf − inf
    | .infinity sa, _ => (fp_encode f (.infinity sa), no_flags)
    | _, .infinity sb => (fp_encode f (.infinity sb), no_flags)
    | _, _ =>
        enc f (round_scaled f md (zero_sign md (sf_sign x) (sf_sign y))
                            (scaled_add (sf_scaled x) (sf_scaled y)))

/-- Subtraction is addition of the sign-flipped operand: `fp_neg` is a
    bit flip, so it changes neither NaN-ness nor signalling-ness, and
    the zero-sign rule then reads correctly off the flipped sign
    (x − x = +0 except under RDN; −0 − +0 = −0). -/
def fp_sub (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  fp_add f md a (fp_neg f b)

def fp_mul (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | .infinity _, .zero _ => (fp_canonical_nan f, nv_flag)   -- 0 × inf
    | .zero _, .infinity _ => (fp_canonical_nan f, nv_flag)
    | .infinity sa, y => (fp_encode f (.infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, .infinity sb => (fp_encode f (.infinity (Bool.xor (sf_sign x) sb)), no_flags)
    | .zero sa, y => (fp_encode f (.zero (Bool.xor sa (sf_sign y))), no_flags)
    | x, .zero sb => (fp_encode f (.zero (Bool.xor (sf_sign x) sb)), no_flags)
    | .finite sa ma ea, .finite sb mb eb =>
        enc f (round_exact f md (Bool.xor sa sb) (ma * mb) (ea + eb))
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable: NaNs handled above

def fp_div (f : format) (md : rmode) (a b : Int) : Int × fflags :=
  match nan_pass2 f a b with
  | some r => r
  | none =>
    match fp_decode f a, fp_decode f b with
    | .infinity _, .infinity _ => (fp_canonical_nan f, nv_flag)
    | .zero _, .zero _ => (fp_canonical_nan f, nv_flag)
    | .infinity sa, y => (fp_encode f (.infinity (Bool.xor sa (sf_sign y))), no_flags)
    | x, .infinity sb => (fp_encode f (.zero (Bool.xor (sf_sign x) sb)), no_flags)
    | .zero sa, y => (fp_encode f (.zero (Bool.xor sa (sf_sign y))), no_flags)
    -- finite nonzero / zero: the only divide-by-zero there is
    | x, .zero sb => (fp_encode f (.infinity (Bool.xor (sf_sign x) sb)), dz_flag)
    | .finite sa ma ea, .finite sb mb eb =>
        let (mz, ez, lz) :=
          SFdivCoreBinary (fp_prec f) (fp_emax f) ((ma : Int)) ea ((mb : Int)) eb
        enc f (round_aux f md (Bool.xor sa sb) mz ez lz)
    | _, _ => (fp_canonical_nan f, no_flags)  -- unreachable

/-- sqrt(−0) is −0, not an invalid operation: IEEE makes the negative
    ZERO the one negative input with a result. -/
def fp_sqrt (f : format) (md : rmode) (a : Int) : Int × fflags :=
  match nan_pass1 f a with
  | some r => r
  | none =>
    match fp_decode f a with
    | .zero s => (fp_encode f (.zero s), no_flags)
    | .infinity false => (fp_encode f (.infinity false), no_flags)
    | .infinity true => (fp_canonical_nan f, nv_flag)
    | .finite true _ _ => (fp_canonical_nan f, nv_flag)
    | .finite false m e =>
        let (mz, ez, lz) := SFsqrtCoreBinary (fp_prec f) (fp_emax f) ((m : Int)) e
        enc f (round_aux f md false mz ez lz)
    | .nan => (fp_canonical_nan f, no_flags)  -- unreachable

/-! ## Fused multiply-add

    FUSED: the product is not rounded before the addend is applied, so
    the exact product's mantissa and the addend are summed as scaled
    integers and rounded ONCE.  That is the whole point of the
    instruction and the only reason it cannot be composed from
    `fp_mul` and `fp_add`.

    An invalid product (0 × inf) raises NV even when the addend is a
    quiet NaN — the product is examined first, per IEEE's
    fusedMultiplyAdd. -/

def fp_fma (f : format) (md : rmode) (a b c : Int) : Int × fflags :=
  let x := fp_decode f a
  let y := fp_decode f b
  let prod_invalid :=
    match x, y with
    | .infinity _, .zero _ => true
    | .zero _, .infinity _ => true
    | _, _ => false
  if prod_invalid && !(fp_is_nan f a || fp_is_nan f b)
  then (fp_canonical_nan f, nv_flag)
  else
  match nan_pass3 f a b c with
  | some r => r
  | none =>
    let z := fp_decode f c
    let sp := Bool.xor (sf_sign x) (sf_sign y)
    match x, y with
    -- An infinite product: the addend can only make it invalid.
    | .infinity _, _ =>
        match z with
        | .infinity sz =>
            (if (sp == sz)
             then (fp_encode f (.infinity sp), no_flags)
             else (fp_canonical_nan f, nv_flag))
        | _ => (fp_encode f (.infinity sp), no_flags)
    | _, .infinity _ =>
        match z with
        | .infinity sz =>
            (if (sp == sz)
             then (fp_encode f (.infinity sp), no_flags)
             else (fp_canonical_nan f, nv_flag))
        | _ => (fp_encode f (.infinity sp), no_flags)
    | .finite _ ma ea, .finite _ mb eb =>
        -- A finite product plus an INFINITE addend is that infinity;
        -- `sf_scaled` maps every non-finite datum to 0, so without
        -- this case the addend would silently vanish.
        match z with
        | .infinity sz => (fp_encode f (.infinity sz), no_flags)
        | _ =>
          let prod := ((if sp then -(((ma * mb : Nat)) : Int)
                       else (((ma * mb : Nat)) : Int)), ea + eb)
          enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                              (scaled_add prod (sf_scaled z)))
    -- A zero product: the sum is the addend, but the ZERO SIGN still
    -- follows the product's sign when the addend is zero too.
    | _, _ =>
        match z with
        | .infinity sz => (fp_encode f (.infinity sz), no_flags)
        | _ => enc f (round_scaled f md (zero_sign md sp (sf_sign z))
                                   (sf_scaled z))

/-! ## Comparisons, min/max, classification -/

/-- `none` is "unordered", i.e. a NaN operand. -/
def fp_compare (f : format) (a b : Int) : Option Ordering :=
  SFcompare (fp_decode f a) (fp_decode f b)

/-- feq is QUIET: only a signalling NaN raises NV.  flt/fle are
    SIGNALLING: any NaN raises it.  All three answer false when
    unordered. -/
def fp_eq (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with
    | some .eq => true
    | _ => false),
   if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags)

def fp_lt (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with
    | some .lt => true
    | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

def fp_le (f : format) (a b : Int) : Bool × fflags :=
  ((match fp_compare f a b with
    | some .lt => true
    | some .eq => true
    | _ => false),
   if fp_is_nan f a || fp_is_nan f b then nv_flag else no_flags)

/-- fmin/fmax.  Three RISC-V rules a naive `fp_compare` would miss:
    one NaN operand yields the OTHER operand (both NaN yields the
    canonical NaN), NV is raised only for a SIGNALLING NaN, and −0 is
    strictly less than +0 even though `SFcompare` calls them equal —
    so the equal case is decided on the sign bits. -/
def fp_minmax (f : format) (is_max : Bool) (a b : Int) : Int × fflags :=
  let fl := if fp_is_snan f a || fp_is_snan f b then nv_flag else no_flags
  if fp_is_nan f a && fp_is_nan f b then (fp_canonical_nan f, fl)
  else if fp_is_nan f a then (b, fl)
  else if fp_is_nan f b then (a, fl)
  else
    let a_lt_b :=
      match fp_compare f a b with
      | some .lt => true
      | some .eq => fp_sign_bit f a && !(fp_sign_bit f b)
      | _ => false
    ((if Bool.xor is_max a_lt_b then a else b), fl)

/-- The fclass bit mask: bit 0 −inf, 1 −normal, 2 −subnormal, 3 −0,
    4 +0, 5 +subnormal, 6 +normal, 7 +inf, 8 sNaN, 9 qNaN. -/
def fp_class (f : format) (a : Int) : Int :=
  let s := fp_sign_bit f a
  let e := fp_exp_field f a
  let m := fp_man_field f a
  if e == zones (fp_ew f) then
    (if m == 0 then (if s then 1 else (1 : Int) <<< 7)
     else if fp_is_snan f a then (1 : Int) <<< 8 else (1 : Int) <<< 9)
  else if e == 0 then
    (if m == 0 then (if s then (1 : Int) <<< 3 else (1 : Int) <<< 4)
     else if s then (1 : Int) <<< 2 else (1 : Int) <<< 5)
  else (if s then (1 : Int) <<< 1 else (1 : Int) <<< 6)

/-! ## Conversions

    float → integer.  `bits` is the integer width (32 or 64) and
    `signed` its signedness; the answer is the RAW two's-complement
    value in that width, which `Sem` sign-extends into the 64-bit
    destination register (RISC-V sign-extends fcvt.wu's unsigned
    result too).

    Saturation, not wraparound: an out-of-range magnitude, an
    infinity or a NaN gives the nearest representable integer and
    raises NV.  A NaN gives the MAXIMUM in both signednesses.  NV
    suppresses NX, so a saturated conversion reports exactly one
    exception. -/

def int_lo (signed : Bool) (bits : Int) : Int :=
  if signed then -((1 : Int) <<< (bits - 1).toNat) else 0

def int_hi (signed : Bool) (bits : Int) : Int :=
  if signed then ((1 : Int) <<< (bits - 1).toNat) - 1
  else ((1 : Int) <<< bits.toNat) - 1

/-- Two's-complement image of `v` in `bits` bits. -/
def int_wrap (bits v : Int) : Int := ztrunc bits v

def fp_to_int (f : format) (md : rmode) (signed : Bool) (bits : Int)
    (a : Int) : Int × fflags :=
  let sat (v : Int) : Int × fflags := (int_wrap bits v, nv_flag)
  if fp_is_nan f a then sat (int_hi signed bits)
  else
    match fp_decode f a with
    | .infinity s => sat (if s then int_lo signed bits else int_hi signed bits)
    | .zero _ => (0, no_flags)
    | .nan => sat (int_hi signed bits)   -- unreachable
    | .finite s m e =>
        -- Split the scaled mantissa at the binary point: `q` is the
        -- truncated magnitude, `l` says where the discarded part sits
        -- between `q` and `q+1`, and `choice_mode` applies the
        -- rounding rule to the MAGNITUDE with the sign supplied
        -- separately — the same convention the FP kernel uses.
        let (q, l) :=
          if 0 ≤ e then (((m : Int) <<< e.toNat), Location.exact)
          else
            let d := (1 : Int) <<< (-e).toNat
            let (q, r) := (Int.ediv ((m : Int)) d, Int.emod ((m : Int)) d)
            (q, newLocation d r)
        let q' := choiceMode (flocq_mode md) s q l
        let v := if s then -q' else q'
        if v < int_lo signed bits || int_hi signed bits < v
        then sat (if s then int_lo signed bits else int_hi signed bits)
        else (int_wrap bits v,
              match l with
              | .exact => no_flags
              | _ => nx_flag)

/-- integer → float.  `v` is the raw `bits`-wide value from the
    source register, read with the requested signedness before
    rounding. -/
def fp_of_int (f : format) (md : rmode) (signed : Bool) (bits : Int)
    (v : Int) : Int × fflags :=
  let u := int_wrap bits v
  let n := if signed && ztestBit u (bits - 1).toNat
           then u - ((1 : Int) <<< bits.toNat) else u
  enc f (round_scaled f md false (n, 0))

/-- float → float.  Widening is exact; narrowing rounds and can
    overflow or underflow, so both directions go through the same
    kernel and the flags fall out.  A NaN converts to the
    DESTINATION's canonical NaN, and a signalling one raises NV. -/
def fp_convert (src dst : format) (md : rmode) (a : Int) : Int × fflags :=
  if fp_is_nan src a
  then (fp_canonical_nan dst, if fp_is_snan src a then nv_flag else no_flags)
  else
    match fp_decode src a with
    | .zero s => (fp_encode dst (.zero s), no_flags)
    | .infinity s => (fp_encode dst (.infinity s), no_flags)
    | .nan => (fp_canonical_nan dst, no_flags)   -- unreachable
    | .finite s m e => enc dst (round_exact dst md s m e)

/-! ## Sanity checks

    Concrete vectors, evaluated by the kernel.  These pin the encoding,
    the rounding kernel and the flag story end to end. -/

/-- 1.0 + 1.0 = 2.0 -/
example : fp_add fmt_single .RNE 0x3F800000 0x3F800000
    = (0x40000000, no_flags) := by decide

/-- 2.0 * 2.0 = 4.0 -/
example : fp_mul fmt_single .RNE 0x40000000 0x40000000
    = (0x40800000, no_flags) := by decide

/-- 1.0 / 2.0 = 0.5 -/
example : fp_div fmt_single .RNE 0x3F800000 0x40000000
    = (0x3F000000, no_flags) := by decide

/-- 1.0 − 1.0 = +0.0 -/
example : fp_sub fmt_single .RNE 0x3F800000 0x3F800000
    = (0, no_flags) := by decide

/-- π, truncated toward zero, is 3 — and inexact. -/
example : fp_to_int fmt_single .RTZ true 32 0x40490FDB
    = (3, nx_flag) := by decide

/-- Some more single-precision special cases: overflow to infinity,
    division by zero, 0 × inf, a fused multiply-add, sqrt of a perfect
    square, the signed-zero ordering of fmin, fclass, a widening
    conversion and a NaN → integer saturation. -/
example : fp_mul fmt_single .RNE 0x7F7FFFFF 0x40000000
    = (0x7F800000, Fflags false false true false true) := by decide
example : fp_div fmt_single .RNE 0x3F800000 0
    = (0x7F800000, dz_flag) := by decide
example : fp_mul fmt_single .RNE 0 0x7F800000
    = (0x7FC00000, nv_flag) := by decide
example : fp_fma fmt_single .RNE 0x40000000 0x40400000 0x3F800000
    = (0x40E00000, no_flags) := by decide
example : fp_sqrt fmt_single .RNE 0x40800000
    = (0x40000000, no_flags) := by decide
example : fp_minmax fmt_single false 0x80000000 0
    = (0x80000000, no_flags) := by decide
example : fp_class fmt_single 0x7FC00000 = 512 := by decide
example : fp_convert fmt_single fmt_double .RNE 0x3F800000
    = (0x3FF0000000000000, no_flags) := by decide
example : fp_to_int fmt_single .RTZ true 32 0x7FC00000
    = (0x7FFFFFFF, nv_flag) := by decide

/-! ### Vectors from `FpuTests`

  The conformance table of `FpuTests.lean`, restricted to the
  `Fpu`-level entries (the `Sem`-level ones need `Sem`).  These are the cases a
    reader is most likely to want to check by hand: rounding at a tie,
    the boundary where UNDERFLOW switches on, tininess detected after
    rounding, overflow, saturation, NaN canonicalization and fclass.

    The binary64 entries need a deeper elaborator recursion budget than
    the default: the computations are small, but `Decidable` search
    through the `Int` kernel is deep. -/

section vectors

set_option maxRecDepth 100000

/-- Rounding-mode resolution: `rm` 0..4 are the modes, 5 and 6 are
    reserved, 7 is DYNAMIC (read `frm`), and a reserved `frm` is
    reserved too. -/
example : rmode_of_field 0 0 = some .RNE := by decide
example : rmode_of_field 7 2 = some .RDN := by decide
example : rmode_of_field 5 0 = none := by decide
example : rmode_of_field 6 0 = none := by decide
example : rmode_of_field 7 5 = none := by decide

/-- 1.0 / 3.0 is inexact, and RUP goes the other way from RTZ. -/
example : fp_div fmt_double .RNE 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555555, nx_flag) := by decide
example : fp_div fmt_double .RTZ 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555555, nx_flag) := by decide
example : fp_div fmt_double .RUP 0x3ff0000000000000 0x4008000000000000
    = (0x3fd5555555555556, nx_flag) := by decide

/-- A tie under RNE goes to the EVEN mantissa, under RMM away from zero. -/
example : fp_add fmt_double .RNE 0x4340000000000000 0x3ff0000000000000
    = (0x4340000000000000, nx_flag) := by decide
example : fp_add fmt_double .RMM 0x4340000000000000 0x3ff0000000000000
    = (0x4340000000000001, nx_flag) := by decide

/-- Overflow: RNE produces +inf, RTZ/RDN produce +MAXFLOAT; both raise
    OF and NX. -/
example : fp_mul fmt_double .RNE 0x7fefffffffffffff 0x4000000000000000
    = (0x7ff0000000000000, Fflags false false true false true) := by decide
example : fp_mul fmt_double .RTZ 0x7fefffffffffffff 0x4000000000000000
    = (0x7fefffffffffffff, Fflags false false true false true) := by decide
example : fp_mul fmt_double .RDN 0x7fefffffffffffff 0x4000000000000000
    = (0x7fefffffffffffff, Fflags false false true false true) := by decide

/-- Underflow is TINY AND INEXACT: halving the smallest normal is exact
    (no flag), halving the smallest subnormal is not (UF+NX). -/
example : fp_div fmt_double .RNE 0x0010000000000000 0x4000000000000000
    = (0x0008000000000000, no_flags) := by decide
example : fp_div fmt_double .RNE 0x0000000000000001 0x4000000000000000
    = (0x0000000000000000, Fflags false false false true true) := by decide

/-- Tininess is detected AFTER ROUNDING: the delivered result can be
    normal and still be flagged UF. -/
example : fp_mul fmt_double .RNE 0x0010000000000000 0x3fefffffffffffff
    = (0x0010000000000000, Fflags false false false true true) := by decide
example : fp_mul fmt_double .RTZ 0x0010000000000000 0x3fefffffffffffff
    = (0x000fffffffffffff, Fflags false false false true true) := by decide
example : fp_mul fmt_double .RNE 0x1ffffffffc000000 0x2000000002000000
    = (0x0010000000000000, nx_flag) := by decide

/-- The same boundary through the fused path (fmsub.s under RDN). -/
example : fp_fma fmt_single .RDN 0x3f7ffffd 0x80400000 0x80400000
    = (0x80800000, Fflags false false false true true) := by decide
example : fp_fma fmt_single .RDN 0x3f7ffffd 0x80200000 0x80600000
    = (0x80800000, nx_flag) := by decide

/-- Invalid operations and divide by zero. -/
example : fp_add fmt_double .RNE 0x7ff0000000000000 0xfff0000000000000
    = (0x7ff8000000000000, nv_flag) := by decide
example : fp_mul fmt_double .RNE 0 0x7ff0000000000000
    = (0x7ff8000000000000, nv_flag) := by decide
example : fp_div fmt_double .RNE 0x3ff0000000000000 0
    = (0x7ff0000000000000, dz_flag) := by decide
example : fp_div fmt_double .RNE 0 0
    = (0x7ff8000000000000, nv_flag) := by decide
example : fp_sqrt fmt_double .RNE 0xbff0000000000000
    = (0x7ff8000000000000, nv_flag) := by decide
example : fp_sqrt fmt_double .RNE 0x8000000000000000
    = (0x8000000000000000, no_flags) := by decide

/-- NaN propagation: the canonical NaN comes back, payloads never
    survive, and only a signalling NaN raises NV. -/
example : fp_add fmt_double .RNE 0x7ffc000000000000 0x3ff0000000000000
    = (0x7ff8000000000000, no_flags) := by decide
example : fp_add fmt_double .RNE 0x7ff4000000000000 0x3ff0000000000000
    = (0x7ff8000000000000, nv_flag) := by decide

/-- feq is quiet, flt is signalling; the zeros compare EQUAL. -/
example : fp_eq fmt_double 0x7ff8000000000000 0x3ff0000000000000
    = (false, no_flags) := by decide
example : fp_lt fmt_double 0x7ff8000000000000 0x3ff0000000000000
    = (false, nv_flag) := by decide
example : fp_eq fmt_double 0x8000000000000000 0
    = (true, no_flags) := by decide

/-- fmin/fmax: one NaN yields the other operand, both NaN yields the
    canonical NaN, −0 is strictly below +0. -/
example : fp_minmax fmt_double false 0x7ff8000000000000 0x3ff0000000000000
    = (0x3ff0000000000000, no_flags) := by decide
example : fp_minmax fmt_double true 0x7ff0000000000001 0x3ff0000000000000
    = (0x3ff0000000000000, nv_flag) := by decide
example : fp_minmax fmt_double false 0x7ff8000000000000 0x7ff8000000000000
    = (0x7ff8000000000000, no_flags) := by decide
example : fp_minmax fmt_double false 0x8000000000000000 0
    = (0x8000000000000000, no_flags) := by decide
example : fp_minmax fmt_double true 0x8000000000000000 0
    = (0, no_flags) := by decide

/-- float → int saturates, a NaN gives the MAXIMUM, and NV suppresses
    NX. -/
example : fp_to_int fmt_double .RTZ true 32 0x400d999999999999
    = (3, nx_flag) := by decide
example : fp_to_int fmt_double .RTZ true 32 0x4008000000000000
    = (3, no_flags) := by decide
example : fp_to_int fmt_double .RTZ true 32 0x41e0000000000000
    = (0x7fffffff, nv_flag) := by decide
example : fp_to_int fmt_double .RTZ true 32 0xc1e0000000000001
    = (0x80000000, nx_flag) := by decide
example : fp_to_int fmt_double .RTZ true 32 0xc1e0000000200000
    = (0x80000000, nv_flag) := by decide
example : fp_to_int fmt_double .RTZ true 32 0x7ff8000000000000
    = (0x7fffffff, nv_flag) := by decide
example : fp_to_int fmt_double .RTZ false 32 0x7ff8000000000000
    = (0xffffffff, nv_flag) := by decide
example : fp_to_int fmt_double .RTZ false 64 0xbff0000000000000
    = (0, nv_flag) := by decide
example : fp_to_int fmt_double .RTZ false 32 0xbfe0000000000000
    = (0, nx_flag) := by decide

/-- int → float and float → float. -/
example : fp_of_int fmt_double .RNE true 64 12345
    = (0x40c81c8000000000, no_flags) := by decide
example : fp_of_int fmt_double .RNE true 64 9007199254740993
    = (0x4340000000000000, nx_flag) := by decide
example : fp_convert fmt_single fmt_double .RNE 0x3f800000
    = (0x3ff0000000000000, no_flags) := by decide
example : fp_convert fmt_double fmt_single .RNE 0x3fd5555555555555
    = (0x3eaaaaab, nx_flag) := by decide
example : fp_convert fmt_double fmt_single .RNE 0x7ff0000000000001
    = (0x7fc00000, nv_flag) := by decide

/-- fclass: one bit per class. -/
example : fp_class fmt_double 0xfff0000000000000 = 1 := by decide
example : fp_class fmt_double 0xbff0000000000000 = 2 := by decide
example : fp_class fmt_double 0x8000000000000001 = 4 := by decide
example : fp_class fmt_double 0x8000000000000000 = 8 := by decide
example : fp_class fmt_double 0 = 16 := by decide
example : fp_class fmt_double 0x0000000000000001 = 32 := by decide
example : fp_class fmt_double 0x3ff0000000000000 = 64 := by decide
example : fp_class fmt_double 0x7ff0000000000000 = 128 := by decide
example : fp_class fmt_double 0x7ff0000000000001 = 256 := by decide
example : fp_class fmt_double 0x7ff8000000000000 = 512 := by decide

end vectors

end LinuxSem.Riscv
