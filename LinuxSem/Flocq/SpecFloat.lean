/-
  * SpecFloat — the IEEE-754 rounding kernel, in Lean 4.

  PROVENANCE AND LICENSE.  The definitions in this file are translated from
  Rocq's `theories/Floats/SpecFloat.v` (the Rocq standard library, LGPL-2.1)
  and from Flocq's `IEEE754/BinarySingleNaN.v` (LGPL-3).  They are a
  derived work of those files and are distributed under the same terms
  (see `LICENSE-Flocq` in this directory); the rest of this repository is
  MIT.  The upstream `rocq-linux-process-semantics` has the same
  relationship to Flocq (it links against it through Rocq).

  WHY THIS FILE EXISTS.  `Riscv/Fpu.v` needs the *value* half of IEEE
  rounding, with the intermediate that the flags are read off.  Rocq gets
  it from Flocq's `binary_round_aux`; this is the minimal definitional
  closure of that function (plus the RISC-V-relevant helpers), ported so
  the port stays independent of a Rocq installation.

  This file is DEFINITIONS ONLY (plus a couple of definitional lemmas):
  the correctness theorem lives in Flocq and is taken as the trust
  boundary, exactly as upstream does.  `Fpu.lean` re-derives the value
  with the location kept, and `round_aux_value` pins it to
  `binaryRoundAux` definitionally.
-/
namespace LinuxSem.Flocq

/-! ## The specification datatype (`spec_float`)

Similar to Flocq's `full_float`, but with no NaN payload.  The mantissa of
a finite number is a `Nat`; it is always non-zero in values produced by
the kernel (the `zero` constructor covers the zero case), so `0` is not a
reachable finite mantissa. -/
inductive SpecFloat : Type
  | zero (s : Bool)
  | infinity (s : Bool)
  | nan
  | finite (s : Bool) (m : Nat) (e : Int)
  deriving DecidableEq, Repr

/-- Rounding locations: where the exact value sits relative to the two
    candidate mantissas. -/
inductive Location : Type
  | exact
  | inexact (c : Ordering)
  deriving DecidableEq, Repr

/-- A mantissa being shifted right, with the bits shifted out so far:
    `r` is the rounding bit, `s` the sticky bit. -/
structure ShrRecord : Type where
  m : Int
  r : Bool
  s : Bool
  deriving DecidableEq, Repr

/-- The five architectural rounding modes (plus Flocq's `mode_NA`,
    round-to-nearest-away). -/
inductive Mode : Type
  | NE | ZR | DN | UP | NA
  deriving DecidableEq, Repr

/-! ## Format parameters (`fexp`, `emin`, `Zdigits2`) -/

/-- Exponent of the smallest subnormal. -/
def emin (prec emax : Int) : Int := 3 - emax - prec

/-- The canonical exponent function (Flocq's `FLT_exp`). -/
def fexp (prec emax : Int) (e : Int) : Int := max (e - prec) (emin prec emax)

/-- Number of significant bits of a positive integer (`Pos.size`). -/
def digits2Pos (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `Zdigits2`: the number of significant bits of an integer, as an `Int`;
    zero maps to zero. -/
def Zdigits2 (n : Int) : Int :=
  if n = 0 then 0 else (digits2Pos n.natAbs : Int)

/-! ## Shifting the mantissa -/

/-- Shift a mantissa right by one bit, truncating toward zero and
    recording the shifted-out bit in `r` (rounding) and `s` (sticky).
    This is `SpecFloat.shr_1`, including its handling of negative
    mantissas (`Zneg (xI p)` loses the odd bit without borrowing). -/
def shr1 (mrs : ShrRecord) : ShrRecord :=
  let s := mrs.r || mrs.s
  if mrs.m = 0 then ⟨0, false, s⟩
  else
    let neg := mrs.m < 0
    let a := mrs.m.natAbs
    let q := a / 2
    let r := a % 2 == 1
    ⟨if neg then -(q : Int) else (q : Int), r, s⟩

/-- Where the current mantissa sits relative to its neighbours. -/
def locOfShrRecord (mrs : ShrRecord) : Location :=
  match mrs.r, mrs.s with
  | false, false => .exact
  | false, true => .inexact .lt
  | true, false => .inexact .eq
  | true, true => .inexact .gt

/-- The inverse of `locOfShrRecord`. -/
def shrRecordOfLoc (m : Int) : Location → ShrRecord
  | .exact => ⟨m, false, false⟩
  | .inexact .lt => ⟨m, false, true⟩
  | .inexact .eq => ⟨m, true, false⟩
  | .inexact .gt => ⟨m, true, true⟩

/-- Shift right `n` times (only for positive `n`, as in `SpecFloat.shr`). -/
def shr (mrs : ShrRecord) (e : Int) (n : Int) : ShrRecord × Int :=
  if n > 0 then
    (Nat.rec mrs (fun _ ih => shr1 ih) n.toNat, e + n)
  else
    (mrs, e)

/-- Normalise the mantissa to the format's canonical exponent. -/
def shrFexp (prec emax : Int) (m : Int) (e : Int) (l : Location) : ShrRecord × Int :=
  shr (shrRecordOfLoc m l) e (fexp prec emax (Zdigits2 m + e) - e)

/-! ## Rounding-mode selection (Flocq `Round` + `choice_mode`) -/

/-- Increment a mantissa according to a decision bit. -/
def condIncr (b : Bool) (m : Int) : Int := if b then m + 1 else m

/-- Round-to-nearest decision: `p` breaks the tie (for round-to-nearest-even
    it is `!(m even)`; for round-away it is `true`). -/
def roundN (p : Bool) : Location → Bool
  | .exact => false
  | .inexact .lt => false
  | .inexact .eq => p
  | .inexact .gt => true

/-- Directed rounding toward −∞: increment iff the value is negative and
    the shift was inexact. -/
def roundSignDN (sx : Bool) : Location → Bool
  | .exact => false
  | .inexact _ => sx

/-- Directed rounding toward +∞: increment iff the value is positive and
    the shift was inexact. -/
def roundSignUP (sx : Bool) : Location → Bool
  | .exact => false
  | .inexact _ => !sx

/-- Choose the integer mantissa for the requested rounding mode. -/
def choiceMode (md : Mode) (sx : Bool) (mx : Int) (lx : Location) : Int :=
  match md with
  | .NE => condIncr (roundN (!(mx % 2 == 0)) lx) mx
  | .ZR => mx
  | .DN => condIncr (roundSignDN sx lx) mx
  | .UP => condIncr (roundSignUP sx lx) mx
  | .NA => condIncr (roundN true lx) mx

/-- Round to nearest, ties to even (the `SpecFloat`-only helper). -/
def roundNearestEven (mx : Int) : Location → Int
  | .exact => mx
  | .inexact .lt => mx
  | .inexact .eq => if mx % 2 == 0 then mx else mx + 1
  | .inexact .gt => mx + 1

/-! ## Overflow -/

/-- Does this mode overflow to infinity (rather than to ±MAX)? -/
def overflowToInf (md : Mode) (s : Bool) : Bool :=
  match md with
  | .NE => true
  | .NA => true
  | .ZR => false
  | .UP => !s
  | .DN => s

/-- The overflow result: ±inf, or the largest finite number, according to
    the mode. -/
def binaryOverflow (prec emax : Int) (md : Mode) (s : Bool) : SpecFloat :=
  if overflowToInf md s then .infinity s
  else .finite s (((2 : Int) ^ prec.toNat - 1).toNat) (emax - prec)

/-- Fit a rounded mantissa/exponent into the format, overflowing if the
    exponent is too large. -/
def binaryFitAux (prec emax : Int) (md : Mode) (sx : Bool) (mx : Int) (ex : Int) : SpecFloat :=
  if ex ≤ emax - prec then .finite sx mx.toNat ex else binaryOverflow prec emax md sx

/-- Flocq's `binary_round_aux`: round a (mantissa, exponent, location)
    into an interchange-format datum.  `Fpu.round_aux` restates this with
    the intermediate location kept, so it can report the IEEE flags. -/
def binaryRoundAux (prec emax : Int) (md : Mode) (sx : Bool)
    (mx : Int) (ex : Int) (lx : Location) : SpecFloat :=
  let (mrs', e') := shrFexp prec emax mx ex lx
  let (mrs'', e'') :=
    shrFexp prec emax (choiceMode md sx mrs'.m (locOfShrRecord mrs')) e' .exact
  match mrs''.m with
  | 0 => .zero sx
  | m => if m > 0 then binaryFitAux prec emax md sx m e'' else .nan

/-- Left-align a mantissa to a target exponent (`shl_align`). -/
def shlAlign (mx : Int) (ex ex' : Int) : Int × Int :=
  if ex' < ex then (mx <<< (ex - ex').toNat, ex') else (mx, ex)

/-- `SpecFloat`'s `binary_round`: align, then round to nearest even. -/
def binaryRound (prec emax : Int) (sx : Bool) (mx : Nat) (ex : Int) : SpecFloat :=
  let ez := fexp prec emax ((digits2Pos mx : Int) + ex)
  let (mz, ez') := shlAlign (mx : Int) ex ez
  binaryRoundAux prec emax .NE sx mz ez' .exact

/-- `SpecFloat`'s `binary_normalize`. -/
def binaryNormalize (prec emax : Int) (m : Int) (e : Int) (szero : Bool) : SpecFloat :=
  match m with
  | 0 => .zero szero
  | _ => if m > 0 then binaryRound prec emax false m.toNat e
         else binaryRound prec emax true m.natAbs e


/-- Exact integer square root (binary search, fuel-bounded so it is
    structurally recursive).  Lean's core library has no `Nat.sqrt`, and
    this is computation only — no proof depends on how it is spelled. -/
def isqrtGo (fuel n lo hi : Nat) : Nat :=
  match fuel with
  | 0 => lo
  | f + 1 =>
      if lo + 1 ≥ hi then lo
      else
        let mid := (lo + hi) / 2
        if mid * mid ≤ n then isqrtGo f n mid hi else isqrtGo f n lo mid

def isqrt (n : Nat) : Nat := isqrtGo (n + 1) n 0 (n + 1)

/-! ## Comparison and the division/square-root cores

These are `SpecFloat.SFcompare`, `new_location`, `SFdiv_core_binary` and
`SFsqrt_core_binary`, translated from the Rocq standard library.  They are
the exact-integer cores that `Fpu.fp_div` and `Fpu.fp_sqrt` hand to the
rounding kernel. -/

/-- Total order on spec floats, with `none` for an unordered (NaN) pair.
    Mirrors `SpecFloat.SFcompare`, including the sign and exponent cases. -/
def SFcompare : SpecFloat → SpecFloat → Option Ordering
  | .nan, _ => none
  | _, .nan => none
  | .infinity s1, .infinity s2 =>
      some (match s1, s2 with
        | true, true => .eq | false, false => .eq
        | true, false => .lt | false, true => .gt)
  | .infinity s, _ => some (if s then .lt else .gt)
  | _, .infinity s => some (if s then .gt else .lt)
  | .finite s _ _, .zero _ => some (if s then .lt else .gt)
  | .zero _, .finite s _ _ => some (if s then .gt else .lt)
  | .zero _, .zero _ => some .eq
  | .finite s1 m1 e1, .finite s2 m2 e2 =>
      some (match s1, s2 with
        | true, false => .lt
        | false, true => .gt
        | false, false =>
            match compare e1 e2 with
            | .lt => .lt | .gt => .gt | .eq => compare m1 m2
        | true, true =>
            match compare e1 e2 with
            | .lt => .gt | .gt => .lt | .eq => (compare m1 m2).swap)

/-- Location of a remainder `k` out of `nbSteps`. -/
def newLocationEven (nbSteps k : Int) : Location :=
  if k = 0 then .exact else .inexact (compare (2 * k) nbSteps)

def newLocationOdd (nbSteps k : Int) : Location :=
  if k = 0 then .exact
  else
    .inexact (match compare (2 * k + 1) nbSteps with
      | .lt => .lt | .eq => .lt | .gt => .gt)

def newLocation (nbSteps : Int) : Int → Location :=
  fun k => if nbSteps % 2 == 0 then newLocationEven nbSteps k else newLocationOdd nbSteps k

/-- Core of binary division: the exact quotient mantissa, its exponent,
    and the location of the discarded remainder. -/
def SFdivCoreBinary (prec emax : Int) (m1 e1 m2 e2 : Int) : Int × Int × Location :=
  let d1 := Zdigits2 m1
  let d2 := Zdigits2 m2
  let e' := min (fexp prec emax (d1 + e1 - (d2 + e2))) (e1 - e2)
  let s := e1 - e2 - e'
  let m' := if s > 0 then m1 <<< s.toNat else if s = 0 then m1 else 0
  (m' / m2, e', newLocation m2 (m' % m2))

/-- Core of binary square root. -/
def SFsqrtCoreBinary (prec emax : Int) (m e : Int) : Int × Int × Location :=
  let d := Zdigits2 m
  let e' := min (fexp prec emax ((d + e + 1) / 2)) (e / 2)
  let s := e - 2 * e'
  let m' := if s > 0 then m <<< s.toNat else if s = 0 then m else 0
  let q : Nat := isqrt m'.toNat
  let r : Nat := m'.toNat - q * q
  let l := if r = 0 then .exact else .inexact (if r ≤ q then .lt else .gt)
  ((q : Int), e', l)

end LinuxSem.Flocq
