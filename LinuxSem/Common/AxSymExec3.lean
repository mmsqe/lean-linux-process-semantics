/-
  * Common.AxSymExec3 — the reflective certified symbolic executor, module AX2.
  module `AX2`.

  Image-INDEPENDENT.  A from-scratch extension of `SymExec` (whose
  design notes apply verbatim; read its header first).  What it adds:

  - VALUES: `EExt sx lo n e` (byte-slice extraction, so a narrow reload
    of a wider store, `lb`/`lh`/`lw` sign extension and `sb`/`sh`/`sw`
    round trips are modelled), `EBlob` (a byte range of an opaque byte
    string: file contents delivered by `read`, a copied payload),
    constant folding for EVERY ALU/M op (computed with the ISA's own
    functions on closed bitvectors — sound by `Z_to_bv_bv_unsigned`),
    literal branch conditions decided without consuming the script.
  - ADDRESSES: `saddr` = arbitrary base expression + literal offset
    (not just a variable), so `p + n` style symbolic bases are legal;
    same-base questions are decided by `Int` arithmetic, cross-base
    questions emit obligations (`SCDisj`/`SCInside`) steered by a HINT
    script where undecidable.
  - MEMORY KNOWLEDGE: besides the in-block store log, the state carries
    facts about the BASE memory (`KWord`, `KZero`, `KBlob`, `KImg`):
    spilled values / argv words, mmap'd zero pages, syscall-written byte
    strings, and untouched image ranges (`.rodata`/`.data` constants are
    then read straight out of the segment list).  A load is resolved
    log-first, then knowledge, then the `SCReadBase` fallback.
  - all integer loads/stores (lb lbu lh lhu lw lwu ld / sb sh sw sd),
    `fence` as a no-op.

  Soundness: `sym_exec_sound` — a `vm_compute`d run plus its side
  conditions give `CatSim.msteps` from any concrete state the entry
  symbolic state describes (`st_ok`).  Nothing is admitted.

  ** RV64A atomics + reservation tracking; P-a/b/c

  STATE.  `sym_state` has a sixth (last) field `s_resv : Option saddr`,
  the symbolic LR/SC reservation; the record constructor is `SSR`.
  `SS p r l k n` is a parametric ABBREVIATION for `SSR p r l k n none`
  (no live reservation), so a 5-field construction — plan checker,
  certificates, drivers — parses, computes and reduces without a
  reservation argument (and normal forms PRINT as `SS ...`).  `sset` /
  `sjump` preserve `s_resv`; `clr ss` clears it; `s_clean ss` tests it.

  Denotation (`AxSymExec3Sound.st_okR`): the machine is
  `SymStepR.mkstR regs pc mem rom (resv_denot E (s_resv ss))` where
  `resv_denot E (some a) = some (adenot E a)`, `resv_denot E none = none`;
  `mkstR regs pc mem rom none` is convertible with `PropExec.mkst regs pc mem rom`.

  `sym_step` CASES for atomics (all with proof, `AxSymExec3Sound.sym_step_soundR`):
  - `Lr wd aq rl rd rs1` (any aq/rl): requires `amo_alignedb fk (rs1) wd`
    = the ISA's `amo_aligned` decided TRUE by `lin_lowbits_kn` on the
    address expression (low 2 resp. 3 bits provably 0), else `SStop`.
    Address `a := to_saddrK fk (rs1) 0`; the read is resolved exactly like
    a `Load` of 4 bytes sign-extended (`.w`, i.e. `lw`) / 8 bytes (`.d`)
    through the shared `sym_read` (log, knowledge, `SCReadBase` fallback;
    same side conditions as a load); `rd := value`; `s_resv := some a`.
  - `Sc wd aq rl rd rs1 rs2`: requires alignment as above AND
    `s_resv = some r` with `saddr_eqb r a` (syntactically the reserved
    address) — otherwise `SStop`: the FAILING sc is never produced.  Then
    behaves as a `Store` of the low 4 / 8 bytes of `rs2` at `a` (log entry
    `SE a 4|8 (rs2)`, side conditions `flat_sc ++ storeok_sc`),
    `rd := ELit 0`, `s_resv := none`.
  - `Amo op wd aq rl rd rs1 rs2` for op in {SWAP, ADD, XOR, AND, OR}
    (`amo_aluop`; MIN/MAX/MINU/MAXU: `SStop`): alignment as above; old
    value `vold` by `sym_read` (4 bytes sign-extended / 8 bytes); log entry
    `SE a n (amo_newval fk wd aop vold (rs2))` where the new value is
    `rs2` (swap), `mkAluwK fk op vold rs2` (`.w`: 32-bit op, low 4 bytes
    stored) or `mkAluK fk op vold rs2` (`.d`); `rd := vold` (the value
    of rs2 is read BEFORE rd is written); side conditions
    `read scs ++ storeok_sc`; reservation: `resv_inval` (below).
  - `Store`: the usual log entry and side conditions; additionally the
    reservation is updated by `resv_inval (s_resv ss) a`: `none` stays
    `none` (the common case); `some r`
    with `saddr_eqb r a` is killed; same base expression with offsets
    differing mod 2^64 is kept; anything else (undecidable aliasing) is
    `SStop`.  (`Sem.inval_resv` kills a reservation on a store to EXACTLY
    the reserved address.)
  - every other instruction passes `s_resv` through.
  The `Load` case is phrased through `sym_read`.

  DRIVERS.  `sym_exec`, `sym_execS`, `sym_execT` are wrappers around the
  tail-recursive loops `sym_exec_go`, `sym_execS_go`, `sym_execT_go` which
  carry a CHECKPOINT (the last state with `s_resv = none`, with its side
  conditions / scripts): a run never hands back a state with a live
  reservation — if it comes to rest between an `lr` and its `sc` (stop pc,
  fuel, undecided branch, unsupported instruction) it returns the state AT
  the `lr` instead (`sym_exec_resv`, `sym_execS_resv`, `sym_execT_resv`).
  The entry state's `s_resv` is ignored (`clr`).  Consequently the
  soundness theorems `sym_exec_sound/_ex`, `sym_execS_sound/_ex`,
  `sym_execT_sound/_ex` are stated over `mkst`, with
  the block-boundary `st_ok`; the general forms are
  `sym_exec_soundR`, `sym_execS_soundR`, `sym_execT_soundR`.

  P-a: `decide_branch` falls back to `lin_branch`: `bltu` /
  `bgeu` decided by exact linear arithmetic (`lin_ge0`: `b-1-a >= 0` resp.
  `a-b >= 0`), `blt`/`bge` likewise when both operands are provably below
  2^63 (`erange`).
  P-b: `log_lookup`, same base, read PARTIALLY overlapping a log entry:
  composed bytewise (`log_bytes_lit`) when every byte of the
  read is covered by a same-base log entry holding a LITERAL (newest
  wins per byte); result `lit_of_bytes`; otherwise stuck.
  P-c: `lowbits kn e j` (low `j` bits through AND/OR/XOR with a literal,
  ADD, SUB, literal multiple; leaves: literal, `ealign`, `lin_lowbits_kn`)
  is consulted by `mkAnd`'s `2^j-1` mask case before the other tests (on
  a case they also simplify it yields the same literal).

  ** `mkSrl` split condition; align-down atoms in `erange`

  R4.1 `mkSrl`'s partial
     split `(A + R) >> s` (R3.3) fires ONLY when the residual R provably lies in
     one 2^s-block (`erange` of `unlin R`: lo >> s = hi >> s = q), giving the
     pure linear form `A/2^s + q` — the constant residual is folded by
     construction (e.g. `(4096 v + 6143 + len) >> 3 = 512 v + 770` for len
     in `[17,22]`).  Otherwise the whole shift stays ONE atom `SRL(A + R, s)`,
     so relational `KRange` facts about the
     unsplit sum (`KRange (s + L)`, shifted match) keep bounding
     it and no `A' + AND(SRL(R), -8)` address forms arise downstream.
  R4.2 `erange kn e` = the basic interval (`erange0`) tightened, when
     `e` contains align-down atoms `x AND -2^j` (j <= 48) under `ALU_ADD`
     nodes, by the interval of the de-ANDed sum (`deand`, as
     `APC.deand`; re-normalised through `unlin (lin_of _)` so relational
     facts on the canonical sum match): `u e = u e' - rho`, 0 <= rho <= s,
     hence `e` in `[lo' - s, hi']` when `s <= lo'`.  Pure tightening
     (intersection); `AxSymExec3Sound.deand_sound`, `erange_sound`.

  ** `KUnk`, EXTENSION MODE, register cap, partial `mkSrl`

  All with proof (`AxSymExec3Sound`).
  The classic executor (`sym_step`, `sym_exec`, `sym_execS`, `sym_execT`)
  and its theorems do not use the items below, except
  (R3.3), which fires only where `mkSrl` would otherwise give up.

  R3.1 kentry `KUnk a n` (LAST constructor): the bytes `a, a+n` are
     DEFINED in the base overlay (mapped, readable and writable) but
     arbitrary; `n` may be symbolic.  Structurally a KZero: `prune_zf KUnk`
     / `kunk_cut` / `kbase`; lookups never hit it (no value).  Node-side
     lemmas: `AxSymExec3Sound.know_ok_unk_intro` (after any `wbytes`),
     `know_ok_unk_intro_pt`, `kunk_of_zero|fill|blob`, `kentry_ok_unk_grows`
     (preserved by every `mem_grows` memory change, e.g. any write anywhere:
     `kentry_ok_unk_frame`), `kunk_store_ok`, `kunk_cut_sound`.
  R3.2 EXTENSION MODE `sym_stepX K` / drivers `sym_execSX K`, `sym_execTX t K`
     (section 4c): the classic step, then (a) the obligations the knowledge
     decides are DISCHARGED — this step's base read `SCReadBase a n sx
     (EVar (s_next ss))` when `a, a+n` is provably readable (`kn_readable`:
     inside one KUnk/KZero/KFill/KBlob/KWord entry by offsets or `xinside`, or
     bytewise by literal-extent entries / image bytes), so the load yields a
     FRESH VARIABLE with no side condition; `SCFlat` likewise; `SCStoreOk`
     when the range is provably overlay-defined (`kn_overlay`) — and (b) the
     destination register is capped: with `K > 0`, an expression of more
     than `K` nodes (`esize_le`) is renamed to `EVar (s_next ss)` (`cap_rd`,
     `rd_of`); `K = 0`: no cap.  Soundness by ENVIRONMENT EXTENSION
     (`AxSymExec3Sound.st_okX`, `sym_stepX_sound`, `sym_execTX_sound` /
     `sym_execTX_ex` / `sym_execSX_sound`, `AxSymRun3.runTX_sound`): from a
     state closed below its counter, some valuation agreeing with the given
     one below `s_next` simulates the run, and the result is again good for
     all valuations agreeing below the new counter.
  R3.3 `mkSrl`: when only SOME terms of the linear form
     have coefficients divisible by 2^s — A (divisible terms) + R (the rest
     and the constant) — and both the whole form and R provably do not wrap
     (`lin_nowrap`, `lin_nowrap_l`): `(A + R) >> s = A/2^s + (R >> s)`, the
     SRL atom covering only R (`lsplit_divc`); e.g. `(4096 v + 6143 + len)
     >> 3 = 512 v + ((len + 6143) >> 3)`.
  R3.4 `erange` of `x >> s` atoms (`lo >> s, hi >> s`) and point-range
     folding (`foldK` via `mkAluK`).

  ** Knowledge byte composition, prune keep-bytes,
     `KFill`, EQ/NE by linear arithmetic, aligned/residual split of `mkAnd`

  All with proof (`AxSymExec3Sound`).

  1. `prune1`/`prune1p` (hence `carry`), KWord case (task 1): a store
     `k, k+w` that PARTIALLY overlaps a same-base `KWord (SA b kk) w' (ELit z)`
     keeps the untouched bytes as literal KWords — the piece below `k` and
     the piece from `k+w` up (`kword_cut`: widths `k-kk` / `kk+w'-k-w`,
     values the byte slices of `z` folded by `mkExt`).  Non-literal values
     are dropped.
  2. `know_lookupA` (task 2): the walk is `know_lookupA0`; when it finds
     NO single covering entry (`LMiss`) but every byte of `rb+rk, +n` is
     covered by LITERAL knowledge of the same base spelling — a KWord
     holding an `ELit`, a literal-length `KZero`/`KFill`, or for the
     absolute base `ELit 0` an untouched image byte (`KImg` + `seg_rom`) —
     the read is the composed literal (`know_byte_lit`/`know_bytes_lit`,
     `lit_of_bytes`; like P-b's `log_bytes_lit`).  Priority: log,
     single knowledge entry, THEN composition, then the `SCReadBase`
     fallback.  Also reaches `know_lookup`.
  3. kentry `KFill a n c` (task 3; LAST constructor, so numbered case
     analyses elsewhere keep their order): base holds `n` copies of the byte
     `Z_to_bv 8 c` at `a`, `n` possibly symbolic (`AxSymExec3Sound.kentry_ok`:
     flat + pointwise, exactly KZero's shape with byte c; no constraint on
     c, lookups use `c mod 256`).  Reads inside: `fill_lit sx n c` (hit
     decided exactly like KZero: `rel_lit` for a literal length, `xinside`
     / hint protocol otherwise).  `prune1`/`prune1p`/`prune1pc`/`kbase`:
     the KZero protocol, generic in the constructor (`prune_zf`, `ktrim`,
     `kcut`; `kzero_cut` = `kcut KZero`, `kfill_cut c`).  `is_factb`: not a
     fact (memory entry).  AsanPlanCore / AxSymRun3: KFill treated as KZero in
     kentry_vars_lt, kentry_apart_b(p), havoc1(p) (cut by `kfill_cut`),
     grant_keep_b, live_vars, kn_gc_entry.  Node-side lemmas:
     `AxSymExec3Sound.know_ok_fill_intro` (after `wbytes M a (repeat (Z_to_bv 8 c) n)`),
     `know_ok_fill_intro_pt` (pointwise memory), `kentry_ok_frame_bytes`
     (entries apart from a written byte string survive), `kfill_cut_sound`.
  4. `lin_branch` (task 4): `beq`/`bne` decided when one operand is
     provably strictly below the other by exact linear arithmetic
     (`lin_ge0` on b-1-a resp. a-1-b; needs both sides' no-wrap, i.e. base
     ranges).  Last resort of `decide_branch`.
  5. `mkAnd` with an alignment mask (task 5).  `a AND -2^j` where the
     linear form of `a` has terms that are multiples of 2^j (`lsplit_div`:
     by coefficient or coefficient x atom alignment) AND residual terms:
     A + R with A = aligned terms + (c - c mod 2^j), R = `unlin (c mod 2^j,
     residual terms)`; if `erange R` lies inside one block `q 2^j, (q+1) 2^j`
     the result is the LINEAR form A + q 2^j, else A + (R AND -2^j) (the
     opaque atom covers only the residual) — `and_high_split`.  Dually
     `a AND (2^j-1)` = R - q 2^j, else R AND (2^j-1) — `and_low_split`.
     When nothing aligned can be split off (e.g. musl's `(n + 4095) & -4096`)
     the answer is the R6 spelling 2^j (a >> j) resp. the plain atom.
     `erange (x AND -2^j)` = `lo - lo mod 2^j, hi - hi mod 2^j` from
     `erange x` (monotone).
  6. the align-up idiom `x + m - (x AND (m-1))`
     (compiler-rt `InitAligned`): `pageup_low`/`pageup_align` recognise the
     dual sign pattern c + y - (y AND mm) (`find_and_atom_k`/`pageup_low_k`
     with sg = -1, tried only after the sg = +1 musl page-up idiom failed), so
     `ealign` of SpaceBeg = 4096 v + 65536 - (4096 v AND 65535) is 16 and
     masks of it fold.  The normal form of the AND itself stays as is.

  The encodings are `Int` for the value level and `Nat` for counts and
  `Z_to_bv n z` → `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)`,
  `bv_signed w` → `w.toInt`, `list` → `List`, `option` → `Option`,
  `Record` → `structure`, `Inductive` → `inductive`).
  Two `Int`-level vocabulary gaps, carried here in the file's own `Z`
  section (see `PropExec` for the same reasoning):
  - `Z.land` / `Z.lor` / `Z.lxor` / `Z.ones` have no Lean core
    counterpart (there is no `Int.land`).  The file's uses are all
    confined to a 64-bit window (the all-ones masks `2^64-1`, `2^32-1`,
    `2^k-1` with `k <= 64`, and operands already wrapped into
    `[0, 2^64)`), so `zland`/`zlor`/`zlxor` are defined on the 64-bit
    window `a % 2^64`, which is the value every use site here wants.  The one negative mask  is
    `Z.land z (-2)` (`-2 = ...1110`), carried as the exact
    two's-complement identity `zland_m2 z = z - z % 2` (`PropExec`).
  - `Z.div`/`Z.modulo` are floor division and a non-negative remainder
    for a positive divisor; Lean's `Int` `/` and `%` are the same, so
    they are used directly.  `Z.shiftr z k` is `z / 2^k` (floor),
    `Z.shiftl z k` is `z * 2^k`.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StoreOk
import LinuxSem.Common.SymExec
import LinuxSem.Common.RocqSpelling

namespace LinuxSem.Common.AxSymExec3

open LinuxSem.Riscv
open LinuxSem.Common.RocqSpelling
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec

local instance axsymexec3_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-- `2^64`. -/
def two64z : Int := 2 ^ 64

/-- `2^64` ( keeps both spellings). -/
def two64 : Int := 2 ^ 64

/-- `2^64 - 1`.  PERF: once, not per `clampi` call. -/
def two64m1 : Int := two64 - 1

/-- PERF: powers of two as TOP-LEVEL constants.  The native compiler
    evaluates a top-level constant once (lazily); an inline `2 ^ 63` is a
    `Z.pow` call chain re-run at every evaluation of the enclosing
    function. -/
def two63z : Int := 2 ^ 63

/-- `-2^63`. -/
def mtwo63z : Int := - 2 ^ 63

/-- `2^32`. -/
def two32z : Int := 2 ^ 32

/-- `2^31`. -/
def two31z : Int := 2 ^ 31

/-!     See the NOTES above for why `zland` is 64 bits wide. -/

/- `Z_to_bv`, `bv_unsigned`, `bv_signed` are the shared Rocq spellings,
   imported from `LinuxSem.Common.RocqSpelling` (and opened above). -/

/-- The low `n` bits set, i.e. `2^n - 1`. -/
def zones (n : Nat) : Int := (2 : Int) ^ n - 1

/-- `Z.ones 64`; `zland k ones64z = k mod 2^64` (`land_ones64z'`). -/
def ones64z : Int := zones 64

/-- `Z.land`, on the 64-bit window that every use in this file lives in. -/
def zland (a b : Int) : Int := (((a % two64).toNat &&& (b % two64).toNat : Nat) : Int)

/-- `Z.lor`, on the 64-bit window (see `zland`). -/
def zlor (a b : Int) : Int := (((a % two64).toNat ||| (b % two64).toNat : Nat) : Int)

/-- Bitwise xor, on the 64-bit window (see `zland`). -/
def zlxor (a b : Int) : Int := (((a % two64).toNat ^^^ (b % two64).toNat : Nat) : Int)

/-- `Z.land z (-2)` — "clear bit 0" — as the exact two's-complement
    identity. -/
def zland_m2 (z : Int) : Int := z - z % 2

/-- Left shift of `a` by `k >= 0`. -/
def zshiftl (a : Int) (k : Nat) : Int := a * (2 : Int) ^ k

/-- Right shift of `a` by `k >= 0`: floor division by `2^k`. -/
def zshiftr (a : Int) (k : Nat) : Int := a / (2 : Int) ^ k

/-! ## 1. Values -/

/-- A symbolic 64-bit value.  Literals are `Int` (never `bv`), so a
    `vm_compute`d run never carries a bitvector around. -/
inductive expr : Type
  /-- `Z_to_bv 64 z`. -/
  | ELit (z : Int)
  /-- ambient word variable -/
  | EVar (n : Nat)
  /-- `alu64 op a b` -/
  | EAlu (op : AluOp) (a b : expr)
  /-- `sext 64 (alu32 op (low32 a) (low32 b))` -/
  | EAluw (op : AluOp) (a b : expr)
  /-- `mul_div op a b` -/
  | EMd (op : MulOp) (a b : expr)
  /-- `sext 64 (mul_div op (low32 a) (low32 b))` -/
  | EMdw (op : MulOp) (a b : expr)
  /-- bytes `[lo,lo+n)` of `e`, zero/sign extended -/
  | EExt (sx : Bool) (lo n : Nat) (e : expr)
  /-- `n` LE bytes at offset `i` of byte string `k` -/
  | EBlob (sx : Bool) (k : Nat) (i : Int) (n : Nat)
  deriving DecidableEq, Repr

/-- The valuation: word variables and byte-string variables. -/
structure env where
  /-- values of the word variables -/
  ev : Nat → word
  /-- values of the byte-string variables -/
  eb : Nat → List byte

/-- `ext_Z`: the integer reading of bytes `[lo, lo+n)` of `z`. -/
def ext_Z (sx : Bool) (lo n : Nat) (z : Int) : Int :=
  let u := z / (2 : Int) ^ (8 * lo) % (2 : Int) ^ (8 * n)
  if sx then bv_swrap (8 * n) u else u

/-- The word reading of the same slice. -/
def ext_val (sx : Bool) (lo n : Nat) (v : word) : word :=
  Z_to_bv 64 (ext_Z sx lo n (bv_unsigned v))

/-- `n` bytes at offset `i` of a byte string. -/
def blob_bytes (bs : List byte) (i : Int) (n : Nat) : List byte :=
  (bs.drop i.toNat).take n

/-- The word reading of a slice of a byte string. -/
def blob_val (sx : Bool) (bs : List byte) (i : Int) (n : Nat) : word :=
  Z_to_bv 64 (let u := bytes_le_to_Z (blob_bytes bs i n)
              if sx then bv_swrap (8 * n) u else u)

/-- Denotation of a symbolic value. -/
def edenot (E : env) : expr → word
  | .ELit z => Z_to_bv 64 z
  | .EVar n => E.ev n
  | .EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | .EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | .EMd op a b => mul_div op (edenot E a) (edenot E b)
  | .EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  | .EExt sx lo n a => ext_val sx lo n (edenot E a)
  | .EBlob sx k i n => blob_val sx (E.eb k) i n

/-! ### Decidable syntactic equality -/

/-- `aluop_eqb` (this tree's `AluOp` already has `DecidableEq`;
    this is kept because the reflective code compares constructors by
    `Bool`). -/
def aluop_eqb (a b : AluOp) : Bool :=
  match a, b with
  | .ADD, .ADD | .SUB, .SUB | .SLL, .SLL | .SLT, .SLT
  | .SLTU, .SLTU | .XOR, .XOR | .SRL, .SRL | .SRA, .SRA
  | .OR, .OR | .AND, .AND => true
  | _, _ => false
def mulop_eqb (a b : MulOp) : Bool :=
  match a, b with
  | .MUL, .MUL | .MULH, .MULH | .MULHSU, .MULHSU | .MULHU, .MULHU
  | .DIV, .DIV | .DIVU, .DIVU | .REM, .REM | .REMU, .REMU => true
  | _, _ => false

/-- Structural equality of symbolic values. -/
def expr_eqb : expr → expr → Bool
  | .ELit a, .ELit b => a == b
  | .EVar a, .EVar b => a == b
  | .EAlu o a b, .EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | .EAluw o a b, .EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | .EMd o a b, .EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | .EMdw o a b, .EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | .EExt s l n a, .EExt s' l' n' a' =>
      (s == s') && (l == l') && (n == n') && expr_eqb a a'
  | .EBlob s k i n, .EBlob s' k' i' n' =>
      (s == s') && (k == k') && (i == i') && (n == n')
  | _, _ => false

/-! ### Smart constructors (constant folding / normal forms) -/

/-- Closed evaluation of the ISA primitives on literals. -/
def zalu (op : AluOp) (x y : Int) : Int :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y))

/-- The 32-bit variant. -/
def zaluw (op : AluOp) (x y : Int) : Int :=
  bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word)

/-- Closed evaluation of an M-extension op on literals. -/
def zmd (op : MulOp) (x y : Int) : Int :=
  bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y))

/-- The 32-bit variant. -/
def zmdw (op : MulOp) (x y : Int) : Int :=
  bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))) : word)

/-- Closed byte-slice extraction of a literal. -/
def zext_lit (sx : Bool) (lo n : Nat) (x : Int) : Int :=
  bv_unsigned (ext_val sx lo n (Z_to_bv 64 x))

/-- Is the expression a literal? -/
def is_lit (e : expr) : Option Int :=
  match e with | .ELit z => some z | _ => none

/-! ### Linear normal forms

    Sums `c + k1*a1 + ... + kn*an` (mod 2^64) over ATOMS (any expression
    that is not itself a literal / sum / literal multiple / literal left
    shift) are kept in one canonical shape: atoms sorted by `expr_cmp`,
    coefficients and constant in the symmetric range (-2^63, 2^63] (so
    stack offsets print as `-48`, not `2^64-48`), zero terms dropped.
    Consequences: `p + 16*off - 16*off` cancels syntactically; every
    address is `terms + literal`, so `split_lit` finds base and offset. -/

/-- Reference definition (what the soundness proofs reason about). -/
def snorm_ref (k : Int) : Int :=
  let m := k % two64z
  if 2 ^ 63 ≤ m then m - two64z else m

/-- PERF: `snorm` is called by every `lins`/`ladd`/`lscale`/`lin_of` step;
    almost every argument already lies in the symmetric range, where it is
    the identity (two comparisons, no allocation); otherwise `Z.land` with
    `2^64-1` replaces the long division.  `snorm_eq`: equal to
    `snorm_ref`. -/
def snorm (k : Int) : Int :=
  if (mtwo63z ≤ k && k < two63z) then k
  else let m := zland k ones64z
       if two63z ≤ m then m - two64z else m

/-- `log2_up`: the smallest `k` with `n <= 2^k`, i.e. `0` for
    `n <= 1` and `floor(log2 (n-1)) + 1` otherwise. -/
def zlog2_up (n : Int) : Int :=
  if n ≤ 1 then 0 else ((Nat.log2 (n.toNat - 1) + 1 : Nat) : Int)

/-- Power at a non-negative `Int` exponent. -/
def zpow (a : Int) (k : Int) : Int := a ^ k.toNat

/-- `Z.land a (2^64 - 1) = a mod 2^64` — `Z.land_ones`. -/
theorem land_ones64z' (a : Int) : zland a ones64z = a % 2 ^ 64 := by
  have h2 : ((2 : Int) ^ 64 - 1).toNat = 2 ^ 64 - 1 := by decide
  have h1 : ((2 : Int) ^ 64 - 1) % ((2 : Int) ^ 64) = (2 : Int) ^ 64 - 1 := by decide
  have hX : 0 ≤ a % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
  have hXlt : a % (2 : Int) ^ 64 < (2 : Int) ^ 64 := Int.emod_lt_of_pos _ (by decide)
  unfold zland ones64z zones two64
  rw [h1, h2]
  rw [Nat.and_two_pow_sub_one_eq_mod _ 64]
  have hcast : ((a % (2 : Int) ^ 64).toNat : Int) = a % (2 : Int) ^ 64 :=
    Int.toNat_of_nonneg hX
  have hmod : (a % (2 : Int) ^ 64).toNat % 2 ^ 64 = (a % (2 : Int) ^ 64).toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod, hcast]

/-- `snorm` is `snorm_ref` (the fast path is the symmetric range). -/
theorem snorm_eq (k : Int) : snorm k = snorm_ref k := by
  have hland : zland k ones64z = k % (2 : Int) ^ 64 := land_ones64z' k
  simp only [snorm, snorm_ref, two63z, two64z, two64, mtwo63z, hland]
  /- THE GUARDS ARE HOISTED INTO `have`s, with their statements written
     out, instead of being passed to `rw` as `(by …)` blocks.  This
     toolchain elaborates a rewrite's argument before it looks for the
     pattern, so `ite_eq_left (by …)` asks the block to prove a metavariable
     and the `rw`/`omega` inside answers "did not find an occurrence";
     even with the guard named, the peel is `(ite_eq_left h).trans` /
     `ite_eq_right h` rather than `rw [ite_eq_left h]`, whose instance
     unification the same goal defeats (the `Decidable` of a `&&` of two
     `decide`s).  `simp only [hk]` is used where the rewritten term sits
     under such an instance and `rw` refuses the motive. -/
  by_cases h1 : -(2 : Int) ^ 63 ≤ k
  · by_cases h2 : k < (2 : Int) ^ 63
    · have hg : (decide (-(2 : Int) ^ 63 ≤ k) && decide (k < (2 : Int) ^ 63)) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨h1, h2⟩
      refine (ite_eq_left hg).trans ?_
      by_cases h3 : 0 ≤ k
      · have hk : k % (2 : Int) ^ 64 = k := Int.emod_eq_of_lt h3 (by omega)
        have hg2 : ¬ ((2 : Int) ^ 63 ≤ k) := by omega
        simp only [hk]
        exact (ite_eq_right hg2).symm
      · have h3' : k < 0 := by omega
        have hstep : (k + (2 : Int) ^ 64) % (2 : Int) ^ 64 = k % (2 : Int) ^ 64 := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
          have hsub : (k + (2 : Int) ^ 64) - k = (2 : Int) ^ 64 := by omega
          rw [hsub]
          exact Int.emod_self
        have hkm : (k + (2 : Int) ^ 64) % (2 : Int) ^ 64 = k + (2 : Int) ^ 64 :=
          Int.emod_eq_of_lt (by omega) (by omega)
        have hk : k % (2 : Int) ^ 64 = k + (2 : Int) ^ 64 := by omega
        have hg3 : (2 : Int) ^ 63 ≤ k + (2 : Int) ^ 64 := by omega
        simp only [hk]
        rw [ite_eq_left hg3]
        omega
    · have hg : ¬ ((decide (-(2 : Int) ^ 63 ≤ k) && decide (k < (2 : Int) ^ 63)) = true) := by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        omega
      exact ite_eq_right hg
  · have hg : ¬ ((decide (-(2 : Int) ^ 63 ≤ k) && decide (k < (2 : Int) ^ 63)) = true) := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      omega
    exact ite_eq_right hg

/-- PERF: remainder by 2^64 with the in-range fast path, provably equal to
    the arithmetic it replaces for ALL arguments. -/
def zmod64 (z : Int) : Int :=
  if (0 ≤ z && z < two64z) then z else zland z ones64z

/-- PERF: quotient by 2^64 with the in-range fast path, provably equal to
    the arithmetic it replaces for ALL arguments. -/
def zdiv64 (z : Int) : Int :=
  if (0 ≤ z && z < two64z) then 0 else zshiftr z 64

/-- `zmod64` is `z mod 2^64`. -/
theorem zmod64_eq (z : Int) : zmod64 z = z % 2 ^ 64 := by
  have hland : zland z ones64z = z % (2 : Int) ^ 64 := land_ones64z' z
  have hpos : (0 : Int) < (2 : Int) ^ 64 := by decide
  unfold zmod64 two64z
  by_cases h1 : 0 ≤ z
  · by_cases h2 : z < (2 : Int) ^ 64
    · rw [ite_eq_left (by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨h1, h2⟩)]
      exact (Int.emod_eq_of_lt h1 h2).symm
    · rw [ite_eq_right (by
        intro hc
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
        omega)]
      exact hland
  · rw [ite_eq_right (by
      intro hc
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
      omega)]
    exact hland

/-- `zdiv64` is `z / 2^64`. -/
theorem zdiv64_eq (z : Int) : zdiv64 z = z / 2 ^ 64 := by
  unfold zdiv64 two64z
  by_cases h1 : 0 ≤ z
  · by_cases h2 : z < (2 : Int) ^ 64
    · rw [ite_eq_left (by
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨h1, h2⟩)]
      exact (Int.ediv_eq_zero_of_lt h1 h2).symm
    · rw [ite_eq_right (by
        intro hc
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
        omega)]
      rfl
  · rw [ite_eq_right (by
      intro hc
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
      omega)]
    rfl

/-- Alias. -/
theorem zmod64_eq2 (z : Int) : zmod64 z = z % two64 := zmod64_eq z

/-- Alias. -/
theorem zdiv64_eq2 (z : Int) : zdiv64 z = z / two64 := zdiv64_eq z

/-- `wrap64`: reduce a literal to `[0, 2^64)`. -/
def wrap64 (z : Int) : Int :=
  if (0 ≤ z && z < two64) then z else z % two64

/-- Sign-extend the low 32 bits of a canonical literal to 64 bits. -/
def sx32 (r : Int) : Int :=
  if r < 2147483648 then r else r + 18446744069414584320

/-- PERF: reduction modulo 2^64 / 2^32 WITHOUT `Z.modulo` (bit-serial long
    division; on the enumeration sweeps of `evalS` it was a fifth of a
    class-wide payload leaf): the range test first, `Z.land` with the
    all-ones mask otherwise (`Z.land_ones`).  `= z mod 2^64` / `= z mod
    2^32` for EVERY z (`AxSymExec3Sound.land64_eq`, `land32_eq`). -/
def ones32z : Int := zones 32

/-- `z mod 2^64` by mask. -/
def land64 (z : Int) : Int :=
  if (0 ≤ z && z < two64) then z else zland z ones64z

/-- `z mod 2^32` by mask. -/
def land32 (z : Int) : Int :=
  if (0 ≤ z && z < two32z) then z else zland z ones32z

/-- Plain-`Int` ALU on canonical (wrapped) literals; equal to `zalu` on
    canonical arguments. -/
def zfast (op : AluOp) (x y : Int) : Int :=
  match op with
  | .ADD => let t := x + y; if t < two64 then t else t - two64
  | .SUB => let t := x - y; if 0 ≤ t then t else t + two64
  | .AND => zland x y
  | .OR => zlor x y
  | .XOR => zlxor x y
  | .SRL => zshiftr x (zland y 63).toNat
  | .SLL => land64 (zshiftl x (zland y 63).toNat)
  | .SLTU => if x < y then 1 else 0
  | _ => zalu op x y

/-- The 32-bit variant. -/
def zfastw (op : AluOp) (x y : Int) : Int :=
  match op with
  | .ADD => sx32 (land32 (x + y))
  | .SUB => sx32 (land32 (x - y))
  | .SRL => sx32 (zshiftr (land32 x) (zland y 31).toNat)
  | .SLL => sx32 (land32 (zshiftl (land32 x) (zland y 31).toNat))
  | _ => zaluw op x y

/-- The M-extension variant. -/
def zfastm (op : MulOp) (x y : Int) : Int :=
  match op with
  | .MUL => land64 (x * y)
  | _ => zmd op x y

/-- PERF: byte-slice extraction of a CANONICAL literal with shifts and masks
    only (`= zext_lit`, `AxSymExec3Sound.zext_fast_eq`). -/
def zext_fast (sx : Bool) (lo n : Nat) (x : Int) : Int :=
  let k := (8 * (n : Int))
  let u := zland (zshiftr x (8 * lo)) (zones (8 * n))
  if sx then
    match n with
    -- this module's `bv_swrap` spells the half-modulus `2 ^ (n - 1)`
    -- with `Nat` subtraction, so `bv_swrap 0 0 = -1` where `bv_modulus n / 2` would give `0`.
    -- `zext_lit` goes through `ext_Z`/`bv_swrap` and therefore yields
    -- `2 ^ 64 - 1` at width 0; the fast path matches it here so that
    -- `zext_fast_eq`'s conclusion and `evalS_eq` hold without a side
    -- condition.  The executor never builds a zero-width extension.
    | 0 => wrap64 (u - 1)
    | _ => if u < zshiftl 1 (k - 1).toNat then wrap64 u
           else wrap64 (u - zshiftl 1 k.toNat + two64)
  else wrap64 u

/-- PERF: literal folding in `mkAlu`/`mkAluw`/`mkMd` without the bitvector
    round trip: canonicalise both literals (`wrap64`) and use the
    plain-Z operators `zfast`/`zfastw`/`zfastm`.  Equal to
    `zalu`/`zaluw`/`zmd` for ALL arguments
    (`AxSymExec3Sound.zalu_l_eq`, `zaluw_l_eq`, `zmd_l_eq`). -/
def zalu_l (op : AluOp) (x y : Int) : Int := zfast op (wrap64 x) (wrap64 y)

/-- See `zalu_l`. -/
def zaluw_l (op : AluOp) (x y : Int) : Int := zfastw op (wrap64 x) (wrap64 y)

/-- See `zalu_l`. -/
def zmd_l (op : MulOp) (x y : Int) : Int := zfastm op (wrap64 x) (wrap64 y)

/-- A linear form: constant + coefficient/atom terms. -/
abbrev lin : Type := Int × List (Int × expr)

/-- Constructor index, for the ordering of values with different heads. -/
def ctor_ix : expr → Nat
  | .ELit _ => 0
  | .EVar _ => 1
  | .EAlu _ _ _ => 2
  | .EAluw _ _ _ => 3
  | .EMd _ _ _ => 4
  | .EMdw _ _ _ => 5
  | .EExt _ _ _ _ => 6
  | .EBlob _ _ _ _ => 7

/-- ALU-op index, for `expr_cmp`. -/
def aluop_ix : AluOp → Nat
  | .ADD => 0
  | .SUB => 1
  | .SLL => 2
  | .SLT => 3
  | .SLTU => 4
  | .XOR => 5
  | .SRL => 6
  | .SRA => 7
  | .OR => 8
  | .AND => 9

/-- M-op index, for `expr_cmp`. -/
def mulop_ix : MulOp → Nat
  | .MUL => 0
  | .MULH => 1
  | .MULHSU => 2
  | .MULHU => 3
  | .DIV => 4
  | .DIVU => 5
  | .REM => 6
  | .REMU => 7

/-- `bool` index, for `expr_cmp`. -/
def bool_ix (b : Bool) : Nat := if b then 1 else 0

/-- `lexc`: take the first non-`Eq` comparison in a chain. -/
def lexc (c k : Ordering) : Ordering := match c with | .eq => k | _ => c

/-- The canonical ordering of symbolic values (what keeps linear forms
    sorted). -/
def expr_cmp (x : expr) : expr → Ordering
  | .ELit b => match x with | .ELit a => compare a b | _ => compare (ctor_ix x) (ctor_ix (.ELit b))
  | .EVar b => match x with | .EVar a => compare a b | _ => compare (ctor_ix x) (ctor_ix (.EVar b))
  | .EAlu o a b => match x with
      | .EAlu o' a' b' => lexc (compare (aluop_ix o') (aluop_ix o)) (lexc (expr_cmp a' a) (expr_cmp b' b))
      | _ => compare (ctor_ix x) (ctor_ix (.EAlu o a b))
  | .EAluw o a b => match x with
      | .EAluw o' a' b' => lexc (compare (aluop_ix o') (aluop_ix o)) (lexc (expr_cmp a' a) (expr_cmp b' b))
      | _ => compare (ctor_ix x) (ctor_ix (.EAluw o a b))
  | .EMd o a b => match x with
      | .EMd o' a' b' => lexc (compare (mulop_ix o') (mulop_ix o)) (lexc (expr_cmp a' a) (expr_cmp b' b))
      | _ => compare (ctor_ix x) (ctor_ix (.EMd o a b))
  | .EMdw o a b => match x with
      | .EMdw o' a' b' => lexc (compare (mulop_ix o') (mulop_ix o)) (lexc (expr_cmp a' a) (expr_cmp b' b))
      | _ => compare (ctor_ix x) (ctor_ix (.EMdw o a b))
  | .EExt s l n e => match x with
      | .EExt s' l' n' e' =>
          lexc (compare (bool_ix s') (bool_ix s))
            (lexc (compare l' l) (lexc (compare n' n) (expr_cmp e' e)))
      | _ => compare (ctor_ix x) (ctor_ix (.EExt s l n e))
  | .EBlob s k i n => match x with
      | .EBlob s' k' i' n' =>
          lexc (compare (bool_ix s') (bool_ix s))
            (lexc (compare k' k) (lexc (compare i' i) (compare n' n)))
      | _ => compare (ctor_ix x) (ctor_ix (.EBlob s k i n))

/-- Insert `k*a` into a sorted term list (coefficients combine on
    syntactically equal atoms — `expr_eqb`, which is what soundness uses). -/
def lins (k : Int) (a : expr) : List (Int × expr) → List (Int × expr)
  | [] => if snorm k == 0 then [] else [(snorm k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        let s := snorm (k + k')
        if s == 0 then rest else (s, a') :: rest
      else match expr_cmp a a' with
           | .lt => if snorm k == 0 then (k', a') :: rest else (snorm k, a) :: (k', a') :: rest
           | _ => (k', a') :: lins k a rest

/-- Sum of two linear forms. -/
def ladd (x y : lin) : lin :=
  (snorm (x.1 + y.1), x.2.foldr (fun t acc => lins t.1 t.2 acc) y.2)

/-- Scale a term list. -/
def lscale_terms (m : Int) : List (Int × expr) → List (Int × expr)
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k)
      if k' == 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest

/-- Scale a linear form. -/
def lscale (m : Int) (x : lin) : lin := (snorm (m * x.1), lscale_terms m x.2)

/-- View any expression as a linear form (structural; atoms are leaves). -/
def lin_of (e : expr) : lin :=
  match e with
  | .ELit z => (snorm z, [])
  | .EAlu .ADD a b => ladd (lin_of a) (lin_of b)
  | .EAlu .SUB a b => ladd (lin_of a) (lscale (-1) (lin_of b))
  | .EAlu .SLL a (.ELit s) => lscale (zpow 2 (s % 64)) (lin_of a)
  | .EMd .MUL (.ELit k) a => lscale k (lin_of a)
  | .EMd .MUL a (.ELit k) => lscale k (lin_of a)
  | _ => (0, [(1, e)])

/-- One linear term back as an expression. -/
def lterm (t : Int × expr) : expr :=
  if t.1 == 1 then t.2 else .EMd .MUL (.ELit t.1) t.2

/-- A term list back as an expression. -/
def lterms : List (Int × expr) → expr
  | [] => .ELit 0
  | [t] => lterm t
  | t :: rest => .EAlu .ADD (lterm t) (lterms rest)

/-- A linear form back as an expression. -/
def unlin (x : lin) : expr :=
  match x.2 with
  | [] => .ELit x.1
  | _ => if x.1 == 0 then lterms x.2 else .EAlu .ADD (lterms x.2) (.ELit x.1)

/-- Low `k` bits of a linear form are a LITERAL when every coefficient is
    a multiple of `2^k`: `(c + Σ ki·ai) mod 2^k = c mod 2^k`. -/
def coeffs_div (m : Int) : List (Int × expr) → Bool
  | [] => true
  | (k, _) :: rest => (k % m == 0) && coeffs_div m rest

/-- The low `k` bits of `e`, as a literal, when they are constant. -/
def lin_lowbits (e : expr) (k : Int) : Option Int :=
  let l := lin_of e
  if coeffs_div (zpow 2 k) l.2 then some (l.1 % zpow 2 k) else none

/-- A shift amount is usable when its low 6 (resp. 5) bits are literal. -/
def shamt_of (e : expr) (bits : Int) : Option Int :=
  match e with
  | .ELit s => some (s % zpow 2 bits)
  | _ => lin_lowbits e bits

/-- The smart ALU constructor (constant folding plus linear normal forms). -/
def mkAlu (op : AluOp) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zalu_l op x y)
  | _, _ =>
    match op with
    | .ADD => unlin (ladd (lin_of a) (lin_of b))
    | .SUB => unlin (ladd (lin_of a) (lscale (-1) (lin_of b)))
    | .SLL => match shamt_of b 6 with
              | some s => unlin (lscale (zpow 2 s) (lin_of a))
              | none => .EAlu op a b
    | .SRL | .SRA =>
        match is_lit b with
        | some _ => .EAlu op a b
        | none => match shamt_of b 6 with
                  | some s => .EAlu op a (.ELit s)
                  | none => .EAlu op a b
    | _ => .EAlu op a b

/-- The smart 32-bit ALU constructor. -/
def mkAluw (op : AluOp) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zaluw_l op x y)
  | _, _ =>
      match op with
      | .SLL | .SRL | .SRA =>
          match is_lit b with
          | some _ => .EAluw op a b
          | none => match shamt_of b 5 with
                    | some s => match is_lit a with
                                | some x => .ELit (zaluw_l op x s)
                                | none => .EAluw op a (.ELit s)
                    | none => .EAluw op a b
      | _ => .EAluw op a b

/-- The smart M-extension constructor. -/
def mkMd (op : MulOp) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zmd_l op x y)
  | some x, none => match op with | .MUL => unlin (lscale x (lin_of b)) | _ => .EMd op a b
  | none, some y => match op with | .MUL => unlin (lscale y (lin_of a)) | _ => .EMd op a b
  | _, _ => .EMd op a b

/-- The smart 32-bit M-extension constructor. -/
def mkMdw (op : MulOp) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zmdw op x y)
  | _, _ => .EMdw op a b

/-- Byte-slice extraction.  A full-width slice of a value is the value;
    a slice of a literal folds; a slice of a zero-extended slice composes. -/
def mkExt (sx : Bool) (lo n : Nat) (e : expr) : expr :=
  match e with
  | .ELit x => .ELit (zext_fast sx lo n (wrap64 x))
  | _ =>
    if (lo == 0 && n == 8) then e
    else match e with
         | .EExt false lo' n' e' =>
             if (lo + n ≤ n' && n' ≤ 8) then .EExt sx (lo' + lo) n e'
             else .EExt sx lo n e
         | _ => .EExt sx lo n e

/-! ## 2. Registers -/

/-- Register index. -/
def ridx (r : reg) : Nat := (bv_unsigned r).toNat

/-- Read a symbolic register (`x0` is hardwired to zero). -/
def sr_get (sr : List expr) (r : reg) : expr :=
  if bv_eqb r 0 then .ELit 0 else sr.getD (ridx r) (.ELit 0)

/-- Write a symbolic register. -/
def sr_upd (sr : List expr) : Nat → expr → List expr
  | 0, e => match sr with | [] => [e] | _ :: t => e :: t
  | n + 1, e => match sr with
                | [] => .ELit 0 :: sr_upd [] n e
                | h :: t => h :: sr_upd t n e

/-- The identity register file: register `i` is the variable `i`. -/
def sr_id : List expr :=
  [.EVar 0, .EVar 1, .EVar 2, .EVar 3, .EVar 4, .EVar 5, .EVar 6, .EVar 7,
   .EVar 8, .EVar 9, .EVar 10, .EVar 11, .EVar 12, .EVar 13, .EVar 14, .EVar 15,
   .EVar 16, .EVar 17, .EVar 18, .EVar 19, .EVar 20, .EVar 21, .EVar 22, .EVar 23,
   .EVar 24, .EVar 25, .EVar 26, .EVar 27, .EVar 28, .EVar 29, .EVar 30, .EVar 31]

/-! ## 3. Symbolic memory -/

/-- Address normal form: base expression (no literal addend) + literal. -/
structure saddr where
  /-- the base expression -/
  a_base : expr
  /-- the literal offset -/
  a_off : Int
  deriving DecidableEq, Repr

/-- `SA` — the record constructor. -/
abbrev SA (b : expr) (k : Int) : saddr := ⟨b, k⟩

/-- Split an expression into (base, literal offset). -/
def split_lit (e : expr) : expr × Int :=
  match e with
  | .ELit z => (.ELit 0, z)
  | .EAlu .ADD b (.ELit z) => (b, z)
  | _ => (e, 0)

/-- Normalise `e + imm` into an `saddr`. -/
def to_saddr (e : expr) (imm : Int) : saddr :=
  let (b, k) := split_lit e
  SA b (k + imm)

/-- Denotation of an address. -/
def adenot (E : env) (a : saddr) : word :=
  v_addi (edenot E a.a_base) a.a_off

/-- Syntactic equality of addresses. -/
def saddr_eqb (a b : saddr) : Bool :=
  expr_eqb a.a_base b.a_base && (a.a_off == b.a_off)

/-- In-block store log entry: `w` LE bytes of `v` at `a`. -/
structure sentry where
  /-- the address -/
  e_addr : saddr
  /-- the width in bytes -/
  e_width : Nat
  /-- the stored value -/
  e_val : expr
  deriving DecidableEq, Repr

/-- `SE` — the record constructor. -/
abbrev SE (a : saddr) (w : Nat) (v : expr) : sentry := ⟨a, w, v⟩

/-- Knowledge about the BASE memory of the block. -/
inductive kentry : Type
  /-- base holds `word_to_le_bytes w v` at `a` -/
  | KWord (a : saddr) (w : Nat) (v : expr)
  /-- base holds `n` zero bytes at `a` -/
  | KZero (a : saddr) (n : expr)
  /-- base holds byte string `k`, of length `n`, at `a` -/
  | KBlob (a : saddr) (n : expr) (k : Nat)
  /-- base overlay undefined on `[lo,hi)`: reads see the image -/
  | KImg (lo hi : Int)
  /-- not about memory: `bv_unsigned e mod m = 0` -/
  | KAlign (e : expr) (m : Int)
  /-- not about memory: `lo <= bv_unsigned e <= hi` -/
  | KRange (e : expr) (lo hi : Int)
  /-- every sub-range of `a, a+n` is writable (`store_ok`); `n` may be
      symbolic (its value, a length < 2^64) -/
  | KWr (a : saddr) (n : expr)
  /-- not about contents: the Z-intervals `a1,a1+n1` and `a2,a2+n2` (of
      `estart`; lengths = values of n1/n2) do not overlap -/
  | KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
  /-- base holds `n` copies of the byte `Z_to_bv 8 c` at `a`; `n` may be
      symbolic (like `KZero`, which is the case c = 0).  Appended (not
      inserted) on purpose: numbered case analyses over `kentry` keep
      their order. -/
  | KFill (a : saddr) (n : expr) (c : Int)
  /-- the bytes `a, a+n` are DEFINED in the base overlay (mapped:
      readable and writable) but arbitrary; `n` may be symbolic.  Reads
      inside produce a fresh variable in extension mode (`sym_stepX`). -/
  | KUnk (a : saddr) (n : expr)
  deriving DecidableEq, Repr

/-- Side conditions (obligations handed back to the caller). -/
inductive sidecond : Type
  /-- a branch was decided as `taken` -/
  | SCBr (taken : Bool) (c : BranchCond) (a b : expr)
  /-- `0 <= base+off` and `base+off+n <= 2^64` -/
  | SCFlat (a : saddr) (n : expr)
  /-- ranges disjoint (both flat) -/
  | SCDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
  /-- `a1,a1+n1` inside `a2,a2+n2` -/
  | SCInside (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
  /-- against the BASE memory -/
  | SCStoreOk (a : saddr) (n : Nat)
  /-- base read of n bytes denotes e -/
  | SCReadBase (a : saddr) (n : Nat) (sx : Bool) (e : expr)
  /-- two expressions denote the same word -/
  | SCEq (a b : expr)
  deriving DecidableEq, Repr

/-- The symbolic state. -/
structure sym_state where
  /-- the symbolic program counter -/
  s_pc : Int
  /-- the symbolic register file -/
  s_regs : List expr
  /-- the store log, newest first -/
  s_log : List sentry
  /-- knowledge about the base memory -/
  s_know : List kentry
  /-- next fresh word-variable index -/
  s_next : Nat
  /-- live LR reservation: `none` at every block boundary -/
  s_resv : Option saddr
  deriving DecidableEq, Repr

/-- `SS` — the historical 5-field constructor: a state with NO live
    reservation.  A parametric abbreviation (elaborates to the record
    constructor `SSR ... none`), so every existing `SS pc regs log kn nx`
    in the plan checker / certificates / drivers parses, computes and
    reduces exactly as before. -/
abbrev SS (p : Int) (r : List expr) (l : List sentry) (k : List kentry) (n : Nat) : sym_state :=
  ⟨p, r, l, k, n, none⟩

/-- Write a register and set the pc. -/
def sset (ss : sym_state) (rd : reg) (e : expr) (npc : Int) : sym_state :=
  ⟨npc, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) e),
   ss.s_log, ss.s_know, ss.s_next, ss.s_resv⟩

/-- Jump. -/
def sjump (ss : sym_state) (npc : Int) : sym_state :=
  ⟨npc, ss.s_regs, ss.s_log, ss.s_know, ss.s_next, ss.s_resv⟩

/-- Forget the reservation. -/
def clr (ss : sym_state) : sym_state :=
  ⟨ss.s_pc, ss.s_regs, ss.s_log, ss.s_know, ss.s_next, none⟩

/-- Test the reservation. -/
def s_clean (ss : sym_state) : Bool :=
  match ss.s_resv with | none => true | some _ => false

/-! ### Range questions -/

/-- Outcome of comparing a READ range against a known range. -/
inductive rangerel : Type
  /-- inside, at this offset -/
  | RInside (delta : Int)
  /-- disjoint -/
  | RDisjoint
  /-- partially overlapping -/
  | RPartial
  /-- undecided -/
  | RUnknown
  deriving DecidableEq, Repr

/-- Same syntactic base and literal lengths: decided.  Otherwise unknown. -/
def rel_lit (rb : expr) (rk : Int) (rn : Int) (kb : expr) (kk : Int) (kn : Int) : rangerel :=
  if expr_eqb rb kb then
    if (kk ≤ rk && rk + rn ≤ kk + kn) then .RInside (rk - kk)
    else if (rk + rn ≤ kk || kk + kn ≤ rk) then .RDisjoint
    else .RPartial
  else .RUnknown

/-- `ELit (Z.of_nat n)`. -/
def elen (n : Nat) : expr := .ELit (n : Int)

/-- Split off a literal addend. -/
def lit_strip (e : expr) : expr × Int :=
  match e with
  | .EAlu .ADD v (.ELit c) => (v, c)
  | _ => (e, 0)

/-- Interval bounds of a base expression: literals are exact, other
    expressions through a `KRange` fact.  SHIFTED match: a fact about
    `v + c'` also bounds `v + c` (same non-literal part `v`, literal
    offsets; the executor's linear normal form is `EAlu ALU_ADD v (ELit
    c)`), provided the shifted interval stays inside `0, 2^64`. -/
def find_range (kn : List kentry) (e : expr) : Option (Int × Int) :=
  match kn with
  | [] => none
  | .KRange e' lo hi :: rest =>
      if expr_eqb e e' then some (lo, hi)
      else
        match e with
        | .ELit _ => find_range rest e
        | _ =>
          let (v, c) := lit_strip e
          let (v', c') := lit_strip e'
          if expr_eqb v v' then
            let d := c - c'
            if (0 ≤ lo && lo ≤ hi && hi < 2 ^ 64 && 0 ≤ lo + d && hi + d < 2 ^ 64)
            then some (lo + d, hi + d) else find_range rest e
          else find_range rest e
  | _ :: rest => find_range rest e

/-- Alignment facts: `KAlign e m` says `bv_unsigned e mod m = 0`. -/
def find_align (kn : List kentry) (e : expr) : Option Int :=
  match kn with
  | [] => none
  | .KAlign e' m :: rest => if expr_eqb e e' then some m else find_align rest e
  | _ :: rest => find_align rest e

/-- `erange kn e = some (lo, hi)`: the unsigned value of `e` lies in
    `lo, hi` under any valuation validating `kn`.  A `KRange` fact about
    `e` itself wins; otherwise intervals are propagated bottom-up through
    the operations whose unsigned result is monotone/affine when no
    wrap-around can happen.  Everything is decided in `Int`. -/
def clampi (r : Int × Int) : Int × Int :=
  let (lo, hi) := r
  (max lo 0, min hi two64m1)

/-- Smallest `2^k - 1` (k <= 64) covering `h`. -/
def mask_cover (h : Int) : Int :=
  if h < 0 then 0 else zpow 2 (zlog2_up (h + 1)) - 1

/-- The literal low 6 bits of a shift amount. -/
def lit_shamt (e : expr) : Option Int :=
  match e with | .ELit s => some (s % 64) | _ => none

/-- A literal addend read as a SIGNED quantity (for `addi x, -16` style
    sums): `v` in `2^63, 2^64` stands for `v - 2^64`. -/
def zsigned64 (v : Int) : Int := if two63z ≤ v then v - two64 else v

/-- Interval of a linear form evaluated in `Int` with SIGNED coefficients:
    sound whenever the resulting interval shows no wrap-around. -/
def lin_range (rng : expr → Option (Int × Int)) (c : Int) :
    List (Int × expr) → Option (Int × Int)
  | [] => some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | some (al, ah), some (lo, hi) =>
          if 0 ≤ k then some (lo + k * al, hi + k * ah)
          else some (lo + k * ah, hi + k * al)
      | _, _ => none

/-- Is the linear form exactly one atom with coefficient 1? -/
def lin_trivial (l : lin) : Bool :=
  match l with
  | (c, [(k, _)]) => (c == 0 && k == 1)
  | _ => false

/-- Floor log base 2 (`0` for `z <= 0`). -/
def zlog2 (z : Int) : Int := if z ≤ 0 then 0 else (Nat.log2 z.toNat : Int)

/-- `erange_f`: the interval domain, by fuel. -/
def erange_f : Nat → List kentry → expr → Option (Int × Int)
  | 0, _, _ => none
  | fuel + 1, kn, e =>
    let erange := erange_f fuel kn
    match find_range kn e with
    | some r => some (clampi r)
    | none =>
      match (let l := lin_of e
             if lin_trivial l then none
             else
               match lin_range erange l.1 l.2 with
               | some (lo, hi) =>
                   let q := zdiv64 lo
                   if q == zdiv64 hi then some (lo - q * two64, hi - q * two64) else none
               | none => none) with
      | some r => some r
      | none =>
        match e with
        | .ELit z => let v := zmod64 z; some (v, v)
        | .EVar _ => none
        | .EAlu op a b =>
            match op with
            | .ADD =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if ah + bh < two64 then some (al + bl, ah + bh)
                    else if two64 ≤ al + bl then some (al + bl - two64, ah + bh - two64)
                    else none
                | _, _ => none
            | .SUB =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if bh ≤ al then some (al - bh, ah - bl)
                    else if ah < bl then some (al - bh + two64, ah - bl + two64)
                    else none
                | _, _ => none
            | .AND =>
                -- mask 2^j-1 on a range that crosses no multiple of 2^j:
                -- exact residues; mask -2^j: both bounds rounded down to a
                -- multiple of 2^j (monotone)
                match (match b, erange a with
                       | .ELit m, some (al, ah) =>
                           let m' := m % two64
                           let j := zlog2 (m' + 1)
                           if (m' + 1 == zpow 2 j && al / zpow 2 j ≤ ah / zpow 2 j &&
                               al / zpow 2 j == ah / zpow 2 j)
                           then some (al % zpow 2 j, ah % zpow 2 j)
                           else
                             let jh := zlog2 (two64 - m')
                             if (two64 - m' == zpow 2 jh && jh < 64)
                             then some (al - al % zpow 2 jh, ah - ah % zpow 2 jh)
                             else none
                       | _, _ => none) with
                | some r => some r
                | none =>
                  match erange a, erange b with
                  | some (_, ah), some (_, bh) => some (0, min ah bh)
                  | some (_, ah), none => some (0, ah)
                  | none, some (_, bh) => some (0, bh)
                  | none, none => none
            | .OR =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) => some (max al bl, mask_cover (max ah bh))
                | _, _ => none
            | .XOR =>
                match erange a, erange b with
                | some (_, ah), some (_, bh) => some (0, mask_cover (max ah bh))
                | _, _ => none
            | .SRL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s => some (al / zpow 2 s, ah / zpow 2 s)
                | _, _ => none
            | .SRA =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    if ah < zpow 2 63 then some (al / zpow 2 s, ah / zpow 2 s) else none
                | _, _ => none
            | .SLL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    if ah * zpow 2 s < two64 then some (al * zpow 2 s, ah * zpow 2 s) else none
                | _, _ => none
            | .SLTU =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if ah < bl then some (1, 1)
                    else if bh ≤ al then some (0, 0) else some (0, 1)
                | _, _ => some (0, 1)
            | .SLT =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (ah < zpow 2 63 && bh < zpow 2 63) then
                      (if ah < bl then some (1, 1)
                       else if bh ≤ al then some (0, 0) else some (0, 1))
                    else some (0, 1)
                | _, _ => some (0, 1)
        | .EAluw op a b =>
            match op with
            | .ADD =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    let bl' := if bl == bh then zsigned64 bl else bl
                    let bh' := if bl == bh then zsigned64 bh else bh
                    if (0 ≤ al + bl' && ah + bh' < zpow 2 31)
                    then some (al + bl', ah + bh') else none
                | _, _ => none
            | .SUB =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (bh ≤ al && ah - bl < zpow 2 31) then some (al - bh, ah - bl) else none
                | _, _ => none
            | .SLL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if ah * zpow 2 s' < zpow 2 31 then some (al * zpow 2 s', ah * zpow 2 s')
                    else none
                | _, _ => none
            | .SRL =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if (ah < zpow 2 32 && (0 < s' || ah < zpow 2 31))
                    then some (al / zpow 2 s', ah / zpow 2 s') else none
                | _, _ => none
            | .SRA =>
                match erange a, lit_shamt b with
                | some (al, ah), some s =>
                    let s' := s % 32
                    if ah < zpow 2 31 then some (al / zpow 2 s', ah / zpow 2 s') else none
                | _, _ => none
            | _ => none
        | .EMd op a b =>
            match op with
            | .MUL =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (0 ≤ al && 0 ≤ bl && ah * bh < two64) then some (al * bl, ah * bh) else none
                | _, _ => none
            | .MULHU =>
                match erange a, erange b with
                | some (al, ah), some (bl, bh) =>
                    if (0 ≤ al && 0 ≤ bl) then some (al * bl / two64, ah * bh / two64) else none
                | _, _ => none
            | .DIVU =>
                match erange a, b with
                | some (al, ah), .ELit d =>
                    let d' := d % two64
                    if 0 < d' then some (al / d', ah / d') else none
                | _, _ => none
            | .REMU =>
                match erange a, b with
                | some (al, ah), .ELit d =>
                    let d' := d % two64
                    if 0 < d' then some (0, min ah (d' - 1)) else none
                | _, _ => none
            | _ => none
        | .EMdw _ _ _ => none
        | .EExt sx lo n a =>
            let w := zpow 2 (8 * (n : Int))
            if sx then
              match lo, erange a with
              | 0, some (al, ah) =>
                  if (0 ≤ al && ah < w / 2) then some (al, ah)
                  else if (1 ≤ n && n ≤ 8 && w / 2 ≤ al && ah < w)
                       then some (two64 - w + al, two64 - w + ah) else none
              | _, _ => none
            else
              match lo, erange a with
              | 0, some (al, ah) =>
                  if (0 ≤ al && ah < w) then some (al, ah) else some (0, min (w - 1) two64m1)
              | _, _ => some (0, min (w - 1) two64m1)
        | .EBlob sx _ _ n =>
            -- a sign-extended blob slice is still a word
            if sx then some (0, two64m1)
            else some (0, min (zpow 2 (8 * (n : Int)) - 1) two64m1)

/-- The fuel constant is OPAQUE to the tactic reduction machinery
    (cbn/simpl in the soundness proofs must never unfold 64 levels of
    `erange_f`); `vm_compute` ignores opacity and computes it normally. -/
def erange_fuel : Nat := 64

attribute [local irreducible] erange_fuel

/-- PERF: the interval/alignment domains consult only `KRange`/`KAlign`
    facts; pre-filtering them out of the (long) knowledge list makes every
    `find_range`/`find_align` scan short. -/
def is_factb : kentry → Bool
  | .KRange _ _ _ | .KAlign _ _ | .KDisj _ _ _ _ | .KWr _ _ => true
  | _ => false

/-- PERF (s3): `facts_of` is called by every `erange`/`xlo`/`xhi` entry
    point, and most callers already pass a facts-only list (the per-store /
    per-instruction `fk`); re-filtering such a list allocated a fresh copy
    on every call (the hottest allocation site of the whole checker).
    Return the list itself when it is already facts-only: same RESULT as
    filtering (`facts_of_filter`), no allocation. -/
def all_factsb : List kentry → Bool
  | [] => true
  | K :: rest => if is_factb K then all_factsb rest else false

/-- The facts in a knowledge list. -/
def facts_of (kn : List kentry) : List kentry :=
  if all_factsb kn then kn else kn.filter is_factb

/-- `facts_of` filtering when the list is already facts-only. -/
theorem all_factsb_filter : ∀ kn : List kentry,
    all_factsb kn = true → kn.filter is_factb = kn
  | [], _ => rfl
  | K :: rest, H => by
      cases h : is_factb K with
      | false => simp [all_factsb, h] at H
      | true => simp [all_factsb, h, all_factsb_filter rest (by simpa [all_factsb, h] using H)]

/-- `facts_of` is filtering, definitionally. -/
theorem facts_of_filter (kn : List kentry) : facts_of kn = kn.filter is_factb := by
  unfold facts_of
  by_cases h : all_factsb kn = true
  · rw [ite_eq_left h]
    exact (all_factsb_filter kn h).symm
  · rw [ite_eq_right h]

/-- `erange0`: the interval domain on the facts of a knowledge list. -/
def erange0 (kn : List kentry) (e : expr) : Option (Int × Int) :=
  erange_f erange_fuel (facts_of kn) e

/-- Align-down atoms inside a sum (as `APC.deand`):
    `deand e = (e', s)` replaces every `x AND -2^j` (j <= 48) reachable
    through `ALU_ADD` nodes by `x`; then `u e = u e' - rho (mod 2^64)` for
    some `0 <= rho <= s`, so a bound `lo', hi'` of `e'` with `s <= lo'`
    bounds `e` by `lo' - s, hi'` — the relational facts about the
    UNROUNDED sum (e.g. a shadow address before RoundDown) bound the
    rounded one. -/
def deand (e : expr) : expr × Int :=
  match e with
  | .EAlu .AND x (.ELit m) =>
      let m' := m % two64
      let j := zlog2 (two64 - m')
      if (two64 - m' == zpow 2 j && j ≤ 48)
      then let (x', s) := deand x; (x', s + (zpow 2 j - 1))
      else (e, 0)
  | .EAlu .ADD a b =>
      let (a', s1) := deand a
      let (b', s2) := deand b
      (.EAlu .ADD a' b', s1 + s2)
  | _ => (e, 0)

/-- `erange`: `erange0` tightened by the align-down atoms (R4.2). -/
def erange (kn : List kentry) (e : expr) : Option (Int × Int) :=
  let r := erange0 kn e
  let (e', s) := deand e
  if s == 0 then r
  else
    match erange0 kn (unlin (lin_of e')) with
    | some (lo', hi') =>
        if s ≤ lo' then
          match r with
          | some (lo, hi) => some (max lo (lo' - s), min hi hi')
          | none => some (lo' - s, hi')
        else r
    | none => r

/-- PERF (s3): a literal base needs no knowledge. -/
def base_range (kn : List kentry) (e : expr) : Option (Int × Int) :=
  match e with
  | .ELit z => let v := z % two64; some (v, v)
  | _ => erange kn e

/-! ### Alignment domain -/

/-- `ctz64 z`: number of trailing zero bits of `z` (capped at 64; 64 for 0). -/
def ctz_fuel : Nat → Int → Int
  | 0, _ => 0
  | f + 1, z => if z % 2 == 0 then 1 + ctz_fuel f (z / 2) else 0

/-- Trailing zeros, 64 bits' worth. -/
def ctz64 (z : Int) : Int := ctz_fuel 64 z

/-- The fact-free (`find_align` miss) half of `ealign0`; this tree writes it
    as the `None` branch of the same fixpoint, split out here so that the
    structural recursion is on `e` alone. -/
def ealign0_nofact (kn : List kentry) : expr → Int
  | .ELit z => ctz64 (z % two64)
  | .EAlu .ADD a b => min (ealign0_nofact kn a) (ealign0_nofact kn b)
  | .EAlu .SUB a b => min (ealign0_nofact kn a) (ealign0_nofact kn b)
  | .EAlu .AND a b => max (ealign0_nofact kn a) (ealign0_nofact kn b)
  | .EAlu .OR a b => min (ealign0_nofact kn a) (ealign0_nofact kn b)
  | .EAlu .SLL a b =>
      match lit_shamt b with
      | some s => min (ealign0_nofact kn a + s) 64
      | none => 0
  | .EMd .MUL a b => min (ealign0_nofact kn a + ealign0_nofact kn b) 64
  | _ => 0

/-- `ealign kn e = k`: `2^k` divides the unsigned value of `e`
    (`0 <= k <= 64`; 0 = no information). -/
def ealign0 (kn : List kentry) (e : expr) : Int :=
  match find_align kn e with
  | some m => if 0 < m then ctz64 m else 0
  | none => ealign0_nofact kn e

/-- Exact (integer, un-normalized) term-list arithmetic, for reasoning
    about DIFFERENCES of addresses in `Int` (no modular wrap allowed). -/
def lins_e (k : Int) (a : expr) : List (Int × expr) → List (Int × expr)
  | [] => if k == 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        let s := k + k'
        if s == 0 then rest else (s, a') :: rest
      else (k', a') :: lins_e k a rest

/-- `ts1 - ts2`, exactly. -/
def lsub_e (ts2 ts1 : List (Int × expr)) : List (Int × expr) :=
  ts1.foldr (fun t acc => lins_e (-t.1) t.2 acc) ts2

/-- Page rounding recognised (J3e): a linear form `c + (y AND mm) - y`
    (musl's `x + ((-x-20) & 4095) + 20` = pageup(x+20)) is congruent to
    `c + c_y` modulo `mm+1`, hence modulo every power of two m dividing
    `mm+1`.  `pageup_low e m = some r`: `u e mod m = r`;
    `pageup_align e = k` when the whole form is a multiple of `2^k = mm+1`.
    `sg = +1`: the page-UP idiom above; `sg = -1`: the dual align-up idiom
    `c + y - (y AND mm)` (compiler-rt's
    `start += align - (start & (align-1))`), congruent to `c - c_y`. -/
def find_and_atom_k (sg : Int) : List (Int × expr) → Option (expr × Int)
  | [] => none
  | (k, .EAlu .AND y (.ELit mm)) :: r =>
      if (k == sg && 0 < mm && zland (mm + 1) mm == 0) then some (y, mm)
      else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r

/-- The `+1` idiom. -/
def find_and_atom (ts : List (Int × expr)) : Option (expr × Int) := find_and_atom_k 1 ts

/-- `pageup_low_k`: the residue of the page-up form modulo `m`. -/
def pageup_low_k (sg : Int) (e : expr) (m : Int) : Option Int :=
  let l := lin_of e
  match find_and_atom_k sg l.2 with
  | some (y, mm) =>
      if (0 < m && (mm + 1) % m == 0 && mm + 1 ≤ two64) then
        let ly := lin_of y
        let rest := lins_e (-sg) (.EAlu .AND y (.ELit mm)) l.2
        match rest.foldr (fun t acc => lins_e (sg * t.1) t.2 acc) ly.2 with
        | [] => some ((l.1 + sg * ly.1) % m)
        | _ => none
      else none
  | none => none

/-- The `+1` idiom first (results unchanged where it applied), then the dual. -/
def pageup_low (e : expr) (m : Int) : Option Int :=
  match pageup_low_k 1 e m with
  | some r => some r
  | none => pageup_low_k (-1) e m

/-- `pageup_align`: the power of two the whole form is a multiple of. -/
def pageup_align (e : expr) : Int :=
  let l := lin_of e
  match (match find_and_atom_k 1 l.2 with
         | some p => some p
         | none => find_and_atom_k (-1) l.2) with
  | some (y, mm) =>
      let m := mm + 1
      let k := ctz64 m
      if (m == zpow 2 k && k ≤ 64) then
        match pageup_low e m with | some 0 => k | _ => 0
      else 0
  | none => 0

/-- `ealign`: the alignment domain. -/
def ealign (kn : List kentry) (e : expr) : Int :=
  max (ealign0 (facts_of kn) e) (pageup_align e)

/-- The linear form of `e` provably does not wrap around 2^64. -/
def lin_nowrap (kn : List kentry) (e : expr) : Bool :=
  let l := lin_of e
  match lin_range (erange kn) l.1 l.2 with
  | some (lo, hi) => (0 ≤ lo && hi < two64)
  | none => false

/-- Page-rounding made linear: a term `k * SRL(e, s)` with `2^s | k` and
    `e` a non-wrapping linear form equals
    `(k/2^s) * e - (k/2^s) * (e AND (2^s-1))` EXACTLY
    (`u (e AND (m-1)) = u e mod m`); the remainder atom has range
    `0, 2^s-1` for `erange`, and plans may sharpen it with a
    KRange/PSplit. -/
def srl_rem (e : expr) (m : Int) : expr := .EAlu .AND e (.ELit (m - 1))

/-- The mask of a high-AND atom `e AND -2^s` as written by the executor
    (`ELit` of `-2^s` or of `2^64 - 2^s`); `none` if the literal is not
    such a mask with `0 < s < 64`. -/
def highmask_s (mk : Int) : Option Int :=
  let m' := mk % two64
  let s := zlog2 (two64 - m')
  if (two64 - m' == zpow 2 s && 0 < s && s < 64) then some s else none

/-- Expand SRL atoms (and high-AND atoms) of a term list into linear form. -/
def srl_expand (kn : List kentry) : List (Int × expr) → Int × List (Int × expr)
  | [] => (0, [])
  | (k, a) :: rest =>
      let (c, ts') := srl_expand kn rest
      let keep := (c, lins_e k a ts')
      match a with
      | .EAlu .SRL e (.ELit s) =>
          let m := zpow 2 ((s % two64) % 64)
          if (k % m == 0 && lin_nowrap kn e) then
            let q := k / m
            let le := lin_of e
            if (s % two64) % 64 ≤ ealign kn e then
              -- exact: e is a multiple of m (J3e)
              (c + q * le.1, le.2.foldr (fun t acc => lins_e (q * t.1) t.2 acc) ts')
            else
              (c + q * le.1,
               lins_e (-q) (srl_rem e m) (le.2.foldr (fun t acc => lins_e (q * t.1) t.2 acc) ts'))
          else keep
      | .EAlu .AND e (.ELit mk) =>
          -- the align-down atom `e AND -2^s` = `e - (e AND (2^s-1))`
          -- exactly, for ANY coefficient — so that `2^s * SRL(e,s)` and
          -- `e AND -2^s` (two spellings of the same rounding,
          -- `and_high_split` produces the latter) expand to the same form
          -- and cancel
          match highmask_s mk with
          | some s =>
              if lin_nowrap kn e then
                let le := lin_of e
                (c + k * le.1,
                 lins_e (-k) (srl_rem e (zpow 2 s))
                   (le.2.foldr (fun t acc => lins_e (k * t.1) t.2 acc) ts'))
              else keep
          | none => keep
      | _ => keep

/-- NESTED page rounding — `4096 * SRL(8 * SRL(v+7,3) + 8191, 12)` against
    `8 * SRL(v+7,3)`: one pass of `srl_expand` expands the atoms of the
    ORIGINAL list only, so the inner atom re-introduced by the outer
    expansion stays opaque and no longer cancels against the (already
    expanded) copy that stood in the list itself.  A second pass over the
    result expands the re-introduced atoms too (`lins_e` then
    merges/cancels equal atoms).  Used as a further attempt only where the
    one-pass form failed, so every comparison the one-pass form proves
    stays provable. -/
def has_srl : List (Int × expr) → Bool
  | [] => false
  | (_, .EAlu .SRL _ (.ELit _)) :: _ => true
  | _ :: rest => has_srl rest

/-! *** Relational bounds from KRange facts on COMPOSITE linear forms
    ("sum facts", J2-b).  A fact `KRange e lo hi` whose `lin_of e`
    has >= 2 atoms (e.g. `n + cfglen + 6 ∈ [6, 65535]`) bounds every
    multiple `q * (e - c_e)` occurring inside a linear form far better than
    the per-atom intervals.  `lin_test kn c ts test` bounds `c + Σ ts` with
    the plain per-atom interval first and, only when `test` fails on it AND
    some fact's atoms all occur in `ts` with proportional coefficients,
    retries with those atoms replaced by the fact's interval. -/

/-- A digested fact: atoms (of `lin_of e`) plus an interval. -/
abbrev sfact : Type := List (Int × expr) × (Int × Int)

/-- The srl-expanded version of a digested fact (J3c): `lin_ge0` bounds
    srl-expanded forms, so a fact on `4096*SRL(n+4115,12) - n - 16*off`
    must also be available as one on `4099 - rem - 16*off`. -/
def sum_fact_x (allkn : List kentry) (ts : List (Int × expr)) (lo hi : Int) : List sfact :=
  let (c2, ts2) := srl_expand allkn ts
  match ts2 with
  | _ :: _ => if c2 == 0 then [] else [(ts2, (lo - c2, hi - c2))]
  | [] => []

/-- A KRange fact `lo <= u e <= hi` pins the LINEAR FORM of `e` (not just
    its value mod 2^64) when the form's plain interval `a,b` allows no
    other representative: `b < 2^64` and `hi < a + 2^64` (J3d). -/
def fact_nowrap (allkn : List kentry) (e : expr) (hi : Int) : Bool :=
  let l := lin_of e
  match lin_range (erange allkn) l.1 l.2 with
  | some (a, b) => (b < two64 && hi < a + two64)
  | none => false

/-- The digested facts of a knowledge list. -/
def sum_facts (allkn kn : List kentry) : List sfact :=
  match kn with
  | [] => []
  | .KRange e lo hi :: rest =>
      match e with
      | .EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, ts@(_ :: _ :: _)) =>
            if fact_nowrap allkn e hi
            then (ts, (lo - c, hi - c)) ::
                 (sum_fact_x allkn ts (lo - c) (hi - c) ++ sum_facts allkn rest)
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
  | _ :: rest => sum_facts allkn rest

/-- Coefficient of atom `a` in `ts` (0 when absent). -/
def coef_of (a : expr) : List (Int × expr) → Int
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r

/-- The common nonzero quotient `q` with `coef_of a ts = q * k` for every
    fact term `(k, a)`, if the fact occurs proportionally in `ts`. -/
def fact_quot (fts ts : List (Int × expr)) (acc : Option Int) : Option Int :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if k == 0 then none
      else
        let K := coef_of a ts
        if K == 0 then none
        else if !(K % k == 0) then none
        else
          let q := K / k
          match acc with
          | none => fact_quot r ts (some q)
          | some q0 => if q0 == q then fact_quot r ts acc else none

/-- Subtract `q * fts` from `ts`. -/
def sub_fact (q : Int) (fts ts : List (Int × expr)) : List (Int × expr) :=
  fts.foldr (fun t acc => lins_e (-(q * t.1)) t.2 acc) ts

/-- Greedily apply the facts: residual terms, accumulated interval of the
    replaced part, and whether anything matched. -/
def sum_subst (fs : List sfact) (ts : List (Int × expr)) (lo hi : Int) (hit : Bool) :
    List (Int × expr) × (Int × Int) × Bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quot fts ts none with
      | some q =>
          let ts' := sub_fact q fts ts
          if 0 ≤ q then sum_subst r ts' (lo + q * flo) (hi + q * fhi) true
          else sum_subst r ts' (lo + q * fhi) (hi + q * flo) true
      | none => sum_subst r ts lo hi hit

/-- `lin_test_rel`: the relational interval of `c + Σ ts`. -/
def lin_test_rel (kn : List kentry) (c : Int) (ts : List (Int × expr))
    (test : Int → Int → Bool) : Bool :=
  match sum_facts kn kn with
  | [] => false
  | fs =>
      match sum_subst fs ts 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) c ts' with
          | some (lo, hi) => test (lo + lo0) (hi + hi0)
          | none => false
      | _ => false

/-- `lin_test`: per-atom interval first, then the relational retry. -/
def lin_test (kn : List kentry) (c : Int) (ts : List (Int × expr))
    (test : Int → Int → Bool) : Bool :=
  match lin_range (erange kn) c ts with
  | some (lo, hi) => if test lo hi then true else lin_test_rel kn c ts test
  | none => lin_test_rel kn c ts test

/-- Interval of a linear form whose SRL atoms become expandable only after
    SCALING by `2^j` — "difference of two roundings of the same quantity in
    shadow units", e.g. `512*SRL(X,12) - 512 - SRL(v+7,3)` with
    `X = 8*SRL(v+7,3) + 8191`: times 8 it is
    `4096*SRL(X,12) - 4096 - 8*SRL(v+7,3)`, which `srl_expand` (two passes)
    turns into `4095 - (X AND 4095)` in `0, 4095`, hence the form lies in
    `0, 511`.  The scaled Z-interval divided back (ceiling / floor); valid
    as the VALUE's interval when inside `0, 2^64`. -/
def srl_scale_need : List (Int × expr) → Int
  | [] => 0
  | (k, .EAlu .SRL _ (.ELit s)) :: rest =>
      max (((s % two64) % 64) - ctz64 k) (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest

/-- Ceiling division. -/
def zcdiv (a b : Int) : Int := -((-a) / b)

/-- The scaled-interval bound of a linear form. -/
def lin_srange (kn : List kentry) (e : expr) : Option (Int × Int) :=
  let l := lin_of e
  let j := srl_scale_need l.2
  if (0 ≤ j && j ≤ 24) then
    -- j = 0 too — the plain two-pass expansion interval
    let sc := zpow 2 j
    let ts := l.2.map (fun t => (sc * t.1, t.2))
    let (c2, t2) := srl_expand kn ts
    let (c3, t3) := (if has_srl t2 then srl_expand kn t2 else ((0 : Int), t2))
    match lin_range (erange kn) (sc * l.1 + c2 + c3) t3 with
    | some (lo', hi') =>
        let lo := zcdiv lo' sc
        let hi := hi' / sc
        if (0 ≤ lo && (lo ≤ hi && hi < two64)) then some (lo, hi) else none
    | none => none
  else none

/-- No-wrap of a linear form, with the relational step (J3): e.g. the
    reserved length `stride-4-n-16*off` of a slot is >= 0 only by the sum
    fact `16*off + n <= stride-4`, not by the atoms' own ranges. -/
def lin_nowrapR (kn : List kentry) (e : expr) : Bool :=
  let l := lin_of e
  let (c2, t2) := srl_expand kn l.2   -- J3g: page-rounded forms
  if lin_test kn (l.1 + c2) t2 (fun lo hi => (0 ≤ lo && hi < two64)) then true
  else -- the scaled two-pass expansion interval proves no-wrap too
    match lin_srange kn e with | some _ => true | none => false

/-- PERF prefilter: an exact linear comparison between two bases can
    only succeed when they mention a common variable (or both are closed);
    `vm_compute` is call-by-value, so guard the expensive decision with it. -/
def mentions_var (v : Nat) : expr → Bool
  | .ELit _ => false
  | .EVar w => v == w
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b =>
      if mentions_var v a then true else mentions_var v b
  | .EExt _ _ _ a => mentions_var v a
  | .EBlob _ _ _ _ => false

/-- Do the two expressions mention a common variable? -/
def shares_var (e1 : expr) : expr → Bool
  | .ELit _ => false
  | .EVar w => mentions_var w e1
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b =>
      if shares_var e1 a then true else shares_var e1 b
  | .EExt _ _ _ a => shares_var e1 a
  | .EBlob _ _ _ _ => false

/-- Is the expression closed? -/
def novars : expr → Bool
  | .ELit _ => true
  | .EVar _ => false
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b =>
      if novars a then novars b else false
  | .EExt _ _ _ a => novars a
  | .EBlob _ _ _ _ => true

/-- `b2` is the CONTAINER side: a literal-based container (image, ceiling
    window) can hold a symbolic range; a symbolic container never provably
    holds an unrelated range. -/
def related (b1 b2 : expr) : Bool :=
  if shares_var b1 b2 then true else novars b2

/-- Two ranges `b1+k1, +n1` and `b2+k2, +n2` are apart when the exact
    difference of their starts, as a linear form, is bounded away. -/
def lin_apart0 (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
  (let l1 := lin_of b1
   let l2 := lin_of b2
   lin_test kn (l2.1 + k2 - l1.1 - k1) (lsub_e l2.2 l1.2)
     (fun lo hi => (n1 ≤ lo || hi ≤ -n2)))

/-- `lin_apart`, guarded by the shared-variable prefilter. -/
def lin_apart (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  if shares_var b1 b2 then lin_apart0 kn b1 k1 n1 b2 k2 n2 else false

/-- A literal's value (the cheap test first: `vm_compute` evaluates
    eagerly). -/
def zlit64 (z : Int) : Int := if (0 ≤ z && z < two64) then z else z % two64

/-- Relational interval of a linear form (J3b): sum facts substituted; it
    is the VALUE's interval when it shows no wrap.  Used by `xlo`/`xhi`
    when `erange` fails (e.g. the reserved length
    `stride-4-n-16*off`). -/
def lin_brange (kn : List kentry) (e : expr) : Option (Int × Int) :=
  let l := lin_of e
  match sum_facts kn kn with
  | [] => none
  | fs =>
      match sum_subst fs l.2 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) l.1 ts' with
          | some (lo, hi) =>
              let lo' := lo + lo0
              let hi' := hi + hi0
              if (0 ≤ lo' && hi' < two64) then some (lo', hi') else none
          | none => none
      | _ => none

/-- Lower numeric bound of an expression. -/
def xlo (kn : List kentry) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
      match erange kn e with
      | some (lo, _) => some lo
      | none =>
          match lin_brange kn e with
          | some (lo, _) => some lo
          | none => match lin_srange kn e with | some (lo, _) => some lo | none => none

/-- Upper numeric bound of an expression. -/
def xhi (kn : List kentry) (e : expr) : Option Int :=
  match e with
  | .ELit z => some (zlit64 z)
  | _ =>
      match erange kn e with
      | some (_, hi) => some hi
      | none =>
          match lin_brange kn e with
          | some (_, hi) => some hi
          | none => match lin_srange kn e with | some (_, hi) => some hi | none => none

/-! ### Exact linear comparisons with SYMBOLIC lengths -/

/-- A sum of offset terms: `(e, k)` denotes `bv_unsigned (edenot E e) + k`. -/
abbrev xterms : Type := List (expr × Int)

/-- Every term's base does not wrap. -/
def xt_nowrap (kn : List kentry) : xterms → Bool
  | [] => true
  | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r

/-- The literal part of a sum of offset terms. -/
def xt_const : xterms → Int
  | [] => 0
  | (e, k) :: r => (lin_of e).1 + k + xt_const r

/-- The term list of a sum of offset terms. -/
def xt_lin : xterms → List (Int × expr)
  | [] => []
  | (e, _) :: r => (lin_of e).2.foldr (fun t acc => lins_e t.1 t.2 acc) (xt_lin r)

/-- Last resort of `lin_ge0` — the form SCALED by `2^j` so that every
    `k * SRL(_, s)` term becomes expandable (shadow-unit roundings), two
    expansion passes. -/
def lin_ge0_scaled (kn : List kentry) (c : Int) (ts : List (Int × expr)) : Bool :=
  let j := srl_scale_need ts
  if (0 < j && j ≤ 24) then
    let sc := zpow 2 j
    let ts' := ts.map (fun t => (sc * t.1, t.2))
    let (c2, t2) := srl_expand kn ts'
    let (c3, t3) := (if has_srl t2 then srl_expand kn t2 else ((0 : Int), t2))
    lin_test kn (sc * c + c2 + c3) t3 (fun lo _ => 0 ≤ lo)
  else false

/-- `Σ pos - Σ neg >= 0` holds for every valuation satisfying `kn`. -/
def lin_ge0 (kn : List kentry) (pos neg : xterms) : Bool :=
  xt_nowrap kn pos && xt_nowrap kn neg &&
  -- plain form first (a point-range SRL atom beats its expansion), then
  -- srl-expanded (F17)
  (if lin_test kn (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg))
        (fun lo _ => 0 ≤ lo) then true
   else
     let (c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg))
     if lin_test kn (xt_const pos - xt_const neg + c2) t2 (fun lo _ => 0 ≤ lo) then true
     else -- nested roundings — second expansion pass, only when atoms to
          -- expand remain
       if (if has_srl t2 then
             let (c3, t3) := srl_expand kn t2
             lin_test kn (xt_const pos - xt_const neg + c2 + c3) t3 (fun lo _ => 0 ≤ lo)
           else false) then true
       else -- scaled expansion
         lin_ge0_scaled kn (xt_const pos - xt_const neg) (lsub_e (xt_lin pos) (xt_lin neg)))

/-- Containment of `b1+k1, +n1` in `b2+k2, +n2`, lengths symbolic. -/
def xinside0 (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)]
  then lin_ge0 kn [(b2, k2), (n2, 0)] [(b1, k1), (n1, 0)]
  else false

/-- Numeric containment (literal-based container): bounds only, no algebra. -/
def xinside_num (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match xlo kn b2, xhi kn b2 with
  | some lo2, some hi2 =>
      if lo2 == hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | some (lo1, hi1), some h1, some l2 =>
            (lo2 + k2 ≤ lo1 + k1) && (hi1 + k1 + h1 ≤ lo2 + k2 + l2)
        | _, _, _ => false
      else false
  | _, _ => false

/-- `xinside`: containment of symbolic ranges. -/
def xinside (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then xinside_num kn b1 k1 n1 b2 k2 n2 else false

/-- `b+k, b+k+n` (n literal) lies inside `c, c + m` where `m` is a length
    EXPRESSION: against its lower bound.  (Nested `if`s: under `vm_compute`
    `&&` evaluates both sides, and `xlo` of a symbolic length is not
    cheap.) -/
def sub_itv (allkn : List kentry) (b : expr) (k n : Int) (c : saddr) (m : expr) : Bool :=
  if (if (expr_eqb b c.a_base && c.a_off ≤ k) then
        match xlo allkn m with
        | some ml => k + n ≤ c.a_off + ml
        | none => false
      else false)
  then true
  else -- other spelling of the base: exact linear containment
    if (0 ≤ n && n < two64) then xinside allkn b k (.ELit n) c.a_base c.a_off m else false

/-- A recorded `KDisj` fact separates the two ranges (each inside one side). -/
def kdisj_apart (allkn kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  match kn with
  | [] => false
  | .KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2

/-- `ranges_apart`: literal-length apartness. -/
def ranges_apart (kn : List kentry) (b1 : expr) (k1 n1 : Int) (b2 : expr) (k2 n2 : Int) : Bool :=
  if (match base_range kn b1, base_range kn b2 with
      | some (lo1, hi1), some (lo2, hi2) =>
          (hi1 + k1 + n1 ≤ lo2 + k2 || hi2 + k2 + n2 ≤ lo1 + k1)
      | _, _ => false) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apart kn b1 k1 n1 b2 k2 n2

/-- Containment test of a symbolic length range in a `KDisj` side. -/
def sub_itv_x (kn : List kentry) (b : expr) (k : Int) (n : expr) (c : saddr) (m : expr) : Bool :=
  xinside kn b k n c.a_base c.a_off m

/-- `kdisj_apart` with symbolic lengths. -/
def kdisj_apart_x (allkn kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match kn with
  | [] => false
  | .KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2

/-- The END of a SYMBOLIC-length range `b+k, +n` through a JOINT fact
    `KRange (b + k + n) _ ehi` (as `mmap_null` records for a symbolic
    length: base + len <= CEIL — with only the separate ranges of base and
    length the bound base_hi + len_hi overshoots by the class width).
    Valid as an integer bound when the sum provably does not wrap. -/
def end_hi (kn : List kentry) (b : expr) (k : Int) (n : expr) (lo1 hi1 h1 : Int) : Option Int :=
  match n with
  | .ELit _ => none
  | _ =>
      if (if 0 ≤ lo1 + k then hi1 + k + h1 < two64 else false) then
        match find_range (facts_of kn) (mkAlu .ADD (mkAlu .ADD b (.ELit k)) n) with
        | some (_, ehi) => some ehi
        | none => none
      else none

/-- `some e <= y`, `false` for `none` (the END-fact test, used twice). -/
def le_end (x : Option Int) (y : Int) : Bool :=
  match x with | some e => e ≤ y | none => false

/-- The numeric-bounds part of `ranges_apart_x` (with the joint END facts). -/
def num_apart (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
  | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
      if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
      else -- joint END facts of symbolic-length ranges
      if le_end (end_hi kn b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
      else le_end (end_hi kn b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
  | _, _, _, _ => false

/-- Apartness of `b1+k1, +n1` and `b2+k2, +n2`, lengths symbolic: the
    literal decision when both lengths are literals, else numeric bounds,
    a recorded KDisj, or the exact linear difference. -/
def ranges_apart_x (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if num_apart kn b1 k1 n1 b2 k2 n2 then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2), (n2, 0)]

/-! *** P2: store-side preparation.
    `prune` tests ONE store range `b1+k1, +w` against every knowledge
    entry; the parts of `ranges_apart_x` that depend only on the store —
    its base range and, for the KDisj scan, WHICH recorded sides contain
    the store — are computed once per store (`mk_sprep`) instead of once
    per entry.  `AxSymExec3Sound.ranges_apart_p_eq`: the prepared test IS
    `ranges_apart_x` (boolean equality), so `prune`/`carry` results are
    unchanged by theorem. -/

/-- Prepared store-side facts. -/
structure sprep where
  /-- `base_range kn b1` -/
  sp_rng : Option (Int × Int)
  /-- `xhi kn n1` -/
  sp_h1 : Option Int
  /-- KDisj sides whose partner side contains the store (literal lengths) -/
  sp_D : List (saddr × expr)
  /-- the same with `sub_itv_x` (lengths as expressions) -/
  sp_Dx : List (saddr × expr)
  deriving DecidableEq, Repr

/-- `SPrep` — the record constructor. -/
abbrev SPrep (r : Option (Int × Int)) (h : Option Int)
    (d : List (saddr × expr)) (dx : List (saddr × expr)) : sprep := ⟨r, h, d, dx⟩

/-- The `KDisj` partners of the sides that contain the store. -/
def disj_sides (allkn kn : List kentry) (b1 : expr) (k1 : Int) (n1 : Int) : List (saddr × expr) :=
  match kn with
  | [] => []
  | .KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1

/-- The same with symbolic lengths. -/
def disj_sides_x (allkn kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) :
    List (saddr × expr) :=
  match kn with
  | [] => []
  | .KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1

/-- Does one of the prepared sides contain the other range? -/
def in_sides (allkn : List kentry) (D : List (saddr × expr)) (b2 : expr) (k2 n2 : Int) : Bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2

/-- The symbolic-length variant. -/
def in_sides_x (allkn : List kentry) (D : List (saddr × expr)) (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2

/-- Prepare the store-side facts once per store. -/
def mk_sprep (kn : List kentry) (b1 : expr) (k1 : Int) (n1 : expr) : sprep :=
  SPrep (base_range kn b1) (xhi kn n1)
        (match n1 with | .ELit z1 => disj_sides kn kn b1 k1 (zlit64 z1) | _ => [])
        (disj_sides_x kn kn b1 k1 n1)

/-- The prepared numeric-bounds test (the `sp`-side of `ranges_apart_x`). -/
def num_apart_p (kn : List kentry) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match sp.sp_rng, base_range kn b2, sp.sp_h1, xhi kn n2 with
  | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
      if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
      else -- joint END facts of symbolic-length ranges
      if le_end (end_hi kn b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
      else le_end (end_hi kn b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
  | _, _, _, _ => false

/-- `= ranges_apart_x kn b1 k1 n1 b2 k2 n2` when `sp = mk_sprep kn b1 k1 n1`. -/
def ranges_apart_p (kn : List kentry) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 =>
      let m1 := zlit64 z1
      let m2 := zlit64 z2
      if (match sp.sp_rng, base_range kn b2 with
          | some (lo1, hi1), some (lo2, hi2) =>
              (hi1 + k1 + m1 ≤ lo2 + k2 || hi2 + k2 + m2 ≤ lo1 + k1)
          | _, _ => false) then true
      else if in_sides kn sp.sp_D b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if num_apart_p kn sp b1 k1 n1 b2 k2 n2 then true
    else if in_sides_x kn sp.sp_Dx b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2), (n2, 0)]

/-! ### Positive tries (moved here from the instruction-table section)

    The trie is keyed by `Nat` — `xH = 0`, `xO k = 2k+1`, `xI k = 2k+2`
    decoded on the fly — which is the same dictionary under the same
    binary branching, and keeps `pt_gss`/`pt_gso` stated at `Nat`
    equality (what `mk_itab_fuel_sound` needs). -/

/-- A binary trie. -/
inductive ptree (A : Type) : Type
  /-- empty -/
  | PTLeaf : ptree A
  /-- left subtree, optional value, right subtree -/
  | PTNode : ptree A → Option A → ptree A → ptree A

/-- Trie lookup (`k = 0` is `xH`, `2m+1` is `xO m`, `2m+2` is `xI m`). -/
def pt_get {A : Type} : ptree A → Nat → Option A
  | .PTLeaf, _ => none
  | .PTNode _ o _, 0 => o
  | .PTNode l _ r, n + 1 => if n % 2 == 0 then pt_get l (n / 2) else pt_get r (n / 2)
termination_by _ k => k
decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.div_le_self _ _)

/-- Trie insertion. -/
def pt_set {A : Type} : Nat → A → ptree A → ptree A
  | 0, v, .PTLeaf => .PTNode .PTLeaf (some v) .PTLeaf
  | 0, v, .PTNode l _ r => .PTNode l (some v) r
  | n + 1, v, .PTLeaf =>
      if n % 2 == 0 then .PTNode (pt_set (n / 2) v .PTLeaf) none .PTLeaf
      else .PTNode .PTLeaf none (pt_set (n / 2) v .PTLeaf)
  | n + 1, v, .PTNode l o r =>
      if n % 2 == 0 then .PTNode (pt_set (n / 2) v l) o r
      else .PTNode l o (pt_set (n / 2) v r)
termination_by k _ _ => k
decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.div_le_self _ _)
/-! ### Load resolution -/

/-- Result of resolving a load. -/
inductive lres : Type
  /-- a hit: the value, the side conditions, the consumed hints -/
  | LHit (v : expr) (scs : List sidecond) (hints : List Bool)
  /-- nothing in log/knowledge covers it -/
  | LMiss (scs : List sidecond) (hints : List Bool)
  /-- stuck -/
  | LStuck
  deriving DecidableEq, Repr

/-- Little-endian bytes to an `Int`. -/
def zbytes_le_to_Z : List Int → Int
  | [] => 0
  | b :: rest => zlor b (zshiftl (zbytes_le_to_Z rest) 8)

/-- The literal `n` bytes denote. -/
def lit_of_bytes (sx : Bool) (n : Nat) (bs : List Int) : expr :=
  .ELit (let u := zbytes_le_to_Z bs
         if sx then bv_swrap (8 * n) u else u)

/-- (P-b) One byte at `rb+rk` out of the store log, when the newest
    SAME-BASE entry covering it holds a LITERAL: byte `d` of that literal.
    `none` = not covered by the log, covered by a non-literal, or preceded
    by an entry of another base (undecided aliasing). -/
def log_byte_lit (log : List sentry) (rb : expr) (rk : Int) : Option Int :=
  match log with
  | [] => none
  | ⟨⟨kb, kk⟩, w, v⟩ :: rest =>
      match rel_lit rb rk 1 kb kk (w : Int) with
      | .RInside d =>
          match v with
          | .ELit z => some (((z % two64) / zpow 2 (8 * d)) % 256)
          | _ => none
      | .RDisjoint => log_byte_lit rest rb rk
      | _ => none

/-- `n` consecutive such bytes. -/
def log_bytes_lit (log : List sentry) (rb : expr) (rk : Int) : Nat → Option (List Int)
  | 0 => some []
  | n + 1 =>
      match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n with
      | some b, some r => some (b :: r)
      | _, _ => none

/-- Walk the store log (newest first).  Same base: decide by offsets
    (hit inside one entry, skip if disjoint; a read PARTIALLY overlapping
    an entry is composed bytewise from literal entries of the log
    (`log_bytes_lit`), else stuck).  Other base: consume a hint — `true`
    (or no hint) = assume disjoint (emit `SCDisj`), `false` = stuck
    (aliasing through a different spelling is not modelled: pin the
    register to the canonical spelling instead). -/
def log_lookup (kn : List kentry) (log : List sentry) (rb : expr) (rk : Int) (n : Nat) (sx : Bool)
    (hints : List Bool) (acc : List sidecond) : lres :=
  match log with
  | [] => .LMiss acc hints
  | ⟨⟨kb, kk⟩, w, v⟩ :: rest =>
      match rel_lit rb rk (n : Int) kb kk (w : Int) with
      | .RInside d => .LHit (mkExt sx d.toNat n v) acc hints
      | .RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | .RPartial =>
          match log_bytes_lit log rb rk n with
          | some bs => .LHit (lit_of_bytes sx n bs) acc hints
          | none => .LStuck
      | .RUnknown =>
          if ranges_apart kn rb rk (n : Int) kb kk (w : Int)
          then log_lookup kn rest rb rk n sx hints acc
          else
            match hints with
            | false :: _ => .LStuck
            | _ => log_lookup kn rest rb rk n sx hints.tail
                     (.SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)

/-- Read `n` image bytes at absolute address `a` (every byte must come
    from a readable segment: `seg_rom`). -/
def img_bytes (segs : List Segment) (a : Int) : Nat → Option (List Int)
  | 0 => some []
  | n + 1 =>
      match seg_rom segs (Z_to_bv 64 a) with
      | some b => match img_bytes segs (a + 1) n with
                  | some r => some (bv_unsigned b :: r)
                  | none => none
      | none => none

/-- The literal an `n`-byte read of bytes all equal to `c` denotes. -/
def fill_lit (sx : Bool) (n : Nat) (c : Int) : expr :=
  lit_of_bytes sx n (List.replicate n (c % 256))

/-- One byte at `rb+rk` out of LITERAL knowledge of the same base
    SPELLING: a `KWord` holding a literal, a literal-length `KZero` /
    `KFill`, or — for the absolute base `ELit 0` — an untouched image byte
    (`KImg` + `seg_rom`).  `none`: no such entry covers the byte.  (All
    knowledge entries hold simultaneously, so unlike the log there is no
    order to respect: the first covering entry is as good as any.) -/
def know_byte_lit (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int) : Option Int :=
  match kn with
  | [] => none
  | K :: rest =>
      match K with
      | .KWord ⟨kb, kk⟩ w (.ELit z) =>
          match rel_lit rb rk 1 kb kk (w : Int) with
          | .RInside d => some (((z % two64) / zpow 2 (8 * d)) % 256)
          | _ => know_byte_lit segs rest rb rk
      | .KZero ⟨kb, kk⟩ (.ELit l0) =>
          match rel_lit rb rk 1 kb kk (l0 % two64) with
          | .RInside _ => some 0
          | _ => know_byte_lit segs rest rb rk
      | .KFill ⟨kb, kk⟩ (.ELit l0) c =>
          match rel_lit rb rk 1 kb kk (l0 % two64) with
          | .RInside _ => some (c % 256)
          | _ => know_byte_lit segs rest rb rk
      | .KImg lo hi =>
          match rb with
          | .ELit 0 =>
              if (lo ≤ rk && rk < hi) then
                match seg_rom segs (Z_to_bv 64 rk) with
                | some b => some (bv_unsigned b)
                | none => none -- undefined AND outside the image: unreadable
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
      | _ => know_byte_lit segs rest rb rk

/-- `n` consecutive such bytes. -/
def know_bytes_lit (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int) :
    Nat → Option (List Int)
  | 0 => some []
  | n + 1 =>
      match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n with
      | some b, some r => some (b :: r)
      | _, _ => none

/-- Insertion reads back. -/
theorem pt_gss {A : Type} (k : Nat) (v : A) (t : ptree A) :
    pt_get (pt_set k v t) k = some v := by
  revert t
  refine Nat.strongRecOn k (fun k ih t => ?_)
  cases k with
  | zero =>
      cases t with
      | PTLeaf => rw [pt_set.eq_1, pt_get.eq_2]
      | PTNode l o r => rw [pt_set.eq_2, pt_get.eq_2]
  | succ n =>
      cases t with
      | PTLeaf =>
          rw [pt_set.eq_3]
          by_cases h : (n % 2 == 0) = true
          · rw [ite_eq_left h, pt_get.eq_3, ite_eq_left h]
            exact ih (n / 2) (by omega) _
          · rw [ite_eq_right h, pt_get.eq_3, ite_eq_right h]
            exact ih (n / 2) (by omega) _
      | PTNode l o r =>
          rw [pt_set.eq_4]
          by_cases h : (n % 2 == 0) = true
          · rw [ite_eq_left h, pt_get.eq_3, ite_eq_left h]
            exact ih (n / 2) (by omega) _
          · rw [ite_eq_right h, pt_get.eq_3, ite_eq_right h]
            exact ih (n / 2) (by omega) _

/-- Two keys with the same parity and the same half are equal (the
    `pt_gso` parity step). -/
theorem eq_of_div2_eq {n m : Nat} (h : n % 2 = m % 2) (he : n / 2 = m / 2) : n = m := by
  have hn := Nat.mod_add_div n 2
  have hm := Nat.mod_add_div m 2
  omega

/-- Insertion preserves every other key. -/
theorem pt_gso {A : Type} (k k' : Nat) (v : A) (t : ptree A) (H : k ≠ k') :
    pt_get (pt_set k' v t) k = pt_get t k := by
  have main : ∀ (k : Nat) (t : ptree A) (k' : Nat), k ≠ k' →
      pt_get (pt_set k' v t) k = pt_get t k := by
    intro k
    refine Nat.strongRecOn k (fun k ih => ?_)
    intro t k' H
    cases k with
    | zero =>
        cases k' with
        | zero => exact absurd rfl H
        | succ m =>
            cases t with
            | PTLeaf =>
                rw [pt_set.eq_3]
                by_cases h : (m % 2 == 0) = true
                · rw [ite_eq_left h, pt_get.eq_2, pt_get.eq_1]
                · rw [ite_eq_right h, pt_get.eq_2, pt_get.eq_1]
            | PTNode l o r =>
                rw [pt_set.eq_4]
                by_cases h : (m % 2 == 0) = true
                · rw [ite_eq_left h, pt_get.eq_2, pt_get.eq_2]
                · rw [ite_eq_right h, pt_get.eq_2, pt_get.eq_2]
    | succ n =>
        cases k' with
        | zero =>
            cases t with
            | PTLeaf =>
                rw [pt_set.eq_1, pt_get.eq_3]
                by_cases h : (n % 2 == 0) = true
                · rw [ite_eq_left h, pt_get.eq_1, pt_get.eq_1]
                · rw [ite_eq_right h, pt_get.eq_1, pt_get.eq_1]
            | PTNode l o r =>
                rw [pt_set.eq_2, pt_get.eq_3]
                by_cases h : (n % 2 == 0) = true
                · rw [ite_eq_left h, pt_get.eq_3, ite_eq_left h]
                · rw [ite_eq_right h, pt_get.eq_3, ite_eq_right h]
        | succ m =>
            cases t with
            | PTLeaf =>
                rw [pt_set.eq_3]
                by_cases h : (n % 2 == 0) = true
                · by_cases h' : (m % 2 == 0) = true
                  · rw [ite_eq_left h', pt_get.eq_3, ite_eq_left h, pt_get.eq_1]
                    by_cases he : n / 2 = m / 2
                    · have hnm : n = m := eq_of_div2_eq (by
                        have h1 : n % 2 = 0 := by simpa using h
                        have h2 : m % 2 = 0 := by simpa using h'
                        omega) he
                      exact absurd (by omega) H
                    · rw [ih (n / 2) (by omega) .PTLeaf (m / 2) he, pt_get.eq_1]
                  · rw [ite_eq_right h', pt_get.eq_3, ite_eq_left h, pt_get.eq_1, pt_get.eq_1]
                · by_cases h' : (m % 2 == 0) = true
                  · rw [ite_eq_left h', pt_get.eq_3, ite_eq_right h, pt_get.eq_1, pt_get.eq_1]
                  · rw [ite_eq_right h', pt_get.eq_3, ite_eq_right h, pt_get.eq_1]
                    by_cases he : n / 2 = m / 2
                    · have hnm : n = m := eq_of_div2_eq (by
                        have h1 : n % 2 = 1 := by simpa using h
                        have h2 : m % 2 = 1 := by simpa using h'
                        omega) he
                      exact absurd (by omega) H
                    · rw [ih (n / 2) (by omega) .PTLeaf (m / 2) he, pt_get.eq_1]
            | PTNode l o r =>
                rw [pt_set.eq_4]
                by_cases h : (n % 2 == 0) = true
                · by_cases h' : (m % 2 == 0) = true
                  · rw [ite_eq_left h', pt_get.eq_3, ite_eq_left h, pt_get.eq_3, ite_eq_left h]
                    by_cases he : n / 2 = m / 2
                    · have hnm : n = m := eq_of_div2_eq (by
                        have h1 : n % 2 = 0 := by simpa using h
                        have h2 : m % 2 = 0 := by simpa using h'
                        omega) he
                      exact absurd (by omega) H
                    · exact ih (n / 2) (by omega) l (m / 2) he
                  · rw [ite_eq_right h', pt_get.eq_3, ite_eq_left h, pt_get.eq_3, ite_eq_left h]
                · by_cases h' : (m % 2 == 0) = true
                  · rw [ite_eq_left h', pt_get.eq_3, ite_eq_right h, pt_get.eq_3, ite_eq_right h]
                  · rw [ite_eq_right h', pt_get.eq_3, ite_eq_right h, pt_get.eq_3, ite_eq_right h]
                    by_cases he : n / 2 = m / 2
                    · have hnm : n = m := eq_of_div2_eq (by
                        have h1 : n % 2 = 1 := by simpa using h
                        have h2 : m % 2 = 1 := by simpa using h'
                        omega) he
                      exact absurd (by omega) H
                    · exact ih (n / 2) (by omega) r (m / 2) he
  exact main k t k' H

/-- The empty trie has nothing. -/
theorem pt_get_leaf {A : Type} (k : Nat) : pt_get (ptree.PTLeaf : ptree A) k = none :=
  @pt_get.eq_1 A k

/-- Bitwise complement at the 64-bit window. -/
def zlnot (z : Int) : Int := -z - 1

/-- Consult the knowledge list (order = priority).  For entries with a
    symbolic extent or a different base the hint script decides whether
    to CLAIM coverage (`true`: emit `SCInside`) or pass (`false`/none).
    `know_lookupA0` is the walk; `know_lookupA` (below) adds the bytewise
    literal composition when the walk finds no single covering entry. -/
def know_lookupA0 (allkn : List kentry) (segs : List Segment) (kn : List kentry) (rb : expr)
    (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  match kn with
  | [] => .LMiss acc hints
  | K :: rest =>
      match K with
      | .KWord ⟨kb, kk⟩ w v =>
          match rel_lit rb rk (n : Int) kb kk (w : Int) with
          | .RInside d => .LHit (mkExt sx d.toNat n v) acc hints
          | _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KZero ⟨kb, kk⟩ len =>
          match len with
          | .ELit l0 =>
              match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
              | .RInside _ => .LHit (.ELit 0) acc hints
              | .RDisjoint | .RPartial => know_lookupA0 allkn segs rest rb rk n sx hints acc
              | .RUnknown =>
                  -- containment modulo base spelling, by exact linear
                  -- arithmetic over the FULL knowledge
                  if xinside allkn rb rk (elen n) kb kk len then .LHit (.ELit 0) acc hints
                  else
                    match hints with
                    | true :: hs => .LHit (.ELit 0) (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                    | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then .LHit (.ELit 0) acc hints
              else
                match hints with
                | true :: hs => .LHit (.ELit 0) (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc
      | .KFill ⟨kb, kk⟩ len c =>
          -- exactly the KZero protocol; the hit value is the literal with
          -- all n bytes = c
          let hit := fill_lit sx n c
          match len with
          | .ELit l0 =>
              match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
              | .RInside _ => .LHit hit acc hints
              | .RDisjoint | .RPartial => know_lookupA0 allkn segs rest rb rk n sx hints acc
              | .RUnknown =>
                  if xinside allkn rb rk (elen n) kb kk len then .LHit hit acc hints
                  else
                    match hints with
                    | true :: hs => .LHit hit (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                    | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then .LHit hit acc hints
              else
                match hints with
                | true :: hs => .LHit hit (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc
      | .KUnk _ _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
          -- never a value; see `kn_readable`
      | .KBlob ⟨kb, kk⟩ len k =>
          if expr_eqb rb kb then
            -- same base: offset into the blob is the literal rk - kk
            if kk ≤ rk then
              match len with
              | .ELit l0 =>
                  if rk + (n : Int) ≤ kk + (l0 % two64)
                  then .LHit (.EBlob sx k (rk - kk) n) acc hints
                  else if kk + (l0 % two64) ≤ rk then know_lookupA0 allkn segs rest rb rk n sx hints acc
                  else .LStuck
              | _ =>
                  -- symbolic length: inside for every valuation (interval
                  -- domain over the later entries), else consult a hint
                  if (let ins : Bool := (match erange allkn len with -- perf: the FULL fact list
                                         | some (lo, _) => rk + (n : Int) ≤ kk + lo
                                         | none => false)
                      ins) then .LHit (.EBlob sx k (rk - kk) n) acc hints
                  else
                    match hints with
                    | true :: hs => .LHit (.EBlob sx k (rk - kk) n)
                                      (.SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                    | false :: hs => know_lookupA0 allkn segs rest rb rk n sx hs acc
                    | [] => know_lookupA0 allkn segs rest rb rk n sx [] acc
            else know_lookupA0 allkn segs rest rb rk n sx hints acc
          else know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KImg lo hi =>
          match rb with
          | .ELit 0 =>
              if (lo ≤ rk && rk + (n : Int) ≤ hi) then
                match img_bytes segs rk n with
                | some bs => .LHit (lit_of_bytes sx n bs) acc hints
                | none => .LStuck
              else know_lookupA0 allkn segs rest rb rk n sx hints acc
          | _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KAlign _ _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KRange _ _ _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KWr _ _ => know_lookupA0 allkn segs rest rb rk n sx hints acc
      | .KDisj _ _ _ _ => know_lookupA0 allkn segs rest rb rk n sx hints acc

/-- ... and when NO single entry covers the read (`LMiss`) but every one of
    its bytes is covered by literal knowledge of the same base spelling
    (`know_bytes_lit` over the whole list `kn`), the read is the composed
    literal.  Priority order unchanged: log, single knowledge entry,
    composition, `SCReadBase` fallback. -/
def know_lookupA (allkn : List kentry) (segs : List Segment) (kn : List kentry) (rb : expr)
    (rk : Int) (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | .LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | some bs => .LHit (lit_of_bytes sx n bs) acc' hints'
      | none => .LMiss acc' hints'
  | r => r

/-- The knowledge lookup on the state's own list. -/
def know_lookup (segs : List Segment) (kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) (sx : Bool) (hints : List Bool) (acc : List sidecond) : lres :=
  know_lookupA kn segs kn rb rk n sx hints acc

/-- Every term `k*a` of a linear form is a multiple of `m`, judging by the
    coefficient alone or by the coefficient times the atom's known
    alignment. -/
def coeffs_divk (kn : List kentry) (m : Int) : List (Int × expr) → Bool
  | [] => true
  | (k, a) :: rest =>
      ((k % m == 0 || (k * zpow 2 (ealign kn a)) % m == 0) && coeffs_divk kn m rest)

/-- The low `k` bits of `e` under the knowledge (J3e: page-rounded forms
    fall back to `pageup_low`). -/
def lin_lowbits_kn (kn : List kentry) (e : expr) (k : Int) : Option Int :=
  let l := lin_of e
  if coeffs_divk kn (zpow 2 k) l.2 then some (l.1 % zpow 2 k)
  else pageup_low e (zpow 2 k)

/-- Right shift of a linear form whose coefficients are multiples of `2^s`
    and whose constant is in `0, 2^s`: exact term-wise division, provided
    the form does not wrap (checked by `erange`). -/
def ldiv_terms (m : Int) : List (Int × expr) → List (Int × expr)
  | [] => []
  | (k, a) :: rest => (k / m, a) :: ldiv_terms m rest

/-- Split a term list by pure coefficient divisibility. -/
def lsplit_divc (m : Int) : List (Int × expr) → List (Int × expr) × List (Int × expr)
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest
      if k % m == 0 then ((k, a) :: d, r) else (d, (k, a) :: r)

/-- `lin_nowrap` of a linear form given directly. -/
def lin_nowrap_l (kn : List kentry) (c : Int) (ts : List (Int × expr)) : Bool :=
  match lin_range (erange kn) c ts with
  | some (lo, hi) => (0 ≤ lo && hi < two64)
  | none => false

/-- `mkSrl`: right shift of a symbolic value, kept linear where possible
    (`R3.3` for the partial split). -/
def mkSrl (kn : List kentry) (a : expr) (s : Int) : expr :=
  let l := lin_of a
  let m := zpow 2 s
  if (!(lin_trivial l) && coeffs_div m l.2 && lin_nowrap kn a)
  then unlin (l.1 / m, ldiv_terms m l.2) -- any constant: floor
  else
    -- only SOME terms divisible: A + R with the coefficients of A multiples
    -- of 2^s and R (rest + constant) provably in 0, 2^64 AND inside one
    -- 2^s-block q 2^s, (q+1) 2^s: (A + R) >> s = A/2^s + q — a linear form,
    -- no SRL atom.  (When R spans several blocks the whole shift stays ONE
    -- atom, so relational range facts about the unsplit sum keep applying.)
    match (if (!(lin_trivial l) && lin_nowrap kn a) then lsplit_divc m l.2 else ([], [])) with
    | (dts@(_ :: _), rts@(_ :: _)) =>
        match (if lin_nowrap_l kn l.1 rts then erange kn (unlin (l.1, rts)) else none) with
        | some (lo, hi) =>
            if lo / m == hi / m then unlin (lo / m, ldiv_terms m dts)
            else mkAlu .SRL a (.ELit s)
        | none => mkAlu .SRL a (.ELit s)
    | _ => mkAlu .SRL a (.ELit s)

/-- (P-c) `lowbits kn e j = some v`: the low `j` bits of the value of `e`
    are `v` (`0 <= v < 2^j`), evaluated through bitwise operations with a
    literal operand, sums, differences and literal multiples; leaves:
    literals, `2^j`-aligned expressions (`ealign`), linear forms
    (`lin_lowbits_kn`). -/
def lowbits (kn : List kentry) (e : expr) (j : Int) : Option Int :=
  let m := zpow 2 j
  let dflt := if j ≤ ealign kn e then some 0 else lin_lowbits_kn kn e j
  match e with
  | .ELit z => some ((z % two64) % m)
  | .EAlu .AND a (.ELit c) =>
      if (c % two64) % m == 0 then some 0
      else
        match lowbits kn a j with
        | some v => some (zland v ((c % two64) % m))
        | none => dflt
  | .EAlu .OR a (.ELit c) =>
      match lowbits kn a j with
      | some v => some (zlor v ((c % two64) % m))
      | none => dflt
  | .EAlu .XOR a (.ELit c) =>
      match lowbits kn a j with
      | some v => some (zlxor v ((c % two64) % m))
      | none => dflt
  | .EAlu .ADD a b =>
      match lowbits kn a j, lowbits kn b j with
      | some x, some y => some ((x + y) % m)
      | _, _ => dflt
  | .EAlu .SUB a b =>
      match lowbits kn a j, lowbits kn b j with
      | some x, some y => some ((x - y) % m)
      | _, _ => dflt
  | .EMd .MUL (.ELit c) a =>
      if (c % two64) % m == 0 then some 0
      else
        match lowbits kn a j with
        | some v => some ((c * v) % m)
        | none => dflt
  | _ => dflt

/-- (task 5) Split a term list into the terms that are multiples of `m`
    (by coefficient, or coefficient times the atom's alignment — the
    `coeffs_divk` test) and the rest.  Both parts stay sorted. -/
def lsplit_div (kn : List kentry) (m : Int) :
    List (Int × expr) → List (Int × expr) × List (Int × expr)
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest
      if (k % m == 0 || (k * zpow 2 (ealign kn a)) % m == 0)
      then ((k, a) :: d, r) else (d, (k, a) :: r)

/-- (task 5) `a AND -2^j` for `a` = A + R with A (terms `dts` and constant
    `cA`) ≡ 0 mod 2^j and R = `r` the residual: if the interval of `r` lies
    inside one block `q 2^j, (q+1) 2^j` the result is the LINEAR form
    A + q 2^j, else A + (r AND -2^j) (the opaque atom covers only the
    residual).  `a AND (2^j - 1)` likewise is r - q 2^j, else
    r AND (2^j - 1). -/
def and_high_split (kn : List kentry) (bk : expr) (j c : Int)
    (dts rts : List (Int × expr)) : expr :=
  let m := zpow 2 j
  let cA := c - c % m
  let r := unlin (c % m, rts)
  match erange kn r with
  | some (lo, hi) =>
      if lo / m == hi / m then unlin (cA + (lo / m) * m, dts)
      else mkAlu .ADD (unlin (cA, dts)) (mkAlu .AND r bk)
  | none => mkAlu .ADD (unlin (cA, dts)) (mkAlu .AND r bk)

/-- The `2^j - 1` half of the split. -/
def and_low_split (kn : List kentry) (bk : expr) (j c : Int)
    (rts : List (Int × expr)) : expr :=
  let m := zpow 2 j
  let r := unlin (c % m, rts)
  match erange kn r with
  | some (lo, hi) =>
      if lo / m == hi / m then unlin (c % m - (lo / m) * m, rts)
      else mkAlu .AND r bk
  | none => mkAlu .AND r bk

/-- AND with an alignment mask `-2^j` on a value known to be `2^j`-aligned
    (or a multiple) is the identity; AND with `2^j - 1` on such a value is
    0. -/
def mkAnd0 (kn : List kentry) (a b : expr) : expr :=
  match b with
  | .ELit k =>
      let k' := k % two64
      let j := zlog2 (two64 - k')
      if (two64 - k' == zpow 2 j && j < 64) then
        -- mask -2^j: identity on 2^j-aligned values; on a linear form whose
        -- terms are multiples of 2^j it only clears the constant's low bits
        (if j ≤ ealign kn a then a
         else
           let l := lin_of a
           if (!(lin_trivial l) && coeffs_divk kn (zpow 2 j) l.2)
           then unlin (l.1 - l.1 % zpow 2 j, l.2)
           else -- (task 5) split off the aligned part when there is one
             match (if lin_trivial l then ([], l.2) else lsplit_div kn (zpow 2 j) l.2) with
             | (dts@(_ :: _), rts@(_ :: _)) => and_high_split kn b j l.1 dts rts
             | _ => -- x & -2^j = 2^j * (x >> j)  (R6)
                    mkMd .MUL (.ELit (zpow 2 j)) (mkSrl kn a j))
      else
        let j2 := zlog2 (k' + 1)
        if (k' + 1 == zpow 2 j2 && j2 < 64) then
          -- mask 2^j2-1: 0 on an aligned value, the constant's low bits on a
          -- linear form with divisible terms
          (if j2 ≤ ealign kn a then .ELit 0
           else
             match lowbits kn a j2 with -- P-c
             | some v => .ELit v
             | none =>
               if lin_trivial (lin_of a) then mkAlu .AND a b
               else
                 match lin_lowbits_kn kn a j2 with
                 | some v => .ELit v
                 | none => -- (task 5) the residual part decides the low bits
                     match lsplit_div kn (zpow 2 j2) (lin_of a).2 with
                     | (_ :: _, rts@(_ :: _)) => and_low_split kn b j2 (lin_of a).1 rts
                     | _ => mkAlu .AND a b)
        else -- J3e: any literal mask below 2^j3: decided by the low j3 bits
             -- when they are known
          let j3 := zlog2 k' + 1
          if (0 < k' && j3 ≤ 64 && !(lin_trivial (lin_of a))) then
            match lin_lowbits_kn kn a j3 with
            | some v => .ELit (zland v k')
            | none => mkAlu .AND a b
          else mkAlu .AND a b
  | _ => mkAlu .AND a b

/-- (SEMANTIC extension, not equal-output) masks of the form
    `2^j - 2^i` (ones on bits i..j-1, e.g. asan's 48-bit size bitfield
    `size & 0xFFFFFFFFFFF8` / `size & 0xFFFFFFFFFFFF`): when the operand is
    provably below `2^j` (`xhi`) the AND equals the AND with the plain
    alignment mask `2^64 - 2^i` (bits >= j are 0 anyway), which `mkAnd0`
    knows how to simplify (`i = 0`: the identity).  Soundness:
    AxSymExec3Sound.mkAnd_denot via `land_mask_narrow`. -/
def narrow_mask (kn : List kentry) (a : expr) (k' : Int) : Option Int :=
  let i := ctz64 k'
  let m := k' + zpow 2 i
  let j := zlog2 m
  if (0 < k' && m == zpow 2 j && j < 64) then
    match xhi kn a with
    | some h => if h < zpow 2 j then some (two64 - zpow 2 i) else none
    | none => none
  else none

/-- Mask merge: `(x & m1) & k = x & (m1 & k)`  (R1'). -/
def mkAnd (kn : List kentry) (a b : expr) : expr :=
  match b with
  | .ELit k =>
      match narrow_mask kn a (k % two64) with
      | some m => mkAnd0 kn a (.ELit m)
      | none => mkAnd0 kn a b
  | _ => mkAnd0 kn a b

/-- `mkAndK`: mask merge with the R6 spelling of `x & -2^i`. -/
def mkAndK (kn : List kentry) (a b : expr) : expr :=
  match a, b with
  | .EAlu .AND x (.ELit m1), .ELit k =>
      mkAnd kn x (.ELit (zland (m1 % two64) (k % two64)))
  | .EMd .MUL (.ELit m) (.EAlu .SRL x (.ELit i)), .ELit k =>
      -- the R6 spelling of `x & -2^i`
      let i' := (i % two64) % 64
      if m % two64 == zpow 2 i' then
        mkAnd kn x (.ELit (zland (two64 - zpow 2 i') (k % two64)))
      else mkAnd kn a b
  | _, _ => mkAnd kn a b

/-- OR of bit-disjoint operands is addition: `a | b = a + b` when `a` is
    `2^k`-aligned and `0 <= b < 2^k` (musl packs bit-fields this way), so
    the result stays a linear form. -/
def or_disjoint (kn : List kentry) (a b : expr) : Bool :=
  match erange kn b with
  | some (lo, hi) => (0 ≤ lo && hi < zpow 2 (ealign kn a))
  | none => false

/-- `mkOr`: the smart OR constructor. -/
def mkOr (kn : List kentry) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | some x, some y => .ELit (zalu .OR x y)
  | _, _ =>
      if or_disjoint kn a b then mkAlu .ADD a b
      else if or_disjoint kn b a then mkAlu .ADD a b
      else -- a | c = (a & ~c) + c for a literal c  (R1)
        match b with
        | .ELit c => mkAlu .ADD (mkAndK kn a (.ELit (zlnot (c % two64)))) (.ELit c)
        | _ =>
            match a with
            | .ELit c => mkAlu .ADD (mkAndK kn b (.ELit (zlnot (c % two64)))) (.ELit c)
            | _ => .EAlu .OR a b

/-! ### Small-range concretization

    When an expression depends on the environment only through ONE
    sub-expression `s` whose interval is small, evaluate it for every
    possible value of `s`: if all evaluations agree on a literal, the
    expression IS that literal.  This is what turns musl's de Bruijn `clz`
    bit trick in `size_to_class` (table-driven, not interval-monotone) into
    a constant inside one size class. -/

/-- Is the expression closed (no variables, no blobs)? -/
def closedb : expr → Bool
  | .ELit _ => true
  | .EVar _ => false
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b => closedb a && closedb b
  | .EExt _ _ _ a => closedb a
  | .EBlob _ _ _ _ => false

mutual
/-- Substitute `r` for `s` everywhere. -/
def esubst (s r e : expr) : expr :=
  if expr_eqb e s then r else esubst_go s r e

/-- The structural core of `esubst` ( single fixpoint). -/
def esubst_go (s r : expr) : expr → expr
  | .EAlu op a b => .EAlu op (esubst s r a) (esubst s r b)
  | .EAluw op a b => .EAluw op (esubst s r a) (esubst s r b)
  | .EMd op a b => .EMd op (esubst s r a) (esubst s r b)
  | .EMdw op a b => .EMdw op (esubst s r a) (esubst s r b)
  | .EExt sx lo n a => .EExt sx lo n (esubst s r a)
  | e => e
end

/-- Direct evaluation of a CLOSED expression (linear in its size). -/
def eval_closed : expr → Option Int
  | .ELit z => some (z % two64)
  | .EVar _ => none
  | .EAlu op a b =>
      match eval_closed a, eval_closed b with
      | some x, some y => some (zalu op x y)
      | _, _ => none
  | .EAluw op a b =>
      match eval_closed a, eval_closed b with
      | some x, some y => some (zaluw op x y)
      | _, _ => none
  | .EMd op a b =>
      match eval_closed a, eval_closed b with
      | some x, some y => some (zmd op x y)
      | _, _ => none
  | .EMdw op a b =>
      match eval_closed a, eval_closed b with
      | some x, some y => some (zmdw op x y)
      | _, _ => none
  | .EExt sx lo n a =>
      match eval_closed a with
      | some x => some (zext_lit sx lo n x)
      | none => none
  | .EBlob _ _ _ _ => none

/-- Candidate pivots: sub-expressions in POST-order (innermost first), so
    the smallest closing pivot — usually the variable itself or the first
    range-reducing operation on it — is found first. -/
def subexprs : expr → List expr
  | .EAlu op a b => subexprs a ++ subexprs b ++ [.EAlu op a b]
  | .EAluw op a b => subexprs a ++ subexprs b ++ [.EAluw op a b]
  | .EMd op a b => subexprs a ++ subexprs b ++ [.EMd op a b]
  | .EMdw op a b => subexprs a ++ subexprs b ++ [.EMdw op a b]
  | .EExt sx lo n a => subexprs a ++ [.EExt sx lo n a]
  | e => [e]

/-- All of `e[s:=lo+i]`, `i < cnt`, evaluate to the literal `v`. -/
def all_eval_to (s e : expr) (v lo : Int) : Nat → Bool
  | 0 => true
  | c + 1 =>
      match eval_closed (esubst s (.ELit lo) e) with
      | some w => if w == v then all_eval_to s e v (lo + 1) c else false -- short-circuit under cbv
      | none => false

mutual
/-- `evalS s z e`: evaluate `e` with `s := z` (no substitution built). -/
def evalS (s : expr) (z : Int) (e : expr) : Option Int :=
  if expr_eqb e s then some z else evalS_go s z e

/-- The structural core of `evalS`. -/
def evalS_go (s : expr) (z : Int) : expr → Option Int
  | .ELit w => some (wrap64 w)
  | .EVar _ => none
  | .EAlu op a b =>
      match evalS s z a with
      | some x => match evalS s z b with | some y => some (zfast op x y) | none => none
      | none => none
  | .EAluw op a b =>
      match evalS s z a with
      | some x => match evalS s z b with | some y => some (zfastw op x y) | none => none
      | none => none
  | .EMd op a b =>
      match evalS s z a with
      | some x => match evalS s z b with | some y => some (zfastm op x y) | none => none
      | none => none
  | .EMdw op a b =>
      match evalS s z a with
      | some x => match evalS s z b with | some y => some (zmdw op x y) | none => none
      | none => none
  | .EExt sx lo n a =>
      match evalS s z a with
      | some x => some (zext_fast sx lo n x)
      | none => none
  | .EBlob _ _ _ _ => none
end

/-- `= all_eval_to` (`AxSymExec3Sound.all_eval_toS_eq`). -/
def all_eval_toS (s e : expr) (v lo : Int) : Nat → Bool
  | 0 => true
  | c + 1 =>
      match evalS s (wrap64 lo) e with
      | some w => if w == v then all_eval_toS s e v (lo + 1) c else false
      | none => false

/-- Probe one point: does `e[s:=z]` evaluate to `v`? -/
def probeS (s e : expr) (v z : Int) : Bool :=
  match evalS s (wrap64 z) e with | some w => w == v | none => false

/-- Membership in a list of expressions. -/
def memE (e : expr) : List expr → Bool
  | [] => false
  | x :: r => if expr_eqb e x then true else memE e r

/-- Deduplicate (accumulator version). -/
def nubE_acc (l acc : List expr) : List expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)

/-- Deduplicate. -/
def nubE (l : List expr) : List expr := nubE_acc l []

/-- The sweep limit. -/
def conc_limit : Int := 4096

mutual
/-- PERF: `evalS s z e` can only succeed when every variable / blob of `e`
    lies inside an occurrence of the pivot `s`
    (`AxSymExec3Sound.evalS_def_None`); deciding that first skips the
    interval query for hopeless pivots (most sub-expressions of an
    address). -/
def evalS_def (s e : expr) : Bool :=
  if expr_eqb e s then true else evalS_def_go s e

/-- The structural core of `evalS_def`. -/
def evalS_def_go (s : expr) : expr → Bool
  | .ELit _ => true
  | .EVar _ => false
  | .EAlu _ a b | .EAluw _ a b | .EMd _ a b | .EMdw _ a b =>
      if evalS_def s a then evalS_def s b else false
  | .EExt _ _ _ a => evalS_def s a
  | .EBlob _ _ _ _ => false
end

/-- The concretization sweep. -/
def conc_try (kn : List kentry) (e : expr) (cands : List expr) : Option Int :=
  match cands with
  | [] => none
  | s :: rest =>
      if closedb s then conc_try kn e rest
      else if !(evalS_def s e) then conc_try kn e rest
      else
        match erange kn s with
        | some (lo, hi) =>
            if hi - lo ≤ conc_limit then
              match evalS s (wrap64 lo) e with
              | some v =>
                  if (if hi < lo then true
                      else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2) else false) then
                    if all_eval_toS s e v lo (hi - lo + 1).toNat then some v
                    else conc_try kn e rest
                  else conc_try kn e rest
              | none => conc_try kn e rest
            else conc_try kn e rest
        | none => conc_try kn e rest

/-- The reference sweep (no pre-filter) and the equality. -/
def conc_try_ref (kn : List kentry) (e : expr) (cands : List expr) : Option Int :=
  match cands with
  | [] => none
  | s :: rest =>
      if closedb s then conc_try_ref kn e rest
      else
        match erange kn s with
        | some (lo, hi) =>
            if hi - lo ≤ conc_limit then
              match evalS s (wrap64 lo) e with
              | some v =>
                  if (if hi < lo then true
                      else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2) else false) then
                    if all_eval_toS s e v lo (hi - lo + 1).toNat then some v
                    else conc_try_ref kn e rest
                  else conc_try_ref kn e rest
              | none => conc_try_ref kn e rest
            else conc_try_ref kn e rest
        | none => conc_try_ref kn e rest

/-- `concretize`: the small-range sweep. -/
def concretize (kn : List kentry) (e : expr) : Option Int :=
  if closedb e then eval_closed e else conc_try kn e (nubE (subexprs e))

/-- A value whose range is provably a single point IS that literal. -/
def foldK (kn : List kentry) (e : expr) : expr :=
  match e with
  | .ELit _ => e
  | _ =>
      match erange kn e with
      | some (lo, hi) =>
          if lo == hi then .ELit lo
          else match concretize kn e with | some v => .ELit v | none => e
      | none => match concretize kn e with | some v => .ELit v | none => e -- enumeration (F13)

/-- Branch decision on two literals. -/
def lit_branch (c : BranchCond) (x y : Int) : Bool :=
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y)

/-- A branch on two syntactically equal operands. -/
def cond_on_eq (c : BranchCond) : Bool :=
  match c with
  | .EQ => true | .NE => false | .LT => false | .GE => true
  | .LTU => false | .GEU => true

/-- Decide an unsigned `<` from intervals. -/
def itv_ltu (al ah bl bh : Int) : Option Bool :=
  if ah < bl then some true else if bh ≤ al then some false else none

/-- Signed `<` from unsigned intervals: both sides in the same half, or in
    opposite halves. -/
def itv_lts (al ah bl bh : Int) : Option Bool :=
  let h := zpow 2 63
  if (ah < h && bh < h) || (h ≤ al && h ≤ bl) then itv_ltu al ah bl bh
  else if (h ≤ al && bh < h) then some true
  else if (ah < h && h ≤ bl) then some false
  else none

/-- Decide a branch from interval bounds. -/
def range_branch (c : BranchCond) (al ah bl bh : Int) : Option Bool :=
  match c with
  | .EQ =>
      if (ah < bl || bh < al) then some false
      else if (al == ah && bl == bh && al == bl) then some true else none
  | .NE =>
      if (ah < bl || bh < al) then some true
      else if (al == ah && bl == bh && al == bl) then some false else none
  | .LTU => itv_ltu al ah bl bh
  | .GEU => (itv_ltu al ah bl bh).map (!·)
  | .LT => itv_lts al ah bl bh
  | .GE => (itv_lts al ah bl bh).map (!·)

/-- EQ/NE decided by the DIFFERENCE being a nonzero/zero literal (same
    base, different literal offsets). -/
def diff_branch (c : BranchCond) (a b : expr) : Option Bool :=
  match c with
  | .EQ | .NE =>
      match is_lit (mkAlu .SUB a b) with
      | some z =>
          let e := (z % two64 == 0)
          some (match c with | .EQ => e | _ => !e)
      | none => none
  | _ => none

/-- (P-a) An unsigned `<` decided by EXACT linear arithmetic on the
    difference (`lin_ge0`: b - 1 - a >= 0, resp. a - b >= 0), for operands
    whose intervals overlap (e.g. `sp-352 <u sp-64`); the signed
    comparisons agree with the unsigned ones when both operands are below
    2^63. -/
def lin_branch (kn : List kentry) (c : BranchCond) (a b : expr) : Option Bool :=
  let ltu := if lin_ge0 kn [(b, -1)] [(a, 0)] then some true
             else if lin_ge0 kn [(a, 0)] [(b, 0)] then some false else none
  match c with
  | .LTU => ltu
  | .GEU => ltu.map (!·)
  | .LT | .GE =>
      match erange kn a, erange kn b with
      | some (_, ah), some (_, bh) =>
          if (ah < zpow 2 63 && bh < zpow 2 63)
          then match c with | .LT => ltu | _ => ltu.map (!·)
          else none
      | _, _ => none
  | .EQ | .NE =>
      -- (task 4) the operands differ when one is strictly below the other by
      -- exact linear arithmetic (a <u b or b <u a)
      if (lin_ge0 kn [(b, -1)] [(a, 0)] || lin_ge0 kn [(a, -1)] [(b, 0)])
      then some (match c with | .EQ => false | _ => true)
      else
        -- ... and EQUAL when each is >= the other
        if (if lin_ge0 kn [(a, 0)] [(b, 0)] then lin_ge0 kn [(b, 0)] [(a, 0)] else false)
        then some (match c with | .EQ => true | _ => false)
        else none

/-- `decide_branch`: literal operands, equal operands, separated intervals,
    the difference, then exact linear arithmetic. -/
def decide_branch (kn : List kentry) (c : BranchCond) (a b : expr) : Option Bool :=
  match a, b with
  | .ELit x, .ELit y => some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then some (cond_on_eq c)
      else
        match diff_branch c a b with
        | some t => some t
        | none =>
            match (match erange kn a, erange kn b with
                   | some (al, ah), some (bl, bh) => range_branch c al ah bl bh
                   | _, _ => none) with
            | some t => some t
            | none => lin_branch kn c a b -- P-a

/-- SLT/SLTU as INSTRUCTIONS decided like branches (`lin_branch` via
    `decide_branch`): provable -> literal 1/0. -/
def mkSlt (kn : List kentry) (c : BranchCond) (op : AluOp) (a b : expr) : expr :=
  match a, b with
  | .ELit _, .ELit _ => mkAlu op a b
  | _, _ =>
      match decide_branch kn c a b with
      | some true => .ELit 1
      | some false => .ELit 0
      | none => mkAlu op a b

/-- `mkAluK0`: the knowledge-aware smart ALU constructor. -/
def mkAluK0 (kn : List kentry) (op : AluOp) (a b : expr) : expr :=
  match op with
  | .SLTU => mkSlt kn .LTU .SLTU a b
  | .SLT => mkSlt kn .LT .SLT a b
  | .AND =>
      match a, b with
      | .ELit _, .ELit _ => mkAnd kn a b
      | .ELit _, _ => mkAndK kn b a -- literal mask on the right
      | _, _ => mkAndK kn a b
  | .OR => if expr_eqb a b then a else mkOr kn a b
  | .XOR =>
      if expr_eqb a b then .ELit 0
      else
        match is_lit a, b with
        | none, .ELit k =>
            if k % two64 == two64 - 1 then mkAlu .SUB (.ELit (two64 - 1)) a
            else mkAlu op a b
        | _, _ => mkAlu op a b
  | .SRL =>
      match is_lit a, shamt_of b 6 with
      | none, some s => mkSrl kn a s
      | _, _ => mkAlu op a b
  | _ => mkAlu op a b

/-- 32-bit add/sub whose 64-bit linear form is a literal or provably below
    2^31 IS that 64-bit form (no truncation, no sign). -/
def zsx32 (v : Int) : Int := bv_swrap 32 v % two64

/-- `mkAluK`. -/
def mkAluK (kn : List kentry) (op : AluOp) (a b : expr) : expr :=
  foldK kn (mkAluK0 kn op a b)

/-- Unsigned division / remainder by a literal power of two are a right
    shift / a low-bit mask (the ASan runtime's `x % page` and
    `x / granule`); everything else as `mkMd`. -/
def pow2_log (m : Int) : Option Int :=
  let m' := m % two64
  let k := zlog2 m'
  if (0 < m' && m' == zpow 2 k && k < 64) then some k else none

/-- `mkMdK`: the knowledge-aware smart M constructor. -/
def mkMdK (kn : List kentry) (op : MulOp) (a b : expr) : expr :=
  match is_lit a, op, b with
  | none, .REMU, .ELit m =>
      match pow2_log m with
      | some k => mkAluK kn .AND a (.ELit (zpow 2 k - 1))
      | none => mkMd op a b
  | none, .DIVU, .ELit m =>
      match pow2_log m with
      | some k => mkAluK kn .SRL a (.ELit k)
      | none => mkMd op a b
  | _, _, _ => mkMd op a b

/-- The 64-bit values whose 32-bit truncation sign-extends back to them:
    `0, 2^31` and `2^64 - 2^31, 2^64`. -/
def sx32_stable (lo hi : Int) : Bool :=
  (hi < zpow 2 31 || two64 - zpow 2 31 ≤ lo)

/-- The INTEGER linear form of `d` lies in (-2^31, 2^31): then the 32-bit
    result sign-extends to `d` itself even when `d`'s unsigned range wraps
    (a symbolic base cancelling on both sides, e.g. `end - p - n`). -/
def zband32 (kn : List kentry) (d : expr) : Bool :=
  let l := lin_of d
  match lin_range (erange kn) l.1 l.2 with
  | some (lo, hi) => (-(zpow 2 31) < lo && hi < zpow 2 31)
  | none => false

/-- `mkAluwK0`: the knowledge-aware smart 32-bit ALU constructor. -/
def mkAluwK0 (kn : List kentry) (op : AluOp) (a b : expr) : expr :=
  match op with
  | .ADD | .SUB =>
      let d := mkAlu op a b
      match is_lit d with
      | some v => .ELit (zsx32 v)
      | none =>
          match erange kn d with
          | some (lo, hi) =>
              if sx32_stable lo hi then d else if zband32 kn d then d else mkAluw op a b
          | none => if zband32 kn d then d else mkAluw op a b
  | _ => mkAluw op a b

/-- `mkAluwK`. -/
def mkAluwK (kn : List kentry) (op : AluOp) (a b : expr) : expr :=
  foldK kn (mkAluwK0 kn op a b)

/-- A zero/sign-extended low slice of a value provably below the slice's
    (signed) capacity is the value itself (C int-isms: lw/lbu reloads). -/
def extK0 (kn : List kentry) (v : expr) : expr :=
  match v with
  | .EExt sx 0 n e =>
      if n ≤ 7 then
        match erange kn e with
        | some (lo, hi) =>
            if hi < (if sx then zpow 2 (8 * (n : Int)) / 2 else zpow 2 (8 * (n : Int))) then e else v
        | none => v
      else v
  | _ => v

/-- `extK`. -/
def extK (kn : List kentry) (v : expr) : expr := foldK kn (extK0 kn v)

/-- Bytes of a modeled memory access size. -/
def msize_bytes : MSize → Nat
  | .SZ1 => 1
  | .SZ2 => 2
  | .SZ4 => 4
  | .SZ8 => 8

/-- Flatness obligation for an `n`-byte access at `a`, unless the known
    interval bounds already decide it. -/
def flat_sc (kn : List kentry) (a : saddr) (n : Nat) : List sidecond :=
  match base_range kn a.a_base with
  | some (lo, hi) =>
      if (0 ≤ lo + a.a_off && hi + a.a_off + (n : Int) ≤ 2 ^ 64)
      then [] else [.SCFlat a (elen n)]
  | none => [.SCFlat a (elen n)]

/-- Writability obligation, unless a `KWr` window covers the range (the
    window's length may be symbolic: its lower bound is used). -/
def wr_covered (allkn kn : List kentry) (a : saddr) (n : Nat) : Bool :=
  match kn with
  | [] => false
  | .KWr ⟨kb, kk⟩ len :: rest =>
      if (if (expr_eqb a.a_base kb && kk ≤ a.a_off) then
            match xlo allkn len with
            | some l => a.a_off + (n : Int) ≤ kk + l
            | none => false
          else false)
      then true
      else if xinside allkn a.a_base a.a_off (.ELit (n : Int)) kb kk len then true
      else wr_covered allkn rest a n
  | _ :: rest => wr_covered allkn rest a n

/-- The store-ok obligation list. -/
def storeok_sc (kn : List kentry) (a : saddr) (n : Nat) : List sidecond :=
  if wr_covered kn kn a n then [] else [.SCStoreOk a n]

/-! ## 4. The stepper -/

/-- Scripts threaded through a run. -/
structure scripts where
  /-- branch directions (consumed only by undecided branches) -/
  sc_dirs : List Bool
  /-- names for base-memory fallback reads -/
  sc_reads : List expr
  /-- overlap hints -/
  sc_hints : List Bool
  deriving DecidableEq, Repr

/-- `SCR` — the record constructor. -/
abbrev SCR (d : List Bool) (r : List expr) (h : List Bool) : scripts := ⟨d, r, h⟩

/-- One step's outcome. -/
inductive stepres : Type
  /-- a step: new state, side conditions, scripts -/
  | SOk (ss : sym_state) (scs : List sidecond) (scr : scripts)
  /-- stop -/
  | SStop
  deriving DecidableEq, Repr

/-- A register value replaced by its literal, when provable. -/
def conc_expr (kn : List kentry) (e : expr) : expr :=
  match e with
  | .ELit _ => e
  | _ => match concretize kn e with | some v => .ELit v | none => e

/-- Branch decision by ENUMERATION: a probe expression whose value encodes
    the comparison, concretized over a small-range sub-expression
    (`concretize`); `EQ`/`NE` probe the difference, signed/unsigned `<`
    probe `SLT`/`SLTU`; the boolean says whether the branch is taken on a
    NONZERO probe. -/
def cond_probe (c : BranchCond) (a b : expr) : expr × Bool :=
  match c with
  | .EQ => (.EAlu .SLTU (.EAlu .SUB a b) (.ELit 1), true) -- a-b <u 1 <-> a = b
  | .NE => (.EAlu .SLTU (.EAlu .SUB a b) (.ELit 1), false)
  | .LT => (.EAlu .SLT a b, true)
  | .GE => (.EAlu .SLT a b, false)
  | .LTU => (.EAlu .SLTU a b, true)
  | .GEU => (.EAlu .SLTU a b, false)

/-- `enum_branch`: decide a branch by enumeration. -/
def enum_branch (kn : List kentry) (c : BranchCond) (a b : expr) : Option Bool :=
  let (e, pos) := cond_probe c a b
  match concretize kn e with
  | some v =>
      let z := (v % two64 == 0)
      some (if pos then !z else z)
  | none => none

/-- Address formation with concretization of a non-literal base. -/
def to_saddrK (kn : List kentry) (e : expr) (imm : Int) : saddr :=
  match split_lit e with
  | (.ELit _, _) => to_saddr e imm
  | _ =>
      match concretize kn (mkAlu .ADD e (.ELit imm)) with
      | some v => SA (.ELit 0) v
      | none => to_saddr e imm

/-- Operand width of an atomic as a load/store size. -/
def amo_sz : AWidth → MSize
  | .W => .SZ4
  | .D => .SZ8

/-- `lr.w`/`amo*.w` sign-extend the old value (like `lw`); `.d` is plain. -/
def amo_sx : AWidth → Bool
  | .W => true
  | .D => false

/-- The ISA's `amo_aligned wd a` (`bv_unsigned a mod 4|8 = 0`) decided TRUE
    from the linear form / alignment facts of the address expression
    (`lin_lowbits_kn`); anything undecided makes the instruction an
    `SStop` (a misaligned atomic is a MachineFault). -/
def amo_alignedb (kn : List kentry) (e : expr) (wd : AWidth) : Bool :=
  match lin_lowbits_kn kn e (match wd with | .W => 2 | .D => 3) with
  | some r => r == 0
  | none => false

/-- Effect of a store / AMO at `a` on the tracked reservation
    (`Sem.inval_resv`: an access to EXACTLY the reserved address kills it).
    `some r'` = the new reservation; `none` = undecidable (the step
    declines).  Decided cases: no reservation; syntactically the same
    address (killed); same base expression and offsets that differ modulo
    2^64 (kept). -/
def resv_inval (r : Option saddr) (a : saddr) : Option (Option saddr) :=
  match r with
  | none => some none
  | some ra =>
      if saddr_eqb ra a then some none
      else if (expr_eqb ra.a_base a.a_base && !((ra.a_off - a.a_off) % two64 == 0))
           then some r
           else none

/-- AMO combine functions the value language expresses exactly:
    `some none` = swap, `some (some op)` = `alu op old src`; min/max: no. -/
def amo_aluop : AmoOp → Option (Option AluOp)
  | .SWAP => some none
  | .ADD => some (some .ADD)
  | .XOR => some (some .XOR)
  | .AND => some (some .AND)
  | .OR => some (some .OR)
  | _ => none

/-- The value an AMO stores (as a 64-bit expression whose low `4|8` bytes
    are written): `.w` computes at 32 bits (`EAluw`, matching
    `Sem.amo_val` on `bv 32`), `.d` at 64. -/
def amo_newval (kn : List kentry) (wd : AWidth) (aop : Option AluOp) (old src : expr) : expr :=
  match aop with
  | none => src
  | some o => match wd with | .W => mkAluwK kn o old src | .D => mkAluK kn o old src

/-- Resolution of an `n`-byte read at `a` (shared by `Load`, `Lr`, `Amo`):
    log first, then knowledge, then the `SCReadBase` fallback (read script
    name or fresh variable).  Returns the value expression, the side
    conditions, the remaining scripts and the new `s_next`. -/
def sym_read (segs : List Segment) (ss : sym_state) (fk : List kentry) (scr : scripts)
    (a : saddr) (n : Nat) (sx' : Bool) :
    Option (expr × List sidecond × scripts × Nat) :=
  match log_lookup fk ss.s_log a.a_base a.a_off n sx' scr.sc_hints [] with
  | .LStuck => none
  | .LHit v scs hints =>
      some (extK fk v, flat_sc fk a n ++ scs, SCR scr.sc_dirs scr.sc_reads hints, ss.s_next)
  | .LMiss scs hints =>
      match know_lookupA fk segs ss.s_know a.a_base a.a_off n sx' hints scs with
      | .LStuck => none
      | .LHit v scs' hints' =>
          some (extK fk v, flat_sc fk a n ++ scs', SCR scr.sc_dirs scr.sc_reads hints', ss.s_next)
      | .LMiss scs' hints' =>
          -- fallback: name the value (read script) or make it fresh
          let i := ss.s_next
          let rv := match scr.sc_reads with | [] => .EVar i | e :: _ => e
          let reads' := match scr.sc_reads with | [] => [] | _ :: t => t
          some (rv, flat_sc fk a n ++ .SCReadBase a n sx' rv :: scs',
                SCR scr.sc_dirs reads' hints', i + 1)

/-- The symbolic stepper: one instruction. -/
def sym_step (segs : List Segment) (i : Instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get ss.s_regs r
  let p := ss.s_pc
  let fk := facts_of ss.s_know -- PERF: the non-memory facts, filtered once per instruction
  match i with
  | .opImm op rd rs imm => .SOk (sset ss rd (mkAluK fk op (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm op rd rs sh =>
      .SOk (sset ss rd (mkAluK fk op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op op rd rs1 rs2 => .SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | .opImm32 rd rs imm =>
      .SOk (sset ss rd (mkAluwK fk .ADD (g rs) (.ELit (bv_signed imm))) (p + 4)) [] scr
  | .shiftImm32 op rd rs sh =>
      .SOk (sset ss rd (mkAluw op (g rs) (.ELit (bv_unsigned sh))) (p + 4)) [] scr
  | .op32 op rd rs1 rs2 => .SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul op rd rs1 rs2 => .SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | .mul32 op rd rs1 rs2 => .SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | .lui rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (zshiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | .auipc rd imm =>
      .SOk (sset ss rd (.ELit (bv_unsigned (Z_to_bv 64 (zshiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | .jal rd imm =>
      .SOk (sset ss rd (.ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | .jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | .ELit z =>
          .SOk (sset ss rd (.ELit (p + 4)) (zland_m2 (bv_wrap 64 z + bv_signed imm) % 2 ^ 64)) [] scr
      | _ => .SStop
  | .branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm))
      let a := g rs1
      let b := g rs2
      match (match decide_branch fk c a b with
             | some t => some t
             | none =>
                 match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                 | some t => some t
                 | none => enum_branch fk c a b) with
      | some t => .SOk (sjump ss (if t then tk else p + 4)) [] scr
      | none =>
          match scr.sc_dirs with
          | [] => .SStop
          | t :: dirs' =>
              .SOk (sjump ss (if t then tk else p + 4)) [.SCBr t c a b]
                  (SCR dirs' scr.sc_reads scr.sc_hints)
  | .fence _ _ _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .fenceI _ _ _ => .SOk (sjump ss (p + 4)) [] scr
  | .load sz sx rd rs imm =>
      let n := msize_bytes sz
      -- the ISA's `Load SZ8 true` is `ld` (no extension needed); treat
      -- 8-byte as unsigned slice
      let sx' := match sz with | .SZ8 => false | _ => sx
      let a := to_saddrK fk (g rs) (bv_signed imm)
      match sym_read segs ss fk scr a n sx' with
      | none => .SStop
      | some (v, scs, scr', nx') =>
          .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                   ss.s_log, ss.s_know, nx', ss.s_resv⟩ scs scr'
  | .store sz rs1 rs2 imm =>
      let n := msize_bytes sz
      let a := to_saddrK fk (g rs1) (bv_signed imm)
      match resv_inval ss.s_resv a with
      | none => .SStop
      | some r' =>
          .SOk ⟨p + 4, ss.s_regs, SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, r'⟩
              (flat_sc fk a n ++ storeok_sc fk a n) scr
  -- ---- A extension ----
  | .lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0
        match sym_read segs ss fk scr a n (amo_sx wd) with
        | none => .SStop
        | some (v, scs, scr', nx') =>
            .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) v),
                     ss.s_log, ss.s_know, nx', some a⟩ scs scr'
      else .SStop
  | .sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd)
      let e := g rs1
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0
        match ss.s_resv with
        | some r =>
            if saddr_eqb r a then
              .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs
                            else sr_upd ss.s_regs (ridx rd) (.ELit 0)),
                     SE a n (g rs2) :: ss.s_log, ss.s_know, ss.s_next, none⟩
                  (flat_sc fk a n ++ storeok_sc fk a n) scr
            else .SStop -- reservation elsewhere / lost: the failing SC is never needed
        | none => .SStop
      else .SStop
  | .amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | none => .SStop
      | some aop =>
          let n := msize_bytes (amo_sz wd)
          let e := g rs1
          if amo_alignedb fk e wd then
            let a := to_saddrK fk e 0
            match resv_inval ss.s_resv a with
            | none => .SStop
            | some r' =>
                match sym_read segs ss fk scr a n (amo_sx wd) with
                | none => .SStop
                | some (vold, scs, scr', nx') =>
                    .SOk ⟨p + 4, (if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) vold),
                             SE a n (amo_newval fk wd aop vold (g rs2)) :: ss.s_log,
                             ss.s_know, nx', r'⟩
                        (scs ++ storeok_sc fk a n) scr'
          else .SStop
  | _ => .SStop

/-- Syntactic dedup of side conditions (cheap win: a spill slot touched ten
    times yields one obligation). -/
def sidecond_eqb (x y : sidecond) : Bool :=
  match x, y with
  | .SCFlat a n, .SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | .SCStoreOk a n, .SCStoreOk a' n' => saddr_eqb a a' && (n == n')
  | .SCDisj a n b m, .SCDisj a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | .SCInside a n b m, .SCInside a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | _, _ => false

/-- Side-condition membership (syntactic). -/
def sc_mem (x : sidecond) : List sidecond → Bool
  | [] => false
  | y :: t => sidecond_eqb x y || sc_mem x t

/-- Add the new obligations, deduplicated. -/
def sc_add (news acc : List sidecond) : List sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)

/-! ### 4b. P4: decoded-instruction table

    A minimal binary trie over `positive` keys (CompCert's PTree, cut down
    to get/set), used to look the decoded instruction at a pc up in
    O(bits pc) instead of re-reading four hex-encoded bytes from the
    image's PrimString and re-decoding them at every step (measured:
    ~40 us per instruction, up to a fifth of the plan checker's time).
    `sym_execT` below is `sym_execS` reading the table; it STOPS wherever
    the table has no entry, so an incomplete table costs completeness,
    never soundness (`AxSymExec3Sound.sym_execT_sound` asks only
    `itab_sound`). -/

/-- The instruction table (see `ptree` for the key encoding). -/
abbrev itab : Type := ptree Instr

/-- Lookup at a `Z` pc (`Zpos p` only: an address is a key). -/
def itab_lookup (t : itab) (pc : Int) : Option Instr :=
  if 0 < pc then pt_get t pc.toNat else none

/-- The table entry a pc deserves: its decoded 4-byte non-ecall
    instruction. -/
def itab_entry (segs : List Segment) (pc : Int) : Option Instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | none => none
  | some w =>
      if is_ecall w then none
      else
        match decodeAny w with
        | some (i, sz) => if sz == 4 then some i else none
        | none => none

/-- Fill `n` entries from `pc` on. -/
def mk_itab_fuel (segs : List Segment) (n : Nat) (pc : Int) (t : itab) : itab :=
  match n with
  | 0 => t
  | n' + 1 =>
      mk_itab_fuel segs n' (pc + 4)
        (match pc, itab_entry segs pc with
         | .ofNat m, some i => if 0 < m then pt_set m i t else t
         | _, _ => t)

/-- the instructions at `lo`, `lo+4`, ... (`n` of them) -/
def mk_itab (segs : List Segment) (lo : Int) (n : Nat) : itab :=
  mk_itab_fuel segs n lo .PTLeaf

/-- Every entry in the table is the right one. -/
def itab_sound (segs : List Segment) (t : itab) : Prop :=
  ∀ pc i, itab_lookup t pc = some i → itab_entry segs pc = some i


/-! ### 4a. The drivers -/

/-- Run at most `fuel` instructions; stop (returning the state AT the
    instruction) at any pc in `stops`, at an ecall, at anything `sym_step`
    declines, or when a script runs dry.

    RESERVATION DISCIPLINE.  A run never hands back a state with a live LR
    reservation: `ck` is the last CLEAN state seen (with its side
    conditions / scripts), and a run that comes to rest between an `lr` and
    its `sc` backs off to it.  The entry state's `s_resv` is ignored
    (`clr`): block boundaries are `mkst` states (no reservation).  Both
    loops are tail recursive (the checkpoint is an accumulator). -/
def sym_exec_go (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (scr : scripts) (ss : sym_state) (acc : List sidecond)
    (ck : sym_state × List sidecond × scripts) :
    sym_state × List sidecond × scripts :=
  match fuel with
  | 0 => if s_clean ss then (ss, acc, scr) else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then (ss, acc, scr) else ck)
      else
        match fetch_word segs (Z_to_bv 64 ss.s_pc) with
        | none => if s_clean ss then (ss, acc, scr) else ck
        | some w =>
            if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck)
            else
              match decodeAny w with
              | none => if s_clean ss then (ss, acc, scr) else ck
              | some (i, sz) =>
                  if !(sz == 4) then (if s_clean ss then (ss, acc, scr) else ck)
                  else
                    match sym_step segs i ss scr with
                    | .SOk ss' scs scr' =>
                        let acc' := sc_add scs acc
                        sym_exec_go segs f false stops scr' ss' acc'
                          (if s_clean ss' then (ss', acc', scr') else ck)
                    | .SStop => if s_clean ss then (ss, acc, scr) else ck

/-- The classic driver. -/
def sym_exec (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (scr : scripts) (ss : sym_state) (acc : List sidecond) :
    sym_state × List sidecond × scripts :=
  sym_exec_go segs fuel first stops scr (clr ss) acc (clr ss, acc, scr)

/-- STRICT variant for the reflective plan checker: no scripts, and it
    stops AT any instruction whose symbolic step would need a side
    condition (so an unprovable store — e.g. through a NULL pointer — is
    where the run ends, ready for a fault node).  Returns only the state. -/
def scr_nil : scripts := SCR [] [] []

/-- `sym_execS`'s loop. -/
def sym_execS_go (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match fetch_word segs (Z_to_bv 64 ss.s_pc) with
        | none => if s_clean ss then ss else ck
        | some w =>
            if is_ecall w then (if s_clean ss then ss else ck)
            else
              match decodeAny w with
              | none => if s_clean ss then ss else ck
              | some (i, sz) =>
                  if !(sz == 4) then (if s_clean ss then ss else ck)
                  else
                    match sym_step segs i ss scr_nil with
                    | .SOk ss' [] _ => sym_execS_go segs f false stops ss' (if s_clean ss' then ss' else ck)
                    | _ => if s_clean ss then ss else ck

/-- The strict driver. -/
def sym_execS (segs : List Segment) (fuel : Nat) (first : Bool) (stops : List Int)
    (ss : sym_state) : sym_state :=
  sym_execS_go segs fuel first stops (clr ss) (clr ss)

/-- P4: `sym_execS` reading the decoded-instruction table `t`. -/
def sym_execT_go (segs : List Segment) (t : itab) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match itab_lookup t ss.s_pc with
        | none => if s_clean ss then ss else ck
        | some i =>
            match sym_step segs i ss scr_nil with
            | .SOk ss' [] _ => sym_execT_go segs t f false stops ss' (if s_clean ss' then ss' else ck)
            | _ => if s_clean ss then ss else ck

/-- The table-driven strict driver. -/
def sym_execT (segs : List Segment) (t : itab) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) : sym_state :=
  sym_execT_go segs t fuel first stops (clr ss) (clr ss)

/-! ### 4c. EXTENSION MODE: fresh variables inside a block

    In extension mode the executor may NAME values it cannot express: a
    read of bytes known to be mapped but arbitrary (`KUnk`, or any
    overlay-defined / image range the knowledge proves readable) becomes
    `EVar (s_next ss)` with NO side condition, and (optionally) a register
    whose expression outgrows `K` nodes is renamed likewise.  Soundness is
    by ENVIRONMENT EXTENSION (`AxSymExec3Sound.st_okX`,
    `sym_execTX_sound`): the valuation of the new variables is chosen by
    the theorem, so every symbolic object must mention only variables below
    `s_next` — which the relation `st_okX` states semantically.  The
    classic drivers above are untouched (their fixed-valuation theorems
    stay as they are).

    Implementation: `sym_stepX` runs the classic `sym_step` and then
    (1) DISCHARGES the obligations the knowledge decides — `SCReadBase` of
    THIS step's fresh read variable, `SCFlat`, `SCStoreOk` — when the range
    is covered (`kn_readable` / `kn_overlay`); (2) caps the destination
    register (`cap_rd`). -/

/-- `rb+rk, +n` inside ONE entry, by offsets (literal length, same base
    spelling) or by exact linear arithmetic (`xinside`, any spelling /
    symbolic length). -/
def zf_covers (allkn : List kentry) (rb : expr) (rk : Int) (n : Nat) (kb : expr) (kk : Int)
    (len : expr) : Bool :=
  (match len with
   | .ELit l0 =>
       match rel_lit rb rk (n : Int) kb kk (l0 % two64) with
       | .RInside _ => true
       | _ => false
   | _ => false) || xinside allkn rb rk (elen n) kb kk len

/-- an entry proving the range OVERLAY-DEFINED (hence readable and
    writable) -/
def kentry_overlay (allkn : List kentry) (rb : expr) (rk : Int) (n : Nat) (K : kentry) : Bool :=
  match K with
  | .KUnk ⟨kb, kk⟩ len | .KZero ⟨kb, kk⟩ len | .KFill ⟨kb, kk⟩ len _ | .KBlob ⟨kb, kk⟩ len _ =>
      zf_covers allkn rb rk n kb kk len
  | _ => false

/-- an entry proving the range READABLE: overlay-defined, or a `KWord` (its
    bytes read back, from the overlay or the image) -/
def kentry_readable (allkn : List kentry) (rb : expr) (rk : Int) (n : Nat) (K : kentry) : Bool :=
  match K with
  | .KWord ⟨kb, kk⟩ w _ =>
      match rel_lit rb rk (n : Int) kb kk (w : Int) with
      | .RInside _ => true
      | _ => false
  | _ => kentry_overlay allkn rb rk n K

/-- bytewise: the byte at `rb+rk` lies in a literal-extent entry of the same
    base spelling (`img`: also an image byte under a `KImg`, base
    `ELit 0`) -/
def know_byte_cov (segs : List Segment) (img : Bool) (kn : List kentry) (rb : expr)
    (rk : Int) : Bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit (kb : expr) (kk l : Int) : Bool :=
        match rel_lit rb rk 1 kb kk l with | .RInside _ => true | _ => false
      (match K with
       | .KWord ⟨kb, kk⟩ w _ => img && lit kb kk (w : Int)
       | .KZero ⟨kb, kk⟩ (.ELit l0) | .KFill ⟨kb, kk⟩ (.ELit l0) _
       | .KBlob ⟨kb, kk⟩ (.ELit l0) _ | .KUnk ⟨kb, kk⟩ (.ELit l0) => lit kb kk (l0 % two64)
       | .KImg lo hi =>
           img &&
             (match rb with
              | .ELit 0 =>
                  lo ≤ rk && rk < hi &&
                    (match seg_rom segs (Z_to_bv 64 rk) with | some _ => true | none => false)
              | _ => false)
       | _ => false) || know_byte_cov segs img rest rb rk

/-- the bytewise test over `n` bytes -/
def know_bytes_cov (segs : List Segment) (img : Bool) (kn : List kentry) (rb : expr)
    (rk : Int) : Nat → Bool
  | 0 => true
  | n + 1 => know_byte_cov segs img kn rb rk && know_bytes_cov segs img kn rb (rk + 1) n

/-- The range is provably readable. -/
def kn_readable (segs : List Segment) (allkn kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) : Bool :=
  kn.any (kentry_readable allkn rb rk n) || know_bytes_cov segs true kn rb rk n

/-- The range is provably overlay-defined. -/
def kn_overlay (segs : List Segment) (allkn kn : List kentry) (rb : expr) (rk : Int)
    (n : Nat) : Bool :=
  kn.any (kentry_overlay allkn rb rk n) || know_bytes_cov segs false kn rb rk n

/-- Variables of an expression all below `b` (its value is then fixed by the
    valuation below `b`: `AxSymExec3Sound.edenot_evars_lt`). -/
def evars_lt (b : Nat) : expr → Bool
  | .ELit _ | .EBlob _ _ _ _ => true
  | .EVar v => v < b
  | .EAlu _ x y | .EAluw _ x y | .EMd _ x y | .EMdw _ x y => evars_lt b x && evars_lt b y
  | .EExt _ _ _ x => evars_lt b x

/-- The base read THIS step named `EVar i` (classic `sym_read` fallback). -/
def find_readbase (i : Nat) : List sidecond → Option (saddr × Nat × Bool)
  | [] => none
  | .SCReadBase a n sx (.EVar j) :: rest =>
      if j == i then some (a, n, sx) else find_readbase i rest
  | _ :: rest => find_readbase i rest

/-- The obligations of ONE classic step `ss -> ss'` that extension mode
    discharges from the knowledge: the base read of this step's fresh
    variable (all its occurrences name the same read `rb`; the address
    mentions no variable from `s_next ss` on, so it means the same under
    every extension), flatness and writability of covered ranges. -/
def x_dischargeable (segs : List Segment) (ss ss' : sym_state)
    (rb : Option (saddr × Nat × Bool)) (sc : sidecond) : Bool :=
  let kn := ss.s_know
  let fk := facts_of kn
  match sc with
  | .SCReadBase a n sx (.EVar j) =>
      (match rb with
       | some (a', n', sx') => saddr_eqb a' a && (n' == n) && (sx' == sx)
       | none => false) &&
      (j == ss.s_next) && (j < ss'.s_next) && evars_lt ss.s_next a.a_base &&
      (1 ≤ n && n ≤ 8) && kn_readable segs fk kn a.a_base a.a_off n
  | .SCFlat a (.ELit z) =>
      (1 ≤ z && z ≤ 8) && kn_readable segs fk kn a.a_base a.a_off z.toNat
  | .SCStoreOk a n => (1 ≤ n && n ≤ 8) && kn_overlay segs fk kn a.a_base a.a_off n
  | _ => false

/-- Filter the obligations extension mode discharges. -/
def x_filter (segs : List Segment) (ss ss' : sym_state) (scs : List sidecond) : List sidecond :=
  match scs with
  | [] => [] -- the common case
  | _ =>
      let rb := find_readbase ss.s_next scs
      scs.filter (fun sc => !(x_dischargeable segs ss ss' rb sc))

/-- Register-size cap.  `esize_le e k`: `e` has at most `k` nodes (the count
    stops as soon as the budget is exhausted). -/
def esize_budget : expr → Nat → Option Nat
  | _, 0 => none
  | .ELit _, b' + 1 => some b'
  | .EVar _, b' + 1 => some b'
  | .EBlob _ _ _ _, b' + 1 => some b'
  | .EAlu _ x y, b' + 1 =>
      match esize_budget x b' with | some b'' => esize_budget y b'' | none => none
  | .EAluw _ x y, b' + 1 =>
      match esize_budget x b' with | some b'' => esize_budget y b'' | none => none
  | .EMd _ x y, b' + 1 =>
      match esize_budget x b' with | some b'' => esize_budget y b'' | none => none
  | .EMdw _ x y, b' + 1 =>
      match esize_budget x b' with | some b'' => esize_budget y b'' | none => none
  | .EExt _ _ _ x, b' + 1 => esize_budget x b'
termination_by e b => sizeOf e
decreasing_by all_goals (simp_wf; omega)

/-- Does `e` fit `k` nodes? -/
def esize_le (e : expr) (k : Nat) : Bool :=
  match esize_budget e k with | some _ => true | none => false

/-- The integer destination register of an instruction the executor
    handles. -/
def rd_of : Instr → Option reg
  | .lui rd _ | .auipc rd _ | .jal rd _ => some rd
  | .jalr rd _ _ | .load _ _ rd _ _ => some rd
  | .opImm _ rd _ _ | .shiftImm _ rd _ _ | .op _ rd _ _ => some rd
  | .opImm32 rd _ _ | .shiftImm32 _ rd _ _ | .op32 _ rd _ _ => some rd
  | .mul _ rd _ _ | .mul32 _ rd _ _ => some rd
  | .lr _ _ _ rd _ | .sc _ _ _ rd _ _ | .amo _ _ _ _ rd _ _ => some rd
  | _ => none

/-- `K = 0`: no cap.  Otherwise the destination register, if its new
    expression has more than `K` nodes, is renamed to a fresh variable. -/
def cap_rd (K : Nat) (i : Instr) (ss : sym_state) : sym_state :=
  match K with
  | 0 => ss
  | _ =>
      match rd_of i with
      | none => ss
      | some rd =>
          if bv_eqb rd 0 then ss
          else if esize_le (sr_get ss.s_regs rd) K then ss
          else ⟨ss.s_pc, sr_upd ss.s_regs (ridx rd) (.EVar ss.s_next),
                ss.s_log, ss.s_know, ss.s_next + 1, ss.s_resv⟩

/-- The extension-mode step: the classic step, obligations discharged,
    destination capped. -/
def sym_stepX (segs : List Segment) (K : Nat) (i : Instr) (ss : sym_state)
    (scr : scripts) : stepres :=
  match sym_step segs i ss scr with
  | .SOk ss' scs scr' =>
      if ss.s_next ≤ ss'.s_next -- always; keeps the soundness proof generic
      then .SOk (cap_rd K i ss') (x_filter segs ss ss' scs) scr'
      else .SStop
  | .SStop => .SStop

/-- The strict driver in extension mode (`K`: register cap, 0 = none). -/
def sym_execSX_go (segs : List Segment) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match fetch_word segs (Z_to_bv 64 ss.s_pc) with
        | none => if s_clean ss then ss else ck
        | some w =>
            if is_ecall w then (if s_clean ss then ss else ck)
            else
              match decodeAny w with
              | none => if s_clean ss then ss else ck
              | some (i, sz) =>
                  if !(sz == 4) then (if s_clean ss then ss else ck)
                  else
                    match sym_stepX segs K i ss scr_nil with
                    | .SOk ss' [] _ => sym_execSX_go segs K f false stops ss' (if s_clean ss' then ss' else ck)
                    | _ => if s_clean ss then ss else ck

/-- The strict extension-mode driver. -/
def sym_execSX (segs : List Segment) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) : sym_state :=
  sym_execSX_go segs K fuel first stops (clr ss) (clr ss)

/-- The table-driven strict extension-mode driver. -/
def sym_execTX_go (segs : List Segment) (t : itab) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | 0 => if s_clean ss then ss else ck
  | f + 1 =>
      if (!first && stops.any (· == ss.s_pc)) then (if s_clean ss then ss else ck)
      else
        match itab_lookup t ss.s_pc with
        | none => if s_clean ss then ss else ck
        | some i =>
            match sym_stepX segs K i ss scr_nil with
            | .SOk ss' [] _ => sym_execTX_go segs t K f false stops ss' (if s_clean ss' then ss' else ck)
            | _ => if s_clean ss then ss else ck

/-- `sym_execTX`. -/
def sym_execTX (segs : List Segment) (t : itab) (K : Nat) (fuel : Nat) (first : Bool)
    (stops : List Int) (ss : sym_state) : sym_state :=
  sym_execTX_go segs t K fuel first stops (clr ss) (clr ss)

/-! ## 7. Inter-block glue: carrying knowledge through the store log -/

/-- Exact split of a zero entry `kb+kk, + len` by a written / havoc'd range
    `wb+wk, + wn`, MODULO BASE SPELLING, decided by exact linear arithmetic
    (`lin_ge0`): the part strictly below the write start (length
    S = w_start - K_start, kept when S >= 1 and w_start <= K_end) and the
    part from the write end up (length T = K_end - w_end, kept when T >= 1
    and K_start <= w_end).  Lengths (and, if `split_lit` cannot be
    justified exactly, the high start) are spelled with `mkAlu` so that
    same-spelling literal cases fold to literals. -/
def kcut (mk : saddr → expr → kentry) (kn : List kentry) (wb : expr) (wk : Int)
    (wn : expr) (kb : expr) (kk : Int) (len : expr) : List kentry :=
  let ws := mkAlu .ADD wb (.ELit wk)
  let ks := mkAlu .ADD kb (.ELit kk)
  -- pieces may be EMPTY for some valuations (S = 0 / T = 0): that is fine
  -- (a zero-length entry is vacuous) and needed when a gap closes at a
  -- class boundary; a piece that is provably always empty is omitted.
  let lowc : Bool :=
    if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false -- S <= 0 always: omit
    else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk), (len, 0)] [(wb, wk)]
    else false
  let low := if lowc then [mk (SA kb kk) (mkAlu .SUB ws ks)] else []
  let highc : Bool :=
    if lin_ge0 kn [(kb, kk), (len, 0)] [(wb, wk), (wn, 0)] -- T >= 0
    then
      if lin_ge0 kn [(wb, wk), (wn, 0)] [(kb, kk)] -- K_start <= w_end
      then lin_ge0 kn [(.ELit 0, two64 - 1)] [(kb, kk), (len, 0)] -- K_end < 2^64
      else false
    else false
  let high :=
    if highc then
      let we := mkAlu .ADD ws wn
      let (hb, ho) := split_lit we
      let ha :=
        if (lin_ge0 kn [(hb, ho)] [(wb, wk), (wn, 0)] && lin_ge0 kn [(wb, wk), (wn, 0)] [(hb, ho)])
        then SA hb ho else SA we 0
      [mk ha (mkAlu .SUB (mkAlu .ADD ks len) we)]
    else []
  low ++ high

/-- `kcut` at `KZero`. -/
def kzero_cut (kn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcut .KZero kn wb wk wn kb kk len

/-- `kcut` at `KFill c`. -/
def kfill_cut (c : Int) (kn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr)
    (kk : Int) (len : expr) : List kentry :=
  kcut (fun a n => .KFill a n c) kn wb wk wn kb kk len

/-- `kcut` at `KUnk`. -/
def kunk_cut (kn : List kentry) (wb : expr) (wk : Int) (wn : expr) (kb : expr) (kk : Int)
    (len : expr) : List kentry :=
  kcut .KUnk kn wb wk wn kb kk len

/-- A LITERAL-length `KZero`/`KFill` entry `kb+kk, +l0` of the store's own
    base spelling, trimmed around the written offsets `k, k+w`. -/
def ktrim (mk : saddr → expr → kentry) (kb : expr) (kk : Int) (l0 : Int) (k : Int)
    (w : Nat) : List kentry :=
  let l := l0 % two64
  let hi1 := min k (kk + l)
  let r1 := if kk < hi1 then [mk (SA kb kk) (.ELit (hi1 - kk))] else []
  let lo2 := max kk (k + (w : Int))
  let r2 := if lo2 < kk + l then [mk (SA kb lo2) (.ELit (kk + l - lo2))] else []
  r1 ++ r2

/-- (task 1) A `KWord kb+kk w' v` of the store's base spelling that the
    store `k, k+w` PARTIALLY overlaps: when `v` is a literal, the bytes
    below `k` and the bytes from `k+w` up survive as literal `KWord`s (byte
    slices of `v`, folded by `mkExt`); other values are dropped as before. -/
def kword_cut (kb : expr) (kk : Int) (w' : Nat) (v : expr) (k : Int) (w : Nat) : List kentry :=
  match v with
  | .ELit _ =>
      let n1 := k - kk -- bytes [kk, k)
      let r1 := if 0 < n1 then [.KWord (SA kb kk) n1.toNat (mkExt false 0 n1.toNat v)] else []
      let d := k + (w : Int) - kk -- entry offset of the first byte above the store
      let r2 :=
        if d < (w' : Int)
        then [.KWord (SA kb (kk + d)) (w' - d.toNat) (mkExt false d.toNat (w' - d.toNat) v)]
        else []
      r1 ++ r2
  | _ => []

/-- The same-base-or-not protocol shared by `KZero` and `KFill` entries
    (`mk` rebuilds the entry kind), against the store `wb+k, +w`; `apart`
    is the caller's apartness test for the entry range. -/
def prune_zf (mk : saddr → expr → kentry) (allkn : List kentry) (wb : expr) (k : Int) (w : Nat)
    (K : kentry) (kb : expr) (kk : Int) (len : expr) (apart : Unit → Bool) (hints : List Bool)
    (diffbase : Unit → List kentry × List sidecond × List Bool) :
    List kentry × List sidecond × List Bool :=
  -- `apart`/`diffbase` are thunks: under call-by-value (`vm_compute`) they
  -- are evaluated only on the paths that need them, as before
  if expr_eqb kb wb then
    match len with
    | .ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ =>
        if k + (w : Int) ≤ kk then ([K], [], hints)
        else (kcut mk allkn wb k (elen w) kb kk len, [], hints)
  else if apart () then ([K], [], hints)
  else
    match kcut mk allkn wb k (elen w) kb kk len with
    | [] => diffbase ()
    | cut => (cut, [], hints)

/-- One knowledge entry against a freshly written range `wa, wa+w`. -/
def prune1 (allkn : List kentry) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) : List kentry × List sidecond × List Bool :=
  let k := wa.a_off
  let diffbase (ka : saddr) (kl : expr) : List kentry × List sidecond × List Bool :=
    let apart := ranges_apart_x allkn wa.a_base k (elen w) ka.a_base ka.a_off kl
    if apart then ([K], [], hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj wa (elen w) ka kl], hs) -- hint: claim disjoint
      | false :: hs => ([], [], hs) -- hint: drop
      | [] => ([], [], []) -- default: drop (always sound)
  match K with
  | .KAlign _ _ => ([K], [], hints)
  | .KRange _ _ _ => ([K], [], hints)
  | .KWr _ _ => ([K], [], hints)
  | .KDisj _ _ _ _ => ([K], [], hints)
  | .KImg lo hi =>
      match wa.a_base with
      | .ELit 0 =>
          let r1 := if lo < min k hi then [.KImg lo (min k hi)] else []
          let lo2 := max lo (k + (w : Int))
          let r2 := if lo2 < hi then [.KImg lo2 hi] else []
          (r1 ++ r2, [], hints)
      | _ =>
          if hi - lo < 2 ^ 64 then diffbase (SA (.ELit 0) lo) (.ELit (hi - lo))
          else ([], [], hints)
  | .KZero ⟨kb, kk⟩ len =>
      prune_zf .KZero allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_x allkn wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KFill ⟨kb, kk⟩ len c =>
      prune_zf (fun a n => .KFill a n c) allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_x allkn wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KUnk ⟨kb, kk⟩ len =>
      prune_zf .KUnk allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_x allkn wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KWord ⟨kb, kk⟩ w' v =>
      if expr_eqb kb wa.a_base then
        (if (kk + (w' : Int) ≤ k || k + (w : Int) ≤ kk)
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints)) -- keep bytes
      else if ranges_apart_x allkn wa.a_base k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (w == 1 && w' == 1 && expr_eqb wv v)
      then ([K], [], hints) -- benign alias: a 1-byte write of the SAME value
      else diffbase (SA kb kk) (elen w')
  | .KBlob ⟨kb, kk⟩ len bk =>
      if expr_eqb kb wa.a_base then
        match len with
        | .ELit l0 =>
            let l := l0 % two64
            (if (kk + l ≤ k || k + (w : Int) ≤ kk) then ([K], [], hints) else ([], [], hints))
        | _ => if k + (w : Int) ≤ kk then ([K], [], hints) else ([], [], hints)
      else diffbase (SA kb kk) len

/-- Prune the whole knowledge list against one store. -/
def prune (allkn : List kentry) (wa : saddr) (w : Nat) (wv : expr) (kn : List kentry)
    (hints : List Bool) : List kentry × List sidecond × List Bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let (kept, scs1, hs1) := prune1 allkn wa w wv K hints
      let (r, scs2, hs2) := prune allkn wa w wv rest hs1
      (kept ++ r, scs1 ++ scs2, hs2)

/-- P2: `prune1` against a PREPARED store (`AxSymExec3Sound.prune1p_eq`,
    `prunep_eq`). -/
def prune1p (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) : List kentry × List sidecond × List Bool :=
  let k := wa.a_off
  let diffbase (ka : saddr) (kl : expr) : List kentry × List sidecond × List Bool :=
    let apart := ranges_apart_p allkn sp wa.a_base k (elen w) ka.a_base ka.a_off kl
    if apart then ([K], [], hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj wa (elen w) ka kl], hs) -- hint: claim disjoint
      | false :: hs => ([], [], hs) -- hint: drop
      | [] => ([], [], []) -- default: drop (always sound)
  match K with
  | .KAlign _ _ => ([K], [], hints)
  | .KRange _ _ _ => ([K], [], hints)
  | .KWr _ _ => ([K], [], hints)
  | .KDisj _ _ _ _ => ([K], [], hints)
  | .KImg lo hi =>
      match wa.a_base with
      | .ELit 0 =>
          let r1 := if lo < min k hi then [.KImg lo (min k hi)] else []
          let lo2 := max lo (k + (w : Int))
          let r2 := if lo2 < hi then [.KImg lo2 hi] else []
          (r1 ++ r2, [], hints)
      | _ =>
          if hi - lo < 2 ^ 64 then diffbase (SA (.ELit 0) lo) (.ELit (hi - lo))
          else ([], [], hints)
  | .KZero ⟨kb, kk⟩ len =>
      prune_zf .KZero allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_p allkn sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KFill ⟨kb, kk⟩ len c =>
      prune_zf (fun a n => .KFill a n c) allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_p allkn sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KUnk ⟨kb, kk⟩ len =>
      prune_zf .KUnk allkn wa.a_base k w K kb kk len
        (fun _ => ranges_apart_p allkn sp wa.a_base k (elen w) kb kk len) hints
        (fun _ => diffbase (SA kb kk) len)
  | .KWord ⟨kb, kk⟩ w' v =>
      if expr_eqb kb wa.a_base then
        (if (kk + (w' : Int) ≤ k || k + (w : Int) ≤ kk)
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints)) -- keep bytes
      else if ranges_apart_p allkn sp wa.a_base k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (w == 1 && w' == 1 && expr_eqb wv v)
      then ([K], [], hints) -- benign alias: a 1-byte write of the SAME value
      else diffbase (SA kb kk) (elen w')
  | .KBlob ⟨kb, kk⟩ len bk =>
      if expr_eqb kb wa.a_base then
        match len with
        | .ELit l0 =>
            let l := l0 % two64
            (if (kk + l ≤ k || k + (w : Int) ≤ kk) then ([K], [], hints) else ([], [], hints))
        | _ => if k + (w : Int) ≤ kk then ([K], [], hints) else ([], [], hints)
      else diffbase (SA kb kk) len

/-- `prune` against a prepared store. -/
def prunep (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) (hints : List Bool) : List kentry × List sidecond × List Bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let (kept, scs1, hs1) := prune1p allkn sp wa w wv K hints
      let (r, scs2, hs2) := prunep allkn sp wa w wv rest hs1
      (kept ++ r, scs1 ++ scs2, hs2)

/-! *** P3: the entry-side `base_range` of `ranges_apart_p`
    is looked up ONCE per distinct entry base during a prune pass (a store
    meets dozens of entries over the same handful of bases).  `prunepc` =
    `prunep` by theorem (`AxSymExec3Sound.prunepc_eq`). -/

/-- `ranges_apart_p` with the entry-side base range supplied. -/
def ranges_apart_pc (kn : List kentry) (sp : sprep) (b1 : expr) (k1 : Int) (n1 : expr)
    (br2 : Option (Int × Int)) (b2 : expr) (k2 : Int) (n2 : expr) : Bool :=
  match n1, n2 with
  | .ELit z1, .ELit z2 =>
      let m1 := zlit64 z1
      let m2 := zlit64 z2
      if (match sp.sp_rng, br2 with
          | some (lo1, hi1), some (lo2, hi2) =>
              (hi1 + k1 + m1 ≤ lo2 + k2 || hi2 + k2 + m2 ≤ lo1 + k1)
          | _, _ => false) then true
      else if in_sides kn sp.sp_D b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp.sp_rng, br2, sp.sp_h1, xhi kn n2 with
        | some (lo1, hi1), some (lo2, hi2), some h1, some h2 =>
            if (hi1 + k1 + h1 ≤ lo2 + k2 || hi2 + k2 + h2 ≤ lo1 + k1) then true
            else -- joint END facts of symbolic-length ranges
            if le_end (end_hi kn b1 k1 n1 lo1 hi1 h1) (lo2 + k2) then true
            else le_end (end_hi kn b2 k2 n2 lo2 hi2 h2) (lo1 + k1)
        | _, _, _, _ => false) then true
    else if in_sides_x kn sp.sp_Dx b2 k2 n2 then true
    else if !(shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1), (n1, 0)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2), (n2, 0)]

/-- The entry base whose `base_range` `prune1p` may consult
    (KZero/KWord/KBlob). -/
def kbase : kentry → Option expr
  | .KZero ⟨kb, _⟩ _ | .KWord ⟨kb, _⟩ _ _ | .KBlob ⟨kb, _⟩ _ _
  | .KFill ⟨kb, _⟩ _ _ | .KUnk ⟨kb, _⟩ _ => some kb
  | _ => none

/-- `prune1p` with the entry-side base range `br2` supplied. -/
def prune1pc (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr) (K : kentry)
    (hints : List Bool) (br2 : Option (Int × Int)) :
    List kentry × List sidecond × List Bool :=
  let k := wa.a_off
  let diffbase (ka : saddr) (kl : expr) : List kentry × List sidecond × List Bool :=
    let apart := ranges_apart_pc allkn sp wa.a_base k (elen w) br2 ka.a_base ka.a_off kl
    if apart then ([K], [], hints)
    else
      match hints with
      | true :: hs => ([K], [.SCDisj wa (elen w) ka kl], hs)
      | false :: hs => ([], [], hs)
      | [] => ([], [], [])
  match K with
  | .KAlign _ _ | .KRange _ _ _ | .KWr _ _ | .KDisj _ _ _ _ | .KImg _ _ =>
      prune1p allkn sp wa w wv K hints
  | .KZero ⟨kb, kk⟩ len =>
      if expr_eqb kb wa.a_base then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kzero_cut allkn wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KFill ⟨kb, kk⟩ len c =>
      if expr_eqb kb wa.a_base then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kfill_cut c allkn wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KUnk ⟨kb, kk⟩ len =>
      if expr_eqb kb wa.a_base then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp wa.a_base k (elen w) br2 kb kk len then ([K], [], hints)
      else
        match kunk_cut allkn wa.a_base k (elen w) kb kk len with
        | [] => diffbase (SA kb kk) len
        | cut => (cut, [], hints)
  | .KWord ⟨kb, kk⟩ w' v =>
      if expr_eqb kb wa.a_base then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp wa.a_base k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (w == 1 && w' == 1 && expr_eqb wv v)
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | .KBlob ⟨kb, kk⟩ len bk =>
      if expr_eqb kb wa.a_base then prune1p allkn sp wa w wv K hints
      else diffbase (SA kb kk) len

/-- Look a base range up in the cache. -/
def br_lookup (c : List (expr × Option (Int × Int))) (b : expr) : Option (Option (Int × Int)) :=
  match c with
  | [] => none
  | (b', r) :: rest => if expr_eqb b b' then some r else br_lookup rest b

/-- `prunep` with the entry-side base ranges cached. -/
def prunepc (allkn : List kentry) (sp : sprep) (wa : saddr) (w : Nat) (wv : expr)
    (kn : List kentry) (hints : List Bool) (cache : List (expr × Option (Int × Int))) :
    List kentry × List sidecond × List Bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let (br2, cache') :=
        match kbase K with
        | some kb =>
            match br_lookup cache kb with
            | some r => (r, cache)
            | none =>
                let r := base_range allkn kb
                (r, (kb, r) :: cache)
        | none => (none, cache)
      let (kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2
      let (r, scs2, hs2) := prunepc allkn sp wa w wv rest hs1 cache'
      (kept ++ r, scs1 ++ scs2, hs2)

/-- Knowledge about `mem_denot E base log` from knowledge about `base`:
    process the log oldest-first, each store pruning what it overlaps and
    then recording itself. -/
def carry (log : List sentry) (kn : List kentry) (hints : List Bool) :
    List kentry × List sidecond × List Bool :=
  match log with
  | [] => (kn, [], hints)
  | ⟨a, w, v⟩ :: older =>
      let (kn1, scs1, hs1) := carry older kn hints
      let fk := facts_of kn1
      let (kn2, scs2, hs2) :=
        prunepc fk (mk_sprep fk a.a_base a.a_off (elen w)) a w v kn1 hs1 [] -- P2/P3
      (.KWord a w v :: kn2, scs1 ++ scs2, hs2)


/-- `evalS_def` is a sound pre-filter for `evalS`. -/
theorem evalS_def_None (s e : expr) (z : Int) (H : evalS_def s e = false) :
    evalS s z e = none := by
  revert z
  induction e with
  | ELit w =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.ELit w) s) = true
      · simp [h] at H
      · rw [ite_eq_right h, evalS_def_go.eq_1] at H
        exact absurd H (by simp)
  | EVar n =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EVar n) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_2]
  | EAlu op a b iha ihb =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EAlu op a b) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_3]
        by_cases ha : evalS_def s a = true
        · rw [ite_eq_right h, evalS_def_go.eq_3, ite_eq_left ha] at H
          cases hsa : evalS s z a with
          | none => rfl
          | some x => rw [ihb H z]
        · have ha' : evalS_def s a = false := by simpa using ha
          rw [iha ha' z]
  | EAluw op a b iha ihb =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EAluw op a b) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_4]
        by_cases ha : evalS_def s a = true
        · rw [ite_eq_right h, evalS_def_go.eq_4, ite_eq_left ha] at H
          cases hsa : evalS s z a with
          | none => rfl
          | some x => rw [ihb H z]
        · have ha' : evalS_def s a = false := by simpa using ha
          rw [iha ha' z]
  | EMd op a b iha ihb =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EMd op a b) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_5]
        by_cases ha : evalS_def s a = true
        · rw [ite_eq_right h, evalS_def_go.eq_5, ite_eq_left ha] at H
          cases hsa : evalS s z a with
          | none => rfl
          | some x => rw [ihb H z]
        · have ha' : evalS_def s a = false := by simpa using ha
          rw [iha ha' z]
  | EMdw op a b iha ihb =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EMdw op a b) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_6]
        by_cases ha : evalS_def s a = true
        · rw [ite_eq_right h, evalS_def_go.eq_6, ite_eq_left ha] at H
          cases hsa : evalS s z a with
          | none => rfl
          | some x => rw [ihb H z]
        · have ha' : evalS_def s a = false := by simpa using ha
          rw [iha ha' z]
  | EExt sx lo n a ih =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EExt sx lo n a) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_7]
        have ha : evalS_def s a = false := by
          rw [ite_eq_right h, evalS_def_go.eq_7] at H
          exact H
        rw [ih ha z]
  | EBlob sx k i n =>
      intro z
      rw [evalS_def.eq_1] at H
      by_cases h : (expr_eqb (expr.EBlob sx k i n) s) = true
      · simp [h] at H
      · rw [evalS.eq_1, ite_eq_right h, evalS_go.eq_8]

/-- The pre-filter is transparent: both sweeps agree. -/
theorem conc_try_eq (kn : List kentry) (e : expr) (cands : List expr) :
    conc_try kn e cands = conc_try_ref kn e cands := by
  induction cands with
  | nil => rfl
  | cons s rest ih =>
      simp only [conc_try, conc_try_ref]
      rw [ih]
      by_cases hc : (closedb s) = true
      · rw [ite_eq_left hc, ite_eq_left hc]
      · rw [ite_eq_right hc, ite_eq_right hc]
        by_cases hd : evalS_def s e = true
        · rw [ite_eq_right (by simp [hd])]
        · have hd' : evalS_def s e = false := by simpa using hd
          rw [ite_eq_left (by simp [hd'])]
          cases hr : erange kn s with
          | none => rfl
          | some p =>
              obtain ⟨lo, hi⟩ := p
              simp only []
              by_cases hb : hi - lo ≤ conc_limit
              · rw [ite_eq_left hb, evalS_def_None s e (wrap64 lo) hd']
              · rw [ite_eq_right hb]

/-- Filling preserves soundness. -/
theorem mk_itab_fuel_sound (segs : List Segment) (n : Nat) (pc : Int) (t : itab)
    (Ht : itab_sound segs t) : itab_sound segs (mk_itab_fuel segs n pc t) := by
  induction n generalizing pc t with
  | zero => exact Ht
  | succ n ih =>
      refine ih (pc + 4)
        (match pc, itab_entry segs pc with
         | .ofNat m, some i => if 0 < m then pt_set m i t else t
         | _, _ => t) ?_
      intro pc' i' Hi'
      split at Hi'
      · rename_i m i hentry
        by_cases hm : 0 < m
        · rw [ite_eq_left hm] at Hi'
          unfold itab_lookup at Hi'
          by_cases hp : 0 < pc'
          · rw [ite_eq_left hp] at Hi'
            by_cases he : pc'.toNat = m
            · rw [he, pt_gss] at Hi'
              injection Hi' with h
              have hpc : pc' = (m : Int) := by
                have h1 : ((pc'.toNat : Nat) : Int) = pc' := Int.toNat_of_nonneg (by omega)
                rw [← h1, he]
              rw [hpc]
              exact hentry.trans (by rw [h])
            · rw [pt_gso _ _ _ _ he] at Hi'
              exact Ht pc' i' (by unfold itab_lookup; rw [ite_eq_left hp]; exact Hi')
          · rw [ite_eq_right hp] at Hi'
            exact absurd Hi' (by simp)
        · rw [ite_eq_right hm] at Hi'
          exact Ht pc' i' Hi'
      · exact Ht pc' i' Hi'

/-- The freshly built table is sound. -/
theorem mk_itab_sound (segs : List Segment) (lo : Int) (n : Nat) :
    itab_sound segs (mk_itab segs lo n) := by
  refine mk_itab_fuel_sound segs n lo .PTLeaf ?_
  intro pc i Hi
  unfold itab_lookup at Hi
  by_cases hp : 0 < pc
  · rw [ite_eq_left hp, pt_get_leaf] at Hi
    exact absurd Hi (by simp)
  · rw [ite_eq_right hp] at Hi
    exact absurd Hi (by simp)

namespace LinuxSem.Common.AxSymExec3

/-- Distinct small `Int`s are distinct 5-bit register indices. -/
theorem reg_neq (a b : Int) (Ha : 0 ≤ a ∧ a < 32) (Hb : 0 ≤ b ∧ b < 32) (Hne : a ≠ b) :
    (Z_to_bv 5 a : reg) ≠ Z_to_bv 5 b := by
  intro Heq
  have h := congrArg BitVec.toNat Heq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt] at h
  have h3 : a % ((2 ^ 5 : Nat) : Int) = b % ((2 ^ 5 : Nat) : Int) := by
    have h4 := congrArg (fun n : Nat => (n : Int)) h
    rwa [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))] at h4
  rw [Int.emod_eq_of_lt Ha.1 (by omega), Int.emod_eq_of_lt Hb.1 (by omega)] at h3
  exact Hne h3

end LinuxSem.Common.AxSymExec3

