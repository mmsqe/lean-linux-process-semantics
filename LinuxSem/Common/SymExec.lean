/-
  * Common.SymExec — a REFLECTIVE certified symbolic executor (prototype).

  EXPLORATION / PROTOTYPE.  This file is an alternative to the
  per-instruction tactic route of `PropExec`/`StepTac`: instead of one
  `eapply step_* ; ...` block per instruction, a straight line of
  instructions is discharged by a single application of one soundness
  theorem whose hypothesis is a `vm_compute`d equation over DEEP SYNTAX.

  The three pieces:

  - `expr` — a deep-embedded symbolic value language.  Its constructors mirror
    the ISA's own value primitives (`Sem.alu64`, `Sem.alu32`, `Sem.mul_div`),
    which is what makes the soundness proof one line per instruction: the
    generic step lemmas `PropExec.step_opimm_gen` & co. are already stated in
    exactly those terms.  Literals are plain `Int` (never `bv`) so that
    nothing `vm_compute` ever touches contains a bitvector — see the OOM trap
    below.
  - `sym_state` — a literal `Int` pc, a list of `expr` for the 32 registers,
    and a SYMBOLIC MEMORY: a store log over an opaque base memory.  Its
    DENOTATION `st_ok` into a real `machine_state` takes the log to a fold
    of `CatExec.wbytes` — the same layering the tactic route builds by hand.
  - `sym_exec` — a computable fixpoint that fetches, decodes and steps from
    the current symbolic pc, accumulating side conditions, and stops
    cleanly at anything it does not model.  `sym_exec_sound` turns a
    successful run into `CatSim.msteps`.

  THE MEMORY MODEL, in one paragraph.  An address is kept in the normal
  form `saddr` = "symbolic base + literal offset", where a base is either
  the literal 0 (`SBLit` — globals, `.data`, image constants) or an
  ambient symbolic value (`SBVar n` — the ASLR `sp`, a heap pointer, an
  argv-derived pointer).  A load walks the log (`sm_lookup`): with the
  SAME base the offsets decide hit / free-skip / stuck by `Int` arithmetic
  that `vm_compute` settles; with DIFFERENT bases it emits an
  `SCDisjoint` obligation and carries on, so cross-base reasoning is
  first class rather than assumed away.  A load that falls through the
  whole log emits `SCReadBase`, the hook for the per-image `rdn` facts a
  proof already has, and its result is a fresh `EVar`.  A store emits
  `SCStoreOk` stated against the ORIGINAL memory — `mem_denot_grows` and
  `StoreOk.store_ok_mono` lift it through the chain — so a store site
  never peels an overlay.  `Common/Footprint` is where a binary states
  its layout once and discharges the `SCFlat`/`SCDisjoint` batch.

  TRAP AVOIDANCE.  Everything `sym_exec` computes over is closed: `Int`
  literals, register indices, and the (closed) memory image.  Symbolic
  quantities — the ASLR stack pointer, argc, input bytes — appear only as
  `EVar n`, interpreted by a valuation `env : Nat → word` that
  `vm_compute` never sees.  In particular a `vm_compute`d
  `sym_exec segs fuel dirs ss0 []` contains no `bv` variable.

  WHAT IS *NOT* HERE.  Loads `lb` and `lh`
  and stores `sh`/`sw` (no value-precise step lemma exists for them);
  a log hit at anything other than an exact 8-byte slot (a narrow
  reload of a wider slot needs byte-extraction `expr`s); a data-
  dependent offset (a bump allocator advancing by a symbolic length);
  a read spanning several log entries (a buffer filled by a loop);
  `ecall` and compressed encodings.  In every one of those cases
  `sym_step` returns `none`, which makes `sym_exec` stop at that
  instruction and hand the state back to the existing tactic layer.
  Nothing is admitted (no proof hole, no extra postulate).

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  Conventions: `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` →
  `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)`, `bv_signed w`
  → `w.toInt`, `Z.of_nat n` → `(n : Int)`, `Z.land z (-2)` → this tree's
  `PropExec.zland_m2 z` (the same function on every `Int`),
  `Z.eqb`/`Z.leb`/`Z.ltb` → `==`/`≤`/`<` on the `decide`-side,
  `list` → `List`, `option` → `Option`, `Record` → `structure`,
  `Inductive` → `inductive`, `Forall P l` → `∀ x ∈ l, P x` (the
  repo-wide spelling of `List.Forall`), `lia` → `omega`,
  `injection H as <- <-` → `cases H` / `simp` at the hypothesis.

  `step_sb`/`step_sd_val`/`step_ld`/`step_lbu`/`step_lhu`/`step_lwu` and
  every `step_*_gen` used below likewise live in `PropExec`/`SeqExec`.

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
import LinuxSem.Common.Footprint

namespace LinuxSem.Common.SymExec

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StoreOk
open LinuxSem.Common.Footprint

/-- `Section WithFP1. Context {fx : FPState}.`: every step lemma
    the soundness proof applies is stated over an ambient FP state, so the
    whole file lives in that section.  `fx0` is the state at process entry,
    exactly as `Common/StoreOk.lean` does it. -/
local instance symexec_fx : FPState := fx0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

/-! ## 1. The symbolic value language -/

/-- A symbolic 64-bit value.  `ELit z` denotes `BitVec.ofInt 64 z` (so the
    literal is an ordinary `Int` and folding is `Int` arithmetic — no `bv`
    ever enters a `vm_compute`d term).  `EVar n` denotes `E n` for the
    ambient valuation; this is how the quantified initial `sp`, `argc`
    and any input-dependent value get in.

    The remaining four constructors are the ISA's own value primitives,
    so that `edenot` of a symbolic register is SYNTACTICALLY the value
    the generic `step_*_gen` lemmas write back. -/
inductive expr : Type
  /-- `BitVec.ofInt 64 z`. -/
  | ELit (z : Int)
  /-- `E n`, the ambient valuation. -/
  | EVar (n : Nat)
  /-- `alu64 op a b`. -/
  | EAlu (op : AluOp) (a b : expr)
  /-- `sext 64 (alu32 op (low32 a) (low32 b))`. -/
  | EAluw (op : AluOp) (a b : expr)
  /-- `mul_div op a b`. -/
  | EMd (op : MulOp) (a b : expr)
  /-- `sext 64 (mul_div op (low32 a) (low32 b))`. -/
  | EMdw (op : MulOp) (a b : expr)
  deriving DecidableEq, Repr

/-- The ambient valuation: the values of the quantified symbolic inputs.
    `sym_exec` never looks at it (it only ever appears as `EVar n`). -/
abbrev env : Type := Nat → word

/-- Denotation of a symbolic value. -/
def edenot (E : env) : expr → word
  | .ELit z => BitVec.ofInt 64 z
  | .EVar n => E n
  | .EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | .EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | .EMd op a b => mul_div op (edenot E a) (edenot E b)
  | .EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))

/-! ### Z-level plumbing for literals -/

/-- Two `Int`s congruent mod `2^64` denote the same word.  The single
    congruence step every literal lemma below goes through. -/
theorem ofInt64_congr {x y : Int} (h : x % ((2 ^ 64 : Nat) : Int) = y % ((2 ^ 64 : Nat) : Int)) :
    BitVec.ofInt 64 x = BitVec.ofInt 64 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  rw [h]

/-- `BitVec.ofInt` of a `toNat` is the word itself. -/
theorem ofInt64_toNat (w : word) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The unsigned reading of `BitVec.ofInt 64 z` is `z mod 2^64`. -/
theorem toNat_ofInt64 (p : Int) :
    ((BitVec.ofInt 64 p).toNat : Int) = p % ((2 ^ 64 : Nat) : Int) := by
  rw [BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

/-- `ofInt` commutes with subtraction.  (Lean core has `BitVec.ofInt_add`
    and `BitVec.ofInt_neg` but no subtraction version.) -/
theorem ofInt64_sub (x y : Int) :
    BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- The `BvBase`-level `+`/`-` bridges: this tree's value shapes (`v_add`,
    `v_sub`, `v_addi`, …) are `BitVec` arithmetic in disguise.  Stating
    them this way lets every literal lemma below be a `BitVec` rewrite
    instead of an `Int`-modularity argument. -/
theorem ofInt64_ofNat_add (a : word) (i : Int) :
    BitVec.ofInt 64 ((a.toNat : Int) + i) = a + BitVec.ofInt 64 i := by
  rw [BitVec.ofInt_add, ofInt64_toNat]

theorem ofInt64_ofNat_sub (a : word) (i : Int) :
    BitVec.ofInt 64 ((a.toNat : Int) - i) = a - BitVec.ofInt 64 i := by
  rw [ofInt64_sub, ofInt64_toNat]

theorem ofInt64_ofNat_add2 (a b : word) :
    BitVec.ofInt 64 ((a.toNat : Int) + (b.toNat : Int)) = a + b := by
  rw [BitVec.ofInt_add, ofInt64_toNat, ofInt64_toNat]

theorem ofInt64_ofNat_sub2 (a b : word) :
    BitVec.ofInt 64 ((a.toNat : Int) - (b.toNat : Int)) = a - b := by
  rw [ofInt64_sub, ofInt64_toNat, ofInt64_toNat]

theorem v_addi_eq (x : word) (i : Int) : v_addi x i = x + BitVec.ofInt 64 i := by
  unfold v_addi
  exact ofInt64_ofNat_add x i

theorem v_add_eq (x y : word) : v_add x y = x + y := ofInt64_ofNat_add2 x y

theorem v_sub_eq (x y : word) : v_sub x y = x - y := ofInt64_ofNat_sub2 x y

/-- The ALU's `ADD` is `BitVec` addition. -/
theorem alu64_add_eq (x y : word) : alu64 .ADD x y = x + y := by rw [alu_add, v_add_eq]

/-- The ALU's `SUB` is `BitVec` subtraction. -/
theorem alu64_sub_eq (x y : word) : alu64 .SUB x y = x - y := by rw [alu_sub, v_sub_eq]

/-- A wrapped literal is the literal. -/
theorem ofInt64_wrap (z : Int) : BitVec.ofInt 64 (bv_wrap 64 z) = BitVec.ofInt 64 z := by
  apply ofInt64_congr
  show (z % _) % _ = z % _
  rw [Int.emod_emod]

theorem Z_to_bv64_wrap_l (a b : Int) :
    BitVec.ofInt 64 (bv_wrap 64 a + b) = BitVec.ofInt 64 (a + b) := by
  rw [BitVec.ofInt_add, ofInt64_wrap, ← BitVec.ofInt_add]

theorem Z_to_bv64_wrap_r (a b : Int) :
    BitVec.ofInt 64 (a + bv_wrap 64 b) = BitVec.ofInt 64 (a + b) := by
  rw [BitVec.ofInt_add, ofInt64_wrap, ← BitVec.ofInt_add]

theorem Z_to_bv64_wrap_sub (a b : Int) :
    BitVec.ofInt 64 (bv_wrap 64 a - bv_wrap 64 b) = BitVec.ofInt 64 (a - b) := by
  rw [ofInt64_sub, ofInt64_wrap, ofInt64_wrap, ← ofInt64_sub]

/-- The pc of a symbolic state is an `Int`; every straight-line instruction
    advances it by 4 through `v_addi`.  This is the only lemma that keeps
    the pc a literal. -/
theorem v_addi_lit (p i : Int) : v_addi (BitVec.ofInt 64 p) i = BitVec.ofInt 64 (p + i) := by
  rw [v_addi_eq, ← BitVec.ofInt_add]

theorem btgt_lit (p i : Int) : btgt (BitVec.ofInt 64 p) i = BitVec.ofInt 64 (p + i) :=
  v_addi_lit p i

theorem v_auipc_lit (p i : Int) : v_auipc (BitVec.ofInt 64 p) i = BitVec.ofInt 64 (i + p) := by
  unfold v_auipc
  rw [toNat_ofInt64]
  exact Z_to_bv64_wrap_r i p

/-- The jalr target of a literal pc, as a literal. -/
theorem jalr_tgt_lit (z i : Int) :
    jalr_tgt (BitVec.ofInt 64 z) i = BitVec.ofInt 64 (zland_m2 (bv_wrap 64 z + i)) := by
  unfold jalr_tgt jalr_tgtZ bv_wrap
  rw [toNat_ofInt64]

/-- `sext`/`zext` on a literal.  Both are definitionally `BitVec.ofInt` of the
    signed/unsigned value, which is what lets the immediates of the decoded
    AST become `ELit`s.  (The width bound is explicit: Lean's
    `BitVec.signExtend` truncates for wider sources.) -/
theorem sext64_lit {n : Nat} (b : BitVec n) (hn : n ≤ 64) :
    sext 64 b = BitVec.ofInt 64 b.toInt :=
  sext_eq_ofInt b hn

theorem zext_lit {n m : Nat} (b : BitVec n) (hn : n ≤ m) :
    zext m b = BitVec.ofInt m (b.toNat : Int) := by
  apply BitVec.eq_of_toNat_eq
  have hb : (b.toNat : Int) % ((2 ^ m : Nat) : Int) = (b.toNat : Int) := by
    apply Int.emod_eq_of_lt
    · omega
    · have := b.isLt
      have h2 : (2 ^ n : Nat) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hn
      omega
  rw [BitVec.toNat_ofInt, hb, Int.toNat_natCast]
  unfold zext
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by
    have := b.isLt
    have h2 : (2 ^ n : Nat) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hn
    omega)

theorem zext64_lit {n : Nat} (b : BitVec n) (hn : n ≤ 64) :
    zext 64 b = BitVec.ofInt 64 (b.toNat : Int) :=
  zext_lit b hn

theorem bv_wrap_32_64 (z : Int) : bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z := by
  show z % ((2 ^ 64 : Nat) : Int) % ((2 ^ 32 : Nat) : Int) = z % ((2 ^ 32 : Nat) : Int)
  exact Int.emod_emod_of_dvd z (by decide)

/-- `low32 (BitVec.ofInt 64 z) = BitVec.ofInt 32 z`: the low half of a
    literal is a literal. -/
theorem low32_lit (z : Int) : low32 (BitVec.ofInt 64 z) = BitVec.ofInt 32 z := by
  apply BitVec.eq_of_toNat_eq
  simp only [low32, bits, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero,
    Nat.mod_one]
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg (Int.emod_nonneg z (by decide)),
    Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))]
  exact Int.emod_emod_of_dvd z (by decide)

theorem sext32_low32 {n : Nat} (b : BitVec n) (hn : n ≤ 32) :
    sext 32 b = low32 (BitVec.ofInt 64 b.toInt) := by
  rw [sext_eq_ofInt b hn, low32_lit]

theorem zext32_low32 {n : Nat} (b : BitVec n) (hn : n ≤ 32) :
    zext 32 b = low32 (BitVec.ofInt 64 (b.toNat : Int)) := by
  rw [zext_lit b hn, low32_lit]

/-! ### Smart constructors: constant folding -/

/-- Folding `ALU_ADD`/`ALU_SUB` on literals is what keeps a real compiled
    prologue's `li`/`mv`/`addi` chain collapsed to one `ELit` per register
    instead of a growing tree.  The nested cases
    (`(base + x) + y ~> base + (x+y)`) are what keeps a SYMBOLIC base —
    `sp` after two `addi sp,sp,-16`s, or a heap pointer that has been
    bumped twice — in the `EVar n + literal` normal form that `to_saddr`
    below recognises as an address.  (The other eight `AluOp`s and the
    `MulOp`s fold the same way; each costs one more three-line lemma of
    the shape below.) -/
def mkAlu (op : AluOp) (a b : expr) : expr :=
  match op with
  | .ADD =>
    match b with
    | .ELit y =>
      match a with
      | .ELit x => .ELit (x + y)
      | .EAlu .ADD a' (.ELit x) => .EAlu .ADD a' (.ELit (x + y))
      | _ => .EAlu .ADD a b
    | _ => .EAlu .ADD a b
  | .SUB =>
    match b with
    | .ELit y =>
      match a with
      | .ELit x => .ELit (x - y)
      | .EAlu .ADD a' (.ELit x) => .EAlu .ADD a' (.ELit (x - y))
      | _ => .EAlu .SUB a b
    | _ => .EAlu .SUB a b
  | _ => .EAlu op a b

theorem alu64_add_lit (x y : Int) :
    alu64 .ADD (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (x + y) := by
  rw [alu64_add_eq, ← BitVec.ofInt_add]

theorem alu64_sub_lit (x y : Int) :
    alu64 .SUB (BitVec.ofInt 64 x) (BitVec.ofInt 64 y) = BitVec.ofInt 64 (x - y) := by
  rw [alu64_sub_eq, ← ofInt64_sub]

/-- `(a + x) - y = a + (x-y)` on the ALU, all literals. -/
theorem Z_to_bv64_wrap_sub_l (a b : Int) :
    BitVec.ofInt 64 (bv_wrap 64 a - b) = BitVec.ofInt 64 (a - b) := by
  rw [ofInt64_sub, ofInt64_wrap, ← ofInt64_sub]

theorem Z_to_bv64_wrap_sub_r (a b : Int) :
    BitVec.ofInt 64 (a - bv_wrap 64 b) = BitVec.ofInt 64 (a - b) := by
  rw [ofInt64_sub, ofInt64_wrap, ← ofInt64_sub]

/-- The two "register plus literal" normal forms, as `Int` arithmetic on
    the unsigned reading.  Everything below rewrites through these. -/
theorem v_add_lit (u : word) (x : Int) :
    v_add u (BitVec.ofInt 64 x) = BitVec.ofInt 64 ((u.toNat : Int) + x) := by
  rw [v_add_eq, BitVec.ofInt_add, ofInt64_toNat]

theorem v_add_comm (x y : word) : v_add x y = v_add y x := by
  rw [v_add_eq, v_add_eq, BitVec.add_comm]

theorem v_sub_lit (u : word) (x : Int) :
    v_sub u (BitVec.ofInt 64 x) = BitVec.ofInt 64 ((u.toNat : Int) - x) := by
  rw [v_sub_eq, ofInt64_sub, ofInt64_toNat]

theorem alu64_add_add_lit (u : word) (x y : Int) :
    alu64 .ADD (alu64 .ADD u (BitVec.ofInt 64 x)) (BitVec.ofInt 64 y)
      = alu64 .ADD u (BitVec.ofInt 64 (x + y)) := by
  rw [alu64_add_eq, alu64_add_eq, alu64_add_eq, BitVec.add_assoc, ← BitVec.ofInt_add]

theorem alu64_add_sub_lit (u : word) (x y : Int) :
    alu64 .SUB (alu64 .ADD u (BitVec.ofInt 64 x)) (BitVec.ofInt 64 y)
      = alu64 .ADD u (BitVec.ofInt 64 (x - y)) := by
  simp only [alu64_sub_eq, alu64_add_eq]
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ofInt64_sub, BitVec.sub_eq_add_neg]

/-- `mkAlu` preserves the denotation — the folding is sound, in exactly the
    ISA's own value primitives. -/
theorem mkAlu_denot (E : env) (op : AluOp) (a b : expr) :
    edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b) := by
  cases op with
  | ADD =>
    cases b with
    | ELit y =>
      cases a with
      | ELit x => simp only [mkAlu, edenot]; exact (alu64_add_lit x y).symm
      | EVar n => rfl
      | EAlu op a1 a2 =>
        cases op with
        | ADD =>
          cases a2 with
          | ELit x => simp only [mkAlu, edenot]; exact (alu64_add_add_lit (edenot E a1) x y).symm
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | SUB =>
    cases b with
    | ELit y =>
      cases a with
      | ELit x => simp only [mkAlu, edenot]; exact (alu64_sub_lit x y).symm
      | EVar n => rfl
      | EAlu op a1 a2 =>
        cases op with
        | ADD =>
          cases a2 with
          | ELit x => simp only [mkAlu, edenot]; exact (alu64_add_sub_lit (edenot E a1) x y).symm
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-! ## 2. The symbolic register file and state -/

/-- A register index as a `Nat`. -/
def ridx (r : reg) : Nat := r.toNat

theorem ridx_inj {r r' : reg} (H : ridx r = ridx r') : r = r' := by
  apply BitVec.eq_of_toNat_eq
  simpa [ridx] using H

/-- Register 0 is not stored: `sr_get` answers `ELit 0` for it, matching
    `getr`'s hard-wired x0. -/
def sr_get (sr : List expr) (r : reg) : expr :=
  if bv_eqb r 0 then .ELit 0 else sr.getD (ridx r) (.ELit 0)

/-- A total update: extends the list with `ELit 0` padding rather than
    carrying a `length sr = 32` invariant. -/
def sr_upd : List expr → Nat → expr → List expr
  | [], 0, e => [e]
  | _ :: t, 0, e => e :: t
  | [], n + 1, e => .ELit 0 :: sr_upd [] n e
  | h :: t, n + 1, e => h :: sr_upd t n e

theorem nth_sr_upd (n : Nat) (sr : List expr) (e : expr) (i : Nat) :
    (sr_upd sr n e).getD i (.ELit 0) = if i = n then e else sr.getD i (.ELit 0) := by
  induction n generalizing sr i with
  | zero =>
    cases sr with
    | nil => cases i <;> simp [sr_upd]
    | cons h t => cases i <;> simp [sr_upd]
  | succ n ih =>
    cases sr with
    | nil =>
      cases i with
      | zero => simp [sr_upd]
      | succ i => simp only [sr_upd, List.getD_cons_succ, Nat.succ.injEq, ih, List.getD_nil,
          ite_true]
    | cons h t =>
      cases i with
      | zero => simp [sr_upd]
      | succ i => simp only [sr_upd, List.getD_cons_succ, Nat.succ.injEq, ih]

/-! ## 2b. Symbolic addresses and the store log -/

/-- An address is kept in the NORMAL FORM "symbolic base + literal
    offset".  A base is either the literal 0 (`SBLit` — absolute
    addresses: globals, .data, an image constant) or one of the ambient
    symbolic values (`SBVar n` — the ASLR `sp`, a heap pointer returned
    by mmap/brk, an argv-derived pointer).  Nothing else: this is what
    makes the load resolver's offset arithmetic plain `Int` arithmetic,
    which `vm_compute` decides.

    Cross-base reasoning is FIRST CLASS: two different bases are never
    assumed disjoint, they emit an `SCDisjoint` obligation. -/
inductive sbase : Type
  | SBLit
  | SBVar (n : Nat)
  deriving DecidableEq, Repr

def sbase_eqb (b1 b2 : sbase) : Bool :=
  match b1, b2 with
  | .SBLit, .SBLit => true
  | .SBVar n, .SBVar m => n == m
  | _, _ => false

theorem sbase_eqb_eq {b1 b2 : sbase} (H : sbase_eqb b1 b2 = true) : b1 = b2 := by
  cases b1 <;> cases b2 <;> simp [sbase_eqb] at H ⊢
  case SBVar.SBVar n m => rw [H]

/-- A symbolic address: a base plus a literal offset. -/
structure saddr where
  a_base : sbase
  a_off : Int
  deriving DecidableEq, Repr

/-- The  constructor `SA b k`. -/
abbrev SA (b : sbase) (k : Int) : saddr := ⟨b, k⟩

/-- A store log entry: address, width in bytes, stored value. -/
structure sentry where
  e_addr : saddr
  e_width : Nat
  e_val : expr
  deriving DecidableEq, Repr

/-- The  constructor `SE a w v`. -/
abbrev SE (a : saddr) (w : Nat) (v : expr) : sentry := ⟨a, w, v⟩

def bdenot (E : env) (b : sbase) : word :=
  match b with
  | .SBLit => BitVec.ofInt 64 0
  | .SBVar n => E n

/-- Written with `v_addi` — exactly the shape the machine's addressing
    mode produces — so that the address side of every load/store lemma
    matches by `rewrite`, not by `bv` normalisation. -/
def adenot (E : env) (a : saddr) : word :=
  v_addi (bdenot E a.a_base) a.a_off

/-- Recognise "[expr] used as a base register, plus a displacement" as a
    symbolic address.  Anything else stops the executor. -/
def to_saddr (e : expr) (i : Int) : Option saddr :=
  match e with
  | .ELit z => some (SA .SBLit (z + i))
  | .EVar n => some (SA (.SBVar n) i)
  | .EAlu .ADD (.EVar n) (.ELit z) => some (SA (.SBVar n) (z + i))
  | .EAlu .ADD (.ELit z) (.EVar n) => some (SA (.SBVar n) (z + i))
  | _ => none

theorem u_Z_to_bv64_0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by decide

/-- The displacement is exactly the machine's addressing mode. -/
theorem to_saddr_denot (E : env) (e : expr) (i : Int) (a : saddr)
    (H : to_saddr e i = some a) : adenot E a = v_addi (edenot E e) i := by
  unfold adenot
  cases e with
  | ELit z =>
    simp only [to_saddr, Option.some.injEq] at H
    subst H
    show v_addi (BitVec.ofInt 64 0) (z + i) = v_addi (BitVec.ofInt 64 z) i
    rw [v_addi_lit, v_addi_lit]
    rw [Int.zero_add]
  | EVar n =>
    simp only [to_saddr, Option.some.injEq] at H
    subst H
    rfl
  | EAlu op e1 e2 =>
    cases op with
    | ADD =>
      cases e1 with
      | ELit z1 =>
        cases e2 with
        | EVar n =>
          simp only [to_saddr, Option.some.injEq] at H
          subst H
          show v_addi (E n) (z1 + i) = v_addi (alu64 .ADD (BitVec.ofInt 64 z1) (E n)) i
          rw [alu64_add_eq, v_addi_eq, v_addi_eq, BitVec.ofInt_add]
          bv_omega
        | _ => simp [to_saddr] at H
      | EVar n =>
        cases e2 with
        | ELit z2 =>
          simp only [to_saddr, Option.some.injEq] at H
          subst H
          show v_addi (E n) (z2 + i) = v_addi (alu64 .ADD (E n) (BitVec.ofInt 64 z2)) i
          rw [alu64_add_eq, v_addi_eq, v_addi_eq, BitVec.ofInt_add, BitVec.add_assoc]
        | _ => simp [to_saddr] at H
      | _ => simp [to_saddr] at H
    | _ => simp [to_saddr] at H
  | EAluw op e1 e2 => simp [to_saddr] at H
  | EMd op e1 e2 => simp [to_saddr] at H
  | EMdw op e1 e2 => simp [to_saddr] at H

/-! ### The state -/

/-- `s_log` is the store log, MOST RECENT FIRST; `s_next` is the next
    free valuation index (fresh symbolic values for bytes read out of
    the base memory are `EVar` at these indices, starting at 32 —
    indices below 32 are the entry register values, see `sr_id`). -/
structure sym_state where
  s_pc : Int
  s_regs : List expr
  s_log : List sentry
  s_next : Nat
  deriving Repr

/-- Write `e` to `rd` (x0 discarded) and set the pc. -/
def sset (ss : sym_state) (rd : reg) (e : expr) (npc : Int) : sym_state :=
  ⟨npc, if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) e,
   ss.s_log, ss.s_next⟩

/-- Move the pc, leaving the register file and the log alone. -/
def sjump (ss : sym_state) (npc : Int) : sym_state :=
  ⟨npc, ss.s_regs, ss.s_log, ss.s_next⟩

/-! The projections of `sset`/`sjump`, as `rfl` facts.  The soundness proofs
    below rewrite with these instead of unfolding the structure literals
    under a `mkst`, which keeps every state equality a syntactic one. -/

theorem sset_pc (ss : sym_state) (rd : reg) (e : expr) (npc : Int) :
    (sset ss rd e npc).s_pc = npc := rfl

theorem sset_regs (ss : sym_state) (rd : reg) (e : expr) (npc : Int) :
    (sset ss rd e npc).s_regs
      = if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) e := rfl

theorem sset_log (ss : sym_state) (rd : reg) (e : expr) (npc : Int) :
    (sset ss rd e npc).s_log = ss.s_log := rfl

theorem sset_next (ss : sym_state) (rd : reg) (e : expr) (npc : Int) :
    (sset ss rd e npc).s_next = ss.s_next := rfl

theorem sjump_pc (ss : sym_state) (npc : Int) : (sjump ss npc).s_pc = npc := rfl

theorem sjump_regs (ss : sym_state) (npc : Int) :
    (sjump ss npc).s_regs = ss.s_regs := rfl

theorem sjump_log (ss : sym_state) (npc : Int) :
    (sjump ss npc).s_log = ss.s_log := rfl

theorem sjump_next (ss : sym_state) (npc : Int) :
    (sjump ss npc).s_next = ss.s_next := rfl

/-! ### Denotation into the concrete machine state -/

/-- The register file agrees with the symbolic one under `E`. -/
def regs_ok (E : env) (sr : List expr) (regs : BvMap word) : Prop :=
  ∀ r : reg, getr regs r = edenot E (sr_get sr r)

/-- The log denotes a fold of `wbytes` over the base memory: the oldest
    entry is applied first, so the head of the list is the outermost —
    exactly the layering the tactic route builds by hand. -/
def mem_denot (E : env) (base : word → Option byte) : List sentry → word → Option byte
  | [] => base
  | ⟨a, w, v⟩ :: rest =>
    wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v))

/-- Everything the log does to memory only ADDS defined bytes, which is
    what lets a `store_ok` obligation be stated against the ORIGINAL
    memory and lifted through the whole chain (see `SCStoreOk`). -/
theorem mem_denot_grows (E : env) (base : word → Option byte) (log : List sentry) :
    mem_grows base (mem_denot E base log) := by
  induction log with
  | nil => exact mem_grows_refl base
  | cons hd rest ih =>
    obtain ⟨a, w, v⟩ := hd
    exact mem_grows_trans ih
      (wbytes_grows (word_to_le_bytes w (edenot E v)) (mem_denot E base rest) (adenot E a))

/-- Every logged store address is flat (no wraparound).  Established one
    entry at a time from the `SCFlat` the store emits; consumed by every
    later load, which is why a same-base overlap test costs no side
    condition at all. -/
def log_flat (E : env) : List sentry → Prop
  | [] => True
  | ⟨a, w, _⟩ :: rest =>
    (0 ≤ (bdenot E a.a_base).toNat + a.a_off)
    ∧ ((bdenot E a.a_base).toNat + a.a_off < ((2 ^ 64 : Nat) : Int))
    ∧ ((bdenot E a.a_base).toNat + a.a_off + (w : Int) ≤ ((2 ^ 64 : Nat) : Int))
    ∧ log_flat E rest

/-- `ms` is described by `ss` under valuation `E`: same registers, same
    pc, and a memory that is the base memory with the log's writes
    layered on top. -/
def st_ok (E : env) (base rom : word → Option byte) (ss : sym_state)
    (ms : machine_state) : Prop :=
  ∃ regs, ms = mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom
    ∧ regs_ok E ss.s_regs regs
    ∧ log_flat E ss.s_log

/-! The one-`cons` shapes of `mem_denot` and `log_flat`, as `rfl` facts, so
    the store case of `sym_step_sound` never has to beta-reduce a match under
    an equality. -/

theorem mem_denot_cons (E : env) (base : word → Option byte) (a : saddr) (w : Nat)
    (v : expr) (rest : List sentry) :
    mem_denot E base (SE a w v :: rest)
      = wbytes (mem_denot E base rest) (adenot E a) (word_to_le_bytes w (edenot E v)) :=
  rfl

theorem log_flat_cons (E : env) (a : saddr) (w : Nat) (v : expr) (rest : List sentry) :
    log_flat E (SE a w v :: rest)
      = ((0 ≤ (bdenot E a.a_base).toNat + a.a_off
          ∧ ((bdenot E a.a_base).toNat + a.a_off < ((2 ^ 64 : Nat) : Int))
          ∧ ((bdenot E a.a_base).toNat + a.a_off + (w : Int) ≤ ((2 ^ 64 : Nat) : Int))
          ∧ log_flat E rest)) :=
  rfl

theorem regs_ok_upd (E : env) (sr : List expr) (regs : BvMap word) (rd : reg)
    (v : word) (e : expr)
    (Hr : regs_ok E sr regs) (Hv : edenot E e = v) :
    regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
      (if bv_eqb rd 0 then regs else regupd regs rd v) := by
  by_cases hrd : bv_eqb rd 0 = true
  · rw [ite_eq_left hrd, ite_eq_left hrd]; exact Hr
  · rw [ite_eq_right hrd, ite_eq_right hrd]
    have Hne : rd ≠ 0 := by
      intro h; subst h; exact hrd (bv_eqb_refl 0)
    intro r
    by_cases hr0 : bv_eqb r 0 = true
    · have h0 : r = 0 := beq_iff_eq.mp hr0
      subst h0
      show getr (regupd regs rd v) 0 = edenot E (.ELit 0)
      rw [show getr (regupd regs rd v) 0 = 0 from by simp [getr, bv_eqb_refl]]
      show (0 : word) = BitVec.ofInt 64 0
      decide
    · have Hrr : getr regs r = edenot E (sr.getD (ridx r) (.ELit 0)) := by
        have h := Hr r
        unfold sr_get at h
        rw [ite_eq_right hr0] at h
        exact h
      unfold sr_get
      rw [ite_eq_right hr0, nth_sr_upd]
      by_cases hi : ridx r = ridx rd
      · rw [ite_eq_left hi]
        have hrr : r = rd := ridx_inj hi
        subst hrr
        rw [getr_same _ _ _ Hne]
        exact Hv.symm
      · rw [ite_eq_right hi]
        have hrr : r ≠ rd := by intro h; subst h; exact hi rfl
        rw [getr_other _ _ _ _ hrr]
        exact Hrr

/-- Pin one register to a symbolic expression, given that the concrete file
    already agrees.  This is how a block's ENTRY state is built: start from
    `sr_id` (nothing known) and pin the registers the caller has facts for. -/
theorem regs_ok_pin (E : env) (sr : List expr) (regs : BvMap word) (r : reg) (e : expr)
    (Hr : regs_ok E sr regs) (Hv : getr regs r = edenot E e) :
    regs_ok E (sr_upd sr (ridx r) e) regs := by
  intro r'
  by_cases hr0 : bv_eqb r' 0 = true
  · have h0 : r' = 0 := beq_iff_eq.mp hr0
    subst h0
    show getr regs 0 = edenot E (sr_get (sr_upd sr (ridx r) e) 0)
    rw [show getr regs 0 = 0 from by simp [getr, bv_eqb_refl]]
    unfold sr_get
    rw [ite_eq_left (bv_eqb_refl (0 : reg))]
    show (0 : word) = BitVec.ofInt 64 0
    decide
  · have Hrr : getr regs r' = edenot E (sr.getD (ridx r') (.ELit 0)) := by
      have h := Hr r'
      unfold sr_get at h
      rw [ite_eq_right hr0] at h
      exact h
    unfold sr_get
    rw [ite_eq_right hr0, nth_sr_upd]
    by_cases hi : ridx r' = ridx r
    · rw [ite_eq_left hi]
      have hrr : r' = r := ridx_inj hi
      subst hrr
      exact Hv
    · rw [ite_eq_right hi]
      exact Hrr

/-- The "nothing known" symbolic register file: every register is its own
    variable.  Paired with `E0`, `regs_ok_id` gives an `st_ok` for ANY
    concrete state, with no hypotheses at all.
-/
def sr_id : List expr := (List.range 32).map (fun n => .EVar n)

/-- The explicit 32-entry spelling of `sr_id`, as  writes it. -/
theorem sr_id_eq : sr_id =
    [.EVar 0, .EVar 1, .EVar 2, .EVar 3, .EVar 4, .EVar 5, .EVar 6, .EVar 7,
     .EVar 8, .EVar 9, .EVar 10, .EVar 11, .EVar 12, .EVar 13, .EVar 14, .EVar 15,
     .EVar 16, .EVar 17, .EVar 18, .EVar 19, .EVar 20, .EVar 21, .EVar 22, .EVar 23,
     .EVar 24, .EVar 25, .EVar 26, .EVar 27, .EVar 28, .EVar 29, .EVar 30, .EVar 31] := by
  decide

theorem sr_id_getD (n : Nat) (hn : n < 32) : sr_id.getD n (.ELit 0) = .EVar n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [sr_id] using hn)]
  simp only [sr_id, List.getElem_map, List.getElem_range]
  rfl

def E0 (regs : BvMap word) : env :=
  fun n => getr regs (BitVec.ofInt 5 (n : Int))

theorem ridx_range (r : reg) : ridx r < 32 := by
  have := u5_range r
  simp only [ridx]; omega

theorem ridx_roundtrip (r : reg) : BitVec.ofInt 5 (ridx r : Int) = r := by
  rw [BitVec.ofInt_natCast]
  show BitVec.ofNat 5 r.toNat = r
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem regs_ok_id (regs : BvMap word) : regs_ok (E0 regs) sr_id regs := by
  intro r
  by_cases hr0 : bv_eqb r 0 = true
  · have h0 : r = 0 := beq_iff_eq.mp hr0
    subst h0
    show getr regs 0 = edenot (E0 regs) (sr_get sr_id 0)
    rw [show getr regs 0 = 0 from by simp [getr, bv_eqb_refl]]
    unfold sr_get
    rw [ite_eq_left (bv_eqb_refl (0 : reg))]
    show (0 : word) = BitVec.ofInt 64 0
    decide
  · have hget : sr_id.getD (ridx r) (.ELit 0) = .EVar (ridx r) :=
      sr_id_getD (ridx r) (ridx_range r)
    have hE : E0 regs (ridx r) = getr regs r := by
      unfold E0
      rw [ridx_roundtrip]
    unfold sr_get
    rw [ite_eq_right hr0, hget]
    exact hE.symm

/-- `E0` extended with the values of the bytes the block reads OUT OF the
    base memory, in the order the executor meets them: index `32 + k` is
    the `k`-th such read.  This is the only place the caller has to say
    anything about the contents of memory it did not itself write —
    `argc` at `sp`, an image word, a syscall's read buffer. -/
def Eplus (regs : BvMap word) (vals : List word) : env :=
  fun n => if n < 32 then getr regs (BitVec.ofInt 5 (n : Int))
           else vals.getD (n - 32) (BitVec.ofInt 64 0)

theorem regs_ok_Eplus (regs : BvMap word) (vals : List word) :
    regs_ok (Eplus regs vals) sr_id regs := by
  intro r
  by_cases hr0 : bv_eqb r 0 = true
  · have h0 : r = 0 := beq_iff_eq.mp hr0
    subst h0
    show getr regs 0 = edenot (Eplus regs vals) (sr_get sr_id 0)
    rw [show getr regs 0 = 0 from by simp [getr, bv_eqb_refl]]
    unfold sr_get
    rw [ite_eq_left (bv_eqb_refl (0 : reg))]
    show (0 : word) = BitVec.ofInt 64 0
    decide
  · have hget : sr_id.getD (ridx r) (.ELit 0) = .EVar (ridx r) :=
      sr_id_getD (ridx r) (ridx_range r)
    have hE : Eplus regs vals (ridx r) = getr regs r := by
      unfold Eplus
      rw [ite_eq_left (ridx_range r), ridx_roundtrip]
    unfold sr_get
    rw [ite_eq_right hr0, hget]
    exact hE.symm

/-! ## 3. The symbolic stepper -/

/-- Deep side conditions.  The executor NEVER guesses and never fails on
    a semantic question: whenever it needs a fact it cannot decide by
    closed arithmetic, it records the fact and carries on.  The caller
    discharges a *batch* of them at the end.

    - `SCBr` — a branch decision (the caller's branch script says which
      way; the path condition is recorded).
    - `SCFlat` — "this address is [base + offset] with no wraparound,
      and the [n] bytes after it stay inside the address space".  One
      `omega` from any `Footprint.covers` fact.  Emitted at every memory
      access; the ones a STORE emits enter the state invariant
      (`log_flat`), which is what lets a later load decide same-base
      overlap by `Int` arithmetic alone.
    - `SCDisjoint` — "these two byte ranges do not overlap" (and neither
      wraps).  Emitted for every log entry a load has to look PAST.  One
      `omega` from two `Footprint.covers` facts and a `rg_disj`.
    - `SCStoreOk` — "this range is writable".  Stated against the
      ORIGINAL memory: `mem_denot_grows` + `StoreOk.store_ok_mono` lift
      it through the whole store chain, so `Common/StoreOk`'s
      `solve_store_ok` closes it exactly as it does elsewhere, without any
      peeling.
    - `SCReadBase` — "the load fell through the entire log; here is what
      the base memory holds there".  This is the hook for the per-image
      `rdn` facts (`ArgvEnv.rdn_wmem_stack`, `read_argc`, an image's
      `srom_*`).  The loaded word is normally the fresh variable
      `EVar i`, but the caller's READ SCRIPT can NAME it instead (see
      `sym_step`'s `rds` argument): naming a reloaded return address
      `ELit 0x11020` is what lets the `ret` two instructions later
      resolve to a concrete pc, so a musl wrapper's whole epilogue stays
      inside one block. -/
inductive sidecond : Type
  | SCBr (taken : Bool) (c : BranchCond) (a b : expr)
  | SCFlat (a : saddr) (n : Nat)
  | SCDisjoint (a1 : saddr) (n1 : Nat) (a2 : saddr) (n2 : Nat)
  | SCStoreOk (a : saddr) (n : Nat)
  | SCReadBase (a : saddr) (n : Nat) (e : expr)
  deriving Repr

/-- "[a] is [base + offset] literally, and [n] bytes fit above it." -/
def sc_flat (E : env) (a : saddr) (n : Nat) : Prop :=
  0 ≤ (bdenot E a.a_base).toNat + a.a_off
  ∧ ((bdenot E a.a_base).toNat + a.a_off < ((2 ^ 64 : Nat) : Int))
  ∧ ((bdenot E a.a_base).toNat + a.a_off + (n : Int) ≤ ((2 ^ 64 : Nat) : Int))

/-- A flat access with no wraparound: the concrete address is exactly the
    literal `base + offset`. -/
theorem flat_u (E : env) (a : saddr) (n : Nat) (H : sc_flat E a n) :
    ((adenot E a).toNat : Int) = (bdenot E a.a_base).toNat + a.a_off := by
  obtain ⟨H1, H2, H3⟩ := H
  unfold adenot v_addi
  rw [toNat_ofInt64, Int.emod_eq_of_lt H1 H2]

/-- The denotation of one side condition. -/
def sc_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (s : sidecond) : Prop :=
  match s with
  | .SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | .SCFlat a n => sc_flat E a n
  | .SCDisjoint a1 n1 a2 n2 =>
    ((adenot E a1).toNat : Int) + (n1 : Int) ≤ ((2 ^ 64 : Nat) : Int)
    ∧ ((adenot E a2).toNat : Int) + (n2 : Int) ≤ ((2 ^ 64 : Nat) : Int)
    ∧ (((adenot E a1).toNat : Int) + (n1 : Int) ≤ ((adenot E a2).toNat : Int)
       ∨ ((adenot E a2).toNat : Int) + (n2 : Int) ≤ ((adenot E a1).toNat : Int))
  | .SCStoreOk a n => store_ok segs base (adenot E a) n = true
  | .SCReadBase a n e =>
    ∃ bs, rdn segs base (adenot E a) n = some bs
          ∧ bytes_le_to_Z bs = ((edenot E e).toNat : Int)

/-- A whole batch of side conditions. -/
def scs_denot (segs : List Segment) (base : word → Option byte) (E : env)
    (l : List sidecond) : Prop :=
  ∀ s ∈ l, sc_denot segs base E s

/-! ### The footprint interface

    These two lemmas are the whole contract between the executor and
    `Common/Footprint`: state a binary's memory layout ONCE as a handful of
    `region`s with pairwise `rg_disj` facts, and every `SCFlat` /
    `SCDisjoint` the executor emits is discharged by placing its address in
    one of them.  A Hoare-style frame rule can consume the same
    `covers`/`rg_disj` facts for its separating conjunction; neither side
    needs to know about the other.

    The interface is deliberately stated on the CONCRETE address, so a
    moving bound (a bump allocator raising `cur`) is absorbed by
    `Footprint.covers_mono` instead of re-proving anything here. -/

theorem sc_flat_of_region (E : env) (a : saddr) (n : Nat) (r : region)
    (Hw : rg_wf r) (Hn : 1 ≤ n)
    (Hl : r.rg_lo ≤ (bdenot E a.a_base).toNat + a.a_off)
    (Hh : (bdenot E a.a_base).toNat + a.a_off + (n : Int) ≤ r.rg_hi) :
    sc_flat E a n := by
  obtain ⟨H0, H1, H2⟩ := Hw
  unfold sc_flat
  refine ⟨by omega, by omega, by omega⟩

theorem sc_disjoint_of_regions (segs : List Segment) (base : word → Option byte)
    (E : env) (a1 : saddr) (n1 : Nat) (a2 : saddr) (n2 : Nat)
    (r1 r2 : region) (Hw1 : rg_wf r1) (Hw2 : rg_wf r2) (Hd : rg_disj r1 r2)
    (Hc1 : covers r1 (adenot E a1) n1) (Hc2 : covers r2 (adenot E a2) n2) :
    sc_denot segs base E (.SCDisjoint a1 n1 a2 n2) := by
  refine ⟨covers_nowrap r1 _ _ Hw1 Hc1, covers_nowrap r2 _ _ Hw2 Hc2,
    covers_disj r1 r2 _ _ _ _ Hd Hc1 Hc2⟩

/-- Same region, disjoint offsets: the case the executor decides by `Int`
    arithmetic.  Kept as a lemma so a caller that wants to discharge an
    `SCDisjoint` between two same-region accesses has the same shape. -/
theorem sc_disjoint_same_region (segs : List Segment) (base : word → Option byte)
    (E : env) (a1 : saddr) (n1 : Nat) (a2 : saddr) (n2 : Nat) (r : region)
    (Hw : rg_wf r) (Hc1 : covers r (adenot E a1) n1) (Hc2 : covers r (adenot E a2) n2)
    (Hd : ((adenot E a1).toNat : Int) + (n1 : Int) ≤ ((adenot E a2).toNat : Int)
       ∨ ((adenot E a2).toNat : Int) + (n2 : Int) ≤ ((adenot E a1).toNat : Int)) :
    sc_denot segs base E (.SCDisjoint a1 n1 a2 n2) := by
  exact ⟨covers_nowrap r _ _ Hw Hc1, covers_nowrap r _ _ Hw Hc2, Hd⟩

/-! ### Load resolution against the log -/

/-- Walk the log (most recent first) looking for the [n] bytes at
    `SA b k`.

    - SAME base: the offsets decide.  Exact same address and width 8
      (the only width whose stored bytes read back as the stored word
      with no masking) is a HIT.  Provably-disjoint is a skip, decided
      by `Int` arithmetic with NO side condition — this is the case that
      makes a spill/reload frame free.  Anything else (partial overlap,
      a narrower read of a wider slot) STOPS the executor.
    - DIFFERENT base: an `SCDisjoint` obligation and carry on.  Two
      argv-derived pointers, or a heap pointer versus `sp`, land here.

    Result: `none` = stuck; `some (some e, scs)` = hit, value `e`;
    `some (none, scs)` = fell through to the base memory. -/
def sm_lookup (log : List sentry) (b : sbase) (k : Int) (n : Nat) :
    Option (Option expr × List sidecond) :=
  match log with
  | [] => some (none, [])
  | ⟨⟨b', k'⟩, w, v⟩ :: rest =>
    if sbase_eqb b b' then
      (if (k == k' && n == 8 && w == 8) then some (some v, [])
       else if (decide (k + (n : Int) ≤ k') || decide (k' + (w : Int) ≤ k)) then
         sm_lookup rest b k n
       else none)
    else
      match sm_lookup rest b k n with
      | some (r, scs) => some (r, .SCDisjoint (SA b k) n (SA b' k') w :: scs)
      | none => none

/-- The number of bytes a memory access touches. -/
def msize_bytes : MSize → Nat
  | .SZ1 => 1 | .SZ2 => 2 | .SZ4 => 4 | .SZ8 => 8

/-- Sign-extend a 32-bit value using the ALU primitives the executor
    already denotes: `sext 64 (alu32 ADD (low32 x) 0)` IS `v_lw x`. -/
def mkSext32 (e : expr) : expr := .EAluw .ADD e (.ELit 0)

/-- The value a load that fell through the whole log reads: the next entry of
    the caller's READ SCRIPT if there is one, otherwise the fresh variable
    `EVar n` (`n = s_next`). -/
def read_val (rds : List expr) (n : Nat) : expr :=
  match rds with
  | [] => .EVar n
  | e :: _ => e

/-- The read script's tail after consuming one read. -/
def read_tail (rds : List expr) : List expr :=
  match rds with
  | [] => []
  | _ :: t => t

/-- `sset` with an explicit next-fresh-variable counter: the load-miss case
    bumps `s_next`, so the next base-memory read gets a new `EVar`. -/
def ssetn (ss : sym_state) (rd : reg) (e : expr) (npc : Int) (nx : Nat) : sym_state :=
  ⟨npc, if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) e,
   ss.s_log, nx⟩

theorem ssetn_pc (ss : sym_state) (rd : reg) (e : expr) (npc : Int) (nx : Nat) :
    (ssetn ss rd e npc nx).s_pc = npc := rfl

theorem ssetn_regs (ss : sym_state) (rd : reg) (e : expr) (npc : Int) (nx : Nat) :
    (ssetn ss rd e npc nx).s_regs
      = if bv_eqb rd 0 then ss.s_regs else sr_upd ss.s_regs (ridx rd) e := rfl

theorem ssetn_log (ss : sym_state) (rd : reg) (e : expr) (npc : Int) (nx : Nat) :
    (ssetn ss rd e npc nx).s_log = ss.s_log := rfl

theorem ssetn_next (ss : sym_state) (rd : reg) (e : expr) (npc : Int) (nx : Nat) :
    (ssetn ss rd e npc nx).s_next = nx := rfl

/-! ### One instruction

    `none` = "not modelled, stop the block here";
    otherwise the new state, the side conditions it assumed, and the
    unconsumed tail of the READ SCRIPT.

    `rds` is to loads what `dirs` is to branches: an optional caller
    supplied name for each value the block reads out of the BASE memory.
    An empty script gives a fresh `EVar`; a supplied `expr` is used
    instead, and the `SCReadBase` obligation is stated against it, so the
    caller pays exactly the same `rdn` fact and gets a value the executor
    can go on computing with. -/
def sym_step (i : Instr) (ss : sym_state) (rds : List expr) :
    Option (sym_state × List sidecond × List expr) :=
  let g r := sr_get ss.s_regs r
  let p := ss.s_pc
  match i with
  | .opImm op rd rs imm =>
    some (sset ss rd (mkAlu op (g rs) (.ELit imm.toInt)) (p + 4), [], rds)
  | .shiftImm op rd rs sh =>
    some (sset ss rd (mkAlu op (g rs) (.ELit (sh.toNat : Int))) (p + 4), [], rds)
  | .op op rd rs1 rs2 => some (sset ss rd (mkAlu op (g rs1) (g rs2)) (p + 4), [], rds)
  | .opImm32 rd rs imm =>
    some (sset ss rd (.EAluw .ADD (g rs) (.ELit imm.toInt)) (p + 4), [], rds)
  | .shiftImm32 op rd rs sh =>
    some (sset ss rd (.EAluw op (g rs) (.ELit (sh.toNat : Int))) (p + 4), [], rds)
  | .op32 op rd rs1 rs2 => some (sset ss rd (.EAluw op (g rs1) (g rs2)) (p + 4), [], rds)
  | .mul op rd rs1 rs2 => some (sset ss rd (.EMd op (g rs1) (g rs2)) (p + 4), [], rds)
  | .mul32 op rd rs1 rs2 => some (sset ss rd (.EMdw op (g rs1) (g rs2)) (p + 4), [], rds)
  | .lui rd imm => some (sset ss rd (.ELit (zshiftl imm.toInt 12)) (p + 4), [], rds)
  | .auipc rd imm => some (sset ss rd (.ELit (zshiftl imm.toInt 12 + p)) (p + 4), [], rds)
  | .jal rd imm => some (sset ss rd (.ELit (p + 4)) (p + imm.toInt), [], rds)
  | .jalr rd rs1 imm =>
    -- the jump target must be a literal for the pc to stay concrete
    match g rs1 with
    | .ELit z => some (sset ss rd (.ELit (p + 4)) (zland_m2 (bv_wrap 64 z + imm.toInt)), [], rds)
    | _ => none
  -- ---- loads: ld, lwu, lw, lhu, lbu (lh/lb are not modelled) ----
  | .load sz sgn rd rs imm =>
    let n := msize_bytes sz
    match to_saddr (g rs) imm.toInt with
    | none => none
    | some a =>
      match sm_lookup ss.s_log a.a_base a.a_off n with
      | none => none
      | some (some v, scs) =>
        -- a hit is only ever an 8-byte slot read back whole
        match sz, sgn with
        | .SZ8, true => some (sset ss rd v (p + 4), .SCFlat a 8 :: scs, rds)
        | _, _ => none
      | some (none, scs) =>
        -- `rv`/`rds'`/the next state are  inline `match
        -- rds`/structure literal, named (`read_val`, `read_tail`, `ssetn`) so
        -- `sym_step_sound` can speak about them; the terms are the same.
        let rv : expr := read_val rds ss.s_next
        let rds' : List expr := read_tail rds
        let scs' : List sidecond := .SCFlat a n :: .SCReadBase a n rv :: scs
        let mk (e : expr) : Option (sym_state × List sidecond × List expr) :=
          some (ssetn ss rd e (p + 4) (ss.s_next + 1), scs', rds')
        match sz, sgn with
        | .SZ8, true => mk rv
        | .SZ4, false => mk rv
        | .SZ2, false => mk rv
        | .SZ1, false => mk rv
        | .SZ4, true => mk (mkSext32 rv)
        | _, _ => none
    -- ---- stores: sb, sw and sd (sh has no step lemma yet) ----
  | .store sz rs1 rs2 imm =>
    match sz with
    | .SZ1 | .SZ4 | .SZ8 =>
      let n := msize_bytes sz
      match to_saddr (g rs1) imm.toInt with
      | none => none
      | some a =>
        some (⟨p + 4, ss.s_regs, SE a n (g rs2) :: ss.s_log, ss.s_next⟩,
              [.SCFlat a n, .SCStoreOk a n], rds)
    | _ => none
  | _ => none

/-! ### Extra machine-level step lemmas the executor needs -/

/-- The signed word load's value bridge is `PropExec.b_lw_val`; this is the
    ALU-level identity that turns `mkSext32` into it. -/
theorem alu32_add_0 (x : BitVec 32) : alu32 .ADD x (BitVec.ofInt 32 0) = x := by
  show x + BitVec.ofInt 32 0 = x
  simp

/-- A one-byte read's value is the byte's unsigned reading. -/
theorem bytes_le_to_Z_1 (b : byte) : bytes_le_to_Z [b] = (b.toNat : Int) := by
  simp [bytes_le_to_Z, bytes_le_to_Nat]

theorem mkSext32_denot (E : env) (e : expr) : edenot E (mkSext32 e) = v_lw (edenot E e) := by
  simp only [mkSext32, edenot]
  rw [low32_lit, alu32_add_0]
  exact b_lw_val (edenot E e)

/-! ### Log lookup soundness -/

section WithSegs

variable (segs : List Segment)

theorem scs_denot_cons (base : word → Option byte) (E : env) (s : sidecond)
    (l : List sidecond) (H : scs_denot segs base E (s :: l)) :
    sc_denot segs base E s ∧ scs_denot segs base E l := by
  refine ⟨H s (by simp), fun x hx => H x (by simp [hx])⟩

/-- The lookup-soundness statement in CONJUNCTION form . -/
theorem sm_lookup_sound_gen (base : word → Option byte) (E : env) (log : List sentry)
    (b : sbase) (k : Int) (n : Nat) (r : Option expr) (scs : List sidecond)
    (Hl : sm_lookup log b k n = some (r, scs))
    (Hsc : scs_denot segs base E scs)
    (Hlf : log_flat E log)
    (Hfl : sc_flat E (SA b k) n) :
    (r = none →
        rdn segs (mem_denot E base log) (adenot E (SA b k)) n
          = rdn segs base (adenot E (SA b k)) n)
    ∧ (∀ v, r = some v →
        n = 8 ∧ rdn segs (mem_denot E base log) (adenot E (SA b k)) n
          = some (word_to_le_bytes 8 (edenot E v))) := by
  induction log generalizing b k n r scs with
  | nil =>
    simp only [sm_lookup, Option.some.injEq, Prod.mk.injEq] at Hl
    obtain ⟨hr, hscs⟩ := Hl
    subst hr; subst hscs
    exact ⟨fun _ => rfl, fun v hv => by simp at hv⟩
  | cons hd rest ih =>
    obtain ⟨⟨b', k'⟩, w, v'⟩ := hd
    have Hua : ((adenot E (SA b k)).toNat : Int) = (bdenot E b).toNat + k :=
      flat_u E (SA b k) n Hfl
    have HflC := Hfl
    obtain ⟨Hk1, Hk2, Hk3⟩ := HflC
    have HlfC := Hlf
    obtain ⟨Hf1, Hf2, Hf3, Hlf'⟩ := HlfC
    by_cases hb : sbase_eqb b b' = true
    · have hbb : b = b' := sbase_eqb_eq hb
      subst hbb
      have Hua' : ((adenot E (SA b k')).toNat : Int) = (bdenot E b).toNat + k' :=
        flat_u E (SA b k') w ⟨Hf1, Hf2, Hf3⟩
      by_cases hhit : ((k == k' && n == 8 && w == 8) = true)
      · -- HIT: the read is exactly a stored 8-byte slot
        have Hl' : some (some v', ([] : List sidecond)) = some (r, scs) := by
          simpa only [sm_lookup, ite_eq_left hb, ite_eq_left hhit] using Hl
        simp only [Option.some.injEq, Prod.mk.injEq] at Hl'
        obtain ⟨hr, hscs⟩ := Hl'
        subst hr; subst hscs
        simp only [Bool.and_eq_true, beq_iff_eq] at hhit
        obtain ⟨⟨hk, hn8⟩, hw8⟩ := hhit
        subst k'; subst n; subst w
        refine ⟨fun h => by simp at h, fun v hv => ?_⟩
        simp only [Option.some.injEq] at hv
        subst hv
        refine ⟨rfl, ?_⟩
        rw [show mem_denot E base (⟨⟨b, k⟩, 8, v'⟩ :: rest)
              = wbytes (mem_denot E base rest) (adenot E (SA b k))
                  (word_to_le_bytes 8 (edenot E v')) from rfl]
        exact rdn_wbytes_hit8 segs _ _ _ (by rw [Hua]; omega)
      · -- not a hit: either a free skip or stuck
        by_cases hdis : ((decide (k + (n : Int) ≤ k') || decide (k' + (w : Int) ≤ k)) = true)
        · -- SKIP: provably disjoint, decided by Int arithmetic alone
          have Hl' : sm_lookup rest b k n = some (r, scs) := by
            simpa only [sm_lookup, ite_eq_left hb, ite_eq_right hhit, ite_eq_left hdis] using Hl
          have Hres := ih b k n r scs Hl' Hsc Hlf' Hfl
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hdis
          have Hd : ((adenot E (SA b k)).toNat : Int) + (n : Int)
                      ≤ ((adenot E (SA b k')).toNat : Int)
                    ∨ ((adenot E (SA b k')).toNat : Int) + (w : Int)
                      ≤ ((adenot E (SA b k)).toNat : Int) := by
            rcases hdis with h | h
            · left; rw [Hua, Hua']; omega
            · right; rw [Hua, Hua']; omega
          have Hskip :
              rdn segs (wbytes (mem_denot E base rest) (adenot E (SA b k'))
                    (word_to_le_bytes w (edenot E v'))) (adenot E (SA b k)) n
              = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n := by
            rcases Hd with Hd | Hd
            · refine rdn_wbytes_below segs _ _ _ _ _ Hd ?_
              rw [length_N_to_le_bytes, Hua']
              exact Hf3
            · refine rdn_wbytes_disjoint segs _ _ _ _ _ ?_ ?_
              · rw [length_N_to_le_bytes]; exact Hd
              · rw [Hua]; omega
          rw [show mem_denot E base (⟨⟨b, k'⟩, w, v'⟩ :: rest)
                = wbytes (mem_denot E base rest) (adenot E (SA b k'))
                    (word_to_le_bytes w (edenot E v')) from rfl, Hskip]
          exact Hres
        · have Hnone : sm_lookup (⟨⟨b, k'⟩, w, v'⟩ :: rest) b k n = none := by
            simp only [sm_lookup, ite_eq_left hb, ite_eq_right hhit, ite_eq_right hdis]
          rw [Hnone] at Hl
          exact absurd Hl (by simp)
    · -- DIFFERENT base: an SCDisjoint obligation and carry on
      cases hrec : sm_lookup rest b k n with
      | none =>
        have Hl' : sm_lookup (⟨⟨b', k'⟩, w, v'⟩ :: rest) b k n = none := by
          simp only [sm_lookup, ite_eq_right hb, hrec]
        rw [Hl'] at Hl
        exact absurd Hl (by simp)
      | some p =>
        obtain ⟨r0, scs0⟩ := p
        have Hl' : sm_lookup (⟨⟨b', k'⟩, w, v'⟩ :: rest) b k n
            = some (r0, sidecond.SCDisjoint (SA b k) n (SA b' k') w :: scs0) := by
          simp only [sm_lookup, ite_eq_right hb, hrec]
        rw [Hl'] at Hl
        simp only [Option.some.injEq, Prod.mk.injEq] at Hl
        obtain ⟨hr, hscs⟩ := Hl
        subst hr; subst hscs
        obtain ⟨Hhd, Htl⟩ := scs_denot_cons segs base E _ _ Hsc
        obtain ⟨Hnw1, Hnw2, Hd⟩ := Hhd
        have Hres := ih b k n r0 scs0 hrec Htl Hlf' Hfl
        have Hskip :
            rdn segs (wbytes (mem_denot E base rest) (adenot E (SA b' k'))
                  (word_to_le_bytes w (edenot E v'))) (adenot E (SA b k)) n
            = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n := by
          rcases Hd with Hd | Hd
          · refine rdn_wbytes_below segs _ _ _ _ _ Hd ?_
            rw [length_N_to_le_bytes]; exact Hnw2
          · refine rdn_wbytes_disjoint segs _ _ _ _ _ ?_ Hnw1
            rw [length_N_to_le_bytes]; exact Hd
        rw [show mem_denot E base (⟨⟨b', k'⟩, w, v'⟩ :: rest)
              = wbytes (mem_denot E base rest) (adenot E (SA b' k'))
                  (word_to_le_bytes w (edenot E v')) from rfl, Hskip]
        exact Hres

/-- The heart of the memory model: a log lookup that the executor
    resolved really does describe the layered memory. -/
theorem sm_lookup_sound (base : word → Option byte) (E : env) (log : List sentry)
    (b : sbase) (k : Int) (n : Nat) (r : Option expr) (scs : List sidecond)
    (Hl : sm_lookup log b k n = some (r, scs))
    (Hsc : scs_denot segs base E scs)
    (Hlf : log_flat E log)
    (Hfl : sc_flat E (SA b k) n) :
    (match r with
     | none => rdn segs (mem_denot E base log) (adenot E (SA b k)) n
                 = rdn segs base (adenot E (SA b k)) n
     | some v => n = 8 ∧ rdn segs (mem_denot E base log) (adenot E (SA b k)) n
                 = some (word_to_le_bytes 8 (edenot E v))) := by
  have h := sm_lookup_sound_gen segs base E log b k n r scs Hl Hsc Hlf Hfl
  cases r with
  | none => exact h.1 rfl
  | some v => exact h.2 v rfl

/-! ### The one-step dispatch -/

/-- The DIRECTED one-step relation: what `sym_exec` does at one instruction,
    branch dispatch included.
 Its purpose is proof-shape only — `sym_exec` then has a single
    `match sym_move … with | some (ss', scs, rds', dirs') => … | none => …`,
    so every lemma about the executor splits on an `Option` (four components)
    instead of on the 35 `Instr` constructors.  `sym_step` itself and its
    signature are untouched.
    `none` covers both "the branch script ran out" and "`sym_step` declines
    the instruction"; either way the executor stops at that instruction. -/
def sym_move (i : Instr) (ss : sym_state) (rds : List expr) (dirs : List Bool) :
    Option (sym_state × List sidecond × List expr × List Bool) :=
  match i with
  | .branch c rs1 rs2 imm =>
    match dirs with
    | [] => none
    | t :: dirs' =>
      some (sjump ss (if t then ss.s_pc + imm.toInt else ss.s_pc + 4),
            [.SCBr t c (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2)], rds, dirs')
  | _ =>
    match sym_step i ss rds with
    | some (ss', scs, rds') => some (ss', scs, rds', dirs)
    | none => none

/-! ### The executor -/

/-- Run from `ss`'s pc for at most `fuel` instructions.  `dirs` is the
    caller's branch script: one boolean per `Branch` encountered, saying
    which way to go; the assumed path condition is recorded in the
    side-condition list.  Anything else that `sym_step` declines (an
    unrecognised address shape, a partially-overlapping reload, `ecall`,
    a compressed encoding, an unresolvable `jalr`) stops the run,
    returning the state AT that instruction.
-/
def sym_exec (fuel : Nat) (dirs : List Bool) (rds : List expr) (ss : sym_state)
    (acc : List sidecond) : sym_state × List sidecond :=
  match fuel with
  | 0 => (ss, acc)
  | f + 1 =>
    match fetch_word segs (BitVec.ofInt 64 ss.s_pc) with
    | none => (ss, acc)
    | some w =>
      if is_ecall w then (ss, acc) else
      match decodeAny w with
      | none => (ss, acc)
      | some (i, sz) =>
        if !(sz == 4) then (ss, acc) else
        match sym_move i ss rds dirs with
        | some (ss', scs, rds', dirs') => sym_exec f dirs' rds' ss' (scs ++ acc)
        | none => (ss, acc)

/-! ### Unfolding lemmas for the executor

    `sym_exec` is a nested match, so a proof that wants one step of it states
    the equation it needs as a lemma here; the proofs below then `rw` these in
    instead of unfolding a fixpoint under binders.  Each is `rfl` because the
    right-hand side IS the corresponding branch of the definition. -/

/-- The `fuel = 0` case. -/
theorem sym_exec_zero (dirs : List Bool) (rds : List expr) (ss : sym_state)
    (acc : List sidecond) : sym_exec segs 0 dirs rds ss acc = (ss, acc) := rfl

/-- The fetch failed: nothing to execute. -/
theorem sym_exec_nofetch (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = none) :
    sym_exec segs (f + 1) dirs rds ss acc = (ss, acc) := by
  simp only [sym_exec, H]

/-- The word is the `ecall` encoding: the executor hands the state back. -/
theorem sym_exec_ecall (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (w : BitVec 32)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = true) :
    sym_exec segs (f + 1) dirs rds ss acc = (ss, acc) := by
  simp only [sym_exec, H, He, ite_true]

/-- The word does not decode. -/
theorem sym_exec_nodecode (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (w : BitVec 32)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false) (Hd : decodeAny w = none) :
    sym_exec segs (f + 1) dirs rds ss acc = (ss, acc) := by
  simp only [sym_exec, H, He, Hd, Bool.false_eq_true, ite_false]

/-- The instruction is compressed (not a 4-byte encoding). -/
theorem sym_exec_nosz (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (w : BitVec 32) (i : Instr) (sz : Int)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false) (Hd : decodeAny w = some (i, sz)) (Hsz : (sz == 4) = false) :
    sym_exec segs (f + 1) dirs rds ss acc = (ss, acc) := by
  have hn : (!(sz == 4)) = true := by rw [Hsz]; rfl
  simp only [sym_exec, H, He, Hd, Bool.false_eq_true, ite_false, hn, ite_true]

/-- The instruction is executed: `sym_move` succeeded. -/
theorem sym_exec_step (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (w : BitVec 32) (i : Instr)
    (ss' : sym_state) (scs : List sidecond) (rds' : List expr) (dirs' : List Bool)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false) (Hd : decodeAny w = some (i, 4))
    (Hm : sym_move i ss rds dirs = some (ss', scs, rds', dirs')) :
    sym_exec segs (f + 1) dirs rds ss acc
      = sym_exec segs f dirs' rds' ss' (scs ++ acc) := by
  have h4 : (!((4 : Int) == 4)) = false := by decide
  simp only [sym_exec, H, He, Hd, Bool.false_eq_true, ite_false, h4, ite_true, Hm]

/-- The instruction is not executed: `sym_move` declined it. -/
theorem sym_exec_stuck (f : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (w : BitVec 32) (i : Instr)
    (H : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false) (Hd : decodeAny w = some (i, 4))
    (Hm : sym_move i ss rds dirs = none) :
    sym_exec segs (f + 1) dirs rds ss acc = (ss, acc) := by
  have h4 : (!((4 : Int) == 4)) = false := by decide
  simp only [sym_exec, H, He, Hd, Bool.false_eq_true, ite_false, h4, ite_true, Hm]

/-- **The accumulator only grows.**  Every side condition the executor
    assumes is appended to the front of the caller's accumulator, so one
    batch discharged for the RESULT covers the whole run — which is what lets
    `sym_exec_sound` state its hypothesis on the returned list. -/
theorem sym_exec_acc (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) :
    ∃ pre, (sym_exec segs fuel dirs rds ss acc).2 = pre ++ acc := by
  induction fuel generalizing dirs rds ss acc with
  | zero => exact ⟨[], rfl⟩
  | succ f ih =>
    cases Hf : fetch_word segs (BitVec.ofInt 64 ss.s_pc) with
    | none => exact ⟨[], by simp [sym_exec_nofetch segs f dirs rds ss acc Hf]⟩
    | some w =>
      by_cases He : is_ecall w = true
      · exact ⟨[], by simp only [sym_exec_ecall segs f dirs rds ss acc w Hf He, Prod.snd,
      List.nil_append]⟩
      · have He' : is_ecall w = false := by simpa using He
        cases Hd : decodeAny w with
        | none => exact ⟨[], by simp [sym_exec_nodecode segs f dirs rds ss acc w Hf He' Hd]⟩
        | some p =>
          obtain ⟨i, sz⟩ := p
          by_cases Hsz : (sz == 4) = true
          · have hsz : sz = 4 := by simpa using Hsz
            subst hsz
            cases Hm : sym_move i ss rds dirs with
            | none => exact ⟨[], by simp [sym_exec_stuck segs f dirs rds ss acc w i Hf He' Hd Hm]⟩
            | some q =>
              obtain ⟨ss2, scs2, rds2, dirs2⟩ := q
              obtain ⟨pre, hpre⟩ := ih dirs2 rds2 ss2 (scs2 ++ acc)
              refine ⟨pre ++ scs2, ?_⟩
              rw [sym_exec_step segs f dirs rds ss acc w i ss2 scs2 rds2 dirs2 Hf He' Hd Hm,
                hpre, List.append_assoc]
          · exact ⟨[], by
              simp [sym_exec_nosz segs f dirs rds ss acc w i sz Hf He' Hd
                (by simpa using Hsz)]⟩

/-! ### Batch manipulation -/

theorem scs_denot_app (base : word → Option byte) (E : env) (l1 l2 : List sidecond)
    (H : scs_denot segs base E (l1 ++ l2)) :
    scs_denot segs base E l1 ∧ scs_denot segs base E l2 := by
  refine ⟨fun x hx => H x (by simp [hx]), fun x hx => H x (by simp [hx])⟩




/-! ### One symbolic step -/

/-- **One symbolic step simulates one machine step.**  If `sym_step` succeeds
    at a decoded, non-`ecall` instruction and every side condition it emitted
    holds under the valuation `E`, then the concrete machine takes ONE step to
    a state the returned symbolic state describes.

    The 21 constructors `sym_step` declines need no case of their own: after
    `cases i` the hypothesis `Hs` is `none = some …` there, so a single `try`
    (`simp [sym_step] at Hs`, which closes a goal whose hypothesis became
    `False`) discharges all of them at once.  That is the reason the case list
    below is only the 14 modelled instructions rather than all 35. -/
theorem sym_step_sound (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (i : Instr) (ss' : sym_state)
    (scs : List sidecond) (w : BitVec 32) (rds rds' : List expr)
    (Hf : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (i, 4))
    (Hs : sym_step i ss rds = some (ss', scs, rds'))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok E base rom ss ms) :
    ∃ ms', RiscvSemantics.step segs ms = .MachineOk ms' ∧ st_ok E base rom ss' ms' := by
  obtain ⟨regs, rfl, Hregs, Hlf⟩ := Hst
  cases i <;> try (simp [sym_step] at Hs)
  case lui rd imm =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : v_lui (zshiftl imm.toInt 12) = edenot E (.ELit (zshiftl imm.toInt 12)) := rfl
    refine ⟨mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (zshiftl imm.toInt 12)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_lui segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd imm Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case auipc rd imm =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : v_auipc (BitVec.ofInt 64 ss.s_pc) (zshiftl imm.toInt 12)
        = edenot E (.ELit (zshiftl imm.toInt 12 + ss.s_pc)) := by
      simp only [v_auipc_lit, edenot]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_auipc (BitVec.ofInt 64 ss.s_pc) (zshiftl imm.toInt 12)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_auipc segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd imm Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case jal rd imm =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : v_addi (BitVec.ofInt 64 ss.s_pc) 4
        = edenot E (.ELit (ss.s_pc + 4)) := by
      simp only [v_addi_lit, edenot]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (v_addi (BitVec.ofInt 64 ss.s_pc) 4))
        (btgt (BitVec.ofInt 64 ss.s_pc) imm.toInt) (mem_denot E base ss.s_log) rom,
      step_jal_link segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd imm Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, btgt_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case jalr rd rs1 imm =>
    cases Hg : sr_get ss.s_regs rs1 with
    | ELit z =>
      simp only [sym_step, Hg, Option.some.injEq, Prod.mk.injEq] at Hs
      obtain ⟨rfl, rfl, rfl⟩ := Hs
      have hg : getr regs rs1 = BitVec.ofInt 64 z := by
        simp only [Hregs rs1, Hg, edenot]
      have hval : v_addi (BitVec.ofInt 64 ss.s_pc) 4
          = edenot E (.ELit (ss.s_pc + 4)) := by
        simp only [v_addi_lit, edenot]
      have hpc : v_jalr (getr regs rs1) imm.toInt
          = BitVec.ofInt 64 (zland_m2 (bv_wrap 64 z + imm.toInt)) := by
        rw [hg]
        exact jalr_tgt_lit z imm.toInt
      refine ⟨mkst (if bv_eqb rd 0 then regs
          else regupd regs rd (v_addi (BitVec.ofInt 64 ss.s_pc) 4))
          (v_jalr (getr regs rs1) imm.toInt) (mem_denot E base ss.s_log) rom,
        step_jalr segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs1 imm Hf He Hd, ?_⟩
      exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, hval, hpc],
        regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
    | EVar n =>
      revert Hs
      simp [sym_step, Hg]
    | EAlu op a b => simp [sym_step, Hg] at Hs
    | EAluw op a b => simp [sym_step, Hg] at Hs
    | EMd op a b => simp [sym_step, Hg] at Hs
    | EMdw op a b => simp [sym_step, Hg] at Hs
  case load sz sgn rd rs imm =>
    cases Ha : to_saddr (sr_get ss.s_regs rs) imm.toInt with
    | none => simp [sym_step, Ha] at Hs
    | some a =>
      have Hadr : adenot E a = v_addi (getr regs rs) imm.toInt := by
        rw [to_saddr_denot E (sr_get ss.s_regs rs) imm.toInt a Ha, ← Hregs rs]
      cases Hlk : sm_lookup ss.s_log a.a_base a.a_off (msize_bytes sz) with
      | none => simp [sym_step, Ha, Hlk] at Hs
      | some p =>
        obtain ⟨r0, scs0⟩ := p
        cases r0 with
        | some v =>
          -- a HIT is only modelled for a whole 8-byte slot: `ld`
          cases sz with
          | SZ1 => simp [sym_step, Ha, Hlk] at Hs
          | SZ2 => simp [sym_step, Ha, Hlk] at Hs
          | SZ4 => simp [sym_step, Ha, Hlk] at Hs
          | SZ8 =>
            cases sgn with
            | false => simp [sym_step, Ha, Hlk] at Hs
            | true =>
              simp only [sym_step, Ha, Hlk] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc0⟩ := scs_denot_cons segs base E _ _ Hsc
              have Hlk8 : sm_lookup ss.s_log a.a_base a.a_off 8 = some (some v, scs0) := Hlk
              obtain ⟨_, Hread0⟩ := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 8
                (some v) scs0 Hlk8 Hsc0 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 8
                  = some (word_to_le_bytes 8 (edenot E v)) := by
                rw [← Hadr]
                exact Hread0
              refine ⟨mkst (if bv_eqb rd 0 then regs
                  else regupd regs rd (edenot E v))
                  (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                step_ld segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm _ (edenot E v) Hf He Hd Hread
                  (bytes_le_to_Z_8 _), ?_⟩
              exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit],
                regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
        | none =>
          -- a MISS reads the base memory into the read script's value
          cases sz with
          | SZ1 =>
            cases sgn with
            | false =>
              -- lbu
              simp only [sym_step, Ha, Hlk, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
              obtain ⟨Hrb, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
              obtain ⟨bs, Hrdn, Hbs⟩ := Hrb
              have Hlk1 : sm_lookup ss.s_log a.a_base a.a_off 1 = some (none, scs0) := Hlk
              have hmiss := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 1
                none scs0 Hlk1 Hsc2 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 1 = some bs := by
                rw [← Hadr]
                exact hmiss.trans Hrdn
              have Hlen : bs.length = 1 :=
                rdn_length segs (mem_denot E base ss.s_log) 1 _ bs Hread
              obtain ⟨b, rfl⟩ : ∃ b, bs = [b] := by
                cases bs with
                | nil => simp at Hlen
                | cons b t =>
                  cases t with
                  | nil => exact ⟨b, rfl⟩
                  | cons b' t => simp at Hlen
              rw [bytes_le_to_Z_1] at Hbs
              have hval : BitVec.ofInt 64 (b.toNat : Int)
                  = edenot E (read_val rds ss.s_next) := by
                rw [Hbs]
                exact ofInt64_toNat _
              exact ⟨mkst (if bv_eqb rd 0 then regs
                    else regupd regs rd (BitVec.ofInt 64 (b.toNat : Int)))
                    (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                  step_lbu segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm b Hf He Hd Hread,
                ⟨_, by simp only [ssetn_pc, ssetn_log, ssetn_regs, v_addi_lit, hval],
                  regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩⟩
            | true => simp [sym_step, Ha, Hlk] at Hs
          | SZ2 =>
            cases sgn with
            | false =>
              -- lhu
              simp only [sym_step, Ha, Hlk, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
              obtain ⟨Hrb, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
              obtain ⟨bs, Hrdn, Hbs⟩ := Hrb
              have Hlk2 : sm_lookup ss.s_log a.a_base a.a_off 2 = some (none, scs0) := Hlk
              have hmiss := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 2
                none scs0 Hlk2 Hsc2 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 2 = some bs := by
                rw [← Hadr]
                exact hmiss.trans Hrdn
              exact ⟨mkst (if bv_eqb rd 0 then regs
                    else regupd regs rd (edenot E (read_val rds ss.s_next)))
                    (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                  step_lhu segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm bs (edenot E (read_val rds ss.s_next))
                    Hf He Hd Hread Hbs,
                ⟨_, by simp only [ssetn_pc, ssetn_log, ssetn_regs, v_addi_lit],
                  regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩⟩
            | true => simp [sym_step, Ha, Hlk] at Hs
          | SZ4 =>
            cases sgn with
            | false =>
              -- lwu
              simp only [sym_step, Ha, Hlk, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
              obtain ⟨Hrb, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
              obtain ⟨bs, Hrdn, Hbs⟩ := Hrb
              have Hlk4 : sm_lookup ss.s_log a.a_base a.a_off 4 = some (none, scs0) := Hlk
              have hmiss := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 4
                none scs0 Hlk4 Hsc2 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 4 = some bs := by
                rw [← Hadr]
                exact hmiss.trans Hrdn
              exact ⟨mkst (if bv_eqb rd 0 then regs
                    else regupd regs rd (edenot E (read_val rds ss.s_next)))
                    (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                  step_lwu segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm bs (edenot E (read_val rds ss.s_next))
                    Hf He Hd Hread Hbs,
                ⟨_, by simp only [ssetn_pc, ssetn_log, ssetn_regs, v_addi_lit],
                  regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩⟩
            | true =>
              -- lw
              simp only [sym_step, Ha, Hlk, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
              obtain ⟨Hrb, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
              obtain ⟨bs, Hrdn, Hbs⟩ := Hrb
              have Hlk4 : sm_lookup ss.s_log a.a_base a.a_off 4 = some (none, scs0) := Hlk
              have hmiss := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 4
                none scs0 Hlk4 Hsc2 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 4 = some bs := by
                rw [← Hadr]
                exact hmiss.trans Hrdn
              have hval : v_lw (edenot E (read_val rds ss.s_next))
                  = edenot E (mkSext32 (read_val rds ss.s_next)) := by
                rw [mkSext32_denot]
              exact ⟨mkst (if bv_eqb rd 0 then regs
                    else regupd regs rd (v_lw (edenot E (read_val rds ss.s_next))))
                    (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                  step_lw segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm bs (edenot E (read_val rds ss.s_next))
                    Hf He Hd Hread Hbs,
                ⟨_, by simp only [ssetn_pc, ssetn_log, ssetn_regs, v_addi_lit, hval],
                  regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩⟩
          | SZ8 =>
            cases sgn with
            | false => simp [sym_step, Ha, Hlk] at Hs
            | true =>
              -- ld
              simp only [sym_step, Ha, Hlk, Option.some.injEq, Prod.mk.injEq] at Hs
              obtain ⟨rfl, rfl, rfl⟩ := Hs
              obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
              obtain ⟨Hrb, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
              obtain ⟨bs, Hrdn, Hbs⟩ := Hrb
              have Hlk8 : sm_lookup ss.s_log a.a_base a.a_off 8 = some (none, scs0) := Hlk
              have hmiss := sm_lookup_sound segs base E ss.s_log a.a_base a.a_off 8
                none scs0 Hlk8 Hsc2 Hlf Hfit
              have Hread : rdn segs (mem_denot E base ss.s_log)
                  (v_addi (getr regs rs) imm.toInt) 8 = some bs := by
                rw [← Hadr]
                exact hmiss.trans Hrdn
              exact ⟨mkst (if bv_eqb rd 0 then regs
                    else regupd regs rd (edenot E (read_val rds ss.s_next)))
                    (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
                  step_ld segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm bs (edenot E (read_val rds ss.s_next))
                    Hf He Hd Hread Hbs,
                ⟨_, by simp only [ssetn_pc, ssetn_log, ssetn_regs, v_addi_lit],
                  regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩⟩
  case store sz rs1 rs2 imm =>
    cases sz with
    | SZ2 => simp [sym_step] at Hs
    | SZ1 =>
      cases Ha : to_saddr (sr_get ss.s_regs rs1) imm.toInt with
      | none => simp [sym_step, Ha] at Hs
      | some a =>
        have Hadr : adenot E a = v_addi (getr regs rs1) imm.toInt := by
          rw [to_saddr_denot E (sr_get ss.s_regs rs1) imm.toInt a Ha, ← Hregs rs1]
        simp only [sym_step, Ha, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl⟩ := Hs
        obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
        obtain ⟨Hok, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
        have Hok' : store_ok segs (mem_denot E base ss.s_log)
            (v_addi (getr regs rs1) imm.toInt) 1 = true := by
          rw [← Hadr]
          exact store_ok_mono segs 1 base (mem_denot E base ss.s_log) (adenot E a)
            (mem_denot_grows E base ss.s_log) Hok
        refine ⟨mkst regs (v_addi (BitVec.ofInt 64 ss.s_pc) 4)
            (wbytes (mem_denot E base ss.s_log) (v_addi (getr regs rs1) imm.toInt)
              (word_to_le_bytes 1 (getr regs rs2))) rom,
          step_sb segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rs1 rs2 imm Hf He Hd Hok', ?_⟩
        refine ⟨regs, ?_, Hregs, ?_⟩
        · simp only [v_addi_lit, mem_denot_cons, Hadr, ← Hregs rs2, msize_bytes]
        · rw [log_flat_cons]
          exact ⟨Hfit.1, Hfit.2.1, Hfit.2.2, Hlf⟩
    | SZ4 =>
      cases Ha : to_saddr (sr_get ss.s_regs rs1) imm.toInt with
      | none => simp [sym_step, Ha] at Hs
      | some a =>
        have Hadr : adenot E a = v_addi (getr regs rs1) imm.toInt := by
          rw [to_saddr_denot E (sr_get ss.s_regs rs1) imm.toInt a Ha, ← Hregs rs1]
        simp only [sym_step, Ha, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl⟩ := Hs
        obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
        obtain ⟨Hok, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
        have Hok' : store_ok segs (mem_denot E base ss.s_log)
            (v_addi (getr regs rs1) imm.toInt) 4 = true := by
          rw [← Hadr]
          exact store_ok_mono segs 4 base (mem_denot E base ss.s_log) (adenot E a)
            (mem_denot_grows E base ss.s_log) Hok
        refine ⟨mkst regs (v_addi (BitVec.ofInt 64 ss.s_pc) 4)
            (wbytes (mem_denot E base ss.s_log) (v_addi (getr regs rs1) imm.toInt)
              (word_to_le_bytes 4 (getr regs rs2))) rom,
          step_sw_val segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rs1 rs2 imm Hf He Hd Hok', ?_⟩
        refine ⟨regs, ?_, Hregs, ?_⟩
        · simp only [v_addi_lit, mem_denot_cons, Hadr, ← Hregs rs2, msize_bytes]
        · rw [log_flat_cons]
          exact ⟨Hfit.1, Hfit.2.1, Hfit.2.2, Hlf⟩
    | SZ8 =>
      cases Ha : to_saddr (sr_get ss.s_regs rs1) imm.toInt with
      | none => simp [sym_step, Ha] at Hs
      | some a =>
        have Hadr : adenot E a = v_addi (getr regs rs1) imm.toInt := by
          rw [to_saddr_denot E (sr_get ss.s_regs rs1) imm.toInt a Ha, ← Hregs rs1]
        simp only [sym_step, Ha, Option.some.injEq, Prod.mk.injEq] at Hs
        obtain ⟨rfl, rfl, rfl⟩ := Hs
        obtain ⟨Hfit, Hsc1⟩ := scs_denot_cons segs base E _ _ Hsc
        obtain ⟨Hok, Hsc2⟩ := scs_denot_cons segs base E _ _ Hsc1
        have Hok' : store_ok segs (mem_denot E base ss.s_log)
            (v_addi (getr regs rs1) imm.toInt) 8 = true := by
          rw [← Hadr]
          exact store_ok_mono segs 8 base (mem_denot E base ss.s_log) (adenot E a)
            (mem_denot_grows E base ss.s_log) Hok
        refine ⟨mkst regs (v_addi (BitVec.ofInt 64 ss.s_pc) 4)
            (wbytes (mem_denot E base ss.s_log) (v_addi (getr regs rs1) imm.toInt)
              (word_to_le_bytes 8 (getr regs rs2))) rom,
          step_sd_val segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rs1 rs2 imm Hf He Hd Hok', ?_⟩
        refine ⟨regs, ?_, Hregs, ?_⟩
        · simp only [v_addi_lit, mem_denot_cons, Hadr, ← Hregs rs2, msize_bytes]
        · rw [log_flat_cons]
          exact ⟨Hfit.1, Hfit.2.1, Hfit.2.2, Hlf⟩
  case opImm op rd rs imm =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : alu64 op (getr regs rs) (sext 64 imm)
        = edenot E (mkAlu op (sr_get ss.s_regs rs) (.ELit imm.toInt)) := by
      rw [mkAlu_denot]
      simp only [edenot]
      rw [← Hregs rs, ← sext64_lit imm (by decide)]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_opimm_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs imm Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case shiftImm op rd rs sh =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : alu64 op (getr regs rs) (zext 64 sh)
        = edenot E (mkAlu op (sr_get ss.s_regs rs) (.ELit (sh.toNat : Int))) := by
      rw [mkAlu_denot]
      simp only [edenot]
      rw [← Hregs rs, ← zext64_lit sh (by decide)]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_shiftimm_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs sh Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case op op rd rs1 rs2 =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : alu64 op (getr regs rs1) (getr regs rs2)
        = edenot E (mkAlu op (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2)) := by
      rw [mkAlu_denot, ← Hregs rs1, ← Hregs rs2]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_op_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs1 rs2 Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case opImm32 rd rs imm =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm))
        = edenot E (.EAluw .ADD (sr_get ss.s_regs rs) (.ELit imm.toInt)) := by
      simp only [edenot]
      rw [← Hregs rs, ← sext32_low32 imm (by decide)]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 .ADD (low32 (getr regs rs)) (sext 32 imm))))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_opimm32_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w rd rs imm Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case shiftImm32 op rd rs sh =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))
        = edenot E (.EAluw op (sr_get ss.s_regs rs) (.ELit (sh.toNat : Int))) := by
      simp only [edenot]
      rw [← Hregs rs, ← zext32_low32 sh (by decide)]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_shiftimm32_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs sh Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case op32 op rd rs1 rs2 =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))
        = edenot E (.EAluw op (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2)) := by
      simp only [edenot]
      rw [← Hregs rs1, ← Hregs rs2]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_op32_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs1 rs2 Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case mul op rd rs1 rs2 =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : mul_div op (getr regs rs1) (getr regs rs2)
        = edenot E (.EMd op (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2)) := by
      simp only [edenot]
      rw [← Hregs rs1, ← Hregs rs2]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_mul_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs1 rs2 Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩
  case mul32 op rd rs1 rs2 =>
    obtain ⟨rfl, rfl, rfl⟩ := Hs
    have hval : sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))
        = edenot E (.EMdw op (sr_get ss.s_regs rs1) (sr_get ss.s_regs rs2)) := by
      simp only [edenot]
      rw [← Hregs rs1, ← Hregs rs2]
    refine ⟨mkst (if bv_eqb rd 0 then regs
        else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
        (v_addi (BitVec.ofInt 64 ss.s_pc) 4) (mem_denot E base ss.s_log) rom,
      step_mul32_gen segs regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom w op rd rs1 rs2 Hf He Hd, ?_⟩
    exact ⟨_, by simp only [sset_pc, sset_log, sset_regs, v_addi_lit, hval],
      regs_ok_upd E ss.s_regs regs rd _ _ Hregs rfl, Hlf⟩

/-! ## 4. The soundness theorem -/

/-- `sym_move` on a NON-branch instruction is `sym_step` with the caller's
    branch script passed through unchanged; on a `.branch` it CONSUMES one
    direction instead and never consults `sym_step`.

    Stating that equation once, for all 34 non-branch constructors, is what
    keeps `sym_move_sound` and `sym_exec_sound` a single `Option` split
    instead of a 35-way `cases`.  `rfl` settles every constructor but
    `.branch`; there the hypothesis is already a contradiction, so `absurd`
    closes the goal before `rfl` is tried. -/
theorem sym_move_eq_of_not_branch {i : Instr}
    (h : ∀ (c : BranchCond) (rs1 rs2 : reg) (imm : BitVec 13),
      i ≠ Instr.branch c rs1 rs2 imm)
    (ss : sym_state) (rds : List expr) (dirs : List Bool) :
    sym_move i ss rds dirs
      = (match sym_step i ss rds with
         | some (ss', scs, rds') => some (ss', scs, rds', dirs)
         | none => none) := by
  cases i <;> first | rfl | exact absurd rfl (h _ _ _ _)

/-- **One directed symbolic move simulates one machine step.**  `sym_move` is
    `sym_step` plus the branch dispatch, so this is `sym_step_sound` on the
    non-branch arm and `step_branch_tk_gen`/`step_branch_ft_gen` on the branch
    arm — with the `SCBr` the executor emitted (`branch_taken c a b = t`)
    supplying the taken flag, and `regs_ok` turning the symbolic operands into
    the machine's `getr`.
 Naming it here is what lets the whole-execution
    induction below deal only with the `Option` returned by `sym_move`. -/
theorem sym_move_sound (E : env) (base rom : word → Option byte)
    (ss : sym_state) (ms : machine_state) (i : Instr) (ss' : sym_state)
    (scs : List sidecond) (w : BitVec 32) (rds rds' : List expr)
    (dirs dirs' : List Bool)
    (Hf : fetch_word segs (BitVec.ofInt 64 ss.s_pc) = some w)
    (He : is_ecall w = false)
    (Hd : decodeAny w = some (i, 4))
    (Hm : sym_move i ss rds dirs = some (ss', scs, rds', dirs'))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok E base rom ss ms) :
    ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' := by
  by_cases hbr : ∃ (c : BranchCond) (rs1 rs2 : reg) (imm : BitVec 13),
      i = .branch c rs1 rs2 imm
  · -- the branch arm: the executor consumed one caller-supplied direction
    obtain ⟨c, rs1, rs2, imm, rfl⟩ := hbr
    cases dirs with
    | nil => simp [sym_move] at Hm
    | cons t dirs0 =>
      simp only [sym_move, Option.some.injEq, Prod.mk.injEq] at Hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hm
      obtain ⟨regs, rfl, Hregs, Hlf⟩ := Hst
      have Hden : branch_taken c (edenot E (sr_get ss.s_regs rs1))
          (edenot E (sr_get ss.s_regs rs2)) = t :=
        (scs_denot_cons segs base E _ _ Hsc).1
      have Hc : branch_taken c (getr regs rs1) (getr regs rs2) = t := by
        simpa only [Hregs rs1, Hregs rs2] using Hden
      have Hstep : RiscvSemantics.step segs
          (mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom)
          = .MachineOk (mkst regs
              (if t then btgt (BitVec.ofInt 64 ss.s_pc) imm.toInt
               else v_addi (BitVec.ofInt 64 ss.s_pc) 4)
              (mem_denot E base ss.s_log) rom) := by
        cases t
        · exact step_branch_ft_gen segs regs _ _ rom w c rs1 rs2 imm Hf He Hd Hc
        · exact step_branch_tk_gen segs regs _ _ rom w c rs1 rs2 imm Hf He Hd Hc
      refine ⟨_, msteps.mst_step _ _ _ rfl Hstep (msteps.mst_refl _), regs, ?_, Hregs, Hlf⟩
      simp only [sjump_pc, sjump_log]
      cases t <;> simp [btgt_lit, v_addi_lit]
  · -- the non-branch arm: exactly one `sym_step`
    rw [sym_move_eq_of_not_branch (fun c rs1 rs2 imm hh => hbr ⟨c, rs1, rs2, imm, hh⟩)
      ss rds dirs] at Hm
    rcases hs : sym_step i ss rds with _ | ⟨ss0, scs0, rds0⟩
    · simp [hs] at Hm
    · simp only [hs, Option.some.injEq, Prod.mk.injEq] at Hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Hm
      obtain ⟨regs, rfl, Hregs, Hlf⟩ := Hst
      obtain ⟨ms', hstep, hstok⟩ :=
        sym_step_sound segs E base rom ss
          (mkst regs (BitVec.ofInt 64 ss.s_pc) (mem_denot E base ss.s_log) rom)
          i ss0 scs0 w rds rds0 Hf He Hd hs Hsc ⟨regs, rfl, Hregs, Hlf⟩
      exact ⟨ms', msteps.mst_step _ _ _ rfl hstep (msteps.mst_refl _), hstok⟩

/-- **If the executor reaches `ss'` from `ss` and every side condition it
    assumed holds under the valuation `E`, then the concrete machine really
    does reach a state described by `ss'`** — INCLUDING its memory, which is
    the base memory with the symbolic store log layered on.
 Every
    remaining arm (no fetch, `ecall`, undecodable, compressed, `sym_move`
    declined) hands the state back unchanged, so the machine stands still and
    `mst_refl` closes it. -/
theorem sym_exec_sound (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (ss' : sym_state) (scs : List sidecond)
    (E : env) (base rom : word → Option byte) (ms : machine_state)
    (Hex : sym_exec segs fuel dirs rds ss acc = (ss', scs))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok E base rom ss ms) :
    ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' := by
  induction fuel generalizing dirs rds ss acc ss' scs E base rom ms with
  | zero =>
    rw [sym_exec_zero segs dirs rds ss acc] at Hex
    obtain ⟨rfl, rfl⟩ := Hex
    exact ⟨ms, msteps.mst_refl ms, Hst⟩
  | succ f ih =>
    -- the fuel index is `Nat.succ f`; the unfolding lemmas are stated at
    -- `f + 1`, which is the same term up to `Nat.add` reduction
    have Hex1 : sym_exec segs (f + 1) dirs rds ss acc = (ss', scs) := Hex
    rcases hf : fetch_word segs (BitVec.ofInt 64 ss.s_pc) with _ | w
    · rw [sym_exec_nofetch segs f dirs rds ss acc hf] at Hex1
      obtain ⟨rfl, rfl⟩ := Hex1
      exact ⟨ms, msteps.mst_refl ms, Hst⟩
    · by_cases he : is_ecall w = true
      · rw [sym_exec_ecall segs f dirs rds ss acc w hf he] at Hex1
        obtain ⟨rfl, rfl⟩ := Hex1
        exact ⟨ms, msteps.mst_refl ms, Hst⟩
      · have he' : is_ecall w = false := by simpa using he
        rcases hd : decodeAny w with _ | ⟨i, sz⟩
        · rw [sym_exec_nodecode segs f dirs rds ss acc w hf he' hd] at Hex1
          obtain ⟨rfl, rfl⟩ := Hex1
          exact ⟨ms, msteps.mst_refl ms, Hst⟩
        · by_cases hsz : (sz == 4) = true
          · have hsz4 : sz = 4 := by simpa using hsz
            subst hsz4
            rcases hm : sym_move i ss rds dirs with _ | ⟨ss2, scs2, rds2, dirs2⟩
            · rw [sym_exec_stuck segs f dirs rds ss acc w i hf he' hd hm] at Hex1
              obtain ⟨rfl, rfl⟩ := Hex1
              exact ⟨ms, msteps.mst_refl ms, Hst⟩
            · -- one directed step, then the induction hypothesis on the tail
              rw [sym_exec_step segs f dirs rds ss acc w i ss2 scs2 rds2 dirs2
                hf he' hd hm] at Hex1
              obtain ⟨pre, hpre⟩ := sym_exec_acc segs f dirs2 rds2 ss2 (scs2 ++ acc)
              have hpre' : scs = pre ++ (scs2 ++ acc) := by
                have h := hpre
                rw [Hex1] at h
                simpa using h
              have Hsc2 : scs_denot segs base E scs2 := by
                have h1 := Hsc
                rw [hpre'] at h1
                exact (scs_denot_app segs base E scs2 acc
                  (scs_denot_app segs base E pre (scs2 ++ acc) h1).2).1
              obtain ⟨msA, hmsA, hstA⟩ :=
                sym_move_sound segs E base rom ss ms i ss2 scs2 w rds rds2 dirs dirs2
                  hf he' hd hm Hsc2 Hst
              obtain ⟨msB, hmsB, hstB⟩ :=
                ih dirs2 rds2 ss2 (scs2 ++ acc) ss' scs E base rom msA Hex1 Hsc hstA
              exact ⟨msB, msteps_trans segs ms msA msB hmsA hmsB, hstB⟩
          · rw [sym_exec_nosz segs f dirs rds ss acc w i sz hf he' hd
              (by simpa using hsz)] at Hex1
            obtain ⟨rfl, rfl⟩ := Hex1
            exact ⟨ms, msteps.mst_refl ms, Hst⟩

/-- Continuation form — the shape a per-binary proof actually uses: execute a
    block reflectively, then keep going with the tactic layer (or the shape
    library) from the resulting state.  The accumulator is the empty list, so
    every side condition of the run is in the returned `scs`. -/
theorem sym_exec_msteps (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (ss' : sym_state) (scs : List sidecond)
    (E : env) (base rom : word → Option byte) (ms : machine_state)
    (Hex : sym_exec segs fuel dirs rds ss [] = (ss', scs))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok E base rom ss ms) :
    ∃ ms', msteps segs ms ms' ∧ st_ok E base rom ss' ms' :=
  sym_exec_sound segs fuel dirs rds ss [] ss' scs E base rom ms Hex Hsc Hst

/-- **The FACTORABLE form.**

    `sym_exec_sound`/`sym_exec_msteps` hand back an EXISTENTIAL machine state
    together with an `st_ok` describing it.  That is the right thing for a
    tactic that immediately consumes both (`SymTac`'s `sym_block` destructs
    them into the goal it is standing in), but it is the wrong thing for a
    lemma STATEMENT: `st_ok` hides the exit register file under one more
    existential, so the caller cannot name it in a conclusion.

    Unfolding `st_ok` once puts the register file in front, which is what a
    per-iteration loop-body lemma needs:

      theorem body : <pre> ->
        exists R, <facts about R> /\ msteps segs ms (mkst R pc' mem' rom).

    Now the block's exit register file IS the lemma's witness, the caller
    `obtain`s the lemma at the top of the enclosing proof, and `R` stays in
    scope for the whole of it.  That is exactly the shape a Hoare loop rule
    (or `Common/DrainAlg`'s `Hread` hypothesis) asks for.

    `log_flat` is deliberately NOT exported: it is an internal invariant of
    one executor run (a following block starts from an EMPTY log, where it is
    `True`), and carrying it would put a second conjunct into every factored
    statement for nothing. -/
theorem sym_exec_ex (fuel : Nat) (dirs : List Bool) (rds : List expr)
    (ss : sym_state) (acc : List sidecond) (ss' : sym_state) (scs : List sidecond)
    (E : env) (base rom : word → Option byte) (ms : machine_state)
    (Hex : sym_exec segs fuel dirs rds ss acc = (ss', scs))
    (Hsc : scs_denot segs base E scs)
    (Hst : st_ok E base rom ss ms) :
    ∃ R, regs_ok E ss'.s_regs R
       ∧ msteps segs ms (mkst R (BitVec.ofInt 64 ss'.s_pc)
                            (mem_denot E base ss'.s_log) rom) := by
  obtain ⟨ms', Hms, R, Heq, Hregs, -⟩ :=
    sym_exec_sound segs fuel dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst
  exact ⟨R, Hregs, by rw [← Heq]; exact Hms⟩

/-! ## 5. Tactic layer -/

/--  closing `Ltac sym_val_norm`: normalize an `edenot` result into
    the `v_*` value shapes the rest of the library (`StepTac`'s `sp_norm`,
    `bveq`, `getr_resolve`) expects.

     is `cbn [edenot sr_get nth ridx bv_eqb s_regs s_pc]`
    then an OPTIONAL `rewrite` with the `alu_*` lemmas.  Lean has no `nth`
    (`sr_get` is `List.getD`-based), `s_regs`/`s_pc` are the structure
    projections, and "optional" is spelled `failIfUnchanged := false`, so the
    tactic is total here exactly as it is . -/
macro "sym_val_norm" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only
      [edenot, mkAlu_denot, mkSext32_denot, sr_get, ridx, bv_eqb,
       sym_state.s_regs, sym_state.s_pc,
       alu_add, alu_sub, alu_and, alu_or, alu_xor,
       alu_slt, alu_sltu, alu_sll, alu_srl, alu_sra])

/-- Compile-time check of the macro: `edenot` of an ALU value lands on the
    `v_*` shape. -/
example (E : env) (a b : expr) :
    edenot E (mkAlu .ADD a b) = v_add (edenot E a) (edenot E b) := by
  sym_val_norm

/-- Compile-time check of the macro: like  optional `rewrite ?`, it
    also accepts a goal that is already normal. -/
example (E : env) (a b : expr) :
    edenot E (.EMdw .MUL a b) = edenot E (.EMdw .MUL a b) := by
  sym_val_norm

/-! ## Contents

    §1 the symbolic value language, §2 the state and its denotation, §3 the
    stepper and the memory model (`sm_lookup_sound`), §4 soundness, §5 the
    tactic layer.  Nothing is deferred, and there is no proof hole and no
    extra postulate.

    Not restated here because they already live elsewhere in this tree (see
    the file header): `step_lw` and `step_sw_val` with their
    `Z_to_le_bytes`/`low32_le_bytes` plumbing (`Common/PropExec`,
    `Common/SeqExec`) and `b_lw_val` (`PropExec`); plus `mod_pow2_low` and
    `shiftr8_mod_pow2`, whose `Z`-level content this tree's `BitVec`-level
    `low32_lit`/`sext32_low32`/`zext32_low32` lemmas make unnecessary.

    §4 as landed:

    * `sym_move_eq_of_not_branch`, `sym_move_sound` — the DIRECTED one-step
      soundness: `sym_step_sound` on the non-branch arm, the two
      `step_branch_*_gen` lemmas on the branch arm.     * `sym_exec_msteps` — the `[]`-accumulator corollary (continuation form).
    * `sym_exec_ex` — the factorable form: the exit register file is the
      witness, `log_flat` is not exported.
    Deviations: `sym_move` is this tree's refactor of the branch dispatch (same
    behaviour, `sym_step` untouched), and `sym_val_norm`'s lemma list replaces
    `nth` — which this tree does not have — with the
    `mkAlu_denot`/`mkSext32_denot` bridges.
    Verify with `lake env lean LinuxSem/Common/SymExec.lean`
    (silent). -/




