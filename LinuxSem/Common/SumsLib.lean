/-
  * Common.SumsLib — image-INDEPENDENT kit for ADDRESS-PARAMETRIC routine summaries.

    SumsLib — image-INDEPENDENT kit for ADDRESS-PARAMETRIC routine summaries.

    A summary of a code blob is proved ONCE in a Section over
      [Variable segs : list Segment] (the image) and [Variable base : word]
      (where the blob is loaded), under the single hypothesis
      [code_at segs base 0 WORDS] (the instruction words fetched at
      base+0, base+4, ...).  The pc is kept in the normal form
      [at_ base <numeral>] throughout the walk ([pcn] re-normalises it after
      every step), so the generic fetch facts match syntactically.
    Instantiating for an image = proving [code_at SEGS (0x... : word) 0 WORDS]
      by computation ([code_at_vm]).  Relocating to another base (same
      words) is one more such instance.

    Also here: the byte-copy / byte-fill memory invariants ([memk], [msetk])
    generic in [segs].

  ---------------------------------------------------------------------
  NOTES (see the header for the tactic-fidelity policy this file follows)
  ---------------------------------------------------------------------

  * `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` → `BitVec.ofInt n z`,
    `bv_unsigned w` → `(w.toNat : Int)`, `repeat b n` →
    `List.replicate n b`, `firstn` → `List.take`, `nth` → `List.getD`,
    `length` → `List.length`.
    Everything else in the file is present, including its digit engine
    (`M8_aux`/`M8_digit_nat`/`M8_digit`).  What remains is the LIST step:
    expanding `Z_to_le_bytes 8 (c * M8)` into its eight `>>>`-shifted bytes
    (the nested `>>> 8 >>> 8` collapses to `>>> 16`, …), applying `M8_digit`
    to each, and rebuilding `List.replicate 8`.  That is plumbing over
    `Z_to_le_bytes`'s recursion, not new arithmetic; it is reported rather
    than left as a hole.
  * `Ltac`s: each becomes a Lean `macro`/`elab` of the same name, with
    COMMA-separated arguments (the house style — two whitespace-separated
    `term` arguments cannot appear in a Lean macro template).  ``'s
    `lazymatch type of D` dispatches (`an`, `ab_tk`, `ab_ft`) read the
    instruction constructor/condition off the constants the decode
    hypothesis MENTIONS (a real dispatch, not a searched arm list: a wrong
    step lemma applied to the wrong goal is an ELABORATION error in Lean, so
    a `first` list cannot backtrack over it).
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.Hoare
import LinuxSem.Common.WalkTac
import LinuxSem.Common.StoreOk
import LinuxSem.Common.StreamSim
import LinuxSem.Common.MmapSim
import LinuxSem.Common.StartupTac
import LinuxSem.Common.RefMemcpyLib

namespace LinuxSem.Common.SumsLib

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.Hoare
open LinuxSem.Common.WalkTac
open LinuxSem.Common.StoreOk
open LinuxSem.Common.StartupTac
open LinuxSem.Common.RefMemcpyLib

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The ambient `FPState` instance . -/
local instance sums_fx : FPState := fx0

/-! =====================================================================
    Code blobs at a symbolic base
    ===================================================================== -/

/-- The instruction words of a blob, fetched at `base + 0`, `base + 4`, … -/
def code_at (segs : List Segment) (base : word) (off : Int) (ws : List (BitVec 32)) : Prop :=
  match ws with
  | [] => True
  | w :: ws' => fetch_word segs (at_ base off) = some w ∧ code_at segs base (off + 4) ws'

/-- Prove a CLOSED `code_at` instance (literal base, concrete image) by
    computation, one fetch at a time.
"unfold, split every conjunction, decide each
    closed fetch".  `decide` on the closed fetch facts is the same
    kernel-checked certificate, and [decide_closed] (WalkTac) keeps it from
    being applied to an open goal. -/
macro "code_at_vm" : tactic =>
  `(tactic|
    (unfold code_at
     repeat (apply And.intro)
     all_goals (first | decide_closed | rfl | trivial | assumption)))

/-- Fold `at_ b (x + y)` with numeral `x`, `y`.

    a documented NO-OP.  A closed `Int` sum inside `at_` IS its value
    in Lean (`Int` addition on literals is definitional), so the `change`
     performs has nothing left to do — the same reasoning StepTac's notes give
    for `wlit`/`wlits`.  The macro is total, so call sites keep
    working. -/
macro "zlit_at" : tactic => `(tactic| skip)

/-- pc re-normalisation helper: rewrite the walker's `getr regs r = v`
    hypotheses into the goal . -/
macro "rwH" : tactic => `(tactic| pin)

/-- `v_addi x e` with `x` a VARIABLE (symbolic base) ~> `at_ x e`.

    a documented NO-OP: in Lean `at_ b e` IS `v_addi b e` (both are
    `BitVec.ofInt 64 (b.toNat + e)`), so there is nothing to change. -/
macro "fold_at_vars" : tactic => `(tactic| skip)

/-- Post-step normaliser (replaces WalkTac's `vnorm` in these walks): resolve
    registers, rewrite the walker's `getr regs r = v` hypotheses in, fold
    pc / address arithmetic into `at_ x <off>` form, literalise closed
    values.
-/
macro "vn" : tactic =>
  `(tactic|
    (gres
     rwH
     imm_norm
     try unfold btgt
     try rw [at_addi]
     try rw [v_addi_0]
     try rw [v_add_0_r]
     try rw [v_add_0_l]
     fold_at_vars
     try rw [at_addi]
     zlit_at
     vals_lit))

/--  second name for [vn]. -/
macro "pcn" : tactic => `(tactic| vn)

/-- the instruction constructor a decode hypothesis is about
    (`decodeAny w = some (Instr.<ctor> …)` mentions exactly one
    `Instr.<ctor>`), i.e. this tree's replacement for `lazymatch type of D`. -/
private def instrCtorOf (D : Lean.Expr) : Lean.MetaM (Option Lean.Name) := do
  let ty ← Lean.Meta.inferType D
  return ty.getUsedConstants.toList.find?
    (fun c => (``Instr).isPrefixOf c && c != ``Instr)

/-- the branch condition a decoded-branch hypothesis is about. -/
private def branchCondOf (D : Lean.Expr) : Lean.MetaM (Option Lean.Name) := do
  let ty ← Lean.Meta.inferType D
  return ty.getUsedConstants.toList.find?
    (fun c => (``BranchCond).isPrefixOf c && c != ``BranchCond)

/-- One ALU instruction / `jal`, then [vn].
-/
elab "an " F:term "," D:term : tactic => withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "an: {D} does not look like a decode hypothesis"
  if c == ``Instr.jal then
    Lean.Elab.Tactic.evalTactic (← `(tactic| (stepj $F, $D; vn)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| (stepi $F, $D; vn)))

/-- ALU step with caller-stated value `v`; `tac` proves the value equation
    (after `gres; rwH`).
-/
macro "av " F:term "," D:term "," v:term "," tac:tactic : tactic =>
  `(tactic| (stepiv $F, $D, $v, (by gres; rwH; imm_norm; $tac); vn))

/-- Conditional branch, TAKEN; `tac` closes the condition after
    `gres; rwH; imm_norm`.

    the six branch conditions are dispatched from `D`'s type, exactly
    as `ab_tk`'s `lazymatch` does; the chain goals are focused by position
    (`chainStepWith`: the extra Lean goal for the target-state metavariable
    is not a proposition, and a `first` list over `refine` arms cannot
    back over that). -/
elab "ab_tk " F:term "," D:term "," tac:tactic : tactic => withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "ab_tk: {D} does not look like a decode hypothesis"
  unless c == ``Instr.branch do
    throwError "ab_tk: {D} is not a decoded branch"
  let some cond ← branchCondOf Dexp
    | throwError "ab_tk: cannot read the branch condition of {D}"
  let lem ←
    if cond == ``BranchCond.EQ then pure ``step_beq_tk
    else if cond == ``BranchCond.NE then pure ``step_bne_tk
    else if cond == ``BranchCond.LT then pure ``step_blt_tk
    else if cond == ``BranchCond.GE then pure ``step_bge_tk
    else if cond == ``BranchCond.LTU then pure ``step_bltu_tk
    else if cond == ``BranchCond.GEU then pure ``step_bgeu_tk
    else throwError "ab_tk: cannot read the branch condition of {D}"
  let stepTac ← `(tactic|
    refine $(Lean.mkIdent lem) _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
      (first | decide_closed | assumption | (gres; rwH; imm_norm; $tac)))
  chainStepWith stepTac (← `(tactic| (step_simpl; vn)))

/-- Conditional branch, FALL-THROUGH (the `_ft` step lemmas, whose condition
    fact is `… = false`). -/
elab "ab_ft " F:term "," D:term "," tac:tactic : tactic => withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "ab_ft: {D} does not look like a decode hypothesis"
  unless c == ``Instr.branch do
    throwError "ab_ft: {D} is not a decoded branch"
  let some cond ← branchCondOf Dexp
    | throwError "ab_ft: cannot read the branch condition of {D}"
  let lem ←
    if cond == ``BranchCond.EQ then pure ``step_beq_ft
    else if cond == ``BranchCond.NE then pure ``step_bne_ft
    else if cond == ``BranchCond.LT then pure ``step_blt_ft
    else if cond == ``BranchCond.GE then pure ``step_bge_ft
    else if cond == ``BranchCond.LTU then pure ``step_bltu_ft
    else if cond == ``BranchCond.GEU then pure ``step_bgeu_ft
    else throwError "ab_ft: cannot read the branch condition of {D}"
  let stepTac ← `(tactic|
    refine $(Lean.mkIdent lem) _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
      (first | decide_closed | assumption | (gres; rwH; imm_norm; $tac)))
  chainStepWith stepTac (← `(tactic| (step_simpl; vn)))

/-- `ret` through register value `k` with `Hk : ret_ok k` in context.

    WalkTac's `stepret` shape — `stepjr` with the target equation
    closed by `gres; rwH; rfl`, then the pc rewritten to `k` from the
    caller's `ret_ok k` hypothesis (tried at both spellings of the offset,
    as WalkTac documents). -/
macro "aret " F:term "," D:term "," k:term : tactic =>
  `(tactic|
    (stepjr $F, $D, $k, (by gres; rwH; rfl)
     imm_norm
     (try (rw [show v_jalr $k 0 = $k from (by assumption)]))
     (try (rw [show v_jalr $k (BitVec.toInt (0 : BitVec 12)) = $k from (by assumption)]))))

/-- Conditions between `at_ x _` / `Z_to_bv 64 _` values, by arithmetic.
 This tree keeps the
    normalisation (`rwH; imm_norm; unorm`) and then closes the condition by
    computation or by `bv_omega`, with the branch-condition unfoldings in
    one arm for the open cases. -/
macro "condz" : tactic =>
  `(tactic|
    (rwH
     imm_norm
     unorm
     first
     | rfl
     | decide_closed
     | (try unfold at_
        try unfold c_eq
        try unfold c_ltu
        try unfold bv_eqb
        try unfold bv_ltu
        imm_norm
        unorm
        first | decide_closed | bv_omega | omega)
     | bv_omega
     | omega))

/-- Standard post-condition closer for a block: split the conjunction,
    resolve registers.

    `f_equal; lia` becomes `congr 1; omega` (`f_equal` is a Mathlib
    tactic and this tree is core Lean only). -/
macro "post" : tactic =>
  `(tactic|
    (repeat (apply And.intro)
     gres
     rwH
     try rw [at_addi]
     all_goals (first | rfl | (congr 1; omega) | assumption | skip)))

/-! =====================================================================
    Small word facts
    ===================================================================== -/

/-- `Z_to_bv 64 (bv_unsigned a + d)` is `at_ a d` (definitionally). -/
theorem at_fold (a : word) (d : Int) : BitVec.ofInt 64 ((a.toNat : Int) + d) = at_ a d :=
  rfl

/-- `v_add` of a literal offset is the `at_` address. -/
theorem v_add_at (a : word) (z : Int) (Hz : 0 ≤ z ∧ z < ((2 ^ 64 : Nat) : Int)) :
    v_add a (BitVec.ofInt 64 z) = at_ a z := by
  unfold v_add at_
  rw [u_Z2bv z Hz.1 Hz.2]

/-- `at_` is injective on in-range offsets. -/
theorem at_eq_u (a : word) (d e : Int)
    (Hd : 0 ≤ (a.toNat : Int) + d ∧ (a.toNat : Int) + d < ((2 ^ 64 : Nat) : Int))
    (He : 0 ≤ (a.toNat : Int) + e ∧ (a.toNat : Int) + e < ((2 ^ 64 : Nat) : Int))
    (H : at_ a d = at_ a e) : d = e := by
  have h := congrArg (fun w : word => (w.toNat : Int)) H
  rw [at_u a d Hd.1 Hd.2, at_u a e He.1 He.2] at h
  omega

/-! =====================================================================
    The byte-copy invariant, generic in the image
    ===================================================================== -/

/-- The copy invariant: a byte list `bs` readable at `src`, a writable range
    at `dst`, and the ranges disjoint. -/
structure cpyH (segs : List Segment) (mem0 : word → Option byte) (dst src : word)
    (n : Int) (bs : List byte) : Prop where
  /-- The copy length is non-negative. -/
  cHn : 0 ≤ n
  /-- The buffer has the copy length. -/
  cHlen : bs.length = n.toNat
  /-- The source buffer is readable. -/
  cHsrc : rdn segs mem0 src bs.length = some bs
  /-- The destination range is writable. -/
  cHdst : store_ok segs mem0 dst bs.length = true
  /-- Source and destination ranges are disjoint. -/
  cHdisj : (dst.toNat : Int) + n ≤ (src.toNat : Int) ∨
    (src.toNat : Int) + n ≤ (dst.toNat : Int)
  /-- The source range does not wrap. -/
  cHnws : (src.toNat : Int) + n < ((2 ^ 64 : Nat) : Int)
  /-- The destination range does not wrap. -/
  cHnwd : (dst.toNat : Int) + n < ((2 ^ 64 : Nat) : Int)

section MEMK

variable (segs : List Segment) (mem0 : word → Option byte)
variable (dst src : word) (n : Int) (bs : List byte)

/-- Memory after `k` bytes have been copied. -/
def memk (k : Int) : word → Option byte :=
  wbytes mem0 dst (bs.take k.toNat)

/-- Source byte `j`. -/
def b_ (j : Int) : byte :=
  bs.getD j.toNat (BitVec.ofInt 8 0)

/-- the scalar facts an invariant proof needs in context . -/
private theorem cpyH_facts (HOK : cpyH segs mem0 dst src n bs) :
    (0 ≤ n ∧ bs.length = n.toNat ∧
      ((dst.toNat : Int) + n ≤ (src.toNat : Int) ∨
        (src.toNat : Int) + n ≤ (dst.toNat : Int)) ∧
      (src.toNat : Int) + n < ((2 ^ 64 : Nat) : Int) ∧
      (dst.toNat : Int) + n < ((2 ^ 64 : Nat) : Int)) :=
  ⟨HOK.cHn, HOK.cHlen, HOK.cHdisj, HOK.cHnws, HOK.cHnwd⟩

theorem memk_0 (HOK : cpyH segs mem0 dst src n bs) :
    memk mem0 dst bs 0 = mem0 := by
  unfold memk
  rfl

theorem memk_n (HOK : cpyH segs mem0 dst src n bs) :
    memk mem0 dst bs n = wbytes mem0 dst bs := by
  unfold memk
  rw [← HOK.cHlen, List.take_length]

/-- The byte `j` of the source is readable after `k` bytes of copying, as
    long as `j < n` and `k ≤ n`. -/
theorem rd_src1 (HOK : cpyH segs mem0 dst src n bs) (k j : Int)
    (Hk : 0 ≤ k ∧ k ≤ n) (Hj : 0 ≤ j) (H1 : j + 1 ≤ n) :
    rdn segs (memk mem0 dst bs k) (at_ src j) 1 = some [b_ bs j] := by
  unfold memk b_
  obtain ⟨hn, hlen, hdisj, hnws, hnwd⟩ := cpyH_facts segs mem0 dst src n bs HOK
  have hnt : ((n.toNat : Int)) = n := Int.toNat_of_nonneg hn
  have htake : ((bs.take k.toNat).length : Int) ≤ n := by
    rw [List.length_take, hlen]; omega
  have hj : ((j.toNat : Int)) = j := Int.toNat_of_nonneg Hj
  have hsl : j.toNat < bs.length := by rw [hlen]; omega
  rw [rdn_wbytes_out]
  · rw [show at_ src j = at_ src ((j.toNat : Int)) from by rw [hj]]
    rw [rdn_sub segs mem0 bs.length src bs j.toNat 1 HOK.cHsrc (by omega)]
    rw [sub_nth bs j.toNat hsl]
  · have hsj : ((at_ src j).toNat : Int) = (src.toNat : Int) + j :=
      at_u src j (by omega) (by omega)
    rw [hsj]
    rcases hdisj with h | h
    · right; omega
    · left; omega
  · have hsj : ((at_ src j).toNat : Int) = (src.toNat : Int) + j :=
      at_u src j (by omega) (by omega)
    rw [hsj]; omega
  · omega

/-- The destination byte `j` is writable after `k` bytes of copying. -/
theorem wr_dst (HOK : cpyH segs mem0 dst src n bs) (k j : Int) (m : Nat)
    (Hj : 0 ≤ j) (Hm : j + (m : Int) ≤ n) :
    store_ok segs (memk mem0 dst bs k) (at_ dst j) m = true := by
  unfold memk
  obtain ⟨hn, hlen, hdisj, hnws, hnwd⟩ := cpyH_facts segs mem0 dst src n bs HOK
  have hnt : ((n.toNat : Int)) = n := Int.toNat_of_nonneg hn
  have hj : ((j.toNat : Int)) = j := Int.toNat_of_nonneg Hj
  rw [← hj]
  refine store_ok_at segs mem0 dst bs.length (bs.take k.toNat) j.toNat m ?_ HOK.cHdst ?_ ?_
  · rw [hlen, hnt]; omega
  · exact Nat.zero_le _
  · rw [hlen, hnt]; push_cast; omega

/-- Copying the source byte `k` extends the copy by one byte. -/
theorem memk_extend1 (HOK : cpyH segs mem0 dst src n bs) (k : Int)
    (Hk : 0 ≤ k) (H1 : k + 1 ≤ n) :
    wbytes (memk mem0 dst bs k) (at_ dst k) [b_ bs k] = memk mem0 dst bs (k + 1) := by
  unfold memk b_
  obtain ⟨hn, hlen, hdisj, hnws, hnwd⟩ := cpyH_facts segs mem0 dst src n bs HOK
  have hnt : ((n.toNat : Int)) = n := Int.toNat_of_nonneg hn
  have hk : ((k.toNat : Int)) = k := Int.toNat_of_nonneg Hk
  have hk1 : (k + 1).toNat = k.toNat + 1 := by
    rw [Int.toNat_add Hk (by omega)]; rfl
  have hlenk : k.toNat < bs.length := by rw [hlen]; omega
  rw [show at_ dst k = at_ dst ((k.toNat : Int)) from by rw [hk]]
  rw [show [bs.getD k.toNat (BitVec.ofInt 8 0)] = sub bs k.toNat 1 from
    (sub_nth bs k.toNat hlenk).symm]
  rw [show (k + 1).toNat = k.toNat + 1 from hk1]
  exact wbytes_extend' mem0 dst bs k.toNat 1 (by omega)

/-- `lbu rd, imm(rs)` reading source byte `j`. -/
theorem mc_lbu (HOK : cpyH segs mem0 dst src n bs) (regs : BvMap word) (pc : word)
    (rom : word → Option byte) (w : BitVec 32) (rd rs : reg) (imm : BitVec 12)
    (k j0 j : Int)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.load .SZ1 false rd rs imm, 4))
    (Hrs : getr regs rs = at_ src j0) (Hj : j0 + imm.toInt = j)
    (Hk : 0 ≤ k ∧ k ≤ n) (Hj0 : 0 ≤ j) (Hj1 : j + 1 ≤ n) :
    RiscvSemantics.step segs (mkst regs pc (memk mem0 dst bs k) rom) =
      .MachineOk (mkst (if bv_eqb rd 0 = true then regs
        else regupd regs rd (BitVec.ofInt 64 ((b_ bs j).toNat : Int)))
        (v_addi pc 4) (memk mem0 dst bs k) rom) := by
  refine step_lbu segs regs pc (memk mem0 dst bs k) rom w rd rs imm (b_ bs j) Hf He Hd ?_
  rw [Hrs, at_addi, show j0 + imm.toInt = j from Hj]
  exact rd_src1 segs mem0 dst src n bs HOK k j Hk Hj0 Hj1

/-- `sb rs2, imm(rs1)` writing destination byte `k`. -/
theorem mc_sb (HOK : cpyH segs mem0 dst src n bs) (regs : BvMap word) (pc : word)
    (rom : word → Option byte) (w : BitVec 32) (rs1 rs2 : reg) (imm : BitVec 12)
    (k k0 : Int) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.store .SZ1 rs1 rs2 imm, 4))
    (Hrs1 : getr regs rs1 = at_ dst k0) (Hk0 : k0 + imm.toInt = k)
    (Hrs2 : getr regs rs2 = v)
    (Hb : BitVec.ofInt 8 ((v.toNat : Int)) = b_ bs k)
    (Hk : 0 ≤ k) (Hk1 : k + 1 ≤ n) :
    RiscvSemantics.step segs (mkst regs pc (memk mem0 dst bs k) rom) =
      .MachineOk (mkst regs (v_addi pc 4) (memk mem0 dst bs (k + 1)) rom) := by
  rw [← memk_extend1 segs mem0 dst src n bs HOK k Hk Hk1]
  refine MmapSim.step_sb_at segs regs pc (memk mem0 dst bs k) rom w rs1 rs2 imm
    (at_ dst k) v (b_ bs k) Hf He Hd ?_ Hrs2 Hb ?_
  · rw [Hrs1, at_addi, show k0 + imm.toInt = k from Hk0]
  · exact wr_dst segs mem0 dst src n bs HOK k k 1 (by omega) (by omega)

end MEMK

/-- The byte of a byte-valued word round-trips through `Z_to_bv 8`. -/
theorem sb_val_b (bs : List byte) (j : Int) :
    BitVec.ofInt 8 (((BitVec.ofInt 64 ((b_ bs j).toNat : Int)).toNat : Int))
      = b_ bs j := by
  have hb := u8_range (b_ bs j)
  rw [u_Z2bv _ hb.1 (by omega), BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  exact BitVec.setWidth_eq _

/-! =====================================================================
    The byte-fill invariant, generic in the image
    ===================================================================== -/

section MSETK

variable (segs : List Segment) (mem0 : word → Option byte)
variable (s : word) (n : Int) (b : byte)

/-- Memory after `k` bytes of the fill. -/
def msetk (k : Int) : word → Option byte :=
  wbytes mem0 s (List.replicate k.toNat b)

theorem msetk_0 (Hnw : (s.toNat : Int) + n < ((2 ^ 64 : Nat) : Int)) :
    msetk mem0 s b 0 = mem0 := by
  unfold msetk
  rfl

theorem wr_s (Hn : 0 ≤ n) (Hnw : (s.toNat : Int) + n < ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs mem0 s n.toNat = true)
    (k j : Int) (m : Nat) (Hj : 0 ≤ j) (Hm : j + (m : Int) ≤ n) :
    store_ok segs (msetk mem0 s b k) (at_ s j) m = true := by
  unfold msetk
  have hnt : ((n.toNat : Int)) = n := Int.toNat_of_nonneg Hn
  have hj : ((j.toNat : Int)) = j := Int.toNat_of_nonneg Hj
  rw [← hj]
  refine store_ok_at segs mem0 s n.toNat (List.replicate k.toNat b) j.toNat m ?_ Hok ?_ ?_
  · rw [hnt]; omega
  · exact Nat.zero_le _
  · rw [hnt]; push_cast; omega

theorem msetk_extend (Hn : 0 ≤ n) (Hnw : (s.toNat : Int) + n < ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs mem0 s n.toNat = true)
    (k : Int) (m : Nat) (Hk : 0 ≤ k) :
    wbytes (msetk mem0 s b k) (at_ s k) (List.replicate m b)
      = msetk mem0 s b (k + (m : Int)) := by
  unfold msetk
  have hk : ((k.toNat : Int)) = k := Int.toNat_of_nonneg Hk
  have hkm : ((k + (m : Int)).toNat) = k.toNat + m := by
    rw [Int.toNat_add Hk (by omega)]
    rfl
  rw [show at_ s k = at_ s ((k.toNat : Int)) from by rw [hk]]
  rw [show ((k + (m : Int)).toNat) = k.toNat + m from hkm]
  rw [← List.replicate_append_replicate, wbytes_app, List.length_replicate]

theorem msetk_extend1 (Hn : 0 ≤ n) (Hnw : (s.toNat : Int) + n < ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs mem0 s n.toNat = true) (k : Int) (Hk : 0 ≤ k) :
    wbytes (msetk mem0 s b k) (at_ s k) [b] = msetk mem0 s b (k + 1) := by
  have h := msetk_extend segs mem0 s n b Hn Hnw Hok k 1 Hk
  simpa using h

end MSETK

/-! =====================================================================
    Replicated-byte patterns (internal_memset's aligned path)
    ===================================================================== -/

/-- a multiple of `2^k` has no bits below `k`. -/
private theorem testBit_mul_two_pow_false {x i k : Nat} (h : i < k) :
    (x * 2 ^ k).testBit i = false := by
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul]
  simp [show ¬ k ≤ i from by omega]

/-- a value below `2^k` has no bits at or above `k`. -/
private theorem testBit_false_of_lt {y i k : Nat} (hy : y < 2 ^ k) (h : k ≤ i) :
    y.testBit i = false := by
  refine Nat.testBit_lt_two_pow ?_
  exact Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) h)

/-- Masking an aligned value with a smaller mask is zero : `Z.land (a * 2^k) b = 0` for `0 ≤ b < 2^k`. -/
theorem land_shl_disjoint (a b : Int) (k : Nat) (Ha : 0 ≤ a)
    (Hb : 0 ≤ b ∧ b < ((2 ^ k : Nat) : Int)) :
    zland (a * ((2 ^ k : Nat) : Int)) b = 0 := by
  have hx : ((a * ((2 ^ k : Nat) : Int)).toNat) = a.toNat * 2 ^ k := by
    rw [Int.toNat_mul Ha (by exact Int.natCast_nonneg (2 ^ k)), Int.toNat_natCast]
  have hy : b.toNat < 2 ^ k := by
    have h1 : ((b.toNat : Int)) < ((2 ^ k : Nat) : Int) := by
      rw [Int.toNat_of_nonneg Hb.1]; exact Hb.2
    exact Int.ofNat_lt.mp h1
  unfold zland
  rw [hx]
  have hzero : a.toNat * 2 ^ k &&& b.toNat = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases h : i < k
    · rw [testBit_mul_two_pow_false h]
      rfl
    · rw [testBit_false_of_lt hy (by omega)]
      exact Bool.and_false _
  rw [hzero]
  rfl

/-- `Z.lor (a * 2^k) b = a * 2^k + b` for `0 ≤ b < 2^k` . -/
theorem lor_shl_disjoint (a b : Int) (k : Nat) (Ha : 0 ≤ a)
    (Hb : 0 ≤ b ∧ b < ((2 ^ k : Nat) : Int)) :
    zlor (a * ((2 ^ k : Nat) : Int)) b = a * ((2 ^ k : Nat) : Int) + b := by
  have hx : ((a * ((2 ^ k : Nat) : Int)).toNat) = a.toNat * 2 ^ k := by
    rw [Int.toNat_mul Ha (by exact Int.natCast_nonneg (2 ^ k)), Int.toNat_natCast]
  have hy : b.toNat < 2 ^ k := by
    have h1 : ((b.toNat : Int)) < ((2 ^ k : Nat) : Int) := by
      rw [Int.toNat_of_nonneg Hb.1]; exact Hb.2
    exact Int.ofNat_lt.mp h1
  unfold zlor
  rw [hx]
  have hnat : a.toNat * 2 ^ k ||| b.toNat = a.toNat * 2 ^ k + b.toNat := by
    rw [show a.toNat * 2 ^ k = a.toNat <<< k from by rw [Nat.shiftLeft_eq]]
    exact (Nat.shiftLeft_add_eq_or_of_lt hy a.toNat).symm
  rw [hnat]
  push_cast
  rw [Int.toNat_of_nonneg Ha, Int.toNat_of_nonneg Hb.1]

/-- `slli` of a word multiplies its value by a power of two . -/
theorem v_slli_mul (x : word) (k : Nat) :
    v_slli x (k : Int) = BitVec.ofInt 64 ((x.toNat : Int) * ((2 ^ k : Nat) : Int)) := by
  unfold v_slli zshiftl
  rw [show ((k : Int)).toNat = k from Int.toNat_natCast k]

/-- `Z_to_bv 64` of an in-range `Int` has that `toNat`. -/
private theorem toNat_ofInt_range (z : Int) (h0 : 0 ≤ z)
    (h1 : z < ((2 ^ 64 : Nat) : Int)) :
    (BitVec.ofInt 64 z).toNat = z.toNat := by
  have h : (((BitVec.ofInt 64 z).toNat : Int)) = z := u_Z2bv z h0 h1
  have h2 : ((z.toNat : Int)) = z := Int.toNat_of_nonneg h0
  exact Int.ofNat_inj.mp (h.trans h2.symm)

/-- `or` of an offset value and a low value.
-/
theorem v_or_shl (x : word) (a : Int) (k : Nat) (Ha : 0 ≤ a)
    (Hak : a * ((2 ^ k : Nat) : Int) + (x.toNat : Int) < ((2 ^ 64 : Nat) : Int))
    (Hx : (x.toNat : Int) < ((2 ^ k : Nat) : Int)) :
    v_or (BitVec.ofInt 64 (a * ((2 ^ k : Nat) : Int))) x
      = BitVec.ofInt 64 (a * ((2 ^ k : Nat) : Int) + (x.toNat : Int)) := by
  have hpow : 0 ≤ ((2 ^ k : Nat) : Int) := Int.natCast_nonneg _
  have hxnn : 0 ≤ (x.toNat : Int) := Int.natCast_nonneg _
  have hu : 0 ≤ a * ((2 ^ k : Nat) : Int) := Int.mul_nonneg Ha hpow
  have hsum : 0 ≤ a * ((2 ^ k : Nat) : Int) + (x.toNat : Int) := by omega
  have hsumlt := Hak
  have hpart : a * ((2 ^ k : Nat) : Int) < ((2 ^ 64 : Nat) : Int) := by omega
  have hxnat : x.toNat < 2 ^ k := by
    have h1 : ((x.toNat : Int)) < ((2 ^ k : Nat) : Int) := Hx
    exact Int.ofNat_lt.mp h1
  have h_unat : (BitVec.ofInt 64 (a * ((2 ^ k : Nat) : Int))).toNat = a.toNat * 2 ^ k := by
    rw [toNat_ofInt_range _ hu hpart, Int.toNat_mul Ha hpow, Int.toNat_natCast]
  have h_vnat : (BitVec.ofInt 64 (a * ((2 ^ k : Nat) : Int) + (x.toNat : Int))).toNat
      = a.toNat * 2 ^ k + x.toNat := by
    rw [toNat_ofInt_range _ hsum hsumlt, Int.toNat_add hu hxnn, Int.toNat_mul Ha hpow,
      Int.toNat_natCast, Int.toNat_natCast]
  have h_or : a.toNat * 2 ^ k ||| x.toNat = a.toNat * 2 ^ k + x.toNat := by
    rw [show a.toNat * 2 ^ k = a.toNat <<< k from by rw [Nat.shiftLeft_eq]]
    exact (Nat.shiftLeft_add_eq_or_of_lt hxnat a.toNat).symm
  apply BitVec.eq_of_toNat_eq
  rw [testbit_u_vor, h_unat, h_vnat, h_or]

/-- `0x0101010101010101`: the byte-replication constant. -/
def M8 : Int := 72340172838076673

/-- `G` lemma — the digit computation from a
    `Mhi * B + Mlo` decomposition of `M8`.  `c * M8 = B * (c * Mhi) + c * Mlo`
    with `c * Mlo < B`, so the division drops the low part, and
    `Mhi % 256 = 1` leaves `c` in the remaining byte. -/
private theorem M8_aux (Mhi Mlo B c : Nat) (HB : 0 < B)
    (HM : Mhi * B + Mlo = 72340172838076673)
    (Hlo : 255 * Mlo < B) (Hm1 : Mhi % 256 = 1) (Hc : c < 256) :
    (c * 72340172838076673) / B % 256 = c := by
  have hc : c ≤ 255 := by omega
  have hcM : c * 72340172838076673 = B * (c * Mhi) + c * Mlo := by
    rw [← HM, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (c * Mhi) B]
  have hsmall : c * Mlo < B := by
    have : c * Mlo ≤ 255 * Mlo := Nat.mul_le_mul_right _ hc
    omega
  rw [hcM, Nat.add_comm (B * (c * Mhi)) (c * Mlo), Nat.add_mul_div_left _ _ HB,
    Nat.div_eq_of_lt hsmall, Nat.zero_add]
  rw [Nat.mul_mod, Hm1, Nat.mul_one]
  rw [Nat.mod_eq_of_lt Hc, Nat.mod_eq_of_lt Hc]

/-- [M8_aux] at  eight `(Mhi, Mlo, B)` triples — the
    byte-replication digit fact, at the `Nat` level. -/
private theorem M8_digit_nat (c k : Nat) (Hc : c < 256) (Hk : k < 8) :
    (c * 72340172838076673) / 2 ^ (8 * k) % 256 = c := by
  match k with
  | 0 => simpa using M8_aux 72340172838076673 0 1 c (by decide) (by decide) (by decide) (by decide) Hc
  | 1 => simpa using M8_aux 282578800148737 1 (2 ^ 8) c (by decide) (by decide) (by decide) (by decide) Hc
  | 2 => simpa using M8_aux 1103823438081 257 (2 ^ 16) c (by decide) (by decide) (by decide) (by decide) Hc
  | 3 => simpa using M8_aux 4311810305 65793 (2 ^ 24) c (by decide) (by decide) (by decide) (by decide) Hc
  | 4 => simpa using M8_aux 16843009 16843009 (2 ^ 32) c (by decide) (by decide) (by decide) (by decide) Hc
  | 5 => simpa using M8_aux 65793 4311810305 (2 ^ 40) c (by decide) (by decide) (by decide) (by decide) Hc
  | 6 => simpa using M8_aux 257 1103823438081 (2 ^ 48) c (by decide) (by decide) (by decide) (by decide) Hc
  | 7 => simpa using M8_aux 1 282578800148737 (2 ^ 56) c (by decide) (by decide) (by decide) (by decide) Hc
  | _ + 8 => omega

/-- The byte an `sb`, byte `k` of the replicated pattern: `Z.shiftr (c * M8)
    (8 * k) mod 256 = c`, with the shift as a `Nat`
    equal to  `k : Z ∈ {0, …, 7}` under its hypothesis.
-/
theorem M8_digit (c : Int) (k : Nat) (Hc : 0 ≤ c ∧ c < 256) (Hk : k < 8) :
    zshiftr (c * M8) (8 * k) % 256 = c := by
  have hc0 := Hc.1
  have hcN : c.toNat < 256 := by
    have h : ((c.toNat : Int)) = c := Int.toNat_of_nonneg hc0
    omega
  have key : (c.toNat * 72340172838076673) / 2 ^ (8 * k) % 256 = c.toNat :=
    M8_digit_nat c.toNat k hcN Hk
  have hnum : c * M8 = ((c.toNat * 72340172838076673 : Nat) : Int) := by
    unfold M8
    conv => lhs; rw [← Int.toNat_of_nonneg hc0]
    rw [show (72340172838076673 : Int) = ((72340172838076673 : Nat) : Int) from rfl,
      ← Int.natCast_mul]
  unfold zshiftr
  rw [hnum, ← Int.natCast_ediv]
  rw [show (256 : Int) = ((256 : Nat) : Int) from rfl, ← Int.natCast_emod, key,
    Int.toNat_of_nonneg hc0]

/-- Two `Z_to_bv 8` are equal when their arguments agree modulo 256. -/
theorem byte_eq_mod (x y : Int)
    (H : x % ((2 ^ 8 : Nat) : Int) = y % ((2 ^ 8 : Nat) : Int)) :
    BitVec.ofInt 8 x = BitVec.ofInt 8 y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, H]

/-- The byte an `sb` of register value `c` stores, as `Z_to_bv 8 (u c)`. -/
theorem sb_byte_u (c : word) :
    BitVec.ofInt 8 ((c.toNat : Int))
      = BitVec.ofInt 8 ((c.toNat : Int) % ((2 ^ 8 : Nat) : Int)) := by
  apply byte_eq_mod
  rw [Int.emod_emod]

/-! =====================================================================
    `or` at a pre-normalized value
    ===================================================================== -/

/-- `or rd, rs1, rs2` with the written value pre-normalized (SeqExec has
    `_at` forms for add/sub/… but not for `or`). -/
theorem step_or_at (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte) (w : BitVec 32) (rd rs1 rs2 : reg) (v : word)
    (Hf : fetch_word segs pc = some w) (He : is_ecall w = false)
    (Hd : decodeAny w = some (Instr.op .OR rd rs1 rs2, 4))
    (Hrd : bv_eqb rd 0 = false)
    (Hv : v_or (getr regs rs1) (getr regs rs2) = v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
      .MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  rw [step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd]
  simp only [Hrd, Bool.false_eq_true, ite_false, Hv]

/-- [av] for an `or` instruction. -/
macro "av_or " F:term "," D:term "," vv:term "," tac:tactic : tactic =>
  `(tactic|
    (chain_step <;>
      (first
       | rfl
       | assumption
       | (refine step_or_at _ _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;>
           (first | decide_closed | assumption | omega | (gres; rwH; imm_norm; $tac)))
       | (step_simpl; vn))))

/-! -/

/-- `code_at` of the empty word list is `True`. -/
example (segs : List Segment) (base : word) (off : Int) :
    code_at segs base off [] := trivial

/-- `code_at` of a one-word blob is the one fetch. -/
example (segs : List Segment) (base : word) (w : BitVec 32)
    (H : fetch_word segs base = some w) : code_at segs base 0 [w] := by
  unfold code_at
  refine ⟨?_, trivial⟩
  rwa [at_0]

/-- `at_fold` is the definitional identity  uses it as. -/
example (a : word) (d : Int) : BitVec.ofInt 64 ((a.toNat : Int) + d) = at_ a d := rfl

/-- `M8` is the byte-replication constant. -/
example : M8 = 72340172838076673 := rfl

end LinuxSem.Common.SumsLib
