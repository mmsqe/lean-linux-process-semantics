/-
  * Common.WalkTac — thin helpers on top of StepTac for walking concrete code
        with the generated *_code fetch/decode facts.

  - `gres`        peel `getr` through a `regupd` chain (SeqExec.getr_resolve
                  minus its final `getr_nz` respelling).  = MuslCall.gres.
  - `vals_lit`    fold every CLOSED register value in the goal's `regupd`
                  chain(s) to its `Z_to_bv 64 z` literal (vm-computed,
                  closedness-guarded, skips values already literal).
  - `vnorm`       the after-step normalizer: `gres; imm_norm;
                  rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit`. Keeps
                  the symbolic state SMALL — without it every register read
                  re-embeds the earlier `regupd` chain and the state doubles
                  per step.
  - `stepn F D`   one ALU instruction (`stepi`) or `jal` (`stepj`) + `vnorm`.
  - `stepb_tk F D tac` / `stepb_ft F D tac`
                  one conditional branch, taken / not taken; `tac` closes the
                  condition fact (`c_eq ..`/`c_lts ..`/`c_ltu ..` =
                  true/false) AFTER `gres` has resolved its registers.
  - `stepret F D k tac`
                  `ret`/`jr` through `stepjr` to target `k`; `tac` proves
                  `getr regs rs1 = k` after `gres`.  If `k` is a literal the
                  pc is re-literalized; if `k` is a variable with
                  `Hk : ret_ok k` in context, the pc becomes `k`.

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  The  file is a tactic library plus two lemmas.  Both lemmas are
  stated faithfully; each `Ltac` becomes a Lean `macro` of the same name and
  arity.  Calling syntax follows StepTac: COMMA-separated arguments
  (`stepn F, D`), because two whitespace-separated `term` arguments cannot
  appear in a Lean macro template.

  The systematic deviations, each marked at the tactic itself:

  1. *`lazymatch type of D`* (`stepn`, `stepb_tk`, `stepb_ft`).  
     picks the ONE applicable step lemma from the SHAPE of the decode
     hypothesis `D` (`decode_any _ = Some (Jal _ _, _)`, `… (Branch BC_LT _
     _ _, _)`, …).  Lean tactics cannot pattern-match a hypothesis type, but
     a tactic ELABORATOR can read the constants that type MENTIONS, and a
     decode hypothesis mentions exactly one `Instr.<ctor>` (and, for a
     branch, one `BranchCond.<cond>`).  This tree therefore keeps the
     dispatch: one metaprogramming helper ([instrCtorOf]/[branchCondOf])
     picks the lemma, and the tactic runs just that lemma.  This is
     deliberate rather than an arm list (the fallback StepTac's
     `stepi`/`stepw` use): a wrong step lemma's `$D` argument is an
     ELABORATION error, not a tactic failure, so a searched list would abort
     instead of failing over.  Same dispatch, same lemmas, same conditions.

  2. *`vm_compute`-based normalizers* (`val_lit`, `vals_lit`, `cond_compute`).
     These exist because `simp`/`dsimp` will not reduce a `bv_unsigned`
     projection over a vm-cast numeral, and because `rewrite` cannot match a
     closed redex whose reduction needs conversion.  `val_lit` still folds one
     NAMED term (`wlit_closed`, a real closedness-guarded rewrite);
     `vals_lit` — the goal SWEEP — is a documented total no-op, and
     `cond_compute` degrades to `rfl`/`decide`.
  3. *`ltac:(…)` tactic arguments* (`tac`, `oktac`, `rtac`) are Lean tactic
     arguments, so a call site writes the tactic directly
     (`stepb_tk F, D, exact Hc`), not wrapped in a term.  (The CATEGORY
     matters: a `tactic` argument splices after a `;`; a `tacticSeq`
     argument splices as a `first` alternative.  `oktac` is the latter, the
     other three the former.)  One exception: `stepv`'s closer is passed
     THROUGH StepTac's `stepiv`, which takes a proof TERM: see `stepv`'s
     docstring.
  4. *Closed-goal computation* (`cond_compute`, and the `is_ecall` premise of
     every step arm).  This tree therefore has
     [decide_closed]: the same closedness test StepTac's `check_closed_term`
     performs, applied to the GOAL, then `decide`.  It is used wherever
      relies on computation on a closed fact.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.SeqExec
import LinuxSem.Common.StepTac
import LinuxSem.Common.Hoare

namespace LinuxSem.Common.WalkTac

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.Common.PropExec
open LinuxSem.Common.CatExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.SeqExec
open LinuxSem.Common.StepTac
open LinuxSem.Common.Hoare

/-- The FP state the smoke tests at the end walk at . -/
local instance walk_fx : FPState := fx0

-- Lean adds a section variable to a lemma's type only when the statement
-- mentions it, and this tree makes the binding explicit.
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Peel `getr` through a `regupd` chain: resolve the register reads of the
    current state to the values the chain wrote.

    The register-inequality side conditions of `getr_same`/`getr_other` are
    closed by `reg_neq_tac` (SeqExec: `decide` — the registers are closed
    `BitVec 5` literals at every call site). -/
macro "gres" : tactic =>
  `(tactic|
    (repeat (first
      | rw [getr_same _ _ _ (by reg_neq_tac)]
      | rw [getr_other _ _ _ _ (by reg_neq_tac)]
      | rw [getr_zero])))

/-- `add rd, rs, x` with a zero operand (e.g. `add a2,s4,a2` after
    `mv a2,zero-valued s0`).

     closes by `bv_eq` after `change (bv_unsigned (Z_to_bv 64 0))
    with 0`; this tree computes that projection with `decide` and finishes with
    StepTac's `ofInt_toNat` (the `BitVec.ofInt`/numeral bridge). -/
theorem v_add_0_r (x : word) : v_add x (BitVec.ofInt 64 0) = x := by
  unfold v_add
  have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by decide
  rw [h0, Int.add_zero]
  exact ofInt_toNat x

theorem v_add_0_l (x : word) : v_add (BitVec.ofInt 64 0) x = x := by
  unfold v_add
  have h0 : ((BitVec.ofInt 64 0).toNat : Int) = 0 := by decide
  rw [h0, Int.zero_add]
  exact ofInt_toNat x

/-- is `e` a `Nat` literal?   -/
private def isNatLitExpr (e : Lean.Expr) : Bool :=
  match e with
  | .lit (.natVal _) => true
  | _ => false

/-- is `e` a `Z` numeral — `Int.ofNat n` or `Int.negSucc n`
    with `n` a `Nat` literal — i.e. -/
private def isIntLitExpr (e : Lean.Expr) : Bool :=
  match e with
  | .lit (.natVal _) => true
  | .app f a =>
    (f.isConstOf ``Int.ofNat || f.isConstOf ``Int.negSucc) && isNatLitExpr a
  | _ => false

/-- Is `p` a `Nat` numeral literal?   tests the SHAPE of a `positive`
    (`xH`, or `xO q`/`xI q` with `q` such a shape); this tree decides the same
    question on the ELABORATED term (`whnf` of a numeral is the literal
    itself, so `3` and `(3)` both qualify, and `n + 1` does not).  Used only
    as a guard — nothing here is a proof. -/
elab "is_pos_lit " p:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm p none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  unless isNatLitExpr (← Lean.Meta.whnf e) do
    throwError "is_pos_lit: {p} is not a numeral literal"

/-- Is `z` a `Z` numeral (`Z0`, `Zpos p`, `Zneg p` with `p` a `positive`
    literal)?  This tree reads the elaborated term: `Int.ofNat n` / a bare
    `Nat` literal for the non-negative case, `Int.negSucc n` for `Zneg`. -/
elab "is_Z_lit " z:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm z none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  unless isIntLitExpr (← Lean.Meta.whnf e) do
    throwError "is_Z_lit: {z} is not an integer literal"

/-- Fold one closed, not-yet-literal word term to its `BitVec.ofInt 64 z`
    literal (StepTac's `wlit_closed`: closedness-guarded, fails fast on an
    open term).
 The two skip
    arms exist only so that `vals_lit`'s SWEEP does not make a literal value
    uglier; in this tree the sweep is a no-op (see `vals_lit`) and this tactic
    is only ever applied to a term the caller explicitly wants folded, so the
    guard has nothing to guard. -/
macro "val_lit " v:term : tactic => `(tactic| wlit_closed $v)

/-- Fold every closed register value sitting in a `regupd` chain of the goal.

    a total no-op.  It sweeps the goal for `regupd _ _ ?v` subterms and
    folds each with `val_lit`: a rewrite cannot match a closed redex whose
    reduction needs conversion, so an unfurled
    chain would re-embed itself at every step.  Lean's `exact`/`rw`/`apply`
    unify up to reducible unfolding and `decide`/`rfl` reduce closed terms, so
    the symbolic state stays flat without the sweep (the same reasoning
    StepTac's notes give for `wlits`/`wlits_closed`, of which this is the
    per-chain instance).  A caller that does want one value folded names it:
    `val_lit (v_addi sp (-8))`. -/
macro "vals_lit" : tactic => `(tactic| skip)

/-- The after-step normalizer: resolve the register reads (`gres`), then fold
    the immediate/zero arithmetic the step introduced. -/
macro "vnorm" : tactic =>
  `(tactic|
    (gres
     imm_norm
     try (rw [v_addi_0])
     try (rw [v_add_0_r])
     try (rw [v_add_0_l])
     vals_lit))

/-- the `Instr` constructor a decode hypothesis is about.
 This is what makes [stepn]/[stepb_tk]/
    [stepb_ft] real dispatchers rather than a searched arm list (which the
    decoded shape alone cannot make safe: passing [D] to the wrong step lemma
    is an elaboration error, not a tactic failure). -/
private def instrCtorOf (D : Lean.Expr) : Lean.MetaM (Option Lean.Name) := do
  let ty ← Lean.Meta.inferType D
  return ty.getUsedConstants.toList.find?
    (fun c => (``Instr).isPrefixOf c && c != (``Instr))

/-- the branch condition a decoded-branch hypothesis is about
    (`decodeAny _ = some (Instr.branch .EQ …)` mentions `BranchCond.EQ`). -/
private def branchCondOf (D : Lean.Expr) : Lean.MetaM (Option Lean.Name) := do
  let ty ← Lean.Meta.inferType D
  return ty.getUsedConstants.toList.find?
    (fun c => (``BranchCond).isPrefixOf c && c != (``BranchCond))

/-- ALU step or jump, then normalize.

     dispatches on `decode_any _ = Some (Jal _ _, _)` and takes
    `stepj` for a `jal`, `stepi` for everything else. -/
elab "stepn " F:term "," D:term : tactic => do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "stepn: {D} does not look like a decode hypothesis"
  if c == ``Instr.jal then
    Lean.Elab.Tactic.evalTactic (← `(tactic| stepj $F, $D))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| stepi $F, $D))
  Lean.Elab.Tactic.evalTactic (← `(tactic| vnorm))

/-- ALU step with the written value stated by the caller (StepTac's `stepiv`)
    and the standard value closer. -/
macro "vres" : tactic =>
  `(tactic|
    (gres
     imm_norm
     try (rw [v_addi_0])
     first | rfl | bveq | skip))

/-- [stepiv] with the value obligation closed by [vres].

    `vres` is a TACTIC, while StepTac's `stepiv` takes its value proof as
    a TERM`).  This tree
    therefore supplies `(by vres)`. -/
macro "stepv " F:term "," D:term "," v:term : tactic =>
  `(tactic| stepiv $F, $D, $v, (by vres))

/-- `decide`, but only on a CLOSED goal.

    This toolchain's `decide` REFUSES a goal that has free variables (it errors
    with "Expected type must not contain free variables" instead of failing
    over, and `decide +revert` overflows the recursion budget on the same
    goals) — so a bare `decide` arm inside a `first` list aborts the whole
    list when it lands on a goal with a variable in it, which in these
    dispatchers is most of them.  The guard is StepTac's `check_closed_term`
    test (no metavariable, no context variable) applied to the goal rather
    than to a named term, i.e. exactly the `is_ecall _ = false` premise the
    step lemmas want, which always IS closed. -/
elab "decide_closed" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  let lctx ← Lean.getLCtx
  let mut mentionsCtx := false
  for ldecl in lctx do
    if target.containsFVar ldecl.fvarId then mentionsCtx := true
  if target.hasMVar || mentionsCtx then
    throwError "decide_closed: the goal is not closed"
  Lean.Elab.Tactic.evalTactic (← `(tactic| decide))

/-- One conditional branch, TAKEN.  `tac` closes the condition fact
    (`c_eq …`/`c_lts …`/`c_ltu …` = `true`) after `gres` has resolved the
    registers the fact is about.

     dispatches the six branch conditions on the shape of `D`;
    this tree reads the condition off the type of `D` ([branchCondOf]) and runs
    the matching step lemma — the same six lemmas, the same six conditions,
    chosen rather than searched.  `step_simpl` closes the goal the chain
    leaves for the next step. -/
elab "stepb_tk " F:term "," D:term "," tac:tactic : tactic => do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "stepb_tk: {D} does not look like a decode hypothesis"
  unless c == ``Instr.branch do
    throwError "stepb_tk: {D} is not a decoded branch"
  let some cond ← branchCondOf Dexp
    | throwError "stepb_tk: cannot read the branch condition of {D}"
  let lem ←
    if cond == ``BranchCond.EQ then pure ``step_beq_tk
    else if cond == ``BranchCond.NE then pure ``step_bne_tk
    else if cond == ``BranchCond.LT then pure ``step_blt_tk
    else if cond == ``BranchCond.GE then pure ``step_bge_tk
    else if cond == ``BranchCond.LTU then pure ``step_bltu_tk
    else if cond == ``BranchCond.GEU then pure ``step_bgeu_tk
    else throwError "stepb_tk: cannot read the branch condition of {D}"
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (chain_step <;>
      first
      | rfl
      | assumption
      | (refine $(Lean.mkIdent lem) _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
          first | decide_closed | assumption | (gres; imm_norm; $tac))
      | step_simpl)))

/-- One conditional branch, NOT taken: the same dispatch as `stepb_tk`, over
    the `_ft` (fall-through) step lemmas, which carry `… = false`. -/
elab "stepb_ft " F:term "," D:term "," tac:tactic : tactic => do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some c ← instrCtorOf Dexp
    | throwError "stepb_ft: {D} does not look like a decode hypothesis"
  unless c == ``Instr.branch do
    throwError "stepb_ft: {D} is not a decoded branch"
  let some cond ← branchCondOf Dexp
    | throwError "stepb_ft: cannot read the branch condition of {D}"
  let lem ←
    if cond == ``BranchCond.EQ then pure ``step_beq_ft
    else if cond == ``BranchCond.NE then pure ``step_bne_ft
    else if cond == ``BranchCond.LT then pure ``step_blt_ft
    else if cond == ``BranchCond.GE then pure ``step_bge_ft
    else if cond == ``BranchCond.LTU then pure ``step_bltu_ft
    else if cond == ``BranchCond.GEU then pure ``step_bgeu_ft
    else throwError "stepb_ft: cannot read the branch condition of {D}"
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (chain_step <;>
      first
      | rfl
      | assumption
      | (refine $(Lean.mkIdent lem) _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
          first | decide_closed | assumption | (gres; imm_norm; $tac))
      | step_simpl)))

/-- Close a CLOSED boolean condition (`c_xx lit lit = b`) by computation.
 `rfl` leads because the
    closed case is definitional. -/
macro "cond_compute" : tactic => `(tactic| (first | rfl | decide_closed))

/-- Branch on two CLOSED (literal) register values: the condition computes,
    and so does the direction. -/
macro "stepb " F:term "," D:term : tactic =>
  `(tactic|
    first
    | stepb_tk $F, $D, cond_compute
    | stepb_ft $F, $D, cond_compute)

/-- `ret` / `jr rs`: jump through a register to `k`.  `tac` proves
    `getr regs rs1 = k` (after `gres` has resolved the chain).

    The pc after the jump is `v_jalr k 0`; when `k` is a literal,
     re-literalizes it with `wlit`, and when `k` is a variable with
    `Hk : ret_ok k` (Hoare) in context — or `Hk : v_jalr k 0 = k` — it
    rewrites the pc to `k`.
    the rewrite is tried at TWO spellings, `v_jalr k 0` and
    `v_jalr k (BitVec.toInt 0)`. -/
macro "stepret " F:term "," D:term "," k:term "," tac:tactic : tactic =>
  `(tactic|
    (stepjr $F, $D, $k, (by gres; $tac)
     imm_norm
     first
     | (rw [show v_jalr $k 0 = $k from (by assumption)])
     | (rw [show v_jalr $k (BitVec.toInt (0 : BitVec 12)) = $k from (by assumption)])
     | (wlit (v_jalr $k 0))
     | skip))

/-- Store-double with SYMBOLIC operands.  Unlike StepTac's `stepw`, the
    address/value side goals are normalized with `gres` (not `getr_resolve`,
    whose final `getr_nz` respells `getr regs r` as `reg_get regs r` and so
    disconnects the goal from the walker's `getr regs r = v` hypotheses); they
    are then closed by reflexivity / assumption / `f_equal; lia` / `bveq`.
    `aa`/`vv`: the intended address and value; `oktac` closes `store_ok`.
 Each script is applicable to its own obligation
    only, which is what makes the merged list behave like the bullets.
    `oktac` is a Lean `tacticSeq` argument, so a
    call site writes `stepsd F, D, a, v, solve_store_ok`; it is tried before
    the generic `assumption` arm so that the `store_ok` obligation is the
    caller's script's to close, not whatever happens to be in context. -/
macro "stepsd " F:term "," D:term "," aa:term "," vv:term "," oktac:tacticSeq : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_sd_at _ _ _ _ _ _ _ _ _ $aa $vv $F ?_ $D ?_ ?_ ?_ <;>
          first
          | decide_closed
          | $oktac
          | assumption
          | (gres; imm_norm; try (rw [v_addi_0]); sp_norm;
             first | rfl | assumption | bveq)
          | (gres; first | rfl | assumption | (symm; assumption)))
      | step_simpl)

/-- Load-double of a value `vv` whose 8 bytes `word_to_le_bytes 8 vv` the
    tactic `rtac` reads back (`rtac` proves
    `rdn segs mem ADDR 8 = some (word_to_le_bytes 8 vv)` after the address has
    been normalized).
-/
macro "stepld " F:term "," D:term "," vv:term "," rtac:tactic : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_ld _ _ _ _ _ _ _ _ _ (word_to_le_bytes 8 $vv) $vv $F ?_ $D ?_ ?_ <;>
          first
          | (apply bytes_le_to_Z_8)
          | decide_closed
          | assumption
          | (gres; imm_norm; try (rw [v_addi_0]); sp_norm; $rtac)
          | rfl)
      | (step_simpl; vnorm))

/-! ## Smoke tests

    One call site per tactic: the tactic layer is otherwise exercised only by
    the `*_code`-driven proofs downstream, and a macro that is never expanded
    is not a macro that works (a wrong argument count only surfaces when the
    arm FIRES).  Each test walks a ONE-instruction chain from an ASSUMED
    fetch/decode fact — the step lemmas are stated for arbitrary `segs` and
    hypotheses about `fetch_word`/`decodeAny`, so no code image is needed —
    and then closes the chain's tail with `msteps.mst_refl` itself. -/

/- `gres` resolves a `regupd` chain (and the x0 read). -/
example (regs : BvMap word) (v : word) :
    getr (regupd (regupd regs 8 v) 9 v) 8 = v := by
  gres

example (regs : BvMap word) (v : word) :
    getr (regupd regs 8 v) 0 = BitVec.ofInt 64 0 := by
  gres

/- The two zero-operand sums. -/
example (x : word) : v_add x (BitVec.ofInt 64 0) = x := v_add_0_r x
example (x : word) : v_add (BitVec.ofInt 64 0) x = x := v_add_0_l x

/- The literal tests, both directions. -/
example : True := by
  is_pos_lit 3
  is_Z_lit (3 : Int)
  is_Z_lit (-3 : Int)
  trivial

example (n : Nat) : True := by
  fail_if_success is_pos_lit (n + 1)
  fail_if_success is_Z_lit (n : Int)
  trivial

/- `vnorm` after a step: the register read resolved, the `addi …, 0` folded. -/
example (regs : BvMap word) (v : word) :
    v_addi (getr (regupd regs 8 v) 8) 0 = v := by
  vnorm

/- `vres` on a settled value obligation. -/
example (regs : BvMap word) (v : word) :
    v_addi (getr (regupd regs 8 v) 8) 0 = v := by
  vres

/- `val_lit` folds one named closed redex. -/
example : v_addi (BitVec.ofInt 64 0) 4 = BitVec.ofInt 64 4 := by
  val_lit (BitVec.ofInt 64 4)
  bveq

/- `stepn` on `addi x8, x9, 0` (`0x00090413`). -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00090413 : BitVec 32))
    (Hd : decodeAny (0x00090413 : BitVec 32) = some (Instr.opImm .ADD 8 9 0, 4)) :
    msteps segs (mkst regs pc mem rom)
      (mkst (if bv_eqb (n := 5) 8 0 = true then regs
             else regupd regs 8 (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))))
        (v_addi pc 4) mem rom) := by
  stepn Hf, Hd
  exact msteps.mst_refl _

/- `stepv`, with the written value named. -/
example (segs : List Segment) (regs : BvMap word) (pc v : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00090413 : BitVec 32))
    (Hd : decodeAny (0x00090413 : BitVec 32) = some (Instr.opImm .ADD 8 9 0, 4)) :
    msteps segs (mkst regs pc mem rom)
      (mkst (regupd regs 8 (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))))
        (v_addi pc 4) mem rom) := by
  stepv Hf, Hd, v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))
  exact msteps.mst_refl _

/- `stepb_tk`: the taken arm of `beq x8, x9, 0` (`0x00940063`). -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00940063 : BitVec 32))
    (Hd : decodeAny (0x00940063 : BitVec 32) = some (Instr.branch .EQ 8 9 0, 4))
    (Hc : c_eq (getr regs 8) (getr regs 9) = true) :
    msteps segs (mkst regs pc mem rom)
      (mkst regs (btgt pc (BitVec.toInt (0 : BitVec 13))) mem rom) := by
  stepb_tk Hf, Hd, exact Hc
  exact msteps.mst_refl _

/- `stepb`: the same branch with a CLOSED condition — an EMPTY register file,
    so both registers read `0` and the direction computes.  This is the
    `cond_compute` path. -/
example (segs : List Segment) (pc : word) (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00940063 : BitVec 32))
    (Hd : decodeAny (0x00940063 : BitVec 32) = some (Instr.branch .EQ 8 9 0, 4)) :
    msteps segs (mkst bvmap_empty pc mem rom)
      (mkst bvmap_empty (btgt pc (BitVec.toInt (0 : BitVec 13))) mem rom) := by
  stepb Hf, Hd
  exact msteps.mst_refl _

/- `stepb_ft`: the fall-through arm of the same branch. -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00940063 : BitVec 32))
    (Hd : decodeAny (0x00940063 : BitVec 32) = some (Instr.branch .EQ 8 9 0, 4))
    (Hc : c_eq (getr regs 8) (getr regs 9) = false) :
    msteps segs (mkst regs pc mem rom) (mkst regs (v_addi pc 4) mem rom) := by
  stepb_ft Hf, Hd, exact Hc
  exact msteps.mst_refl _

/- `stepret`: `ret` through a register pinned to `k`, with `ret_ok k`. -/
example (segs : List Segment) (regs : BvMap word) (pc k : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00048067 : BitVec 32))
    (Hd : decodeAny (0x00048067 : BitVec 32) = some (Instr.jalr 0 9 0, 4))
    (Ht : getr regs 9 = k) (Hk : ret_ok k) :
    msteps segs (mkst regs pc mem rom) (mkst regs k mem rom) := by
  stepret Hf, Hd, k, exact Ht
  exact msteps.mst_refl _

/- `stepsd`: `sd x8, 0(x9)` (`0x0084B023`) into a grant the caller has
    already settled. -/
example (segs : List Segment) (regs : BvMap word) (pc a v : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x0084B023 : BitVec 32))
    (Hd : decodeAny (0x0084B023 : BitVec 32) = some (Instr.store .SZ8 9 8 0, 4))
    (Ha : v_addi (getr regs 9) 0 = a) (Hv : getr regs 8 = v)
    (Hok : store_ok segs mem a 8 = true) :
    msteps segs (mkst regs pc mem rom)
      (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  stepsd Hf, Hd, a, v, exact Hok
  exact msteps.mst_refl _

/- `stepld`: `ld x8, 0(x9)` (`0x0004B403`) of a value the caller has already
    read back. -/
example (segs : List Segment) (regs : BvMap word) (pc v : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x0004B403 : BitVec 32))
    (Hd : decodeAny (0x0004B403 : BitVec 32) = some (Instr.load .SZ8 true 8 9 0, 4))
    (Hr : rdn segs mem (v_addi (getr regs 9) 0) 8
            = some (word_to_le_bytes 8 v)) :
    msteps segs (mkst regs pc mem rom)
      (mkst (regupd regs 8 v) (v_addi pc 4) mem rom) := by
  stepld Hf, Hd, v, exact Hr
  exact msteps.mst_refl _

end LinuxSem.Common.WalkTac
