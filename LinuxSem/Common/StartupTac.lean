/-
  * Common.StartupTac — stepping tactics for the reference startup walk.

    StartupTac — stepping tactics for the reference startup walk.
    Image-INDEPENDENT (the [F_*]/[D_*] facts are passed as arguments).

    Conventions of these walks:
    - register facts are hypotheses [getr regs r = v]; [pin] rewrites every
      such fact into the goal, so values stay small and symbolic bases
      ([sp0], [d], ...) appear by name;
    - addresses/values relative to a symbolic base [b] are spelled
      [Z_to_bv 64 (bv_unsigned b + k)] / [Z_to_bv 64 (bv_unsigned b - k)];
    - memory is either a plain [wbytes] chain (leaf summaries such as
      [memset]) or [MemSplit.cmem sp0 mem0 J D].

  ---------------------------------------------------------------------
  NOTES (see the tactic-fidelity section of `Common/StepTac.lean`)
  ---------------------------------------------------------------------

  The  file is a tactic library plus TWO lemmas (`bwd`,
  `bwd_msteps`); both lemmas are stated faithfully and each `Ltac` becomes
  a Lean `macro`/`elab` of the same name.  Calling syntax follows StepTac
  and WalkTac: COMMA-separated arguments (`stw F, D, aa, vv, oktac`),
  because two whitespace-separated `term` arguments cannot appear in a
  Lean macro template.
*`lazymatch type of D`* (`stw`, `ld_step`, `lb_step`).  Lean tactics
     cannot pattern-match a hypothesis type, but a tactic ELABORATOR can
     read the constants a type MENTIONS — and a decode hypothesis mentions
     exactly one `Instr.<ctor>` and one `MSize.<size>`.  This tree therefore
     keeps the dispatch as a real dispatch (`findConstApp` below), not as a
     searched arm list: passing `D` to the wrong step lemma is an
     ELABORATION error, not a tactic failure, so a `first` list over the
     arms would abort instead of failing over (`WalkTac`'s docstring records
     the same finding).
  2. *`vm_compute`-based normalizers* (`zlit`, and the `imm_norm` inside
     `addr_norm`/`vclose`).  These exist because `simp`/`dsimp` will not
     reduce a `bv_unsigned` projection over a vm-cast numeral, and because
     `rewrite` cannot match a closed redex whose reduction needs
     conversion.
  3. *`ltac:(…)` tactic arguments* (`oktac`, `rdtac`, `valtac`) are Lean
     tactic arguments, so a call site writes the tactic directly
     (`stw F, D, a, v, exact Hok`), not wrapped in a term.
  4. *Closed-goal computation* (the `is_ecall` premise of every step arm,
     and `ok_data`'s `wseg_ok` premise).
  5. *`check_closed_term x; eval vm_compute in x; change x with x'`*
     (`zlit`, `blit`).  `blit` is stated as a real rewrite (the byte fold is
     a lemma, not a computation); `zlit` is the no-op of note 2.

  6.
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
import LinuxSem.Common.MemSplit
import LinuxSem.Common.StartupAux
import LinuxSem.Common.ZStores

namespace LinuxSem.Common.StartupTac

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
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
open LinuxSem.Common.StreamSim
open LinuxSem.Common.MemSplit
open LinuxSem.Common.StartupAux
open LinuxSem.Common.ZStores

set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The `FPState` instance the step/value lemmas carry an unused section
    argument for; every statement below is FP-free . -/
local instance startup_tac_fx : FPState := fx0

/-! =====================================================================
    Register facts ([pin]) and address/value normalization
    ===================================================================== -/

/-- does `pat` occur as a subterm of `e`?   -/
private partial def occursExpr (pat : Lean.Expr) (e : Lean.Expr) : Bool :=
  if e == pat then true
  else
    match e with
    | .app f a => occursExpr pat f || occursExpr pat a
    | .lam _ d b _ => occursExpr pat d || occursExpr pat b
    | .forallE _ d b _ => occursExpr pat d || occursExpr pat b
    | .letE _ t v b _ => occursExpr pat t || occursExpr pat v || occursExpr pat b
    | .mdata _ b => occursExpr pat b
    | .proj _ _ b => occursExpr pat b
    | _ => false

/-- the two sides of an equation type.

    Not `Expr.eq?`: this toolchain's `eq?` returns the type argument and the
    left side, not the two sides (this tree therefore destructures the
    `@Eq α lhs rhs` application itself). -/
private def eqSides? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  match ty with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs => some (lhs, rhs)
  | _ => none

/-- (shared with `Common/SumsLib.lean`): run `tac`, RESTORING
    the goal list if it throws.

    This is load-bearing, not hygiene: a Lean tactic that fails part-way can
    leave the ambient goal list emptied (`all_goals` clears it before running
    its tactic), and an enclosing `first` then believes the goal was CLOSED —
    a silently "successful" tactic.  Elab-based tactics therefore restore the
    goal list on failure, so a failed arm behaves like a failed tactic:
    the state is exactly what it was before the arm. -/
def withGoalsRestored (tac : Lean.Elab.Tactic.TacticM Unit) :
    Lean.Elab.Tactic.TacticM Unit := do
  let saved ← Lean.Elab.Tactic.getGoals
  try tac
  catch e =>
    Lean.Elab.Tactic.setGoals saved
    throw e

/-- Rewrite every register hypothesis `getr regs r = v` into the goal, i.e.
    make the walker's symbolic values appear by name.
 Lean has no
    hypothesis-pattern matching in tactic syntax, so this is an `elab` that
    walks the local context; the `repeat` is bounded to four passes for the
    reason StepTac's `u_norm` is (an unbounded `repeat` whose last arm always
    succeeds does not terminate) — four passes cover every chain a walk
    produces, because each pass rewrites every applicable hypothesis at
    once. -/
elab "pin" : tactic => withGoalsRestored do
  for _ in [0:4] do
    let target ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.getLCtx
    let mut idents : Array Lean.Ident := #[]
    for ldecl in lctx do
      unless ldecl.isImplementationDetail do
        if let some (lhs, _) := eqSides? ldecl.type then
          if lhs.getAppFn.isConstOf ``getr && occursExpr lhs target then
            idents := idents.push
              (Lean.mkIdentFrom (← Lean.MonadRef.getRef) ldecl.userName)
    if idents.isEmpty then break
    for id in idents do
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [$id:term]))

/-- rewrite `u_Z2bv` in ONE goal, depth-bounded, returning the
    side conditions as extra goals (instead of trying to close them). -/
private partial def unormGoal (g : Lean.MVarId) (depth : Nat) :
    Lean.Elab.Tactic.TacticM (List Lean.MVarId) := do
  if depth == 0 then return [g]
  try
    match ← Lean.Elab.Tactic.run g (Lean.Elab.Tactic.evalTactic
        (← `(tactic| rw [u_Z2bv]))) with
    | [] => return []
    | main :: sides =>
      let rest ← unormGoal main (depth - 1)
      return rest ++ sides
  catch _ => return [g]

/-- `bv_unsigned (Z_to_bv 64 z)` -> `z` when the arithmetic can bound `z`.
 `u_norm` is
    `iterate 4 (first | ((rw [u_Z2bv]) <;> (first | omega | skip)) | skip)`,
    and the `<;>` makes its `omega` run on the REWRITTEN MAIN GOAL as well —
    so `u_norm`'s own `omega` can close the caller's goal, after which any
    following tactic in the same sequence raises "no goals to be solved".
    `unorm` therefore rewrites on the caller's goal only and leaves the two
    range side conditions as extra goals for the caller's arithmetic closer
    (which is what `region_side` and `addr_norm` end with). -/
elab "unorm" : tactic => withGoalsRestored do
  let gs ← Lean.Elab.Tactic.getGoals
  match gs with
  | [] => return ()
  | g :: rest =>
    let out ← unormGoal g 4
    Lean.Elab.Tactic.setGoals (out ++ rest)

/-- Fold a closed `Z` inside a `Z_to_bv 64 _` address/value position.

    a documented NO-OP: it would need a `change z with z'` only if a rewrite
    could not match a closed redex whose reduction needs conversion; in Lean
    the numeral IS the value, so
    `rfl`/`decide`/`bveq` see straight through.  The macro is total, so call
    sites keep working unchanged. -/
macro "zlit" : tactic => `(tactic| skip)

/-- run the tactic steps in order, stopping as soon as the goal
    list is empty.

    Lean raises "no goals to be solved" where a tactic sequence would simply
    have nothing left to do — and `region_side`'s `u_norm` CAN close
    its goal (its `omega` runs on the main goal too, as a `;`-sequencing
    side effect).  The guard keeps the sequence usable as a side-condition
    closer. -/
private def runWhileGoals (steps : List Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit := do
  for step in steps do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return ()
    Lean.Elab.Tactic.evalTactic step

/-- is `tac` — a CONDITIONAL rewrite — applicable to `g` with all
    of its side conditions closed by `sideTac`?

    Lean's `rw` cannot run `by region_side`, so a side condition is closed
    AFTER the rewrite; that would commit the rewrite even when the region is
    the wrong one. -/
private def sidesClose (g : Lean.MVarId) (tac : Lean.Syntax) (sideTac : Lean.Syntax) :
    Lean.Elab.Tactic.TacticM Bool := do
  let saved ← Lean.Elab.Tactic.getGoals
  let out ← (do
    let ty ← g.getType
    let copy ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar ty
    try
      let rem ← Lean.Elab.Tactic.run copy.mvarId! (Lean.Elab.Tactic.evalTactic tac)
      if rem.isEmpty then return false
      for side in rem.tail! do
        let rest ← Lean.Elab.Tactic.run side (Lean.Elab.Tactic.evalTactic sideTac)
        unless rest.isEmpty do return false
      return true
    catch _ => return false)
  Lean.Elab.Tactic.setGoals saved
  return out

/-- the committing half of [sidesClose] — the same conditional
    rewrite on the real goal, with every side condition closed by [sideTac]
    and the rewritten goal (always the FIRST goal `rw` produces) left for the
    caller. -/
private def commitRewrite (sideTac : Lean.Syntax) (tac : Lean.Syntax) :
    Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic tac
  -- `rw` leaves the rewritten goal first, then its side conditions.
  let gs ← Lean.Elab.Tactic.getGoals
  match gs with
  | [] => return ()
  | main :: sides =>
    for side in sides do
      Lean.Elab.Tactic.setGoals [side]
      Lean.Elab.Tactic.evalTactic sideTac
    Lean.Elab.Tactic.setGoals [main]

/-- Side conditions of the `cmem` region lemmas and of `rdn_wbytes_out`.
-/
elab "region_side" : tactic => withGoalsRestored do
  runWhileGoals [
    ← `(tactic| try unfold win_lo),
    ← `(tactic| try rw [CatExec.stack_max_size_val]),
    ← `(tactic| try rw [length_N_to_le_bytes]),
    ← `(tactic| try rw [length_zeros]),
    ← `(tactic| try rw [repeat_length]),
    ← `(tactic| imm_norm),
    ← `(tactic| unorm),
    ← `(tactic| all_goals (first | omega | (left; omega) | (right; omega)))]

/-- Normalize the address of a load/store obligation. -/
macro "addr_norm" : tactic =>
  `(tactic|
    (gres
     pin
     imm_norm
     try rw [v_addi_0]
     try unfold v_addi
     try unfold v_add
     unorm
     zlit))

/-! =====================================================================
    Closing a value obligation ([vclose_fin], [vclose])
    ===================================================================== -/

/-- Value closer for `stepiv` with a caller-chosen value.
    `f_equal` is a Mathlib tactic (this tree has core Lean only), so the
    `f_equal; lia` arm is written `congr 1; omega`.
-/
macro "vclose_fin" : tactic =>
  `(tactic|
    first
    | rfl
    | (congr 1; omega)
    | exact at_self _
    | (symm; exact at_self _)
    | (apply Z_to_bv_u_eq <;> omega)
    | (apply Z_to_bv_u_eq_sym <;> omega)
    | bveq)

/-- The standard value closer: resolve the registers, fold the zero/`addi`
    arithmetic, then [vclose_fin].
-/
macro "vclose" : tactic =>
  `(tactic|
    (gres
     pin
     imm_norm
     (first
      | rfl
      | (try unfold v_addi; try unfold v_add; unorm; zlit; vclose_fin)
      | ((try rw [v_addi_0]); (try rw [v_add_0_r]); (try rw [v_add_0_l])
         (first | rfl | vclose_fin))
      | ((try rw [v_addi_0]); (try rw [v_add_0_r]); (try rw [v_add_0_l])
         (try unfold v_addi); (try unfold v_add); unorm; zlit; vclose_fin))))

/-- ALU step: automatic value (`stepn`) + `pin`. -/
macro "sn " F:term "," D:term : tactic =>
  `(tactic| (stepn $F, $D; pin))

/-- ALU step with the written value stated by the caller (`stepiv`) and the
    standard value closer.
-/
macro "sv " F:term "," D:term "," v:term : tactic =>
  `(tactic| stepiv $F, $D, $v, (by vclose))

/-! =====================================================================
    Stores into the described memory ([blit], [push_store], [stw])
    ===================================================================== -/

/-- the byte an `sb` of a 64-bit literal value leaves,
    folded into the `Z_to_bv 8 z` spelling: `Z_to_bv 8 (bv_unsigned
    (Z_to_bv 64 z)) = Z_to_bv 8 z` (the low byte depends only on `z mod
    256`, and `256 ∣ 2^64`).
-/
theorem blit_byte (z : Int) :
    BitVec.ofInt 8 (((BitVec.ofInt 64 z).toNat : Int)) = BitVec.ofInt 8 z := by
  have h1 : (((BitVec.ofInt 64 z).toNat : Int)) = z % ((2 ^ 64 : Nat) : Int) :=
    toNat_ofInt_emod' z
  have h2 : (z % ((2 ^ 64 : Nat) : Int)) % ((2 ^ 8 : Nat) : Int)
      = z % ((2 ^ 8 : Nat) : Int) :=
    Int.emod_emod_of_dvd z ⟨((2 ^ 56 : Nat) : Int), by decide⟩
  apply BitVec.eq_of_toNat_eq
  rw [h1, BitVec.toNat_ofInt, BitVec.toNat_ofInt, h2]

/-- Normalize the byte an `sb` of a literal leaves: `Z_to_bv 8 (bv_unsigned
    (Z_to_bv 64 z))`.
-/
macro "blit" : tactic => `(tactic| repeat (rw [blit_byte]))

/-- Push a store into the right region of `cmem`.
 `idtac` is the third arm. -/
elab "push_store" : tactic => withGoalsRestored do
  Lean.Elab.Tactic.evalTactic (← `(tactic| blit))
  let sideTac ← `(tactic| region_side)
  let winTac ← `(tactic| rw [wbytes_cmem_win])
  let dataTac ← `(tactic| rw [wbytes_cmem_data])
  if (← Lean.Elab.Tactic.getGoals).isEmpty then return ()
  let g ← Lean.Elab.Tactic.getMainGoal
  if ← sidesClose g winTac sideTac then
    commitRewrite sideTac winTac
  else if ← sidesClose g dataTac sideTac then
    commitRewrite sideTac dataTac
  else pure ()

/-- the constant application `Instr.<n> …` inside a decode
    hypothesis's type (this tree's replacement for `lazymatch type of D`, see
    -/
private partial def findConstApp (n : Lean.Name) : Lean.Expr → Option (Array Lean.Expr)
  | e =>
    if e.getAppFn.isConstOf n then some e.getAppArgs
    else
      match e with
      | .app f a => findConstApp n f <|> findConstApp n a
      | .lam _ d b _ => findConstApp n d <|> findConstApp n b
      | .forallE _ d b _ => findConstApp n d <|> findConstApp n b
      | .letE _ t v b _ => findConstApp n t <|> findConstApp n v <|> findConstApp n b
      | .mdata _ b => findConstApp n b
      | .proj _ _ b => findConstApp n b
      | _ => none

/-- the `MSize` a decode hypothesis is about (`SZ1`/`SZ2`/`SZ4`/
    `SZ8`), read off the constants its type mentions. -/
private def msizeOf (D : Lean.Expr) (ctor : Lean.Name) : Lean.MetaM (Option Lean.Name) := do
  let ty ← Lean.Meta.inferType D
  let some args := findConstApp ctor ty | return none
  unless 1 ≤ args.size do return none
  let sz := args[0]!.getAppFn
  if sz.isConstOf ``MSize.SZ1 then return some ``MSize.SZ1
  else if sz.isConstOf ``MSize.SZ2 then return some ``MSize.SZ2
  else if sz.isConstOf ``MSize.SZ4 then return some ``MSize.SZ4
  else if sz.isConstOf ``MSize.SZ8 then return some ``MSize.SZ8
  else return none

/-- is the `Instr.load` a decode hypothesis is about SIGNED?
    (`Instr.load sz signed …`; the `false`/`true` are `Bool` constructors in
    the elaborated term). -/
private def loadSignedOf (D : Lean.Expr) : Lean.MetaM (Option Bool) := do
  let ty ← Lean.Meta.inferType D
  let some args := findConstApp ``LinuxSem.Riscv.Instr.load ty | return none
  unless 2 ≤ args.size do return none
  return some (args[1]!.isConstOf ``Bool.true)

/-- (shared with `Common/SumsLib.lean`): one instruction step
    inside the chain relation.

    `chain_step` leaves the `ms_svc_pending` premise, the step equation and
    the chain continuation — PLUS a goal for the target state's metavariable
    (Lean's `apply` publishes a metavariable of non-`Prop` type as a goal).
 [stepTac] closes
    the step's own premises; [contTac] runs on the continuation.  Each focus
    goes through `Lean.Elab.Tactic.run`, which leaves the ambient goal list
    alone (and the solved target metavariable's goal is dropped). -/
def chainStepWith (stepTac contTac : Lean.Syntax) : Lean.Elab.Tactic.TacticM Unit :=
    withGoalsRestored do
  Lean.Elab.Tactic.evalTactic (← `(tactic| chain_step))
  let gs ← Lean.Elab.Tactic.getGoals
  let some svcG := gs.head? | throwError "chain step: goal 1 (ms_svc_pending) is missing"
  let some stepG := gs.tail.head?
    | throwError "chain step: goal 2 (the step equation) is missing"
  let rest := gs.tail.tail
  let _ ← Lean.Elab.Tactic.run svcG
    (Lean.Elab.Tactic.evalTactic (← `(tactic| first | rfl | assumption)))
  let leftStep ← Lean.Elab.Tactic.run stepG (Lean.Elab.Tactic.evalTactic stepTac)
  let rest ← rest.filterM fun g => return !(← g.isAssigned)
  let mut contLeft : List Lean.MVarId := []
  let mut more : List Lean.MVarId := rest
  match rest with
  | [] => pure ()
  | contG :: tl =>
    contLeft ← Lean.Elab.Tactic.run contG (Lean.Elab.Tactic.evalTactic contTac)
    more := tl
  let moreF ← more.filterM fun g => return !(← g.isAssigned)
  Lean.Elab.Tactic.setGoals (leftStep ++ contLeft ++ moreF)

/-- A store with the caller's address `aa` and value `vv`; `oktac` proves
    the `store_ok` obligation.
 `oktac` is a
    `tacticSeq` because  splices it as one bullet. -/
elab "stw " F:term "," D:term "," aa:term "," vv:term "," oktac:tacticSeq : tactic =>
    withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some sz ← msizeOf Dexp ``LinuxSem.Riscv.Instr.store
    | throwError "stw: {D} does not look like a decoded store"
  let lemName ←
    if sz == ``MSize.SZ8 then pure ``step_sd_at
    else if sz == ``MSize.SZ4 then pure ``step_sw_at
    else if sz == ``MSize.SZ2 then pure ``step_sh_at
    else pure ``MmapSim.step_sb_at
  let head := Lean.mkIdent lemName
  let stepTac ←
    if lemName == ``MmapSim.step_sb_at then
      `(tactic|
        refine $head _ _ _ _ _ _ _ _ _ $aa $vv ?_ $F ?_ $D ?_ ?_ ?_ ?_ <;>
          (first | decide_closed | $oktac | rfl | assumption | vclose))
    else
      `(tactic|
        refine $head _ _ _ _ _ _ _ _ _ $aa $vv $F ?_ $D ?_ ?_ ?_ <;>
          (first | decide_closed | $oktac | rfl | assumption | vclose))
  chainStepWith stepTac (← `(tactic| (step_simpl; push_store)))

/-- Store bound inside a region already known writable as a whole
    (`Hok : store_ok segs m lo N = true`), through any `wbytes` layers.
 The
    bullets leave three arithmetic premises, closed together; the
    `?`-rewrites become `try rw` and `lia` becomes `omega`. -/
macro "ok_sub " Hok:term : tactic =>
  `(tactic|
    (store_ok_peel
     apply store_ok_sub (Hok := $Hok)
     all_goals (try rw [length_N_to_le_bytes]
                try rw [length_zeros]
                unorm)
     all_goals omega))

/-- Store bound in the `cmem` window: peel the explicit `wbytes` layers of
    `J` with `wfJ_wbytes` down to the hypothesis `HJ : wfJ sp0 J`.
 The three bullets are one
    `first` list here (the house pattern): each of the three premises is
    closed by its own script, and only one script applies to each. -/
macro "ok_win " HJ:term : tactic =>
  `(tactic|
    (apply store_ok_cmem_win
     · repeat (apply wfJ_wbytes)
       exact $HJ
     · region_side
     · region_side))

/-- Store bound in a writable segment (closed address).
-/
macro "ok_data" : tactic =>
  `(tactic| (apply store_ok_cmem_data; first | rfl | decide_closed))

/-! =====================================================================
    Loads ([ld_step], [lb_step]) and reading back the described memory
    ===================================================================== -/

/-- A load: `bsv`/`vv` stated by the caller, `rdtac` proves the `rdn` fact
    (after `addr_norm`), `valtac` the `bytes_le_to_Z bs = bv_unsigned v`
    equation.

    the decode-shape dispatch (five `Instr.load` arms distinguished by
    size and signedness) is a real dispatch (-/
elab "ld_step " F:term "," D:term "," bsv:term "," vv:term "," rdtac:tactic "," valtac:tacticSeq :
    tactic => withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some sz ← msizeOf Dexp ``LinuxSem.Riscv.Instr.load
    | throwError "ld_step: {D} does not look like a decoded load"
  let some signed ← loadSignedOf Dexp
    | throwError "ld_step: cannot read the signedness of {D}"
  let lemName ←
    if sz == ``MSize.SZ8 then pure ``step_ld
    else if sz == ``MSize.SZ4 then pure (if signed then ``step_lw else ``step_lwu)
    else if sz == ``MSize.SZ2 then pure (if signed then ``step_lh else ``step_lhu)
    else throwError "ld_step: {D} is a byte load (use lb_step)"
  let head := Lean.mkIdent lemName
  let stepTac ← `(tactic|
    refine $head _ _ _ _ _ _ _ _ _ $bsv $vv $F ?_ $D ?_ ?_ <;>
      (first
       | decide_closed
       | assumption
       | (addr_norm; $rdtac)
       | $valtac))
  chainStepWith stepTac (← `(tactic| (step_simpl; vnorm; pin)))

/-- Byte loads (`lbu`/`lb`): the byte `b` stated by the caller.
-/
elab "lb_step " F:term "," D:term "," bb:term "," rdtac:tactic : tactic =>
    withGoalsRestored do
  let Dexp ← Lean.instantiateMVars (← Lean.Elab.Term.elabTerm D none)
  let some sz ← msizeOf Dexp ``LinuxSem.Riscv.Instr.load
    | throwError "lb_step: {D} does not look like a decoded load"
  unless sz == ``MSize.SZ1 do
    throwError "lb_step: {D} is not a byte load"
  let some signed ← loadSignedOf Dexp
    | throwError "lb_step: cannot read the signedness of {D}"
  let lemName := if signed then ``step_lb else ``step_lbu
  let head := Lean.mkIdent lemName
  let stepTac ← `(tactic|
    refine $head _ _ _ _ _ _ _ _ _ $bb $F ?_ $D ?_ <;>
      (first
       | decide_closed
       | assumption
       | (addr_norm; $rdtac)))
  chainStepWith stepTac (← `(tactic| (step_simpl; vnorm; pin)))

/-- Peel non-overlapping `wbytes` layers off an `rdn` goal.
-/
elab "peel" : tactic => withGoalsRestored do
  let sideTac ← `(tactic| region_side)
  let rwTac ← `(tactic| rw [rdn_wbytes_out])
  for _ in [0:16] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then break
    let g ← Lean.Elab.Tactic.getMainGoal
    unless ← sidesClose g rwTac sideTac do break
    commitRewrite sideTac rwTac

/-- Read an image constant through `cmem`'s data region: `L` is an `img_*`
    lemma over the empty overlay.
-/
elab "rd_img " L:term : tactic => withGoalsRestored do
  Lean.Elab.Tactic.evalTactic (← `(tactic| addr_norm))
  let sideTac ← `(tactic| region_side)
  let rwTac ← `(tactic| rw [rdn_cmem_data])
  let g ← Lean.Elab.Tactic.getMainGoal
  unless ← sidesClose g rwTac sideTac do
    throwError "rd_img: the read is not in the data region of `cmem`"
  commitRewrite sideTac rwTac
  Lean.Elab.Tactic.evalTactic (← `(tactic| peel))
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact $L))

/-- for [rd_hit8]: the same read-back as
    `SeqExec.rdn_wbytes_hit8`, with the slot address and the read address
    tied by an explicit equation —  `replace a with a' by (first
    [f_equal; lia | bveq])` step, stated once as a lemma. -/
theorem rdn_wbytes_hit8_of_eq (segs : List Segment) (m : word → Option byte)
    (a a' v : word) (H : a = a')
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m a' (word_to_le_bytes 8 v)) a 8 = some (word_to_le_bytes 8 v) := by
  subst H
  exact rdn_wbytes_hit8 segs m a v Hnw

/-- An exact 8-byte read-back of a slot written earlier in the chain.
 In Lean the two addresses are
    either the same term up to conversion — which `apply` unifies on its own
    — or they are related by `bveq`-level arithmetic, which is exactly what
    [rdn_wbytes_hit8_of_eq]'s equation premise asks for. -/
macro "rd_hit8" : tactic =>
  `(tactic|
    (addr_norm
     peel
     first
     | (apply rdn_wbytes_hit8 <;> (unorm; omega))
     | (apply rdn_wbytes_hit8_of_eq <;> (first | bveq | (unorm; omega)))))

/-! =====================================================================
    `regs_agree` bookkeeping
    ===================================================================== -/

/-- the set expression of a goal `C r` (or `¬ C r`), and its head
    constant if it is one — this tree's reading of  `cbn [In]`,
    which computes the membership of a literal register list.
-/
private def setHeadOf (e : Lean.Expr) : Option Lean.Name :=
  let e := match e with
    | .app (.const ``Not _) a => a
    | _ => e
  match e.getAppFn with
  | .const c _ => some c
  | _ => none

/-- Membership in the goal's register set, by computation.
 This tree's sets are
    predicates, so the same computation is `simp only [set]` (unfold the
    clobber-set definition) followed by `decide` — the same kernel-checked
    certificate, on the same closed goal. -/
elab "in_list" : tactic => withGoalsRestored do
  let target ← Lean.Elab.Tactic.getMainTarget
  let tac ← match setHeadOf target with
    | some c =>
      let id := Lean.mkIdent c
      `(tactic|
        (first
         | (simp only [$id:term]; decide)
         | (dsimp only; decide)
         | decide
         | assumption))
    | none => `(tactic| (first | (dsimp only; decide) | decide | assumption))
  Lean.Elab.Tactic.evalTactic tac

/-- Non-membership in the goal's register set, by computation. -/
elab "notin_list" : tactic => withGoalsRestored do
  let target ← Lean.Elab.Tactic.getMainTarget
  let tac ← match setHeadOf target with
    | some c =>
      let id := Lean.mkIdent c
      `(tactic|
        (first
         | (simp only [$id:term]; decide)
         | (dsimp only; decide)
         | decide
         | (intro h; exact absurd h (by decide))))
    | none => `(tactic| (first | (dsimp only; decide) | decide))
  Lean.Elab.Tactic.evalTactic tac

/-- `regs_agree` for a final `regupd` chain. -/
macro "solve_regs_agree" : tactic =>
  `(tactic|
    (repeat (apply regs_agree_upd <;> (first | in_list | skip))
     apply regs_agree_refl))

/-- `regs_agree` weakening between register lists, decided by computation.
    The sets are `reg → Prop`, and the same goal over a FINITE register
    type (`reg` = `BitVec 5`) is decidable once the two set definitions are
    unfolded, so `simp only [C, C']; decide` is the same fact, decided
    rather than destructed. -/
elab "incl_list" : tactic => withGoalsRestored do
  let target ← Lean.Elab.Tactic.getMainTarget
  let core := match target with
    | .forallE _ _ body _ => body
    | _ => target
  let dom? := match core with
    | .forallE _ d _ _ => setHeadOf d
    | _ => none
  let cod? := match core with
    | .forallE _ _ c _ => setHeadOf c
    | _ => none
  let tac ←
    match dom?, cod? with
    | some cd, some cc =>
      let idd := Lean.mkIdent cd
      let idc := Lean.mkIdent cc
      `(tactic|
        (first
         | (simp only [$idd:term, $idc:term]; decide)
         | (dsimp only; decide)
         | (intro r hr
            simp only [$idd:term] at hr
            simp only [$idc:term]
            first | assumption | (simp_all))))
    | _, some cc =>
      let idc := Lean.mkIdent cc
      `(tactic|
        (first
         | (simp only [$idc:term]; decide)
         | (dsimp only; decide)
         | (intro r hr
            simp only [$idc:term]
            first | assumption | (simp_all))))
    | some cd, none =>
      let idd := Lean.mkIdent cd
      `(tactic|
        (first
         | (simp only [$idd:term]; decide)
         | (dsimp only; decide)
         | (intro r hr
            simp only [$idd:term] at hr
            first | assumption | (simp_all))))
    | none, none =>
      `(tactic|
        (first
         | (dsimp only; decide)
         | (intro r hr; first | assumption | simp_all)))
  Lean.Elab.Tactic.evalTactic tac

/-- `regs_agree` weakening through a hypothesis `Hag`. -/
macro "regs_agree_weaken " Hag:term : tactic =>
  `(tactic| (apply regs_agree_mono (H := $Hag); incl_list))

/-- Transport a register fact `H : getr regs r = v` across `Hag : regs_agree
    C regs regs'` (`r` not in `C`), naming it `T`; then resolve the `getr`
    chain in `T` and fold `H` into it.
 `pose proof … as T` becomes a
    `have` whose type is filled in by the proof term (the two `_` in
    `getr _ r = getr _ r`), and the `repeat` becomes a `repeat` over the two
    `rw … at T` arms (a `rw` at a hypothesis fails over when it does not
    apply, so the loop terminates). -/
macro "carry " Hag:term "," H:term "," r:term "," T:ident : tactic =>
  `(tactic|
    (have $T : getr _ $r = getr _ $r := $Hag $r (by notin_list)
     repeat (first
       | rw [getr_same _ _ _ (by reg_neq_tac)] at $T:ident
       | rw [getr_other _ _ _ _ (by reg_neq_tac)] at $T:ident
       | rw [getr_zero] at $T:ident)
     try (rw [$H:term] at $T:ident)))

/-- `regs_agree C regs regs'` where `regs'` is reached from `regs` by a mix
    of explicit `regupd`s and abstract hops justified by hypotheses
    `Hag : regs_agree C' _ regsK` (with `C'` included in `C`).  Works from
    the target backwards, so no evar is ever left as a target.
 The recursion is a bounded (12-pass) `iterate` for
    the reason StepTac's `u_norm` is bounded: an unbounded `repeat` whose
    last arm always succeeds would not terminate. -/
macro "ra_chain" : tactic =>
  `(tactic|
    (iterate 12
      (first
       | exact regs_agree_refl _ _
       | (apply regs_agree_upd <;> (first | in_list | skip))
       | (apply regs_agree_trans <;>
           (first
            | (apply regs_agree_mono <;> (first | incl_list | assumption))
            | skip))
       | skip)))

/-! =====================================================================
    Goal transformers closed under backward `msteps`
    ===================================================================== -/

/-- Summaries are stated for an arbitrary goal `G` on machine states that
    can absorb instruction steps in front (`bwd`): both "`msteps` to a fixed
    target" and "`realizes_f` under a fixed model/shape" are such.  This is
    continuation-passing without the evar-scoping problem of a fixed
    `msteps` target. -/
def bwd (segs : List Segment) (G : machine_state → Prop) : Prop :=
  ∀ st st' : machine_state, msteps segs st st' → G st' → G st

/-- "`msteps` to a fixed target" is closed under backward steps. -/
theorem bwd_msteps (segs : List Segment) (tgt : machine_state) :
    bwd segs (fun st => msteps segs st tgt) := by
  intro st st' H1 H2
  exact msteps_trans segs st st' tgt H1 H2

/-- Start stepping inside a `G`-goal: leaves an `msteps` goal with an evar
    target (close it with `apply msteps.mst_refl` when done) and the `G`-goal
    at the reached state.
-/
macro "gsteps " HG:term : tactic => `(tactic| apply $HG)

/-! =====================================================================
    Smoke tests

    One call site per tactic whose effect is checkable without a code image:
    a macro that is never expanded is not a macro that works (an argument
    mismatch only surfaces when the arm FIRES), so — exactly as WalkTac's
    test section does — each of the stated tactics is exercised once here. -/

/-- `pin` folds a register hypothesis into the goal. -/
example (regs : BvMap word) (v : word) (H : getr regs 8 = v) :
    v_add (getr regs 8) (BitVec.ofInt 64 0) = v := by
  pin
  rw [v_add_0_r]

/-- `unorm` collapses the `bv_unsigned (Z_to_bv 64 z)` projection and leaves
    its two range side conditions to the caller's arithmetic closer. -/
example (z : Int) (h0 : 0 ≤ z) (h1 : z < ((2 ^ 64 : Nat) : Int)) (a : Int) :
    ((BitVec.ofInt 64 z).toNat : Int) + a = z + a := by
  unorm
  all_goals omega

/-- `zlit` and `imm_norm` are total (documented no-ops). -/
example (z : Int) : BitVec.ofInt 64 z = BitVec.ofInt 64 z := by
  zlit
  imm_norm
  rfl

/-- `blit` folds the byte of a 64-bit literal. -/
example : BitVec.ofInt 8 (((BitVec.ofInt 64 0x1234).toNat : Int)) = BitVec.ofInt 8 0x34 := by
  blit
  decide

/-- `region_side` closes the two range side conditions of the window store
    lemma at a literal stack pointer. -/
example : win_lo (BitVec.ofInt 64 0x10000000) ≤
    ((BitVec.ofInt 64 (0x10000000 - 8)).toNat : Int) := by
  region_side

/-- `vclose_fin` closes the `at_` form of a value. -/
example (a : word) : BitVec.ofInt 64 ((a.toNat : Int) + 0) = a := by
  vclose_fin

/-- `in_list` on a clobber set: membership of a literal register. -/
private def smoke_clob : regset := fun r => r = 8 ∨ r = 9 ∨ r = 10

example : smoke_clob 9 := by in_list
example : ¬ smoke_clob 11 := by notin_list
example : ∀ r : reg, (fun x : reg => x = 8 ∨ x = 9) r → smoke_clob r := by incl_list

/-- `solve_regs_agree` on a two-update chain. -/
example (regs : BvMap word) (v w : word) :
    regs_agree smoke_clob regs (regupd (regupd regs 8 v) 9 w) := by
  solve_regs_agree

/-- `regs_agree_weaken` between two clobber sets. -/
example (regs regs' : BvMap word)
    (H : regs_agree (fun r : reg => r = 8 ∨ r = 9) regs regs') :
    regs_agree smoke_clob regs regs' := by
  regs_agree_weaken H

/-- `carry` transports one register fact across an agreement hypothesis. -/
example (regs regs' : BvMap word) (v : word)
    (Hag : regs_agree smoke_clob regs regs') (H : getr regs 11 = v) :
    getr regs' 11 = v := by
  carry Hag, H, 11, T
  exact T

/-- `ra_chain` chains a `regupd` and an abstract hop. -/
example (regs regs' : BvMap word) (v : word)
    (Hag : regs_agree smoke_clob regs regs') :
    regs_agree smoke_clob regs (regupd regs' 8 v) := by
  ra_chain

/-- `sn` (WalkTac's `stepn` + `pin`) on `addi x8, x9, 0` (`0x00090413`). -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00090413 : BitVec 32))
    (Hd : decodeAny (0x00090413 : BitVec 32) = some (Instr.opImm .ADD 8 9 0, 4)) :
    msteps segs (mkst regs pc mem rom)
      (mkst (if bv_eqb (n := 5) 8 0 = true then regs
             else regupd regs 8 (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))))
        (v_addi pc 4) mem rom) := by
  sn Hf, Hd
  exact msteps.mst_refl _

/-- `sv` (StepTac's `stepiv` + `vclose`) on the same instruction. -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00090413 : BitVec 32))
    (Hd : decodeAny (0x00090413 : BitVec 32) = some (Instr.opImm .ADD 8 9 0, 4)) :
    msteps segs (mkst regs pc mem rom)
      (mkst (regupd regs 8 (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))))
        (v_addi pc 4) mem rom) := by
  sv Hf, Hd, v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))
  exact msteps.mst_refl _

/-- `stw` on `sd x8, 0(x9)` (`0x0084B023`), with the address and value
    supplied by the caller. -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x0084B023 : BitVec 32))
    (Hd : decodeAny (0x0084B023 : BitVec 32) = some (Instr.store .SZ8 9 8 0, 4))
    (Hok : store_ok segs mem
      (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))) 8 = true) :
    msteps segs (mkst regs pc mem rom)
      (mkst regs (v_addi pc 4)
        (wbytes mem (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12)))
          (word_to_le_bytes 8 (getr regs 8))) rom) := by
  stw Hf, Hd, v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12)), getr regs 8, exact Hok
  exact msteps.mst_refl _

/-- `stw` dispatches on the SIZE in the decode hypothesis: the same script on
    `sb` (`0x00948023`, `sb x9, 0(x9)`'s `SZ1` arm) reaches
    `MmapSim.step_sb_at`. -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x00848023 : BitVec 32))
    (Hd : decodeAny (0x00848023 : BitVec 32) = some (Instr.store .SZ1 9 8 0, 4))
    (Hok : store_ok segs mem
      (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))) 1 = true) :
    msteps segs (mkst regs pc mem rom)
      (mkst regs (v_addi pc 4)
        (LinuxSem.Common.MmapSim.wbytes mem
          (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12)))
          [BitVec.ofInt 8 ((getr regs 8).toNat : Int)]) rom) := by
  stw Hf, Hd, v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12)), getr regs 8, exact Hok
  exact msteps.mst_refl _

/-- `ld_step` on `ld x8, 0(x9)` (`0x0004B403`). -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x0004B403 : BitVec 32))
    (Hd : decodeAny (0x0004B403 : BitVec 32) = some (Instr.load .SZ8 true 8 9 0, 4))
    (Hr : rdn segs mem (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))) 8
            = some (word_to_le_bytes 8 (getr regs 9))) :
    msteps segs (mkst regs pc mem rom)
      (mkst (regupd regs 8 (getr regs 9)) (v_addi pc 4) mem rom) := by
  ld_step Hf, Hd, word_to_le_bytes 8 (getr regs 9), getr regs 9,
    exact Hr, exact bytes_le_to_Z_8 _
  exact msteps.mst_refl _

/-- `lb_step` on `lbu x8, 0(x9)` (`0x0004C403`). -/
example (segs : List Segment) (regs : BvMap word) (pc : word)
    (mem rom : word → Option byte)
    (Hf : fetch_word segs pc = some (0x0004C403 : BitVec 32))
    (Hd : decodeAny (0x0004C403 : BitVec 32) = some (Instr.load .SZ1 false 8 9 0, 4))
    (Hr : rdn segs mem (v_addi (getr regs 9) (BitVec.toInt (0 : BitVec 12))) 1
            = some [BitVec.ofInt 8 7]) :
    msteps segs (mkst regs pc mem rom)
      (mkst (regupd regs 8 (BitVec.ofInt 64 7)) (v_addi pc 4) mem rom) := by
  lb_step Hf, Hd, BitVec.ofInt 8 7, exact Hr
  exact msteps.mst_refl _

/-- `ok_win`: the window bound of a store 8 bytes below a stack pointer that
    is known to be at least 8 bytes above the bottom. -/
example (segs : List Segment) (sp0 : word) (mem0 J D : word → Option byte)
    (HJ : wfJ sp0 J) (Hsp : 8 ≤ (sp0.toNat : Int)) :
    store_ok segs (cmem sp0 mem0 J D)
      (BitVec.ofInt 64 ((sp0.toNat : Int) - 8)) 8 = true := by
  ok_win HJ

/-- `ok_sub`: a sub-range of a region already known writable, through one
    `wbytes` layer. -/
example (segs : List Segment) (m : word → Option byte) (sp0 : word)
    (Hnw : (sp0.toNat : Int) + 16 ≤ ((2 ^ 64 : Nat) : Int))
    (Hok : store_ok segs m sp0 16 = true) :
    store_ok segs (wbytes m sp0 (word_to_le_bytes 8 0))
      (BitVec.ofInt 64 ((sp0.toNat : Int) + 8)) 8 = true := by
  ok_sub Hok

/-- `rd_hit8`: the 8-byte read-back of a slot written in the chain (the
    read address is the `v_addi … 0` normal form `addr_norm` produces). -/
example (segs : List Segment) (m : word → Option byte) (a : word) (v : word)
    (Hnw : (a.toNat : Int) + 8 ≤ ((2 ^ 64 : Nat) : Int)) :
    rdn segs (wbytes m a (word_to_le_bytes 8 v)) (v_addi a 0) 8
      = some (word_to_le_bytes 8 v) := by
  rd_hit8

/-- `bwd_msteps` is the "fixed target" instance of `bwd`. -/
example (segs : List Segment) (st : machine_state) :
    bwd segs (fun s => msteps segs s st) :=
  bwd_msteps segs st

/-- `gsteps` opens a `bwd` goal, leaving the `msteps` evar target. -/
example (segs : List Segment) (st : machine_state) (G : machine_state → Prop)
    (HG : bwd segs G) (h : G st) : G st := by
  gsteps HG
  exact msteps.mst_refl _
  exact h

end LinuxSem.Common.StartupTac
