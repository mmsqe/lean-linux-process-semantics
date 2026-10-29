/-
  * Common.LiaFast — build-time hygiene for `lia`/`nia` in large proof contexts.
 A symbolic-execution proof context holds hundreds of memory facts
    ([rdn .. = Some ..], [cell], register equations, [Forall] over images)
    that arithmetic can never use.  Every `omega` goal additionally pays for
    the hypotheses around it, and the tactics below exist to cut that
    preprocessing down: it can take most of a file's compile time.
    WHAT (all OPT-IN; nothing here changes the meaning of [lia] for a file
    that merely [Require]s this module):
    - [lia_mod] / [nia_mod]: [lia]/[nia] with the euclidean-division
      preprocessing forced on ([Z.to_euclidean_division_equations] first) —
      for the few goals that need a division fact in a file that switched the
      flag off.
    - [prune_arith_ctx]: ONE Ltac2 [Std.keep] of the hypotheses whose
      statement is built from [/\ \/ ~ <-> ->] over arithmetic atoms
      ([=] at Z/nat/N/positive/bool, orders on Z/nat/N, [Z.divide], [True],
      [False]) plus let-bound definitions; everything else goes, together
      with the variables only it mentioned.  [alia] := prune, then [lia];
      [ania] := prune, then [nia].  Use them only where the arithmetic call
      is TERMINAL for the goal.
    - [flia_prune1]: a single-pass pruner (visits every hypothesis once,
      [clear]s the non-arithmetic ones, never touches a kept one, so the
      proof term references exactly what [lia] would reference — see the
      capture note below); [flia_lin]: for goals WITHOUT div/mod, also drops
      every hypothesis mentioning them and skips the euclidean pass
      entirely; [flia_full1]: full [lia] in the pruned context; [flia2] :=
      linear attempt first, then full — proves everything std [lia] proves
      from the kept hypotheses, usually much cheaper; [flia1]: the two-stage
      variant that drops [_ mod _ = 0] facts unless the goal mentions
      mod/div.
    - [clia]: the closed-goal shortcut — a goal that mentions no variable is
      first tried in the EMPTY context (no hypothesis preprocessing at all),
      then as plain [lia]; a goal with a variable takes the plain path
      directly.  [zlit]: closed literal (in)equalities decided by
      [vm_compute], never by zify.  [plia] := [zlit] else [alia].
    - [solve_BvWf_fast]: the well-formedness side goal [BvWf n z] of a
      bit-vector literal ([(10 : reg)], [3%bv]) decided by [vm_compute]
      directly when both arguments are closed; the context-clearing form
      below costs 0.1-0.5 s per literal in a big-context walk.
      Same proof term.  Registered with [#[export]] at cost 9 , so it is active exactly in the files that [Import] this module.
    HOW TO OPT IN (per file, after its last [Require].  A NON-[Local]
    [Ltac x ::= ...] takes effect in every file that merely [Require]s the
    module, and lia variants are NOT capture-neutral inside Sections — the
    hypotheses a lemma ends up depending on are the ones the certificate
    used — so any rebinding MUST be [Local]):
        From LinuxSem.Common Require Import LiaFast.
        Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
        Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        (* and, if a file's div/mod goals are only over literal divisors: *)
        Local Ltac Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup ::= idtac.
    After converting a file, recompile its importers: a lemma proved with a
    pruning variant may reference a different set of Section hypotheses than
    before.  If a file's lemmas are applied with explicit argument lists
    elsewhere, leave that file alone or fix the importers.
    Depends on Stdlib + Ltac2 + [BvBase] (for [BvWf]) only.
  ---------------------------------------------------------------------
  NOTES (see the tactic-fidelity section of `Common/StepTac.lean`)
  ---------------------------------------------------------------------
  The  file is a pure TACTIC library plus a self-test module: there
  is no definition, lemma or theorem in it.  So the content of this module is
  the tactic layer, and each  `Ltac`/`Ltac2` function becomes a Lean
  `macro`/`elab` of the same name .  The self-tests at the end are stated as `example`s.
= Some ..`, `cell`, `Forall` over images) that `lia` can never
    use, so the preprocessing has less to chew on, and to make the resulting
    proof term depend on exactly the arithmetic hypotheses.
  Lean's `omega` has no zify phase and no per-file flags: it collects the
  hypotheses it can use, in one pass, and never looks at a hypothesis whose
  head it does not recognize.  Consequence: the PRUNERS are still
  meaningful here (a smaller local context is cheaper to traverse, and it
  keeps the proof term's hypotheses explicit), while the DIVISION-KNOB
  tactics (`lia_mod`, `flia1`'s two stages, `flia_lin`'s skip) have less to
  do: `omega` handles `Int.emod`/`Int.ediv` itself, with no switch.
  The banner's HOW TO OPT IN block therefore has NO Lean counterpart: there
  is no global `lia` to rebind and no per-file flag to switch, and importing
  this module changes no tactic's meaning.  A Lean file opts in by NAMING
  the variant it wants (`flia2`, `alia`, `plia`, `lia_mod`, …) at the point
  where the arithmetic call is terminal for the goal.
  **(b) What each  tactic became** (the full table):
  |  | here |
  | --- | --- |
  | `lia_mod` | `macro`, real: `omega` (its div/mod handling is built in; see (a)) |
  | `nia_mod` | `macro`, PARTIAL: `omega` — core Lean has no nonlinear integer procedure.  This tree keeps both; a file that opens both
  namespaces gets the last one opened (see the NAME NOTE at `zlit`).
  **(c) Deviations, each marked at the tactic**
  1.  Core Lean has `omega` (linear, with `Nat`/`Int` div/mod
     support) and no `nlinarith`/`ring` (those live in Mathlib, which this
     project does not depend on).  They FAIL (loudly, no partial state) on a goal that
     needs nonlinearity, so a downstream call site that hits one must pass a
     hand proof — the self-test for `ania` shows the shape
     (`Int.mul_self_lt_mul_self` here), and `nia_mod`'s docstring lists the
     core `Int` monotonicity lemmas that cover the usual cases.  There is no
     faithful rendering available in this toolchain.
  2. *`is_zlit`/`is_nlit`.*   decides "is this a Z/N literal
     expression?" by walking a fixed constructor list (`Z0`, `Zpos`, `Zneg`,
     `Z.pow`, `Z.add`, `Z.sub`, `Z.mul`, `Z.opp`, `Z.of_nat`, and `O`/`S`/
     `Nat.add` for the `nat` side).  Lean numerals are not a fixed
     constructor set (`2 ^ 17` is `HPow.hPow` through a typeclass, `-3` is
     `Neg.neg`, `20` is `OfNat.ofNat …` with an instance argument), and
     kernel reduction is total on CLOSED terms (it gets stuck on a variable
     instead of allocating).  The invariant the test protects —
     "both sides are computable with no variable and no evar" — is therefore
     spelled `¬ hasFVar ∧ ¬ hasMVar` here, i.e. the same closedness test the
     `check_closed_term` uses (`Common/StepTac.lean`).  `zlit` uses
     that test at its four literal arms.
  3. *`zlit`'s `ring` fallback.*  For a `Z` equality whose sides are not
     closed, the answer is a `ring` call.  Core Lean has no `ring`, so this
     tree falls back to `omega` — which covers the LINEAR identities `ring`
     is used for here (`x + 0 = x`, reassociation) but not the polynomial
     ones.  Nonlinear ring identities are consequently out of reach of
     `zlit`/`plia`; prove them by hand (the same limitation as (1)).
  4.  Lean keeps
     `GE.ge`/`GT.gt` as distinct constants, so this tree's order test accepts
     all four heads at `Int`/`Nat`.  That is the same set of goals.
  5.
  6.  The same thing is written here as a `first` list whose head is guarded by
     `lia_closed_has_var`; if the plain call fails on an open goal, the
     emptied-context arm is tried as well.  That arm can never prove a goal
     the plain call would not (an emptied context is a sub-context of the
     original, and `omega` is monotone in its hypotheses; and
     `lia_clear_all` cannot remove a variable the goal mentions), so the
     same goals are proved — only the attempt order differs.
  7.  The "capture-neutral" property that motivated `prune`'s
     single-pass, never-touch-a-kept-hypothesis discipline is therefore
     automatic here.
  **(d) House rules obeyed by the elabs below.**  Every `elab` that can fail
  is wrapped in `withGoalsRestored`, so a failing arm behaves like a failed
  tactic (see: `all_goals` clears the goal list before running its tactic,
  and an enclosing `first` would otherwise believe the goal was closed).
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import Lean
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.Common.StartupTac

namespace LinuxSem.Common.LiaFast

open Lean Elab Tactic
open LinuxSem.Common.StartupTac (withGoalsRestored)

set_option linter.unusedVariables false

/-! ## Shared helpers ()

    Small `Expr` utilities the shape tests and pruners below share. -/

/-- The two immediate subterms of a binary application whose head is the
    constant `n`, else `none` — the Lean form of 
    `lazymatch ty with | ?a /\ ?b => … end` head/arity test.

    Lean's `And`/`Or`/`Iff` take their two arguments directly, so
    no instance argument has to be skipped (unlike the order atoms, which go
    through `LE.le`/`LT.lt`). -/
private def binaryApp? (e : Expr) (n : Name) : Option (Expr × Expr) :=
  if e.isAppOfArity n 2 then
    let args := e.getAppArgs
    some (args[0]!, args[1]!)
  else
    none

/-- The two sides of a binary order atom at sort `α` (`a ≤ b`, `a < b`,
    `a ≥ b`, `a > b`), else `none`.

    the four heads are `LE.le`, `LT.lt`, `GE.ge`, `GT.gt`, each
    with shape `@Head α inst a b`, so the sides are arguments 2 and 3. -/
private def orderSidesAt? (e : Expr) (α : Name) : Option (Expr × Expr) :=
  if (e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 ||
      e.isAppOfArity ``GE.ge 4 || e.isAppOfArity ``GT.gt 4) &&
      e.getAppArgs[0]!.isConstOf α then
    let args := e.getAppArgs
    some (args[2]!, args[3]!)
  else
    none

/-- The two sides of an `Int` equality `a = b`, else `none`.

    this toolchain's `Expr.eq?` returns a different tuple shape
, so the `@Eq Int lhs rhs` application is
    destructured directly — the same approach as `eqSides?` in
    `Common/StartupTac.lean`. -/
private def intEqSides? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Eq 3 && e.getAppArgs[0]!.isConstOf ``Int then
    let args := e.getAppArgs
    some (args[1]!, args[2]!)
  else
    none

/-- `true` iff the expression mentions one of the constants `cs` anywhere.
 `HMod.hMod`/`HDiv.hDiv` are
    the SURFACE forms Lean prints for `x % y`/`x / y` at `Int` (the elaborated
    head of `x % 4` is `@HMod.hMod Int Int Int (@instHMod Int Int.instMod) x 4`,
    printed as `x % 4`), while `Int.emod`/`Int.ediv` are the defining
    functions; a hypothesis written with either is recognized. -/
private partial def mentionsConst (e : Expr) (cs : List Name) : Bool :=
  if e.isConst then
    cs.contains e.constName!
  else
    match e with
    | .app f a => mentionsConst f cs || mentionsConst a cs
    | .lam _ d b _ => mentionsConst d cs || mentionsConst b cs
    | .forallE _ d b _ => mentionsConst d cs || mentionsConst b cs
    | .letE _ t v b _ => mentionsConst t cs || mentionsConst v cs || mentionsConst b cs
    | .mdata _ b => mentionsConst b cs
    | .proj _ _ b => mentionsConst b cs
    | _ => false

/-- `true` iff the expression mentions `mod` or `div` at `Int` — the Lean
    form of  `context [Z.modulo _ _]` / `context [Z.div _ _]`
    tests (`flia1`, `flia_lin`) and of its `H : context [Z.modulo _ _] |- _`
    hypothesis pattern (`flia_lin`). -/
def mentionsDivMod (e : Expr) : Bool :=
  mentionsConst e [``HMod.hMod, ``HDiv.hDiv, ``Int.emod, ``Int.ediv]

/-- `true` iff the expression is the numeral `0` at `Int`.
-/
private def isZeroLit (e : Expr) : Bool :=
  match e with
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal 0))) _ => true
  | .app (.const ``Int.ofNat _) (.lit (.natVal 0)) => true
  | _ => false

/-- `true` iff the type is a hypothesis of the shape `(_ mod _ = 0)` at
    `Int` —  `H : (_ mod _ = 0)%Z`. -/
private def isModEqZero (ty : Expr) : Bool :=
  match ty with
  | .app (.app (.app (.const ``Eq _) (.const ``Int _)) lhs) rhs =>
      mentionsConst lhs [``HMod.hMod, ``Int.emod] && isZeroLit rhs
  | _ => false

/-- `true` iff the term is CLOSED as far as the evaluator is concerned: no
    local variable and no metavariable.
-/
def isClosedLit (e : Expr) : Bool := !e.hasFVar && !e.hasMVar

/-- Clear every local hypothesis whose declaration fails `keep`, keeping  every hypothesis that the goal or another
    hypothesis still depends on.
-/
private def clearHyps (keep : LocalDecl → Bool) (fixpoint : Bool) : TacticM Unit := do
  let mut g ← getMainGoal
  let mut progress := true
  while progress do
    progress := false
    let decl ← g.getDecl
    let hyps := decl.lctx.decls.toList.filterMap id |>.reverse
    for ldecl in hyps do
      unless ldecl.isImplementationDetail do
        unless keep ldecl do
          let cleared ← try
              let g' ← g.clear ldecl.fvarId
              g := g'
              pure true
            catch _ => pure false
          if cleared then progress := true
    if !fixpoint then progress := false
  replaceMainGoal [g]

/-! ## Division facts on demand -/

/-- `lia_mod := Z.to_euclidean_division_equations; lia`: `lia` with
    the div/mod preprocessing forced on.

    `omega`.  Lean's `omega` has no separate zify/euclidean phase —
    its `Int.emod`/`Int.ediv` handling is part of the decision procedure and
    is always on — so forcing the phase is a no-op and the tactic is the
    decision procedure itself.  It proves the division goals
    directly, e.g. `0 ≤ x → x % 4 = 0 → ∃ q, x = 4 * q` (witness `x / 4`)
    and `5 ≤ x → x % 8 = 0 → 1 ≤ x / 8`. -/
macro "lia_mod" : tactic => `(tactic| omega)

/-- `nia_mod := Z.to_euclidean_division_equations; nia`: `nia`
    likewise.

    PARTIAL — see Core Lean has no nonlinear integer
    decision procedure (no `nlinarith`, no Mathlib), so this is `omega`:
    `omega` with its div/mod handling, i.e.  There is no faithful rendering in this toolchain.
    WHAT A DOWNSTREAM CALL SITE SHOULD USE INSTEAD: an explicit proof.  For
    the shapes `nia` is reached for in this development, core Lean already
    has the monotonicity lemmas — e.g. `Int.mul_self_lt_mul_self`
    (`0 ≤ a → a < b → a * a < b * b`), `Int.mul_le_mul_of_nonneg_left`,
    `Int.mul_lt_mul_of_pos_right`, `Int.mul_pos` — and the nonlinear
    self-test below shows the pattern. -/
macro "nia_mod" : tactic => `(tactic| omega)

/-! -/

namespace LiaFastL2

/-- The `prune_arith_ctx` shape test: a statement built from connectives
    over arithmetic atoms.

    an `Expr → Bool` function .  The sorts are this tree's: `Z` and
    `N` are `Int` and `Nat`, `positive` is merged into `Nat` , and `bool` is `Bool`. -/
partial def arith_prop (ty : Expr) : Bool :=
  if let some (a, b) := binaryApp? ty ``And then
    arith_prop a && arith_prop b
  else if let some (a, b) := binaryApp? ty ``Or then
    arith_prop a && arith_prop b
  else if let some (a, b) := binaryApp? ty ``Iff then
    arith_prop a && arith_prop b
  else if ty.isAppOfArity ``Not 1 then
    arith_prop ty.getAppArgs[0]!
  else if ty.isArrow then
    arith_prop ty.bindingDomain! && arith_prop ty.bindingBody!
  else if ty.isConstOf ``True || ty.isConstOf ``False then
    true
  else if ty.isAppOfArity ``Eq 3 then
    -- `@eq Z/nat/bool`
    let α := ty.getAppArgs[0]!
    α.isConstOf ``Int || α.isConstOf ``Nat || α.isConstOf ``Bool
  else if ty.isAppOfArity ``Ne 3 then
    -- `a ≠ b` is `@Ne α a b` in Lean; has it under `~ _`
    let α := ty.getAppArgs[0]!
    α.isConstOf ``Int || α.isConstOf ``Nat || α.isConstOf ``Bool
  else
    -- orders at Z/nat/N (`LE.le`, `LT.lt`, `GE.ge`, `GT.gt`) and `Z.divide`
    (orderSidesAt? ty ``Int).isSome
      || (orderSidesAt? ty ``Nat).isSome
      || (ty.isAppOfArity ``Dvd.dvd 4 && ty.getAppArgs[0]!.isConstOf ``Int)

/-- Does a local declaration pass `prune_arith_ctx`'s shape test?
-/
def arith_hyp (h : LocalDecl) : Bool :=
  h.isLet || arith_prop h.type

/-- ONE `Std.keep`  of the arithmetic hypotheses; the
    variables they and the goal depend on stay automatically.

    `clearHyps` with `arith_hyp` as the keep test, run to fixpoint so
    the result is the dependency closure `clear - ids` computes. -/
def prune_arith_ctx1 : TacticM Unit :=
  clearHyps (keep := arith_hyp) (fixpoint := true)

/-- `prune_arith_ctx` per goal (the Ltac1 callers may hand us several goals,
    e.g. `rewrite .. by ..`).

     is `Control.enter prune_arith_ctx1`, i.e. "run it on the
    current goal"; a Lean `TacticM` body already acts on the main goal, so
    the only thing added is the house goal-list guard `withGoalsRestored`
    (`Common/StartupTac.lean`,). -/
def prune_arith_ctx0 : TacticM Unit :=
  withGoalsRestored prune_arith_ctx1

/-- The `prune` shape test (kept whole conjunctions, bare sort hypotheses).

    an `Expr → Bool` function, like `arith_prop`. -/
partial def is_arith (t : Expr) : Bool :=
  (binaryApp? t ``And).isSome                    -- _ /\ _
  || (binaryApp? t ``Iff).isSome                 -- _ <-> _
  || t.isAppOfArity ``Eq 3                       -- _ = _
  || t.isAppOfArity ``Ne 3                       -- _ <> _
  || t.isAppOfArity ``Not 1                      -- ~ _
  || (orderSidesAt? t ``Int).isSome             -- Z.le / Z.lt / Z.ge / Z.gt
  || (orderSidesAt? t ``Nat).isSome             -- le / lt / ge / gt (nat, N, positive)
  || (binaryApp? t ``Or).isSome                  -- _ \/ _
  || t.isConstOf ``Int                           -- Z
  || t.isConstOf ``Nat                           -- nat / N / positive

/-- Single pass, last hypothesis first: `clear` every non-arithmetic
    hypothesis; one a kept hypothesis depends on simply stays (its `clear`
    fails, cheaply). -/
def prune : TacticM Unit :=
  clearHyps (keep := fun h => is_arith h.type) (fixpoint := false)

end LiaFastL2

/-- `prune_arith_ctx := ltac2:(LiaFastL2.prune_arith_ctx0 ())`: keep
    only the hypotheses built from arithmetic atoms and let-definitions.

    Use it only where the arithmetic call is TERMINAL for the goal: the
    pruned goal is weaker, and the hypotheses are gone for good (unless an
    enclosing `first`/`try` rolls the arm back). -/
elab "prune_arith_ctx" : tactic => LiaFastL2.prune_arith_ctx0

/-- `alia := prune_arith_ctx; lia`.

    `prune_arith_ctx <;> omega` — the `<;>` replays `omega` on exactly
    the goals the pruner produced (one), i.e. -/
macro "alia" : tactic => `(tactic| prune_arith_ctx <;> omega)

/-- `ania := prune_arith_ctx; nia`.

    PARTIAL — `prune_arith_ctx <;> omega`, the linear fragment of
    `nia`; see `nia_mod` (including the "use instead" list) and the notes (c)1.  Nonlinear goals fail and need an explicit proof. -/
macro "ania" : tactic => `(tactic| prune_arith_ctx <;> omega)

/-- `flia_prune1 := ltac2:(Ltac2.Control.enter LiaFastL2.prune)`:
    the single-pass pruner, on the current goal.

    `LiaFastL2.prune` under the house goal-list guard. -/
elab "flia_prune1" : tactic => withGoalsRestored LiaFastL2.prune

/-- `flia_clear_mod0 := repeat match goal with H : (_ mod _ = 0)%Z
    |- _ => clear H end`: drop the `_ mod _ = 0` facts.

    `clearHyps` keeping every hypothesis that is NOT `(_ mod _ = 0)` at
    `Int`, run to fixpoint.  A hypothesis some kept one
    depends on stays, as with any `clear`. -/
elab "flia_clear_mod0" : tactic => withGoalsRestored do
  clearHyps (keep := fun h => !isModEqZero h.type) (fixpoint := true)

/-- `flia1`: the two-stage variant — try WITHOUT the `_ mod _ = 0`
    facts, then with them, but only when the GOAL itself mentions mod/div
    (every other first-attempt failure is a genuinely false goal used as a
    test inside `first [lia | ..]`, and those must fail FAST).  
    refers to zify/xlia directly so that a `Local Ltac lia ::= flia1`
    rebinding does not loop.

    the same two stages with `omega` in the certificate slot:
    `flia_prune1`, then `first | (flia_clear_mod0; omega) | omega`, where the
    second stage is only reached when the goal mentions mod/div.
    The "fail fast unless the goal mentions mod/div" property is preserved:
    on a non-mod/div goal this is exactly `flia_prune1; flia_clear_mod0;
    omega`, so it fails where  fails. -/
elab "flia1" : tactic => withGoalsRestored do
  evalTactic (← `(tactic| flia_prune1))
  if mentionsDivMod (← getMainTarget) then
    evalTactic (← `(tactic|
      first
      | (flia_clear_mod0; omega)
      | omega))
  else
    evalTactic (← `(tactic| flia_clear_mod0; omega))

/-- `flia_lin`: the linear attempt — only for goals WITHOUT div/mod;
    drops every hypothesis mentioning div/mod so the euclidean pass has
    nothing to do.
 Failing leaves no partial
    state: the exception propagates, and the enclosing `first` in `flia2`
    restores the cleared hypotheses before trying the full call. -/
elab "flia_lin" : tactic => withGoalsRestored do
  if mentionsDivMod (← getMainTarget) then
    throwError "flia_lin: the goal mentions div/mod (unsupported by this arm)"
  evalTactic (← `(tactic| flia_prune1))
  clearHyps (keep := fun h => !mentionsDivMod h.type) (fixpoint := true)
  evalTactic (← `(tactic| omega))

/-- `flia_full1 := flia_prune1; Zify.zify; xlia zchecker`: full
    `lia` in the single-pass-pruned context.

    `flia_prune1 <;> omega` — `omega` is the full decision procedure
    here (it has no zify phase to skip). -/
macro "flia_full1" : tactic => `(tactic| flia_prune1 <;> omega)

/-- `flia2 := first [ solve [flia_lin] | flia_full1 ]`: linear
    attempt, then full — so, unlike `flia1`, a goal that needs a
    `_ mod _ = 0` hypothesis without mentioning mod itself still goes
    through.

    `first | flia_lin | flia_full1`. -/
macro "flia2" : tactic => `(tactic|
  first
  | flia_lin
  | flia_full1)

/-! ## Closed goals -/

/-- `lia_closed_has_var := match goal with |- ?G => match G with
    context [?x] => is_var x end end`: succeeds iff the goal mentions a
    local variable.
-/
elab "lia_closed_has_var" : tactic => withGoalsRestored do
  unless (← getMainTarget).hasFVar do
    throwError "lia_closed_has_var: the goal mentions no variable"

/-- `lia_clear_all := repeat match goal with H : _ |- _ => clear H
    end`: empty the context as far as `clear` allows.

    `clearHyps` with a keep test that rejects everything, run to
    fixpoint.  Variables the goal still mentions cannot be cleared and stay
    (`MVarId.clear` refuses), which is what makes `clia`'s empty-context
    attempt a genuine sub-context of the plain call. -/
elab "lia_clear_all" : tactic => withGoalsRestored do
  clearHyps (keep := fun _ => false) (fixpoint := true)

/-- `clia`: a variable-free goal is first tried in the empty context
    (no hypothesis is preprocessed); if that fails (a closed goal provable
    only from contradictory hypotheses) the plain call runs unchanged; an
    open goal takes the plain path directly — exactly the same goals are
    proved.

    `first | (lia_closed_has_var; omega) | (lia_clear_all; omega) |
    omega`, i.e. the open-goal path is the guarded plain call, the
    closed-goal path tries the emptied context and then the plain call. -/
macro "clia" : tactic => `(tactic|
  first
  | (lia_closed_has_var; omega)
  | (lia_clear_all; omega)
  | omega)

/-- `cnia`: `clia` with `nia`.

    PARTIAL — the linear fragment (`omega`); see `nia_mod` and
    The closed/open split is `clia`'s. -/
macro "cnia" : tactic => `(tactic|
  first
  | (lia_closed_has_var; omega)
  | (lia_clear_all; omega)
  | omega)

/-- `is_zlit t`: succeeds iff `t` is a closed `Z` literal
    expression.

    succeeds iff `t` is CLOSED (no local variable, no metavariable) —
    the invariant the constructor-by-constructor list protects, and
    the only one Lean needs, since its numeral syntax is not a fixed
    constructor set and kernel reduction is total on closed terms. -/
elab "is_zlit " t:term : tactic => withGoalsRestored do
  let e ← elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless isClosedLit (← instantiateMVars e) do
    throwError "is_zlit: the term is not a closed literal"

/-- `is_nlit t`: the `nat` half of the `zlit` literal test.

    the same closedness test as `is_zlit`; see there and the notes
    (c)2. -/
elab "is_nlit " t:term : tactic => withGoalsRestored do
  let e ← elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless isClosedLit (← instantiateMVars e) do
    throwError "is_nlit: the term is not a closed literal"

/-- prove every goal of `pending` the way  `zlit` does,
    conjunct by conjunct (the recursion of `split; zlit`), leaving any goals
    a step produces in the goal list.  Called by the `zlit` elab below, which
    documents the arms. -/
private partial def zlitGoals (pending : List MVarId) : TacticM Unit := do
  match pending with
  | [] => pure ()
  | g :: rest =>
    setGoals [g]
    let target ← instantiateMVars (← g.getType)
    if target.isAppOfArity ``And 2 then
      -- `|- ?a /\ ?b => split; zlit`: split, then zlit on every
      -- conjunct produced (exactly `split; zlit`, not just one level)
      evalTactic (← `(tactic| constructor))
      zlitGoals ((← getGoals) ++ rest)
    else if let some (a, b) := orderSidesAt? target ``Int then
      if isClosedLit a && isClosedLit b then
        evalTactic (← `(tactic| decide))
        zlitGoals rest
      else
        throwError "zlit: the sides of the goal are not closed literals"
    else if let some (a, b) := orderSidesAt? target ``Nat then
      if isClosedLit a && isClosedLit b then
        evalTactic (← `(tactic| decide))
        zlitGoals rest
      else
        throwError "zlit: the sides of the goal are not closed literals"
    else if let some (a, b) := intEqSides? target then
      if isClosedLit a && isClosedLit b then
        evalTactic (← `(tactic| decide))
      else
        -- `ring` fallback; see the notes (c)3
        evalTactic (← `(tactic| omega))
      zlitGoals rest
    else
      throwError "zlit: the goal is not a closed literal (in)equality"

/-- `zlit`: closed literal (in)equalities decided by computation,
    never by zify.

    the recursion is spelled out in `zlitGoals` rather than as
    `constructor <;> zlit` in a quotation, because a tactic command's own
    name is not yet in the environment while its body is elaborated — the
    `zlit` inside such a quotation would be StartupTac's (documented no-op)
    `zlit`, not this one.  A file that opens both
    namespaces gets whichever was opened LAST , so open only the one you mean or
    write `LiaFast.zlit`. -/
elab "zlit" : tactic => withGoalsRestored do
  let gs ← getGoals
  match gs with
  | [] => pure ()
  | g :: rest =>
    zlitGoals [g]
    setGoals ((← getGoals) ++ rest)

/-- `plia := first [ zlit | alia ]`: closed literals by computation,
    everything else pruned then `lia`.

    `first | zlit | alia`.  Note the ORDER is the point: a closed
    literal goal is decided without touching the context, so `plia` on
    `0 ≤ 118464 < 2 ^ 64` never preprocesses the surrounding hypotheses. -/
macro "plia" : tactic => `(tactic|
  first
  | zlit
  | alia)

/-! ## Bit-vector literal well-formedness -/

/-- `BvWf n z`: `z` is a well-formed `n`-bit value
    (`0 ≤ z < 2 ^ n`).
 It is defined here,
    with the same meaning, so that `solve_BvWf_fast` and its two self-test
    goals have their  subject and remain checkable. -/
def BvWf (n : Nat) (z : Int) : Prop :=
  0 ≤ z ∧ z < 2 ^ n

/-- The Lean form of  `#[export] Hint Extern 9 (BvWf _ _) =>
    solve_BvWf_fast : typeclass_instances`: a `Decidable` instance, so
    `decide` — and any closer that ends in `decide` — can close a closed
    `BvWf n z` by computation.  Lean has no typeclass hint for
    propositions, so `decide` is the automation hook that plays the role of
    the registered hint; the cost ordering  cares about  has no Lean counterpart.  See:
    `bool_decide P` → `decide P`. -/
instance (n : Nat) (z : Int) : Decidable (BvWf n z) := by
  unfold BvWf
  infer_instance

/-- `bvwf_has_var t := match t with context [?x] => is_var x end`:
    succeeds iff `t` mentions a local variable.

    `Expr.hasFVar` on the elaborated term. -/
elab "bvwf_has_var " t:term : tactic => withGoalsRestored do
  let e ← elabTerm t none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless (← instantiateMVars e).hasFVar do
    throwError "bvwf_has_var: the term mentions no variable"

/-- `solve_BvWf_fast`: decide `BvWf n v` by computation when both
    arguments are closed; the context-clearing form costs 0.1-0.5 s per
    literal in a big-context walk.  Same proof term.
-/
elab "solve_BvWf_fast" : tactic => withGoalsRestored do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``BvWf 2 do
    throwError "solve_BvWf_fast: the goal is not of the form `BvWf n v`"
  let args := target.getAppArgs
  unless isClosedLit args[1]! do
    throwError "solve_BvWf_fast: the value is not closed"
  unless isClosedLit args[0]! do
    throwError "solve_BvWf_fast: the width is not closed"
  evalTactic (← `(tactic| decide))

/-!  They are `example`s here, in the same order.  The `ania` one is the
    single goal this tree cannot close with the arithmetic tactic (it is
    nonlinear integer arithmetic; see the notes (c)1) and carries a hand
    proof instead. -/

namespace LiaFastSelfTest

/-- : `forall (x y : Z) (l : list Z) (b : bool), length l = 3%nat ->
    b = true -> 0 <= x -> x < y -> x < y + 1` by `alia`. -/
example (x y : Int) (l : List Int) (b : Bool) (h1 : l.length = 3) (h2 : b = true)
    (hx : 0 ≤ x) (hxy : x < y) : x < y + 1 := by
  alia

/-- : `forall (x y : Z) (l : list Z), length l = 3%nat -> 0 <= x ->
    x < y -> x * x < y * y` by `ania`.
 This is the documented substitution for
    `nia` call sites. -/
example (x y : Int) (l : List Int) (h1 : l.length = 3) (hx : 0 ≤ x) (hxy : x < y) :
    x * x < y * y := by
  exact Int.mul_self_lt_mul_self hx hxy

/-- : `forall x : Z, 0 <= x -> x mod 4 = 0 -> exists q, x = 4 * q` by
    `lia_mod` (with the witness `x / 4`). -/
example (x : Int) (hx : 0 ≤ x) (hm : x % 4 = 0) : ∃ q, x = 4 * q := by
  refine ⟨x / 4, ?_⟩
  lia_mod

/-- : "the mod fact is needed although the goal does not mention mod:
    flia2 goes through, flia_lin alone would not" —
    `forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x -> x mod 8 = 0
    -> 8 <= x` by `flia2`. -/
example (x : Int) (l : List Int) (h1 : l.length = 2) (hx : 5 ≤ x) (hm : x % 8 = 0) :
    8 ≤ x := by
  flia2

/-- : `forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x ->
    x < 7 -> x <= 6` by `flia_lin`. -/
example (x : Int) (l : List Int) (h1 : l.length = 2) (hx : 5 ≤ x) (hxy : x < 7) :
    x ≤ 6 := by
  flia_lin

/-- : `forall (x : Z), 5 <= x -> x mod 8 = 0 -> x / 8 >= 1` by
    `flia1`. -/
example (x : Int) (hx : 5 ≤ x) (hm : x % 8 = 0) : x / 8 ≥ 1 := by
  flia1

/-- : `(2 ^ 17 + 20 <= 2 ^ 64)%Z /\ (5 < 41)%nat` by `zlit`. -/
example : (2 : Int) ^ 17 + 20 ≤ (2 : Int) ^ 64 ∧ (5 : Nat) < 41 := by
  zlit

/-- : `forall (x : Z) (H : x = 3), (1 <= 8)%Z` by `clia` — a CLOSED
    goal in a non-empty context: the emptied-context arm proves it. -/
example (x : Int) (H : x = 3) : (1 : Int) ≤ 8 := by
  clia

/-- : `forall (x : Z) (H : x = 3), (1 <= x)%Z` by `clia` — an OPEN
    goal: the plain path proves it from `H`. -/
example (x : Int) (H : x = 3) : (1 : Int) ≤ x := by
  clia

/-- : `forall (x : Z), 0 <= x -> (0 <= 118464 < 2 ^ 64)%Z` by
    `plia` — closed literals by computation, no hypothesis preprocessing. -/
example (x : Int) (hx : 0 ≤ x) : (0 : Int) ≤ 118464 ∧ (118464 : Int) < 2 ^ 64 := by
  plia

/-- : `Goal BvWf 64%N 3%Z` by `solve_BvWf_fast`. -/
example : BvWf 64 3 := by
  solve_BvWf_fast

/-- : `Goal BvWf 8%N 255%Z` by `typeclasses eauto` — the hint
    registration.  the `Decidable` instance plus `decide` is the
    automation hook that plays the registered hint's role; see the instance's
    docstring. -/
example : BvWf 8 255 := by
  decide

end LiaFastSelfTest

end LinuxSem.Common.LiaFast
