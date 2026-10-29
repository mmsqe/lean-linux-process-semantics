/-
  * Common.CertRefl — the single-evaluation reflective certificate tactic.

  With it, a certificate file is one import and one line per lemma.

  A reflective certificate has the shape

      theorem leaf_ok : check ARGS plan = COk shape := by
        cert_refl (COk shape)

  where `check` is a plan checker of the ASan reflective automation
  (`AsanPlan.AP.check`, or an image's `seg_check`/`pay_check` wrappers) and
  the right-hand side `shape` was obtained beforehand by running the same
  `check` (the "itinerary": a `by native_decide`/`by decide` evaluation
  off-line).  Plain `rfl` would evaluate the checker TWICE — once while
  elaborating the tactic, once again when the kernel re-checks the proof
  term at the end of the declaration.  `cert_refl rhs` instead builds the
  proof term `@eq_refl α rhs` and hands it to the goal with the
  no-typecheck assignment, so the conversion runs ONCE, when the kernel
  checks the finished declaration.  (`α` is inferred from `rhs`; any
  inductive with decidable equality works the same way — change the
  annotation.)

   is Ltac2:

      Ltac2 cert_refl (rhs : constr) :=
        let g := Control.goal () in
        let r := constr:(@eq_refl _ $rhs) in
        Std.exact_no_check
          (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.native g)).
 Lean has ONE conversion check
    (the kernel's), and no native-cast node versus VM-cast node to choose
    between: `Constr.Cast.native` / `Constr.Cast.vm` have no counterpart,
    so the distinction — "native needs .coq-native objects for
    the whole import closure, VM needs none" — collapses.  Every
    certificate file can use either name; `cert_refl_vm` is kept because
    that is the one  certificate files call.
  Cost note : under a toolchain with native
  compilation disabled the certificate stays valid, only slower (3-5x on
  the ASan plan checks).  Nothing else in the reflective library needs
  native code.  In Lean the cost is the kernel's own reduction of the
  checker at declaration check time; `native_decide` is the escape hatch
  when that reduction is too slow (`decide`'s `of_decide_eq_true` path
  re-checks the computation).
  The two `example`s at the bottom are faithful
  additions: they exercise each tactic once on a goal whose two sides are
  convertible only by computation (a `List.range` length), i.e. the
  certificate shape with the checker replaced by a cheap one.
-/
import Lean

namespace LinuxSem.Common.CertRefl

open Lean Elab Tactic Meta

/-- `cert_refl rhs`: close a goal `lhs = rhs` whose two sides are convertible
    by computation, with one kernel conversion check at the end of the
    declaration. -/
elab "cert_refl " rhs:term : tactic => do
  let g ← getMainGoal
  let rhsExpr ← instantiateMVars (← elabTerm rhs none)
  let α ← inferType rhsExpr
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α rhsExpr)
  replaceMainGoal []

/-- The same with the VM conversion instead of native code — the one to use in
    a certificate file (see the header: it needs no native objects); under a
    toolchain that disables native compilation every native cast turns into
    this anyway.  In Lean both entry points are the same tactic: there is no
    native-cast node to distinguish (see the in the header). -/
elab "cert_refl_vm " rhs:term : tactic => do
  let g ← getMainGoal
  let rhsExpr ← instantiateMVars (← elabTerm rhs none)
  let α ← inferType rhsExpr
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α rhsExpr)
  replaceMainGoal []

/-! ## Sanity checks (decidable checks) -/

/-- A certificate line of the shape: `check ARGS plan` is replaced by
    a cheap computation, `COk shape` by the answer `5`. -/
example : (List.range 5).length = 5 := by cert_refl 5

example : (List.range 5).length = 5 := by cert_refl_vm 5

end LinuxSem.Common.CertRefl
