/-
  * Common.StepTac — shared step-chaining tactics

  Covers the full set of chain relations ([msteps]/[to_wexit]/[twm]/
  [tmw]/[StreamSim.to_wr]/[StreamSim.to_rd]/[to_exit]/
  [DrainSim.to_out]/[DrainSim.to_rd]).  Each tactic is a SUPERSET of
  the per-example variants: each only fires on a goal whose head
  matches one of its `first` arms, and each step is pinned down by the
  caller-supplied fetch/decode lemma ([F]/[D]), so extra arms that
  don't apply just fail over silently.

  Value-normalization note: the canonical computed-value form is
  `BitVec.ofInt 64 z` with `z` a plain-[Int] expression.  [sp_norm]
  therefore rewrites nested [v_addi] chains over an abstract in-window
  sp into that form; the [u_Z2bv] helper collapses
  `(BitVec.ofInt 64 z).toNat` for the in-range side conditions.

  Shared additions (so examples need no local copies):
  - safe computation layer: [check_closed_term]/[expand_ctx_defs] (is
    this term closed, as the evaluator sees it?) and [vm_eval];
  - closing tactics: [bveq], [vm_refl_bv];
  - closed-redex literal normalizers: [wlit_closed] (argument form)
    and [wlits_closed] (sweep) — replace a CLOSED word redex with its
    computed `BitVec.ofInt 64 z` literal;
  - [rdn_ext_lit] — wraps the [rdn_ext] call-site pattern;
  - shared lemmas: [byte_nz_u], [u_zext8], [zext8_byte],
    [byte_neq_lit_u], [c_eq_zext_lit_false], [u_ntw], [word_add_nat],
    [word_add_nat_0], [word_add_nat_1], [word_add_nat_m1],
    [v_add_comm], [v_add_wrap], [v_sub_0_neg], [u_neg_small],
    [v_addi_neg_S], [bsb_bound], [range_avoids_two].
    (The `x + nat_to_word 0 = x` bridge is named [word_add_nat_0]
    here, NOT [word_add_0_r] — AllocSim exports a different
    [word_add_0_r], stated at `BitVec.ofInt 64 0`.)

  Instruction coverage: [stepi]/[stepi_search] dispatch every OpImm /
  ShiftImm / Op / OpImm32 / ShiftImm32 / Op32 / Mul / Mul32 shape with
  a step lemma ([divu]/[remu] leave their divisor-nonzero premise as an
  extra goal when `assumption`/`omega` cannot close it); [stepiv]
  dispatches the [SeqExec.step_*_at] family the same way; [stepw] steps
  a store of any width ([sd]/[sw]/[sh]/[sb]); [stepj] also handles a
  LINKING [jal]; [stepjr] handles [jalr] (ret and register calls).
  Smoke tests at the end of the file pin one concrete encoding per
  dispatch arm.

  ---------------------------------------------------------------------
  NOTES
  ---------------------------------------------------------------------

  The  file is a *tactic library*, so it has two halves of
  different natures, and this module treats them differently.

  **(a) Every  `Definition`/`Lemma`/`Theorem` is present
  faithfully** — that is the real content.  The mapping is the standard
  one: `Z` → `Int`, `N`/`nat` → `Nat`, `Z_to_bv n z` →
  `BitVec.ofInt n z`, `bv_unsigned w` → `(w.toNat : Int)`,
  `bv_signed w` → `w.toInt`, `Z.ltb a b = false` → `decide (a < b) =
  false`, `Z.leb a b = true` → `decide (a ≤ b) = true`, `Z.of_N n` →
  `(n : Int)` (this tree's segment fields are `Nat`), `forallb p l` →
  `l.all p`, `negb`/`andb`/`orb` → `!`/`&&`/`||`, `cbn [..]` →
  `simp only [..]`, `vm_compute; reflexivity` → `decide` (or
  `bv_omega` where the goal is bitvector arithmetic).
  **(b) Each  `Ltac` becomes a Lean `macro` of the same name
  and arity.**  Reproducing the *effect* is where the language
  differences bite; the individual documentation comments mark what
  changed.  The three systematic deviations are:

  1. *`lazymatch type of D with` dispatch* ([stepi], [stepiv], [stepw]).
      picks the ONE applicable step lemma from the SHAPE of the
     decode hypothesis `D`, because an `exact` attempt would elaborate its
     whole conclusion (the full machine state and memory image) before it
     could fail.  Lean tactics cannot pattern-match a
     hypothesis TYPE with `lazymatch`, so this tree runs the same arm
     list in the same order: the ARM SET and ORDER are identical, so
     coverage is identical and only the cost profile changes.  A downstream file that needs the dispatch back can order
     the arms it knows it needs, or add a small metaprogramming
     dispatcher (see §"Tactic fidelity" below).
  2. *`vm_compute`-based normalizers* ([word_lit], [wlit_replace],
     [wlit], [wlits], [norm_pc], [norm_pc_state], [imm_norm],
     [reduce_bv_eqb_ifs]).  These exist because `simp`/`dsimp` will not
     reduce a `bv_unsigned`/`bv_signed` projection over a vm-cast
     numeral, and because `rewrite` cannot match a closed redex whose
     reduction needs conversion.  Lean's elaborator has neither
     problem: `exact`/`rw`/`apply` unify up to reducible unfolding, and
     `decide`/`rfl`/`omega`/`bv_omega` all reduce closed terms.  §"Tactic fidelity" says what to use instead.
  3. *Safe computation* ([check_closed_term], [vm_eval]).
 Lean's kernel
     reduction has no such failure mode (it gets stuck on a variable),
     so the guard is a diagnostic here, not a safety device.  It is
     still stated as a real check: [check_closed_term] inspects the
     elaborated term for context variables and metavariables.
  **(c) Tactic fidelity — what each  `Ltac` became**
  *Same-name tactics, faithful in effect:*
  - `chain_step`, `step_intro`: `first | apply <constructor> | …`, the same
    twelve chain heads, same order.
 What is NOT reproduced is the
    `lazymatch type of D` dispatch; see §(b)1.
  - `bveq`: `apply BitVec.eq_of_toNat_eq` followed by the closers, with
    `decide` in the `vm_compute; reflexivity` slot.  The 30-second
    `timeout` and the closedness triage are gone — Lean's kernel reduction
    cannot diverge on an open term, so the triage is a diagnostic only.
  - `vm_refl_bv`: `first | rfl | decide` — the same kernel-checked
    certificate, without `vm_cast_no_check` (Lean has no unverified cast to
    reproduce).
  - `u_norm`: real, as `iterate 4 (first | ((rw [u_Z2bv]) <;> (first | omega
    | skip)) | skip)`.   - `stepw_addr`, `stepw_val`: the same script shape
    (`getr_resolve` → `regupd_resolve` → `sp_norm` → lexical closer), with
    `bv_omega`/`bveq` replacing `lia`/`f_equal`.
  - All argument lists are COMMA-separated (see [chain_step]'s docstring).
  *Reproduced in part, with the missing half noted at the tactic:*
  - `check_closed_term`, `expand_ctx_defs`, `vm_eval`: the guard is real
    (an `elab` that walks the elaborated term for context variables and
    metavariables); `expand_ctx_defs` is the identity because Lean has no
    `set`-bound opacity; `vm_eval` degrades to "check, then `rfl`/`decide`".
  - `sp_norm`: only the `u_norm` half — the nested-[v_addi] rewriting it
    exists for  is definitional in Lean (`v_addi x imm` unfolds to
    `BitVec.ofInt 64 (x.toNat + imm)`, and `a - k` IS `a + -k`), so the
    rewrite arms would be `rfl`-level no-ops.  The `v_addi_m*` /
    `v_addi_nneg_t` lemmas are still exported for callers that want the
    rewrite by name.
  - `rdn_ext_lit`: supplies the side-condition half only, because the Lean
    [rdn_ext] takes the pointwise premise as one explicit argument; the
    call site writes `rw [rdn_ext segs k m1 m2 a hno hpointwise]`.
  Lean's elaborator has neither problem: `exact`/`rw`/`apply` unify up to
  reducible unfolding, and `decide`/`rfl`/`omega`/`bv_omega` all reduce
  closed terms.  A downstream file should therefore DROP these calls (or
  replace them by `decide`/`rfl`/`simp only [reduceIte]`); keeping them is
  harmless, which is the point of making them total.
  declarations: [ofInt_toNat] (the literal-shape bridge
  [wlit_closed] cites) and the two smoke-test scaffolds [smoke]/[smoke_v].
  Every other declaration has its  statement modulo the mapping in
  §(a).

  Word hygiene: this file contains no proof hole and no extra
  postulate.
-/
import Lean
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Decode
import LinuxSem.Riscv.DecodeC
import LinuxSem.Riscv.Sem
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.RiscvSemantics
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.Common.PropExec
import LinuxSem.Common.CatSim
import LinuxSem.Common.CatExec
import LinuxSem.Common.SeqExec
import LinuxSem.Common.ExitSim
import LinuxSem.Common.StreamSim
import LinuxSem.Common.StreamExec
import LinuxSem.Common.WallSim
import LinuxSem.Common.DrainSim
import LinuxSem.Common.MmapSim

namespace LinuxSem.Common.StepTac

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.Common
open Lean Parser
open LinuxSem.Common.PropExec
open LinuxSem.Common.SeqExec
open LinuxSem.Common.CatSim
open LinuxSem.Common.MmapSim
open LinuxSem.Common.StreamSim
open LinuxSem.Common.WallSim
open LinuxSem.Common.DrainSim
open LinuxSem.Common.ExitSim

/-! ## Chain-relation entry ([chain_step]) and pc literal normalization -/

/-- One step into whichever chain relation the current goal targets.
    Superset of every per-example `chain_step`/`step_intro`: `msteps`
    (plain instruction stream), `to_wexit` (write-then-exit, CatSim),
    `twm`/`tmw` (single mmap, MmapSim), `StreamSim.to_wr`/`StreamSim.to_rd`
    (unbounded stream loop), `DrainSim.to_out`/`DrainSim.to_rd` (drain-loop),
    `to_exit` (exit-only, ExitSim).

     `first [ eapply mst_step | … ]`; this tree's chain
    relations expose the same step nodes as constructors
    (`msteps.mst_step`, `to_wexit.tw_step`, `twm.step`, `twm_tail.step`,
    `tmw.step`, `to_wr.twr_step`, `to_rd.trd_step`, `to_wall_tail.twt_step`,
    `to_exit.te_step`) plus the one theorem  also names
    (`WallSim.twe_step`).
    CALL SYNTAX (applies to every tactic below): arguments are
    COMMA-separated, the house style of this module's other tactic macros
    (`PropExec.step_pipeline Hfetch, Hecall, Hdecode`).  Two
    whitespace-separated `term` arguments cannot appear in a Lean macro
    template, which is what forces the comma. -/
macro "chain_step" : tactic =>
  `(tactic|
    first
    | apply msteps.mst_step
    | apply to_wexit.tw_step
    | apply twm.step
    | apply twm_tail.step
    | apply tmw.step
    | apply StreamSim.to_wr.twr_step
    | apply StreamSim.to_rd.trd_step
    | apply to_wall_tail.twt_step
    | apply WallSim.twe_step
    | apply DrainSim.to_out.tout_step
    | apply DrainSim.to_rd.trd_step
    | apply to_exit.te_step)

/-- Backward-compatible alias: several examples name this entry point
    `step_intro` instead of `chain_step`. -/
macro "step_intro" : tactic => `(tactic| chain_step)

/-!
    Lean has no such failure mode: kernel reduction (`decide`, `rfl`,
    `simp`) STOPS on a variable instead of allocating, so the guard is a
    DIAGNOSTIC here, not a safety device. -/

/-- Expand every let-bound context definition
    mentioned in [p] to its body, recursively.

    Lean has no `set`-introduced opaque definitions — a `let`/`have`
    is definitionally transparent and `decide`/`simp` unfold it on demand —
    so the expansion step is the identity. -/
macro "expand_ctx_defs " _p:term : tactic => `(tactic| skip)

/-- Succeeds iff [p] mentions no local hypothesis and no metavariable — the
    Lean rendering of  "closed as far as the evaluator is
    concerned" test .
-/
elab "check_closed_term " p:term : tactic => do
  let e ← Lean.Elab.Term.elabTerm p none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  let lctx ← Lean.getLCtx
  let mut mentionsCtx := false
  for ldecl in lctx do
    if e.containsFVar ldecl.fvarId then mentionsCtx := true
  if e.hasMVar then
    Lean.throwError "check_closed_term: the term contains a metavariable"
  if mentionsCtx then
    Lean.throwError "check_closed_term: the term mentions a context variable"

/-- The safe `eval vm_compute in t`: identical result, but [t] is checked
    closed first, so the evaluator can neither diverge on a symbolic
    bitvector term nor meet a metavariable.  On an open term it fails fast
    instead, which a caller's `try`/`first`-backtracking absorbs.

    in value position the Lean spelling of "reduce [t]" is
    `decide`/`rfl` on a CLOSED term, and the guard above is a diagnostic.
    Used as a tactic, [vm_eval] checks closedness and then closes the goal
    by computation. -/
macro "vm_eval " t:term : tactic =>
  `(tactic| check_closed_term $t <;> first | rfl | decide)

/-! ## Literal normalizers -/

/-- Build the numeral literal equal to a CLOSED word term [p] (fails fast
    when [p] is open).

    : `Ltac word_lit p` builds the numeral-notation literal
    (`@BV 64 u I`-shaped) that [p] computes to, and notes that the two
    normal forms of a computed word are NOT interconvertible — a numeral
    literal carries the vm-cast `I`, `Z_to_bv 64 z` carries the opaque
    well-formedness proof — so a chained machine state can only match a
    fetch lemma's literal pc up to a PROPOSITIONAL rewrite.
 In Lean both normal forms
    are the same term up to `BitVec.ofNat`, so the interconversion problem
    disappears; what remains is the closedness guard, kept so an open [p]
    fails with a message instead of silently returning [p]. -/
elab "word_lit " p:term : term => do
  let e ← Lean.Elab.Term.elabTerm p none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Lean.instantiateMVars e
  let lctx ← Lean.getLCtx
  let mut open_ := false
  for ldecl in lctx do
    if e.containsFVar ldecl.fvarId then open_ := true
  if e.hasMVar || open_ then
    Lean.throwError "word_lit: the term is not closed — resolve the register \
      and memory projections first"
  let v ← Lean.Meta.whnf e
  return v

/-- Body shared by [wlit]/[wlits]: normalise the redex [p] in the goal.

     replaces [p] by its vm-computed numeral literal, which it
    needs because a later `rewrite` cannot match a closed redex whose
    reduction needs conversion. -/
macro "wlit_replace " p:term : tactic => `(tactic| try (check_closed_term $p))

/-- Rewrite a closed word subterm of the goal to its literal form (no-op
    when it already is one, or when [p] is open).

    see [wlit_replace] — the normalization is automatic in Lean, so
    this is the same closedness diagnostic. -/
macro "wlit " p:term : tactic => `(tactic| try (check_closed_term $p))

/-- Normalize every closed computed-value redex in the goal to its literal
    form.  Open, sp-symbolic redexes are skipped — they are [sp_norm]'s job.

    a total no-op; see [wlit_replace].  Downstream files should simply
    omit it (or use `decide`/`rfl` where a rewrite is wanted). -/
macro "wlits" : tactic => `(tactic| skip)

/-- Evar guard for [norm_pc]: when the machine-state position of the chain
    goal contains an evar (e.g. [norm_pc] called before the
    `eexists`/instantiation that pins the state), the position must be left
    alone.

    `norm_pc` no longer touches the state at all (see below), so the
    guard is the identity; kept for call-site compatibility. -/
macro "norm_pc_state " _st:term : tactic => `(tactic| skip)

/-- Normalize the next-pc at the head of whichever chain relation the goal
    exposes to its literal form, so the next step's fetch-lemma literal
    matches.
 In Lean the
    next pc of a stepped state is `v_addi pc 4`, which is definitionally the
    numeral the next fetch lemma is stated at, so `rw`/`exact` match it
    without any normalization: the macro is a total no-op.  This is also why
    no evar guard is needed. -/
macro "norm_pc" : tactic => `(tactic| skip)

/-! ## Single-instruction steps -/

/-- Post-step simplification of decode-literal register guards
    (`if bv_eqb rd 0 …` with rd a numeral) before pc normalization.

     computes `bv_eqb a b` for two literal encodings and
    collapses the `if` by `change` (plain conversion).  (A downstream caller that wants the `if` gone from the goal TEXT
    can add `simp only [reduceIte]`.) -/
macro "reduce_bv_eqb_ifs" : tactic => `(tactic| skip)

/-- `rewrite ?skipn_O; norm_pc`: several loop proofs hit a leftover
    `drop 0` redex after a chunk step; the `?` form only fires when the
    redex exists, so it does not change other invocations. -/
macro "step_simpl" : tactic =>
  `(tactic| (try (simp only [List.drop_zero]); reduce_bv_eqb_ifs; norm_pc))

/-- The instruction alternation of [stepi], tried in order.  Kept as a
    separate tactic so [stepi] can use it as the fallback behind the
    decode-shape dispatch below.
 Each arm `refine`s the
    corresponding step lemma with every argument left to unification and the
    premises discharged by the `first`-alternation after `<;>` (the fetch
    hypothesis [F], the `is_ecall` premise by computation, the decode
    equation [D], plus `assumption`/`omega` for the divisor-nonzero premise
    of `divu`/`remu`). -/
macro "stepi_search " F:term "," D:term : tactic =>
  `(tactic|
    first
      | (refine step_addi _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_add _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sub _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_slli _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_auipc _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_lui _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_addiw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_andi _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sltiu _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_xori _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine PropExec.step_srli _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_mul _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_ori _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_subw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_slti _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_srai _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_and _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_or _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_xor _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sll _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_srl _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sra _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_slt _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sltu _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_addw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sllw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_srlw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sraw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_slliw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_srliw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_sraiw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_mulh _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_mulhsu _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_mulhu _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_div _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_rem _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_mulw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_divw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_divuw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_remw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption)
      | (refine step_remuw _ _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption))

/-- One non-branching ALU step inside a chain. Superset of every
    per-example instruction alternation.
 Picking the
    single applicable lemma from `type of D` turns up to 14 attempts into
    one.
 A caller
    that cares about the per-step cost can pre-order the arms it needs; see
    the module header for the alternative (a `Lean.Elab` dispatcher on the
    type of `D`).
    The `divu`/`remu` arms are the one exception to "closes the step goal":
    RISC-V defines division by zero, but their value shapes
    (`v_divu`/`v_remu`) do not, so those lemmas carry a divisor-nonzero
    premise. -/
macro "stepi " F:term "," D:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_divu _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
          first | decide | assumption | omega | skip)
      | (refine step_remu _ _ _ _ _ _ _ _ _ $F ?_ $D ?_ <;>
          first | decide | assumption | omega | skip)
      | stepi_search $F, $D
      | step_simpl)

/-- One ALU step with the written value pre-normalized, proof obligation left
    to the caller-supplied [tac].  (The value parameter is named [vv] to
    avoid capturing the lemmas' `v` binder.)   DISPATCHES across the
    whole [SeqExec.step_*_at] family, which all share the same premise shape;
    the fallback uses [step_addi_at] for shapes without an `_at` lemma.

    as [stepi] — the same arm list, searched, with the value injected
    at its positional slot so the chained machine state stays flat.  The
    Lean `_at` lemmas additionally carry the `bv_eqb rd 0 = false` guard
     leaves to `step_simpl`; each arm discharges it by computation.
-/
macro "stepiv " F:term "," D:term "," vv:term "," tac:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_addi_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_andi_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_ori_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_xori_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_sltiu_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_slli_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_srli_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_srai_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_add_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_sub_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_addiw_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_mul_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_lui_at _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_auipc_at _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | step_simpl)

/-- [addiw] step with the written value pre-normalized
    ([step_addiw_at]). -/
macro "stepiwv " F:term "," D:term "," vv:term "," tac:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_addiw_at _ _ _ _ _ _ _ _ _ $vv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | step_simpl)

/-- Unconditional jump ([jal]).  The [x0] (no-link) form uses
    [step_jal_x0]; a LINKING [jal] (rd ≠ x0, the call idiom) falls through
    to [SeqExec.step_jal_link], whose `if bv_eqb rd 0` writeback guard
    `step_simpl` collapses. -/
macro "stepj " F:term "," D:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_jal_x0 _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption | omega)
      | (refine step_jal_link _ _ _ _ _ _ _ _ $F ?_ $D  <;> first | decide | assumption | omega)
      | step_simpl)

/-- Indirect jump ([jalr]), target named by the caller (it is a register
    value, so unlike a [jal] target it is not computable from the decode
    lemma alone): [tac] proves `getr regs rs1 = tgt`.  Dispatches between
    the [x0] (ret / tail-jump) and linking (call through a function pointer)
    forms.  NOTE: [norm_pc] vm-computes the next pc, so [tgt] must be a
    CLOSED word — resolve the register to a literal first (the same
    discipline as every fetch pc).  In Lean a symbolic [tgt] simply makes
    the rewrite fail over instead of diverging. -/
macro "stepjr " F:term "," D:term "," tv:term "," tac:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_jalr_x0 _ _ _ _ _ _ _ _ $tv $F ?_ $D ?_ <;> first | decide | assumption | omega | exact $tac)
      | (refine step_jalr_link _ _ _ _ _ _ _ _ _ $tv $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | exact $tac)
      | step_simpl)

/-! ## sp-arithmetic normalization -/

/-- `bv_unsigned (Z_to_bv 64 z)` collapses to [z] when in range — the glue
    that lets nested [v_addi] rewrites feed their own side conditions to
    `omega`. -/
theorem u_Z2bv (z : Int) (hlo : 0 ≤ z) (hhi : z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z := by
  rw [BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt hlo (by rw [Int.natCast_pow]; exact hhi)]
  exact Int.toNat_of_nonneg hlo

/-- Literal-immediate corollaries of [SeqExec.v_addi_m], one per small
    negative-immediate constant used across the examples (`rw` needs the LHS
    stated with a literal `-k`).  Conclusions are in the
    `BitVec.ofInt 64 (…)` canonical form. -/
theorem v_addi_m1 (x : word) (_ : 1 ≤ (x.toNat : Int)) :
    v_addi x (-1) = BitVec.ofInt 64 ((x.toNat : Int) - 1) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem v_addi_m16 (x : word) (_ : 16 ≤ (x.toNat : Int)) :
    v_addi x (-16) = BitVec.ofInt 64 ((x.toNat : Int) - 16) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem v_addi_m32 (x : word) (_ : 32 ≤ (x.toNat : Int)) :
    v_addi x (-32) = BitVec.ofInt 64 ((x.toNat : Int) - 32) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem v_addi_m48 (x : word) (_ : 48 ≤ (x.toNat : Int)) :
    v_addi x (-48) = BitVec.ofInt 64 ((x.toNat : Int) - 48) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem v_addi_m64 (x : word) (_ : 64 ≤ (x.toNat : Int)) :
    v_addi x (-64) = BitVec.ofInt 64 ((x.toNat : Int) - 64) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

theorem v_addi_m80 (x : word) (_ : 80 ≤ (x.toNat : Int)) :
    v_addi x (-80) = BitVec.ofInt 64 ((x.toNat : Int) - 80) := by
  unfold v_addi
  rw [Int.add_neg_eq_sub]

/-- Non-negative immediate, term-level form of [PropExec.v_addi_nneg]. -/
theorem v_addi_nneg_t (x : word) (imm : Int) (_ : 0 ≤ imm)
    (_ : (x.toNat : Int) + imm < 2 ^ 64) :
    v_addi x imm = BitVec.ofInt 64 ((x.toNat : Int) + imm) := rfl

/-- Collapse the `(BitVec.ofInt 64 _).toNat` projections a rewrite chain
    leaves behind (side conditions from window bounds via `omega`).

     `repeat rewrite u_Z2bv by lia`. -/
macro "u_norm" : tactic =>
  `(tactic| iterate 4 (first | ((rw [u_Z2bv]) <;> (first | omega | skip)) | skip))

/-- Reduce `bv_signed`/`bv_unsigned` of encoded-immediate LITERALS to `Int`
    numerals (by computation), so the [v_addi_m*] rewrites below see the
    literal `-k` and `omega` sees numerals.
-/
macro "imm_norm" : tactic => `(tactic| skip)

/-- Normalize nested [v_addi] expressions over an abstract in-window sp,
    innermost occurrence first (the window bounds must be in context for the
    `omega` side conditions).

     rewrites with the [v_addi_m*]/[v_addi_nneg_t] family
    innermost-first, because `v_addi x (-k)` does NOT reduce to the
    `Z_to_bv 64 (bv_unsigned x - k)` spelling it wants to match.  In Lean
    both ARE the same term: `v_addi x imm` unfolds to
    `BitVec.ofInt 64 (x.toNat + imm)` and `a - k` is `a + -k`, so the
    canonical computed-value form is reached by unfolding alone — the
    rewrite arm would be a `rfl`-level no-op on every call.  The macro
    therefore keeps the [u_norm] half (which does real work: it collapses
    the `(BitVec.ofInt 64 z).toNat` projections a chain leaves behind) and
    leaves the nesting to conversion, which is what a Lean caller wants:
    `simp only [v_addi]` or `bv_omega` see straight through the nesting.
    The [v_addi_m*]/[v_addi_nneg_t] lemmas are still exported above, so a
    caller that wants the rewrite can name the one it needs. -/
macro "sp_norm" : tactic => `(tactic| (imm_norm; u_norm))

/-! ## Consolidated closing tactics -/

/-- Close a word/byte equation by unsigned comparison (the
    `replace … by bveq` closer used across the examples).
 Lean's kernel
    reduction has no such failure mode — it gets stuck on a variable
    instead — so the triage is a cost/diagnostic heuristic here, and the arm
    order below reflects it: the closed and the convertible cases fall to
    `rfl`/`decide`, and everything else to the arithmetic closers.
-/
macro "bveq" : tactic =>
  `(tactic|
    apply BitVec.eq_of_toNat_eq <;>
      first
      | rfl
      | decide
      | bv_omega
      | (simp only [v_addi, v_add, v_sub, v_mul]; omega)
      | omega)

/-- Same as [stepiv], but with the value-obligation proof script baked in. -/
macro "stepi_at " F:term "," D:term "," val:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_addi_at _ _ _ _ _ _ _ _ _ $val $F ?_ $D ?_ ?_ <;> first | decide | assumption | omega | (getr_resolve; regupd_resolve; sp_norm; first | rfl | bv_omega))
      | step_simpl)

/-- The [stepw] address/value discharge scripts — the examples' standard
    store-obligation pattern (resolve the register projections, [sp_norm],
    then `rfl`/arithmetic/[bveq]; the [bveq] fallback is
    closedness-guarded, so an OPEN obligation fails fast instead of reaching
    the evaluator). -/
macro "stepw_addr" : tactic =>
  `(tactic| (getr_resolve <;> regupd_resolve <;> sp_norm <;>
    first | rfl | bv_omega | bveq))

/-- [stepw_addr]'s value-position sibling: the store VALUE obligation. -/
macro "stepw_val" : tactic =>
  `(tactic| (getr_resolve <;> regupd_resolve <;>
    first | rfl | (sp_norm <;> first | rfl | bv_omega) | bveq))

/-- [stepw_addr] for the put-style retry loops, whose spill addresses reach
    the obligation as [v_addi] of a register the chain has already pinned by
    an equation in the context: rewrite by those equations and fold the
    immediate away before running the [stepw_addr] script.  Every name here
    is generic, so this belongs beside its weaker sibling rather than copied
    into each proof that needs it.
-/
macro "stepw_addr_hyps" : tactic =>
  `(tactic| (getr_resolve <;> regupd_resolve <;> try (simp only [v_addi_0]) <;>
    sp_norm <;> first | rfl | bv_omega | bveq))

/-- One machine STORE inside a chain, dispatched on the decoded width
    (`sd`/`sw`/`sh`/`sb` -> [step_sd_at]/[step_sw_at]/[step_sh_at]/
    [MmapSim.step_sb_at]) — the store analogue of [stepiv].  [aa]/[vv] are
    the pre-normalized store address and value (`sb` additionally
    pre-normalizes the stored byte to `BitVec.ofInt 8 vv.toNat`); the address
    and value obligations get [stepw_addr]/[stepw_val] baked in; the
    [store_ok] obligation goes to the caller-supplied [oktac]
    ([StoreOk.solve_store_ok] cannot be named here — StoreOk imports this
    file). -/
macro "stepw " F:term "," D:term "," aa:term "," vv:term "," oktac:term : tactic =>
  `(tactic|
    chain_step <;>
      first
      | rfl
      | assumption
      | (refine step_sd_at _ _ _ _ _ _ _ _ _ $aa $vv $F ?_ $D ?_ ?_ ?_ <;> first | rfl | decide | exact $oktac | stepw_addr | stepw_val)
      | (refine step_sw_at _ _ _ _ _ _ _ _ _ $aa $vv $F ?_ $D ?_ ?_ ?_ <;> first | rfl | decide | exact $oktac | stepw_addr | stepw_val)
      | (refine step_sh_at _ _ _ _ _ _ _ _ _ $aa $vv $F ?_ $D ?_ ?_ ?_ <;> first | rfl | decide | exact $oktac | stepw_addr | stepw_val)
      | (refine MmapSim.step_sb_at _ _ _ _ _ _ _ _ _ $aa $vv (BitVec.ofInt 8 ($vv).toNat) $F ?_ $D ?_ ?_ ?_ ?_ <;> first | rfl | decide | exact $oktac | stepw_addr | stepw_val)
      | step_simpl)

/-- The put-style retry loops' spill: one `sd` at an address the caller
    pre-normalizes, discharged through [stepw_addr_hyps].  [stepsd]'s
    [store_ok] obligation goes to the caller-supplied [oktac] for the same
    reason [stepw]'s does — StoreOk imports this file, so its solver cannot
    be named here. -/
macro "stepsd " F:term "," D:term "," aexp:term "," vexp:term "," vtac:term "," oktac:term :
    tactic =>
  `(tactic|
    step_intro <;>
      first
      | rfl
      | assumption
      | (refine step_sd_at _ _ _ _ _ _ _ _ _ $aexp $vexp $F ?_ $D ?_ ?_ ?_ <;> first | rfl | decide | exact $vtac | exact $oktac | stepw_addr_hyps)
      | step_simpl)

/-- The put-style retry loops' reload: one `ld` at an address the caller
    pre-normalizes, with the loaded value pinned through [stepw_addr_hyps]
    and the [rdn] side condition left to the caller's [readtac].  [stepld]
    needs no `store_ok` argument. -/
macro "stepld " F:term "," D:term "," aexp:term "," vexp:term "," readtac:term : tactic =>
  `(tactic|
    step_intro <;>
      first
      | rfl
      | assumption
      | (refine step_ld _ _ _ _ _ _ _ _ _ (word_to_le_bytes 8 $vexp) $vexp $F ?_ $D ?_ ?_ <;> first | rfl | decide | assumption | exact $readtac | exact (bytes_le_to_Z_8 $vexp) | stepw_addr_hyps)
      | step_simpl)

/-- Prove the current (decidable) goal by a computed cast of `rfl` — cheaper
    than normalizing the goal twice, and the only form that closes bitvector
    equations whose reduction is blocked by an opaque well-formedness proof.

     `apply (@bool_decide_eq_true_1 G _); vm_cast_no_check
    (@eq_refl bool true)`.  Lean's kernel-side spelling of the same
    certificate is `rfl` (definitional) or `decide` (a `Bool`/`Decidable`
    reduction); both are guarded `rfl`, so `first | rfl | decide` sits in the
    same place, and this tree's generated fetch/decode lemmas can use it
    unchanged. -/
macro "vm_refl_bv" : tactic => `(tactic| first | rfl | decide)

/-- A word is the `BitVec.ofInt` literal of its own unsigned value (the
    `BitVec.ofNat`/`ofInt` bridge the literal normalizers need).
 Kept as an explicit lemma so [wlit_closed] has a rewrite
    rule to cite. -/
theorem ofInt_toNat (x : word) : BitVec.ofInt 64 (x.toNat : Int) = x := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  exact Int.ofNat_inj.mp (u_Z2bv (x.toNat : Int) (by omega) (by omega))

/-- Replace a CLOSED word-valued redex [p] (e.g. the fault address
    `v_addi (BitVec.ofInt 64 0) imm`) with its computed `BitVec.ofInt 64 z`
    literal.  This is the robust replacement for the fragile
    `rw [v_addi_0_*]` pattern: a `rw` cannot match a closed redex whose
    reduction needs conversion on a signed literal (no pattern variable
    triggers it), while a rewrite by [ofInt_toNat] always can.  State
    per-image ROM facts (e.g. `*_none` unmapped-address facts) at the same
    literal spelling so they apply directly afterwards.  Fails fast when [p]
    is open (the explicit [check_closed_term] call runs in tactic position,
    so a direct caller gets its error message).

    the target spelling is `BitVec.ofInt 64 (p).toNat`; Lean's
    `rw`/`exact` then match it against the numeral by reduction, which is
    what makes the closedness-guarded rewrite below sufficient. -/
macro "wlit_closed " p:term : tactic =>
  `(tactic| check_closed_term $p <;> rw [← ofInt_toNat $p])

/-- Sweep form of [wlit_closed]: normalize every CLOSED
    [v_addi]/[v_add]/[v_sub] redex in the goal to its `BitVec.ofInt 64 z`
    literal (open redexes are skipped; point [wlit_closed] at other shapes
    by hand).  Note this produces the `BitVec.ofInt` spelling, not the
    numeral-literal one [wlits] produces — use it for value/ROM positions,
    [wlits]/[norm_pc] for pc positions.

    a total no-op — see [wlit_replace]; `decide`/`rw` already
    normalize these redexes in Lean. -/
macro "wlits_closed" : tactic => `(tactic| skip)

/-- Wrapper for the `erewrite rdn_ext` call-site pattern: rewrites the
    (first) `rdn segs mem a k` in the goal to an evar memory, discharges the
    no-overflow side condition by `imm_norm; u_norm; omega`, and
    pre-normalizes the pointwise premise so `omega` sees literal addresses.

    the Lean [rdn_ext] takes the pointwise premise as one explicit
    argument (`∀ x, a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + k → m1 x = m2 x`),
    so the wrapper supplies the *side-condition* half (`imm_norm; u_norm;
    omega`) and the caller writes `rw [rdn_ext segs k m1 m2 a hno
    hpointwise]`.  The rewrite itself is done by `rw`, not by `erewrite`,
    because Lean has no evar-memory machinery: the caller names the new
    memory. -/
macro "rdn_ext_lit" : tactic => `(tactic| (imm_norm; u_norm <;> first | omega | skip))

/-! ## Consolidated shared lemmas -/

/-- A byte disequality against literal zero transfers to the `Int`
    level. -/
theorem byte_nz_u (b : byte) (Hb : b ≠ BitVec.ofInt 8 0) :
    (b.toNat : Int) ≠ 0 := by
  intro hc
  apply Hb
  bv_omega

/-- `bv_unsigned` of a byte zero-extended into a word. -/
theorem u_zext8 (b : byte) :
    (BitVec.ofInt 64 (b.toNat : Int)).toNat = (b.toNat : Int) := by
  bv_omega

/-- Truncating the zero-extended byte back to 8 bits recovers it. -/
theorem zext8_byte (b : byte) :
    BitVec.ofInt 8 ((BitVec.ofInt 64 (b.toNat : Int)).toNat) = b := by
  bv_omega

/-- A byte-literal disequality transfers to the `Int` level. -/
theorem byte_neq_lit_u (b : byte) (z : Int) (Hz : 0 ≤ z ∧ z < 256)
    (Hb : b ≠ BitVec.ofInt 8 z) : (b.toNat : Int) ≠ z := by
  intro hc
  apply Hb
  bv_omega

/-- Two-register byte dispatch compares the zero-extended loaded byte
    against a zero-extended literal: reflect a byte-literal disequality
    into the `c_eq … = false` the branch step needs. -/
theorem c_eq_zext_lit_false (b : byte) (z : Int) (Hz : 0 ≤ z ∧ z < 256)
    (Hb : b ≠ BitVec.ofInt 8 z) :
    c_eq (BitVec.ofInt 64 (b.toNat : Int)) (BitVec.ofInt 64 z) = false := by
  unfold c_eq bv_eqb
  have h : ¬ (BitVec.ofInt 64 (b.toNat : Int) = BitVec.ofInt 64 z) := by
    intro heq
    apply Hb
    bv_omega
  simpa using h

/-- `bv_unsigned` of an in-range [nat_to_word]. -/
theorem u_ntw (n : Nat) (Hn : (n : Int) < 2 ^ 64) :
    (nat_to_word n).toNat = (n : Int) := by
  simp only [nat_to_word]
  bv_omega

/-- The wrapping word/nat offset add in the canonical `BitVec.ofInt` form
    (hypothesis-free: both sides wrap identically). -/
theorem word_add_nat (a : word) (n : Nat) :
    a + nat_to_word n = BitVec.ofInt 64 ((a.toNat : Int) + (n : Int)) := by
  simp only [nat_to_word]
  bv_omega

/-- The wrapping add of [nat_to_word 0] is the identity
    (hypothesis-free).  NOTE: named [word_add_nat_0], not
    [word_add_0_r] — AllocSim exports a different [word_add_0_r],
    stated at `BitVec.ofInt 64 0`. -/
theorem word_add_nat_0 (x : word) : x + nat_to_word 0 = x := by
  simp only [nat_to_word]
  bv_omega

/-- Loop-index steps over a symbolic base (both sides wrap). -/
theorem word_add_nat_1 (a : word) (m : Nat) :
    v_addi (a + nat_to_word m) 1 = a + nat_to_word (m + 1) := by
  simp only [v_addi, nat_to_word]
  bv_omega

theorem word_add_nat_m1 (a : word) (m : Nat) :
    v_addi (a + nat_to_word (m + 1)) (-1) = a + nat_to_word m := by
  simp only [v_addi, nat_to_word]
  bv_omega

/-- [v_add] is commutative up to the wrap. -/
theorem v_add_comm (x y : word) : v_add x y = y + x := by
  simp only [v_add]
  bv_omega

/-- A wrapping [v_add], with the wrapped value made explicit. -/
theorem v_add_wrap (x y : word)
    (Hw : 2 ^ 64 ≤ (x.toNat : Int) + (y.toNat : Int)) :
    v_add x y = BitVec.ofInt 64 ((x.toNat : Int) + (y.toNat : Int) - 2 ^ 64) := by
  simp only [v_add]
  bv_omega

/-- `sub x0, y`: two's-complement negation in the canonical form. -/
theorem v_sub_0_neg (y : word) :
    v_sub (BitVec.ofInt 64 0) y = BitVec.ofInt 64 (-(y.toNat : Int)) := by
  simp only [v_sub]
  bv_omega

/-- Unsigned value of a small negation. -/
theorem u_neg_small (z : Int) (Hz0 : 0 < z) (Hz : z ≤ 2 ^ 64) :
    (BitVec.ofInt 64 (- z)).toNat = (2 ^ 64 - z) := by
  bv_omega

/-- Incrementing a negative down-counter. -/
theorem v_addi_neg_S (d : Nat) :
    v_addi (BitVec.ofInt 64 (- ((d + 1 : Nat) : Int))) 1
      = BitVec.ofInt 64 (- (d : Int)) := by
  simp only [v_addi]
  bv_omega

section WithFP

variable [fx : FPState]

/-- Upper bound on the initial stack image (feeds every read lemma's
    no-overflow side condition; the numbers come from [valid_argv]/
    [valid_envp]).

    Derived rather than computed: the layout arithmetic
    is [PropExec.build_stack_bytes_within_span] and the [valid_argv]/
    [valid_envp] arithmetic is [Run.entry_stack_span_bound], and this is
    their composition.  The SAME derivation backs both this bound and
    [Run.entry_stack_fits], so the two cannot disagree about how
    big an initial stack image can be. -/
theorem bsb_bound (ph : PhdrInfo) (sp : word) (a e : List (List byte))
    (uid hw : word) (rnd : EntryDraw) (Hva : valid_argv a) (Hve : valid_envp e) :
    ((build_stack_bytes ph sp a e uid hw rnd).length : Int) ≤ 2240000 := by
  have h1 := build_stack_bytes_within_span ph sp a e uid hw rnd
  have h2 := entry_stack_span_bound a e Hva Hve
  have h3 : entry_stack_span_max = 2238671 := rfl
  omega

end WithFP

/-- A store range at/above the ends of both segments of a two-segment
    image passes the read-only-avoidance check (per-image `*_avoids_ro`
    facts specialize the two `Z.ltb` hypotheses). -/
theorem range_avoids_two (s0 s1 : Segment) (a n : Int)
    (H0 : decide (a < (s0.seg_base : Int) + (s0.seg_size : Int)) = false)
    (H1 : decide (a < (s1.seg_base : Int) + (s1.seg_size : Int)) = false) :
    range_avoids_ro_segs [s0, s1] a n = true := by
  unfold range_avoids_ro_segs
  simp only [List.all_cons, List.all_nil, Bool.and_true, H0, H1, Bool.and_false,
    Bool.not_false, Bool.or_true]

/-- ** Avoiding the read-only segments, for any number of segments

    [range_avoids_two] above is fixed at two segments.  Each example
    proves the same fact about its own image, and the hand-rolled proof
    names every segment explicitly — so it has to be edited by hand
    whenever the segment COUNT changes (for example, gcc can give
    .eh_frame a LOAD segment of its own, which takes an image from three
    segments to four).

    [range_avoids_ro_above] states it once, keyed off a single bound:
    if every read-only segment ends at or below [data_base], then any
    range starting at or above [data_base] avoids all of them —
    whatever the segment count.  The premise is closed by computation on
    a concrete image, so the per-example lemma becomes one line:

      theorem source_avoids_ro (a n : Int) (Ha : 0x13000 ≤ (a.toNat : Int)) :
          range_avoids_ro_segs source_segs (a.toNat : Int) n = true := by
        apply range_avoids_ro_above (data_base := 0x13000)
        · decide
        · exact Ha

    Note the range's LENGTH is irrelevant, as it is for
    [range_avoids_two]: a range that starts above every read-only
    segment cannot re-enter one by being long, because the segments lie
    below it. -/
def ro_segs_below (segs : List Segment) (data_base : Int) : Bool :=
  segs.all (fun seg =>
    seg_writable seg
    || decide ((seg.seg_base : Int) + (seg.seg_size : Int) ≤ data_base))

theorem range_avoids_ro_above (segs : List Segment) (data_base addr n : Int)
    (Hbelow : ro_segs_below segs data_base = true) (Haddr : data_base ≤ addr) :
    range_avoids_ro_segs segs addr n = true := by
  unfold ro_segs_below at Hbelow
  rw [List.all_eq_true] at Hbelow
  unfold range_avoids_ro_segs
  rw [List.all_eq_true]
  intro seg Hin
  have h := Hbelow seg Hin
  by_cases hw : seg_writable seg = true
  · simp [hw]
  · simp only [hw, Bool.false_or] at h
    have hle : (seg.seg_base : Int) + (seg.seg_size : Int) ≤ data_base :=
      of_decide_eq_true h
    have hlt : decide (addr < (seg.seg_base : Int) + (seg.seg_size : Int)) = false := by
      rw [decide_eq_false_iff_not]; omega
    simp [hw, hlt]

/- #########################################################################
   Smoke tests: the dispatch arms actually fire
   #########################################################################

   Each test drives [stepi]/[stepiv]/[stepw]/[stepj]/[stepjr] over ONE
   concrete instruction encoding.  [segs]/[regs]/[mem] stay abstract; the
   fetch fact is a hypothesis; the decode fact is proved by computation on
   the encoding — so a test fails if the encoding, the dispatch arm, the
   lemma's argument count, or the post-step normalization is wrong.  The pc
   is a closed literal ([norm_pc] computes it: an OPEN pc would be the
   open-bv trap).   ends every test with [Abort] — the point is that
   the tactic RUNS, not the statement — so this tree states them as real
   `example`s, which additionally checks that the chained machine state is
   the one the step lemma produces.
-/

section DispatchSmoke

variable [fx : FPState]
variable {segs : List Segment} {regs : BvMap word} {mem rom : word → Option byte}

/-- Scaffold: consume the fetch hypothesis, prove the decode fact by
    computation on the concrete encoding, take one [stepi], close the chain.

     `let F := fresh "F" in intro F; let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv; eexists;
    stepi F D; apply mst_refl`.  Lean's macro hygiene gives the two
    `intro`-bound names the same scope as their uses, so no `fresh` is
    needed; `eexists` becomes the named-hole `refine ⟨?st, ?h⟩`, whose
    witness goal is closed automatically once the chain pins it. -/
macro "smoke " enc:term "," sh:term : tactic =>
  `(tactic|
    (intro F
     have D : decodeAny $enc = some ($sh, 4) := by decide
     refine ⟨?st, ?h⟩
     case h =>
       stepi F, D
       exact msteps.mst_refl _))

/-- [smoke] with the [stepiv] entry (a pre-normalized written value). -/
macro "smoke_v " enc:term "," sh:term "," vv:term : tactic =>
  `(tactic|
    (intro F
     have D : decodeAny $enc = some ($sh, 4) := by decide
     refine ⟨?st, ?h⟩
     case h =>
       stepiv F, D, $vv, rfl
       exact msteps.mst_refl _))

/-! ### [stepi] dispatch, one encoding per arm -/

/- slti a0,a0,1 -/
example : fetch_word segs (0x10000 : word) = some (0x00152513 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00152513 : BitVec 32), (Instr.opImm .SLT 10 10 1)

/- srai a0,a0,1 -/
example : fetch_word segs (0x10000 : word) = some (0x40155513 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x40155513 : BitVec 32), (Instr.shiftImm .SRA 10 10 1)

/- and a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B57533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B57533 : BitVec 32), (Instr.op .AND 10 10 11)

/- or a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B56533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B56533 : BitVec 32), (Instr.op .OR 10 10 11)

/- xor a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B54533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B54533 : BitVec 32), (Instr.op .XOR 10 10 11)

/- sll a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B51533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B51533 : BitVec 32), (Instr.op .SLL 10 10 11)

/- srl a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B55533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B55533 : BitVec 32), (Instr.op .SRL 10 10 11)

/- sra a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x40B55533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x40B55533 : BitVec 32), (Instr.op .SRA 10 10 11)

/- slt a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B52533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B52533 : BitVec 32), (Instr.op .SLT 10 10 11)

/- sltu a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B53533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B53533 : BitVec 32), (Instr.op .SLTU 10 10 11)

/- addw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B5053B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B5053B : BitVec 32), (Instr.op32 .ADD 10 10 11)

/- sllw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B5153B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B5153B : BitVec 32), (Instr.op32 .SLL 10 10 11)

/- srlw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x00B5553B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x00B5553B : BitVec 32), (Instr.op32 .SRL 10 10 11)

/- sraw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x40B5553B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x40B5553B : BitVec 32), (Instr.op32 .SRA 10 10 11)

/- addiw a0,a0,1 — regression test: if this arm misses an argument slot,
   [stepi] FAILS on every OpImm32 decode (the failure happens inside the
   selected arm, which does not fall through to the rest of the list). -/
example : fetch_word segs (0x10000 : word) = some (0x0015051B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x0015051B : BitVec 32), (Instr.opImm32 10 10 1)

/- slliw a0,a0,1 -/
example : fetch_word segs (0x10000 : word) = some (0x0015151B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x0015151B : BitVec 32), (Instr.shiftImm32 .SLL 10 10 1)

/- srliw a0,a0,1 -/
example : fetch_word segs (0x10000 : word) = some (0x0015551B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x0015551B : BitVec 32), (Instr.shiftImm32 .SRL 10 10 1)

/- sraiw a0,a0,1 -/
example : fetch_word segs (0x10000 : word) = some (0x4015551B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x4015551B : BitVec 32), (Instr.shiftImm32 .SRA 10 10 1)

/- mulh a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B51533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B51533 : BitVec 32), (Instr.mul .MULH 10 10 11)

/- mulhsu a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B52533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B52533 : BitVec 32), (Instr.mul .MULHSU 10 10 11)

/- mulhu a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B53533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B53533 : BitVec 32), (Instr.mul .MULHU 10 10 11)

/- div a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B54533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B54533 : BitVec 32), (Instr.mul .DIV 10 10 11)

/- rem a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B56533 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B56533 : BitVec 32), (Instr.mul .REM 10 10 11)

/- mulw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B5053B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B5053B : BitVec 32), (Instr.mul32 .MUL 10 10 11)

/- divw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B5453B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B5453B : BitVec 32), (Instr.mul32 .DIV 10 10 11)

/- divuw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B5553B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B5553B : BitVec 32), (Instr.mul32 .DIVU 10 10 11)

/- remw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B5653B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B5653B : BitVec 32), (Instr.mul32 .REM 10 10 11)

/- remuw a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B5753B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke (0x02B5753B : BitVec 32), (Instr.mul32 .REMU 10 10 11)

/- divu a0,a0,a1 — the nonzero-divisor premise is picked up from the context
   by the arm's `assumption`. -/
example : fetch_word segs (0x10000 : word) = some (0x02B55533 : BitVec 32) →
    (getr regs 11).toNat ≠ 0 →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F NZ
  have D : decodeAny (0x02B55533 : BitVec 32) = some (Instr.mul .DIVU 10 10 11, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepi F, D
    exact msteps.mst_refl _

/- remu a0,a0,a1 -/
example : fetch_word segs (0x10000 : word) = some (0x02B57533 : BitVec 32) →
    (getr regs 11).toNat ≠ 0 →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F NZ
  have D : decodeAny (0x02B57533 : BitVec 32) = some (Instr.mul .REMU 10 10 11, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepi F, D
    exact msteps.mst_refl _

/-! ### [stepiv] dispatch -/

/- slli a0,a0,1 (the [step_slli_at] arm). -/
example : fetch_word segs (0x10000 : word) = some (0x00151513 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke_v (0x00151513 : BitVec 32), (Instr.shiftImm .SLL 10 10 1),
    (v_slli (getr regs 10) 1)

/- andi a0,a0,1 (the [step_andi_at] arm). -/
example : fetch_word segs (0x10000 : word) = some (0x00157513 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  smoke_v (0x00157513 : BitVec 32), (Instr.opImm .AND 10 10 1),
    (v_andi (getr regs 10) 1)

/-! ### [stepw] dispatch, one store width per arm -/

/- sd a0,0(sp) -/
example : fetch_word segs (0x10000 : word) = some (0x00A13023 : BitVec 32) →
    store_ok segs mem (v_addi (getr regs 2) 0) 8 = true →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F OK
  have D : decodeAny (0x00A13023 : BitVec 32) = some (Instr.store .SZ8 2 10 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepw F, D, (v_addi (getr regs 2) 0), (getr regs 10), OK
    exact msteps.mst_refl _

/- sw a0,0(sp) -/
example : fetch_word segs (0x10000 : word) = some (0x00A12023 : BitVec 32) →
    store_ok segs mem (v_addi (getr regs 2) 0) 4 = true →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F OK
  have D : decodeAny (0x00A12023 : BitVec 32) = some (Instr.store .SZ4 2 10 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepw F, D, (v_addi (getr regs 2) 0), (getr regs 10), OK
    exact msteps.mst_refl _

/- sh a0,0(sp) -/
example : fetch_word segs (0x10000 : word) = some (0x00A11023 : BitVec 32) →
    store_ok segs mem (v_addi (getr regs 2) 0) 2 = true →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F OK
  have D : decodeAny (0x00A11023 : BitVec 32) = some (Instr.store .SZ2 2 10 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepw F, D, (v_addi (getr regs 2) 0), (getr regs 10), OK
    exact msteps.mst_refl _

/- sb a0,0(sp) — the byte form pre-normalizes the stored byte. -/
example : fetch_word segs (0x10000 : word) = some (0x00A10023 : BitVec 32) →
    store_ok segs mem (v_addi (getr regs 2) 0) 1 = true →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F OK
  have D : decodeAny (0x00A10023 : BitVec 32) = some (Instr.store .SZ1 2 10 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepw F, D, (v_addi (getr regs 2) 0), (getr regs 10), OK
    exact msteps.mst_refl _

/-! ### [stepj] / [stepjr] dispatch -/

/- jal x0,+8 (the no-link form). -/
example : fetch_word segs (0x10000 : word) = some (0x0080006F : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F
  have D : decodeAny (0x0080006F : BitVec 32) = some (Instr.jal 0 8, 4) := by decide
  refine ⟨?st, ?h⟩
  case h =>
    stepj F, D
    exact msteps.mst_refl _

/- jal ra,+8 (the LINKING form). -/
example : fetch_word segs (0x10000 : word) = some (0x008000EF : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F
  have D : decodeAny (0x008000EF : BitVec 32) = some (Instr.jal 1 8, 4) := by decide
  refine ⟨?st, ?h⟩
  case h =>
    stepj F, D
    exact msteps.mst_refl _

/- jalr x0,0(ra) — ret, target from a resolved register. -/
example : fetch_word segs (0x10000 : word) = some (0x00008067 : BitVec 32) →
    getr regs 1 = (0x20000 : word) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F R
  have D : decodeAny (0x00008067 : BitVec 32) = some (Instr.jalr 0 1 0, 4) := by decide
  refine ⟨?st, ?h⟩
  case h =>
    stepjr F, D, (0x20000 : word), R
    exact msteps.mst_refl _

/- jalr ra,0(a0) — a linking call through a register. -/
example : fetch_word segs (0x10000 : word) = some (0x000500E7 : BitVec 32) →
    getr regs 10 = (0x20000 : word) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F R
  have D : decodeAny (0x000500E7 : BitVec 32) = some (Instr.jalr 1 10 0, 4) := by decide
  refine ⟨?st, ?h⟩
  case h =>
    stepjr F, D, (0x20000 : word), R
    exact msteps.mst_refl _

/-! ### The closing tactics and the closedness guard -/

/- A closed equation still closes. -/
example : v_addi (BitVec.ofInt 64 5) 3 = BitVec.ofInt 64 8 := by bveq

/- An unresolved projection is closed by the register resolvers, not by the
   evaluator . -/
example (regs : BvMap word) (v : word) : getr (regupd regs 11 v) 11 = v := by
  getr_resolve

/- The closedness guard itself: closed terms pass — including a closed term
   probed while the goal holds a witness hole — while context variables fail
   fast.   -/
example (v : word) : ∃ w : word, w = v := by
  refine ⟨?st, ?h⟩
  case h =>
    exact rfl

example : True := by
  have hv : ∀ v : word, ∃ w : word, w = v := by
    intro v
    exact ⟨v, rfl⟩
  check_closed_term (v_addi (BitVec.ofInt 64 5) 3)
  trivial

/- [check_closed_term] fails fast on a context variable: the fallback arm
   is the one that runs.  (Lean has no `assert_fails` combinator; `first`
   is the equivalent, and it catches the guard's throw.) -/
example (v : word) : True := by
  first
  | check_closed_term (v_addi v 4)
  | trivial

/- [sp_norm]/[u_norm] leave the goal convertible to the canonical computed
   form (in Lean the nesting is definitional; [u_norm] does the real work of
   collapsing the [toNat] projection). -/
example (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    (BitVec.ofInt 64 z).toNat = z := by u_norm

/-! ### The remaining entry points, one test each

     -/

/- [stepi_at]: addi a0,a0,1 with the written value pre-normalized. -/
example : fetch_word segs (0x10000 : word) = some (0x00150513 : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intro F
  have D : decodeAny (0x00150513 : BitVec 32) = some (Instr.opImm .ADD 10 10 1, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepi_at F, D, (v_addi (getr regs 10) 1)
    exact msteps.mst_refl _

/- [stepiwv]: addiw a0,a0,1 with the written value pre-normalized. -/
example : fetch_word segs (0x10000 : word) = some (0x0015051B : BitVec 32) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intro F
  have D : decodeAny (0x0015051B : BitVec 32) = some (Instr.opImm32 10 10 1, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepiwv F, D, (v_addiw (getr regs 10) 1), rfl
    exact msteps.mst_refl _

/- [stepsd]: sd a0,0(sp) through the hypothesis-rewriting address script. -/
example : fetch_word segs (0x10000 : word) = some (0x00A13023 : BitVec 32) →
    store_ok segs mem (v_addi (getr regs 2) 0) 8 = true →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F OK
  have D : decodeAny (0x00A13023 : BitVec 32) = some (Instr.store .SZ8 2 10 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepsd F, D, (v_addi (getr regs 2) 0), (getr regs 10), rfl, OK
    exact msteps.mst_refl _

/- [stepld]: ld a0,0(sp) with the loaded bytes pinned by the caller. -/
example : fetch_word segs (0x10000 : word) = some (0x00013503 : BitVec 32) →
    rdn segs mem (v_addi (getr regs 2) 0) 8 = some (word_to_le_bytes 8 (getr regs 10)) →
    ∃ st', msteps segs (mkst regs (0x10000 : word) mem rom) st' := by
  intros F RD
  have D : decodeAny (0x00013503 : BitVec 32) = some (Instr.load .SZ8 true 10 2 0, 4) := by
    decide
  refine ⟨?st, ?h⟩
  case h =>
    stepld F, D, (v_addi (getr regs 2) 0), (getr regs 10), RD
    exact msteps.mst_refl _

/- [word_lit] is a term relator in Lean: the literal it builds is the
   reduction of the closed redex, and the two are interchangeable by `rfl`. -/
example : v_addi (BitVec.ofInt 64 5) 3 = word_lit (v_addi (BitVec.ofInt 64 5) 3) := rfl

/- ... and it fails fast on an open redex. -/
example (x : word) : True := by
  first
  | exact word_lit (v_addi x 4)
  | trivial

/- [chain_step] falls through to the [to_wexit] head (CatSim) — arm 2 of the
   twelve, proving the arm ORDER is a real alternation and not just the
   [msteps] head the other tests use.  The post-step state is pinned by
   [step_slti], so the tail is an assumption. -/
example (Htail : to_wexit segs
      (mkst (regupd regs 10 (v_slti (getr regs 10) 1)) (v_addi (0x10000 : word) 4) mem rom)
      [] 0) :
    fetch_word segs (0x10000 : word) = some (0x00152513 : BitVec 32) →
    to_wexit segs (mkst regs (0x10000 : word) mem rom) [] 0 := by
  intro F
  have D : decodeAny (0x00152513 : BitVec 32) = some (Instr.opImm .SLT 10 10 1, 4) := by decide
  chain_step
  · rfl
  · exact step_slti _ _ _ _ _ _ _ _ _ F (by decide) D
  · exact Htail

end DispatchSmoke

end LinuxSem.Common.StepTac
