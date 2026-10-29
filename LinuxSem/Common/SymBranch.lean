/-
  * Common.SymBranch — closing [SymExec]'s [SCBr] obligations.

  EXPLORATION / PROTOTYPE.  Image-INDEPENDENT proof library; nothing
  here is part of the trusted specification.

  [Common/SymTac]'s [sym_block] takes a branch SCRIPT (one [bool] per
  [Branch] the run meets) and turns every entry into an [SCBr]
  obligation, so no direction is ever assumed.  For a straight line
  with no input-dependent control flow — [modprint_ns], the file the
  combined stack was first exercised on — that list is EMPTY and this
  file would not exist.

  The moment a binary branches on [argc], on a parsed value, or on a
  loop counter, every block leaves one such obligation per branch, in
  one of exactly three spellings:

    [bv_lts a b = d]   (blt/bge)
    [bv_ltu a b = d]   (bltu/bgeu)
    [bv_eqb a b = d]   (beq/bne, and the [beqz]/[bnez] aliases)

  All three are [Int] comparisons under a [BitVec.toInt]/[(·.toNat : Int)]
  wrapper, and the caller invariably has the [Int] facts already
  (`(argcN.toNat : Int) = (av.length : Int)`, a loop bound, a window
  bound).  What is missing is only the step from [BitVec.toInt] to
  [BitVec.toNat]: `omega` treats `x.toInt` and `x.toNat` as UNRELATED
  atoms, so a goal about a [blt] cannot see a hypothesis about `x.toNat`.

  [bv_signed_small] is that step, and [sym_br] is the whole closer:
  push the comparison down to [Int], drop the [toInt] wrapper on
  every operand small enough for it (which is decided by the caller's
  own bounds, through `omega`), and hand what is left to `omega`.  In
  the example proofs that is a one-line discharge of every branch.

  * The  file has no section: every declaration is stated at
    `word`/`bool` only.  This tree carries one `variable [fx : FPState]`
    because two lemmas it cites — `u64_range` and `v_addiw`'s companion
    facts — live in an `[FPState]` section in [Common.PropExec] (that is
    this tree's standing convention for `Section WithFP…`, see
).  Nothing in this file's STATEMENTS mentions the FP
    state.
  * `sym_br` is an `Ltac` , so it is a Lean `macro` here.  The
    one systematic deviation is in HOW the `by lia` side conditions of
    its rewrites are discharged.   rewrites with
    `bv_signed_lit`/`bv_signed_small`/`v_addiw_range` and proves each
    side condition with `lia` DURING the rewrite.  A Lean `rw` must
    elaborate its lemma term — side-condition holes included — BEFORE
    it knows which subterm it will match, so `rw [bv_signed_small _ (by
    omega)]` cannot work.     The effect is the same one-line discharge; the side conditions are
    simply materialised as hypotheses instead of being discharged inside
    the rewrite.  [bv_signed_lit] and [v_addiw_range] are still exported
    under their  statements so a proof that wants to REASON
    about a branch can name them.
 `bv_ltu_Z` likewise bridges Nat-`<` to
    Int-`<`.
  Word hygiene: this file contains no proof hole and no extra postulate.
-/
import LinuxSem.Common.StepTac
import LinuxSem.Common.PropExec
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.Riscv.Prelude

set_option autoImplicit false
-- Same rationale as `PropExec`/`CatExec`/`SeqExec`: -- Lean only puts a section variable into a lemma's type when the statement
-- mentions it, so the linters below flag exactly that (and unused `simp`
-- hints), which would make the typecheck non-silent.
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LinuxSem.Common.SymBranch

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Common.PropExec
open LinuxSem.Common.StepTac

section WithFP

variable [fx : FPState]

/-! ## The one fact in the file -/

/-- Below `2^63` the signed and unsigned readings agree.  This is the
    only fact in the file; everything else is `omega`.
 This tree states it
    as `(x.toInt : Int) = (x.toNat : Int)`, which is the same statement
    with the two projections expanded; the proof goes through
    [BitVec.toInt]'s defining conditional (`Int.bmod_def` is the same
    `if`, in `Int` form), so no `bv_swrap_small` chain is needed.
-/
theorem bv_signed_small (x : word) (Hx : (x.toNat : Int) < 2 ^ 63) :
    (x.toInt : Int) = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_def]
  split <;> omega

/-- [BitVec.toInt] written as the defining conditional, with NO side
    condition: the "drop the wrapper" step of [sym_br], in the shape a
    Lean rewrite can match before it knows its operand.

    declaration (see the module header's `sym_br` note). -/
theorem bv_signed_cond (x : word) :
    x.toInt = if 2 * x.toNat < 2 ^ 64 then (x.toNat : Int)
      else (x.toNat : Int) - 2 ^ 64 := rfl

/-- The three comparisons, as [Int] comparisons.  Stated separately from
    the tactic so that a proof that wants to REASON about a branch (a
    loop invariant that has to name the exit condition) can rewrite with
    them instead of discharging a goal. -/
theorem bv_lts_small (a b : word) (Ha : (a.toNat : Int) < 2 ^ 63)
    (Hb : (b.toNat : Int) < 2 ^ 63) :
    bv_lts a b = decide ((a.toNat : Int) < (b.toNat : Int)) := by
  unfold bv_lts
  rw [bv_signed_small a Ha, bv_signed_small b Hb]

/-- [bv_lts] is a `decide` over [BitVec.toInt], definitionally.   -/
theorem bv_lts_Z (a b : word) : bv_lts a b = decide (a.toInt < b.toInt) := rfl

/-- [bv_ltu] is `Z.ltb` of the unsigned readings . -/
theorem bv_ltu_Z (a b : word) :
    bv_ltu a b = decide ((a.toNat : Int) < (b.toNat : Int)) := by
  unfold bv_ltu
  rw [decide_eq_decide]
  exact Int.ofNat_lt.symm

/-- [bv_eqb] is `Z.eqb` of the unsigned readings.   -/
theorem bv_eqb_Z (a b : word) :
    bv_eqb a b = decide ((a.toNat : Int) = (b.toNat : Int)) := by
  unfold bv_eqb
  rw [show (a == b) = decide (a = b) from by
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]]
  rw [decide_eq_decide]
  constructor
  · intro h; rw [h]
  · intro h; exact BitVec.eq_of_toNat_eq (by omega)

/-- Negative operands: a [blt] against a literal like [-9] (the [div]
    round-toward-zero fixup a signed division compiles to) has a
    [BitVec.toInt] that is NOT the unsigned reading.  One rewrite handles
    the literal side. -/
theorem bv_signed_lit (z : Int) (Hz : -2 ^ 63 ≤ z ∧ z < 2 ^ 63) :
    (BitVec.ofInt 64 z).toInt = z := by
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  split <;> omega

/-- [addiw] with a NEGATIVE immediate.  [SeqExec.v_addiw_small] carries
    an unused [0 <= imm] hypothesis, so it does not apply to the
    [addiw s1,a0,-2] every [argc]-relative index computation compiles
    to.  Same proof, without that hypothesis; the existing lemma is left
    alone. -/
theorem v_addiw_range (x : word) (imm : Int)
    (Hlo : 0 ≤ (x.toNat : Int) + imm) (Hhi : (x.toNat : Int) + imm < 2 ^ 31) :
    ((v_addiw x imm).toNat : Int) = (x.toNat : Int) + imm := by
  unfold v_addiw
  rw [BitVec.toNat_ofInt]
  have hb : bv_swrap 32 ((x.toNat : Int) + imm) = (x.toNat : Int) + imm := by
    unfold bv_swrap
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.add_sub_cancel]
  rw [hb]
  rw [show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl]
  rw [Int.emod_eq_of_lt (by omega) (by have := u64_range x; omega),
    Int.toNat_of_nonneg (by omega)]

/-- [v_addiw_range] as an UNCONDITIONAL `if`-equation, so [sym_br] can
    rewrite before it knows the operand.  In the false branch the value is
    [v_addiw]'s own definition (which is what `rfl` closes), so the rule
    terminates — the branch hypothesis `¬(bounds)` is the side condition
    `omega` will refute from the caller's bounds.

    declaration (see the module header's `sym_br` note). -/
theorem v_addiw_range_ite (x : word) (imm : Int) :
    ((v_addiw x imm).toNat : Int) =
      if 0 ≤ (x.toNat : Int) + imm ∧ (x.toNat : Int) + imm < 2 ^ 31
      then (x.toNat : Int) + imm
      else bv_swrap 32 ((x.toNat : Int) + imm) % 2 ^ 64 := by
  split
  · rename_i h
    exact v_addiw_range x imm h.1 h.2
  · unfold v_addiw
    rw [BitVec.toNat_ofInt]
    rw [show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 from by rw [Int.natCast_pow]; rfl]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]

/-- The closer.  Deliberately `decide`-free: an [SCBr] operand is
    routinely an OPEN `BitVec` term (a symbolic sp, a read-back argc), and
    a kernel-level `decide` on one of those does not fail — it gets stuck,
    so the goal silently survives .
`negb_true_iff`/`negb_false_iff`: move a `!b` wrapper off the
       comparison. `unfold bv_lts, bv_ltu, bv_eqb` (and [branch_taken], the six-way
       branch-condition dispatch of `Riscv/Sem.lean`): push each
       comparison down to an [Int] comparison over the operands'
       readings ([bv_lts_Z], [bv_ltu_Z], [bv_eqb_Z], this tree's form of
       that unfold);
    3. -/
macro "sym_br" : tactic =>
  `(tactic|
    (simp only [c_eq, c_lts, c_ltu, branch_taken, bv_lts_Z, bv_ltu_Z, bv_eqb_Z,
        bv_signed_cond, v_addiw_range_ite, BitVec.toNat_ofInt, Bool.not_not]
     <;> (try (rw [← decide_not]))
     <;> (try (rw [← decide_not]))
     <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not]
     <;> (repeat (first | split | omega | assumption))))
/-! ## Smoke checks ()

    One branch per spelling, at the three shapes an [SCBr] obligation
    takes: a `blt` whose operands are within the sign boundary, a
    `bltu`/`beq` that needs no bound at all, a `blt` against a NEGATIVE
    literal (the [div] fixup), and an [argc]-relative [addiw] index.  The
    caller-side bounds are the hypotheses, exactly as in an example
    proof. -/

/-! ### The [SCBr] obligations themselves

    [SymExec]'s [sc_denot] turns an [SCBr] entry into
    `branch_taken c a b = t` ([Riscv.Sem.branch_taken], with `t` the
    direction the caller's branch script names), so [sym_br] unfolds that
    function too — the six `BranchCond` cases are exactly the three
    spellings above plus their `!`-wrapped duals.  One check per
    constructor family:

      [EQ]/[NE]     — [bv_eqb], negated for [NE];
      [LT]/[GE]     — [bv_lts], negated for [GE];
      [LTU]/[GEU]   — [bv_ltu], negated for [GEU]. -/

/-- `blt` (signed): the bound hypotheses are what makes [bv_signed_small]
    applicable. -/
example (a b : word) (Ha : (a.toNat : Int) < 2 ^ 63) (Hb : (b.toNat : Int) < 2 ^ 63)
    (h : (a.toNat : Int) < (b.toNat : Int)) : c_lts a b = true := by
  sym_br

/-- `bltu` (unsigned), taken direction.  No sign-bound hypothesis: the
    unsigned reading is the comparison's own reading. -/
example (a b : word) (h : (a.toNat : Int) < (b.toNat : Int)) : c_ltu a b = true := by
  sym_br

/-- `bgeu`/`bltu` not-taken direction (`= false`). -/
example (a b : word) (h : ¬ ((a.toNat : Int) < (b.toNat : Int))) : c_ltu a b = false := by
  sym_br

/-- `beq` (and the `beqz`/`bnez` aliases). -/
example (a b : word) (h : (a.toNat : Int) = (b.toNat : Int)) : c_eq a b = true := by
  sym_br

/-- `blt` against a NEGATIVE literal: `-9`, the [div] round-toward-zero
    fixup.  The literal's [toInt] is not its [toNat], so this exercises
    the [bv_signed_cond] branch of the closer. -/
example (a : word) (Ha : (a.toNat : Int) < 2 ^ 63)
    (h : (a.toNat : Int) < (-9 : Int)) : c_lts a (BitVec.ofInt 64 (-9)) = false := by
  sym_br

example (a b : word) (h : (a.toNat : Int) < (b.toNat : Int)) :
    branch_taken .LTU a b = true := by
  sym_br

example (a b : word) (h : ¬ ((a.toNat : Int) < (b.toNat : Int))) :
    branch_taken .GEU a b = true := by
  sym_br

example (a b : word) (Ha : (a.toNat : Int) < 2 ^ 63) (Hb : (b.toNat : Int) < 2 ^ 63)
    (h : (a.toNat : Int) < (b.toNat : Int)) : branch_taken .LT a b = true := by
  sym_br

example (a b : word) (h : (a.toNat : Int) = (b.toNat : Int)) :
    branch_taken .EQ a b = true := by
  sym_br

example (a b : word) (h : (a.toNat : Int) ≠ (b.toNat : Int)) :
    branch_taken .NE a b = true := by
  sym_br

/-- The [argc]-relative index: `addiw s1,a0,-2` compared signed.  This is
    the case [v_addiw_range] exists for, and the one whose side conditions
    `split` materialises for `omega`. -/
example (x y : word) (Hlo : 2 ≤ (x.toNat : Int)) (Hhi : (x.toNat : Int) < 2 ^ 31)
    (Hy : (y.toNat : Int) < 2 ^ 63)
    (h : (x.toNat : Int) + (-2) < (y.toNat : Int)) :
    c_lts (v_addiw x (-2)) y = true := by
  sym_br

end WithFP

end LinuxSem.Common.SymBranch
