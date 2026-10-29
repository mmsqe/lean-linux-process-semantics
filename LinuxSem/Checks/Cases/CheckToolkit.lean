/-
  * `Checks.Cases.CheckToolkit` — the shared toolkit for `check_result` examples.

  ## Why this file exists

  A wall, measured on this toolchain: `rfl` cannot close a checker example whose
  arm reads a value through a `Nat → Int` cast.  The narrowed minimal witness is

      example : decide ((2 : Int) < 2147483648) = true := by rfl                   -- OK
      example : decide (((2 : word).toNat) < 2 ^ 31) = true := by rfl             -- OK
      example : decide ((((2 : word).toNat : Int)) < 2147483648) = true := by rfl -- DIVERGES

  so it is not `^` and not `BitVec.toNat`, but the `Int` comparison whose operand
  is an `Int.ofNat` of a `BitVec.toNat`: `Int.decLt` is `(b-(a+1)).decNonneg`, a
  `Nat.brecOn` recursion that `whnf`/`isDefEq` cannot unwind — while the `decide`
  *tactic* computes it fine.  Since `check_result` carries a `Model` there is no
  `DecidableEq`, so the goal cannot be `decide`d either, and the failing `if` sits
  behind `check_syscall`'s dispatch over `checked_table`.

  ## Route A, and why it is generic

  Nothing below mentions any checker.  `isUnmodeledR` matches on **constructors
  only**, so it never touches `Model`; `isUnmodeledR_eq_true` reflects it back to
  an equality of `check_result`s.  A `by decide` fact about `isUnmodeledR r` then
  gives the equality that `rfl` cannot, in 0.2–0.5 s per arm.

  This settles every `= .CheckUnmodeled` example and — via
  `ne_checkUnmodeled_of_code` — every `≠ .CheckUnmodeled` one, without ever
  naming the value the arm answers with.

  ## Route A's scope is NARROWER than it looks — measured

  Route A closes **only** goals whose answer is the nullary `CheckUnmodeled`.
  On `Cases/Kernel/Time/Hrtimer.lean` it closed **0 of 29**: 15 examples are
  `= .CheckOk m evs` and 11 are `= .CheckReject`, and `isUnmodeledR_eq_true`
  concludes `r = .CheckUnmodeled`, so the `_` stays a metavariable and every
  attempt dies with "Expected type must not contain metavariables". The three
  universally quantified lemmas are worse: `by decide` has nothing to compute.

  So: **try `check_unmodeled` on a `= .CheckUnmodeled` or `≠` conjunct.**

  ## But "CheckOk/CheckReject needs Route B" is ALSO too strong

  Measured on `Cases/Kernel/Sched/Syscalls.lean`: a **nullary** reflection
  settles `= .CheckReject` with **zero per-branch work** —
  `(isRejectR_eq_true _).mp (by decide)` — and `= .CheckOk m []` follows from an
  `isOkR` projection plus a *"this checker never moves the model and never
  emits"* lemma, which holds whenever the accepted model **is the input model**
  (`sched_setscheduler`, `getdents64`, `sched_yield`, …). All 24 conjuncts there
  took 0.54 s total. It fails only for an arm returning a *modified* model —
  `clock_gettime`'s monotonic arm returns `with_clock …`, hence Route B there.

  Caveat: that `by decide` must evaluate the **whole arm** (0.1-0.3 s here), so
  it may be slow on a heavy one.

  ## The real lesson: there is no single recipe

  Three files needed three different routes, because the wall depends on *which
  cast the arm uses*:
  - `Net/Socket` - `sint32` arms; Route B needs `simp only [... checked_table,
    lookup_ca]` to unroll the table.
  - `Kernel/Time/Hrtimer` - dispatch is `rfl`-transparent, so **`rfl`** resolves
    it; putting `checked_table`/`lookup_ca` in the `simp` set instead unrolls a
    90-deep `if`-chain and hits "maximum recursion depth" in 0.3 s.
  - `Kernel/Sched/Syscalls` - nullary reflections, no Route B at all.

  **Probe the arm's shape for one conjunct before committing to a route.**

  It does **not** reach a `CheckOk` payload (`Model`'s `IoState` holds
  functions, so there genuinely is no `DecidableEq`).  For `= .CheckOk m evs` and
  `= .CheckReject` each file needs a **staged evaluator** of its own, of the
  shape documented in `Cases/Net/Socket.lean`'s "The `rfl`-wall route" note:

    1. `simp only [check_syscall, CheckedTable.check_syscall, Dispatch.check_syscall,
       Dispatch.checked_table, Dispatch.lookup_ca]` — resolves the 90-arm table
       WITHOUT reducing any `Decidable` instance (note `lookup_ca checked_table 198
       = some arm_socket` alone *is* `rfl`; the checker application is not);
    2. `simp [in_arg]`;
    3. `simp [check_<arm>, int32_neg, sint32, int32, fd32, abi_low32, z_ldiff,
       z_land, z_lor, <the UAPI constants>]` — normalises `sint32` at the
       now-literal argument;
    4. `try rfl`.

  ## Traps that silently defeat an otherwise-correct attempt

  - **`repeat constructor <;> …` is a silent killer.** `Eq`'s `constructor` is
    `Eq.refl`, whose *implicit defeq check* is exactly the divergent unification.
    Use `repeat' apply And.intro`.
  - **`repeat` iterates on the FIRST goal only**; on a 6-way conjunction it
    leaves goals behind. `repeat'` (primed) is required.
  - **`simp`/`simp only` ERROR on no progress**, so a stage that may be a no-op
    needs `(config := { failIfUnchanged := false })`.
  - A `macro` body resolves identifiers at the *macro definition site*, so a
    helper declared later in the same file gets hygiene-renamed (`foo✝`) —
    unfold it at the call site, not inside the macro.

  ## A `bind`-chain hypothesis needs `cases` on the OUTCOME first

  Measured on `Cases/Net/Socket.lean`'s `socket_write_never_admitted`, where the
  recorded diagnosis ("`rcases` cannot destruct the `Exists`") was a red
  herring.  `bind`'s body is a `match` on the **outcome**, so while that outcome
  is still a variable the `Exists` body stays stuck in an un-reduced `match` and
  `rcases` *legitimately* reports "not an inductive datatype".  **`cases o`
  first**, then the chain reduces and 15 lines finish each lemma.

  Two companions to that rule:
  - **bare `bind` is ambiguous with `Bind.bind`** - `simp only [bind]` dies with
    "Invalid simp theorem: Expected a proposition".  Write the qualified
    `LinuxSem.LinuxProcessSem.bind`.
  - rewrite the `fd_lookup` hypothesis into the goal-side hypothesis
    (`rw [Hfd] at hK2`) **before** splitting, so the socket arm becomes
    `unmodeled` / `writev_buf_gap` and `exact nomatch hK2` closes it.

-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Checks.Sys.Prelude

namespace LinuxSem.Checks.Cases

open LinuxSem.Riscv
open LinuxSem.Checks.Sys.Prelude

/-- A constructor-only test for `CheckUnmodeled`.  Unlike an equality test it
    never inspects a `Model` payload, so it is total and computable. -/
def isUnmodeledR : check_result → Bool
  | .CheckUnmodeled => true
  | _ => false

/-- Route A's reflection.  Mentions no checker, so it is reusable for every
    arm: a `by decide` fact about `isUnmodeledR r` gives the equality of
    `check_result`s that `rfl` cannot. -/
theorem isUnmodeledR_eq_true (r : check_result) :
    isUnmodeledR r = true ↔ r = .CheckUnmodeled := by
  cases r <;> simp [isUnmodeledR]

/-- And the refutation: a checker that projects to `false` is not
    `CheckUnmodeled`.  This is the `≠` form, and it never has to name (or
    reduce) the value the arm answers with. -/
theorem ne_checkUnmodeled_of_code (r : check_result)
    (h : isUnmodeledR r = false) : r ≠ .CheckUnmodeled := by
  intro hr
  rw [hr] at h
  exact Bool.noConfusion h

/-- Route A as one tactic: close `… = .CheckUnmodeled` by computing the
    constructor test.  Falls through (rather than failing) when the goal is an
    equality at some other constructor — that is what lets it be the first
    alternative in a `first | …` chain. -/
macro "check_unmodeled" : tactic =>
  `(tactic| first
    | exact (isUnmodeledR_eq_true _).mp (by decide)
    | exact ne_checkUnmodeled_of_code _ (by decide))

end LinuxSem.Checks.Cases
