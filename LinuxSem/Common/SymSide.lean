/-
  * Common.SymSide — nested-window normalization for [SymExec]'s
    address side conditions.

      EXPLORATION / PROTOTYPE.  Image-INDEPENDENT proof library; nothing
      here is part of the trusted specification.

      [Common/SymTac]'s [sym_sc_auto] closes an [SCFlat] / [SCDisjoint]
      with [repeat split; lia] once the addresses are [Z] expressions over
      the caller's symbolic bases.  [StepTac.u_norm] is what gets them
      there — it collapses [bv_unsigned (Z_to_bv 64 z)] to [z] — and for a
      binary with ONE frame it is enough, because every address is
      [Z_to_bv 64 (bv_unsigned sp + k)] and the projection is one level
      deep.

      It stops working the moment a block crosses a CALL.  [main]'s frame
      is [Z_to_bv 64 (bv_unsigned rsp - 96)], [print_array]'s is
      [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160)],
      and a spill inside it is one level deeper again.  [u_norm] is
      [repeat rewrite u_Z2bv by lia], and [rewrite] takes the OUTERMOST
      match: its side condition is
      [0 <= bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160 < 2^64],
      which [lia] cannot see is true, because the inner projection is
      still an opaque atom.  So [u_norm] fails on the outside and never
      reaches the inside, and every cross-call [SCDisjoint] is left for
      the caller.

      [u_norm_deep] rewrites INNERMOST-first, so each side condition is
      posed only over projections that have already been collapsed.  That
      single change is what makes a block spanning
      [main -> print_array -> write_all] cost the same per instruction as
      a block inside one function.

    NOTES.
 Each is stated as a Lean `macro` of the same name with the same
    job, so call sites read unchanged.
    - [u_norm_deep] / [u_norm_deep_in]: Lean's `rw` takes the outermost
      occurrence, exactly the failure mode  describes, and a
      `repeat rw` cannot fix it. by lia` pass — one collapse per level, every bound
      posed over already-collapsed projections.  See the macro's docstring.
 Lean's kernel reduction has no
      allocate-until-the-machine-dies failure mode (it gets stuck on a
      variable), so the guard has no counterpart to make; the closer is
      `rfl`/`decide`, which is the same normalisation by computation.
      `bv_eq` is `BitVec.eq_of_toNat_eq` here (`StepTac.bveq`), `lia` is
      `omega`, `repeat split` is a bounded iteration of `constructor`
      (`split` is for `if`/`match` in Lean and leaves a conjunction whole),
      and `length_N_to_le_bytes` is
      `BvBase.length_Z_to_le_bytes` — this tree has no `N`-indexed byte
      encoder.
-/

import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.Common.StepTac
import LinuxSem.Common.SymBranch
import LinuxSem.Common.CatExec

set_option autoImplicit false

namespace LinuxSem.Common.SymSide

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.Common.StepTac

/-- Collapse [bv_unsigned (Z_to_bv 64 _)] innermost-first.  The [lia] side
    conditions see a fully normalized argument, so the caller's window bounds
    ([sp_window_lo <= bv_unsigned rsp], a grant's [alloc_top] bound) are
    enough.

     is `repeat match goal with... => rewrite (u_Z2bv z) by lia end`
    under a guard that the matched argument has no [Z_to_bv] inside it — that
    guard is what makes the pass innermost-first.  Lean's `simp` traverses
    subterms inner-first and runs a `discharger` on each conditional rewrite's
    premises, so `simp (discharger := omega) only [u_Z2bv]` is the same pass:
    each bound is posed over projections that are already collapsed, and a
    level whose premises cannot be closed is simply left for the caller
.
    NOTE for callers. -/
macro "u_norm_deep" : tactic =>
  `(tactic| try simp (discharger := omega) only [u_Z2bv])

/-- The same, in a hypothesis. -/
macro "u_norm_deep_in " h:ident : tactic =>
  `(tactic| try simp (discharger := omega) only [u_Z2bv] at $h:ident)

/-- A computation closer that REFUSES to run on an open goal.

    [SymTac.sym_close]'s last alternative is [StepTac.bveq], which is
    [vm_compute]-based, and a symbolic [sp] or [mmap] grant base reaching
    it does not make it fail — it makes it allocate until the process is
    OOM-killed, with no error and no useful diagnostic (the build
    just reports "Command got signal KILL").  Inside an
    [all: try solve [...]] list that is fatal in a new way: [try solve]
    is exactly the idiom that hands a tactic goals it was not written
    for, so ONE open goal in a list of thirty kills the build.

    [check_closed_term] is the guard, and it is cheap: it fails
    immediately if the goal mentions any local hypothesis.  Use this,
    never a bare [vm_compute], in a [try solve] list.

    the guard has no counterpart to make — see the header. -/
macro "vm_closed" : tactic => `(tactic| first | rfl | decide | bveq)

/-- [SymTac.sym_close] with the [bveq] alternative removed, for the same
    reason. -/
macro "sym_close_open" : tactic =>
  `(tactic|
    first
    | rfl
    | (congr 1 <;> omega)
    | (apply BitVec.eq_of_toNat_eq <;> u_norm <;> omega))

/-- The whole address-side-condition closer for a cross-call block. -/
macro "sym_sc" : tactic =>
  `(tactic|
    (imm_norm <;> u_norm_deep <;> u_norm <;> imm_norm <;>
     (iterate 16 (first | constructor | skip)) <;>
     omega))

/-- The side-condition script the [rdn] peeling lemmas want: the same
    normalization, plus the list-length rewrites their bounds mention. -/
macro "rdn_side" : tactic =>
  `(tactic|
    (simp only [length_Z_to_le_bytes] <;>
     imm_norm <;> u_norm_deep <;> u_norm <;> imm_norm <;>
     omega))

end LinuxSem.Common.SymSide
