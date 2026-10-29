/-
  * LinuxSem.Checks.VmMapsDisjoint.Tactics — the PART 3 frame
    tactics, shared by every module the frame half is split into.

  SPLIT NOTE (build parallelism — no proof, statement or hypothesis moves).
  Lean elaborates a MODULE as a unit and lake parallelises only ACROSS
  modules, so the single file `Checks/VmMapsDisjoint.lean` (3,185 lines,
  92.8 s of `lake env lean`, of which five frame arms were ~80 s:
  `prlimit64` 28 s, `writev` 26 s, `pwrite64` 22 s, `setresgid` 20.7 s,
  `futex` 12.1 s) was split into `Tactics` + `Frames` + `Frames/Costly*`,
  which all sit below the aggregator and can be checked concurrently on
  this 16-core machine.  This module is the bottom of that pyramid: it
  holds exactly what the arm modules must share, and nothing else.

  WHAT IS HERE, AND WHY IT HAS TO BE SHARED:

  * the frame tactics, carried over VERBATIM from the single-file version:
    `vm_frame`, BOTH `vm_close` overloads (the plain one and the
    bracketed `[ tac ]` one used for the `private`-helper arms),
    `vm_frame_m`, `vm_ret_only`, `vm_ret_only_copyins` and
    `vm_ret_only_copyins_ds`.  A `macro` is looked up in the environment,
    so every importing module sees them under the same names and the
    single file's call sites (`vm_frame eff H <checker> …`) are unchanged;
  * the five `*_model` inversions (`check_ret_only_model`,
    `check_ret_only_copyins_model`, `check_copyins_model`,
    `check_copyin_prefix_model`, `check_copyins_after_model`).  They are
    term-level facts, not tactics, but their ONLY consumers are the
    terminal arms of the `vm_frame_m` / `vm_ret_only` loops, which cite
    them by name — so they belong to the tactic layer, not to PART 2.

  WHAT IS NOT HERE, AND WHY:

  * `bvnorm` is the ONE tactic of the file that does not move.  Its body is
    `try dsimp only [bv_unsigned, vm_brk, …, vm_wf, m_vmmaps] at *; try simp
    only [two_pow_64] at *`, and Lean resolves a syntax quotation's
    identifiers when the MACRO is elaborated, not when it is used: in a
    module where `bv_unsigned` and `vm_wf` do not exist yet, the expansion
    carries `bv_unsigned✝` / `vm_wf✝`, no use site can resolve those, and
    `try` swallows the failure — the tactic becomes a silent no-op
    (measured: 24 `omega` failures in PART 1/2/2b the first time it was
    tried).  Those abbreviations are PART 1/2's prelude and `vm_wf` is
    PART 2's invariant, so `bvnorm` stays beside them in `Core` — the base
    module that now elaborates PART 1/2, after the aggregator became a pure
    import shim.  NOTHING that moved here uses `bvnorm`, so no arm module
    needs it either.
  * the moved proofs' transitive closure over this file's own declarations
    is exactly the five `*_model` lemmas above (taken with the comments
    stripped, so prose mentions do not count).  The frame arms therefore
    need NOTHING from PART 1/2/2b, which is what lets the aggregator import
    them instead of the other way round.

  NAMESPACE.  Everything sits in
  `LinuxSem.Checks.VmMapsDisjoint` — the single file's own
  namespace — so every fully-qualified name is unchanged and the root
  module, `Checks/Capstone.lean` and the sibling `Checks/` files keep
  resolving them.
-/

import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Sys.Fs.Readdir
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.StateVm
import LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mmap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Mm.Mmap
open LinuxSem.Checks.Sys.Mm.Mremap
open LinuxSem.Checks.Sys.Mm.Mprotect
open LinuxSem.Checks.Sys.Mm.Madvise
open LinuxSem.Checks.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Drivers.Char.Random
open LinuxSem.Checks.Sys.Fs.DPath
open LinuxSem.Checks.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Fs.EventPoll
open LinuxSem.Checks.Sys.Fs.Fcntl
open LinuxSem.Checks.Sys.Fs.File
open LinuxSem.Checks.Sys.Fs.Ioctl
open LinuxSem.Checks.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Fs.Open
open LinuxSem.Checks.Sys.Fs.Pipe
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Fs.Select
open LinuxSem.Checks.Sys.Fs.Stat
open LinuxSem.Checks.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Fs.Timerfd
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Kernel.Groups
open LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Sys.Kernel.Signal
open LinuxSem.Checks.Sys.Kernel.Sys
open LinuxSem.Checks.Sys.Kernel.Time.Time
open LinuxSem.Checks.Sys.Net.Socket

namespace LinuxSem.Checks.VmMapsDisjoint

theorem check_ret_only_model (eff : SyscallEffect) (r : word) (mm : Model)
    (evs0 : List event) (m' : Model) (evs : List event)
    (H : check_ret_only eff r mm evs0 = .CheckOk m' evs) : m' = mm :=
  ((check_ret_only_ok_iff eff r mm evs0 m' evs).mp H).2.1

/-- The copyin wrappers ([Checks/Sys/Prelude]) sit between an arm and
    its answer.  Neither changes the model: [check_ret_only_copyins]
    hands back the model [check_ret_only] was given, and the other two
    pass a result through unchanged. -/
theorem check_ret_only_copyins_model (reads : List (word × Nat))
    (eff : SyscallEffect) (r : word) (mm : Model) (evs0 : List event)
    (m' : Model) (evs : List event)
    (H : check_ret_only_copyins reads eff r mm evs0 = .CheckOk m' evs) : m' = mm :=
  ((check_ret_only_copyins_ok_iff reads eff r mm evs0 m' evs).mp H).2.1

theorem check_copyins_model (reads : List (word × Nat)) (eff : SyscallEffect)
    (res : check_result) (m' : Model) (evs : List event)
    (H : check_copyins reads eff res = .CheckOk m' evs) : res = .CheckOk m' evs := by
  unfold check_copyins at H
  by_cases h : access_ranges_eqb eff.eff_copyins reads = true
  · rw [ite_eq_left h] at H
    exact H
  · rw [ite_eq_right h] at H
    exact absurd H (by simp)

theorem check_copyin_prefix_model (reads : List (word × Nat)) (eff : SyscallEffect)
    (res : check_result) (m' : Model) (evs : List event)
    (H : check_copyin_prefix reads eff res = .CheckOk m' evs) :
    res = .CheckOk m' evs := by
  cases res with
  | CheckUnmodeled => simp [check_copyin_prefix] at H
  | CheckOk m0 evs0 =>
    simp only [check_copyin_prefix] at H
    by_cases h : access_ranges_eqb (eff.eff_copyins.take reads.length) reads = true
    · rw [ite_eq_left h] at H
      exact H
    · rw [ite_eq_right h] at H
      exact absurd H (by simp)
  | CheckReject => simp [check_copyin_prefix] at H

theorem check_copyins_after_model (reads : List (word × Nat)) (eff : SyscallEffect)
    (res : check_result) (m' : Model) (evs : List event)
    (H : check_copyins_after reads eff res = .CheckOk m' evs) :
    res = .CheckOk m' evs := by
  cases res with
  | CheckUnmodeled => simp [check_copyins_after] at H
  | CheckOk m0 evs0 => exact check_copyins_model reads eff _ m' evs H
  | CheckReject => simp [check_copyins_after, check_copyins] at H

/-- Case-split a checker's result hypothesis until it is either
    `CheckOk m [] = CheckOk m' evs` (so `cases` substitutes) or
    `CheckReject = CheckOk …` (so `cases` closes the goal).  See the
    note on the effect-destruct route for why this is `obtain` + `cases`,
    not `split at *`.

    Arguments: the effect variable, the hypothesis, the checker (as a
    qualified name, so nothing depends on which namespace is open), and
    the `check_*` helpers the checker calls. -/
macro "vm_frame" ef:ident h:ident c:ident ids:ident* : tactic =>
  `(tactic| (
    (obtain ⟨r, ws, zs, us, cs, ci⟩ := $ef:ident);
    (cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ci);
    (all_goals (repeat' (first
      | (cases $h:ident; rfl)
      | (cases $h:ident)
      | (split at $h:ident)
      | (simp only [$c:ident, $[$ids:ident],*] at $h:ident)
      | (simp only [m_vmmaps]; rfl))))
  ))

/-- Case-split a checker's result hypothesis exactly like `vm_frame`, but
    with the hypothesis NAME and one extra leading arm passed in.  The
    leading arm is a TERM-level proof (`exact …_frame _ _ _ _ H`) or a
    `first` over several of them, tried before anything else — `cases H`
    on a `private` helper application *succeeds* but is unproductive, so it
    must not get the first word. -/
macro "vm_close" h:ident c:ident ids:ident* : tactic =>
  `(tactic| repeat' (first
      | (cases $h:ident; rfl)
      | (cases $h:ident)
      | (split at $h:ident)
      | (simp only [$c:ident, $[$ids:ident],*] at $h:ident)
      | (simp only [m_vmmaps]; rfl)))

macro "vm_close" h:ident "[" tac:tacticSeq "]" c:ident ids:ident* : tactic =>
  `(tactic| repeat' (first
      | ($tac)
      | (cases $h:ident; rfl)
      | (cases $h:ident)
      | (split at $h:ident)
      | (simp only [$c:ident, $[$ids:ident],*] at $h:ident)
      | (simp only [m_vmmaps]; rfl)))

/- -------------------------------------------------------------------------
   The copy-in-ledger arms: `vm_frame_m`.

   A THIRD obstacle, distinct from both recorded ones, and it is why these
   arms need their own loop.  The accepting branch of most of them ends in
   one of the `check_ret_only` / `check_ret_only_copyins` wrappers, whose
   bodies are

     match check_ret_only (clear_copyins eff) r mm evs0 with
     | .CheckOk m'' evs' => if access_ranges_eqb … then … else …
     | result => result

   and `check_ret_only` itself reduces to an `if bv_eqb ret r`.  With the
   wrappers in the `simp only` list, `simp` reaches the point where the
   `match` scrutinee is that undecidable `if`, and then the loop's
   `split at H` GENERALISES it: it introduces a fresh `x✝` and an equation
   `heq✝`, DESTROYS the hypothesis `H` the loop names, and leaves the goal
   unreachable.  (`split` succeeding unproductively is the same failure
   mode the `openat` note records for `check_copyins_after`.)

   THE ROUTE THAT WORKS is to make the TERMINAL call the loop's business,
   through the `*_model` lemmas above — each of them already says "this
   wrapper hands back the model it was given", which is exactly the
   remaining half of `m_vmmaps m' = m_vmmaps m`:

   * keep the wrappers OUT of the `simp only` list, so the hypothesis
     reaches the terminal call intact;
   * rewrite `m'` with the `*_model` lemma (`rw`, not `exact congrArg`);
     the model handed back is usually a `with_fds`/`with_fs`/`with_clock`
     nest, and `rfl` then closes `m_vmmaps (with_fds …) = m_vmmaps m`
     because a projection of a structure update reduces definitionally;
   * `rfl` is also an explicit loop arm, so a goal that became reflexive
     closes immediately rather than waiting for the last arm.

   That is `vm_frame H` again, with the helper's own `*_model`
   inversion standing in for the answer a closed computation would give. -/

/-- `vm_frame` with the `*_model` inversions as terminal arms.  Use it when
    the checker's accepting branch ends in a `check_ret_only`-family
    wrapper (see the note above for why `split` cannot be allowed to reach
    one). -/
macro "vm_frame_m" h:ident c:ident ids:ident* : tactic =>
  `(tactic| repeat' (first
      | (cases $h:ident; rfl)
      | (cases $h:ident)
      | (rfl)
      | (rw [check_ret_only_model _ _ _ _ _ _ $h])
      | (rw [check_ret_only_copyins_model _ _ _ _ _ _ _ $h])
      | (rw [check_copyins_model _ _ _ _ $h])
      | (rw [check_copyin_prefix_model _ _ _ $h])
      | (rw [check_copyins_after_model _ _ _ $h])
      | (simp only [$c:ident, $[$ids:ident],*] at $h:ident)
      | (split at $h:ident)
      | (simp only [m_vmmaps]; rfl)))

/-- Close a leaf whose hypothesis is a `check_ret_only` acceptance: the
    wrapper hands back the model it was given, so the projection is the
    old one — and `rfl` absorbs the arms that hand back a `with_…` REBUILD
    of it.  `contradiction` covers the leaves whose effect shape already
    forced `.CheckReject`; see the note above for why it must not be
    `exact nomatch`. -/
macro "vm_ret_only" h:ident : tactic =>
  `(tactic| first
      | (rw [check_ret_only_model _ _ _ _ _ _ $h:ident] <;> rfl)
      | (contradiction))

/-- Close a leaf whose hypothesis is a `check_ret_only_copyins` acceptance.
    Same shape as `vm_ret_only`: the wrapper hands back the model
    `check_ret_only` was given. -/
macro "vm_ret_only_copyins" h:ident : tactic =>
  `(tactic| first
      | (rw [check_ret_only_copyins_model _ _ _ _ _ _ _ $h:ident] <;> rfl)
      | (contradiction))

/-- The dead-effect-shape closer used by the `sendmsg` walk, where the
    effect match sits behind a six-way `read_u64` import: `dsimp` first
    (the match may still be on a constructor tuple), then the same
    inversion. -/
macro "vm_ret_only_copyins_ds" h:ident : tactic =>
  `(tactic| first
      | (try (dsimp only at $h:ident)
         rw [check_ret_only_copyins_model _ _ _ _ _ _ _ $h:ident] <;> rfl)
      | (contradiction))


end LinuxSem.Checks.VmMapsDisjoint
