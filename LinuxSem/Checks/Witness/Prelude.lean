/-
  * LinuxProcessSem.Checks.Witness.Prelude — the witnesses' shared helpers and tactics

  Shared infrastructure for the witnesses below it: this one mirrors
  no kernel source, and holds nothing syscall-specific.

  `Checks/Progress.lean` keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching `Sys` module, which is what
  progress is proved from.

  Notation used throughout the witness layer: `word` is `BitVec 64` (from
  `Riscv.Prelude`); the spec monad `Sys A` is `SysSpec A` (see
  `MonadInstances`); `outcome A` is `Outcome A Model event`; and `In e
  es` is `e ∈ es`.  The `srw` tactic macro below is `rw` followed by
  `dsimp only`, the beta/iota/zeta reduction that a scrutinee rewrite
  needs.
-/
import LinuxSem.LinuxProcessSem.BvBase
import LinuxSem.LinuxProcessSem.Fs
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.Monad
import LinuxSem.LinuxProcessSem.Specs

namespace LinuxSem.Checks.Witness.Prelude

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall

/-- Rewrite a scrutinee equation, then iota-reduce the match/if it
    unblocks. -/
macro "srw " h:term : tactic => `(tactic| (rw [$h:term]; dsimp only))

/-- A bind step whose first component contributes no events (it may still
    update the model), propagating EITHER outcome shape of the
    continuation.  Every step in the witnesses below is of this form
    except `emit`, which gets its own lemma. -/
theorem bind_step {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (x : A) (m1 : Model) (o : Outcome B Model event)
    (Hc : c i m (.ok x m1 [])) (Hk : k x i m1 o) : bind c k i m o := by
  cases o with
  | ok y m2 evs => exact bind_ok c k i m x m1 [] y m2 evs Hc Hk
  | unmodeled => exact bind_unmodeled2 c k i m x m1 [] Hc Hk

/-- `emit` followed by `pure`: the whole program's events are exactly the
    emitted ones. -/
theorem emit_pure_ok {A : Type} (evs : List event) (x : A)
    (i : SyscallInput) (m : Model) :
    bind (emit evs) (fun _ => pure x) i m (.ok x m evs) := by
  simpa using bind_ok (emit evs) (fun _ => pure x) i m () m evs x m []
    (emit_ok evs i m) (pure_ok x i m)

/-- Every injectable-errno set is inhabited, so the failure branch is
    always available: the head of the list is a member.  ENOMEM heads
    `openat_errnos`, `mmap_errnos`, `mprotect_errnos` and `dup_errnos`;
    `getrandom_errnos` is headed by EINTR. -/
theorem errno_from_witness (es : List Int) (e : Int) (i : SyscallInput) (m : Model)
    (H : e ∈ es) : errno_from es i m (.ok e m []) :=
  choose_ok (fun x => x ∈ es) e i m H

theorem errno_head_witness (e : Int) (es : List Int) (i : SyscallInput) (m : Model) :
    errno_from (e :: es) i m (.ok e m []) :=
  choose_ok (fun x => x ∈ e :: es) e i m (by simp)

/-- ENOMEM (12): the errno the openat/mmap/dup witnesses below fail
    with (it heads those sets). -/
def witness_errno : Int := ENOMEM

/-- Shorthand for the "return [r], change nothing, emit nothing"
    outcome. -/
def ret_outcome (r : word) (m : Model) : Outcome SyscallEffect Model event :=
  .ok (mkEffect r [] []) m []

theorem witness_bind_ok_eq {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (x : A) (m1 : Model) (evs1 : List event)
    (y : B) (m2 : Model) (evs2 : List event) (evs : List event)
    (Hc : c i m (.ok x m1 evs1)) (Hk : k x i m1 (.ok y m2 evs2))
    (Hevs : evs = evs1 ++ evs2) : bind c k i m (.ok y m2 evs) := by
  subst Hevs
  exact bind_ok c k i m x m1 evs1 y m2 evs2 Hc Hk

/-! ## Sanity checks

    These are this module's own checks; they pin the two computable
    definitions above. -/

/-- `witness_errno` really is ENOMEM (12). -/
example : witness_errno = 12 := by decide

/-- `ret_outcome r m` returns `r` and carries no effect at all. -/
example (r : word) (m : Model) :
    (match ret_outcome r m with
     | .ok e _ _ =>
         e.eff_ret = r ∧ e.eff_writes = [] ∧ e.eff_zeros = [] ∧
           e.eff_unmaps = [] ∧ e.eff_copies = [] ∧ e.eff_copyins = []
     | .unmodeled => False) := by
  simp [ret_outcome, mkEffect]

/- =========================================================================
   read (63) — witness: the one-byte delivery from the input stream
   (channel; 0 at end of input), the deterministic file read (file),
   -EFAULT for a destination whose first byte cannot be written, or
   the fail-closed `Unmodeled`
   ========================================================================= -/

/- `Uaccess.access_ok_zero` as a witness: the zero answer where the model
   is sure the range passed `access_ok`, -EFAULT where it is sure it did
   not, and the fail-closed decline in between.

   (A comment, not a declaration: the read witness lives in the file that
   continues this one.) -/
