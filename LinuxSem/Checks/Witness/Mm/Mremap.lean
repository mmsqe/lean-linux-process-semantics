/-
  * LinuxProcessSem.Checks.Witness.Mm.Mremap — the mremap (216) witnesses, and their proofs

  Answers to Linux [mm/mremap.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`.  The witness's `if` chain sits at `Outcome` type while the
  spec's sits at function type, so each gate is rewritten in both — that is
  what the `repeat rw` below is for (the same idiom as
  `Checks/Witness/Mm/Mprotect.lean`).

  Each step has a named lemma: a gate's `err_ret` / `ret_only` is `pure` of
  the same effect by definition, so `exact pure_ok _ i m` closes it; the
  two monadic steps are `bind_step` of `Checks.Witness.Prelude`; the errno
  alternative is `errno_head_witness` (ENOMEM heads `mremap_errnos`, and
  the witness's `witness_errno` IS `ENOMEM`); and the three fail-closed
  arms are `unmodeled_intro`.  `alt_l` is the `Monad` introduction lemma,
  kept spelled out rather than as `Or.inl`.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mremap

namespace LinuxSem.Checks.Witness.Mm.Mremap

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mremap
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Witness.Prelude

/-- The `mremap` (216) witness.

    The same argument gates as `mremap_spec`, in the same order, each of
    which the spec answers with one `err_ret` / `ret_only`, and then one
    outcome out of the resizing shapes the spec answers:

    - the equal-size no-op answers `old` with no effect;
    - every other answered shape is the injected -ENOMEM (`witness_errno`,
      the head of `mremap_errnos`) with the state untouched.  A resize
      offers `alt (injected errno) (shrink | in-place grow | move)`, and
      progress needs only one of the two, so the witness exhibits the
      injected failure;
    - a flag word other than exactly `MREMAP_MAYMOVE`, a zero rounded
      source length, or a source the model does not track is `.unmodeled`,
      exactly where the spec declines.

    The witness deliberately does NOT touch the model: no `modify` step, so
    the outcome carries the starting model on every `ok` path. -/
def mremap_witness (old old_size new_size flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !((flags.toNat : Int) == MREMAP_MAYMOVE) then .unmodeled
  else if !(((old.toNat : Int) % page_size) == 0) then
    ret_outcome (errno_ret EINVAL) m
  else if page_align_is0_b new_size then ret_outcome (errno_ret EINVAL) m
  else if page_align_is0_b old_size then .unmodeled
  else
    let old_nZ := page_round_up_Z (old_size.toNat : Int)
    let new_nZ := page_round_up_Z (new_size.toNat : Int)
    let old_n := BitVec.ofInt 64 old_nZ
    if !(mremap_source_b (m_vmmaps m) old old_n old_nZ &&
         mremap_backing_uniform_b m old old_n) then .unmodeled
    else if old_nZ == new_nZ then ret_outcome old m
    else ret_outcome (errno_ret witness_errno) m

section

-- The witness's gate chain and the spec's are driven together; the
-- default recursion budget is not enough to unify the instantiated
-- alternatives (the same option guards the analogous proof in
-- `Checks/Witness/Mm/Mprotect.lean`).
set_option maxRecDepth 1000000

theorem mremap_witness_ok (old old_size new_size flags : word) (i : SyscallInput)
    (m : Model) :
    mremap_spec old old_size new_size flags i m
      (mremap_witness old old_size new_size flags m) := by
  unfold mremap_spec mremap_witness
  dsimp only
  by_cases hshape : (!((flags.toNat : Int) == MREMAP_MAYMOVE)) = true
  · -- the flag gate declines on both sides
    repeat rw [ite_eq_left hshape]
    exact unmodeled_intro i m
  · repeat rw [ite_eq_right hshape]
    by_cases halign : (!(((old.toNat : Int) % page_size) == 0)) = true
    · -- the misaligned address: -EINVAL, state untouched
      repeat rw [ite_eq_left halign]
      exact pure_ok _ i m
    · repeat rw [ite_eq_right halign]
      by_cases hnew : page_align_is0_b new_size = true
      · -- a zero rounded new length: -EINVAL, state untouched
        repeat rw [ite_eq_left hnew]
        exact pure_ok _ i m
      · repeat rw [ite_eq_right hnew]
        by_cases hold : page_align_is0_b old_size = true
        · -- a zero rounded source length: both sides decline
          repeat rw [ite_eq_left hold]
          exact unmodeled_intro i m
        · repeat rw [ite_eq_right hold]
          rw [bind_getModel]
          by_cases hsrc : (!(mremap_source_b (m_vmmaps m) old
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int)))
              (page_round_up_Z (old_size.toNat : Int)) &&
            mremap_backing_uniform_b m old
              (BitVec.ofInt 64 (page_round_up_Z (old_size.toNat : Int))))) = true
          · -- a source the model does not track: both sides decline
            repeat rw [ite_eq_left hsrc]
            exact unmodeled_intro i m
          · repeat rw [ite_eq_right hsrc]
            by_cases heq : (page_round_up_Z (old_size.toNat : Int) ==
                page_round_up_Z (new_size.toNat : Int)) = true
            · -- the equal-size no-op answers the source address
              repeat rw [ite_eq_left heq]
              exact pure_ok _ i m
            · -- a resize: exhibit the injected -ENOMEM, state untouched
              repeat rw [ite_eq_right heq]
              exact alt_l _ _ i m _
                (bind_step (errno_from mremap_errnos) (fun e => err_ret e) i m
                  ENOMEM m _
                  (errno_head_witness ENOMEM [] i m) (pure_ok _ i m))

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the witness
    and its one proof.  The checks below are sanity checks: they pin the
    gate order the proof relies on, at concrete arguments. -/

/-- A flag word outside exactly `MREMAP_MAYMOVE` declines. -/
example (m : Model) :
    mremap_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 0) m = .unmodeled := by
  unfold mremap_witness
  rw [ite_eq_left (by decide)]

/-- A misaligned address is -EINVAL, whatever the sizes are. -/
example (m : Model) :
    mremap_witness (BitVec.ofInt 64 0x1001) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 MREMAP_MAYMOVE) m =
      ret_outcome (errno_ret EINVAL) m := by
  unfold mremap_witness
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A zero new size is -EINVAL, before the source is read. -/
example (m : Model) :
    mremap_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 MREMAP_MAYMOVE) m =
      ret_outcome (errno_ret EINVAL) m := by
  unfold mremap_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A zero old size is the clone shape: the model declines instead of
    answering. -/
example (m : Model) :
    mremap_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 MREMAP_MAYMOVE) m = .unmodeled := by
  unfold mremap_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

end LinuxSem.Checks.Witness.Mm.Mremap
