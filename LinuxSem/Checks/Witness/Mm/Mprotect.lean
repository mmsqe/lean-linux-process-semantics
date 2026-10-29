/-
  * LinuxProcessSem.Checks.Witness.Mm.Mprotect — the mprotect (226) witnesses, and their proofs

  Answers to Linux [mm/mprotect.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`.  The `<=?` gate is the spec's `Prop` form
  `two_pow_64 ≤ …` (see `Sys/Mm/Mprotect.lean`), so it is split with
  `by_cases`, while the other gates are `Bool` equations.

  Each step has a named lemma: a gate's `err_ret` / `ret_only` is `pure` of
  the same effect by definition, so `exact pure_ok _ i m` closes it; the
  two monadic steps are `bind_step` of `Checks.Witness.Prelude` with
  `dsimp only` after them; the errno alternative is `errno_head_witness`
  (ENOMEM heads `mprotect_errnos`, and the witness's `witness_errno` IS
  `ENOMEM`); and the two fail-closed arms are `unmodeled_intro`.  `alt_l`
  is `alt`'s introduction lemma, kept spelled out rather than as `Or.inl`,
  so the statement names which side it takes.

  Every gate test occurs twice in the goal after the two definitions are
  unfolded — once in the spec (`SysSpec` type) and once in the witness
  (`Outcome` type) — and a single `rw [ite_eq_left h]` instantiates the lemma at
  ONE type.  `repeat` runs it once per occurrence/type, which is what
  reaches both sides at once.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect

namespace LinuxSem.Checks.Witness.Mm.Mprotect

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Mprotect
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.Checks.Witness.Prelude

/-- The `mprotect` (226) witness.

    The same argument gates as `mprotect_spec`, in the same order, each of
    which the spec answers with one `err_ret` / `ret_only`; then, for the
    one `prot` the model interprets, one outcome out of each answered
    shape:

    - over a range contained in one tracked `vm_noaccess` interval and one
      tracked `vm_maps` entry the spec offers `alt (injected errno)
      (exposure)`; the witness exhibits the INJECTED errno — ENOMEM, the
      head of `mprotect_errnos` (`witness_errno`), with the state
      untouched.  The exposure is the `alt`'s other arm, and progress
      needs only one;
    - over a range inside a live `vm_maps` entry and clear of
      `vm_noaccess` it exhibits the already-rw no-op: 0, no effect;
    - anywhere else the model declines, which is `.unmodeled`.

    A `prot` the model does not answer is `.unmodeled` too, at nonzero
    length, exactly where the spec declines. -/
def mprotect_witness (addr len prot : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if mprotect_grows_conflict_b prot then
    ret_outcome (errno_ret EINVAL) m
  else if !(((addr.toNat : Int) % page_size) == 0) then
    ret_outcome (errno_ret EINVAL) m
  else if w_is0 len then ret_outcome (BitVec.ofInt 64 0) m
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    ret_outcome (errno_ret ENOMEM) m
  else if mprotect_modeled_b prot then
    let nZ := page_round_up_Z (len.toNat : Int)
    let n := BitVec.ofInt 64 nZ
    if map_contains (m_vmmaps m).vm_noaccess addr n &&
        map_contains (m_vmmaps m).vm_maps addr n then
      ret_outcome (errno_ret witness_errno) m
    else if map_contains (m_vmmaps m).vm_maps addr n &&
        region_free (m_vmmaps m).vm_noaccess addr n then
      ret_outcome (BitVec.ofInt 64 0) m
    else .unmodeled
  else .unmodeled

section

-- The witness's last arm is a `match`-shaped `if` chain that the proof
-- drives together with the spec's; the default recursion budget is not
-- enough to unify the instantiated alternatives.
set_option maxRecDepth 1000000

theorem mprotect_witness_ok (addr len prot : word) (i : SyscallInput)
    (m : Model) :
    mprotect_spec addr len prot i m (mprotect_witness addr len prot m) := by
  unfold mprotect_spec mprotect_witness
  by_cases hgrows : mprotect_grows_conflict_b prot = true
  · repeat rw [ite_eq_left hgrows]
    exact pure_ok _ i m
  · repeat rw [ite_eq_right hgrows]
    by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
    · repeat rw [ite_eq_left halign]
      exact pure_ok _ i m
    · repeat rw [ite_eq_right halign]
      by_cases hlen : w_is0 len = true
      · repeat rw [ite_eq_left hlen]
        exact pure_ok _ i m
      · repeat rw [ite_eq_right hlen]
        by_cases hbig : two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · repeat rw [ite_eq_left hbig]
          exact pure_ok _ i m
        · repeat rw [ite_eq_right hbig]
          by_cases hmod : mprotect_modeled_b prot = true
          · repeat rw [ite_eq_left hmod]
            dsimp only
            rw [bind_getModel]
            by_cases hcover : (map_contains (m_vmmaps m).vm_noaccess addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
              map_contains (m_vmmaps m).vm_maps addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
            · -- the range is protected: exhibit the injected -ENOMEM
              repeat rw [ite_eq_left hcover]
              exact alt_l _ _ i m _
                (bind_step (errno_from mprotect_errnos) (fun e => err_ret e) i m
                  ENOMEM m _
                  (errno_head_witness ENOMEM [] i m) (pure_ok _ i m))
            · repeat rw [ite_eq_right hcover]
              by_cases hrw : (map_contains (m_vmmaps m).vm_maps addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) &&
                region_free (m_vmmaps m).vm_noaccess addr
                  (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int)))) = true
              · -- the already-rw no-op: 0, no effect
                repeat rw [ite_eq_left hrw]
                exact pure_ok _ i m
              · repeat rw [ite_eq_right hrw]
                exact unmodeled_intro i m
          · repeat rw [ite_eq_right hmod]
            exact unmodeled_intro i m

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the witness
    and its one proof.  The checks below are sanity checks: they pin the two
    shapes the proof takes, the fail-closed decline for a `prot` the model
    does not answer and the zero-length answer, which the argument gates
    fix before `prot` is read. -/

/-- A `prot` the model does not answer at nonzero length is the
    fail-closed `.unmodeled`. -/
example (m : Model) :
    mprotect_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 PROT_NONE) m = .unmodeled := by
  unfold mprotect_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)]

/-- Zero length answers 0 for EVERY `prot`, including PROT_NONE. -/
example (m : Model) :
    mprotect_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 PROT_NONE) m =
      ret_outcome (BitVec.ofInt 64 0) m := by
  unfold mprotect_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

end LinuxSem.Checks.Witness.Mm.Mprotect
