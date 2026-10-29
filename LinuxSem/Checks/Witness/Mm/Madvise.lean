/-
  * LinuxProcessSem.Checks.Witness.Mm.Madvise — the madvise (233) witness, and its proof

  Answers to Linux [mm/madvise.c]: this file holds the witness for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled`.  The `<=?` gate is the spec's `Prop` form
  `two_pow_64 ≤ …` (see `Sys/Mm/Madvise.lean`), so it is split with
  `by_cases`, while the other gates are `Bool` equations.

  As in `Checks/Witness/Mm/Mprotect.lean`, every gate test occurs twice in
  the goal after the two definitions are unfolded — once in the spec
  (`SysSpec` type) and once in the witness (`Outcome` type) — and a single
  `rw [ite_eq_left h]` instantiates the lemma at ONE type, so the gates are
  closed with `repeat rw`, which reaches both sides.  The two monadic steps
  are `bind_step` of `Checks.Witness.Prelude`, with `try dsimp only` after
  each of them.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Mm.Madvise

namespace LinuxSem.Checks.Witness.Mm.Madvise

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Mm.Madvise
open LinuxSem.Checks.Witness.Prelude

/-- madvise witness: the spec has no nondeterminism, so the witness is
    the spec's one answer at every gate — -EINVAL on a misaligned
    address or a wrapping range, 0 at zero length, the zero-fill with
    the returned charges on the answered shape, and [Unmodeled] (fail
    closed) on any other advice value or any range the ledger does not
    describe as one read-write anonymous mapping (see
    [Madvise.madvise_spec]).

    The gate order is the spec's, which is the kernel's: alignment, then
    the advice, then the zero length, then the wrapping range, then the
    ledger (`is_valid_madvise`'s four refusals all precede the
    zero-length exit — see `Sys/Mm/Madvise.lean`'s header). -/
def madvise_witness (addr len advice : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(((addr.toNat : Int) % page_size) == 0) then
    ret_outcome (errno_ret EINVAL) m
  else if !madvise_dontneed_b advice then .unmodeled
  else if w_is0 len then ret_outcome (BitVec.ofInt 64 0) m
  else if two_pow_64 ≤ (addr.toNat : Int) + page_round_up_Z (len.toNat : Int) then
    ret_outcome (errno_ret EINVAL) m
  else
    let nZ := page_round_up_Z (len.toNat : Int)
    let n := BitVec.ofInt 64 nZ
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      .ok (mkEffect (BitVec.ofInt 64 0) [] [(addr, n)])
        (madvise_dontneed_next m addr n) []
    else .unmodeled

section

-- The witness's last arm is an `if` chain that the proof drives together
-- with the spec's, and the default recursion budget is not enough to
-- unify the instantiated alternatives through the two gate copies.
set_option maxRecDepth 1000000

theorem madvise_witness_ok (addr len advice : word) (i : SyscallInput)
    (m : Model) :
    madvise_spec addr len advice i m (madvise_witness addr len advice m) := by
  unfold madvise_spec madvise_witness
  by_cases halign : (!(((addr.toNat : Int) % page_size) == 0)) = true
  · repeat rw [ite_eq_left halign]
    exact pure_ok _ i m
  · repeat rw [ite_eq_right halign]
    by_cases hadv : (!madvise_dontneed_b advice) = true
    · repeat rw [ite_eq_left hadv]
      exact unmodeled_intro i m
    · repeat rw [ite_eq_right hadv]
      by_cases hlen : w_is0 len = true
      · repeat rw [ite_eq_left hlen]
        exact pure_ok _ i m
      · repeat rw [ite_eq_right hlen]
        by_cases hbig : two_pow_64 ≤
            (addr.toNat : Int) + page_round_up_Z (len.toNat : Int)
        · repeat rw [ite_eq_left hbig]
          exact pure_ok _ i m
        · repeat rw [ite_eq_right hbig]
          dsimp only
          by_cases hok : madvise_dontneed_ok (m_vmmaps m) addr
              (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))) = true
          · -- the answered shape: give the charges back, zero-fill the range
            repeat rw [ite_eq_left hok]
            refine bind_step getModelSpec _ i m m m _ rfl ?_
            try dsimp only
            repeat rw [ite_eq_left hok]
            refine bind_step
              (modify fun _ => madvise_dontneed_next m addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))))
              _ i m ()
              (madvise_dontneed_next m addr
                (BitVec.ofInt 64 (page_round_up_Z (len.toNat : Int))))
              _ (modify_ok _ i m) ?_
            exact pure_ok _ i _
          · -- a range the ledger does not describe: decline
            repeat rw [ite_eq_right hok]
            refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
            try dsimp only
            repeat rw [ite_eq_right hok]
            exact unmodeled_intro i m

end

/-! ## Sanity checks

    The module's proofs leave no `vm_compute` goal — it is the witness
    and its one proof.  The checks below are sanity checks: they pin the
    gate order the witness shares with the spec, which is the kernel's
    (`is_valid_madvise`'s four refusals precede the zero-length exit), and
    the two fail-closed declines. -/

/-- A misaligned address is -EINVAL for EVERY advice value — the
    alignment gate is first, so the witness never reads the advice. -/
example (m : Model) (len : word) :
    madvise_witness (BitVec.ofInt 64 0x1001) len (BitVec.ofInt 64 99) m =
      ret_outcome (errno_ret EINVAL) m := by
  unfold madvise_witness
  rw [ite_eq_left (by decide)]

/-- An advice value other than MADV_DONTNEED declines at an aligned,
    nonzero-length address — fail closed, not -EINVAL. -/
example (m : Model) :
    madvise_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 99) m = .unmodeled := by
  unfold madvise_witness
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- Zero length answers 0 — behind the alignment and advice gates, which
    is what makes the kernel's ordering observable. -/
example (m : Model) :
    madvise_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 4) m = ret_outcome (BitVec.ofInt 64 0) m := by
  unfold madvise_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A length whose page rounding wraps is -EINVAL, again behind the
    earlier gates. -/
example (m : Model) :
    madvise_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0xFFFFFFFFFFFFFFFF)
        (BitVec.ofInt 64 4) m = ret_outcome (errno_ret EINVAL) m := by
  unfold madvise_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A range the ledger does not own declines rather than answering the
    walk's -ENOMEM: the arguments pass every gate, but the range is not
    inside one live anonymous mapping of the empty ledger the witness
    is handed. -/
example (m : Model) (hm : m_vmmaps m = mkVmMaps [] [] (BitVec.ofInt 64 0)
    (BitVec.ofInt 64 0) 0x100000) :
    madvise_witness (BitVec.ofInt 64 0x1000) (BitVec.ofInt 64 0x1000)
        (BitVec.ofInt 64 4) m = .unmodeled := by
  unfold madvise_witness
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), hm,
    ite_eq_right (by decide)]

end LinuxSem.Checks.Witness.Mm.Madvise
