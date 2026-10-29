/-
  * LinuxProcessSem.Checks.Witness.Kernel.Futex.Syscalls — the futex (98) witness, and its proof

  Answers to Linux [kernel/futex/syscalls.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and
  re-exports this module. A witness here exhibits one admissible
  outcome for a spec in the matching [Sys] module, which is what
  progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, declining as
  `.unmodeled` and answering `.ok …` on the accepted arms; `ret_outcome` is
  `Checks.Witness.Prelude`'s helper — the same "return `r`, change nothing,
  emit nothing" outcome the spec's `ret_only` produces — and `mkEffect` is
  the no-unmap/no-copy abbreviation of `SyscallEffect`.  The `FUTEX_*`
  words are `Sys.Uapi`'s, and the `-EAGAIN` ledger width is
  `FUTEX_WORD_SIZE_nat`.

  The gate is written out here again; [Checks/Sys/Fs/Timerfd] says why the
  three layers restate it rather than share one predicate.  As in the
  checker file, the statement spells
  `!((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)`, which is the DEFINITION
  of `futex_aligned_b`; the proof unfolds both, so it is literally the same
  test on the same term as the spec's.

  Each proof makes one `unfold` of
  `futex_spec`/`futex_witness`/`futex_wake_private_spec`/
  `futex_wait_private_spec`/`futex_key_check`/`futex_aligned_b`, then runs
  the `cases` chain, closing the branch answers by `rfl` (they are the same
  term in both) except where the spec's answer is a `record_copyins` —
  there the Prelude lemmas `record_copyins_unmodeled` and
  `record_copyins_ok_empty` supply the step.  The one `bind` step is
  `bind_step` + `input_ok`.  `cases` on the read's `Option` leaves the
  branch body under the match's pattern variable, so the `some` arm states
  that body with `show` first — the two are definitionally equal, and the
  `show` is what puts the value back in reach of the last case split.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

namespace LinuxSem.Checks.Witness.Kernel.Futex.Syscalls

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi (FUTEX_WAKE FUTEX_WAIT FUTEX_WAKE_PRIVATE
  FUTEX_WAIT_PRIVATE FUTEX_WORD_SIZE)
open LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxSem.Checks.Witness.Prelude

/-- The gate is written out for the third time; [Checks/Sys/Fs/Timerfd]
    says why the three layers restate it rather than share one
    predicate.

    [Unmodeled] IS an admissible outcome, so the declined halves need no
    invented answer — the spec's own arm is [unmodeled], and exhibiting
    it is what makes this total.  [timerfd_create_witness] takes the
    same shape for the same reason.  Every arm of this spec is a single
    answer rather than a choice, so the witness is the spec read back:
    there is no environment nondeterminism here for it to pick a member
    of.

    The timeout test comes FIRST on the wait arm, before either gate,
    because that is the kernel's order:
    `SYSCALL_DEFINE6(futex)` reads the timeout (and `get_timespec64` can
    fail on it) before `do_futex` reaches `get_futex_key`.  The spec nests
    it the same way, and the witness follows the spec branch for branch —
    the matching [Sys] module is where that order is stated. -/
def futex_witness (uaddr op val utime : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE)
  then (if !((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)
        then ret_outcome (errno_ret EINVAL) m
        else if !access_okb uaddr FUTEX_WORD_SIZE
        then ret_outcome (errno_ret EFAULT) m
        else ret_outcome (BitVec.ofInt 64 0) m)
  else if bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE)
  then (if !w_is0 utime then .unmodeled
        else if !((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)
        then ret_outcome (errno_ret EINVAL) m
        else if !access_okb uaddr FUTEX_WORD_SIZE
        then ret_outcome (errno_ret EFAULT) m
        else
          match read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
          | none => .unmodeled
          | some uval =>
              if bv_eqb (le_bytes_to_word uval) (abi_low32 val) then .unmodeled
              else .ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
                          (mkEffect (errno_ret EAGAIN) [] [])) m [])
  else .unmodeled

theorem futex_witness_ok (uaddr op val utime : word) (i : SyscallInput) (m : Model) :
    futex_spec uaddr op val utime i m (futex_witness uaddr op val utime i m) := by
  unfold futex_spec futex_witness futex_wake_private_spec futex_wait_private_spec
    futex_key_check futex_aligned_b
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    cases ha : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
    | false =>
      rfl
    | true =>
      cases hok : access_okb uaddr FUTEX_WORD_SIZE with
      | false =>
        rfl
      | true =>
        rfl
  | false =>
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      rfl
    | true =>
      cases ht : w_is0 utime with
      | false =>
        rfl
      | true =>
        cases ha : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
        | false =>
          rfl
        | true =>
          cases hok : access_okb uaddr FUTEX_WORD_SIZE with
          | false =>
            rfl
          | true =>
            refine bind_step input _ i m i m _ (input_ok i m) ?_
            cases hr : read_bytes_map i.in_mem uaddr
                (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
            | none =>
              rfl
            | some uval =>
              show record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
                (if bv_eqb (le_bytes_to_word uval) (abi_low32 val) = true then unmodeled
                 else err_ret EAGAIN) i m
                (if bv_eqb (le_bytes_to_word uval) (abi_low32 val) = true then .unmodeled
                 else .ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
                             (mkEffect (errno_ret EAGAIN) [] [])) m [])
              cases hv : bv_eqb (le_bytes_to_word uval) (abi_low32 val) with
              | false =>
                simp only [Bool.false_eq_true, ite_false]
                exact record_copyins_ok_empty rfl
                  (pure_ok (M := Model) (I := SyscallInput) (E := event)
                    (mkEffect (errno_ret EAGAIN) [] []) i m)
              | true =>
                simp only [ite_true]
                exact record_copyins_unmodeled (unmodeled_intro i m)

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the two
    answers the witness's gate order produces, and the timeout-first
    order of the wait arm; the branch equations are the same ones the
    proof above follows. -/

/-- A misaligned address is the -EINVAL outcome, before the range test. -/
example (i : SyscallInput) (m : Model) :
    futex_witness 1 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 0 i m
      = ret_outcome (errno_ret EINVAL) m := by
  simp only [futex_witness]
  rw [ite_eq_left (by decide), ite_eq_left (by decide)]

/-- An aligned, in-range address wakes with 0 — the witness does not
    resolve the page either. -/
example (i : SyscallInput) (m : Model) :
    futex_witness (BitVec.ofInt 64 0x2000) (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 0 i m
      = ret_outcome (BitVec.ofInt 64 0) m := by
  simp only [futex_witness]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

/-- A non-NULL timeout declines on the wait arm before the address is
    looked at: the answer is [Unmodeled], not an errno. -/
example (i : SyscallInput) (m : Model) :
    futex_witness 1 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 2 0x1000 i m = .unmodeled := by
  simp only [futex_witness]
  rw [ite_eq_right (by decide), ite_eq_left (by decide), ite_eq_left (by decide)]

/-- The shared wake word is not the private one, and the witness declines
    it: the key would not be the caller's mm. -/
example (i : SyscallInput) (m : Model) :
    futex_witness 0 (BitVec.ofInt 64 FUTEX_WAKE) 0 0 i m = .unmodeled := by
  simp only [futex_witness]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

end LinuxSem.Checks.Witness.Kernel.Futex.Syscalls
