/-
  * LinuxSem.Checks.Cases.Kernel.Futex.Syscalls — worked examples over futex (98)

  Worked cases over `Sys.Kernel.Futex.Syscalls`, which answers to Linux
  [kernel/futex/syscalls.c]: the examples for the syscalls defined there,
  and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  `Z` is `Int`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
  `bv_unsigned w` is `(w.toNat : Int)` (`LinuxSem.Common.RocqSpelling`'s, as
  throughout this tree), `Ok …`/`unmodeled` are `.ok …`/`.unmodeled`,
  `mkEffect` is `State.mkEffect`, `mkInput` is the `SyscallInput`
  constructor, and `input`/`pure` are the monad's.

  `Z.land` has no counterpart.  `Int` carries no bitwise-and, so the two
  gate lemmas state the same claim with the guard written
  `flags.toNat &&& CLONE_VM.toNat = 0` — the SAME FUNCTION on the
  non-negative operands (`bv_unsigned flags` is a `Nat` cast and both
  constants are positive), and the spelling
  `Sys.Mm.Mmap.mmap_flags_core_id` is itself stated in.  Nothing is
  weakened; the `decide` that closes each lemma works on the very same
  bit pattern.

  Proofs.  The two answer lemmas are the ones
  `Sys.Kernel.Futex.Syscalls` proves in the other direction, so the file
  takes the spec's own gate inversion ([futex_key_check_ok_iff]) rather
  than destructing the checker's condition inline: the gate disjunction
  hands back the two errno effects and, in the third arm, the command's
  own body, which [input_bind_ok_inv]/[record_copyins_ok_inv] peel.  The
  branch's conjunction is `⟨rfl, rfl, _⟩`.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Futex.Syscalls
import LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.Checks
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Futex.Syscalls
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Kernel.Futex.Syscalls

open LinuxSem.Common.RocqSpelling

/-! `bv_unsigned` and `Z_to_bv` come from `LinuxSem.Common.RocqSpelling`,
    opened above. -/

/-! ## Three answers and no fourth

    Two lemmas, and no fourth answer exists for any address. -/

/-- THREE ANSWERS AND NO FOURTH, for every address at once.

    ADMISSION REASON: universally quantified.  A run can reach each of
    the three on one address apiece; what no set of traces can show is
    that there is
    no address at all for which a private wake answers something else.
    The statement also pins two things a program's view of a return value
    does not reveal: the model that comes back is the SAME model, and the
    event list is empty — a wake is inert.

    Read the disjunction as [get_futex_key]'s two refusals
    (kernel/futex/core.c) followed by the count [futex_wake]
    (kernel/futex/waitwake.c) returns, which is 0 because the waiter set
    of a private key is empty here (the spec's header argues it).  That
    the count is 0 rather than the errno of an unresolvable page is the
    content: no arm of this disjunction depends on what is mapped. -/
theorem futex_wake_private_answers (uaddr : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : futex_wake_private_spec uaddr i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧
    (eff = mkEffect (errno_ret EINVAL) [] []
     ∨ eff = mkEffect (errno_ret EFAULT) [] []
     ∨ eff = mkEffect (Z_to_bv 64 0) [] []) := by
  have H' : futex_key_check uaddr (ret_only (BitVec.ofInt 64 0)) i m
      (.ok eff m' evs) := H
  have hd := (futex_key_check_ok_iff uaddr (ret_only (BitVec.ofInt 64 0)) i m
    eff m' evs).mp H'
  rcases hd with ⟨hal, heff, hm, hev⟩ | ⟨hal, hok, heff, hm, hev⟩ | ⟨hal, hok, Hk⟩
  · exact ⟨hm, hev, Or.inl heff⟩
  · exact ⟨hm, hev, Or.inr (Or.inl heff)⟩
  · simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
      Outcome.ok.injEq] at Hk
    obtain ⟨rfl, rfl, rfl⟩ := Hk
    exact ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩

/-- A WAIT NEVER SUCCEEDS, for every address and every expected value at
    once.

    ADMISSION REASON: universally quantified, and the same two
    model-internal facts.  A private [FUTEX_WAIT] this model answers has
    exactly one non-gate answer, -EAGAIN, and it carries the four-byte
    copy-in — so a run in which the wait slept and was woken, which is
    what a 0 return means ([__futex_wait] reaches its [return 0] only
    after [futex_unqueue] finds the entry already dequeued), is not an
    outcome this spec admits on any input.  That is the claim the
    single-task argument rests on, stated where it can be checked: there
    is no address on which a 0 would be accepted. -/
theorem futex_wait_private_answers (uaddr val : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : futex_wait_private_spec uaddr val i m (.ok eff m' evs)) :
    m' = m ∧ evs = [] ∧
    (eff = mkEffect (errno_ret EINVAL) [] []
     ∨ eff = mkEffect (errno_ret EFAULT) [] []
     ∨ eff = with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
              (mkEffect (errno_ret EAGAIN) [] [])) := by
  have H' : futex_key_check uaddr
      (bind input (fun i0 =>
        match read_bytes_map i0.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
        | none => unmodeled
        | some uval =>
            record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
              (if bv_eqb (le_bytes_to_word uval) val then unmodeled
               else err_ret EAGAIN)))
      i m (.ok eff m' evs) := H
  have hd := (futex_key_check_ok_iff uaddr _ i m eff m' evs).mp H'
  rcases hd with ⟨hal, heff, hm, hev⟩ | ⟨hal, hok, heff, hm, hev⟩ | ⟨hal, hok, Hk⟩
  · exact ⟨hm, hev, Or.inl heff⟩
  · exact ⟨hm, hev, Or.inr (Or.inl heff)⟩
  · have hb := input_bind_ok_inv
      (fun i0 : SyscallInput =>
        match read_bytes_map i0.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
        | none => unmodeled
        | some uval =>
            record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
              (if bv_eqb (le_bytes_to_word uval) val then unmodeled
               else err_ret EAGAIN))
      i m eff m' evs Hk
    cases hr : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
    | none =>
      rw [hr] at hb
      try dsimp only at hb
      exact nomatch hb
    | some uval =>
      rw [hr] at hb
      try dsimp only at hb
      cases hv : bv_eqb (le_bytes_to_word uval) val with
      | true =>
        rw [hv] at hb
        try dsimp only at hb
        exact nomatch hb
      | false =>
        rw [hv] at hb
        try dsimp only at hb
        obtain ⟨core, Hcore, heff⟩ :=
          record_copyins_ok_inv [(uaddr, FUTEX_WORD_SIZE_nat)] (err_ret EAGAIN)
            i m eff m' evs hb
        simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
          Outcome.ok.injEq] at Hcore
        obtain ⟨rfl, rfl, rfl⟩ := Hcore
        refine ⟨rfl, rfl, Or.inr (Or.inr ?_)⟩
        rw [heff]
        rfl

/-! ## The clone gates

    The two gate lemmas: no clone gate ever grants [CLONE_VM]. -/

/-- NO CLONE GATE EVER GRANTS [CLONE_VM], which is the one cross-file
    premise the answers above rest on.

    ADMISSION REASON: universally quantified, and about a syscall this
    file does not otherwise concern itself with.  [futex_wake_private_spec]
    answers 0 because no task shares the caller's mm, and the reason no
    task does is that [Kernel.Fork]'s two gates admit one flag word each
    and neither sets the bit.  That is an argument across two files, so
    it is exactly the kind that rots silently: a later change widening
    [clone] to a flag MASK, or adding a second admitted word, would leave
    every futex proof closing and the count wrong.

    These two make the premise a compile-time fact instead.  Widening
    either gate to admit [CLONE_VM] breaks the build HERE, next to the
    prose that says why it matters, rather than nowhere. -/
theorem clone_fork_gate_grants_no_shared_mm (flags : word)
    (H : clone_fork_flags_b flags = true) :
    flags.toNat &&& CLONE_VM.toNat = 0 := by
  have hflags : flags = BitVec.ofInt 64 SIGCHLD := by
    simpa only [clone_fork_flags_b, bv_eqb, beq_iff_eq] using H
  rw [hflags]
  decide

theorem clone3_fork_gate_grants_no_shared_mm (bs : List byte)
    (H : clone3_fork_args_b bs = true) :
    (clone_args_field bs 0).toNat &&& CLONE_VM.toNat = 0 := by
  have h0 : w_is0 (clone_args_field bs 0) = true := by
    have h := H
    unfold clone3_fork_args_b at h
    simp only [Bool.and_eq_true] at h
    simp_all
  have hfield : clone_args_field bs 0 = BitVec.ofInt 64 0 := by
    simpa only [w_is0, bv_eqb, beq_iff_eq] using h0
  rw [hfield]
  decide

end LinuxSem.Checks.Cases.Kernel.Futex.Syscalls
