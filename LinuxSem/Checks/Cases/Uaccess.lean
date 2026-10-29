/-
  * LinuxProcessSem.Checks.Cases.Uaccess — worked examples over the user-buffer boundary

  Worked cases over `Sys.Uaccess`, which answers to the kernel uaccess
  headers — the range test it transcribes is [__access_ok]
  (include/asm-generic/access_ok.h at v6.18.46), not anything
  include/linux/uaccess.h defines.  This file holds the worked
  examples for that range guard, and no syscall's own arms.

  `Checks.Examples` keeps what is not per-syscall and
  re-exports this module.  These are worked examples
  over the specs and checkers for the matching [Sys] module, read off
  without running a binary.

  Spelling.  `Z` is `Int`, `word` is `BitVec 64`, `Z_to_bv n z` is
  `BitVec.ofInt n z`, and `bv_unsigned w` is `(w.toNat : Int)`.  A `Z`
  comparison is a `Bool` here, so it is written `decide (a < b)` /
  `decide (a ≤ b)`; the `if … then … else` and the `&&` chains around
  it keep their shape and their evaluated value.  `Z_to_bv 8 0` is
  `BitVec.ofInt 8 0`.

  Proofs.  A closed decidable goal is discharged by `decide` — a `Bool`
  equality, or an `Option` non-equality — and `rfl` closes
  [access_ok_zero_faults_on_the_wrap], whose two sides are the same term
  once the guard's `if` reduces.  None of these is a super-linear
  computation: the widest walk below is eight bytes.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Syscall

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Uaccess

/-! ## The range check and the byte walk, where they disagree

    [State.access_okb] tests a range as [__access_ok] does, by a
    SUBTRACTION in `Int`; [State.read_bytes_map] walks `buf`, `buf + 1`,
    ... in WORD arithmetic and so WRAPS at 2^64.  A range that starts
    just under the top of the address space therefore walks off the end,
    comes back at 0, and reads in full — while its exact end is past
    [State.TASK_SIZE].  These examples pin that the guard every
    zero-delivery arm asks, [Uaccess.access_ok_zero], answers -EFAULT
    there and does not let the walk speak for it.

    A real run cannot reach this.  An Sv48
    kernel maps nothing at or above 2^47 ([TASK_SIZE],
    arch/riscv/include/asm/pgtable.h, v6.18.46) — let alone at the top
    of the 64-bit space, where a wrapping range has to start.  So no
    wrapping range is expressible there at all.  It is reachable in the
    DEFINITION, which is what matters — [Equivalence.strong_universal_T]
    quantifies over the image freely, and nothing bounds a
    segment's address.  So this
    is the third reason a case belongs in this file: it pins model-internal
    state no observation reveals.

    [wrap_buf] is 2^64 - 4 and the count is 8, so the walk covers the
    four bytes below 2^64 and the four at 0.  [wrap_mem] maps exactly
    those eight and nothing else. -/

/-- `buf` for the wrapping range: 2^64 - 4, four bytes below the top of the
    address space. -/
def wrap_buf : word := BitVec.ofInt 64 (2 ^ 64 - 4)

/-- The map the wrapping range reads: the four bytes at 0 and the four
    below 2^64, and nothing else — every one of them zero. -/
def wrap_mem : word → Option byte :=
  fun a => if decide ((a.toNat : Int) < 4) || decide (2 ^ 64 - 4 ≤ (a.toNat : Int))
           then some (BitVec.ofInt 8 0) else none

/-- The walk really does wrap: all eight bytes read, so a guard that
    trusted the walk would call the range mapped end to end. -/
theorem wrap_range_reads_across_the_top :
    read_bytes_map wrap_mem wrap_buf (BitVec.ofInt 64 8) ≠ none := by
  decide

/-- And the kernel's predicate refuses it: `size` is 8, comfortably
    under [TASK_SIZE], so the first half passes, and it is
    `addr <= TASK_SIZE - 8` that 2^64 - 4 violates. -/
theorem wrap_range_is_refused : access_okb wrap_buf 8 = false := by
  decide

/-- THE ONE THAT MATTERS: the arm's verdict is the range's, whatever
    the walk says.  Delete the range test from [access_ok_zero] and let
    a mapping walk decide, and this theorem fails — which is the whole
    of the guard's mutation test. -/
theorem access_ok_zero_faults_on_the_wrap (k : SysSpec SyscallEffect) :
    access_ok_zero wrap_buf (BitVec.ofInt 64 8) k = err_ret EFAULT :=
  rfl

/-- THE MUTATION TEST, MADE PERMANENT rather than performed once: the
    mapping walk alone, evaluated on the same witness, says the range is
    fine, which is the wrong answer.  Pinning it here is what stops the
    theorem above from going vacuous — it would also pass if [wrap_mem]
    quietly stopped mapping the range, or if [wrap_buf] stopped wrapping,
    and then it would be testing nothing. -/
theorem wrap_would_pass_a_bare_walk :
    ((match read_bytes_map wrap_mem wrap_buf (BitVec.ofInt 64 8) with
      | some _ => true | none => false)
     && (match read_bytes_map wrap_mem wrap_buf (BitVec.ofInt 64 1) with
        | some _ => true | none => false)) = true := by
  decide

/-! ## Past [TASK_SIZE], where a range does NOT wrap and is still refused

    The wrap is not the only way a walk-based argument fails, and a
    guard that only closed the wrap would still be wrong.  `buf = 2^63`
    with `count = 8` does NOT wrap — its `Int` sum is 2^63 + 8, comfortably
    under 2^64, so the walk visits exactly the bytes the sum names — and
    [access_ok] refuses it anyway, because [__access_ok] tests
    `addr <= TASK_SIZE - size`.

    THIS IS THE CASE THAT DISCRIMINATES THE GUARD.  A plain no-wrap test
    at 2^64 passes here and would answer the arm's 0; only asking
    [State.access_okb], the kernel's own predicate, answers -EFAULT.
    Same reason as the wrap for belonging here: an Sv48 kernel cannot map
    2^63 either. -/

/-- The map the high range reads: the eight bytes from 2^63, all zero. -/
def high_mem : word → Option byte :=
  fun a => if decide (2 ^ 63 ≤ (a.toNat : Int))
              && decide ((a.toNat : Int) < 2 ^ 63 + 8)
           then some (BitVec.ofInt 8 0) else none

/-- The range is mapped end to end, exactly as the wrapping one was. -/
theorem high_range_reads :
    read_bytes_map high_mem (BitVec.ofInt 64 (2 ^ 63)) (BitVec.ofInt 64 8) ≠ none := by
  decide

/-- And it does NOT wrap — so a no-wrap conjunct would have admitted it.
    This is the mutation test for [access_okb] itself, in the same
    permanent form as [wrap_would_pass_a_bare_walk] above. -/
theorem high_range_would_pass_a_no_wrap_test :
    (decide (two_pow_64 ≤ ((BitVec.ofInt 64 (2 ^ 63)).toNat : Int)
                  + ((BitVec.ofInt 64 8).toNat : Int)) : Bool) = false := by
  decide

theorem high_range_is_refused : access_okb (BitVec.ofInt 64 (2 ^ 63)) 8 = false := by
  decide

/-! ## The boundary itself, from both sides

    [State.TASK_SIZE] is 2^47 — the Sv48 [TASK_SIZE_64] — and
    [__access_ok] admits a range whose exact end
    is AT the limit and refuses one that ends one byte past it.  The edge
    is reached three ways: through the count with `buf = 0`, through the
    base with `count = 0`, and with the last eight bytes of the space.
    ([access_okb]'s size conjunct is implied by its address conjunct in
    `Int`; it is there to mirror the kernel's unsigned subtraction, not as
    a separately pinnable half.) -/

theorem task_size_is_the_sv48_top : TASK_SIZE = 2 ^ 47 := by
  rfl

theorem access_ok_at_the_top : access_okb (BitVec.ofInt 64 (2 ^ 47)) 0 = true := by
  decide

theorem access_ok_one_past_the_top : access_okb (BitVec.ofInt 64 (2 ^ 47 + 1)) 0 = false := by
  decide

theorem access_ok_last_eight_bytes :
    access_okb (BitVec.ofInt 64 (2 ^ 47 - 8)) 8 = true := by
  decide

theorem access_ok_last_eight_bytes_shifted_by_one :
    access_okb (BitVec.ofInt 64 (2 ^ 47 - 7)) 8 = false := by
  decide

theorem access_ok_whole_space : access_okb (BitVec.ofInt 64 0) (2 ^ 47) = true := by
  decide

theorem access_ok_whole_space_plus_one :
    access_okb (BitVec.ofInt 64 0) (2 ^ 47 + 1) = false := by
  decide

/-! ## The older [LONG_MAX] limit, pinned as wrong

    [LONG_MAX] was riscv64's [TASK_SIZE_MAX] between v6.10-rc1 (commit
    ad5643cf2f69) and v6.16-rc3 (reverted by 890ba5be6335).  A check
    against it ACCEPTS every range ending under 2^63.  At v6.18.46 the
    limit is [TASK_SIZE], and a range at 2^60 is refused.  The two
    examples together are what separates the constants: change
    [TASK_SIZE] to [LONG_MAX], in the spec and the checker at once, and
    [task_size_refuses_the_band] fails while everything the biconditional
    proofs cover stays green. -/

/-- `__access_ok` against the OLD limit: the kernel's own shape, with
    `TASK_SIZE` replaced by 2^63 - 1.  The file's control. -/
def long_max_access_okb (base : word) (len : Int) : Bool :=
  decide (len ≤ 2 ^ 63 - 1) && decide ((base.toNat : Int) ≤ 2 ^ 63 - 1 - len)

theorem long_max_would_admit_the_band :
    long_max_access_okb (BitVec.ofInt 64 (2 ^ 60)) 8 = true := by
  decide

theorem task_size_refuses_the_band : access_okb (BitVec.ofInt 64 (2 ^ 60)) 8 = false := by
  decide

end LinuxSem.Checks.Cases.Uaccess
