/-
  * LinuxSem.Checks.Cases.Fs.EventFd — worked examples over eventfd2 (19)

  Worked cases over `Sys.Fs.EventFd`, which answers to Linux [fs/eventfd.c]:
  the examples for the syscalls defined there, and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have are supplied as local transparent `abbrev`s below,
  DEFINITIONALLY EQUAL to what they stand for, so every statement below
  denotes exactly the same claim:
  - `bv_unsigned w` is `(w.toNat : Int)` and `Z_to_bv n z` is
    `BitVec.ofInt n z`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`;
  - `nth_error l n` is `l[n]?` and `existsb p l` is `l.any p`;
  - `bv_leu`/`bv_ltu` come from `Riscv.Prelude`, reached through
    `open LinuxSem.Riscv`, so they need no shim;
  - a record field is read by dot notation here (`e.eff_writes`), the
    same projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim;
  - constructors of an inductive live in the type's namespace, so the
    bare `FdChannel`/`FdFile`/… are `FdEntry.FdChannel`/… and `SkFresh`
    is `SockState.SkFresh`.  `mkInput` is `SyscallInput.mkInput`;
    `mkEffect`/`mkModel`/`mkVmMaps`/`errno_ret` are plain definitions
    and keep their bare names.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.

  Imports.  `Checks.Cases.Prelude` (and, where it is needed,
  `Checks.Cases.Fs.ReadWrite`) is imported directly; the re-export for
  the tree above this file is left to the root module.

  Flag words.  `efd_in`'s two parameters are `Int`, so every `2 ^ n`
  below is an `Int` power wrapped once by `Z_to_bv 64` at the syscall
  boundary.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Fs.EventFd
import LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.EventFd
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.EventFd
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.EventFd

open LinuxSem.Common.RocqSpelling

/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/

/-! * LinuxSem.Checks.Cases.Fs.EventFd — worked examples over eventfd2 (19)

    Worked cases over `Sys.Fs.EventFd`, which answers to Linux [fs/eventfd.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

/-! [eventfd2] reads no field of the model, so the state here only has
    to exist.  Three channels and nothing else, as [timerfd_model] is. -/
def eventfd_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof []

/-! The counter comes FIRST and the flag word second, which is the one
    thing about this call's shape a reader is likely to get backwards.
    [efd_in] is written to make that visible at every use site. -/
def efd_in (count flags : Int) : SyscallInput :=
  SyscallInput.mkInput 19 [Z_to_bv 64 count, Z_to_bv 64 flags, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-! THE FLAG BITS, ONE AT A TIME.
    These examples walk single bits, and carry what a return value
    alone cannot show — the second conjunct below.

    Linux answers -EINVAL for ANY bit outside
    [EFD_CLOEXEC|EFD_NONBLOCK|EFD_SEMAPHORE] (fs/eventfd.c,
    [do_eventfd], v6.18.46), and the spec follows.

    The second conjunct of each pair is what stops the first being
    vacuous: a kernel handing back a DESCRIPTOR for these words is
    rejected, so this pins -EINVAL rather than merely admitting it.
    Together they also pin that the answer is inert — the returned model
    is the SAME model and the event list is empty, neither of which the
    return value reveals. -/

theorem eventfd2_dropped_flag_bits_are_einval :
  /- bit 1, the bit immediately above EFD_SEMAPHORE: the likeliest
     off-by-one when a reader remembers "eventfd2 takes a low bit" -/
  check_syscall (efd_in 0 (2 ^ 1)) (mkEffect (errno_ret EINVAL) [] [])
    eventfd_model
  = check_result.CheckOk eventfd_model []
  ∧ check_syscall (efd_in 0 (2 ^ 1)) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckReject
  /- bit 10, just below O_NONBLOCK's bit 11 -/
  ∧ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = check_result.CheckOk eventfd_model []
  ∧ check_syscall (efd_in 0 (2 ^ 10)) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckReject
  /- bit 15, O_LARGEFILE's bit, which musl ORs into every open it issues
     and which this call does NOT accept -/
  ∧ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = check_result.CheckOk eventfd_model []
  ∧ check_syscall (efd_in 0 (2 ^ 15)) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckReject
  /- bit 20, just above O_CLOEXEC's bit 19 -/
  ∧ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = check_result.CheckOk eventfd_model []
  ∧ check_syscall (efd_in 0 (2 ^ 20)) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ACCEPTED MASK DECLINES RATHER THAN ANSWERS, one bit at a time
    and all together.
    ADMISSION REASON: it is universally quantified in spirit and
    model-internal in fact — a run that fails closed shows that SOME call
    left the surface, and which syscall it was, but not that the decline
    is keyed on the flag word rather than on something else.

    THE SEPARATION FROM [timerfd_create] IS THE POINT OF THE FIRST PAIR.
    [EFD_FLAGS_SET] and [TFD_CREATE_FLAGS] differ in exactly one bit,
    bit 0: it is [EFD_SEMAPHORE] here and belongs to
    [timerfd_settime]'s mask there, so [eventfd2(0, 1)] hands back a
    descriptor while [timerfd_create(CLOCK_MONOTONIC, 1)] is -EINVAL
    ([Uapi.EFD_FLAGS_SET] carries the derivation).  A model that spelled
    one gate with the other's mask would answer -EINVAL here, so the
    conjunct refusing that -EINVAL is what makes the two masks two
    rather than one. -/

theorem eventfd2_accepted_flag_words_decline :
  /- EFD_SEMAPHORE alone: accepted by eventfd2, refused by timerfd_create -/
  check_syscall (efd_in 0 EFD_SEMAPHORE) (mkEffect 3 [] []) eventfd_model
  = check_result.CheckUnmodeled
  /- ...and the -EINVAL a timerfd-shaped mask would have produced for it
     is NOT accepted -/
  ∧ check_syscall (efd_in 0 EFD_SEMAPHORE)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- the empty flag word, which is what glibc's and musl's eventfd(0, 0)
     compiles to -/
  ∧ check_syscall (efd_in 0 0) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (efd_in 0 O_CLOEXEC) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (efd_in 0 O_NONBLOCK) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- every accepted bit at once -/
  ∧ check_syscall (efd_in 0 EFD_FLAGS_SET) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- AND ONE BIT OUTSIDE IT, STILL ANSWERED.  Every conjunct above is
     [CheckUnmodeled], so on their own they stay green under any change
     that declines MORE -- the mask widening, or the arm going unmodeled
     outright -- which is the change this lemma exists to notice.  The
     bit above the mask's top bit is the sharpest witness that the mask
     is still a mask. -/
  ∧ check_syscall (efd_in 0 (2 * O_CLOEXEC))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckOk eventfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE COUNTER IS NOT JUDGED, AND THE FLAG WORD IS ARGUMENT 1.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which argument the model read to
    produce it.

    Two mistakes are ruled out here, and neither is visible from the
    accepted-mask cases above, where the counter is 0 throughout.

    FIRST, that the counter is judged at all.  [count] is stored by
    [ctx->count = count] BELOW the gate, so no value of it can be
    refused: the first two pairs offer a wild counter with an accepted
    flag word and require a decline, and refuse the -EINVAL a spec that
    masked the counter would produce.

    SECOND, that the two arguments are read in the wrong ORDER.  An arm
    reading [in_arg i 0] as the flag word would judge the COUNTER
    against [EFD_FLAGS_SET].  The last pair is what catches it:
    [eventfd2(2^20, 0)] is a legal call Linux answers with a descriptor,
    and a swapped arm would answer -EINVAL for it. -/

theorem eventfd2_counter_is_not_judged :
  /- a counter with bits far outside any flag mask, flags accepted -/
  check_syscall (efd_in (2 ^ 20) 0) (mkEffect 3 [] []) eventfd_model
  = check_result.CheckUnmodeled
  ∧ check_syscall (efd_in (2 ^ 20) 0) (mkEffect (errno_ret EINVAL) [] [])
       eventfd_model
     = check_result.CheckUnmodeled
  /- the largest counter an unsigned int can carry -/
  ∧ check_syscall (efd_in (2 ^ 32 - 1) 0) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (efd_in (2 ^ 32 - 1) 0)
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- a wild counter does not rescue a BAD flag word either -/
  ∧ check_syscall (efd_in (2 ^ 32 - 1) (2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckOk eventfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE FLAG WORD NARROWS TO 32 BITS, and the two halves are pinned
    together because only their conjunction says what narrowing means.
    ADMISSION REASON: model-internal — a run shows the answer the
    kernel returns and cannot show which comparison the model made to
    decline.

    A high half on the flag word aliases onto a clean flag word and
    declines.  A spec comparing the whole 64-bit register would have
    answered -EINVAL, so the second conjunct — that the -EINVAL is
    REFUSED — is the half that discriminates.

    No real run can show the refusal of the -EINVAL, because a kernel
    that returned one for this word does not exist. -/

theorem eventfd2_narrows_the_flag_word :
  check_syscall (efd_in 0 (2 ^ 32)) (mkEffect 3 [] []) eventfd_model
  = check_result.CheckUnmodeled
  ∧ check_syscall (efd_in 0 (2 ^ 32))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- an accepted low half with a high half set is still accepted -/
  ∧ check_syscall (efd_in 0 (2 ^ 32 + EFD_SEMAPHORE))
       (mkEffect 3 [] []) eventfd_model
     = check_result.CheckUnmodeled
  /- and the high half does not rescue a BAD low half: aliasing is not a
     second chance -/
  ∧ check_syscall (efd_in 0 (2 ^ 32 + 2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckOk eventfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! BIT 31 ALONE, WHICH IS THE SIGN BIT OF THE [int] LINUX COMPARES.
    ADMISSION REASON: the REFUSAL of a descriptor for it is the
    environment-cannot-produce-it reason, since no kernel hands one out
    here.

    [flags & ~EFD_FLAGS_SET] is used directly as an [if] condition, so a
    residue of 0x80000000 is truthy exactly as 1 is.  A spec that read
    the residue as a signed [int] and asked whether it was POSITIVE would
    admit this word. -/

theorem eventfd2_sign_bit_is_still_a_bad_bit :
  check_syscall (efd_in 0 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
    eventfd_model
  = check_result.CheckOk eventfd_model []
  ∧ check_syscall (efd_in 0 (2 ^ 31)) (mkEffect 3 [] []) eventfd_model
     = check_result.CheckReject
  /- and beside an accepted bit, so the sign bit is not excused by
     company it keeps -/
  ∧ check_syscall (efd_in 0 (2 ^ 31 + EFD_SEMAPHORE))
       (mkEffect (errno_ret EINVAL) [] []) eventfd_model
     = check_result.CheckOk eventfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Fs.EventFd
