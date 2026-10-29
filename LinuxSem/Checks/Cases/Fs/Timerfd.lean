/-
  * LinuxSem.Checks.Cases.Fs.Timerfd — worked examples over timerfd_create (85)

  Worked cases over `Sys.Fs.Timerfd`, which answers to Linux [fs/timerfd.c]:
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

  Clock ids.  `tfd_in`'s clock id and flag word are `Int`, so the
  `CLOCK_*` constants of `Sys.Uapi` are used unwrapped and `Z_to_bv 64`
  wraps them once at the syscall boundary.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Fs.Timerfd
import LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Syscall

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
open LinuxSem.LinuxProcessSem.Sys.Fs.Timerfd
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Timerfd
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Timerfd

/-! ## The prelude's abbreviations, restored

    Each of these is a transparent alias, so it
    changes no statement's meaning. -/

/-- `bv_unsigned` (`BvBase`): the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `bv_signed`: the signed value of a bitvector, as an `Int`. -/
abbrev bv_signed {n : Nat} (w : BitVec n) : Int := w.toInt

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `Z.eqb` (and `Nat.eqb`), over any `BEq`. -/
abbrev zeqb {α : Type} [BEq α] (a b : α) : Bool := a == b

/-- `Z.leb` on `Int`. -/
abbrev zleb (a b : Int) : Bool := decide (a ≤ b)

/-- `Z.ltb` on `Int`. -/
abbrev zltb (a b : Int) : Bool := decide (a < b)

/-- `nth_error`: `Option`-returning list indexing. -/
abbrev nth_error {α : Type} [Inhabited α] (l : List α) (n : Nat) : Option α := l[n]?

/-- `in_mem` as a function (a `SyscallInput` field projection). -/
abbrev in_mem (i : SyscallInput) : word → Option byte := i.in_mem
/-- `in_wmem` as a function. -/
abbrev in_wmem (i : SyscallInput) : word → Option byte := i.in_wmem
/-- `eff_ret` as a function. -/
abbrev eff_ret (e : SyscallEffect) : word := e.eff_ret
/-- `eff_writes` as a function. -/
abbrev eff_writes (e : SyscallEffect) : List (word × List byte) := e.eff_writes
/-- `eff_zeros` as a function. -/
abbrev eff_zeros (e : SyscallEffect) : List (word × word) := e.eff_zeros
/-- `eff_unmaps` as a function. -/
abbrev eff_unmaps (e : SyscallEffect) : List (word × word) := e.eff_unmaps
/-- `eff_copies` as a function. -/
abbrev eff_copies (e : SyscallEffect) : List MemCopy := e.eff_copies
/-- `eff_copyins` as a function. -/
abbrev eff_copyins (e : SyscallEffect) : List (word × Nat) := e.eff_copyins

/-! * LinuxSem.Checks.Cases.Fs.Timerfd — worked examples over timerfd_create (85)

    Worked cases over `Sys.Fs.Timerfd`, which answers to Linux [fs/timerfd.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

/-! [timerfd_create] reads no field of the model, so the state here only
    has to exist.  Three channels and nothing else. -/
def timerfd_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [] none none none

def tfd_in (clkid flags : Int) : SyscallInput :=
  SyscallInput.mkInput 85 [Z_to_bv 64 clkid, Z_to_bv 64 flags, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-! THE FLAG BITS, ONE AT A TIME.
    These examples walk single bits, and carry what a return value alone
    cannot show — the second conjunct below.

    Linux answers -EINVAL for ANY bit outside [TFD_CLOEXEC|TFD_NONBLOCK]
    (fs/timerfd.c, [SYSCALL_DEFINE2(timerfd_create)], v6.18.46), and the
    spec follows.

    The second conjunct of each pair is what stops the first being
    vacuous: a kernel handing back a DESCRIPTOR for these words is
    rejected, so this pins -EINVAL rather than merely admitting it.
    Together they also pin that the answer is inert — the returned model
    is the SAME model and the event list is empty, neither of which the
    return value reveals. -/

theorem timerfd_create_dropped_flag_bits_are_einval :
  /- bit 22, an ordinary swallowed bit -/
  check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22))
    (mkEffect (errno_ret EINVAL) [] []) timerfd_model
  = check_result.CheckOk timerfd_model []
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 22))
       (mkEffect 3 [] []) timerfd_model
     = check_result.CheckReject
  /- bit 15, a swallowed bit in the other run of them -/
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckOk timerfd_model []
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 15))
       (mkEffect 3 [] []) timerfd_model
     = check_result.CheckReject
  /- bit 20, the third run of them -/
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckOk timerfd_model []
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 20))
       (mkEffect 3 [] []) timerfd_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ADMITTED CLOCK IDS DECLINE RATHER THAN ANSWER, including the two
    alarm ids the model can never resolve.  ADMISSION REASON: it is
    universally quantified in spirit and model-internal in fact — a
    run that fails closed shows that SOME call left the surface, and
    which syscall it was, but not that the decline is keyed on the clock
    id rather than on something else.

    The point of the alarm pair is stated in `Sys.Fs.Timerfd`: keeping
    [CLOCK_REALTIME_ALARM] and [CLOCK_BOOTTIME_ALARM] in the admitted set
    costs nothing and dropping them would answer -EINVAL where Linux
    answers -EPERM or a descriptor.  The two conjuncts that offer
    -EINVAL on the alarm ids are what make that concrete — the errno a
    shortened whitelist would produce is offered there and must NOT be
    accepted. -/

theorem timerfd_create_admitted_clocks_decline :
  check_syscall (tfd_in CLOCK_REALTIME 0) (mkEffect 3 [] []) timerfd_model
  = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC 0) (mkEffect 3 [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_BOOTTIME 0) (mkEffect 3 [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0) (mkEffect 3 [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0) (mkEffect 3 [] []) timerfd_model
     = check_result.CheckUnmodeled
  /- the alarm ids decline the -EPERM a real kernel gives an unprivileged
     caller too: declining is not "it happens to answer the right errno" -/
  ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0)
       (mkEffect (errno_ret EPERM) [] []) timerfd_model
     = check_result.CheckUnmodeled
  /- and a shortened whitelist's -EINVAL is not accepted for them -/
  ∧ check_syscall (tfd_in CLOCK_REALTIME_ALARM 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_BOOTTIME_ALARM 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckUnmodeled
  /- AND A CLOCK ID IN THE ADMITTED SET'S OWN GAP, STILL ANSWERED.
     Every conjunct above is [CheckUnmodeled], so on their own they stay
     green under any change that declines MORE -- the membership test
     widening, or the arm going unmodeled outright -- which is the change
     this lemma exists to notice.

     The admitted ids are 0, 1, 7, 8 and 9, so they are not an interval,
     and the likeliest way to widen the test is to read them as one:
     [0 <= clockid <= CLOCK_BOOTTIME_ALARM] swallows 2 through 6 and no
     conjunct above would notice.  [CLOCK_PROCESS_CPUTIME_ID] (2) sits in
     that gap and takes the gate's -EINVAL, so pinning it here is what
     makes the admitted set a SET rather than a range. -/
  ∧ check_syscall (tfd_in CLOCK_PROCESS_CPUTIME_ID 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckOk timerfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE ARGUMENTS NARROW TO 32 BITS, and the two halves are pinned
    together because only their conjunction says what narrowing means.
    ADMISSION REASON: model-internal — a run shows the answer the kernel
    returns and cannot show which comparison the model made to decline.

    A high half on the CLOCK ID aliases onto the admitted id and
    declines; a high half on the FLAGS aliases onto a clean flag word and
    declines.  A spec comparing the whole 64-bit register would have
    answered -EINVAL to both, so the second conjunct of each pair —
    that the -EINVAL is REFUSED — is the half that discriminates.

    No real run can show the refusal of the -EINVAL, because a kernel
    that returned one for these words does not exist. -/

theorem timerfd_create_narrows_both_arguments :
  check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0)
    (mkEffect 3 [] []) timerfd_model
  = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in (2 ^ 32 + CLOCK_MONOTONIC) 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32))
       (mkEffect 3 [] []) timerfd_model
     = check_result.CheckUnmodeled
  ∧ check_syscall (tfd_in CLOCK_MONOTONIC (2 ^ 32))
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckUnmodeled
  /- the high half does not rescue a BAD low half either: aliasing is not
     a second chance -/
  ∧ check_syscall (tfd_in (2 ^ 32 + 11) 0)
       (mkEffect (errno_ret EINVAL) [] []) timerfd_model
     = check_result.CheckOk timerfd_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Fs.Timerfd
