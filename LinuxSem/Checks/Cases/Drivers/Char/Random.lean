/-
  * LinuxSem.Checks.Cases.Drivers.Char.Random — worked examples over getrandom (278)

  Worked cases over `Sys.Drivers.Char.Random`, which answers to Linux
  [drivers/char/random.c]: the examples for the syscalls defined there,
  and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have come from `LinuxSem.Common.RocqSpelling`, transparent
  `abbrev`s DEFINITIONALLY EQUAL to what they stand for, so every
  statement below denotes exactly the same claim:
  - `bv_unsigned w` is `(w.toNat : Int)` and `Z_to_bv n z` is
    `BitVec.ofInt n z`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`;
  - `nth_error l n` is `l[n]?` and `existsb p l` is `l.any p`;
  - `repeat x n` is `List.replicate n x` (argument order swapped), so
    `repeat (Z_to_bv 8 7) n` reads `List.replicate n (Z_to_bv 8 7)`;
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

  Imports.  `Checks.Cases.Prelude` is imported directly; the re-export
  for the tree above this file is left to the root module.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Drivers.Char.Random
import LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
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
open LinuxSem.LinuxProcessSem.Sys.Drivers.Char.Random
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Drivers.Char.Random
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Drivers.Char.Random

open LinuxSem.Common.RocqSpelling

/-! Rocq spellings (`bv_unsigned`/`bv_signed`, `Z_to_bv`, `zeqb`/`zleb`/`zltb`,
    `nth_error`, `in_mem`/`in_wmem`, and the `eff_*` field shims) come
    from `LinuxSem.Common.RocqSpelling`, opened above. -/

/-! * LinuxSem.Checks.Cases.Drivers.Char.Random — worked examples over getrandom (278)

    Worked cases over `Sys.Drivers.Char.Random`, which answers to Linux
    [drivers/char/random.c]: the examples for the syscalls defined there,
    and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

/-! A writable landing zone at 4096, wide enough for a request above
    [Random.getrandom_small_max]. -/

def getrandom_dest : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4608 then some 0 else none

def getrandom_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)

/-! One getrandom(4096, buflen, 0) over that zone. -/

def getrandom_call (buflen : Int) : SyscallInput :=
  SyscallInput.mkInput 278 [4096, Z_to_bv 64 buflen, 0, 0, 0, 0] getrandom_dest getrandom_dest

/-! [n] environment bytes, all the same. -/

def some_bytes (n : Nat) : List byte := List.replicate n (Z_to_bv 8 7)

/-! A SMALL REQUEST IS DELIVERED IN FULL, AND ONLY IN FULL.  ADMISSION
    REASON: the environment cannot be made to produce what this
    REJECTS.  A real kernel never cuts a request of at most
    [Random.getrandom_small_max] bytes short and never interrupts it,
    so no execution can show the short count or the -EINTR being
    refused; this pins them against the checker directly.

    The first conjunct is what makes the rejections say something: the
    full delivery on the same call is ACCEPTED, so the rejections are
    of the count and the errno, not of the call. -/

theorem getrandom_small_request_is_delivered_in_full :
  check_syscall (getrandom_call 16)
    (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
  = check_result.CheckOk getrandom_model []
  /- the short count Linux cannot produce below the bound -/
  ∧ check_syscall (getrandom_call 16)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = check_result.CheckReject
  /- nor the interrupted return -/
  ∧ check_syscall (getrandom_call 16)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = check_result.CheckReject
  /- and over-delivery stays out, as everywhere -/
  ∧ check_syscall (getrandom_call 16)
       (mkEffect 17 [(4096, some_bytes 17)] []) getrandom_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE BOUND IS INCLUSIVE.  ADMISSION REASON: it pins the exact edge
    of the narrowing, which no execution reaches — a real kernel
    delivers both of these requests in full.
    A request of exactly [Random.getrandom_small_max] bytes is small;
    one byte more is large, and its short count is admitted again. -/

theorem getrandom_small_bound_is_inclusive :
  check_syscall (getrandom_call 256)
    (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
  = check_result.CheckReject
  ∧ check_syscall (getrandom_call 256)
       (mkEffect 256 [(4096, some_bytes 256)] []) getrandom_model
     = check_result.CheckOk getrandom_model []
  ∧ check_syscall (getrandom_call 257)
       (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
     = check_result.CheckOk getrandom_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A LARGE REQUEST STILL ADMITS THE SHORT COUNT AND -EINTR, and still
    refuses the bare 0.  ADMISSION REASON: the environment cannot be
    made to produce it — with no signal, a real kernel delivers a
    large request in full too, and the admissions below are
    what keep a signal-interrupted large request from being rejected
    as impossible. -/

theorem getrandom_large_request_still_admits_the_short_count :
  check_syscall (getrandom_call 300)
    (mkEffect 300 [(4096, some_bytes 300)] []) getrandom_model
  = check_result.CheckOk getrandom_model []
  ∧ check_syscall (getrandom_call 300)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = check_result.CheckOk getrandom_model []
  ∧ check_syscall (getrandom_call 300)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = check_result.CheckOk getrandom_model []
  /- a nonzero request never "succeeds" with nothing delivered -/
  ∧ check_syscall (getrandom_call 300)
       (mkEffect 0 [] []) getrandom_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Drivers.Char.Random
