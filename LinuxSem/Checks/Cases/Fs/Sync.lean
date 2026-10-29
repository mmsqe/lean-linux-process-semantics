/-
  * LinuxSem.Checks.Cases.Fs.Sync — worked examples over fsync (82), fdatasync (83)

  Worked cases over `Sys.Fs.Sync`, which answers to Linux [fs/sync.c]:
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

  Where the module ends.  The last block below introduces a
  `prlimit64 (261)` group and then a one-line doc comment for a
  `struct rlimit64` with single-byte soft and hard limits — and NO
  declaration follows either of them: the group they announce is not in
  this module.  Both comments are kept verbatim (the `/- … -/` block,
  then the trailing `/-! … -/`), and nothing is added after them.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.Sync
import LinuxSem.LinuxProcessSem.Sys.Fs.Sync
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
open LinuxSem.LinuxProcessSem.Sys.Fs.Sync
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Sync
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Sync

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

/-! * LinuxSem.Checks.Cases.Fs.Sync — worked examples over fsync (82), fdatasync (83)

    Worked cases over `Sys.Fs.Sync`, which answers to Linux [fs/sync.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

def fsync_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
      (3, FdEntry.FdFile [102] 7), (4, FdEntry.FdFileW [103] 9), (5, FdEntry.FdDir) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]), ([103], [121])] none none none

/-! THE CHANNEL ARM ON fd 0.

    The second conjunct is what makes the first non-vacuous: a kernel
    claiming SUCCESS is rejected, so this pins -EINVAL rather than
    merely admitting it. -/

theorem fsync_on_a_channel_is_einval :
  check_syscall (SyscallInput.mkInput 82 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 82 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) fsync_model
     = check_result.CheckReject
  /- and [fdatasync] answers fd 0 identically -/
  ∧ check_syscall (SyscallInput.mkInput 83 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 83 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) fsync_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE fd32 TRUNCATION ALIASES ONTO fd 0.

    What is worth pinning is that truncation ALIASES rather than
    REJECTS — a model comparing the full 64-bit register would have
    found no such fd and answered -EBADF.  The third conjunct rules that
    out.

    The first conjunct is an equation between two checker calls, so on
    its own it would hold vacuously if BOTH sides were [CheckReject].
    The second names the shared value outright, which is what makes the
    first say what it reads as saying. -/

theorem fsync_fd_truncates_to_32_bits :
  check_syscall (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) fsync_model
  = check_syscall (SyscallInput.mkInput 82 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
      (mkEffect (errno_ret EINVAL) [] []) fsync_model
  /- ...and that shared value is an ACCEPTANCE, not a shared rejection -/
  ∧ check_syscall (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) fsync_model
     = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 82 [Z_to_bv 64 (2 ^ 32), 0, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) fsync_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! SUCCESS IS INERT.  ADMISSION REASON: it pins model-internal state
    that no observation reveals.

    A real run sees only the 0.  That the fd's offset (7 and 9 here) and
    the file's contents came back UNCHANGED, and that no event was
    emitted, is a statement about the model's own state, and the
    equalities below are the whole of it: the returned model is the SAME
    model, and the event list is empty. -/

theorem fsync_success_is_inert_on_every_file_kind :
  check_syscall (SyscallInput.mkInput 82 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) fsync_model = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 82 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) fsync_model = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 82 [5, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) fsync_model = check_result.CheckOk fsync_model []
  ∧ check_syscall (SyscallInput.mkInput 83 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) fsync_model = check_result.CheckOk fsync_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/- -------------------------------------------------------------------------
   prlimit64 (261): the pin, and what no real run can show.

   Nearly all of this spec's fail-closed surface IS reachable from a
   real run — it just calls prlimit64 with a nonzero pid or an unmodeled
   resource id.  Three things a run cannot show are left, and they are
   the whole of this group:

   - THE ENVIRONMENT CANNOT PRODUCE a kernel reporting soft > hard.
     Linux maintains soft <= hard on every path that writes a limit.
     So [Kernel.Sys.rlim64_wf]'s ordering conjunct is stated here or
     nowhere.
   - Nor can it produce a later read delivering a DIFFERENT well-formed
     pair.
   - The rest pin MODEL-INTERNAL STATE — the recorded limit, and that a
     set REPLACES it.  A run reveals only the pair it happened to
     inherit, never that the model is holding it, so the claim is pinned
     here, where the recorded pair is chosen rather than inherited.
   ------------------------------------------------------------------------- -/

/-! A [struct rlimit64] with single-byte soft and hard limits. -/

end LinuxSem.Checks.Cases.Fs.Sync
