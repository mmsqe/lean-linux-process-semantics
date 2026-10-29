/-
  * LinuxSem.Checks.Cases.Fs.File — worked examples over dup (23), dup3 (24)

  Worked cases over `Sys.Fs.File`, which answers to Linux [fs/file.c]:
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
  - a record field is read by dot notation here (`e.eff_writes`), the
    same projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Fs.File
import LinuxSem.LinuxProcessSem.Sys.Fs.File
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
open LinuxSem.LinuxProcessSem.Sys.Fs.File
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.File
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.File


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

/-! * LinuxProcessSem.Checks.Cases.Fs.File — worked examples over dup (23), dup3 (24)

    Worked cases over `Sys.Fs.File`, which answers to Linux [fs/file.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary.

    What a real run cannot show, and these therefore carry: the fd TABLE
    the model is left with (a real run reveals only the return value),
    the DECLINES, which hold for every claimed return rather than for
    the one return a given execution happened to produce, and the two
    facts about dup3's RLIMIT_NOFILE gate that need a SECOND model to
    state — that it is read from the run rather than written into the
    spec, and that it beats a descriptor the process already holds. -/


/-! The three channels, a read-only file "f" = "hi" at fd 3 positioned
    one byte in, and the directory fd at 4 — one fd of every kind, so
    both sides of [File.dup_modeled_entry] are in reach.  The lowest
    free fd is 5. -/
def dup_model : Model :=
  mkModel [(0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
           (3, FdEntry.FdFile [102] 1), (4, FdEntry.FdDir)]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104, 105])] none none
    none

/-! dup hands out the lowest free fd and binds it to a COPY of the
    entry, which is the whole of what "share the description" means for
    a channel: the read position is [m_stdin] and the writes are trace
    events, so both fds already name the same thing.  No kernel can be
    made to hand out a non-lowest fd, so the second conjunct — the model
    REJECTS fd 6 — is only reachable here. -/
theorem dup_installs_a_copy_at_the_lowest_free_fd :
  check_syscall (SyscallInput.mkInput 23 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 5 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (FdEntry.FdChannel 0)) dup_model) []
  ∧ check_syscall (SyscallInput.mkInput 23 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 6 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A directory fd duplicates too: [FdDir] is nullary, so a copy carries
    no position that could drift. -/
theorem dup_of_a_directory_fd_duplicates :
  check_syscall (SyscallInput.mkInput 23 [4, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 5 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 5 FdEntry.FdDir) dup_model) []
:= by rfl

/-! The offset-sharing gap, stated as the model's answer rather than as
    a comment: duplicating a FILE fd declines WHATEVER the kernel
    claims.  A real run pins one claimed return; this pins all of them,
    which is what makes it a fail-closed gap rather than a wrong
    answer. -/
theorem dup_of_a_file_fd_declines_whatever_the_kernel_claims : ∀ eff,
  check_syscall (SyscallInput.mkInput 23 [3, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    eff dup_model
  = check_result.CheckUnmodeled := by
  intro eff
  rfl

/-! dup3 returns the fd it was GIVEN, silently closing what was there:
    fd 1 stops naming channel 1 and names channel 0, so it stops being
    WRITABLE — [write_spec]'s channel arm answers -EBADF for channel 0.
    That the entry moved is model-internal state no return value
    reveals. -/
theorem dup3_replaces_the_target_and_returns_it :
  check_syscall (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 1 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (FdEntry.FdChannel 0)) dup_model) []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 1, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 5 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! O_CLOEXEC is accepted and leaves the same state as flags 0 — nothing
    in [Specs.modeled_sysnos] can observe a close-on-exec bit.  Any
    OTHER bit is [ksys_dup3]'s -EINVAL, so claiming the successful
    return there is rejected. -/
theorem dup3_ignores_o_cloexec_but_not_another_bit :
  check_syscall (SyscallInput.mkInput 24 [0, 1, 524288, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 1 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 1 (FdEntry.FdChannel 0)) dup_model) []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 1, 4, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 1 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [oldfd == newfd] is -EINVAL even for a FILE fd, which is a place
    the model is deliberately MORE precise than its own decline: the
    equality test precedes every kind test, as [ksys_dup3] orders them,
    so the entry that carries an offset is never reached.  Declining
    here instead would be fail-closed but wrong-shaped — Linux answers
    -EINVAL whatever the fd is. -/
theorem dup3_eq_beats_the_file_fd_decline :
  check_syscall (SyscallInput.mkInput 24 [3, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) dup_model
  = check_result.CheckOk dup_model []
  ∧ check_syscall (SyscallInput.mkInput 24 [3, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 3 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A FREE [newfd] below [Uapi.NR_OPEN_DEFAULT] is installed at the
    number given, not at the lowest free one — which is the difference
    between dup3 and dup, and is why the rejected conjunct claims fd 5,
    the number [dup] would have answered.  [dup_model]'s limit is
    [State.default_nofile], so 7 is under it. -/
theorem dup3_takes_a_free_newfd_below_the_embedded_table :
  check_syscall (SyscallInput.mkInput 24 [0, 7, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 7 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 7 (FdEntry.FdChannel 0)) dup_model) []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 7, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 5 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A FREE [newfd] at or above it is declined for every claimed return.
    Linux decides 100 here out of the descriptor table's current
    [max_fds] and the [sysctl_nr_open] ceiling, neither of which the
    model carries: it may return 100, or -EBADF (from the -EMFILE
    [ksys_dup3] rewrites), or -ENOMEM.  Three answers, no way to choose
    — see [File.dup3_spec]. -/
theorem dup3_declines_a_free_newfd_above_the_embedded_table : ∀ eff,
  check_syscall (SyscallInput.mkInput 24 [0, 100, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    eff dup_model
  = check_result.CheckUnmodeled := by
  intro eff
  rfl

/-! THE LIMIT IS READ FROM THE RUN, not written into the spec, and this
    is the pair that says so.  [dup_model] carries
    [State.default_nofile]; this is the same model, same descriptors,
    under a soft limit of 4 — which a parent that lowered RLIMIT_NOFILE
    really can hand a process, since [execve] closes only the
    close-on-exec descriptors and the rest stay open however low the
    limit is.  Every check below runs the SAME input against both
    models, so only the limit can separate the answers: replace
    [File.dup3_newfd_under_limit]'s [m_nofile m] with any constant and
    one of the two sides breaks. -/
def dup_model_nofile4 : Model := with_nofile (Z_to_bv 64 4) dup_model

/-! fd 5 is free and below [Uapi.NR_OPEN_DEFAULT], so nothing but the
    limit can separate the two answers: under [State.default_nofile] the
    free-[newfd] arm installs it, and under 4 the gate answers first. -/
theorem dup3_free_newfd_is_decided_by_the_run_s_limit :
  check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 5 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 5 (FdEntry.FdChannel 0)) dup_model) []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
     = check_result.CheckOk dup_model_nofile4 []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 5, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 5 [] []) dup_model_nofile4
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The gate beats the descriptor the process ALREADY HOLDS, which is
    the case a spec can answer wrongly rather than decline: fd 4 is
    open (it is the directory fd) and sits AT the limit, so dup3 onto it
    is -EBADF where a spec that only looked the fd up would have
    returned 4.  fd 3 beside it, open and under the limit, is the
    ordinary replacement — so the pair also pins the comparison as
    STRICT, since [newfd <= limit] would make 4 succeed. -/
theorem dup3_limit_beats_an_fd_the_process_holds :
  check_syscall (SyscallInput.mkInput 24 [0, 3, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 3 [] []) dup_model_nofile4
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model_nofile4) 3 (FdEntry.FdChannel 0))
               dup_model_nofile4) []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) dup_model_nofile4
     = check_result.CheckOk dup_model_nofile4 []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 4, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 4 [] []) dup_model_nofile4
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [Uapi.NR_OPEN_DEFAULT]'s own boundary, adjacent values either side:
    63 is answered and 64 is declined.  The examples above do not reach
    it — they sit at 5, 7 and 100 — so an off-by-one
    in that one comparison would otherwise pass everything, the spec and
    the checker sharing the test. -/
theorem dup3_free_newfd_just_below_the_embedded_table :
  check_syscall (SyscallInput.mkInput 24 [0, 63, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 63 [] []) dup_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds dup_model) 63 (FdEntry.FdChannel 0)) dup_model) []
:= by rfl

theorem dup3_declines_a_free_newfd_at_the_embedded_table : ∀ eff,
  check_syscall (SyscallInput.mkInput 24 [0, 64, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    eff dup_model
  = check_result.CheckUnmodeled := by
  intro eff
  rfl

/-! The RLIMIT_NOFILE gate, and its PLACEMENT.  [ksys_dup3] tests
    [newfd >= rlimit(RLIMIT_NOFILE)] before it looks [oldfd] up, so the
    answer is -EBADF even for an [oldfd] whose kind the model refuses to
    duplicate — 3 is [FdFile], which [File.dup_modeled_entry] rejects.
    Reorder the spec to test the kind first and the second conjunct
    turns into [CheckUnmodeled].  The order holds for EVERY claimed
    return and needs no run.  2000 is above
    [State.default_nofile]. -/
theorem dup3_over_the_limit_is_ebadf_before_the_oldfd_lookup :
  check_syscall (SyscallInput.mkInput 24 [0, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EBADF) [] []) dup_model
  = check_result.CheckOk dup_model []
  ∧ check_syscall (SyscallInput.mkInput 24 [3, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) dup_model
     = check_result.CheckOk dup_model []
  ∧ check_syscall (SyscallInput.mkInput 24 [0, 2000, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 2000 [] []) dup_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Fs.File
