/-
  * LinuxSem.Checks.Cases.Fs.Locks — worked examples over flock (32)

  Worked cases over `Sys.Fs.Locks`, which answers to Linux [fs/locks.c]:
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
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.Locks
import LinuxSem.LinuxProcessSem.Sys.Fs.Locks
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
open LinuxSem.LinuxProcessSem.Sys.Fs.Locks
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Locks
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Locks

open LinuxSem.Common.RocqSpelling


/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/

/-- `Checks.Cases.Fs.ReadWrite`'s `mem_open_write`, spelled through its
    own namespace so that opening this one does not drag the other's shims
    in. -/
abbrev mem_open_write : word → Option byte :=
  LinuxSem.Checks.Cases.Fs.ReadWrite.mem_open_write

/-! * LinuxProcessSem.Checks.Cases.Fs.Locks — worked examples over flock (32)

    Worked cases over `Sys.Fs.Locks`, which answers to Linux [fs/locks.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/


/-! One opener per file: fd 3 reads "f", fd 4 writes "g", fd 5 is a
    directory reference. -/
def flock_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
      (3, FdEntry.FdFile [102] 7), (4, FdEntry.FdFileW [103] 9), (5, FdEntry.FdDir) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]), ([103], [121])]

/-! The same table with a SECOND descriptor on "f" — what a second
    [openat] of the same name produces.  Only fd 6 differs. -/
def flock_two_openers_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
      (3, FdEntry.FdFile [102] 7), (4, FdEntry.FdFileW [103] 9), (5, FdEntry.FdDir),
      (6, FdEntry.FdFile [102] 0) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]), ([103], [121])]

/-! SUCCESS IS INERT.  ADMISSION REASON: it pins model-internal state
    that no observation reveals.

    A real run sees only the 0.  That the descriptors' offsets (7 and 9
    here) and the files' contents came back UNCHANGED, and that no event
    was emitted, is a statement about the model's own state, and the
    equalities below are the whole of it: the returned model is the SAME
    model, and the event list is empty.  It is worth pinning for flock
    in particular, because the syscall a program is issuing here is one
    that CHANGES kernel state — the whole point of taking a lock — and
    the model's answer is that none of the state it carries moves.

    Three arms are covered because they reach the answer by three
    different routes: LOCK_EX on the sole opener of "f" goes through the
    sole-opener gate, LOCK_UN on a directory reference skips the fd-kind
    match entirely, and LOCK_MAND (32) answers before the descriptor is
    resolved at all — which is why its case uses a descriptor that is
    not open.

    Each is paired with a rejection of a DIFFERENT return, so that "the
    model accepts this" is not the vacuous reading of a checker that
    accepts everything. -/

theorem flock_success_is_inert :
  /- LOCK_EX on the sole opener of "f" -/
  check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) flock_model = check_result.CheckOk flock_model []
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EAGAIN) [] []) flock_model = check_result.CheckReject
  /- LOCK_UN on a directory reference: 0 without consulting the fd kind -/
  ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) flock_model = check_result.CheckOk flock_model []
  ∧ check_syscall (SyscallInput.mkInput 32 [5, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) flock_model = check_result.CheckReject
  /- LOCK_MAND on a descriptor that is NOT OPEN: still 0, because the bit
     is tested before the lookup.  A model that resolved the fd first
     would answer -EBADF, which the second conjunct rules out. -/
  ∧ check_syscall (SyscallInput.mkInput 32 [9999, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) flock_model = check_result.CheckOk flock_model []
  ∧ check_syscall (SyscallInput.mkInput 32 [9999, 32, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) flock_model = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE SOLE-OPENER GATE IS WHAT DECIDES THE GRANT.  ADMISSION REASON:
    it compares two models, and no run holds two.

    A program can reach the decline — it opens the same name twice and the
    run stops fail-closed — but a fail-closed verdict says only that the
    model left its surface, not WHICH fact took it there.  The contrast
    is what carries the argument, and it needs the two tables side by
    side: identical but for fd 6, one granting and one declining.

    The third and fourth conjuncts are what keep this from reading as
    "the second model declines everything".  LOCK_UN on the very same
    descriptor of the very same two-opener table still answers 0, and a
    different return is still rejected there — which is the claim that
    an unlock needs no premise about who else holds the file, stated
    where it can be compared against the request that does. -/

/-! EVERY FILE KIND COUNTS AS AN OPENER, and this is the claim the
    enumeration in [Fs.Locks.path_openers] cannot make.

    That fixpoint names every [State.FdEntry] constructor so that a
    later kind is a build error rather than a silent miscount, and the
    argument is sound as far as it goes -- but it is an argument about a
    missing ARM, not about an arm's ANSWER.  Replacing any counting arm
    with the skipping one the four non-file kinds take
    (`path_openers r p`) compiles and closes every proof in the flock
    stack.  [flock_sole_opener] then answers TRUE with a second
    descriptor of that kind already on the path, and [flock_spec]
    returns 0 for a lock the kernel makes conflict: an unsound ACCEPT,
    with nothing red anywhere.

    Of the four counting arms, only [FdFile] is pinned elsewhere, by
    [flock_two_openers_model] holding two [FdFile] descriptors on one
    name.  Without this example, the [FdFileW], [FdFileA] and [FdFileRW]
    arms could each take the skip with every proof still closing.

    So the example is over all four kinds rather than over one.
    For each: the sole opener is answered, a SECOND descriptor of the
    same kind on the same name is declined, and a second descriptor of a
    DIFFERENT kind is declined too -- which is what says the count is
    over openers rather than over kinds, and is the half a per-kind
    counter would still pass.

    [sys_flock] reads neither [f_mode] nor [f_flags] on the path to
    [flock_lock_inode_wait]: the lock is on the inode, and which
    directions a description may transfer is not one of its inputs
    (fs/locks.c, Linux v6.18.46).  That is the one kernel fact all four
    arms rest on. -/
def flock_openers_model (es : List (word × FdEntry)) : Model :=
  mkModel ([(0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2)] ++ es)
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120])]

/-! LOCK_EX on fd 3, which is the descriptor each model below puts on
    "f"; the effect claims the success, so a decline shows up as
    [CheckUnmodeled] and a wrong success as [CheckReject]. -/
def flock_ex_on_3 (m : Model) : check_result :=
  check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) m

theorem flock_every_file_kind_counts_as_an_opener :
  let sole k := flock_openers_model [(3, k [102] (Z_to_bv 64 0))] ;
  let pair k := flock_openers_model
                  [(3, k [102] (Z_to_bv 64 0)), (4, k [102] (Z_to_bv 64 5))] ;
  let mixed k := flock_openers_model
                   [(3, k [102] (Z_to_bv 64 0)),
                    (4, FdEntry.FdFile [102] (Z_to_bv 64 5))] ;
  /- the sole opener of "f" is provably uncontended, on every kind -/
  flock_ex_on_3 (sole FdEntry.FdFile) = check_result.CheckOk (sole FdEntry.FdFile) []
  ∧ flock_ex_on_3 (sole FdEntry.FdFileW) = check_result.CheckOk (sole FdEntry.FdFileW) []
  ∧ flock_ex_on_3 (sole FdEntry.FdFileA) = check_result.CheckOk (sole FdEntry.FdFileA) []
  ∧ flock_ex_on_3 (sole FdEntry.FdFileRW) = check_result.CheckOk (sole FdEntry.FdFileRW) []
  /- a SECOND descriptor of the same kind on the same name: declined -/
  ∧ flock_ex_on_3 (pair FdEntry.FdFile) = check_result.CheckUnmodeled
  ∧ flock_ex_on_3 (pair FdEntry.FdFileW) = check_result.CheckUnmodeled
  ∧ flock_ex_on_3 (pair FdEntry.FdFileA) = check_result.CheckUnmodeled
  ∧ flock_ex_on_3 (pair FdEntry.FdFileRW) = check_result.CheckUnmodeled
  /- ...and a second descriptor of a DIFFERENT kind contends just the
     same, which a counter that counted each kind only against its own
     would still get wrong -/
  ∧ flock_ex_on_3 (mixed FdEntry.FdFileW) = check_result.CheckUnmodeled
  ∧ flock_ex_on_3 (mixed FdEntry.FdFileA) = check_result.CheckUnmodeled
  ∧ flock_ex_on_3 (mixed FdEntry.FdFileRW) = check_result.CheckUnmodeled
  /- the decline is the sole-opener gate and not the KIND: LOCK_UN on the
     very same two-descriptor table still answers 0, since an unlock
     spends no premise about other holders -/
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) (pair FdEntry.FdFileRW) = check_result.CheckOk (pair FdEntry.FdFileRW) []
  /- and a kernel claiming the sole opener conflicted is refused -/
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EAGAIN) [] []) (sole FdEntry.FdFileRW) = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

theorem flock_second_opener_declines :
  check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) flock_model = check_result.CheckOk flock_model []
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 2, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) flock_two_openers_model = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 0 [] []) flock_two_openers_model
     = check_result.CheckOk flock_two_openers_model []
  ∧ check_syscall (SyscallInput.mkInput 32 [3, 8, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EAGAIN) [] []) flock_two_openers_model = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Fs.Locks
