/-
  * LinuxSem.Checks.Cases.Fs.Readdir — worked examples over getdents64 (61)

  Worked cases over `Sys.Fs.Readdir`, which answers to Linux
  [fs/readdir.c]: the examples for the syscalls defined there, and no
  others.

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

  Proofs.  `rfl` — kernel reduction of a closed goal — closes a concrete
  example here, but not the directory arm's own first test on the shape
  the next note measures: that one reads `sint32` at a concrete word, and
  while `sint32` had the `narrow` body the kernel could not reduce it.
  `sint32` is now `(w.setWidth 32).toInt`, which does reduce at a literal,
  but the examples below keep the two routes the socket examples
  (`Checks.Cases.Net.Socket`) also use:

  (A) the CONSTRUCTOR projection `isUnmodeledR` from
      `Checks.Cases.CheckToolkit` — `by decide` a `Bool`, reflect it
      back, never name the value the arm answers with; and
  (B) a staged evaluation — `check_syscall`'s dispatch is resolved first
      (`check_syscall_getdents64` below), and only then is the arm
      unfolded, with its branch tests discharged by `by decide`/`rfl`
      instead of by asking the kernel to reduce `sint32`'s `Int`
      comparison.

  All three examples below are proved by those two routes; WHY the
  directory arm needed them, and what was measured, sits in the note
  above the examples.

  Imports.  `Checks.Cases.Prelude` and `Checks.Cases.Fs.ReadWrite` are
  both imported directly; the re-export for the tree above this file is
  left to the root module.  No name from `Checks.Cases.Fs.ReadWrite` is
  used below, so its namespace is imported but not opened — which also
  keeps the two files' `bv_unsigned`-style shims from shadowing one
  another.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.CheckToolkit
import LinuxSem.Checks.Cases.Fs.ReadWrite
import LinuxSem.Checks.Sys.Fs.Readdir
import LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
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
open LinuxSem.LinuxProcessSem.Sys.Fs.Readdir
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.Readdir
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.Readdir

open LinuxSem.Common.RocqSpelling

/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/

/-! * LinuxSem.Checks.Cases.Fs.Readdir — worked examples over getdents64 (61)

    Worked cases over `Sys.Fs.Readdir`, which answers to Linux [fs/readdir.c]: the
    examples for the syscalls defined there, and no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary.

    ALMOST NOTHING ABOUT THIS SYSCALL BELONGS HERE, and that is the
    point of saying so: every arm of [Fs.Readdir.getdents64_spec] is
    reachable from a real run, and so is the decline, by giving a
    directory fd a buffer with room in it.  What is left is the two
    things a real run reveals nothing about. -/

/-! fd 3 is an O_RDONLY file parked at offset 7, fd 4 an O_WRONLY one at
    offset 9, fd 5 the directory.  The two offsets and the two file
    bodies are what the inertness check below has to find unchanged. -/
def getdents64_model : Model :=
  mkModel
    [ (0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
      (3, FdEntry.FdFile [102] 7), (4, FdEntry.FdFileW [103] 9), (5, FdEntry.FdDir) ]
    (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120]), ([103], [121])]

/-! One getdents64 call, with [buf] parked at a mapped-looking address
    that no arm below reads: the spec does not take the pointer, so
    every answer here is settled without it. -/
def getdents64_in (fd count : Int) : SyscallInput :=
  SyscallInput.mkInput 61 [Z_to_bv 64 fd, Z_to_bv 64 4096, Z_to_bv 64 count, 0, 0, 0]
    (fun _ => none) (fun _ => none)


/-! ### The route down to the arm: `check_syscall_getdents64`

    Why a bridge lemma, and how it is proved.  Every statement below is
    written at `check_syscall` level, i.e. over the 90-arm
    `checked_table` dispatch; the arm itself is
    `Checks.Sys.Fs.Readdir.check_getdents64`.  `check_syscall_getdents64`
    is the connective, and it is what makes the per-arm recipe that
    `Checks/Sys/Fs/Readdir.lean` already uses (`unfold`, then discharge
    each branch test by name) reachable from here.

    It is proved by unfolding ONLY the three `check_syscall` definitions
    and `getdents64_in`, and then letting the KERNEL resolve
    `lookup_ca checked_table 61`: `lookup_ca` at a literal number is a
    closed computation over the 90 arms, each of which has `ca_no = 61`
    by `rfl` (`Dispatch.ca_no_arm_getdents64`), so `exact` closes what is
    left definitionally.  Unfolding `checked_table`/`lookup_ca` inside the
    `simp` instead would turn the lookup into a 90-deep `if`-chain that
    `simp` then has to re-compute — the measured cause of the
    "maximum recursion depth" failures this file used to record.

    The arm's own checker is then read off by
    `Dispatch.ca_check_arm_getdents64` (an `rfl` lemma):
    `check_getdents64 (fd32 (in_arg i 0)) (in_arg i 2) eff m`. -/
theorem check_syscall_getdents64 (fd count : Int) (eff : SyscallEffect) (m : Model) :
    check_syscall (getdents64_in fd count) eff m
      = check_getdents64 (Sys.Syscall.fd32 (Z_to_bv 64 fd)) (Z_to_bv 64 count) eff m := by
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, getdents64_in]
  exact Sys.Dispatch.ca_check_arm_getdents64 _ _ _

/-- The DIRECTORY arm, opened up to its buffer test.  `fd` names the
    descriptor and `count` the buffer size; both are spelled as the `Int`
    arguments of `getdents64_in`, because the buffer test is
    `by decide`-discharged and `decide` computes through `Z_to_bv`.

    The descriptor lookup is discharged by `rfl` rather than `decide`:
    `FdEntry` has no `DecidableEq` (it carries a `SockState`, whose
    streams hold functions), but `fd_lookup` over the literal table is a
    closed `if` on `word` equality, which the kernel does reduce.

    The two facts are BOUND rather than inlined into the `rw` calls: an
    antiquotation inside a `rw [ … ]` bracket does not parse, while one in
    a `have`'s type does — and the buffer fact is parenthesised
    `(by decide)` so its `by` block cannot swallow the next tactic. -/
macro "getdents64_dir" "(" fd:term ")" "(" count:term ")" : tactic =>
  `(tactic|
    (rw [check_syscall_getdents64];
     unfold check_getdents64;
     have hlook : fd_lookup (m_fds getdents64_model) (Sys.Syscall.fd32 (Z_to_bv 64 ($fd))) = some FdEntry.FdDir := (by rfl);
     rw [hlook];
     dsimp only;
     have hroom : getdents64_no_room (Z_to_bv 64 ($count)) = true := (by decide);
     rw [ite_eq_left hroom]))

/-- A NON-directory arm: the checker answers `check_ret_only eff r m []`, so
    the ledger test and the return test are the whole of it.  `entry` is
    what the descriptor looks up to; the errno the arm answers with is
    the one the goal states, and `bv_eqb_refl` finds it there. -/
macro "getdents64_other" "(" fd:term ")" "(" entry:term ")" : tactic =>
  `(tactic|
    (rw [check_syscall_getdents64];
     unfold check_getdents64;
     have hlook : fd_lookup (m_fds getdents64_model) (Sys.Syscall.fd32 (Z_to_bv 64 ($fd))) = $entry := (by rfl);
     rw [hlook];
     dsimp only;
     unfold check_ret_only;
     dsimp only;
     rw [ite_eq_left (bv_eqb_refl _)]))

/-! ### The `rfl` wall, MEASURED, and how it was passed

    MEASURED AGAINST THE EARLIER `sint32`.  `Sys.Syscall.sint32` is now
    `(w.setWidth 32).toInt`, which the kernel does reduce at a literal, so
    the wall recorded here no longer stands in front of it; the numbers
    are the record for the `narrow` shape, which `Sys.Syscall.nfds_signed`
    still has.  They are kept because they are why these examples are
    staged rather than `rfl`-closed.

    The
    directory arm's first test is `if getdents64_no_room count`, i.e.
    `decide (Sys.Syscall.sint32 count < Readdir.dirent64_min_reclen)`, and
    closing THAT by `rfl` asked the kernel to reduce `sint32` at a concrete
    word.  Measured, on this toolchain: at `maxRecDepth 1000000` the
    elaborator reports "maximum recursion depth has been reached", and at
    20 000 000 the kernel stack overflows.  `decide` closes the individual
    facts — `getdents64_no_room (23 : word) = true`,
    `getdents64_ctx_count (23 : word) = 23` and `sint32 (23 : word) = 23`
    are each provable that way — so the obstruction was the definitional
    check `rfl` performs, not the arithmetic.  The same hazard is on
    record in `LinuxSem/Checks/Sys/Fs/Readdir.lean`, and
    `Checks/Witness/Fs/Readdir.lean` works around it by rewriting the `if`
    with a `decide`-proved side condition (`ite_eq_left` / `ite_eq_right`).

    That workaround does lift to these three, but only after the dispatch
    is out of the way: `rw [ite_eq_left …]` needs the `if` to occur
    SYNTACTICALLY, and in `check_syscall`'s conclusion it sits behind the
    `checked_table` lookup.  `check_syscall_getdents64` above is that
    step, and with it each arm is a plain `check_getdents64` application
    at literal arguments — so `getdents64_dir` unfolds the arm, resolves
    the descriptor by `rfl`, and discharges the buffer test by `decide`,
    exactly as the Witness module does one level down.

    Route A is needed only for the `= .CheckUnmodeled` conjuncts
    go through the toolkit's `check_unmodeled` (the constructor
    projection, 0.2-0.5 s per arm), which never names the model.

    Everything ELSE about these calls does reduce: `fd_lookup` on the
    concrete table, `check_ret_only`, the effect shapes and the errno
    sets all normalise — so the proofs below are short and the four
    conjuncts of each example are still checked separately. -/

/-! WHERE THE BUFFER-SIZE EDGE IS.  ADMISSION REASON: it pins a model
    constant that no observation of a real execution reveals.

    A real run learns that the kernel said -EINVAL at some count and
    listed the directory at some larger one; it never learns where the
    MODEL puts the boundary between them, and a spec whose edge sat one
    byte either side would pass every run that lands clear of it.  [Fs.Readdir.dirent64_min_reclen] is 24 — the aligned size of a
    one-byte name's record — so 23 is answered and 24 is declined, and
    naming the two together is the whole of the claim.

    The third and fourth conjuncts are what make the first two say what
    they read as saying: without them, "23 is -EINVAL" would hold just
    as well of a checker that accepted every return at that count, and
    "24 declines" of one that declined every count. -/

/-! The first statement, at `check_syscall` level (the proof is the two
    routes above):

    ```
    Example getdents64_edge_is_the_minimum_reclen :
      check_syscall (getdents64_in 5 23) (mkEffect (errno_ret EINVAL) [] [])
        getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 5 24) (mkEffect (errno_ret EINVAL) [] [])
           getdents64_model = CheckUnmodeled
      (* ...and 23 admits that errno rather than any return *)
      /\ check_syscall (getdents64_in 5 23) (mkEffect (Z_to_bv 64 0) [] [])
           getdents64_model = CheckReject
      (* ...while 24 declines the very return 23 would have accepted, so the
         decline is the COUNT's doing and not the effect's *)
      /\ check_syscall (getdents64_in 5 24) (mkEffect (Z_to_bv 64 24) [] [])
           getdents64_model = CheckUnmodeled.
    Proof. repeat split; check_eq. Qed.
    ```
-/
theorem getdents64_edge_is_the_minimum_reclen :
  check_syscall (getdents64_in 5 23) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 5 24) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = check_result.CheckUnmodeled
  ∧ check_syscall (getdents64_in 5 23) (mkEffect (Z_to_bv 64 0) [] [])
       getdents64_model = check_result.CheckReject
  ∧ check_syscall (getdents64_in 5 24) (mkEffect (Z_to_bv 64 24) [] [])
       getdents64_model = check_result.CheckUnmodeled
:= by
  (repeat' apply And.intro)
  /- 23 bytes cannot hold the smallest record, and -EINVAL is admitted
     there rather than any other return. -/
  · getdents64_dir (5) (23)
    rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
          (errno_ret EINVAL) = true)),
        ite_eq_left (by decide : bv_eqb (errno_ret EINVAL) (errno_ret EINVAL) = true)]
  /- 24 has room, so the listing is what the model cannot produce. -/
  · check_unmodeled
  /- …and at 23 a bare 0 is REFUSED: the errno set is not "any return". -/
  · getdents64_dir (5) (23)
    rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos (Z_to_bv 64 0) = true)),
        ite_eq_right (by decide : ¬(bv_eqb (Z_to_bv 64 0) (errno_ret EINVAL) = true))]
  /- …while at 24 the very return 23 would have accepted is declined, so the
     decline is the COUNT's doing and not the effect's. -/
  · check_unmodeled

/-! THE SAME EDGE, ON THE OTHER SIDE OF THE SIGN.  ADMISSION REASON: as
    above — it is where the model reads [count] as
    [struct dir_context]'s [int] rather than as the [unsigned int] the
    prototype declares, and no single run separates the two readings.

    2^31 - 1 is the largest positive [ctx->count], and has room; 2^31 is
    the smallest negative one, and has none.  A model comparing the
    unsigned low half would have declined BOTH, so the second conjunct
    is the one that carries the reading, and the fourth rules out the
    other mistake — that the model simply accepts -EINVAL everywhere
    above the boundary. -/

/-! The second statement, at `check_syscall` level:

    ```
    Example getdents64_count_is_a_signed_int :
      check_syscall (getdents64_in 5 (2 ^ 31 - 1)) (mkEffect (errno_ret EINVAL) [] [])
        getdents64_model = CheckUnmodeled
      /\ check_syscall (getdents64_in 5 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
           getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 5 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] [])
           getdents64_model = CheckOk getdents64_model []
      (* the high half is discarded first, so 2^32 | 24 has room again *)
      /\ check_syscall (getdents64_in 5 (2 ^ 32 + 24)) (mkEffect (errno_ret EINVAL) [] [])
           getdents64_model = CheckUnmodeled.
    Proof. repeat split; check_eq. Qed.
    ```
-/
theorem getdents64_count_is_a_signed_int :
  check_syscall (getdents64_in 5 (2 ^ 31 - 1)) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = check_result.CheckUnmodeled
  ∧ check_syscall (getdents64_in 5 (2 ^ 31)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 5 (2 ^ 32 - 1)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 5 (2 ^ 32 + 24)) (mkEffect (errno_ret EINVAL) [] [])
       getdents64_model = check_result.CheckUnmodeled
:= by
  (repeat' apply And.intro)
  /- 2^31 - 1 is the largest positive `ctx->count`, and has room. -/
  · check_unmodeled
  /- 2^31 is the smallest NEGATIVE one: the SIGNED reading is what makes
     this answer -EINVAL instead of a large successful read. -/
  · getdents64_dir (5) (2 ^ 31)
    rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
          (errno_ret EINVAL) = true)),
        ite_eq_left (by decide : bv_eqb (errno_ret EINVAL) (errno_ret EINVAL) = true)]
  /- …and the unsigned low half is READ AS SIGNED, so 2^32 - 1 is -1 too. -/
  · getdents64_dir (5) (2 ^ 32 - 1)
    rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
          (errno_ret EINVAL) = true)),
        ite_eq_left (by decide : bv_eqb (errno_ret EINVAL) (errno_ret EINVAL) = true)]
  /- The high half is discarded first, so 2^32 | 24 has room again. -/
  · check_unmodeled

/-! EVERY ANSWER IS INERT.  ADMISSION REASON: it pins model-internal
    state that no observation reveals.

    A real run sees only the errno.  That the fds' offsets (7 and 9 here),
    the file bodies and the fd table itself came back UNCHANGED, and
    that no event was emitted, is a statement about the model's own
    state, and the equalities below are the whole of it: the returned
    model is the SAME model, and the event list is empty.

    This is not the same claim as "the effect carries no writes".
    That one is about what the checker refuses to accept; this one is
    about what it DOES with an answer it accepts. -/

/-! The third statement, at `check_syscall` level:

    ```
    Example getdents64_answers_are_inert :
      check_syscall (getdents64_in 5 0) (mkEffect (errno_ret EINVAL) [] [])
        getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 3 0) (mkEffect (errno_ret ENOTDIR) [] [])
           getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 4 0) (mkEffect (errno_ret ENOTDIR) [] [])
           getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 0 0) (mkEffect (errno_ret ENOTDIR) [] [])
           getdents64_model = CheckOk getdents64_model []
      /\ check_syscall (getdents64_in 99 0) (mkEffect (errno_ret EBADF) [] [])
           getdents64_model = CheckOk getdents64_model []
      (* and the injected failure, which leaves the model alone too *)
      /\ check_syscall (getdents64_in 5 0) (mkEffect (errno_ret ENOENT) [] [])
           getdents64_model = CheckOk getdents64_model [].
    Proof. repeat split; check_eq. Qed.
    ```
-/
theorem getdents64_answers_are_inert :
  check_syscall (getdents64_in 5 0) (mkEffect (errno_ret EINVAL) [] [])
    getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 3 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 4 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 0 0) (mkEffect (errno_ret ENOTDIR) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 99 0) (mkEffect (errno_ret EBADF) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
  ∧ check_syscall (getdents64_in 5 0) (mkEffect (errno_ret ENOENT) [] [])
       getdents64_model = check_result.CheckOk getdents64_model []
:= by
  (repeat' apply And.intro)
  /- The directory with a buffer that cannot hold an entry: -EINVAL. -/
  · getdents64_dir (5) (0)
    rw [ite_eq_right (by decide : ¬(errno_ret_in getdents64_errnos
          (errno_ret EINVAL) = true)),
        ite_eq_left (by decide : bv_eqb (errno_ret EINVAL) (errno_ret EINVAL) = true)]
  /- A regular file: -ENOTDIR, and the model is the same one. -/
  · getdents64_other (3) (some (FdEntry.FdFile [102] 7))
  /- …and an O_WRONLY one, whose offset 9 must also survive. -/
  · getdents64_other (4) (some (FdEntry.FdFileW [103] 9))
  /- A channel: -ENOTDIR as well. -/
  · getdents64_other (0) (some (FdEntry.FdChannel 0))
  /- A CLOSED descriptor: -EBADF, and no object is examined at all. -/
  · getdents64_other (99) (none)
  /- …and the injected -ENOENT, which `iterate_dir` answers for a removed
     directory before `filldir64` ever runs. -/
  · getdents64_dir (5) (0)
    rw [ite_eq_left (by decide : errno_ret_in getdents64_errnos (errno_ret ENOENT) = true)]

end LinuxSem.Checks.Cases.Fs.Readdir
