/-
  * LinuxSem.Checks.Cases.Fs.ReadWrite — worked examples over read (63), write (64), pread64 (67), pwrite64 (68), writev (66), readv (65), lseek (62)

  Worked cases over `Sys.Fs.ReadWrite`, which answers to Linux
  [fs/read_write.c]: the examples for the syscalls defined there, and no
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
  - a record field is read by dot notation here (`e.eff_writes`), the
    same projection the prelude applies as a function;
    `m_fds`/`m_fs`/`m_stdin`/`m_pipes` are already functions
    (`StateLedger`), so they need no shim.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  `decide` cannot be the rule: `check_result` carries
  a `Model` and so has no `DecidableEq`.

  The file has two layers.  The worked examples above are closed
  computations and are all proved.  The sixteen lemmas quantified over
  free variables, in the section at the end of the file, are ordinary
  tactic proofs; each names what its argument turns on where the shape is
  not obvious.  Ten are proved there, and six are marked `TODO` with what
  is missing and why.  `read_eof_is_sticky` is the one that is RESTATED:
  the sentence provable in this tree's `InputStream` encoding is not the
  naive one, so the file proves the provable form (under `stream_sticky`
  plus the checker's position-0 test) and carries the counterexample in
  its comment.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Sys.Fs.ReadWrite
-- the `check_write` / `check_writev` quadruples live in these two
-- companion modules (the file is split by size, not by subject); the
-- quantified lemmas below need their completeness halves
import LinuxSem.Checks.Sys.Fs.ReadWrite.Write
import LinuxSem.Checks.Sys.Fs.ReadWrite.Vec
import LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
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
open LinuxSem.LinuxProcessSem.Sys.Fs.Open
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Fs.ReadWrite
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess
open LinuxSem.Checks.Cases.Prelude

namespace LinuxSem.Checks.Cases.Fs.ReadWrite

open LinuxSem.Common.RocqSpelling

/-! The Rocq spellings used below (`bv_unsigned`, `Z_to_bv`, …) are the shared transparent aliases of `LinuxSem.Common.RocqSpelling`. -/










/-! The headline property, short writes included: on the same model, an
    admissible channel-writev outcome whose gathered bytes equal the
    readable contents of a write's flat buffer determines an admissible
    outcome of that write — same return, same post-model, same per-byte
    events, with only [eff_copyins] replaced by the flat-buffer range.
    (And hence, byte-level events erasing chunking — see part 3 — its
    events are also events of the per-iovec SEQUENCE of writes.  This
    is why musl's stdio flushing through writev costs nothing.)

    Inherits [writev_channel_outcome]'s import premise: the iovec array
    has to import cleanly ([ImpOk]), which readability alone does not
    give — a descriptor whose length is negative as [ssize_t] is
    -EINVAL, and there is no writev outcome to place. -/

theorem write_ab_events :
  check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
    (with_copyins [(4096, 2)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97, event.WriteEv 1 98]
:= by rfl

/-! The same write("ab") may deliver only "a" — a SHORT channel write,
    the environment's choice: ret 1 with one event for the delivered
    byte is admissible.  What is NOT admissible: delivering more than
    was readable-and-requested (ret 3), and a zero-byte delivery of a
    nonzero request (a blocked pipe blocks; it does not return 0). -/

theorem write_ab_short_delivery :
  check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
    (with_copyins [(4096, 1)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97]
  ∧ check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
       (with_copyins [(4096, 3)] (mkEffect 3 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
       (with_copyins [(4096, 0)] (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...produces exactly the events of write("a"); write("b"): the trace
    cannot tell the syscall chunking apart, which is the point of
    byte-granularity events.  (Channel writes do not change the model,
    so both writes run from [init_model].) -/

theorem write_a_then_b_events :
  check_syscall (SyscallInput.mkInput 64 [1, 4096, 1, 0, 0, 0] mem_ab (fun _ => none))
    (with_copyins [(4096, 1)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97]
  ∧ check_syscall (SyscallInput.mkInput 64 [1, 4097, 1, 0, 0, 0] mem_ab (fun _ => none))
       (with_copyins [(4097, 1)] (mkEffect 1 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 98]
:= by constructor <;> rfl

/-! Concretely for writev: [mem_ab] plus an iovec array at 8192
    splitting "ab" into two single-byte iovecs {4096,1},{4097,1} (LP64
    iovec layout: 8-byte little-endian base then length). -/

theorem read_bad_fd_ebadf :
  check_syscall (SyscallInput.mkInput 63 [5, 4096, 16, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
:= by rfl

theorem read_bad_fd_success_rejected :
  check_syscall (SyscallInput.mkInput 63 [5, 4096, 16, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 4 [(4096, [1, 2, 3, 4])] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckReject
:= by rfl

/- -------------------------------------------------------------------------
   munmap: length, alignment, and the ledger.  A model with one live
   4096-byte anonymous mapping at 65536.
   ------------------------------------------------------------------------- -/

theorem write_fd_truncates_to_32_bits :
  check_syscall (SyscallInput.mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1), 4096, 2, 0, 0, 0]
                   mem_ab (fun _ => none))
    (with_copyins [(4096, 2)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
      (with_copyins [(4096, 2)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  ∧ check_syscall (SyscallInput.mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1), 4096, 2, 0, 0, 0]
                     mem_ab (fun _ => none))
       (with_copyins [(4096, 2)] (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97, event.WriteEv 1 98]
:= by constructor <;> rfl

theorem write_fd_high_bits_ebadf_rejected :
  check_syscall (SyscallInput.mkInput 64 [Z_to_bv 64 (2 ^ 32 + 1), 4096, 2, 0, 0, 0]
                   mem_ab (fun _ => none))
    (with_copyins [(4096, 2)] (mkEffect (errno_ret EBADF) [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckReject
:= by rfl

/-! read(2^32, buf, 16) is a read on STDIN: at end of input it returns 0,
    not -EBADF. -/

theorem read_fd_truncates_to_32_bits :
  check_syscall (SyscallInput.mkInput 63 [Z_to_bv 64 (2 ^ 32), 4096, 16, 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 63 [Z_to_bv 64 (2 ^ 32), 4096, 16, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The dead-fd boundary sweep: 2^31 (INT_MIN as an [int]), 2^32 - 1
    (-1), and 2^64 - 1 all have low halves at or above 2^31, which no
    entry of a table capped at 4096 ([State.alloc_fd]) can match — so
    zero- and sign-extension of the low half agree on every one of them,
    which is what makes [fd32]'s zero-extension faithful. -/

/-! THE SHARED WRITE GUARD IS SHARED, pinned once per file kind.

    [write_spec]'s three file arms -- the write-only one, the append one
    and the read-write one -- reach their count gate through ONE helper,
    [ReadWrite.write_range_gate].  Agreeing on the helper's NAME is not
    enough, and this example checks the ANSWER: a helper the arms agree
    on can still be given the wrong boundary, and no proof in this
    development relates the three arms.

    THIS IS THE TEST THAT NOTICES, and it is written as three claims
    rather than one because the thing at risk is precisely that the
    three stop being one thing.  A single example on a single kind would
    pass throughout the divergence it exists to catch.

    THE COUNT IS DERIVED FROM THE BOUND, not written as a literal:
    [Uaccess.rw_bytes_max] is the constant the guard reads, so moving it
    moves this example with it.  A literal 131073 would keep passing
    against a bound that had moved, which is the same failure one step
    removed.

    THE BUFFER IS AT THE TOP OF THE ADDRESS SPACE, and it has to be.
    The gate is the DISJUNCTION
    [modeled_rw_count count || access_okb buf count], so a count past
    [rw_bytes_max] at an ordinary mapped buffer is admitted by the right
    disjunct and declines on no kind at all.  Putting [buf] where
    [buf + count] passes [State.TASK_SIZE] switches the right disjunct
    off and leaves the count as the only thing that can admit the call,
    which is what makes this a test of the COUNT boundary.

    AND THAT IS ALSO WHY THE LAST THREE CONJUNCTS EXIST.  At [near_top]
    the disjunction and its LEFT disjunct alone agree at every count, so
    everything above is blind to an arm that gates on [modeled_rw_count]
    by itself.  The mapped buffer is where the two part, and
    the three answers there are what a re-acquired count gate would
    move.

    The file is present and the fd is open, so nothing else on any of
    the three arms can be what declines -- and the guard runs ahead of
    the append arm's [access_ok] and [rw_verify_area] too, so the three
    really do meet here rather than at three different tests. -/
theorem write_count_bound_declines_on_every_file_kind :
  let over := Z_to_bv 64 (rw_bytes_max + 1) ;
  let at_bound := Z_to_bv 64 rw_bytes_max ;
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) ;
  let unmod r := (match r with | check_result.CheckUnmodeled => true | _ => false ) ;
  let model_of (k : path → word → FdEntry) : Model :=
    mkModel [(3, k [102] (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      [([102], [104, 105])] ;
  let call_at b n k := check_syscall
        (SyscallInput.mkInput 64 [3, b, n, 0, 0, 0]
           (fun a => if bv_eqb a b then some 122 else none)
           (fun _ => none))
        (with_copyins [(b, 1)] (mkEffect 1 [] []))
        (model_of k) ;
  let call n k := call_at near_top n k ;
  call over FdEntry.FdFileW = check_result.CheckUnmodeled
  ∧ call over FdEntry.FdFileA = check_result.CheckUnmodeled
  ∧ call over FdEntry.FdFileRW = check_result.CheckUnmodeled
  /- ...and the SAME call at the bound itself declines on no kind, which
     is what stops the three claims above from holding for some reason of
     their own.  A count of [rw_bytes_max] is inside the gate's LEFT
     disjunct, so the call is admitted even though the buffer is not
     addressable -- and whatever each arm then answers, and the three
     answer differently because their middles differ, none of them
     answers [CheckUnmodeled].  Without this half the example would keep
     passing if an arm started declining for an unrelated reason, which
     is exactly the shape it exists to rule out. -/
  ∧ unmod (call at_bound FdEntry.FdFileW) = false
  ∧ unmod (call at_bound FdEntry.FdFileA) = false
  ∧ unmod (call at_bound FdEntry.FdFileRW) = false
  /- ...AND THE SAME OVERSIZED COUNT AT A MAPPED BUFFER DECLINES ON NO
     KIND EITHER, which is the half that says WHICH disjunct is missing
     when one goes.  Above the bound the two candidate gates part company
     only here: [Uaccess.modeled_rw_count] alone would decline this call,
     the disjunction admits it through [access_okb].  Without these three
     the example would still pass on an arm with a [modeled_rw_count]
     gate of its own, because at [near_top] above the two agree at every
     count. -/
  ∧ unmod (call_at (Z_to_bv 64 4096) over FdEntry.FdFileW) = false
  ∧ unmod (call_at (Z_to_bv 64 4096) over FdEntry.FdFileA) = false
  ∧ unmod (call_at (Z_to_bv 64 4096) over FdEntry.FdFileRW) = false
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...AND THE SECOND BOUNDARY, which is the one a change to the RANGE
    judgement moves.  The count guard above is not enough on its own:
    [Uaccess.modeled_rw_count] reads the count and nothing else, so a
    rewrite that folded the BUFFER into the shared guard would agree
    with it at every count and disagree only where [buf + count] crosses
    [State.TASK_SIZE].  A test that never puts a buffer there cannot
    tell the two apart, and would stay green through exactly the
    divergence it was written to catch.

    So this pins the three kinds at that address instead, and the three
    answers DIFFER -- which is the point rather than a defect, and the
    one thing the shared helper deliberately does NOT make uniform.  The
    append arm models [vfs_write]'s [access_ok] and refuses a delivering
    write whose named range passes TASK_SIZE; the write-only arm models
    neither that test nor [rw_verify_area], judging a delivering write
    by its readable prefix instead, which is a known divergence from
    Linux; and the
    read-write arm takes the write-only answer because it calls the same
    two helpers with the same empty middle in front of them.

    WHAT THIS LINE IS FOR: a change to the shared range judgement has to
    come here and say what it did to all three.  Move the append arm's
    [access_ok] into [ReadWrite.write_file_tail], where it would look
    like tidying, and the first verdict below flips -- the write-only arm
    would start refusing a write Linux's own [vfs_write] does not refuse
    on that arm's reading, which is a behaviour change wearing a
    refactor's clothes. -/
theorem write_range_boundary_pins_the_three_file_kinds :
  let near_top := Z_to_bv 64 (TASK_SIZE - 4) ;
  let small := Z_to_bv 64 8 ;
  let model_of (k : path → word → FdEntry) : Model :=
    mkModel [(3, k [102] (Z_to_bv 64 0))] (mkVmMaps [] [] 0 0 demo_limit) IEof
      [([102], [104, 105])] ;
  let call k := check_syscall
        (SyscallInput.mkInput 64 [3, near_top, small, 0, 0, 0]
           (fun a => if bv_eqb a near_top then some 122 else none)
           (fun _ => none))
        (with_copyins [(near_top, 1)] (mkEffect 1 [] []))
        (model_of k) ;
  let verdict (r : check_result) : Nat :=
    (match r with
    | check_result.CheckOk _ _ => 0 | check_result.CheckReject => 1 | check_result.CheckUnmodeled => 2
    ) ;
  /- the count is far inside [rw_bytes_max], so the guard pinned above is
     not what answers here -/
  verdict (call FdEntry.FdFileW) = 0      /- no access_ok modeled: judged by the readable prefix -/
  ∧ verdict (call FdEntry.FdFileA) = 1   /- access_ok modeled: the delivering write is refused -/
  ∧ verdict (call FdEntry.FdFileRW) = 0/- the write-only shape, so the write-only answer -/
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...AND NO AGGREGATE BOUND OF THE MODEL'S OWN on [writev], pinned the
    same way.

    [writev_spec]'s file arms carry no gate declining an aggregate past
    [Uaccess.rw_bytes_max]: the import already clamps the aggregate at
    the kernel's own [State.MAX_RW_COUNT] ([State.cap_iovecs]), so a
    bound of the model's own in front of it would only narrow what is
    judged.  An arm that kept such a gate would decline on an O_RDWR
    descriptor an aggregate the same [writev] on an O_WRONLY descriptor
    delivers.  Not a wrong answer — a decline never is — but the same
    call judged by which descriptor it holds.

    THE THREE ANSWER ALIKE HERE.  The aggregate is one byte past
    [Uaccess.rw_bytes_max], DERIVED from it rather than spelled, so it
    moves if the constant does.  The source address is
    unmapped, so every kind gathers nothing and answers -EFAULT against a
    claimed length of 1; what this asserts is that none of them answers
    [CheckUnmodeled], which is exactly what such a gate would make an
    arm do.

    THE PIPE IS THE CONTROL.  A vectored write to a pipe declines for a
    reason of its own ([writev_buf_gap], the atomicity argument being per
    transfer rather than per vector), so [CheckUnmodeled] is reachable in
    this fixture and "not unmodeled" above is a fact about the file arms
    rather than about the shape of the call. -/
theorem writev_aggregate_past_the_retired_bound_is_judged_by_every_file_kind :
  let iovbytes := word_le8 (Z_to_bv 64 4096)
                    ++ word_le8 (Z_to_bv 64 (rw_bytes_max + 1)) ;
  let mem : word → Option byte :=
    fun a =>
      if bv_leu 8192 a && bv_ltu a 8208
      then nth_error iovbytes (Int.toNat (bv_unsigned a - 8192))
      else none ;
  let unmod r := (match r with | check_result.CheckUnmodeled => true | _ => false ) ;
  let call (e : FdEntry) := check_syscall
        (SyscallInput.mkInput 66 [3, 8192, 1, 0, 0, 0] mem (fun _ => none))
        (mkEffect 1 [] [])
        (mkModel [(3, e)] (mkVmMaps [] [] 0 0 demo_limit) IEof
           [([102], [104, 105])]) ;
  unmod (call (FdEntry.FdFileW [102] (Z_to_bv 64 0))) = false
  ∧ unmod (call (FdEntry.FdFileRW [102] (Z_to_bv 64 0))) = false
  ∧ unmod (call (FdEntry.FdFileA [102] (Z_to_bv 64 0))) = false
  ∧ unmod (call (FdEntry.FdPipe (Z_to_bv 64 7) true)) = true
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE KIND ANSWERS IN BOTH DIRECTIONS, which is the whole content of
    [State.FdFileRW], and the half no real run reaches is the REFUSAL: a
    kernel cannot make a read-write fd answer -EBADF to either
    direction, so the model must not admit one that claims to.  Both
    -EBADFs are the answer the OTHER two file kinds really give, which
    is what makes this the mistake a flag on [FdFileW] would have
    produced. -/
theorem rdwr_fd_refuses_ebadf_in_either_direction :
  let m := mkModel [(3, FdEntry.FdFileRW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             [([102], [104, 105])] ;
  check_syscall (SyscallInput.mkInput 63 [3, 4096, 1, 0, 0, 0] (fun _ => none)
                   (fun a => if bv_eqb a 4096 then some 0 else none))
    (mkEffect (errno_ret EBADF) [] []) m = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
                      (fun a => if bv_eqb a 4096 then some 122 else none)
                      (fun _ => none))
       (with_copyins [(4096, 1)] (mkEffect (errno_ret EBADF) [] [])) m
     = check_result.CheckReject
:= by constructor <;> rfl

/-! ...and the positive half of the same claim, on ONE descriptor: the
    read moves the offset the WRITE then lands at.  A model that minted
    two independent positions, or that wrote the entry back under the
    read-only kind, gives "hz" here rather than "hz" at index 1 — the
    file below is "hi" with the second byte overwritten. -/
theorem rdwr_read_then_write_shares_one_offset :
  let m := mkModel [(3, FdEntry.FdFileRW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
             [([102], [104, 105])] ;
  (match check_syscall (SyscallInput.mkInput 63 [3, 4096, 1, 0, 0, 0] (fun _ => none)
                         (fun a => if bv_eqb a 4096 then some 0 else none))
          (mkEffect 1 [(4096, [104])] []) m with
  | check_result.CheckOk m1 [] =>
      fd_lookup (m_fds m1) 3 = some (FdEntry.FdFileRW [102] 1)
      ∧ (match check_syscall
                 (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
                    (fun a => if bv_eqb a 4096 then some 122 else none)
                    (fun _ => none))
                 (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m1 with
         | check_result.CheckOk m2 [] => fs_lookup (m_fs m2) [102] = some [104, 122]
         | _ => False
         )
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

def mem_open_write : word → Option byte :=
  fun a => if bv_eqb a 8192 then some 102       /- 'f' -/
           else if bv_eqb a 8193 then some 0    /- NUL -/
           else if bv_eqb a 4096 then some 104  /- 'h' -/
           else if bv_eqb a 4097 then some 105  /- 'i' -/
           else none

theorem create_write_updates_fs :
  (match check_syscall
          (SyscallInput.mkInput 56 [AT_FDCWD, 8192, Z_to_bv 64 wr_create_flags, 420, 0, 0]
             mem_open_write (fun _ => none))
          (with_copyins [(8192, 2)] (mkEffect 3 [] []))
          (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) with
  | check_result.CheckOk m1 [] =>
      (match check_syscall (SyscallInput.mkInput 64 [3, 4096, 2, 0, 0, 0] mem_open_write (fun _ => none))
              (with_copyins [(4096, 2)] (mkEffect 2 [] [])) m1 with
      | check_result.CheckOk m2 [] => fs_lookup (m_fs m2) [102] = some [104, 105]
      | _ => False
      )
  | _ => False
  )
:= by rfl

/-! File "f" = "hi" open FOR WRITING at fd 3, with the offset parked at 4
    — two bytes PAST end-of-file, where only an lseek can put it. -/

theorem write_zero_len_past_eof_leaves_file_alone :
  (match check_syscall (SyscallInput.mkInput 64 [3, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
          (mkEffect 0 [] []) wpast_model with
  | check_result.CheckOk m [] =>
      fs_lookup (m_fs m) [102] = some [104, 105]
      ∧ fd_lookup (m_fds m) 3 = some (FdEntry.FdFileW [102] 4)
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

theorem write_zero_len_rejects_zero_length_copyin :
  check_syscall (SyscallInput.mkInput 64 [3, 4096, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (with_copyins [(4096, 0)] (mkEffect 0 [] [])) wpast_model = check_result.CheckReject
:= by rfl

/-! The contrast: a NONEMPTY write at the same offset does zero-fill the
    gap (sparse-file semantics), so the no-op above is confined to the
    zero-length corner.  write(3, "z", 1) makes "f" = "hi\0\0z". -/

theorem write_one_byte_past_eof_zero_fills :
  (match check_syscall
          (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
             (fun a => if bv_eqb a 4096 then some 122 else none) (fun _ => none))
          (with_copyins [(4096, 1)] (mkEffect 1 [] [])) wpast_model with
  | check_result.CheckOk m [] =>
      fs_lookup (m_fs m) [102] = some [104, 105, 0, 0, 122]
      ∧ fd_lookup (m_fds m) 3 = some (FdEntry.FdFileW [102] 5)
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A zero-length write WITHIN the file is a no-op, since the two
    [file_write] arms agree at or below end-of-file. -/

theorem write_zero_len_within_file_is_a_noop :
  (match check_syscall (SyscallInput.mkInput 64 [3, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
          (mkEffect 0 [] [])
          (with_fds (fd_insert (m_fds wpast_model) 3 (FdEntry.FdFileW [102] 1)) wpast_model) with
  | check_result.CheckOk m [] => fs_lookup (m_fs m) [102] = some [104, 105]
  | _ => False
  )
:= by rfl

/-! File "f" = "hi" open in APPEND MODE at fd 3, twice, with [f_pos]
    parked at two different places -- one past end-of-file, one at the
    start.  Only an lseek can put it either way. -/

def apast_model : Model :=
  mkModel [(3, FdEntry.FdFileA [102] 4)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104, 105])]

def azero_model : Model :=
  mkModel [(3, FdEntry.FdFileA [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104, 105])]

/-! AN APPEND WRITE DOES NOT READ [f_pos], stated as an equality between
    two whole checker answers rather than as two separate runs.  A real
    run can move the offset and watch the bytes land at the end anyway,
    but it runs ONE offset per execution and so can never say that the answer is the SAME for two
    of them -- which is the actual claim, and the one a spec that
    quietly used [off] would falsify.

    Both answers write "hiz", not "hi\0\0z": the byte goes to
    [len_word data], and the zero-fill the [FdFileW] arm would have had
    to build here is exactly what [ReadWrite.append_opens_no_gap] proves
    an append write never asks for.  And [f_pos] ends at the new end of
    file, 3, from BOTH starting offsets. -/
theorem append_write_ignores_the_offset :
  let w m := check_syscall
        (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
           (fun a => if bv_eqb a 4096 then some 122 else none) (fun _ => none))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m ;
  w apast_model = w azero_model
  ∧ (match w apast_model with
     | check_result.CheckOk m [] =>
         fs_lookup (m_fs m) [102] = some [104, 105, 122]
         ∧ fd_lookup (m_fds m) 3 = some (FdEntry.FdFileA [102] 3)
     | _ => False
     )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...AND A ZERO-LENGTH APPEND WRITE MOVES NOTHING, which is the one
    place the equality above stops holding — deliberately, and it is the
    sharper claim of the two.

    [generic_write_checks] (mm/filemap.c) opens with
    [if (!iov_iter_count(from)) return 0;] BEFORE the
    [if (iocb->ki_flags & IOCB_APPEND) iocb->ki_pos = i_size_read(inode);]
    line, so a zero-count write never computes the append position at
    all; and [new_sync_write] (fs/read_write.c) copies [ki_pos] back only
    under [if (ret > 0 && ppos)].  [f_pos] therefore stays exactly where
    an [lseek] left it, and the two models below answer DIFFERENTLY —
    4 and 0 — where a delivering write makes them agree.  An arm that
    assigned end-of-file unconditionally would answer 3 for both, which
    is a modeled wrong answer rather than a gap: the next
    [lseek(fd, 0, SEEK_CUR)] reports it.

    The file is untouched in both, as [Fs.file_write]'s own [[]] arm
    already guarantees; it is the offset that needed
    [ReadWrite.append_new_pos]. -/
theorem append_zero_write_leaves_the_offset_alone :
  let w m := check_syscall
        (SyscallInput.mkInput 64 [3, 4096, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
        (mkEffect 0 [] []) m ;
  (match w apast_model, w azero_model with
  | check_result.CheckOk m1 [], check_result.CheckOk m2 [] =>
      fs_lookup (m_fs m1) [102] = some [104, 105]
      ∧ fd_lookup (m_fds m1) 3 = some (FdEntry.FdFileA [102] 4)
      ∧ fs_lookup (m_fs m2) [102] = some [104, 105]
      ∧ fd_lookup (m_fds m2) 3 = some (FdEntry.FdFileA [102] 0)
  | _, _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [rw_verify_area]'s position test on a SCALAR write to an APPEND fd,
    which is the one place that arm is not the write-only arm with the
    destination moved.

    [vfs_write] hands [rw_verify_area] (fs/read_write.c) the fd's real
    [&f_pos] and it runs BEFORE the iterator, so
    [(loff_t)(pos + count) < 0] is decided on the position an [lseek]
    left behind — [generic_write_checks] (mm/filemap.c) overrides
    [ki_pos] only once the write is under way.  The append arm keeps the
    test for a reason the write-only arm does not have: it drops
    [modeled_file_gap], and that guard is the whole of why the
    write-only arm's omission of the test is unreachable.  Without
    either guard the
    model would have appended the byte and answered 1 where Linux
    answers -EINVAL.

    A REAL RUN HERE DEPENDS ON THE FILE SYSTEM rather than the model:
    reaching it needs [lseek(fd, LLONG_MAX, SEEK_SET)] to SUCCEED, which
    holds on tmpfs ([s_maxbytes] is [MAX_LFS_FILESIZE]) and fails with
    -EINVAL on a file system whose [s_maxbytes] is smaller, ext4 among
    them.  Both directions are pinned here instead. -/
def append_llong_max_model : Model :=
  mkModel [(3, FdEntry.FdFileA [102] (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [104, 105])]

theorem append_write_at_llong_max_is_einval :
  check_syscall (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
                   (fun a => if bv_eqb a 4096 then some 122 else none)
                   (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) append_llong_max_model
  = check_result.CheckOk append_llong_max_model []
  /- ...and the append the model would have made without the test is
     refused, file and offset untouched -/
  ∧ check_syscall (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
                      (fun a => if bv_eqb a 4096 then some 122 else none)
                      (fun _ => none))
       (with_copyins [(4096, 1)] (mkEffect 1 [] [])) append_llong_max_model
     = check_result.CheckReject
:= by constructor <;> rfl

/-! ...AND [access_ok] COMES FIRST, which is the half that decides the
    ORDER rather than the answer.  [vfs_write] runs
    [if (unlikely(!access_ok(buf, count))) return -EFAULT;] before it
    calls [rw_verify_area] (fs/read_write.c, Linux v6.18.46), so a buffer
    whose named range passes [State.TASK_SIZE] is -EFAULT even at a
    position that would otherwise be -EINVAL.  An arm that modeled the
    later test without the earlier one would answer -EINVAL here, and
    only a state satisfying BOTH conditions can tell the two orders
    apart — which is why this is its own example and not a conjunct of
    the one above.

    [buf] is [2 ^ 47] exactly, the first address whose one-byte range
    leaves the user address space. -/
theorem append_write_access_ok_precedes_the_position_test :
  check_syscall (SyscallInput.mkInput 64 [3, Z_to_bv 64 (2 ^ 47), 1, 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EFAULT) [] []) append_llong_max_model
  = check_result.CheckOk append_llong_max_model []
  /- the position test's answer, offered at the same call, is refused -/
  ∧ check_syscall (SyscallInput.mkInput 64 [3, Z_to_bv 64 (2 ^ 47), 1, 0, 0, 0]
                      (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) append_llong_max_model
     = check_result.CheckReject
:= by constructor <;> rfl

/-! ...and the [FdFileW] fd at the SAME offset is the contrast that makes
    the claim above about O_APPEND rather than about writes in general:
    it zero-fills out to 4 and leaves [f_pos] at 5. -/
theorem non_append_write_at_the_same_offset_differs :
  let w m := check_syscall
        (SyscallInput.mkInput 64 [3, 4096, 1, 0, 0, 0]
           (fun a => if bv_eqb a 4096 then some 122 else none) (fun _ => none))
        (with_copyins [(4096, 1)] (mkEffect 1 [] [])) m ;
  (match w wpast_model with
  | check_result.CheckOk m [] =>
      fs_lookup (m_fs m) [102] = some [104, 105, 0, 0, 122]
      ∧ fd_lookup (m_fds m) 3 = some (FdEntry.FdFileW [102] 5)
  | _ => False
  )
:= by (try dsimp only); (repeat constructor) <;> rfl



/- =========================================================================
   PART 3 — byte-level events erase syscall chunking

   Each example here compares TWO RUNS.  "These two calls emit the same
   events" is a statement about a pair of traces, and a real run yields
   one trace, so nothing in this part is reachable from a real run.
   ========================================================================= -/

def mem_writev_ab : word → Option byte :=
  fun a =>
    (match mem_ab a with
    | some b => some b
    | none =>
        if bv_leu 8192 a && bv_ltu a 8224
        then if bv_eqb a 8193 then some 16       /- iov[0].iov_base = 4096 -/
             else if bv_eqb a 8200 then some 1   /- iov[0].iov_len  = 1 -/
             else if bv_eqb a 8208 then some 1   /- iov[1].iov_base = 4097... -/
             else if bv_eqb a 8209 then some 16  /- ...= 1 + 16*256 -/
             else if bv_eqb a 8216 then some 1   /- iov[1].iov_len  = 1 -/
             else some 0
        else none
    )

/-! writev(1, [{4096,1},{4097,1}], 2) is accepted with exactly the
    verdict and events of write(1, "ab", 2) — one event per byte
    (cf. [write_ab_events]/[write_a_then_b_events]: the same events as
    write("a");write("b") too).  The concrete witness for the
    [writev_outcome_is_write_outcome] / [write_outcome_is_writev_outcome]
    pair — in particular that their two memory premises are jointly
    satisfiable, the flat buffer and the gathered iovecs living in
    different [in_mem]s. -/

theorem writev_two_iovecs_equals_one_write :
  check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
      (with_copyins [(4096, 2)] (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
       (with_copyins
          (import_iovecs_accesses mem_writev_ab 8192 2 ++
           iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
          (mkEffect 2 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97, event.WriteEv 1 98]
:= by constructor <;> rfl

/-! Linux >= 4.1 truncates writev's count to 32 bits before validating it
    ([iovcnt32]): with the same two-iovec array, iovcnt = 2^32 + 2 writes
    2 iovecs exactly like iovcnt = 2, and iovcnt = 2^32 is an empty writev
    returning 0.  A count whose low 32 bits exceed IOV_MAX (e.g. 1025, or
    -1's low 32 bits) is -EINVAL on every path.

    (qemu-user answers -EINVAL for the raw count instead.) -/

theorem writev_iovcnt_truncates_to_32_bits :
  check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32 + 2), 0, 0, 0]
                   mem_writev_ab (fun _ => none))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
      (with_copyins
         (import_iovecs_accesses mem_writev_ab 8192 2 ++
          iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
         (mkEffect 2 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32), 0, 0, 0]
                     mem_writev_ab (fun _ => none))
       (mkEffect 0 [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, 1025, 0, 0, 0] mem_writev_ab (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (two_pow_64 - 1), 0, 0, 0]
                     mem_writev_ab (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A raw count over IOV_MAX whose low 32 bits are in range is the
    truncated transfer and NOTHING ELSE: the bare -EINVAL qemu-user's
    [lock_iovec] answers for the raw count is REJECTED, where an older
    reading of this model admitted it beside the transfer.  The third
    conjunct keeps the count band honest from the other side: an IN-RANGE
    count accepts the delivery and NOT -EINVAL either. -/

theorem writev_over_max_truncates_only :
  check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32 + 2), 0, 0, 0]
                   mem_writev_ab (fun _ => none))
    (with_copyins
       (import_iovecs_accesses mem_writev_ab 8192 2 ++
        iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
       (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97, event.WriteEv 1 98]
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32 + 2), 0, 0, 0]
                     mem_writev_ab (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A two-entry array at 8192 with the entries given as words, plus one
    readable source byte at 4096: the shapes below vary the entries and
    keep the array. -/
def mem_iov_pair (b0 l0 b1 l1 : word) : word → Option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8224 then
      nth_error (word_le8 b0 ++ word_le8 l0 ++ word_le8 b1 ++ word_le8 l1)
        (Int.toNat (bv_unsigned a - 8192))
    else if bv_eqb a 4096 then some 97
    else none

/-! THE PER-SEGMENT [access_ok] REACHES writev TOO — [vfs_writev] and
    [vfs_readv] call the same [import_iovec] — and it runs on EVERY
    entry's uncapped length, zero-length entries included, before a byte
    is gathered.  A readable first entry followed by one whose range
    leaves the user address space is -EFAULT at import, not the one-byte
    short write an import without the check would gather; and a lone
    zero-length entry with a base past the ceiling is -EFAULT, not the 0
    qemu-user answers when its [lock_iovec] skips the entry.  Both pin
    the order whatever value the limit takes: the second entry's
    [addr <= TASK_SIZE - size] fails by one for base 1 and length
    [TASK_SIZE], and [2^63 <= TASK_SIZE] fails for any limit under
    2^63. -/
theorem writev_import_range_fault_beats_the_gather :
  let mem := mem_iov_pair 4096 1 1 (Z_to_bv 64 TASK_SIZE) ;
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem (fun _ => none))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, 2, 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 2 ++
                      iov_prefix_accesses (cap_iovecs [(4096, 1)]) 1)
          (mkEffect 1 [] [])) m
     = check_result.CheckReject
  ∧ let mem1 := mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0 ;
     check_syscall (SyscallInput.mkInput 66 [1, 8192, 1, 0, 0, 0] mem1 (fun _ => none))
       (with_copyins (import_iovecs_accesses mem1 8192 1)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = check_result.CheckOk m []
  ∧ let mem1 := mem_iov_pair (Z_to_bv 64 (2 ^ 63)) 0 0 0 ;
     check_syscall (SyscallInput.mkInput 66 [1, 8192, 1, 0, 0, 0] mem1 (fun _ => none))
       (with_copyins (import_iovecs_accesses mem1 8192 1) (mkEffect 0 [] [])) m
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [rw_verify_area]'s position test on the vectored write: a nonempty
    writev to a regular file at offset [LLONG_MAX] is -EINVAL, and the
    file and offset are untouched. -/
def writev_llong_max_model : Model :=
  mkModel [(3, FdEntry.FdFileW [102] (Z_to_bv 64 (2 ^ 63 - 1)))]
    (mkVmMaps [] [] 0 0 demo_limit) IEof [([102], [])]

theorem writev_at_llong_max_is_einval :
  check_syscall (SyscallInput.mkInput 66 [3, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
    (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2)
       (mkEffect (errno_ret EINVAL) [] [])) writev_llong_max_model
  = check_result.CheckOk writev_llong_max_model []
  ∧ check_syscall (SyscallInput.mkInput 66 [3, 8192, 2, 0, 0, 0] mem_writev_ab (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_writev_ab 8192 2 ++
                      iov_prefix_accesses (cap_iovecs [(4096, 1), (4097, 1)]) 2)
          (mkEffect 2 [] [])) writev_llong_max_model
     = check_result.CheckReject
:= by constructor <;> rfl

/-! THE AGGREGATE IS THE KERNEL'S, NOT THE MODEL'S.  A raw count of
    2^32 + 1 truncates to one segment; with that segment one byte over
    [Uaccess.rw_bytes_max] the call is JUDGED — a one-byte short write,
    since only [4096] is mapped — and not declined.  The first conjunct
    is the negative half: qemu-user's raw-count -EINVAL is REJECTED
    rather than declined, which is what an answered arm buys over a
    fail-closed one. -/
theorem writev_over_rw_bytes_max_total_is_judged :
  let mem := mem_iov_pair 4096 (Z_to_bv 64 (rw_bytes_max + 1)) 0 0 ;
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof) ;
  check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32 + 1), 0, 0, 0] mem (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) m
  = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 66 [1, 8192, Z_to_bv 64 (2 ^ 32 + 1), 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 1 ++
                      iov_prefix_accesses (cap_iovecs [(4096, Z_to_bv 64 (rw_bytes_max + 1))]) 1)
          (mkEffect 1 [] [])) m
     = check_result.CheckOk m [event.WriteEv 1 97]
:= by constructor <;> rfl

/-! The [MAX_RW_COUNT] aggregate cap is a per-entry walk, not a truncation
    of the total.  On a vector whose budget runs out INSIDE the second
    entry, all three of its behaviours show at once: the first entry, which
    fits, passes through UNCHANGED; the straddling second entry is cut IN
    PLACE to exactly the 16 bytes of budget left; and the third entry, past
    the cap entirely, SURVIVES AT LENGTH ZERO.

    That last one is the part a naive implementation gets wrong, and it
    matters because the kernel imports and address-checks the whole array:
    dropping the tail would renumber the vector, so a later index would
    silently shift onto a different descriptor.  [iovs_total_cap] proves
    the aggregate is right for every vector; this pins the SHAPE, which the
    aggregate alone does not determine.

    No real run can reach this: it would need a 2 GB aggregate, and the
    extracted checker overflows its stack well below that. -/

def mem_readv_iov : word → Option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8208
    then if bv_eqb a 8193 then some 16       /- iov[0].iov_base = 4096 -/
         else if bv_eqb a 8200 then some 1   /- iov[0].iov_len  = 1 -/
         else some 0
    else none

/-! The single-iovec import path caps its length BEFORE [access_ok], while
    the multi-iovec path checks every original length BEFORE applying the
    aggregate cap (lib/iov_iter.c [import_ubuf] against [__import_iovec]'s
    loop, v6.18.46).  Put the first base exactly [MAX_RW_COUNT] below
    [TASK_SIZE] and give it one byte more than [MAX_RW_COUNT]: the
    capped range ends exactly at the limit, but the original range ends
    one byte past it.  With [TASK_SIZE] = 2^47 the base is
    0x7fff80001000, a real user address.  The second descriptor is
    {NULL, 0} and matters only by selecting the multi-iovec path.

    The first two conjuncts pin the imported state directly.  The next two
    pin the corresponding readv results with EOF on stdin: count one
    reaches the read and returns zero, while count two faults during
    import.  The final rejection makes that distinction non-vacuous. -/

def readv_cap_order_base : word :=
  Z_to_bv 64 (TASK_SIZE - MAX_RW_COUNT)

def readv_cap_order_len : word :=
  Z_to_bv 64 (MAX_RW_COUNT + 1)

def mem_readv_cap_order : word → Option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8224 then
      nth_error
        (word_le8 readv_cap_order_base ++ word_le8 readv_cap_order_len ++
         word_le8 (Z_to_bv 64 0) ++ word_le8 (Z_to_bv 64 0))
        (Int.toNat (bv_unsigned a - 8192))
    else none

theorem readv_single_iovec_caps_before_access_ok :
  import_iovecs mem_readv_cap_order 8192 1
    = iov_import.ImpOk [(readv_cap_order_base, readv_cap_order_len)]
  ∧ import_iovecs mem_readv_cap_order 8192 2 = iov_import.ImpFault
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 1, 0, 0, 0]
          mem_readv_cap_order (fun _ => none))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 1)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0]
          mem_readv_cap_order (fun _ => none))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect (errno_ret EFAULT) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0]
          mem_readv_cap_order (fun _ => none))
       (with_copyins
          (import_iovecs_accesses mem_readv_cap_order 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A huge positive iov_len must not become a huge Peano natural during
    extraction.  These concrete checks force both bounded conversions:
    the channel case scatters one available byte through a 2^62-byte
    descriptor, and the file case first reads a one-byte file with that
    count and then scatters it.  Both ordinary one-byte deliveries remain
    modeled; the implementation bound changes evaluation strategy, not
    the relational syscall surface. -/

def readv_huge_len : word := Z_to_bv 64 (2 ^ 62)

def mem_readv_huge : word → Option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a 8208 then
      nth_error (word_le8 (Z_to_bv 64 4096) ++ word_le8 readv_huge_len)
        (Int.toNat (bv_unsigned a - 8192))
    else none

def wmem_readv_one : word → Option byte :=
  fun a => if bv_eqb a 4096 then some 0 else none

def readv_huge_file_model : Model :=
  mkModel [(3, FdEntry.FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [120])]

theorem readv_huge_len_delivers_one_byte_without_unary_expansion :
  check_syscall
    (SyscallInput.mkInput 65 [0, 8192, 1, 0, 0, 0] mem_readv_huge wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
       (mkEffect 1 [(4096, [120])] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.ReadEv 0 120]
  ∧ check_syscall
       (SyscallInput.mkInput 65 [3, 8192, 1, 0, 0, 0] mem_readv_huge wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
          (mkEffect 1 [(4096, [120])] [])) readv_huge_file_model
     = check_result.CheckOk
         (with_fds
            (fd_insert (m_fds readv_huge_file_model) 3 (FdEntry.FdFile [102] 1))
            readv_huge_file_model) []
:= by constructor <;> rfl

/-! The matching offset guard is bounded by the concrete file length too:
    an enormous offset on a one-byte file reaches EOF without converting
    that offset to a request-sized natural. -/

theorem readv_huge_file_offset_is_bounded_by_file_length :
  let m := with_fds
    (fd_insert (m_fds readv_huge_file_model) 3
      (FdEntry.FdFile [102] readv_huge_len)) readv_huge_file_model ;
  check_syscall
    (SyscallInput.mkInput 65 [3, 8192, 1, 0, 0, 0] mem_readv_huge wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_huge 8192 1)
       (mkEffect 0 [] [])) m = check_result.CheckOk m []
:= by rfl

/-! Linux keeps only eight descriptors on the syscall stack.  Counts 9
    through 1024 may fail their temporary allocation before importing any
    descriptor, so readv deliberately fails closed over that whole range.
    THE BAND IS KEYED ON THE NARROWED COUNT, so a raw 2^32+9 lands in it too
    and declines exactly as a bare 9 does. -/

def mem_readv_eight_zero : word → Option byte :=
  fun a =>
    if bv_leu 8192 a && bv_ltu a (8192 + 8 * 16) then some 0 else none

def readv_write_only_model : Model :=
  mkModel [(3, FdEntry.FdFileW [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [])]

theorem readv_heap_iovec_boundary_fails_closed :
  check_syscall
    (SyscallInput.mkInput 65 [0, 8192, 8, 0, 0, 0] mem_readv_eight_zero (fun _ => none))
    (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 8, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_eight_zero 8192 8)
          (mkEffect (errno_ret ENOMEM) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 9, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 9, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 1024, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect 0 [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
  ∧ check_syscall
       (SyscallInput.mkInput 65 [5, 8192, 9, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall
       (SyscallInput.mkInput 65 [3, 8192, 9, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
     = check_result.CheckOk readv_write_only_model []
  /- A raw count of 2^32 + 9 narrows to 9, inside the heap-backed band,
     so the call DECLINES exactly as the in-range twin above does: the raw
     high bits do not change whether the model can describe the call.
     Neither the -EINVAL qemu-user answers for the raw count nor the
     -ENOMEM the allocation may produce is admitted -- the first is not
     Linux's answer at all, the second is the decline's reason. -/
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, Z_to_bv 64 (2 ^ 32 + 9), 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, Z_to_bv 64 (2 ^ 32 + 9), 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret ENOMEM) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
  ∧ check_syscall
       (SyscallInput.mkInput 65 [0, 8192, 1025, 0, 0, 0]
          mem_readv_eight_zero (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! readv's count reaches Linux through [__import_iovec]'s [unsigned]
    parameter, so only the low 32 bits are used ([iovcnt32]): a raw count
    of 2^32 + 1 behaves exactly as 1.  Such a count takes the
    SINGLE-DESCRIPTOR import path and never reaches the UIO_MAXIOV test
    at all, which is why the answer is a plain 0 and not -EINVAL.

    (qemu-user validates the FULL 64-bit count in [lock_iovec] before
    dispatching, and answers -EINVAL instead.) -/

theorem readv_iovcnt_truncates_to_32_bits :
  check_syscall (SyscallInput.mkInput 65 [0, 8192, Z_to_bv 64 (2 ^ 32 + 1), 0, 0, 0]
                   mem_readv_iov (fun _ => none))
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_syscall (SyscallInput.mkInput 65 [0, 8192, 1, 0, 0, 0] mem_readv_iov (fun _ => none))
      (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
         (mkEffect 0 [] []))
      (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 1, 0, 0, 0] mem_readv_iov (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  /- two descriptors reaches the unreadable one: -EFAULT, so a zero return
     is inadmissible there -- the conjunct that makes the first two
     non-vacuous -/
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem_readv_iov (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 2)
          (mkEffect 0 [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A raw count over IOV_MAX whose low 32 bits select the on-stack path
    (one here) is a real transfer and NOTHING ELSE: the bare -EINVAL
    qemu-user's [lock_iovec] answers for the raw count is REJECTED.  The
    third conjunct keeps the count band honest from the other side: an
    IN-RANGE count accepts the delivery and NOT -EINVAL either. -/

theorem readv_over_max_truncates_only :
  check_syscall (SyscallInput.mkInput 65 [0, 8192, Z_to_bv 64 (2 ^ 32 + 1), 0, 0, 0]
                   mem_readv_iov (fun _ => none))
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect 0 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, Z_to_bv 64 (2 ^ 32 + 1), 0, 0, 0]
                     mem_readv_iov (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 1, 0, 0, 0] mem_readv_iov (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! An fd not open for reading is -EBADF decided BEFORE the iovec array is
    imported: fd 1 is stdout, and here NO memory is readable at all, so the
    array import would fault if it ran (fs/read_write.c [vfs_readv]'s
    [FMODE_READ] test precedes its [import_iovec] call, v6.18.46; commit
    b8e1425bae85 hoisted it there, first released in v6.8).  The second
    conjunct pins the order.

    (qemu-user's lock_iovec locks the descriptor array before it
    dispatches on the fd at all, so under qemu-user this shape answers
    -EFAULT.) -/

theorem readv_write_only_fd_is_ebadf_before_import :
  check_syscall (SyscallInput.mkInput 65 [1, 8192, 2, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 65 [1, 8192, 2, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EFAULT) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by constructor <;> rfl

/-! A file "abcde" on fd 3 at offset [off], and a directory on fd 3. -/
def readv_abcde_model (off : word) : Model :=
  mkModel [(3, FdEntry.FdFile [102] off)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [97, 98, 99, 100, 101])]

def readv_dir_model : Model :=
  mkModel [(3, FdEntry.FdDir)] (mkVmMaps [] [] 0 0 demo_limit) IEof []

/-! A ZERO-LENGTH ENTRY, THEN A BAD BASE, on a regular file.  The
    zero-length entry is skipped and the first delivered byte lands at
    NULL, which is not writable: -EFAULT, nothing delivered, the offset
    unchanged (mm/shmem.c [shmem_file_read_iter]: [copied = 0] on the
    first folio, so [-EFAULT] is returned rather than a count).  The
    negatives are the answers qemu-user gives for this vector: its
    [lock_iovec] zeroes a bad LATER range and every following length and
    lets the host call return 0 for the empty aggregate, and the same
    vector on a directory is -EISDIR.  Neither is Linux's answer on a
    file. -/
theorem readv_zero_prefix_then_bad_base_is_efault_on_a_file :
  let mem := mem_iov_pair 0 0 0 1 ;
  let m := readv_abcde_model 0 ;
  check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] [])) m
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE SAME VECTOR ON A DIRECTORY never reaches a copy: the entries
    import (an in-range NULL base passes [access_ok]; whether it is mapped
    is not asked), the aggregate is 1, and fs/libfs.c [generic_read_dir]
    answers -EISDIR without touching the destination.  qemu-user's 0 and
    -EFAULT for this vector are both refused.  The second pair puts a
    WRITABLE first entry ahead of the NULL one, and pins that -EFAULT is
    not admitted for a bad later base either. -/
theorem readv_directory_never_consults_the_destination :
  let mem := mem_iov_pair 0 0 0 1 ;
  let mem2 := mem_iov_pair 4096 1 0 1 ;
  let m := readv_dir_model ;
  check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EISDIR) [] [])) m
  = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 2) (mkEffect 0 [] [])) m
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem (fun _ => none))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem2 wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem2 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem2 wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem2 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! WHAT THE DESTINATION CAN SAY ON A DIRECTORY, IT SAYS AT IMPORT.  An
    entry whose range leaves the user address space — base 1 with length
    [TASK_SIZE], so [addr <= TASK_SIZE - size] fails by one — is -EFAULT
    from [__import_iovec]'s per-segment [access_ok], ahead of
    [generic_read_dir]; -EISDIR is not admitted.  Stated against the
    constant rather than a number so that it pins the ORDER, import
    before the read operation, whatever value the limit takes. -/
theorem readv_directory_import_range_fault_beats_eisdir :
  let mem := mem_iov_pair 1 (Z_to_bv 64 TASK_SIZE) 4096 3 ;
  let m := readv_dir_model ;
  check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem 8192 2)
       (mkEffect (errno_ret EFAULT) [] [])) m
  = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 2, 0, 0, 0] mem wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EISDIR) [] [])) m
     = check_result.CheckReject
:= by constructor <;> rfl

/-! [copy_iovec_from_user] loads BOTH fields of a descriptor before it
    tests the sign of [iov_len] (lib/iov_iter.c, v6.18.46), so a readable
    negative length beside an UNREADABLE base is -EFAULT, not -EINVAL:
    the base load faults first.  Here the first entry's base bytes
    (8192..8199) are absent and its length bytes hold 2^63.  Reachable
    on a real kernel through a page-granular hole with the array
    straddling the boundary.  The copy-in ledger is the one attempted
    descriptor. -/
def mem_readv_len_only : word → Option byte :=
  fun a =>
    if bv_leu 8200 a && bv_ltu a 8224 then
      nth_error (word_le8 (Z_to_bv 64 (2 ^ 63)) ++ word_le8 4096 ++ word_le8 1)
        (Int.toNat (bv_unsigned a - 8200))
    else none

theorem readv_unreadable_base_faults_before_the_sign_test :
  import_iovecs_accesses mem_readv_len_only 8192 2 = [(8192, 16)]
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem_readv_len_only (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_len_only 8192 2)
          (mkEffect (errno_ret EFAULT) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem_readv_len_only (fun _ => none))
       (with_copyins (import_iovecs_accesses mem_readv_len_only 8192 2)
          (mkEffect (errno_ret EINVAL) [] []))
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [rw_verify_area]'s position test (fs/read_write.c, v6.18.46): a
    nonempty readv of a regular file at offset [LLONG_MAX] is -EINVAL —
    [(loff_t)(pos + count) < 0] — where an offset merely past end-of-file
    is 0.  Reachable, since [lseek(fd, LLONG_MAX, SEEK_SET)] succeeds on
    tmpfs.  The scalar [read] reaches the same test on the kernel and
    still answers 0 in the model: the last two conjuncts pin THAT known
    divergence from Linux, so that closing it is a visible flip here
    rather than a silent one. -/
theorem readv_at_llong_max_is_einval_not_eof :
  let m := readv_abcde_model (Z_to_bv 64 (2 ^ 63 - 1)) ;
  check_syscall (SyscallInput.mkInput 65 [3, 8192, 1, 0, 0, 0] mem_readv_iov wmem_readv_one)
    (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
       (mkEffect (errno_ret EINVAL) [] [])) m
  = check_result.CheckOk m []
  ∧ check_syscall (SyscallInput.mkInput 65 [3, 8192, 1, 0, 0, 0] mem_readv_iov wmem_readv_one)
       (with_copyins (import_iovecs_accesses mem_readv_iov 8192 1)
          (mkEffect 0 [] [])) m
     = check_result.CheckReject
  ∧ check_syscall (SyscallInput.mkInput 63 [3, 4096, 1, 0, 0, 0] (fun _ => none) wmem_readv_one)
       (mkEffect 0 [] []) m
     = check_result.CheckOk (with_fds (fd_insert (m_fds m) 3
                  (FdEntry.FdFile [102] (Z_to_bv 64 (2 ^ 63 - 1)))) m) []
  ∧ check_syscall (SyscallInput.mkInput 63 [3, 4096, 1, 0, 0, 0] (fun _ => none) wmem_readv_one)
       (mkEffect (errno_ret EINVAL) [] []) m
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A PARTIALLY WRITABLE DESTINATION ON A PIPE IS DECLINED.  Five bytes
    are queued on stdin and the vector holds five, but only the first
    four destination bytes are writable: fs/pipe.c [anon_pipe_read]
    answers -EFAULT with four bytes stored and nothing consumed if the
    five arrived in one buffer, and a count of whole buffers otherwise,
    so the model declines the five-byte delivery, the -EFAULT and the
    four-byte short read alike.  Give it the fifth byte and the delivery
    is admitted: the decline is exactly [w < min total remaining].  The
    scalar [read] follows the same rule. -/
def hello_stdin : InputStream :=
  ICons 104 (ICons 101 (ICons 108 (ICons 108 (ICons 111 IEof))))

def wmem_first (n : Int) : word → Option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a (Z_to_bv 64 (4096 + n)) then some 0 else none

theorem partial_destination_on_a_pipe_declines :
  let mem := mem_iov_pair 4096 2 4098 3 ;
  let m := init_model [] 0 0 demo_sp demo_limit (demo_input [] hello_stdin) ;
  let delivered := mkEffect 5 [(4096, [104, 101]), (4098, [108, 108, 111])] [] ;
  check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem (wmem_first 4))
    (with_copyins (import_iovecs_accesses mem 8192 2) delivered) m
  = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem (wmem_first 4))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect (errno_ret EFAULT) [] [])) m
     = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem (wmem_first 4))
       (with_copyins (import_iovecs_accesses mem 8192 2)
          (mkEffect 4 [(4096, [104, 101]), (4098, [108, 108])] [])) m
     = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 65 [0, 8192, 2, 0, 0, 0] mem (wmem_first 5))
       (with_copyins (import_iovecs_accesses mem 8192 2) delivered) m
     = check_result.CheckOk (with_stdin IEof m)
         [event.ReadEv 0 104, event.ReadEv 0 101, event.ReadEv 0 108, event.ReadEv 0 108, event.ReadEv 0 111]
  ∧ check_syscall (SyscallInput.mkInput 63 [0, 4096, 100, 0, 0, 0] (fun _ => none) (wmem_first 4))
       (mkEffect 4 [(4096, [104, 101, 108, 108])] []) m
     = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 63 [0, 4096, 100, 0, 0, 0] (fun _ => none) (wmem_first 5))
       (mkEffect 5 [(4096, [104, 101, 108, 108, 111])] []) m
     = check_result.CheckOk (with_stdin IEof m)
         [event.ReadEv 0 104, event.ReadEv 0 101, event.ReadEv 0 108, event.ReadEv 0 108, event.ReadEv 0 111]
:= by (try dsimp only); (repeat constructor) <;> rfl

/- =========================================================================
   PART 4 — fail-closed, and the model state no observation reveals

   The rest of the per-syscall checks: cases a real run could reach only
   by making a REAL kernel misbehave, cases about model-internal
   bookkeeping, and the places qemu-user is known to diverge from
   Linux.
   ========================================================================= -/

/-! An unmodeled syscall number (umask = 166) is a model error — the
    dispatcher fails closed, so the trace semantics takes the [SError]
    transition.  Fatal for a target, so source binaries must keep away
    from unmodeled syscalls.  This is the shape of every [CheckUnmodeled]
    verdict in the development.

    Pick a number here that the dispatcher really does not cover, because
    the example does not fail loudly when its number gets an arm.  A
    modeled [uname] on an unmapped destination, for example, is
    [Unmodeled] too — for a different reason, a copy the model will not
    tear — so an example on it would go on computing to [CheckUnmodeled]
    and say nothing about the fallback arm it is named for.  A number
    whose decline is a JUDGEMENT rather than a missing field is what
    keeps it honest; umask is not modeled. -/

def lseek_model : Model :=
  mkModel [(0, FdEntry.FdChannel 0), (3, FdEntry.FdFile [102] 0)] (mkVmMaps [] [] 0 0 demo_limit) IEof
    [([102], [104, 105])]

/-! Channels are unseekable streams: -ESPIPE. -/

theorem lseek_channel_espipe :
  check_syscall (SyscallInput.mkInput 62 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ESPIPE) [] []) lseek_model
  = check_result.CheckOk lseek_model []
:= by rfl

/-! The whence check precedes the fd's KIND, which is what makes an
    unseekable fd answer -EINVAL rather than -ESPIPE: [ksys_lseek] tests
    [whence <= SEEK_MAX] before calling [vfs_llseek].  Verified on a real
    pipe under qemu-riscv64: whence 42 is -EINVAL, whence 4 (SEEK_HOLE)
    is -ESPIPE. -/

theorem lseek_channel_bad_whence_is_einval_not_espipe :
  check_syscall (SyscallInput.mkInput 62 [0, 0, 42, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = check_result.CheckOk lseek_model []
  ∧ check_syscall (SyscallInput.mkInput 62 [0, 0, 42, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret ESPIPE) [] []) lseek_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A whence the kernel DOES accept (SEEK_HOLE = 4 = [SEEK_MAX]) still
    reaches the fd's kind, so a channel is -ESPIPE there. -/

theorem lseek_channel_seek_hole_is_espipe :
  check_syscall (SyscallInput.mkInput 62 [0, 0, 4, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret ESPIPE) [] []) lseek_model
  = check_result.CheckOk lseek_model []
:= by rfl

/-! On a FILE, SEEK_DATA/SEEK_HOLE are answered by real filesystems —
    with a filesystem-dependent notion of a hole — so the model fails
    CLOSED there rather than claiming an -EINVAL. -/

theorem lseek_seek_data_on_a_file_is_unmodeled :
  check_syscall (SyscallInput.mkInput 62 [3, 0, 3, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = check_result.CheckUnmodeled
  ∧ check_syscall (SyscallInput.mkInput 62 [3, 0, 4, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 2 [] []) lseek_model
     = check_result.CheckUnmodeled
  /- AND THE TWO NEIGHBOURS THAT STILL ANSWER, one along each axis, so
     the pair above is a boundary rather than a description of one.
     Both declines are [CheckUnmodeled] and would survive [lseek]
     declining MORE -- SEEK_HOLE going unmodeled on the channel too, or
     the file arm going quiet on every whence.  So: whence 4 on the
     CHANNEL is still -ESPIPE, and whence 2 (SEEK_END) on the FILE still
     reports the size and advances the offset. -/
  ∧ check_syscall (SyscallInput.mkInput 62 [0, 0, 4, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret ESPIPE) [] []) lseek_model
     = check_result.CheckOk lseek_model []
  ∧ check_syscall (SyscallInput.mkInput 62 [3, 0, 2, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect 2 [] []) lseek_model
     = check_result.CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdEntry.FdFile [102] 2))
                  lseek_model) []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! [SYSCALL_DEFINE3(lseek, unsigned int, fd, off_t, offset,
    unsigned int, whence)]: the origin selector is truncated exactly like
    the fd, so lseek(3, 0, 2^32 | SEEK_END) is a SEEK_END and reports the
    file size.  A model that compared the full register would demand
    -EINVAL — a return no kernel produces — and so REJECT a conforming
    trace.  A real run can show the accepting half; that the -EINVAL is
    inadmissible it cannot. -/

theorem lseek_whence_high_bits_einval_rejected :
  check_syscall (SyscallInput.mkInput 62 [3, 0, Z_to_bv 64 (2 ^ 32 + 2), 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect 2 [] []) lseek_model
  = check_result.CheckOk (with_fds (fd_insert (m_fds lseek_model) 3 (FdEntry.FdFile [102] 2))
               lseek_model) []
  ∧ check_syscall (SyscallInput.mkInput 62 [3, 0, Z_to_bv 64 (2 ^ 32 + 2), 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) lseek_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The whence checks are ORDERED as [ksys_lseek] orders them: the fd is
    resolved first, so a whence no kernel accepts does not turn a bad fd
    into -EINVAL. -/

theorem lseek_bad_fd_beats_a_bad_whence :
  check_syscall (SyscallInput.mkInput 62 [9, 0, 42, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EBADF) [] []) lseek_model
  = check_result.CheckOk lseek_model []
  ∧ check_syscall (SyscallInput.mkInput 62 [9, 0, 42, 0, 0, 0] (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) lseek_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/- -------------------------------------------------------------------------
   ftruncate on a writable file fd whose path is NOT in the file system.

   Every other arm of [Open.ftruncate_spec] is reachable from a real
   run — including all five fd kinds, the negative length decided
   before the fd lookup, and both sides of the grow bound.  THIS arm is the exception:
   [Open.create_wronly] inserts the path into [m_fs] in the same step
   that hands out the [FdFileW], so no run can reach an [FdFileW]
   pointing at an absent file.  The arm exists because the spec cannot
   appeal to that invariant locally, and it fails closed rather than
   inventing an answer; this pins that it does.
   ------------------------------------------------------------------------- -/

/-! fd 3 is open write-only on "f", but "f" is not in the file system. -/

/- -------------------------------------------------------------------------
   ioctl on a CHANNEL.  Whether a run's standard channels are terminals
   is the environment's business, not the model's.
   ------------------------------------------------------------------------- -/

/-! TIOCGWINSZ — stdio's buffering-mode probe — answers -ENOTTY on a
    channel. -/

theorem bit31_is_part_of_the_32_bit_arguments :
  check_syscall (SyscallInput.mkInput 62 [3, 5, Z_to_bv 64 (2 ^ 31 + 2), 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) lseek_model
  = check_result.CheckOk lseek_model []
  ∧ check_syscall (SyscallInput.mkInput 64 [Z_to_bv 64 (2 ^ 31 + 1), 4096, 2, 0, 0, 0]
                     mem_ab (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 29 [Z_to_bv 64 (2 ^ 31 + 1), TIOCGWINSZ, 4096, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) []
  ∧ check_syscall (SyscallInput.mkInput 29 [1, Z_to_bv 64 (2 ^ 31 + 21523), 4096, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret ENOTTY) [] []) (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckUnmodeled
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! The empty pathname always fails with -ENOENT (path_resolution(7)),
    EVEN WHEN the file-system image contains an empty-path key — open("")
    must not match it.  A real run has one image, so only a
    literal can quantify the image this way.  Path bytes at
    8192: NUL only. -/

/- -------------------------------------------------------------------------
   Three answers Linux can produce that the model REJECTS.

   Each of these is a [CheckReject] on an honest kernel trace, so each is
   a known limitation of the model rather than a demonstration that the
   model is right.

   Every one pairs its rejection with the honest answer AT THE SAME CALL.
   That is the point of the pairing: a checker that had become constantly
   rejecting would fail these examples rather than pass them.  Three of
   the four discriminate further, and would flip to [CheckOk] if an arm
   for the limitation were added; [write_channel_epipe_rejected] is the
   exception and says so at its own docstring.
   ------------------------------------------------------------------------- -/

/-! -EINTR on a read.  read(0, buf, 1) with one byte of input delivers
    it; no model state admits the -EINTR a caught signal produces on a
    blocking read. -/

theorem read_channel_eintr_rejected :
  check_syscall (SyscallInput.mkInput 63 [0, 4096, 1, 0, 0, 0] (fun _ => none) wmem_readv_one)
    (mkEffect 1 [(4096, [120])] [])
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.ReadEv 0 120]
  ∧ check_syscall (SyscallInput.mkInput 63 [0, 4096, 1, 0, 0, 0] (fun _ => none) wmem_readv_one)
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] (ICons 120 IEof)))
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! -EINTR on a write.  write(1, "ab", 2) delivers both bytes; there is
    no arm for what a full pipe and a caught signal give.  fs/pipe.c
    [anon_pipe_write] returns -ERESTARTSYS, and only when nothing was
    copied; arch/riscv/kernel/signal.c [arch_do_signal_or_restart] is
    what turns that into -EINTR, on the branch where a handler runs.
    The same limitation.

    The second conjunct closes by [check_eq], which is [vm_compute], and
    that is a pin of its own: [check_write]'s channel arm converts the
    claimed return to a unary [nat] only under its range test, so an
    errno-encoded return evaluates in bounded time where a flat [&&]
    chain never came back. -/

theorem write_channel_eintr_rejected :
  check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
    (with_copyins [(4096, 2)] (mkEffect 2 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
      [event.WriteEv 1 97, event.WriteEv 1 98]
  ∧ check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
       (mkEffect (errno_ret EINTR) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by constructor <;> rfl

/-! -EPIPE on a channel write.  This rejection is the RIGHT answer for a
    process that installs no handler — SIGPIPE kills it before the errno
    is returned — and the defect is the other direction: the short write
    in the first conjunct is admitted in a state where the reader has
    gone and Linux kills the process instead.  So unlike the other three
    this pair does NOT discriminate its own limitation: no model state
    can express "the reader has gone", so neither conjunct would move if
    it were fixed.  What it carries is that -EPIPE is not admitted here,
    which is what a premature arm would break. -/

theorem write_channel_epipe_rejected :
  check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
    (with_copyins [(4096, 1)] (mkEffect 1 [] []))
    (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
  = check_result.CheckOk (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof)) [event.WriteEv 1 97]
  ∧ check_syscall (SyscallInput.mkInput 64 [1, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
       (mkEffect (errno_ret EPIPE) [] [])
       (init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof))
     = check_result.CheckReject
:= by constructor <;> rfl

/-! A SHORT write on a regular file.  [readv_write_only_model] has fd 3
    open write-only on the empty file "f", so write(3, "ab", 2) writes
    both bytes; the short positive count mm/filemap.c
    [generic_perform_write] returns when write_end fails partway
    (-ENOSPC, -EIO, -ENOMEM, -EDQUOT) is rejected. -/

theorem file_write_short_rejected :
  (match check_syscall (SyscallInput.mkInput 64 [3, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
          (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          readv_write_only_model with
  | check_result.CheckOk m [] => fs_lookup (m_fs m) [102] = some [97, 98]
  | _ => False
  )
  ∧ check_syscall (SyscallInput.mkInput 64 [3, 4096, 2, 0, 0, 0] mem_ab (fun _ => none))
       (with_copyins [(4096, 1)] (mkEffect 1 [] []))
       readv_write_only_model
     = check_result.CheckReject
:= by constructor <;> rfl




/-! The same ordering as a verdict.  fd 5 is not open in
    [readv_write_only_model], so a descriptor-first reading would answer
    -EBADF; the model answers -EINVAL and REFUSES the -EBADF.  The
    second conjunct is what makes the first one a check: without it the
    example would pass on a model that admitted both. -/
theorem pwrite64_negative_pos_rejects_ebadf :
  check_syscall
    (SyscallInput.mkInput 68 [5, 4096, 2, Z_to_bv 64 (-1), 0, 0] mem_ab (fun _ => none))
    (mkEffect (errno_ret EINVAL) [] []) readv_write_only_model
  = check_result.CheckOk readv_write_only_model []
  ∧ check_syscall
       (SyscallInput.mkInput 68 [5, 4096, 2, Z_to_bv 64 (-1), 0, 0] mem_ab (fun _ => none))
       (mkEffect (errno_ret EBADF) [] []) readv_write_only_model
     = check_result.CheckReject
:= by constructor <;> rfl

/-! A pwrite64 lands at the position the CALL names, not at the
    descriptor's offset — which is 0 on fd 3 here, so the two are
    distinguishable — and the descriptor's offset does not move.  Its
    reject twin is the same delivery claimed with the return a write at
    offset 0 would have made. -/
theorem pwrite64_writes_at_the_named_position :
  (match check_syscall
          (SyscallInput.mkInput 68 [3, 4096, 2, 4, 0, 0] mem_ab (fun _ => none))
          (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          readv_write_only_model with
  | check_result.CheckOk m [] =>
      fs_lookup (m_fs m) [102] = some [0, 0, 0, 0, 97, 98]
      ∧ fd_lookup (m_fds m) 3 = some (FdEntry.FdFileW [102] 0)
  | _ => False
  )
  ∧ check_syscall
       (SyscallInput.mkInput 68 [3, 4096, 2, 4, 0, 0] mem_ab (fun _ => none))
       (with_copyins [(4096, 2)] (mkEffect 1 [] []))
       readv_write_only_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ** Three more arms that judge a count over [Uaccess.rw_bytes_max]

    Like [write] and [writev], [pwrite64]'s write-only arm and [read]'s
    socket and pipe arms judge a count over [Uaccess.rw_bytes_max]
    rather than decline it.  These pin that.

    The socket half is in `Checks.Cases.Net.Socket`, beside the model
    that has a connection to read from. -/

/-! A [pwrite64] one byte over [Uaccess.rw_bytes_max] is JUDGED — a
    two-byte write, since [mem_ab] maps two bytes and a regular-file
    write takes the readable prefix — and not declined.  The
    second conjunct is the arm's determinism at that count: a SHORT
    write of one byte is refused, so the first conjunct is a claim about
    the only admissible answer rather than about one of several. -/
theorem pwrite64_over_rw_bytes_max_is_judged :
  (match check_syscall
          (SyscallInput.mkInput 68 [3, 4096, Z_to_bv 64 (rw_bytes_max + 1), 0, 0, 0]
             mem_ab (fun _ => none))
          (with_copyins [(4096, 2)] (mkEffect 2 [] []))
          readv_write_only_model with
  | check_result.CheckOk m [] => fs_lookup (m_fs m) [102] = some [97, 98]
  | _ => False
  )
  ∧ check_syscall
       (SyscallInput.mkInput 68 [3, 4096, Z_to_bv 64 (rw_bytes_max + 1), 0, 0, 0]
          mem_ab (fun _ => none))
       (with_copyins [(4096, 1)] (mkEffect 1 [] []))
       readv_write_only_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! A pipe holding two bytes, on the descriptors [Pipe.pipe2_spec]
    hands out: 3 the read end, 4 the write end, and the queue's mark at
    the two bytes a writer put there. -/
def pipe_queued_model : Model :=
  with_pipes [(0, ([97, 98], 2))]
    (mkModel [(0, FdEntry.FdChannel 0), (1, FdEntry.FdChannel 1), (2, FdEntry.FdChannel 2),
              (3, FdEntry.FdPipe 0 false), (4, FdEntry.FdPipe 0 true)]
       (mkVmMaps [] [] 0 0 demo_limit) IEof [])

/-! A pipe [read] one byte over [Uaccess.rw_bytes_max] is JUDGED, and
    delivers the whole queue: [State.pipe_take] takes the minimum
    against the queue, so the count never reaches a unary numeral and
    needs no ceiling.

    The second conjunct is the arm's determinism — a pipe read delivers
    [min count (length q)] and never less (fs/pipe.c [anon_pipe_read],
    v6.18.46: [if (ret) break] precedes the only wait), so a one-byte
    answer at this count is refused.  The first conjunct also reads the
    QUEUE back, and finds it empty rather than untouched: that is what
    says that passing the delivered length to [State.pipe_consume]
    consumes the same bytes the count would have
    ([State.pipe_consume_of_take]). -/
theorem pipe_read_over_rw_bytes_max_is_judged :
  (match check_syscall
          (SyscallInput.mkInput 63 [3, 4096, Z_to_bv 64 (rw_bytes_max + 1), 0, 0, 0]
             (fun _ => none) (wmem_first 2))
          (mkEffect 2 [(4096, [97, 98])] []) pipe_queued_model with
  | check_result.CheckOk m [] => m_pipes m = [(0, (([] : List byte), 2))]
  | _ => False
  )
  ∧ check_syscall
       (SyscallInput.mkInput 63 [3, 4096, Z_to_bv 64 (rw_bytes_max + 1), 0, 0, 0]
          (fun _ => none) (wmem_first 2))
       (mkEffect 1 [(4096, [97])] []) pipe_queued_model
     = check_result.CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ### The quantified lemmas of this file

    The worked examples above are closed computations over the checkers —
    which is what an example is for — and `rfl` closes every one of them.

    This section is the file's other layer: sixteen lemmas quantified over
    free variables, whose proofs are hand-written case analyses over the
    checkers' own `match` cascade (over `fd_lookup`, `eff`, `fs_lookup`,
    …), not closed reductions.

    Proved here, one lemma per declaration below:
    - `read_eof_is_sticky` (RESTATED — see its own note)
    - `file_write_emits_nothing`
    - `read_after_eof_deterministic`
    - `read_delivers_stream_prefix`
    - `file_read_clamped_len`
    - `pread64_leaves_the_model_alone`
    - `pread64_urandom_advances_the_stream`
    - `pread64_pipe_end_is_espipe`
    - `pwrite64_negative_pos_precedes_the_descriptor`
    - `pwrite64_copyin_clamped`

    `read_eof_is_sticky` is the one to read first: the sentence that is
    provable here is NOT the naive one, so the file proves the provable
    form (under `stream_sticky` plus the checker's position-0 test) and
    records the counterexample.  The declaration's own comment is the
    argument.

    Six more are marked `TODO` below, in the order they are declared, with
    what is missing and why: `read_delivery_clamped`,
    `read_ret_over_clamp_rejected`, `write_channel_outcome`,
    `writev_channel_outcome`, `writev_outcome_is_write_outcome` and
    `write_outcome_is_writev_outcome`.  Nothing in the tree depends on any
    of the sixteen, so those six cost the rest of the tree nothing.

    MEASURED (this is where `read_delivery_clamped` actually stands, so the
    next attempt does not re-derive it).  `check_read_complete_ok` followed
    by `simp only [check_read, check_ret_only, check_access_ok_zero,
    check_socket_pending_error] at Hc` and then the `split`/`dsimp` walk of
    this file's own idiom leaves **five** goals, all of them
    `↑bs.length ≤ MAX_RW_COUNT`, and all five are the REGULAR-FILE
    reflection leaves: the delivered list is pinned to
    `file_read data off (Z_to_bv 64 (rw_count_clamp count))` by TWO facts —
    the checker's `listN_eqb bs' (file_read …) = true` and the
    auto-generated equation `heq✝¹ : file_read … = head✝ :: tail✝` that the
    arm's non-emptiness test leaves in the context — while `heq✝` ties
    `bs` to `bs'`.  Every other leaf (channel 0, socket, pipe, urandom, the
    `zs`/`us` shapes, and the 31 constructor mismatches) closes by
    `simp at Hc` or by the chain's own `decide (↑bs.length ≤ rw_count_clamp
    count)` conjunct plus `rw_count_clamp_range`.  The blocker is purely
    NAMING: `heq✝¹` and `h✝` are auto-generated, their inaccessible names
    shift with the leaf, and `rename_i` therefore cannot reach them
    uniformly.  The two routes out are (a) `rename_i` against each leaf's
    full inaccessible list, or (b) a `file_read` length lemma stated so the
    bound survives forward rewriting — which is `file_read_clamped_len`
    already, so what is wanted is its `listN_eqb`-shaped bridge:
    `listN_eqb bs X = true → bs.length ≤ X.length` composed with it.

    These six are not missing for a reduction-cost reason: no `forallb` or
    `existsb` over a whole page appears in any of them, so no large closed
    computation is the obstruction.  The obstruction is that each proof is
    a bespoke forty-to-two-hundred-and-forty-five line case analysis over
    the checker, and the case analysis has to be done against the
    statements as they are written here rather than transliterated.

    HOW THE TEN PROVED HERE ARE DONE, since the shape is the same for
    the rest.  Each one starts by inverting the spec hypothesis with the
    checker's own completeness half (`check_write_complete_ok`,
    `check_pread64_complete_ok`, `check_pwrite64_complete_ok`, …), which
    turns `*_spec … (.ok eff m' evs)` into `check_* … = .CheckOk m' evs`.
    The checker is then unfolded ONCE at the known `fd_lookup` equation, and
    its `if`/`match` cascade is walked by `split` down to the leaves.  Every
    leaf is an equation of one of four shapes, and
    `check_ret_only_ok_iff` / `check_ret_only_copyins_ok_iff` invert the two
    accepted ones outright — they give the effect, the model and the events
    at once — while a `CheckUnmodeled` leaf is closed by contradiction and
    an `access_ok_zero` leaf by splitting its range verdict.  That is what
    the four helpers just below package up. -/
/-! #### Inverting an accepted leaf

    Four small inversions of `check_ret_only` / `check_ret_only_copyins` /
    `check_access_ok_zero` acceptances.  They are the local machinery of
    this file rather than statements about the model: the `check_*_ok_iff`
    lemmas of `Checks.Sys.Prelude` supply the same equations, and these
    exist so that a leaf of a `split` walk can be closed without naming the
    model or the event list it carries. -/

/-- An accepted `check_ret_only` delivers no event. -/
theorem evs_nil_of_check_ret_only {eff : SyscallEffect} {r : word} {m : Model}
    {m' : Model} {evs : List event} (h : check_ret_only eff r m [] = .CheckOk m' evs) :
    evs = [] :=
  ((check_ret_only_ok_iff eff r m [] m' evs).mp h).2.2

/-- The same for the copy-in-recording variant. -/
theorem evs_nil_of_check_ret_only_copyins {reads : List (word × Nat)}
    {eff : SyscallEffect} {r : word} {m : Model} {m' : Model} {evs : List event}
    (h : check_ret_only_copyins reads eff r m [] = .CheckOk m' evs) : evs = [] :=
  ((check_ret_only_copyins_ok_iff reads eff r m [] m' evs).mp h).2.2

/-- An accepted `check_ret_only` has exactly the claimed effect. -/
theorem effect_of_check_ret_only {eff : SyscallEffect} {r : word} {m : Model}
    {m' : Model} {evs : List event} (h : check_ret_only eff r m [] = .CheckOk m' evs) :
    eff = mkEffect r [] [] :=
  ((check_ret_only_ok_iff eff r m [] m' evs).mp h).1

/-- An accepted `check_ret_only_copyins` has exactly the claimed effect,
    copy-in ledger included. -/
theorem copyins_of_check_ret_only_copyins {reads : List (word × Nat)}
    {eff : SyscallEffect} {r : word} {m : Model} {m' : Model} {evs : List event}
    (h : check_ret_only_copyins reads eff r m [] = .CheckOk m' evs) :
    eff = with_copyins reads (mkEffect r [] []) :=
  ((check_ret_only_copyins_ok_iff reads eff r m [] m' evs).mp h).1

/-- An accepted `check_access_ok_zero` either passed the arm's own answer
    through or answered `-EFAULT`, so an arm-level inversion of the inner
    result inverts this too. -/
theorem evs_nil_of_access_ok_zero {buf count : word} {eff : SyscallEffect}
    {m : Model} {k : check_result} {m' : Model} {evs : List event}
    (h : check_access_ok_zero buf count eff m k = .CheckOk m' evs)
    (hk : ∀ {m'' : Model} {evs' : List event}, k = .CheckOk m'' evs' → evs' = []) :
    evs = [] := by
  unfold check_access_ok_zero at h
  by_cases hb : access_okb buf (count.toNat : Int) = true
  · rw [ite_eq_left hb] at h
    exact hk h
  · rw [ite_eq_right hb] at h
    exact evs_nil_of_check_ret_only h

/-- The `-EFAULT` leaf of a channel read: the range verdict, or a
    destination not even one byte of which is writable. -/
theorem read_eof_outcome_efault {eff : SyscallEffect} {m : Model} {m' : Model}
    {evs : List event}
    (h : check_ret_only eff (errno_ret EFAULT) m [] = .CheckOk m' evs) :
    (eff = mkEffect 0 [] [] ∨ eff = mkEffect (errno_ret EFAULT) [] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp h
  exact ⟨Or.inr heff, hm, hevs⟩

/-- The `0` leaf of a channel read at end of input: `count = 0`, or the
    stream is already ended.  Both are the same effect, and neither moves
    the model or emits. -/
theorem read_eof_outcome_zero {eff : SyscallEffect} {m : Model} {m' : Model}
    {evs : List event}
    (h : check_ret_only eff (BitVec.ofInt 64 0) m [] = .CheckOk m' evs) :
    (eff = mkEffect 0 [] [] ∨ eff = mkEffect (errno_ret EFAULT) [] []) ∧ m' = m ∧ evs = [] := by
  obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp h
  exact ⟨Or.inl heff, hm, hevs⟩

/-! #### `file_write_emits_nothing`

    Claim: a `write` to a file's write-half emits no event.  Formally,
    `write_spec` accepting with effect `eff` at a descriptor that
    `fd_lookup` sends to `FdFileW p off` yields `evs = []`.

    PROOF.  A `write` to a regular file
    moves bytes through `eff_writes`, never through the event list: every
    leaf of the `FdFileW` arm is a `check_ret_only` /
    `check_ret_only_copyins` (whose `evs` argument is `[]`), a
    `check_access_ok_zero` over one of those, or the arm's `unmodeled`
    decline. -/
theorem file_write_emits_nothing (fd buf count : word) (i : SyscallInput) (m : Model)
    (p : Fs.path) (off : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdFileW p off))
    (Hs : write_spec fd buf count i m (.ok eff m' evs)) : evs = [] := by
  have Hc := check_write_complete_ok i fd buf count eff m m' evs Hs
  simp only [check_write, hfd, check_access_ok_zero] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (first
    | (simp at Hc)
    | exact evs_nil_of_check_ret_only Hc
    | exact evs_nil_of_check_ret_only_copyins Hc
    | exact evs_nil_of_access_ok_zero Hc (fun hk => by simp at hk)
    | exact evs_nil_of_access_ok_zero Hc (fun hk => evs_nil_of_check_ret_only hk))

/-! #### `read_after_eof_deterministic`

    Claim: on channel 0 with an ended standard input there are only two
    possible accepted answers — a zero return or `-EFAULT` — and neither
    moves the model nor emits.

    PROOF.  On channel 0 with an ended stream the arm
    has only three leaves left — the range verdict (`-EFAULT`), the
    `count = 0` shortcut and the end-of-input branch — and every one of
    them is a `check_ret_only`, so each names its effect and leaves the
    model and the event list alone.  Substituting `m_stdin m = IEof` into
    the checker's `match` up front deletes the `some _` half of the
    cascade outright (the function encoding of `IEof` is `fun _ => none`),
    which is what makes the walk short. -/
theorem read_after_eof_deterministic (fd buf count : word) (i : SyscallInput) (m : Model)
    (ch : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdChannel ch))
    (hch : ch = 0)
    (heof : m_stdin m = IEof)
    (Hs : read_spec fd buf count i m (.ok eff m' evs)) :
    (eff = mkEffect 0 [] [] ∨ eff = mkEffect (errno_ret EFAULT) [] [])
      ∧ m' = m ∧ evs = [] := by
  subst hch
  have hw : (!(w_is0 (0 : word))) = false := by decide
  have Hc := check_read_complete_ok i fd buf count eff m m' evs Hs
  simp only [check_read, hfd, hw, Bool.false_eq_true, ite_false, heof, IEof] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (first
    | exact read_eof_outcome_efault Hc
    | exact read_eof_outcome_zero Hc)

/-- **`read_eof_is_sticky`, RESTATED.**

    The sentence proved here is NOT the naive one: an accepted zero return
    on channel 0 with a positive count does not by itself keep the stream
    ended.  The difference is the two hypotheses `hsticky` and `h0`:

    - `InputStream` is `Nat → Option byte` (`StateStreams`), so the
      checker's `match m_stdin m 0 with | none => …` tests POSITION 0
      only, and `m_stdin m 0 = none` does not imply that every later
      position is `none`.
    - A counterexample to the unguarded statement: `m_stdin m = fun n =>
      if n = 0 then none else some 0`, `count = 1`, a channel fd, and
      `eff = mkEffect 0 [] []`.  `check_read` takes the `none` branch,
      accepts and returns 0, yet `m_stdin m ≠ IEof`; `read_spec` accepts
      it by `check_read_sound_ok`, so the situation is reachable.
    - `hsticky` is the invariant `StateStreams` introduces for exactly
      this gap (`stream_sticky`, "an ended stream stays ended" — the
      hypothesis `stream_take_rest_self` already carries), and `h0` is
      what the checker's position-0 test hands over.  Together they give
      `m_stdin m = IEof` outright (`stream_sticky_eof`), which is the
      equation the statement needs.

    PROOF.  With `m_stdin m = IEof` in hand this is
    [read_after_eof_deterministic]: the channel-0 arm's only two leaves
    leave the model alone, so `m' = m` and the stream is unchanged.  The
    two further hypotheses — a positive count and a zero return — are
    part of the statement's shape and are not needed for the conclusion:
    at an ended stream EVERY channel-0 outcome is one of the two zero
    answers, which is what that lemma already concludes. -/
theorem read_eof_is_sticky (fd buf count : word) (i : SyscallInput) (m : Model)
    (ch : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdChannel ch))
    (hch : ch = 0)
    (_hcount : 0 < count.toNat)
    (hsticky : stream_sticky (m_stdin m))
    (h0 : m_stdin m 0 = none)
    (Hs : read_spec fd buf count i m (.ok eff m' evs))
    (_hret : eff.eff_ret = 0) :
    m_stdin m = IEof ∧ m_stdin m' = IEof := by
  have heof : m_stdin m = IEof := stream_sticky_eof hsticky h0
  obtain ⟨-, hm, -⟩ :=
    read_after_eof_deterministic fd buf count i m ch eff m' evs hfd hch heof Hs
  exact ⟨heof, by rw [hm]; exact heof⟩

/-! #### `read_delivers_stream_prefix`

    Claim: a `read` from channel 0 that records a write `[(a, bs)]` writes
    exactly the prefix `bs` of the stream, leaves the stream's remainder
    behind, and emits `ReadEv 0` per byte of `bs`.

    PROOF.  Destructing `eff` up front is what makes this one short: the
    claimed write pins `eff_writes` to `[(a, bs)]`, and every leaf of the
    channel arm whose effect is a `check_ret_only` has the EMPTY write
    list, so it is a constructor mismatch (or, once `spread` pins `eff` to
    the checker's own literal, a contradiction with the hypothesis).  That
    leaves the one accepted delivery leaf, where the delivered-prefix
    guard carries `listN_eqb (stream_take (m_stdin m) bs'.length).1 bs'`,
    and the `eff` equation identifies `bs'` with `bs`.  Both are
    `simp_all` facts. -/
theorem read_delivers_stream_prefix (fd buf count : word) (i : SyscallInput) (m : Model)
    (ch : word) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdChannel ch))
    (hch : ch = 0)
    (Hs : read_spec fd buf count i m (.ok eff m' evs))
    (a : word) (bs : List byte) (hw : eff_writes eff = [(a, bs)]) :
    (stream_take (m_stdin m) bs.length).1 = bs
      ∧ m_stdin m' = (stream_take (m_stdin m) bs.length).2
      ∧ evs = bs.map (event.ReadEv 0) := by
  subst hch
  obtain ⟨ret, ws, zs, us, cs, ci⟩ := eff
  have hws : ws = [(a, bs)] := hw
  subst hws
  have hw0 : (!(w_is0 (0 : word))) = false := by decide
  have Hc := check_read_complete_ok i fd buf count ⟨ret, [(a, bs)], zs, us, cs, ci⟩ m m' evs Hs
  simp only [check_read, check_ret_only, hfd, hw0, Bool.false_eq_true, ite_false] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (cases Hc <;> simp_all [Bool.and_eq_true, decide_eq_true_eq, listN_eqb_eq])

/-! #### `file_read_clamped_len`

    Claim: the delivered prefix from a regular file is at most
    `MAX_RW_COUNT` bytes long, whatever the requested count.

    PROOF.  `file_read` is `firstn`/`skipn` at the clamped count
    (`file_read_unguarded`), so its length is at most
    `word_to_nat (Z_to_bv 64 (rw_count_clamp count)) = rw_count_clamp count`
    (`rw_count_clamp_word`), which `rw_count_clamp_range` bounds by
    `MAX_RW_COUNT`.  The bridge is the `Nat`→`Int` cast on the take bound,
    so it is stated on `word_to_nat` in the goal's own spelling. -/
theorem file_read_clamped_len (data : List byte) (off count : word) :
    ((file_read data off (Z_to_bv 64 (rw_count_clamp count))).length : Int) ≤ MAX_RW_COUNT := by
  rw [Fs.file_read_unguarded]
  have hclamp : ((word_to_nat (Z_to_bv 64 (rw_count_clamp count)) : Nat) : Int)
      = rw_count_clamp count := by
    show ((BitVec.ofInt 64 (rw_count_clamp count)).toNat : Int) = rw_count_clamp count
    exact rw_count_clamp_word count
  have hle : ((List.take (word_to_nat (Z_to_bv 64 (rw_count_clamp count)))
      (List.drop (word_to_nat off) data)).length : Int)
      ≤ ((word_to_nat (Z_to_bv 64 (rw_count_clamp count)) : Nat) : Int) := by
    exact_mod_cast List.length_take_le (word_to_nat (Z_to_bv 64 (rw_count_clamp count)))
      (List.drop (word_to_nat off) data)
  have hr := rw_count_clamp_range count
  omega

/-! #### TODO — `read_delivery_clamped`

    Missing: an accepted `read` that records a write of `bs` bounds
    `bs.length` by `MAX_RW_COUNT`.

    Why it is not here: the proof is a case analysis over every
    `fd_lookup` arm (channel, three file kinds, directory, socket, pipe,
    urandom, the two device arms) and then over `eff`'s six fields.  The
    MEASURED paragraph in the section header records how far the current
    walk gets and why the blocker is naming rather than arithmetic. -/
/-! #### TODO — `read_ret_over_clamp_rejected`

    Missing: a `read` at `count = MAX_RW_COUNT + 1` on a regular file,
    whose range still passes the range test and whose clamp names a
    non-empty delivery, must be REJECTED when offered that delivery.

    Why it is not here: it needs a hand case analysis over `check_read` on
    a regular file (about forty lines) and a `bv_eqb`/`listN_eqb`
    decision that the statement's own hypothesis contradicts. -/
/-! #### TODO — `write_channel_outcome`

    Missing: at or below `rw_bytes_max`, a `write` to a pipe-end channel
    with non-empty readable source delivers a prefix: the bytes are
    bounded by `rw_bytes_max`, some `n` with `1 ≤ n ≤ bs.length` is
    copied in, the effect and the events are pinned, and the model is
    unchanged.

    Why it is not here: it needs a hand case analysis over `check_write`
    for the channel arm (about seventy lines), through `rw_range_in_range`,
    `write_source_of_rw`, `readable_bytes_full` and the deliverability
    `andb` chain. -/
/-! #### TODO — `writev_channel_outcome`

    Missing: the same claim as `write_channel_outcome`, for the vectored
    call, with the copy-in ledger carrying the iovec imports as well as
    the delivered prefix.

    Why it is not here: it is the largest write-side case analysis in this
    file's scope (about 245 lines) — the same walk as
    `write_channel_outcome`, but through `writev_gathered`,
    `gather_prefix_full` and `import_iovecs_accesses`. -/
/-! #### TODO — `writev_outcome_is_write_outcome`

    Missing: a corollary of `writev_channel_outcome` — a vectored write's
    outcome is also a single-buffer write's outcome, at the same `n`.

    Why it is not here: it re-drives the checker with the same condition
    chain (about 45 lines), so it is blocked on that lemma. -/
/-! #### TODO — `write_outcome_is_writev_outcome`

    Missing: the converse corollary — a single-buffer write's outcome is
    also a vectored write's outcome.

    Why it is not here: about 110 lines, and blocked on both
    `write_channel_outcome` and `writev_channel_outcome`. -/
/-! #### `pread64_leaves_the_model_alone`

    Claim: an accepted positional read moves neither `m_fds`, nor `m_fs`,
    nor `m_stdin`, and emits nothing.

    PROOF.  A positional read advances no descriptor offset, so no
    `pread64` arm moves anything this statement names: the errno and
    zero-length arms are `check_ret_only` (model unchanged), the two file
    arms accept with `.CheckOk m` — the SAME model — and the urandom arm
    moves only `m_urandom` (`with_urandom`).  `check_ret_only` is unfolded
    before the walk because its own `match` on `eff` is the one shape
    `split` will generalise over a variable rather than reduce; with it
    unfolded every leaf is either a constructor mismatch or an equation
    between two `.CheckOk`s, and `cases` settles both. -/
theorem pread64_leaves_the_model_alone (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hs : pread64_spec fd buf count pos i m (.ok eff m' evs)) :
    m_fds m' = m_fds m ∧ m_fs m' = m_fs m ∧ m_stdin m' = m_stdin m ∧ evs = [] := by
  have Hc := check_pread64_complete_ok i fd buf count pos eff m m' evs Hs
  simp only [check_pread64, check_read_urandom, check_ret_only] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (cases Hc)
  all_goals (first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | simp [with_fds, with_fs, with_stdin, with_urandom, with_pipes])

/-! #### `pread64_urandom_advances_the_stream`

    Claim: an accepted positional read on the urandom descriptor either
    leaves `m_urandom` alone or advances it to exactly the remainder of
    the clamped take.

    PROOF.  The urandom arm is the only one of `check_pread64` that moves
    `m_urandom`, and it moves it to exactly the remainder
    `(stream_take_z (m_urandom m) (rw_count_clamp count)).2`; on every
    other arm (`-EINVAL`, `-ESPIPE`, `-EBADF`, `-EFAULT`, the zero-length
    answer, and the fail-closed partial-destination decline) the model is
    untouched.  Both sides of the disjunction are therefore `rfl` after
    `cases` on the leaf, which is why the discharge names no arm. -/
theorem pread64_urandom_advances_the_stream (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (hfd : fd_lookup (m_fds m) fd = some FdEntry.FdUrandom)
    (Hs : pread64_spec fd buf count pos i m (.ok eff m' evs)) :
    m_urandom m' = m_urandom m
      ∨ m_urandom m' = (stream_take_z (m_urandom m) (rw_count_clamp count)).2 := by
  have Hc := check_pread64_complete_ok i fd buf count pos eff m m' evs Hs
  simp only [check_pread64, check_read_urandom, check_ret_only, hfd] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (cases Hc)
  all_goals (first
    | exact Or.inl rfl
    | exact Or.inr rfl)

/-! #### `pread64_pipe_end_is_espipe`

    Claim: a positional read on a pipe end with a non-negative position
    answers `-ESPIPE`, and nothing else.

    PROOF.  A non-negative position is not `ppos_einvalb`, so the position
    gate falls through to the `fd_lookup` dispatch, where `FdPipe` is one
    of the three kinds that answer `-ESPIPE` before the range verdict — the
    whole checker collapses to `check_ret_only eff (errno_ret ESPIPE) m []`,
    whose inversion names the effect. -/
theorem pread64_pipe_end_is_espipe (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (id : word) (w : Bool) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (hpos : (0 : Int) ≤ bv_signed pos)
    (hfd : fd_lookup (m_fds m) fd = some (FdEntry.FdPipe id w))
    (Hs : pread64_spec fd buf count pos i m (.ok eff m' evs)) :
    eff = mkEffect (errno_ret ESPIPE) [] [] := by
  have hpe : ppos_einvalb pos = false := by
    unfold ppos_einvalb
    rw [decide_eq_false_iff_not]
    have hpos' : (0 : Int) ≤ pos.toInt := hpos
    show ¬ (pos.toInt < 0)
    omega
  have Hc := check_pread64_complete_ok i fd buf count pos eff m m' evs Hs
  simp only [check_pread64, hpe, Bool.false_eq_true, ite_false, hfd] at Hc
  exact ((check_ret_only_ok_iff eff (errno_ret ESPIPE) m [] m' evs).mp Hc).1

/-! #### `pwrite64_negative_pos_precedes_the_descriptor`

    Claim: a positional write with a negative position answers `-EINVAL`,
    whatever the descriptor holds, and leaves the model and the event list
    alone.

    PROOF.  `ppos_einvalb pos` is `pos.toInt < 0`, so the negative position
    decides the FIRST `if` of `check_pwrite64` — it returns `-EINVAL`
    before `fd_lookup` is ever consulted, which is why the statement needs
    no descriptor hypothesis at all. -/
theorem pwrite64_negative_pos_precedes_the_descriptor (fd buf count pos : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (hpos : bv_signed pos < 0)
    (Hs : pwrite64_spec fd buf count pos i m (.ok eff m' evs)) :
    eff = mkEffect (errno_ret EINVAL) [] [] ∧ m' = m ∧ evs = [] := by
  have hpp : ppos_einvalb pos = true := by
    unfold ppos_einvalb
    exact decide_eq_true hpos
  have Hc := check_pwrite64_complete_ok i fd buf count pos eff m m' evs Hs
  simp only [check_pwrite64, hpp, ite_true] at Hc
  have h := (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp Hc
  exact ⟨h.1, h.2.1, h.2.2⟩

/-! #### `pwrite64_copyin_clamped`

    Claim: every copy-in an accepted positional write records is at most
    `MAX_RW_COUNT` bytes.

    PROOF.  Every `pwrite64` arm that records a copy-in records exactly
    `[(buf, bs.length)]`, where `bs` is `write_source … buf count` — the
    source prefix, which `write_source_length_le` bounds by
    `rw_count_clamp count` and `rw_count_clamp_range` by `MAX_RW_COUNT`.
    The arms that answer through `check_ret_only` leave `eff_copyins`
    empty and so cannot satisfy the hypothesis at all. -/
theorem pwrite64_copyin_clamped (fd buf count pos : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (a : word) (n : Nat)
    (Hs : pwrite64_spec fd buf count pos i m (.ok eff m' evs))
    (hci : eff_copyins eff = [(a, n)]) :
    (n : Int) ≤ MAX_RW_COUNT := by
  have Hc := check_pwrite64_complete_ok i fd buf count pos eff m m' evs Hs
  simp only [check_pwrite64] at Hc
  repeat' (first | (split at Hc) | (dsimp only at Hc))
  all_goals (first
    | (simp at Hc)
    | (have heff := copyins_of_check_ret_only_copyins Hc
       have hci' : ([(buf, (write_source i.in_mem buf count).length)] : List (word × Nat))
           = [(a, n)] := by
         rw [heff] at hci
         exact hci
       have hpair : (buf, (write_source i.in_mem buf count).length) = (a, n) := by
         simpa using hci'
       have hn : n = (write_source i.in_mem buf count).length :=
         (congrArg Prod.snd hpair).symm
       rw [hn]
       have h1 := write_source_length_le i.in_mem buf count
       have h2 := (rw_count_clamp_range count).2
       omega)
    | (have heff := effect_of_check_ret_only Hc
       rw [heff] at hci
       simp [mkEffect] at hci))

end LinuxSem.Checks.Cases.Fs.ReadWrite
