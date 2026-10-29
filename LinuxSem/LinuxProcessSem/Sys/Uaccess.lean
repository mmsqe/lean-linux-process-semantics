/-
  * LinuxProcessSem.Sys.Uaccess — the user-buffer boundary

  Every other file under `Sys/` answers to one kernel SOURCE file; this
  one answers to kernel HEADERS, and holds what the specs share rather
  than any one syscall's behaviour.  The predicate it transcribes is
  `__access_ok` and the generic `access_ok` wrapping it
  (include/asm-generic/access_ok.h, `__access_ok` and the `#ifndef
  access_ok` fallback, at stable v6.18.46 / 1f99e9ab748f), which is the
  file `State.access_okb`'s note cites for the same predicate.
  include/linux/uaccess.h defines NEITHER of them — it pulls the arch
  header in and only USES `access_ok`, in `copy_{to,from}_user` and in
  the fallback `#define user_access_begin(ptr,len) access_ok(ptr, len)`
  — so it is named here for the copy helpers, not for the range test.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions every
  spec here follows.

-/
import LinuxSem.LinuxProcessSem.StateMemory
import LinuxSem.LinuxProcessSem.MonadInstances

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem.Sys.Uaccess

/-! ## The `Sys/Syscall.lean` shims

  see the note).

      Definition ret_only (r : word) : Sys SyscallEffect := pure (mkEffect r [] []).
      Definition err_ret (e : Z) : Sys SyscallEffect := ret_only (errno_ret e).
-/

/-- Return `r` with no memory writes. -/
def ret_only (r : word) : SysSpec SyscallEffect := pure (mkEffect r [] [])

/-- Fail with errno `e` (a0 = -e). -/
def err_ret (e : Int) : SysSpec SyscallEffect := ret_only (errno_ret e)

/-! ## The transfer-size bound -/

/-- WHAT THIS CONSTANT BOUNDS: the hole a write or a growing `ftruncate` may open past
    end-of-file (`ReadWrite.modeled_file_gap`,
    `Open.modeled_truncate_gap`), the buffer a `getrandom` may name, and
    the total a socket send may gather.  IT DOES NOT CAP A TRANSFER'S
    COUNT in either direction.  A read's recursion is capped by the file
    or the stream it reads from, and `State.readable_bytes` spends
    neither stack depth nor a length-sized unary numeral on the count a
    write names.  A READ's count faces the kernel's own two tests and
    nothing else — `State.access_okb` on the range, then the
    `MAX_RW_COUNT` clamp (`State.rw_count_clamp`).  A WRITE's faces
    `modeled_rw_range` below, which is this constant OR that same range
    test, and then the same clamp.

    THE HOLE IS NOT THE COUNT, and that is why this constant bounds the
    one and not the other.  A hole is the distance from the file's end to the
    write's offset — bytes the model has to BUILD because it holds a
    file as a flat byte list, where Linux leaves a sparse file's hole
    costing nothing.  No per-call count bounds it: a one-byte write at a
    far offset opens an arbitrarily large one.  A COUNT, by contrast,
    costs the model a chunk-count numeral 4096 times smaller than
    itself and a list bounded by what is actually mapped.

    THIS IS A MODELING BOUND, NOT A KERNEL ONE, and it is here because
    the alternative is a crash.  Linux settles a huge scalar count in
    three cheap steps and then does the transfer.  In `vfs_read` and
    `vfs_write` (fs/read_write.c at v6.18.46), after the `FMODE_*`
    tests and in this order:

    - `if (unlikely(!access_ok(buf, count))) return -EFAULT;`;
    - `rw_verify_area`, whose first statement is
      `if (unlikely((ssize_t) count < 0)) return -EINVAL;`;
    - `if (count > MAX_RW_COUNT) count = MAX_RW_COUNT;`, with
      `#define MAX_RW_COUNT (INT_MAX & PAGE_MASK)` — 0x7ffff000 — in
      include/linux/fs.h.

    The first is `State.access_okb` and the third is
    `State.rw_count_clamp`, and both are what the read AND write
    arms apply; none of the three bounds what the model can EVALUATE,
    which is what this constant is for on the paths it guards.
    THE ORDER MATTERS for
    one errno.  `access_ok` runs first, and on riscv64 it is the generic
    `__access_ok` with its limit at `State.TASK_SIZE` = 2^47, so a
    `count` that is negative as `ssize_t` — at least 2^63 — has already
    been answered -EFAULT before `rw_verify_area`'s sign test is reached:
    on a kernel with an MMU the -EINVAL is UNREACHABLE through the
    read/write syscalls, and modeling the sign test would put -EINVAL
    where Linux returns -EFAULT.  The MMU is doing the work in that
    argument, so state it: `__access_ok` returns true without looking at
    either operand when CONFIG_ALTERNATE_USER_ADDRESS_SPACE is set or
    CONFIG_MMU is not, and a nommu riscv64 kernel reaches that same
    generic `__access_ok` through asm-generic/uaccess.h.  On such a
    kernel -EINVAL is what a negative `count` gets.  This model has
    `mmap` and page permissions and so describes MMU kernels only.

    So above the bound the model declines on the paths it guards;
    it does not invent an errno, and it does not clamp — a clamp would
    have it report a short transfer where Linux transferred everything.

    2^17 IS SET FROM BELOW BY A PROOF, NOT BY A PROGRAM, and the
    distinction matters because it is the difference between "no slack
    exists" and "no slack exists as currently written".  What that proof
    constrains is the WRITE-NODE FAMILY in `Common/` rather than
    the spec: `CatSim.buf_modeled` is stated at this constant and
    is what those lemmas hand `write_source_of_rw` to see the walk they
    were written against.  That is a library convenience, not a bound
    the spec has — a write past it is judged, it just has no ready-made
    node in that family.

    The chain is: a single argv string may be 131071 bytes
    (`Run.valid_argv`, from Linux's MAX_ARG_STRLEN of 32 pages less its
    NUL), and `Examples.brk_rev_ns` writes argv[1] reversed followed by a
    newline.  `brk_rev_ns_source.bufs_modeled_out` discharges
    `buf_modeled` for that write from `nN_le` — the 131071 cap — giving
    131071 + 1 = 131072, the constant on the nose.  Lower the bound by
    one and that lemma's `lia` fails, the write is `unmodeled`, and since
    `unmodeled` puts a run in `Run.reaches_error` the example's
    equivalence theorem stops being provable rather than merely weakening.
    So the constant cannot be lowered without touching that proof.

    WHAT IS NOT TRUE is that the program can perform such a write.  It
    cannot: `brk_rev_ns`'s own source and target both return 3 for an
    argument longer than 65536 bytes (source/program.c and
    target/program.zig, the `n > 65536` guard), so the largest write it
    can ever execute is 65537 bytes.  `bufs_modeled_out` sits in a
    section where only `2 <= length av` is in scope and the program's own
    cap is not, so it reaches for the argv bound instead of the tighter
    one that is actually available; `alloc_join_ns_source` does the
    tighter thing for its own buffer.  Threading the 65536 guard into the
    section would let the constant go as low as 65537.  That is a real
    option, deliberately not taken here: 2^17 is a rounder number to
    explain and nothing needs the room, but the reason to keep it is
    convenience, and it should not be recorded as a program requirement
    it is not.

    FROM ABOVE the constraint is real but soft, and NO SINGLE NUMBER
    SHOULD BE QUOTED FOR IT.  The mechanism: `BvBase.word_to_nat` is
    `Z.to_nat`, and Checks/Extraction.v imports ExtrOcamlZBigInt but not
    ExtrOcamlNatInt, so `nat` stays genuine unary Peano and `Z.to_nat`
    bottoms out in `Pos.to_nat = iter_op add`.  `iter_op`'s doubling keeps
    the NUMBER of additions logarithmic, but Peano `add` is `S (add p m)`,
    not tail-recursive, so the largest intermediate addition costs stack
    depth proportional to the length.  The places below consult that
    length, all but the last of them by recursing with it, and every one
    of them before a single memory lookup, so what a caller sees when
    one of them goes over is `Stack overflow` and exit 2 — or, on an
    OCaml 4 native build, a bare SIGSEGV — a status no verdict maps to.
    THEY DO NOT ALL GO OVER AT THE SAME DEPTH, so do not read them as
    one number.  Measured on OCaml 5, at the same argument,
    `word_to_nat` costs a thousandth of what `State.readable_bytes` costs.
    The others are not measured.  The list, and which of them this
    constant stands in front of:

    - `State.readable_bytes`, for a `write`, and `gather_prefix`, which
      calls it, for a `writev`.  THIS CONSTANT STANDS IN FRONT OF
      NEITHER: both use the chunked tail-recursive walk described on
      `State.wmem_chunk`.  What a write converts to a unary numeral is the
      CHUNK COUNT, `count` over 4096; what it pays is a list as
      long as the mapped prefix it actually reads, which is bounded by
      the process's memory rather than by the call;
    - `Fs.file_write`'s `repeat` and `firstn`, for a write to a file.
      Only the `repeat` is sized by the HOLE, which is what
      `ReadWrite.modeled_file_gap` bounds.  The `firstn` is sized by the ABSOLUTE
      offset, so this bound does not bound it and cannot: it is capped
      by the file's own length, and a file's length is the cost this
      constant explicitly does not cover (see the last paragraph).  An append to a long file pays it
      with a gap of zero;
    - `Fs.file_truncate`'s `repeat` and `firstn`, for an `ftruncate`.
      Both are sized by the NEW LENGTH, and both are built from the one
      numeral `word_to_nat len`, which `Open.modeled_truncate_gap` bounds by
      the file's length plus this constant — one-sidedly, so in both
      directions.  That is the SAME exposure as `file_write` above, not
      a better one: the file's own length is still uncovered, so a
      shrink of a long file builds a numeral the size of that file with
      the gap negative;
    - `State.read_bytes_map` over `buflen`, for a `getrandom` — which
      is why `Random.getrandom_spec` carries this same guard.  THIS ONE
      DOES NOT RECURSE WITH THE LENGTH: it is the
      chunked tail-recursive accumulator described on
      `State.wmem_chunk`, so its depth does not scale with `buflen`
      and the largest numeral it builds is the CHUNK COUNT, `buflen` over
      4096 rather than `buflen`; what it pays is a list that long.
      The guard stays because that cost is real, and because the same
      number of bytes should be the same transfer whichever call names
      it — not because this path would crash.

    A `read` IS ON NEITHER SIDE OF THAT LIST: `Fs.file_read`'s numeral is
    `word_to_nat_bounded count (length rest)` — capped at what is left
    of the file BEFORE the conversion, the cap-and-prove-equal
    technique described below — so a file read is charged for the file
    it holds (the cost this constant explicitly does not cover, see
    the last paragraph) and never for the `count` it names.  The
    OFFSET does not cross into `nat` at all: `Fs.file_from` walks the
    file in `Z` and in tail position.  A channel read consumes `count`
    only through `Z` comparisons (`Syscall.w_is0`, and the
    `length bs <= ...` side condition), and the prefix it delivers is
    bounded by the input stream.  The follow-on walks of a delivering
    read (`State.read_bytes_map` and `delivered_writes` over the
    DELIVERED bytes, the checker's `wmem_ok`) are all sized by that
    same file- or stream-bounded delivery.  That is why the file,
    channel and directory read arms of `ReadWrite.read_spec` are not
    guarded here: their guard is `State.access_okb` and nothing else,
    with Linux's own `MAX_RW_COUNT` clamp (`State.rw_count_clamp`)
    bounding what a delivery may claim.

    THE PIPE AND SOCKET READ ARMS DO NOT RECURSE ON `count` EITHER.
    `State.pipe_take` takes the minimum of `count` and the queue's own
    length in `Z` before it builds a numeral — a pipe delivers at most
    PIPE_BUF bytes whatever the count — and `State.net_take_z` walks in
    `positive`.  Both arms carry `modeled_rw_range`, for the RANGE and
    not for the size.

    How deep the recursion may go before it dies is a property of the
    OCAML MAJOR VERSION, and so of whichever runtime builds the checker,
    rather than of this development.

    BOTH DIRECTIONS WALK IN CHUNKS, and what the ceiling costs is a
    LIST rather than a stack.  `readable_bytes` is
    `State.readable_bytes_chunks` over `State.readable_bytes_acc`: the
    inner walk extends a reversed accumulator through a tail call, the
    outer loop hands out at most `State.wmem_chunk` bytes of fuel at a
    time, and one `rev_append` restores byte order.
    `State.readable_bytes_eq` is the equation proofs go through, in the
    shape `State.read_bytes_map_eq` set on the read side.  The write
    side therefore has the shape of the read side's
    `State.read_bytes_map`, and that is why the write and writev arms
    need no count gate.

    WHAT THAT LEAVES, precisely.  The stack depth scales with `count` on
    neither direction, and the largest unary numeral either builds is
    the CHUNK COUNT, `count` over 4096.  What a transfer still pays per
    byte is its OUTPUT LIST — one cons per mapped byte it actually reads
    — which is bounded by the process's memory rather than by the call,
    and which is the cost this constant explicitly does not cover (see
    the last paragraph).

    ONE PREREQUISITE IS NOT MET.  Nothing in this repository sets
    `OCAMLRUNPARAM` for the extracted checker, so the minor heap and
    the stack ceiling are whatever the invoking shell leaves them.
    That is not a semantic question.

    The measurements are properties of the toolchain rather than of
    this specification, and this comment does not give them.

    REAL PROGRAMS MAKE WRITES PAST THIS CONSTANT, AND THE MODEL JUDGES
    THEM.  A single `write` in sbase's `paste` is an order of magnitude
    past it.  No arm asks about a
    transfer's SIZE at all.  What the transfer arms that gate a
    range carry is `modeled_rw_range`, which admits any count at a
    buffer inside the address space, and every other transfer arm asks
    `access_ok` and nothing else.  So the paragraph ABOVE about
    `brk_rev_ns` — that no modeled example performs such a write — is a
    statement about the examples in this tree and not about programs,
    and what stands between that program and a run is COST rather than a
    modeled decline.  Priority 1 is not at stake, since a decline is
    explicit and fails closed; priority 3 is not at stake for the
    count.  What this constant declines is the past-end-of-file
    HOLE, `getrandom`'s buffer and the socket sends.
    THE PROOF SIDE HAS THE ROOM: nothing in this tree bounds the
    constant from above (`State.access_okb` is a range test and walks
    nothing), so a
    raise meets only the proofs that assume a count under it, the
    `Hcnt`-shaped hypotheses in `Common/`.  So the numeral is the cheap
    half, and moving it alone is the misleading move: it would widen what
    the spec admits while leaving the `OCAMLRUNPARAM` prerequisite unmet.

    WHY A SEMANTIC BOUND AND NOT A REPRESENTATION FIX.  The cheaper
    technique is to CAP the numeral and prove the capped definition equal
    to the uncapped one, which narrows nothing and adds no premise.  This
    file uses it where it applies — `Fs.file_from` and
    `Fs.file_read_unguarded` are exactly that.  It does not apply to
    `State.readable_bytes`, for a reason worth stating so nobody retries
    it: the technique spends a bound you already have, and here there is
    none.  `readable_bytes` walks `mp : word -> option byte`, a bare
    function; the cap it would need is the length of the mapped run at
    the address, which is not definable from a function with no
    computable support.  `Fs.file_read` was capped by `length data`
    because its output was already bounded by a byte list the model
    holds — whereas `readable_bytes`'s numeral bounds its OWN output,
    which is `count` bytes long precisely when the bytes are mapped.

    And the obstruction survives the obvious repair.  Even if memory were
    re-represented as a finite interval structure, the smallest run the
    model structurally guarantees is the 8 MiB zero-mapped stack every
    run has (`Run.init_machine_state`), and an anonymous grant may be
    `State.target_alloc_limit` — 512 GiB.  A correct cap is not a small
    cap: 8 MiB is 64x this constant and was already past the depth the
    extraction was measured to die at.

    WHICH IS WHY THE WALK USES NEITHER OF THESE.  Capping
    cannot bound `readable_bytes`'s walk and re-representing memory
    cannot either, so the walk's SHAPE does the work instead —
    chunked and tail-recursive, as the ceiling paragraphs above describe
    — and that needs no bound at all.  The argument of the two
    paragraphs before this one holds of anything that
    would try to CAP a walk over a bare `mp`; the write direction does
    not need a semantic size bound.

    COST TO THE THEOREM: a source and a target that diverge only on a
    write or a growing `ftruncate` opening a larger hole past
    end-of-file than `rw_bytes_max`, or on a `getrandom` or a socket
    send naming more than it, are not distinguished by
    `Equivalence.strong_universal_T`.  A write naming more than
    `rw_bytes_max` BYTES is not on that list.  The narrowing is one-sided, so it
    admits nothing unsound: a TARGET that performs such a call reaches
    `Run.reaches_error` and is rejected outright.

    NOT covered here, and deliberately: the cost of every path below
    still scales with the length of the file the model is holding, since
    that file IS a byte list — `Fs.file_write` walks it on every write —
    and a run GROWS that file itself, a chain of writes each opening a
    legal hole reaching any length.  So this is not only about
    `Fs.valid_fs`'s initial images, and bounding those would not close it;
    bounding it at all changes what the theorem quantifies over rather
    than what a syscall admits.

    THE BOUND THEREFORE DOES NOT CLOSE ITS OWN CLASS, and that should be
    read as a limit rather than as a claim.  It bounds ONE syscall, and
    the quantity that drives the recursion is reachable by ITERATION: a
    loop of `lseek(fd, off += rw_bytes_max, SEEK_SET); write(fd, b, 1)`
    performs only writes this spec judges — each names one byte and opens
    a hole of exactly `rw_bytes_max`, so `modeled_rw_range` and
    `ReadWrite.modeled_file_gap` both hold at every step — yet after 2048 turns the
    file is 2^28 bytes long, which is the depth the extraction is
    measured to die at.  Nothing here rejects that run; each step is a
    legal transfer, and it is the accumulated LENGTH, which no per-call
    guard sees, that does the damage.  What this constant buys is that a
    SINGLE syscall cannot do it — the crash costs a program 2048 calls
    instead of one, and is not reachable by accident.  Closing the
    class needs a bound on the state, not on the call, and that is the
    change to what the theorem quantifies over described above. -/
def rw_bytes_max : Int := 131072

/-- `count` is a transfer size the model will judge.  This is the gate
    `getrandom` and the socket sends carry, and the shape the hole
    guards are written in.  NO ARM OF `ReadWrite` USES IT.
    Every arm that gates a count uses `modeled_rw_range` below —
    every judging arm of `ReadWrite.write_spec`, named at
    `modeled_rw_range`, and `ReadWrite.read_spec`'s
    socket and pipe arms — and every other read
    and write arm carries no count gate at all (see `rw_bytes_max`). -/
def modeled_rw_count (count : word) : Bool :=
  decide ((count.toNat : Int) ≤ rw_bytes_max)

/-- THE GATE FOR AN ARM THAT HAS NOT ALREADY DECIDED THE RANGE, and the
    whole of the write-side bound.

    Above `rw_bytes_max` the model asks LINUX'S OWN QUESTION about the
    range — `State.access_okb`, i.e. `buf + count <= State.TASK_SIZE` —
    and declines when the answer is no.  Three things are worth being
    explicit about.

    THE ARMS THAT CARRY IT, BY NAME: `ReadWrite.write_spec`'s channel,
    plain-file, read-write-file, append and pipe arms, and its /dev/null
    arm (`State.FdDevNull`, through `ReadWrite.write_range_gate`); and
    `ReadWrite.read_spec`'s SOCKET and PIPE arms.

    THE RULE IS ABOUT ORDER, NOT ABOUT WHETHER AN ARM HAS AN -EFAULT.
    Every arm named above except `write_spec`'s APPEND and /dev/null
    arms asks `access_ok` nowhere at all.  Those arms do ask it — and
    keep this gate AHEAD of it, so the gate still decides.  What makes an
    arm need none is asking `access_ok` FIRST: `read_spec`'s /dev/null,
    channel, file and directory arms do, all of `pread64` does, and so does `pwrite64`'s one judging
    arm, where `rw_range_of_access_ok` below is the proof that this gate
    would then be constantly true.

    THE TWO ORDERS ANSWER THE SAME SHAPE DIFFERENTLY, and both answers
    are admissible.  A count above `rw_bytes_max` at a buffer whose
    range leaves the address space is `unmodeled` through `write` on an
    append fd — the gate is reached first — and -EFAULT through
    `pwrite64` on a write-only fd, which is Linux's answer.  A decline
    is never wrong, so this is a difference in how much the model
    judges, not in what it judges.  Aligning them means either moving
    the append arm's `access_ok` above its gate, which is a widening,
    or putting a gate on `pwrite64`,
    which would be dead code; neither is folded in here.

    The read arms that carry it read it exactly as the write arms do,
    and the paragraphs below apply unchanged to both.

    WHY `rw_bytes_max` IS THE FIRST DISJUNCT.  Below it the
    gate is `modeled_rw_count`, so a proof that discharges
    `modeled_rw_count` discharges this gate with no new fact.  That is not only convenience: the model does NOT have
    an -EFAULT arm for an out-of-range scalar write, and adding one
    would make every write's judgement depend on a stack-layout fact the
    model does not carry — that the initial argv/envp block lies under
    `State.TASK_SIZE` (`StackLayout`'s `sp` bound is `sp_window_hi`,
    which is `TASK_SIZE` itself, so a buffer in that block cannot be
    shown in range).  That gap is a known limitation, and this
    definition deliberately neither widens nor closes it.

    WHY `access_ok` IS THE RIGHT SECOND DISJUNCT.  It is what bounds the
    walk: `State.readable_bytes` steps `a + 1` in the 64-bit word, so a
    range that runs past the top of the address space wraps, and the
    prefix it would then read is not a prefix of anything Linux would
    copy.  Under `access_ok` the walk stays inside the user address
    space, where the bytes it finds are the bytes `copy_from_user`
    would move.

    WHAT IS DECLINED, then, is a transfer above `rw_bytes_max` whose
    range leaves the user address space — where Linux answers -EFAULT
    and this model says `unmodeled` instead.  Fail-closed: every count
    is admitted at an
    in-range buffer, up to and past the kernel's own `MAX_RW_COUNT`
    clamp (`State.rw_count_clamp`, applied by `write_source`).

    writev and readv need no analogue: `State.import_iovecs` already
    applies `access_ok` to every descriptor's uncapped length, so a
    vectored transfer is range-checked before a byte moves. -/
def modeled_rw_range (buf count : word) : Bool :=
  modeled_rw_count count || access_okb buf (count.toNat : Int)

/-- `State.access_okb` over a word-sized count, in the two directions a
    proof needs.  Both halves of `__access_ok` follow from the single
    inequality `buf + count <= TASK_SIZE`, because both operands are
    non-negative — so a proof holding a link-time buffer and a small
    count discharges the guard with one `lia`, and a proof holding the
    guard gets the exact end back. -/
theorem access_okb_intro (buf count : word)
    (h : (buf.toNat : Int) + (count.toNat : Int) ≤ TASK_SIZE) :
    access_okb buf (count.toNat : Int) = true := by
  unfold access_okb
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor <;> omega

theorem access_okb_le (buf count : word)
    (h : access_okb buf (count.toNat : Int) = true) :
    (buf.toNat : Int) + (count.toNat : Int) ≤ TASK_SIZE := by
  unfold access_okb at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  omega

/-- `access_ok_zero buf count k`: what an arm answers once the kernel
    has decided to move NO bytes — `k` is that arm's zero answer.

    Linux checks the buffer range in `vfs_read` / `vfs_write` before it
    dispatches on the fd (fs/read_write.c at v6.18.46: `FMODE_READ` or
    `FMODE_WRITE`, then `FMODE_CAN_*`, then `access_ok(buf, count)`,
    then `rw_verify_area`), and `import_ubuf` (lib/iov_iter.c at v6.18.46) does the
    same for `getrandom`, `sendto` and `recvfrom`, so the check runs on
    a zero-length transfer exactly as on any other.  Without this
    guard an arm would answer 0 where Linux answers -EFAULT.

    TWO ANSWERS AND NO THIRD.  `State.access_okb` is the kernel's own
    predicate at v6.18.46, with its limit the one `TASK_SIZE`
    the Sv48 premise fixes, so there is no range the model cannot
    decide and no `unmodeled` arm here.  Note that -EFAULT is the RANGE
    verdict, not a copy fault: a range the kernel accepts but has
    nothing mapped at still returns the arm's zero answer, because no
    byte is copied. -/
def access_ok_zero (buf count : word) (k : SysSpec SyscallEffect) :
    SysSpec SyscallEffect :=
  if access_okb buf (count.toNat : Int) then k else err_ret EFAULT

/-! ## Discharging the guards

  Discharge the guards.  Stated in the `negb … = false` form the guards
  are written in, so a proof that has the inequality in hand rewrites once
  and reduces. -/

theorem rw_count_in_range (count : word)
    (h : (count.toNat : Int) ≤ rw_bytes_max) :
    !modeled_rw_count count = false := by
  unfold modeled_rw_count
  rw [decide_eq_true h]
  rfl

/-- The scalar-write gate under `rw_bytes_max`: its first disjunct, so a
    proof that discharges `modeled_rw_count` discharges this too. -/
theorem rw_range_in_range (buf count : word)
    (h : (count.toNat : Int) ≤ rw_bytes_max) :
    !modeled_rw_range buf count = false := by
  unfold modeled_rw_range modeled_rw_count
  rw [decide_eq_true h]
  rfl

/-- ... and above it, the range test is what admits the transfer. -/
theorem rw_range_of_access_ok (buf count : word)
    (h : access_okb buf (count.toNat : Int) = true) :
    !modeled_rw_range buf count = false := by
  unfold modeled_rw_range
  rw [h, Bool.or_true]
  rfl

/-- The write-side bound sits far inside the `MAX_RW_COUNT` clamp, so a
    count a write judges is one the clamp leaves alone. -/
theorem rw_count_clamp_of_rw (count : word)
    (h : (count.toNat : Int) ≤ rw_bytes_max) :
    rw_count_clamp count = (count.toNat : Int) := by
  apply rw_count_clamp_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

/-! ## The source prefix a write may move -/

/-- THE SOURCE PREFIX A WRITE MAY MOVE, stated once for the spec, the
    acceptor and the progress witness so that no arm can clamp on one
    side and not on the other — the shape `State.writev_gathered` gives
    the vectored direction.

    Linux clamps a scalar transfer at `MAX_RW_COUNT` before it reaches
    the write operation (`State.rw_count_clamp`; `vfs_write` applies it
    after `rw_verify_area`, fs/read_write.c at v6.18.46), so the bytes a
    `write` can copy out of the user buffer are the readable prefix of
    the CLAMPED range, never of the count the call named.  Below 2^31 the
    clamp is a no-op and this is exactly `State.readable_bytes` at the
    named count. -/
def write_source (mp : word → Option byte) (buf count : word) : List byte :=
  readable_bytes mp buf (BitVec.ofInt 64 (rw_count_clamp count))

/-- `BitVec.ofInt 64` round-trips a `word`'s unsigned value —
    `Z_to_bv_bv_unsigned`, which `write_source_small` rewrites with. -/
private theorem ofInt_toNat (w : word) : BitVec.ofInt 64 (w.toNat : Int) = w := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt]
  · simp
  · exact Int.natCast_nonneg _
  · have := w.isLt
    omega

theorem write_source_length_le (mp : word → Option byte) (buf count : word) :
    ((write_source mp buf count).length : Int) ≤ rw_count_clamp count := by
  have hbounded :=
    readable_bytes_length_le mp buf (BitVec.ofInt 64 (rw_count_clamp count))
  have hw : word_to_nat (BitVec.ofInt 64 (rw_count_clamp count))
      = (rw_count_clamp count).toNat := by
    have h : ((BitVec.ofInt 64 (rw_count_clamp count)).toNat : Int)
        = ((rw_count_clamp count).toNat : Int) := by
      rw [rw_count_clamp_word count, Int.toNat_of_nonneg (rw_count_clamp_range count).1]
    exact Int.ofNat_inj.mp h
  unfold write_source
  rw [hw] at hbounded
  have hle : ((readable_bytes mp buf (BitVec.ofInt 64 (rw_count_clamp count))).length : Int)
      ≤ ((rw_count_clamp count).toNat : Int) := by exact_mod_cast hbounded
  rwa [Int.toNat_of_nonneg (rw_count_clamp_range count).1] at hle

/-- Below the clamp it IS the walk at the named count, which is what a
    proof holding a concrete count needs. -/
theorem write_source_small (mp : word → Option byte) (buf count : word)
    (h : (count.toNat : Int) ≤ MAX_RW_COUNT) :
    write_source mp buf count = readable_bytes mp buf count := by
  unfold write_source
  rw [rw_count_clamp_small count h, ofInt_toNat]

/-- And `rw_bytes_max` sits far inside the clamp, so a proof
    that already holds `count <= rw_bytes_max` sees the same walk. -/
theorem write_source_of_rw (mp : word → Option byte) (buf count : word)
    (h : (count.toNat : Int) ≤ rw_bytes_max) :
    write_source mp buf count = readable_bytes mp buf count := by
  apply write_source_small
  unfold rw_bytes_max at h
  unfold MAX_RW_COUNT
  omega

/-! ## The delivered-writes shape -/

/-- The effect write list for `bs` delivered bytes at `buf`: no entry
    when no byte moves.  This is the CANONICAL zero-byte shape — a read
    that delivers nothing (file at end-of-file, `count = 0`) has effect
    `mkEffect 0 [] []` on every fd kind, the same shape as a zero-byte
    channel read, rather than a vacuous `(buf, [])` entry. -/
def delivered_writes (buf : word) (bs : List byte) : List (word × List byte) :=
  match bs with
  | [] => []
  | _ :: _ => [(buf, bs)]

/-! ## Sanity checks

  `sanityMem` is the tiny memory image from `StateMemory`: the bytes of the list at
  addresses `0`, `1`, … and nothing anywhere else. -/

/-- Under `rw_bytes_max` the scalar gate admits the count... -/
example : modeled_rw_count (131072 : word) = true := by decide

/-- ...and one byte past it does not. -/
example : modeled_rw_count (131073 : word) = false := by decide

/-- A refused `access_ok` range: a buffer just under `TASK_SIZE` with a
    count that runs past it is out of range, so `modeled_rw_range` — with
    an over-bound count, hence no first disjunct — declines it. -/
example : access_okb 0x7fffffffffff (131073 : Int) = false := by decide
example : modeled_rw_range 0x7fffffffffff 131073 = false := by decide

/-- The same over-bound range INSIDE the address space is admitted: the
    gate is the range, not the size. -/
example : modeled_rw_range 0 131073 = true := by decide

/-- A count at the bound is admitted by the first disjunct at any buffer,
    in range or not. -/
example : modeled_rw_range 0x7fffffffffff 131072 = true := by decide

/-- A successful `copy_from_user`-side read: the source prefix a write
    moves out of a mapped buffer is the bytes that are there. -/
example : write_source (sanityMem [1, 2, 3]) 0 2 = [1, 2] := by decide

/-- ...and a FAILED one: with nothing mapped at the buffer no byte moves,
    whatever the count. -/
example : write_source (sanityMem []) 0 4 = [] := by decide

/-- A byte-list delivery: a non-empty delivery is one write entry at the
    buffer, and the empty delivery is no entry at all. -/
example : delivered_writes 0x100 [7, 8] = [(0x100, [7, 8])] := by decide
example : delivered_writes 0x100 [] = [] := by decide

/-- The clamp leaves a count a write judges alone. -/
example : rw_count_clamp (131072 : word) = 131072 := by decide
example : rw_count_clamp (0xffffffffffffffff : word) = MAX_RW_COUNT := by decide

end LinuxSem.LinuxProcessSem.Sys.Uaccess
