/-
  * LinuxProcessSem.StateFd — fd-table and pipe helpers

  - 3922–3935: `fd_lookup`, `fd_insert`, `fd_remove`;
  - 3937–3965: `alloc_fd_aux`, `alloc_fd`, `alloc_fd2` (with the doc
    blocks that precede them);
  - 3971–3984: `pipe_lookup`, `pipe_insert`;
  - 3986–4111: `pipe_write_room`, `pipe_append`, `pipe_take`,
    `firstn_min_length`, `pipe_take_firstn`, `pipe_take_length`,
    `pipe_consume`, `skipn_min_length`, `pipe_consume_of_take`,
    `pipe_new_id`;
  - 4113–4244: `pipe_end_live`;
  - 4246–4261: `le32_bytes`, `pipe_fd_bytes`.

  `event` precedes this range and is
  already in `State.lean` (chunk A1); the VmMaps helpers that follow
  (4262+) are chunk B7.

  TRUST BOUNDARY: this file is part of the trusted specification.

  both live in their own Lean namespaces (`Fs.firstn_min_length` and this one), so
  there is no clash. Lean 4.31 core provides neither `List.take_min_length` nor
  `List.drop_min_length`, so both are proved here, as anticipated.

  There is no `Z.to_nat` in
  the Lean tree: `Int.toNat` is the same function on the same carrier,
  and `Int.min`/`Int.max` are the  `Z.min`/`Z.max`.  The only place
  the two worlds meet is `pipe_take`'s index, and the three lemmas that
  cross it (`pipe_take_firstn`, `pipe_take_length`,
  `pipe_consume_of_take`) either carry `0 <= n` hypothesis or
  use `Z.max 0 n` for exactly that reason.
-/
import LinuxSem.LinuxProcessSem.State
import LinuxSem.LinuxProcessSem.StateLedger

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/-! ## fd table helpers -/

def fd_lookup (fds : List (word × FdEntry)) (fd : word) : Option FdEntry :=
  match fds with
  | [] => none
  | (k, e) :: r => if k == fd then some e else fd_lookup r fd

def fd_insert (fds : List (word × FdEntry)) (fd : word) (e : FdEntry) :
    List (word × FdEntry) :=
  (fd, e) :: fds.filter (fun p => !(p.1 == fd))

def fd_remove (fds : List (word × FdEntry)) (fd : word) : List (word × FdEntry) :=
  fds.filter (fun p => !(p.1 == fd))

/-- Lowest unused fd — the descriptor the kernel hands out at open, as
    Linux does (see `File.lowest_fd`/`Open.openat_spec`).  The scan is
    fuel-bounded at 4096 candidates, so the result is always <= 4096
    (never confusable with an error-encoded return); if all of 0..4095
    are taken the returned candidate may be occupied, and the openat
    spec's freeness side-condition then leaves only the errno branch. -/
def alloc_fd_aux (fds : List (word × FdEntry)) (cand : word) : Nat → word
  | 0 => cand
  | f + 1 =>
      match fd_lookup fds cand with
      | none => cand
      | some _ => alloc_fd_aux fds (cand + 1) f

def alloc_fd (fds : List (word × FdEntry)) : word :=
  alloc_fd_aux fds (BitVec.ofInt 64 0) 4096

/-- The SECOND descriptor a call that reserves two takes: the lowest
    free one strictly above `alloc_fd fds`.  A syscall reserving a pair
    calls `get_unused_fd_flags` twice, and the first reservation is in
    the bitmap by the time the second runs, so the second skips it —
    `Net.Socket.socketpair_spec`'s `fd1` and `fd2` exactly.  Carries the
    same FUEL as `alloc_fd` over a range that starts one higher, so it
    returns at most 8193 — still far below the error-encoding window,
    and callers test both results for freeness for the same reason
    `Fs.File.lowest_fd` does. -/
def alloc_fd2 (fds : List (word × FdEntry)) : word :=
  alloc_fd_aux fds (alloc_fd fds + 1) 4096

/-! ## Pipe helpers — the `fdst_pipes` side table and the fd ends that name it -/

/-- The state of pipe `id`, or `none` for an id no `pipe2` handed out.
    Same shape as `fd_lookup`: first match wins, and `pipe_insert` keeps
    at most one entry per id. -/
def pipe_lookup (ps : List (word × PipeBuf)) (id : word) : Option PipeBuf :=
  match ps with
  | [] => none
  | (k, st) :: r => if k == id then some st else pipe_lookup r id

/-- Bind `id` to `st`, replacing any existing binding. -/
def pipe_insert (ps : List (word × PipeBuf)) (id : word) (st : PipeBuf) :
    List (word × PipeBuf) :=
  (id, st) :: ps.filter (fun p => !(p.1 == id))

/-- MAY A WRITE OF `n` BYTES LAND IN THE SLOT THE PIPE ALREADY USES?
    Every claim below is fs/pipe.c `anon_pipe_read` (:269) /
    `anon_pipe_write` (:431) at v6.18.46, the pair `pipeanon_fops`
    (:1257-1266) installs on an anonymous pipe.

    - an EMPTY queue means the ring is empty too: `anon_pipe_read`
      releases a buffer as soon as its last byte is taken
      (`if (!buf->len)` then `pipe_update_tail`, :359-362, which is
      `pipe_buf_release` at :242 followed by `pipe->tail = ++tail`), so no
      live slot survives a full drain.  The write starts a fresh page, and
      any `n` up to `PIPE_BUF` fits in it — including `n = PIPE_BUF`
      exactly, which skips the merge path (`chars = n & (PAGE_SIZE-1)` at:477 is 0, and:478 tests `chars`) and takes the whole page;
    - a NONEMPTY queue is one slot with `used` bytes of its page already
      spoken for, and the top-up succeeds exactly when `used + n` still
      fits (:480-483).  The other two merge conditions hold by
      construction: `!was_empty` because the queue is nonempty, and
      `PIPE_BUF_FLAG_CAN_MERGE` because every buffer a modeled pipe holds
      was put there by `anon_pipe_write`, which sets that flag on every
      page it allocates (:536-539 — the other branch is packet mode, which
      needs O_DIRECT and so a `pipe2` flag `Pipe.pipe2_spec` declines;
      only splice/vmsplice pages clear it, and neither is modeled).
      `pipe_buf_confirm` is a no-op for `anon_pipe_buf_ops` (:223-227),
      which has no `.confirm`.

    Anything else — a transfer over `PIPE_BUF`, or a top-up that would
    overflow the page — needs a SECOND slot, which is where slot
    accounting and therefore blocking start to matter.  Declined. -/
def pipe_write_room (st : PipeBuf) (n : Int) : Bool :=
  match st with
  | ([], _) => decide (n ≤ PIPE_BUF)
  | (_ :: _, used) => decide (used + n ≤ PIPE_BUF)

/-- The queue after appending `bs`.  An empty queue restarts the mark at
    the new page's fill; a nonempty one carries it up. -/
def pipe_append (st : PipeBuf) (bs : List byte) : PipeBuf :=
  match st with
  | ([], _) => (bs, (bs.length : Int))
  | (q, used) => (q ++ bs, used + (bs.length : Int))

/-- The bytes a read of `n` takes off the front of a pipe's queue.

    `take (word_to_nat count) q` is the natural spelling, but
    `word_to_nat` builds a UNARY NUMERAL of the count
    before it ever looks at `q`, so `read(pipefd, buf, 1 << 20)` would cost
    the extracted checker a million constructors to deliver at most
    PIPE_BUF bytes.  Taking the minimum against the
    queue's own length in `Int` first removes that cost: the numeral is
    bounded by the QUEUE, so the count may be anything.

    `pipe_take_firstn` is the equation proofs go through; the two agree
    for every nonnegative `n`. -/
def pipe_take (q : List byte) (n : Int) : List byte :=
  q.take (Int.toNat (min n (q.length : Int)))

theorem firstn_min_length {A : Type} (l : List A) (n : Nat) :
    List.take (min n l.length) l = List.take n l := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length,
      List.take_of_length_le (by omega)]

theorem pipe_take_firstn (q : List byte) (n : Int) (hn : 0 ≤ n) :
    pipe_take q n = q.take n.toNat := by
  unfold pipe_take
  have h : (min n (q.length : Int)).toNat = min n.toNat q.length := by
    rcases Int.le_total n (q.length : Int) with hle | hge
    · rw [Int.min_eq_left hle, Nat.min_eq_left (by rwa [Int.toNat_le])]
    · rw [Int.min_eq_right hge, Int.toNat_natCast,
        Nat.min_eq_right (by rwa [Int.le_toNat hn])]
  rw [h, firstn_min_length]

theorem pipe_take_length (q : List byte) (n : Int) :
    ((pipe_take q n).length : Int) ≤ max 0 n := by
  unfold pipe_take
  rw [List.length_take]
  have h1 : ((min (Int.toNat (min n (q.length : Int))) q.length : Nat) : Int) ≤
      ((min n (q.length : Int)).toNat : Int) :=
    Int.ofNat_le.mpr (Nat.min_le_left ..)
  have h2 : ((min n (q.length : Int)).toNat : Int) ≤ max 0 n := by
    have h := Int.ofNat_toNat (min n (q.length : Int))
    have hm : min n (q.length : Int) ≤ n := Int.min_le_left ..
    omega
  exact Int.le_trans h1 h2

/-- The queue after a read of `k` bytes.  The mark does not move: the
    bytes a reader consumed are at the FRONT of the page and stay
    unavailable to writers.

    `k` is a `Nat` and stays one: every caller passes the LENGTH OF THE
    DELIVERED PREFIX, which `pipe_take` has already bounded by the
    queue, so no count reaches this in unary.  `drop (length (take k
    q)) q = drop k q`, so passing the delivered length is the same
    queue the count would have left. -/
def pipe_consume (st : PipeBuf) (k : Nat) : PipeBuf :=
  (st.1.drop k, st.2)

theorem skipn_min_length {A : Type} (l : List A) (n : Nat) :
    List.drop (min n l.length) l = List.drop n l := by
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length]
    exact (List.drop_of_length_le (by omega)).symm

theorem pipe_consume_of_take (q : List byte) (used : Int) (n : Int) (hn : 0 ≤ n) :
    pipe_consume (q, used) (pipe_take q n).length = pipe_consume (q, used) n.toNat := by
  simp only [pipe_consume, pipe_take_firstn q n hn, List.length_take]
  rw [skipn_min_length]

/-- The id a new pipe gets: the number of pipes created so far.

    Entries are NEVER REMOVED from `fdst_pipes` — closing both ends of a
    pipe drops its two fds but leaves the table entry behind — so this
    counts creations, and an id is never reused for a second pipe.  That
    is the point: were an id recycled, a fresh pipe could inherit the
    bytes of a dead one.  The dead entry is unreachable (no fd names it)
    and costs only its bytes, which the model keeps rather than inventing
    a reclamation rule; Linux frees the pipe inode, and nothing a program
    can do observes the difference.

    `Pipe.pipe2_spec` still CHECKS that the id it computes is free (as
    `Open.openat_spec` checks `lowest_fd`'s answer), so a run long enough
    to wrap the 64-bit counter declines rather than aliasing. -/
def pipe_new_id (ps : List (word × PipeBuf)) : word :=
  BitVec.ofInt 64 (ps.length : Int)

/-- Is some fd in the table an end of pipe `id` of the given direction?
    `writer = true` asks "does this pipe still have a WRITER", the test
    that separates a pipe read at end-of-data into end-of-file (return 0)
    from a block; `writer = false` asks "does it still have a READER",
    which is what stands between a write and SIGPIPE.

    DERIVED, not counted.  Linux keeps `pipe->readers` / `pipe->writers`
    and `pipe_release` decrements them by the file's `f_mode`
    (fs/pipe.c:730-733, v6.18.46); the model
    reads the same fact off the fd table instead, so there is no counter
    to keep in step with `close` — and no way for one to drift.  The two
    agree because `Pipe.pipe2_spec` is the ONLY thing in this model that
    constructs an `FdPipe`, so a pipe end exists exactly where this table
    shows one — whatever paths the image happens to contain.  Stated that
    way on purpose: an enumeration of the syscalls that
    could alias an end and are absent would be
    falsified by anything added below it.  `openat` resolves against
    `m_fs` and yields an `FdFile`/`FdFileW`/`FdFileA`/`FdFileRW` — or,
    for the device paths it answers, an `FdDevNull` or an `FdUrandom` — never
    an `FdPipe`, so a path
    merely NAMED like a procfs one cannot hand out a second reference.

    A syscall that DUPLICATES a descriptor would keep the two
    constructions in step for a reason worth writing down, because a
    per-fd counter would not: Linux's counters are per `struct file`, and
    a duplication creates no new one — `f_dupfd` (fs/file.c:1472,
    v6.18.46) and `do_dup2` (:1265) each just `get_file` the existing one
    (:1480, :1303) — so `pipe->writers` does not move and `pipe_release`
    runs only at the last `fput`, while a copy here is a second TABLE
    ENTRY and this scan answers `true` while EITHER entry survives and
    `false` once both are gone, the same moment.

    THAT IS AN ARGUMENT ABOUT A CASE NOTHING REACHES, and what keeps it
    unreached is an arm rather than an absence: `dup` (23) and `dup3`
    (24) ARE modeled, and both consult `Fs.File.dup_modeled_entry`, whose
    `| FdPipe _ _ => false` declines a pipe end instead of copying its
    entry.  So no second `FdPipe` naming one pipe is ever built, and
    `Pipe.pipe2_spec` remains the only constructor.  The paragraph above
    is recorded because a later change lifting that decline needs it, not
    because nothing in the model duplicates a descriptor.

    THE OTHER WAY A `struct file` OUTLIVES ITS FD is fd-passing, and it
    matters here for a reason this scan cannot see: Linux counts
    `pipe->writers` per `struct file`, so a pipe end in flight over a
    socket — sent, its sender's fd closed, not yet received — still holds
    the pipe open and still blocks a reader, while this table shows no
    end and would answer end-of-file.  That is the one shape where
    reading the fd table is not merely a different spelling of the
    kernel's counter but a WRONG one.

    What closes it is an arm in a different file, and the coupling is
    worth stating because nobody would look for it here:
    `Net.Socket.socket_spec` answers `unmodeled` for every family but
    AF_INET, and at v6.18.46 fd-passing is AF_UNIX only —
    `unix_attach_fds` (net/unix/af_unix.c:1958) is the sole path from an
    SCM_RIGHTS control message to an installed descriptor, and SCM_RIGHTS
    appears nowhere in net/ipv4: `ip_cmsg_send` (net/ipv4/ip_sockglue.c)
    understands IP_RETOPTS, IP_PKTINFO, IP_TTL, IP_TOS and IP_PROTOCOL,
    none of which carries an fd.  So no modeled socket can transport one.

    THE CONDITION THAT FALSIFIES THIS: modelling AF_UNIX.  A change that
    admits that family reopens the case above, and it must either decline
    a pipe end at `sendmsg`'s control data or give this model a notion of
    a pipe end held by nothing in the fd table.  The decline in
    `socket_spec` is load-bearing for pipe end-of-file, not only for
    sockets.

    THE GENERAL CLAIM, since the paragraphs above each argue one route and
    the scan depends on all of them at once: NO REFERENCE TO A PIPE EXISTS
    OUTSIDE THIS TABLE.  That is strictly stronger than "no second fd
    names a pipe end", which is what the arms in `Fs.File` and
    `Checks/Cases/Fs/Pipe.lean` establish — the latter at the fd-kind
    dispatch sites (`fd_names_path_ignores_a_pipe_end`,
    `dup_of_a_pipe_end_declines`, `clone_with_a_pipe_end_open_declines`)
    and at the starting table (`init_model_holds_no_pipe_end`) — and it
    is the one the scan needs —
    Linux counts `struct file`s, so a reference with no fd is exactly the
    gap between the two claims.  It holds today because every way to make
    one is declined, each by a named arm rather than by absence:

    - a second PROCESS is what the dup paragraph above does not cover:
      `Kernel.Fork.clone_no_shared_file_b` answers `false` for `FdPipe`,
      so a clone with either end open is `unmodeled`, and
      `clone_fork_flags_b` admits only the bare SIGCHLD word, so
      CLONE_FILES and CLONE_THREAD never share a table and no second
      instruction stream exists to race a close;
    - `F_DUPFD` does NOT go through `Fs.File.dup_modeled_entry` the way
      `dup` and `dup3` do.  It is declined by `Fcntl.fcntl_spec`'s
      closing `unmodeled`, which refuses every command that spec does
      not model — a decline that is not pipe-specific and would
      evaporate the moment `F_DUPFD` is modeled for any reason at all.
      Of the three duplication routes this is the weak one, and it is
      the only one that holds by nothing having been added rather than
      by an arm.  `Fcntl.fcntl_spec` carries the obligation in its own
      prose too, beside its `F_DUPFD` bullet, because this file is not
      where someone widening fcntl's command set will look;
    - a reference IN FLIGHT is closed by two gates, the AF_INET one
      argued above and `Net.Socket.sendmsg_spec`'s
      `if negb (w_is0 ctllen) then unmodeled`, which the paragraph above
      names only as something a future AF_UNIX change would need.

    ONLY THE WRITER DIRECTION IS A SOUNDNESS EXPOSURE, which is what
    decides how much any future widening costs.  Under-reporting a WRITER
    makes a read at end-of-data answer 0 where Linux blocks: a modeled
    answer Linux would not give, and the one shape here that costs
    priority 1.  Under-reporting a READER makes the write arm's
    `negb (pipe_end_live … false)` guard fire, which is `unmodeled` — a
    coverage loss, not an unsound answer. -/
def pipe_end_live (fds : List (word × FdEntry)) (id : word) (writer : Bool) : Bool :=
  match fds with
  | [] => false
  | (_, FdEntry.FdPipe id' w) :: r =>
      (id' == id && w == writer) || pipe_end_live r id writer
  /- The non-pipe kinds are named rather than wildcarded, so that a
     later `FdEntry` constructor able to name a pipe end stops the build
     here instead of being skipped silently.  The paragraph above argues
     from what CONSTRUCTS an `FdPipe`; this match is what would have to
     re-read that argument, and a `_ ::` arm is exactly the shape that
     would not.  A missed end costs differently in the two directions,
     per the asymmetry above: on `writer = true` it fails OPEN, answering
     a modeled 0 where Linux blocks, which is a wrong answer rather than
     an `unmodeled` — that is what makes the silent arm expensive.  On
     `writer = false` it fails CLOSED instead, since the write arm
     declines on `negb (pipe_end_live … false)` and a missed reader only
     makes that guard fire more often. -/
  | (_, FdEntry.FdChannel _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdFile _ _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdFileW _ _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdFileA _ _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdFileRW _ _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdDir) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdSocket _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdDevNull _ _) :: r => pipe_end_live r id writer
  | (_, FdEntry.FdUrandom) :: r => pipe_end_live r id writer

/-- A 32-bit value as the four little-endian bytes the kernel's
    `copy_to_user` of an `int` lays down. -/
def le32_bytes (v : word) : List byte :=
  let z := v.toNat
  [ BitVec.ofInt 8 (z : Int),
    BitVec.ofInt 8 ((z >>> 8) : Int),
    BitVec.ofInt 8 ((z >>> 16) : Int),
    BitVec.ofInt 8 ((z >>> 24) : Int) ]

/-- The eight bytes `pipe2` copies out: the read end then the write end,
    as one `int fildes[2]` — a SINGLE contiguous range, which is how
    `do_pipe2`'s one `copy_to_user` writes it (fs/pipe.c:1040, with
    `fd[0] = fdr` and `fd[1] = fdw` set at :1005-1006, v6.18.46). -/
def pipe_fd_bytes (fdr fdw : word) : List byte :=
  le32_bytes fdr ++ le32_bytes fdw

/-! ## Sanity checks

    Concrete evaluations pin the definitions above.  `FdEntry` has no
    `DecidableEq` (its `FdSocket` arm reaches the coinductive `SockState`,
    a function type — see the note on `FdState`), so the fd-table checks
    read the table's KEYS (`Prod.fst`, decidable) and test the looked-up
    binding with `isSome`/`isNone` rather than by comparing entries. -/

/-- A tiny fd table for the checks: 0 a channel, 1 a pipe write end,
    2 `/dev/null`. -/
private def demoFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdPipe 3 true),
   (2, FdEntry.FdDevNull true false)]

example : (fd_lookup demoFds 1).isSome = true := by decide

example : (fd_lookup demoFds 9).isNone = true := by decide

example : (fd_lookup demoFds 1).map
    (fun e => match e with | FdEntry.FdPipe id _ => id | _ => 0) = some 3 := by
  decide

example : (fd_insert demoFds 3 FdEntry.FdDir).map (·.1) = [3, 0, 1, 2] := by
  decide

example : (fd_insert demoFds 1 FdEntry.FdDir).map (·.1) = [1, 0, 2] := by
  decide

example : (fd_remove demoFds 1).map (·.1) = [0, 2] := by decide

example : (fd_remove demoFds 9).length = 3 := by decide

example : alloc_fd demoFds = 3 := by decide

example : alloc_fd2 demoFds = 4 := by decide

example : (pipe_lookup [(0, ([], 0)), (1, ([9], 5))] 1).map (·.2) = some 5 := by
  decide

example : (pipe_insert [(0, ([], 0))] 1 ([9], 1)).map (·.1) = [1, 0] := by decide

example : pipe_write_room ([], 0) 4096 = true := by decide

example : pipe_write_room ([(1 : byte), 2, 3], 96) 4000 = true := by decide

example : pipe_write_room ([(1 : byte), 2, 3], 97) 4000 = false := by decide

example : pipe_append ([], 0) [(1 : byte), 2] = ([1, 2], 2) := by decide

example : pipe_append ([(1 : byte)], 1) [(2 : byte), 3] = ([1, 2, 3], 3) := by
  decide

example : pipe_take [(1 : byte), 2, 3, 4] 2 = [1, 2] := by decide

example : pipe_take [(1 : byte), 2] 10 = [1, 2] := by decide

example : pipe_take [(1 : byte), 2, 3] (-1) = [] := by decide

example : pipe_consume ([(1 : byte), 2, 3], 3) 2 = ([3], 3) := by decide

example : pipe_new_id [] = 0 := by decide

example : pipe_new_id [(0, ([], 0)), (1, ([], 0))] = 2 := by decide

example : pipe_end_live demoFds 3 true = true := by decide

example : pipe_end_live demoFds 3 false = false := by decide

example : pipe_end_live ((0, FdEntry.FdPipe 3 false) :: demoFds) 3 false = true := by
  decide

example : le32_bytes 0x01020304 = [(4 : byte), 3, 2, 1] := by decide

example : pipe_fd_bytes 0 1 = [(0 : byte), 0, 0, 0, 1, 0, 0, 0] := by decide

end LinuxSem.LinuxProcessSem
