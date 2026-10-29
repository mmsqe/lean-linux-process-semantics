/-
  * LinuxProcessSem.Checks.Witness.Fs.ReadWrite — the read (63),
    write (64), pread64 (67), pwrite64 (68), writev (66), readv (65),
    lseek (62) witnesses, and their proofs

  Answers to Linux [fs/read_write.c]: this file holds the witnesses for the syscalls
  defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and re-exports this module.  A
  witness here exhibits one admissible outcome for a spec in the matching
  [Sys] module, which is what progress is proved from.

  A witness answers with `Outcome SyscallEffect Model event`, and the spec
  monad `Sys SyscallEffect` is `SysSpec SyscallEffect` (`MonadInstances`).

  `InputStream` / `NetStream` are total functions over their index
  (`State.InputStream`, `State.NetStream`).  A witness written against
  `ICons b s'` / `NCons b rest` takes `b` from the observation
  `s 0 = some b` and carries the TAIL as the shift
  `fun n => s (n + 1)` — which is `(stream_take s 1).2`, so the state the
  witness returns is exactly the state a one-byte read leaves.

  Each witness proof walks the spec's readers with `bind_step`, closes the
  arms with `pure_ok` / `unmodeled_intro`, and uses
  `record_copyins_outcome` wherever the arm records a ledger.  The four
  delivery witnesses — `read_witness_ok`, `write_witness_ok`,
  `writev_witness_ok` and `readv_witness_ok` — have a `choose` over the
  delivered prefix as their spec arm (`import_iovecs`/`scatter_iovecs` on
  the vectored calls), so each also carries the bridge from the witness's
  ONE-BYTE delivery to the spec's `choose` predicate (`1 ≤ length`,
  `≤ rw_count_clamp count` / `≤ iovs_total`, agreement with
  `stream_take`/`net_take`, and `read_bytes_map … ≠ none` /
  `scatter_iovecs … ≠ none`).

  That bridge needs two equations the stream encoding does not come with:
  `stream_take s 1 = ([b], shift s)` given `s 0 = some b`, and
  `net_take rx 1 = ([b], fun n => rx (n + 1))` given
  `rx 0 = NetStep.cons b`.  `StateStreams` / `StateNet` state their
  successor forms (`stream_take_some`, `net_take_succ_of_cons`) but no
  one-byte lemma, and they are not this file's to extend:
  `stream_take_one_some` / `net_take_one_cons` below state them, each a
  `simp` away from the successor form, and are the only additions the four
  proofs needed.  The same block carries the three arithmetic facts the
  deliveries use (`len_word [b] = 1`, `1 ≤ rw_count_clamp count` at a
  nonzero count, and `addr_is_error_b (len_word (bs.take 1)) = false`),
  plus `emit_then_quiet_ok` (the `emit` ;; event-free-spec bind that
  `emit_pure_ok` covers only for `pure`).

  The recipe the eight proofs follow:
  `access_ok_zero_witness` is stated below: it is the one-line
  witness-side counterpart of `Uaccess.access_ok_zero`, and no
  `Checks/Witness/Uaccess` module exists in this tree to hold it.  When
  one does,
  delete it and import that module.
-/
import LinuxSem.Checks.Witness.Prelude

namespace LinuxSem.Checks.Witness.Fs.ReadWrite

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite
open LinuxSem.Checks.Witness.Prelude

/- =========================================================================
   The witness-side range acceptor

   The statement and the proof-relevant behaviour are
   `Uaccess.access_ok_zero`'s.
   ========================================================================= -/

/-- `Uaccess.access_ok_zero` as a witness: the zero answer where the model
    is sure the range passed `access_ok`, -EFAULT where it is sure it did
    not, and the fail-closed decline in between. -/
def access_ok_zero_witness (buf count : word)
    (m : Model) (k : Outcome SyscallEffect Model event) :
    Outcome SyscallEffect Model event :=
  if access_okb buf (count.toNat : Int) then k
  else ret_outcome (errno_ret EFAULT) m

/-- The byte one observation of a stream holds, and the stream that
    follows it — the `ICons b s'` destruct in function form.  `shift` is
    `(stream_take s 1).2` definitionally. -/
def shift (s : InputStream) : InputStream := fun n => s (n + 1)

/- =========================================================================
   The one-byte destructs the read witnesses need

   The read witnesses open on the stream's first observation and then hold
   the TAIL in hand.  Here the stream is a function, so the tail is the
   shift `fun n => s (n + 1)`, and the equation saying so is
   `StateStreams.stream_take_some` / `StateNet.net_take_succ_of_cons` at
   `k = 0`, from which the one-byte form below is a `simp` away.

   These two lemmas are the whole of that gap: `StateStreams.lean` has
   `stream_take_zero`, `stream_take_eof`, `stream_take_cons` and the
   `_z`/`_infinite` forms but no `stream_take s 1 = (head :: [], shift s)`
   spelling, and `StateNet.lean` states its successor lemma only at
   `k + 1`.  Both are stated here: their home would be
   `StateStreams`/`StateNet`, but those files are not this one's to edit.
   -/

theorem stream_take_one_some {s : InputStream} {b : byte} (h : s 0 = some b) :
    stream_take s 1 = ([b], shift s) := by
  unfold stream_take shift
  rw [h]
  dsimp only
  rw [stream_take_zero]

theorem net_take_one_cons {s : NetStream} {b : byte} (h : s 0 = NetStep.cons b) :
    net_take s 1 = ([b], fun n => s (n + 1)) := by
  unfold net_take
  rw [h]
  dsimp only
  rw [net_take_zero]

/- Arithmetic, stated here because the witnesses below are the only users.
   The one-byte lists the witnesses deliver
   have `len_word [b] = 1`, and a delivery of one byte fits any nonzero
   clamped count. -/

theorem len_word_singleton (b : byte) : len_word [b] = BitVec.ofInt 64 1 := by
  show BitVec.ofNat 64 1 = BitVec.ofInt 64 1
  decide

/-- A nonzero count admits a one-byte delivery: `rw_count_clamp` is
    `min count MAX_RW_COUNT` and the count is at least one. -/
theorem one_le_rw_count_clamp (count : word) (h : 0 < count.toNat) :
    1 ≤ rw_count_clamp count := by
  unfold rw_count_clamp
  refine Int.le_min.mpr ⟨?_, ?_⟩
  · exact_mod_cast h
  · unfold MAX_RW_COUNT
    decide

/-- `addr_is_error_b` is the *signed* return test, so a `len_word` of at
    most one byte is never an error encoding — the `writev` channel arm's
    `addr_is_error_b (len_word bs) = false` premise, at the one-byte
    delivery `writev_witness` makes. -/
theorem addr_is_error_b_len_word_take_one (bs : List byte) :
    addr_is_error_b (len_word (bs.take 1)) = false := by
  have hle : (bs.take 1).length ≤ 1 := List.length_take_le 1 bs
  have hlen : (len_word (bs.take 1)).toNat = (bs.take 1).length := by
    unfold len_word
    rw [BitVec.toNat_ofNat]
    omega
  have hle' : ((bs.take 1).length : Int) ≤ 1 := by exact_mod_cast hle
  unfold addr_is_error_b
  rw [hlen]
  exact decide_eq_false (by unfold two_pow_64; omega)

/- =========================================================================
   read_urandom
   ========================================================================= -/

/-- `[ReadWrite.read_urandom]`'s one outcome per branch: the delivery is
    computed, so the witness IS the delivery. -/
def read_urandom_witness (buf count : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if w_is0 count then ret_outcome (BitVec.ofInt 64 0) m
  else
  match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
  | none => ret_outcome (errno_ret EFAULT) m
  | some _ =>
      let r := stream_take_z (m_urandom m) (rw_count_clamp count)
      if !(((r.1.length : Int) == rw_count_clamp count))
      then .unmodeled
      else
      match read_bytes_map i.in_wmem buf (len_word r.1) with
      | none => .unmodeled
      | some _ =>
          .ok (mkEffect (len_word r.1) [(buf, r.1)] []) (with_urandom r.2 m) []

/- =========================================================================
   read
   ========================================================================= -/

/-- `[ReadWrite.read_spec]`'s witness: the one-byte delivery from the
    input stream (channel; 0 at end of input), the deterministic file
    read, -EFAULT for a destination whose first byte cannot be written,
    or the fail-closed `.unmodeled`.

    ONE BYTE is the channel's admissible short read: a terminal can
    deliver fewer bytes than asked for, and the spec's `choose` admits any
    nonempty prefix, so the witness need only exhibit one. -/
def read_witness (fd buf count : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel ch) =>
      if !(w_is0 ch) then ret_outcome (errno_ret EBADF) m
        -- write-only channel
      else if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
        -- vfs_read's access_ok
      else if w_is0 count then ret_outcome (BitVec.ofInt 64 0) m
      else
        match m_stdin m 0 with
        | none => ret_outcome (BitVec.ofInt 64 0) m
          -- end of input: needs no writable buffer
        | some b =>
            match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
            | none => ret_outcome (errno_ret EFAULT) m
              -- no byte can land: -EFAULT
            | some _ =>
            match read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) with
            | none => .unmodeled
              -- partially writable destination
            | some _ =>
                -- the one-byte delivery is always available
                .ok (mkEffect (BitVec.ofInt 64 1) [(buf, [b])] [])
                   (with_stdin (shift (m_stdin m)) m)
                   [event.ReadEv ch b]
  | some FdEntry.FdDir =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
        -- access_ok precedes the directory's .read
      else ret_outcome (errno_ret EISDIR) m
        -- directory fd: -EISDIR
  | some (FdEntry.FdFileW _ _) => ret_outcome (errno_ret EBADF) m
    -- write-only file
  | some (FdEntry.FdFileA _ _) => ret_outcome (errno_ret EBADF) m
    -- append fd: also O_WRONLY
  | some (FdEntry.FdFile p off) =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
        -- vfs_read's access_ok
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          let bs := Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              -- unwritable DELIVERED prefix: -EFAULT when not even its
              -- first byte can land, else fail closed
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => .unmodeled
          | some _ =>
              .ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                 (with_fds (fd_insert (m_fds m) fd
                              (FdEntry.FdFile p (off + len_word bs))) m)
                 []
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFile] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          let bs := Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => .unmodeled
          | some _ =>
              .ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
                 (with_fds (fd_insert (m_fds m) fd
                              (FdEntry.FdFileRW p (off + len_word bs))) m)
                 []
  | some (FdEntry.FdSocket sk) =>
      if !(modeled_rw_range buf count) then .unmodeled
        -- see [ReadWrite.read_spec]
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (BitVec.ofInt 64 0) m)
        -- count = 0 short-circuits before the protocol
      else
      match sk with
      | .SkConnected peer ch rx =>
          match rx 0 with
          | .fin =>
              access_ok_zero_witness buf count m
                (ret_outcome (BitVec.ofInt 64 0) m)
                -- the peer's FIN, taken in sequence
          | .rst =>
              access_ok_zero_witness buf count m
                (ret_outcome (errno_ret ECONNRESET)
                   (with_fds (fd_insert (m_fds m) fd
                                (FdEntry.FdSocket (SockState.SkReset peer ch))) m))
          | .timedOut =>
              access_ok_zero_witness buf count m
                (ret_outcome (errno_ret ETIMEDOUT)
                   (with_fds (fd_insert (m_fds m) fd
                                (FdEntry.FdSocket (SockState.SkReset peer ch))) m))
          | .cons b =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
                -- no byte can land: -EFAULT
              | some _ =>
              match read_bytes_map i.in_wmem buf
                      (len_word (net_take_z rx (rw_count_clamp count)).1) with
              | none => .unmodeled
                -- partially writable destination
              | some _ =>
                  -- the one-byte delivery is always available
                  .ok (mkEffect (BitVec.ofInt 64 1) [(buf, [b])] [])
                     (with_fds (fd_insert (m_fds m) fd
                                  (FdEntry.FdSocket
                                     (SockState.SkConnected peer ch
                                        (fun n => rx (n + 1))))) m)
                     [event.ReadEv ch b]
      | .SkReset _ _ =>
          access_ok_zero_witness buf count m
            (ret_outcome (BitVec.ofInt 64 0) m)
            -- the error was delivered once already
      | _ =>
          access_ok_zero_witness buf count m
            (ret_outcome (errno_ret ENOTCONN) m)
            -- fresh, bound or listening
  | some (FdEntry.FdDevNull rd _) =>
      if !rd then ret_outcome (errno_ret EBADF) m
      else access_ok_zero_witness buf count m (ret_outcome (BitVec.ofInt 64 0) m)
  | some FdEntry.FdUrandom =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else read_urandom_witness buf count i m
  | some (FdEntry.FdPipe id w) =>
      if w then ret_outcome (errno_ret EBADF) m
        -- write end: read is -EBADF
      else if !(modeled_rw_range buf count) then .unmodeled
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (BitVec.ofInt 64 0) m)
      else
      match pipe_lookup (m_pipes m) id with
      | none => .unmodeled
      | some ([], _) =>
          if pipe_end_live (m_fds m) id true then .unmodeled
            -- would block
          else access_ok_zero_witness buf count m
                 (ret_outcome (BitVec.ofInt 64 0) m)
                 -- end of file
      | some (q@(_ :: _), used) =>
          let del := pipe_take q (rw_count_clamp count)
          match read_bytes_map i.in_wmem buf (len_word del) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => .unmodeled
          | some _ =>
              .ok (mkEffect (len_word del) (delivered_writes buf del) [])
                 (with_pipes (pipe_insert (m_pipes m) id
                                (pipe_consume (q, used) del.length)) m)
                 []

/- =========================================================================
   write
   ========================================================================= -/

/-- `[ReadWrite.write_spec]`'s witness: the full delivery on every kind
    that transfers, and the arm's own errno/decline on the rest. -/
def write_witness (fd buf count : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m
        -- stdin is read-only
      else
      if !(modeled_rw_range buf count) then .unmodeled
        -- see [Uaccess.modeled_rw_range]
      else
      if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (BitVec.ofInt 64 0) m)
        -- count = 0: return 0, but only once the range passes access_ok
      else
      let bs := write_source i.in_mem buf count
      if bs.length == 0
      then ret_outcome (errno_ret EFAULT) m
        -- nothing readable: -EFAULT
      else outcome_copyins [(buf, bs.length)]
             (.ok (mkEffect (len_word bs) [] []) m (bs.map (event.WriteEv ch)))
             -- the full delivery
  | some FdEntry.FdDir => ret_outcome (errno_ret EBADF) m
    -- directory fd is O_RDONLY: -EBADF
  | some (FdEntry.FdFile _ _) => ret_outcome (errno_ret EBADF) m
    -- read-only file
  | some (FdEntry.FdFileW p off) =>
      if !(modeled_rw_range buf count) then .unmodeled
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then ret_outcome (errno_ret EFAULT) m
        -- nothing readable: -EFAULT
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              if !(modeled_file_gap data off bs) then .unmodeled
                -- a hole past end-of-file too large to zero-fill
              else
              let out :=
                .ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileW p (off + len_word bs)))
                     (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                  []
              if w_is0 count then out
              else outcome_copyins [(buf, bs.length)] out
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      if !(modeled_rw_range buf count) then .unmodeled
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then ret_outcome (errno_ret EFAULT) m
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              if !(modeled_file_gap data off bs) then .unmodeled
              else
              let out :=
                .ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileRW p (off + len_word bs)))
                     (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                  []
              if w_is0 count then out
              else outcome_copyins [(buf, bs.length)] out
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (FdEntry.FdFileA p off) =>
      if !(modeled_rw_range buf count) then .unmodeled
        -- the [FdFileW] arm's gate; see [ReadWrite.write_spec]'s
        -- [FdFileA] arm for why it does not subsume the access_ok
      else if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
        -- vfs_write's access_ok, first
      else if rw_pos_einvalb off (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
        -- rw_verify_area, on f_pos
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then ret_outcome (errno_ret EFAULT) m
        -- nothing readable: -EFAULT
      else
        let k :=
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              let out :=
                .ok (mkEffect (len_word bs) [] [])
                  (with_fds (fd_insert (m_fds m) fd
                               (FdEntry.FdFileA p (append_new_pos data bs off)))
                     (with_fs (Fs.fs_set (m_fs m) p
                                 (Fs.file_write data (len_word data) bs)) m))
                  []
              if w_is0 count then out
              else outcome_copyins [(buf, bs.length)] out
        if w_is0 count then access_ok_zero_witness buf count m k else k
  | some (FdEntry.FdSocket _) => .unmodeled
    -- writing a socket is unmodeled, permanently
  | some FdEntry.FdUrandom => ret_outcome (errno_ret EBADF) m
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else if !(modeled_rw_range buf count) then .unmodeled
      else access_ok_zero_witness buf count m
             (ret_outcome (BitVec.ofInt 64 (rw_count_clamp count)) m)
  | some (FdEntry.FdPipe id w) =>
      if !w then ret_outcome (errno_ret EBADF) m
        -- read end: write is -EBADF
      else if !(modeled_rw_range buf count) then .unmodeled
      else if w_is0 count then
        access_ok_zero_witness buf count m (ret_outcome (BitVec.ofInt 64 0) m)
      else if !(pipe_end_live (m_fds m) id false) then .unmodeled
        -- SIGPIPE
      else
      match pipe_lookup (m_pipes m) id with
      | none => .unmodeled
      | some st =>
          if !(pipe_write_room st (count.toNat : Int)) then .unmodeled
          else
          let bs := write_source i.in_mem buf count
          if !(bs.length == word_to_nat count) then .unmodeled
          else outcome_copyins [(buf, bs.length)]
                 (.ok (mkEffect count [] [])
                    (with_pipes (pipe_insert (m_pipes m) id (pipe_append st bs)) m)
                    [])
                 -- the whole source is read, so the range goes in the
                 -- copy-in ledger, exactly as the channel and file arms
                 -- record theirs

/- =========================================================================
   pread64 and pwrite64
   ========================================================================= -/

/-- `[ReadWrite.pread64_spec]`'s witness: the bytes at `pos`, with the
    model untouched. -/
def pread64_witness (fd buf count pos : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdFileW _ _) => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdFileA _ _) => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdDevNull rd _) =>
      if !rd then ret_outcome (errno_ret EBADF) m
      else if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (BitVec.ofInt 64 0) m
  | some FdEntry.FdUrandom =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else read_urandom_witness buf count i m
  | some FdEntry.FdDir =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (errno_ret EISDIR) m
  | some (FdEntry.FdFile p _) =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          let bs := Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => .unmodeled
          | some _ =>
              .ok (mkEffect (len_word bs) (delivered_writes buf bs) []) m []
              -- the model is unchanged: a pread advances no offset
  | some (FdEntry.FdFileRW p _) =>
      -- the [FdFile] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          let bs := Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count))
          match read_bytes_map i.in_wmem buf (len_word bs) with
          | none =>
              match read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
              | none => ret_outcome (errno_ret EFAULT) m
              | some _ => .unmodeled
          | some _ =>
              .ok (mkEffect (len_word bs) (delivered_writes buf bs) []) m []

/-- `[ReadWrite.pwrite64_spec]`'s witness: the whole source written at
    `pos`, the model's file updated and no offset moved; the append kind
    fails closed. -/
def pwrite64_witness (fd buf count pos : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  if ppos_einvalb pos then ret_outcome (errno_ret EINVAL) m
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdPipe _ _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdSocket _) => ret_outcome (errno_ret ESPIPE) m
  | some (FdEntry.FdFile _ _) => ret_outcome (errno_ret EBADF) m
  | some FdEntry.FdDir => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdFileA _ _) => .unmodeled
    -- see [ReadWrite.pwrite64_spec]
  | some FdEntry.FdUrandom => ret_outcome (errno_ret EBADF) m
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else ret_outcome (BitVec.ofInt 64 (rw_count_clamp count)) m
  | some (FdEntry.FdFileW p _) =>
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else
      let bs := write_source i.in_mem buf count
        -- no count gate: see [ReadWrite.pwrite64_spec]
      if !(w_is0 count) && (bs.length == 0)
      then ret_outcome (errno_ret EFAULT) m
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          if !(modeled_file_gap data pos bs) then .unmodeled
          else
          let out :=
            .ok (mkEffect (len_word bs) [] [])
               (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
          if w_is0 count then out
          else outcome_copyins [(buf, bs.length)] out
  | some (FdEntry.FdFileRW p _) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      if !(access_okb buf (count.toNat : Int))
      then ret_outcome (errno_ret EFAULT) m
      else if rw_pos_einvalb pos (count.toNat : Int)
      then ret_outcome (errno_ret EINVAL) m
      else
      let bs := write_source i.in_mem buf count
      if !(w_is0 count) && (bs.length == 0)
      then ret_outcome (errno_ret EFAULT) m
      else
      match Fs.fs_lookup (m_fs m) p with
      | none => .unmodeled
      | some data =>
          if !(modeled_file_gap data pos bs) then .unmodeled
          else
          let out :=
            .ok (mkEffect (len_word bs) [] [])
               (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) []
          if w_is0 count then out
          else outcome_copyins [(buf, bs.length)] out

/- =========================================================================
   writev
   ========================================================================= -/

/-- `[ReadWrite.writev_spec]`'s witness.  The iovec table's import ledger
    wraps every arm, as it does in the spec; the channel delivers ONE
    byte (the admissible short write), the file arms write the whole
    gathering. -/
def writev_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (FdEntry.FdChannel ch) =>
      if w_is0 ch then ret_outcome (errno_ret EBADF) m
        -- stdin is read-only
      else outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0)
               let bs := writev_gathered i.in_mem iovs0
               if total == 0 then ret_outcome (BitVec.ofInt 64 0) m
                 -- zero aggregate
               else if bs.length == 0
               then ret_outcome (errno_ret EFAULT) m
                 -- nothing gatherable
               else if addr_is_error_b (len_word bs) then .unmodeled
               else outcome_copyins
                      (iov_prefix_accesses (cap_iovecs iovs0)
                         (bs.take 1).length)
                      (.ok (mkEffect (len_word (bs.take 1)) [] []) m
                        ((bs.take 1).map (event.WriteEv ch)))
                      -- the one-byte delivery
        )
  | some FdEntry.FdDir => ret_outcome (errno_ret EBADF) m
    -- directory fd is O_RDONLY: -EBADF
  | some (FdEntry.FdFile _ _) => ret_outcome (errno_ret EBADF) m
    -- read-only file
  | some (FdEntry.FdPipe _ w) =>
      if !w then ret_outcome (errno_ret EBADF) m
        -- read end: -EBADF
      else outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               if (iovs_total (cap_iovecs iovs0)) == 0
               then ret_outcome (BitVec.ofInt 64 0) m
                 -- zero aggregate: above the file kind
               else .unmodeled
                 -- vectored pipe writes
        )
  | some FdEntry.FdUrandom => ret_outcome (errno_ret EBADF) m
    -- read-only
  | some (FdEntry.FdDevNull _ wr) =>
      if !wr then ret_outcome (errno_ret EBADF) m
      else outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               ret_outcome (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) m
        )
  | some (FdEntry.FdFileW p off) =>
      outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0)
               let bs := writev_gathered i.in_mem iovs0
               if total == 0 then ret_outcome (BitVec.ofInt 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if bs.length == 0
               then ret_outcome (errno_ret EFAULT) m
               else
                 match Fs.fs_lookup (m_fs m) p with
                 | none => .unmodeled
                 | some data =>
                     if !(modeled_file_gap data off bs) then .unmodeled
                       -- hole too large
                     else
                     if addr_is_error_b (len_word bs) then .unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                       (.ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdEntry.FdFileW p (off + len_word bs)))
                             (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                          [])
        )
  | some (FdEntry.FdFileRW p off) =>
      -- the [FdFileW] arm above, on the O_RDWR kind
      outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0)
               let bs := writev_gathered i.in_mem iovs0
               if total == 0 then ret_outcome (BitVec.ofInt 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if bs.length == 0
               then ret_outcome (errno_ret EFAULT) m
               else
                 match Fs.fs_lookup (m_fs m) p with
                 | none => .unmodeled
                 | some data =>
                     if !(modeled_file_gap data off bs) then .unmodeled
                     else
                     if addr_is_error_b (len_word bs) then .unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                       (.ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdEntry.FdFileRW p (off + len_word bs)))
                             (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m))
                          [])
        )
  | some (FdEntry.FdFileA p off) =>
      outcome_copyins
        (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
        (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
           | .ImpFault => ret_outcome (errno_ret EFAULT) m
           | .ImpInval => ret_outcome (errno_ret EINVAL) m
           | .ImpOk iovs0 =>
               let total := iovs_total (cap_iovecs iovs0)
               let bs := writev_gathered i.in_mem iovs0
               if total == 0 then ret_outcome (BitVec.ofInt 64 0) m
               else if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
               else if bs.length == 0
               then ret_outcome (errno_ret EFAULT) m
               else
                 match Fs.fs_lookup (m_fs m) p with
                 | none => .unmodeled
                 | some data =>
                     if addr_is_error_b (len_word bs) then .unmodeled
                     else outcome_copyins
                       (iov_prefix_accesses (cap_iovecs iovs0) bs.length)
                       (.ok (mkEffect (len_word bs) [] [])
                          (with_fds (fd_insert (m_fds m) fd
                                       (FdEntry.FdFileA p (append_new_pos data bs off)))
                             (with_fs (Fs.fs_set (m_fs m) p
                                         (Fs.file_write data (len_word data) bs)) m))
                          [])
        )
  | some (FdEntry.FdSocket _) => .unmodeled
    -- writing a socket is unmodeled at every count — see
    -- [Sys.Fs.ReadWrite.writev_buf_gap]

/- =========================================================================
   readv
   ========================================================================= -/

/-- `[ReadWrite.readv_spec]`'s witness: one byte scattered into the first
    writable destination iovec on the channel/socket arms, the whole
    readable range on the file arms. -/
def readv_witness (fd iov iovcnt : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      match readable_fd e with
      | none => ret_outcome (errno_ret EBADF) m
        -- the read end has a [RdPipe]; only the O_WRONLY write end
        -- reaches this arm, where -EBADF is the kernel's own answer
      | some r =>
          if readv_heap_iovecb iovcnt
          then .unmodeled
          else
          outcome_copyins
            (import_iovecs_accesses i.in_mem iov (iovcnt32 iovcnt))
          (match import_iovecs i.in_mem iov (iovcnt32 iovcnt) with
          | .ImpFault => ret_outcome (errno_ret EFAULT) m
          | .ImpInval => ret_outcome (errno_ret EINVAL) m
          | .ImpOk iovs0 =>
              let iovs := cap_iovecs iovs0
              let total := iovs_total iovs
              if total == 0 then ret_outcome (BitVec.ofInt 64 0) m
              else
              match r with
              | .RdChannel ch =>
                  match m_stdin m 0 with
                  | none => ret_outcome (BitVec.ofInt 64 0) m
                  | some b =>
                      match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
                      | none => ret_outcome (errno_ret EFAULT) m
                      | some _ =>
                          match scatter_iovecs i.in_wmem iovs
                                  (stream_take_z (m_stdin m) total).1 with
                          | none => .unmodeled
                            -- partially writable destination
                          | some _ =>
                              match scatter_iovecs i.in_wmem iovs [b] with
                              | none => .unmodeled
                                  -- unreachable: byte values do not affect
                                  -- writability, see scatter_iovecs_singleton_some
                              | some writes =>
                                  .ok (mkEffect (BitVec.ofInt 64 1) writes [])
                                     (with_stdin (shift (m_stdin m)) m)
                                     [event.ReadEv ch b]
              | .RdPipe _ => .unmodeled
                -- vectored pipe reads
              | .RdDevNull => ret_outcome (BitVec.ofInt 64 0) m
              | .RdUrandom => .unmodeled
                -- vectored device reads decline
              | .RdDir => ret_outcome (errno_ret EISDIR) m
              | .RdSocket sk =>
                  match sk with
                  | .SkConnected peer ch rx =>
                      match rx 0 with
                      | .fin => ret_outcome (BitVec.ofInt 64 0) m
                      | .rst =>
                          ret_outcome (errno_ret ECONNRESET)
                            (with_fds (fd_insert (m_fds m) fd
                                         (FdEntry.FdSocket
                                            (SockState.SkReset peer ch))) m)
                      | .timedOut =>
                          ret_outcome (errno_ret ETIMEDOUT)
                            (with_fds (fd_insert (m_fds m) fd
                                         (FdEntry.FdSocket
                                            (SockState.SkReset peer ch))) m)
                      | .cons b =>
                          match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ =>
                              match scatter_iovecs i.in_wmem iovs
                                      (net_take_z rx total).1 with
                              | none => .unmodeled
                                -- partially writable destination
                              | some _ =>
                                  match scatter_iovecs i.in_wmem iovs [b] with
                                  | none => .unmodeled
                                      -- unreachable: byte values do not affect
                                      -- writability, see scatter_iovecs_singleton_some
                                  | some writes =>
                                      .ok (mkEffect (BitVec.ofInt 64 1) writes [])
                                         (with_fds (fd_insert (m_fds m) fd
                                            (FdEntry.FdSocket
                                               (SockState.SkConnected peer ch
                                                  (fun n => rx (n + 1))))) m)
                                         [event.ReadEv ch b]
                  | .SkReset _ _ => ret_outcome (BitVec.ofInt 64 0) m
                  | _ => ret_outcome (errno_ret ENOTCONN) m
              | .RdFile p off =>
                  match Fs.fs_lookup (m_fs m) p with
                  | none => .unmodeled
                  | some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := Fs.file_read data off (BitVec.ofInt 64 total)
                      match scatter_iovecs i.in_wmem iovs bs with
                      | some writes =>
                          if addr_is_error_b (len_word bs) then .unmodeled
                          else .ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                    (FdEntry.FdFile p (off + len_word bs))) m) []
                      | none =>
                          match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ => .unmodeled
              | .RdFileRW p off =>
                  -- the [RdFile] arm above, on the O_RDWR kind
                  match Fs.fs_lookup (m_fs m) p with
                  | none => .unmodeled
                  | some data =>
                      if rw_pos_einvalb off total then ret_outcome (errno_ret EINVAL) m
                      else
                      let bs := Fs.file_read data off (BitVec.ofInt 64 total)
                      match scatter_iovecs i.in_wmem iovs bs with
                      | some writes =>
                          if addr_is_error_b (len_word bs) then .unmodeled
                          else .ok (mkEffect (len_word bs) writes [])
                                 (with_fds (fd_insert (m_fds m) fd
                                    (FdEntry.FdFileRW p (off + len_word bs))) m) []
                      | none =>
                          match scatter_iovecs i.in_wmem iovs [BitVec.ofInt 8 0] with
                          | none => ret_outcome (errno_ret EFAULT) m
                          | some _ => .unmodeled
          )

/- =========================================================================
   lseek
   ========================================================================= -/

/-- `[ReadWrite.lseek_spec]`'s witness: the spec is deterministic, so the
    witness is its own answer on every arm. -/
def lseek_witness (fd off whence : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      if decide (SEEK_MAX < (whence.toNat : Int))
      then ret_outcome (errno_ret EINVAL) m
      else
      match e with
      | .FdChannel _ => ret_outcome (errno_ret ESPIPE) m
      | .FdSocket _ => ret_outcome (errno_ret ESPIPE) m
        -- a socket has no offset
      | .FdPipe _ _ => ret_outcome (errno_ret ESPIPE) m
      | .FdDevNull _ _ => ret_outcome (BitVec.ofInt 64 0) m
      | .FdUrandom => ret_outcome (BitVec.ofInt 64 0) m
      | .FdDir => .unmodeled
        -- unmodeled: see [ReadWrite.lseek_spec]
      | .FdFile p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .unmodeled
                -- SEEK_DATA/SEEK_HOLE: unmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => ret_outcome (errno_ret EINVAL) m
                  | some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)) m)
      | .FdFileW p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .unmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => ret_outcome (errno_ret EINVAL) m
                  | some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)) m)
      | .FdFileRW p cur =>
          -- the [FdFileW] arm above, on the O_RDWR kind
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .unmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => ret_outcome (errno_ret EINVAL) m
                  | some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)) m)
      | .FdFileA p cur =>
          match Fs.fs_lookup (m_fs m) p with
          | none => .unmodeled
          | some data =>
              match lseek_base whence cur (len_word data) with
              | none => .unmodeled
              | some base =>
                  match lseek_dest base off with
                  | none => ret_outcome (errno_ret EINVAL) m
                  | some r =>
                      ret_outcome r
                        (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)) m)

/- =========================================================================
   read_urandom — the witness is the spec's own answer
   ========================================================================= -/

theorem read_urandom_witness_ok (buf count : word) (i : SyscallInput) (m : Model) :
    read_urandom buf count i m i m (read_urandom_witness buf count i m) := by
  unfold read_urandom read_urandom_witness
  by_cases h0 : w_is0 count = true
  · simp only [ite_eq_left h0]
    exact pure_ok _ i _
  · simp only [ite_eq_right h0]
    cases hw : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) with
    | none =>
      dsimp only
      exact pure_ok _ i _
    | some w1 =>
      dsimp only
      generalize hr : (stream_take_z (m_urandom m) (rw_count_clamp count)) = r
      by_cases hlen : (!(((r.1).length : Int) == rw_count_clamp count)) = true
      · simp only [ite_eq_left hlen]
        rfl
      · simp only [ite_eq_right hlen]
        cases hw2 : read_bytes_map i.in_wmem buf (len_word r.1) with
        | none =>
          dsimp only
          rfl
        | some w2 =>
          dsimp only
          simp only [set_urandom, seqSpec]
          exact bind_ok (modifySpec (with_urandom r.2))
            (fun _ => LinuxSem.LinuxProcessSem.pure
              (mkEffect (len_word r.1) [(buf, r.1)] []))
            i m () _ [] _ _ [] rfl rfl

/- =========================================================================
   The witness proofs

   The recipe.  A witness and its spec sit in ONE goal (the
   witness is the spec's result argument), so every test the two share is
   rewritten ONCE with `simp only [ite_eq_left h]` / `simp only [ite_eq_right h]` —
   `rw` would rewrite only the outermost occurrence — and the scrutinee
   equations they share are generalised with `generalize … = x at ⊢`
   before `cases`, so that BOTH matches reduce at once.  The spec's
   `bind inputSpec ;; bind getModelSpec` prologue is peeled with
   `bind_step` and `input_ok`/`getModel_ok`, as in the witness proofs
   elsewhere in this layer; the leaves are `pure_ok`, `unmodeled_intro`,
   and
   the `err_ret = ret_outcome (errno_ret …)` rewrite.

   A stuck `match` blocks `simp`, not `rfl`.  A `match` whose
   scrutinee `cases` has just replaced by a constructor is REDUCIBLE but
   not yet REDUCED: `dsimp only` sees no progress, `simp only` cannot
   reach a `record_copyins`/`access_ok_zero` body under it, and plain
   `rfl` still closes the leaf because the two sides are definitionally
   equal.  The delivery proofs therefore `try dsimp only` first (which
   reduces the match when it can) and then use `rfl` for the leaves that
   the macros cannot reach; `unmodeled_intro` (a term, checked up to
   definally equality) is always safe.  The same is why the one-byte
   argument of `choose` is supplied as `⟨[b], ?_, rfl⟩` and its
   conjunction is proved after a `dsimp only` (the `choose` predicate is
   a beta-redex at that point).
   ========================================================================= -/

/-- The one errno leaf of these witnesses: the spec's `err_ret e` and the
    witness's `ret_outcome (errno_ret e)` are the same `pure`. -/
macro "errno_leaf" : tactic =>
  `(tactic| (simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.err_ret,
      LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
      LinuxSem.Checks.Witness.Prelude.ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]))

/-- The one fixed-return leaf: the spec's `ret_only r` and the witness's
    `ret_outcome r`. -/
macro "ret_leaf_w" : tactic =>
  `(tactic| (simp only [LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only,
      LinuxSem.Checks.Witness.Prelude.ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]))

theorem lseek_witness_ok (fd off whence : word) (m : Model) (i : SyscallInput) :
    lseek_spec fd off whence i m (lseek_witness fd off whence m) := by
  unfold lseek_spec lseek_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  simp only [decide_eq_true_eq]
  generalize hq : fd_lookup (m_fds m) fd = q at ⊢
  cases q with
  | none =>
    dsimp only
    errno_leaf
  | some e =>
    dsimp only
    by_cases hw : SEEK_MAX < (whence.toNat : Int)
    · simp only [hw, ite_true]
      errno_leaf
    · simp only [hw, ite_false]
      cases e with
      | FdChannel ch => dsimp only; errno_leaf
      | FdSocket sk => dsimp only; errno_leaf
      | FdPipe id w => dsimp only; errno_leaf
      | FdDevNull rd wr => dsimp only; ret_leaf_w
      | FdUrandom => dsimp only; ret_leaf_w
      | FdDir => dsimp only; exact unmodeled_intro i m
      | FdFile p cur =>
        dsimp only
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => dsimp only; exact unmodeled_intro i m
        | some data =>
          dsimp only
          generalize hb : lseek_base whence cur (len_word data) = b at ⊢
          cases b with
          | none => dsimp only; exact unmodeled_intro i m
          | some base =>
            dsimp only
            generalize hd : lseek_dest base off = d at ⊢
            cases d with
            | none => dsimp only; errno_leaf
            | some r =>
              dsimp only
              refine bind_step (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r))) _ i m () (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFile p r)) m) _ ?_ ?_
              · rfl
              · ret_leaf_w
      | FdFileW p cur =>
        dsimp only
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => dsimp only; exact unmodeled_intro i m
        | some data =>
          dsimp only
          generalize hb : lseek_base whence cur (len_word data) = b at ⊢
          cases b with
          | none => dsimp only; exact unmodeled_intro i m
          | some base =>
            dsimp only
            generalize hd : lseek_dest base off = d at ⊢
            cases d with
            | none => dsimp only; errno_leaf
            | some r =>
              dsimp only
              refine bind_step (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r))) _ i m () (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileW p r)) m) _ ?_ ?_
              · rfl
              · ret_leaf_w
      | FdFileRW p cur =>
        dsimp only
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => dsimp only; exact unmodeled_intro i m
        | some data =>
          dsimp only
          generalize hb : lseek_base whence cur (len_word data) = b at ⊢
          cases b with
          | none => dsimp only; exact unmodeled_intro i m
          | some base =>
            dsimp only
            generalize hd : lseek_dest base off = d at ⊢
            cases d with
            | none => dsimp only; errno_leaf
            | some r =>
              dsimp only
              refine bind_step (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r))) _ i m () (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileRW p r)) m) _ ?_ ?_
              · rfl
              · ret_leaf_w
      | FdFileA p cur =>
        dsimp only
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => dsimp only; exact unmodeled_intro i m
        | some data =>
          dsimp only
          generalize hb : lseek_base whence cur (len_word data) = b at ⊢
          cases b with
          | none => dsimp only; exact unmodeled_intro i m
          | some base =>
            dsimp only
            generalize hd : lseek_dest base off = d at ⊢
            cases d with
            | none => dsimp only; errno_leaf
            | some r =>
              dsimp only
              refine bind_step (set_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r))) _ i m () (with_fds (fd_insert (m_fds m) fd (FdEntry.FdFileA p r)) m) _ ?_ ?_
              · rfl
              · ret_leaf_w

theorem pread64_witness_ok (fd buf count pos : word) (i : SyscallInput) (m : Model) :
    pread64_spec fd buf count pos i m (pread64_witness fd buf count pos i m) := by
  unfold pread64_spec pread64_witness
  by_cases hp : ppos_einvalb pos = true
  · simp only [hp, ite_true]
    errno_leaf
  · simp only [hp, Bool.false_eq_true, ite_false]
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    try dsimp only
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at ⊢
    cases q with
    | none => try dsimp only; errno_leaf
    | some e =>
      cases e with
      | FdChannel ch => try dsimp only; errno_leaf
      | FdFileW p off => try dsimp only; errno_leaf
      | FdFileA p off => try dsimp only; errno_leaf
      | FdPipe id w => try dsimp only; errno_leaf
      | FdSocket sk => try dsimp only; errno_leaf
      | FdDir =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]; errno_leaf
      | FdDevNull rd wr =>
        try dsimp only
        by_cases hrd : (!rd) = true
        · simp only [hrd, ite_true]; errno_leaf
        · simp only [hrd, Bool.false_eq_true, ite_false]
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · simp only [hak, ite_true]; errno_leaf
          · simp only [hak, Bool.false_eq_true, ite_false]
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · simp only [hrp, ite_true]; errno_leaf
            · simp only [hrp, Bool.false_eq_true, ite_false]; ret_leaf_w
      | FdUrandom =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            exact read_urandom_witness_ok buf count i m
      | FdFile p off =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
            cases lk with
            | none => try dsimp only; exact unmodeled_intro i m
            | some data =>
              try dsimp only
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at ⊢
              cases w with
              | none =>
                try dsimp only
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
                cases w1 with
                | none => try dsimp only; errno_leaf
                | some w1 => try dsimp only; exact unmodeled_intro i m
              | some w => try dsimp only; exact pure_ok _ i m
      | FdFileRW p off =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
            cases lk with
            | none => try dsimp only; exact unmodeled_intro i m
            | some data =>
              try dsimp only
              generalize hbs : Fs.file_read data pos (BitVec.ofInt 64 (rw_count_clamp count)) = bs at ⊢
              generalize hw : read_bytes_map i.in_wmem buf (len_word bs) = w at ⊢
              cases w with
              | none =>
                try dsimp only
                generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
                cases w1 with
                | none => try dsimp only; errno_leaf
                | some w1 => try dsimp only; exact unmodeled_intro i m
              | some w => try dsimp only; exact pure_ok _ i m

theorem pwrite64_witness_ok (fd buf count pos : word) (i : SyscallInput) (m : Model) :
    pwrite64_spec fd buf count pos i m (pwrite64_witness fd buf count pos i m) := by
  unfold pwrite64_spec pwrite64_witness
  by_cases hp : ppos_einvalb pos = true
  · simp only [hp, ite_true]
    errno_leaf
  · simp only [hp, Bool.false_eq_true, ite_false]
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    try dsimp only
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    try dsimp only
    generalize hq : fd_lookup (m_fds m) fd = q at ⊢
    cases q with
    | none => try dsimp only; errno_leaf
    | some e =>
      cases e with
      | FdChannel ch => try dsimp only; errno_leaf
      | FdFile p off => try dsimp only; errno_leaf
      | FdFileA p off => try dsimp only; exact unmodeled_intro i m
      | FdPipe id w => try dsimp only; errno_leaf
      | FdSocket sk => try dsimp only; errno_leaf
      | FdDir => try dsimp only; errno_leaf
      | FdUrandom => try dsimp only; errno_leaf
      | FdDevNull rd wr =>
        try dsimp only
        by_cases hwr : (!wr) = true
        · simp only [hwr, ite_true]; errno_leaf
        · simp only [hwr, Bool.false_eq_true, ite_false]
          by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
          · simp only [hak, ite_true]; errno_leaf
          · simp only [hak, Bool.false_eq_true, ite_false]
            by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
            · simp only [hrp, ite_true]; errno_leaf
            · simp only [hrp, Bool.false_eq_true, ite_false]; ret_leaf_w
      | FdFileW p off =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            generalize hbs : write_source i.in_mem buf count = bs at ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · simp only [hz, ite_true]; errno_leaf
            · simp only [hz, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · simp only [hmg, ite_true]; exact unmodeled_intro i m
                · simp only [hmg, Bool.false_eq_true, ite_false]
                  by_cases hw : w_is0 count = true
                  · simp only [hw, ite_true]
                    refine bind_step
                      (set_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) _ rfl ?_
                    exact pure_ok _ i _
                  · simp only [hw, Bool.false_eq_true, ite_false]
                    refine bind_step
                      (set_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) _ rfl ?_
                    exact record_copyins_outcome (pure_ok _ i _)
      | FdFileRW p off =>
        try dsimp only
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb pos (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            generalize hbs : write_source i.in_mem buf count = bs at ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · simp only [hz, ite_true]; errno_leaf
            · simp only [hz, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hmg : (!(modeled_file_gap data pos bs)) = true
                · simp only [hmg, ite_true]; exact unmodeled_intro i m
                · simp only [hmg, Bool.false_eq_true, ite_false]
                  by_cases hw : w_is0 count = true
                  · simp only [hw, ite_true]
                    refine bind_step
                      (set_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) _ rfl ?_
                    exact pure_ok _ i _
                  · simp only [hw, Bool.false_eq_true, ite_false]
                    refine bind_step
                      (set_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data pos bs)) m) _ rfl ?_
                    exact record_copyins_outcome (pure_ok _ i _)

/- =========================================================================
   The range acceptor in `Outcome` form

   `access_ok_zero` (spec side) and `access_ok_zero_witness` (witness side)
   are the same two-armed test, differing only in whether the zero answer
   is a `SysSpec` or an `Outcome`.  The lemma below states that step once,
   so every arm whose two sides call the pair closes with one `exact`. -/

theorem access_ok_zero_witness_ok (buf count : word) (k : SysSpec SyscallEffect)
    (o : Outcome SyscallEffect Model event) (i : SyscallInput) (m : Model)
    (H : k i m o) :
    access_ok_zero buf count k i m (access_ok_zero_witness buf count m o) := by
  unfold access_ok_zero access_ok_zero_witness
  by_cases hak : access_okb buf (count.toNat : Int) = true
  · simp only [hak, ite_true]
    exact H
  · simp only [hak, Bool.false_eq_true, ite_false]
    -- `access_ok_zero` lives in `Sys/Uaccess`, where `err_ret` is
    -- `Uaccess.err_ret` (a definitional copy of `Syscall.err_ret`), so
    -- the two names are unfolded explicitly rather than through
    -- `errno_leaf`.
    simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret,
      LinuxSem.LinuxProcessSem.Sys.Uaccess.ret_only,
      LinuxSem.Checks.Witness.Prelude.ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]

/-- The same acceptor against the OTHER spelling of the range test.  The
    no-transfer arms of `read_spec` (and `write_spec`'s zero-count
    answer) write the test as `if !(access_okb …) then err_ret EFAULT
    else k`, which is `access_ok_zero` with the branches swapped; the
    witness still answers through `access_ok_zero_witness`.  Stated here
    for the same reason as the lemma above. -/
theorem access_ok_zero_witness_ok_not (buf count : word) (k : SysSpec SyscallEffect)
    (o : Outcome SyscallEffect Model event) (i : SyscallInput) (m : Model)
    (H : k i m o) :
    (if !(access_okb buf (count.toNat : Int)) then
        LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret EFAULT
      else k) i m (access_ok_zero_witness buf count m o) := by
  by_cases hak : access_okb buf (count.toNat : Int) = true
  · have hnot : (!(access_okb buf (count.toNat : Int))) = false := by rw [hak]; rfl
    simp only [hnot, Bool.false_eq_true, ite_false]
    simp only [access_ok_zero_witness]
    rw [ite_eq_left hak]
    exact H
  · have hnot : (!(access_okb buf (count.toNat : Int))) = true := by
      cases h : access_okb buf (count.toNat : Int) <;> simp_all
    simp only [hnot, ite_true]
    simp only [access_ok_zero_witness]
    rw [ite_eq_right hak]
    simp only [LinuxSem.LinuxProcessSem.Sys.Uaccess.err_ret,
      LinuxSem.LinuxProcessSem.Sys.Uaccess.ret_only,
      LinuxSem.Checks.Witness.Prelude.ret_outcome, mkEffect,
      LinuxSem.LinuxProcessSem.pure]

/- =========================================================================
   read — the one-byte delivery, bridged into the spec's `choose`
   ========================================================================= -/

theorem read_witness_ok (fd buf count : word) (i : SyscallInput) (m : Model) :
    read_spec fd buf count i m (read_witness fd buf count i m) := by
  unfold read_spec read_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at ⊢
  cases q with
  | none => try dsimp only; errno_leaf
  | some e =>
    cases e with
    | FdFileW p off => try dsimp only; errno_leaf
    | FdFileA p off => try dsimp only; errno_leaf
    | FdDir =>
      try dsimp only
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · simp only [hak, ite_true]; errno_leaf
      · simp only [hak, Bool.false_eq_true, ite_false]; errno_leaf
    | FdDevNull rd wr =>
      try dsimp only
      by_cases hrd : (!rd) = true
      · simp only [hrd, ite_true]; errno_leaf
      · simp only [hrd, Bool.false_eq_true, ite_false]
        exact access_ok_zero_witness_ok_not buf count _ _ i m (by ret_leaf_w)
    | FdUrandom =>
      try dsimp only
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · simp only [hak, ite_true]; errno_leaf
      · simp only [hak, Bool.false_eq_true, ite_false]
        exact read_urandom_witness_ok buf count i m
    | FdChannel ch =>
      try dsimp only
      by_cases hwo : (!(w_is0 ch)) = true
      · simp only [hwo, ite_true]; errno_leaf
      · simp only [hwo, Bool.false_eq_true, ite_false]
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hz : w_is0 count = true
          · simp only [hz, ite_true]; ret_leaf_w
          · simp only [hz, Bool.false_eq_true, ite_false]
            generalize hin : m_stdin m 0 = inp at ⊢
            cases inp with
            | none => try dsimp only; ret_leaf_w
            | some b =>
              try dsimp only
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
              cases w1 with
              | none => try dsimp only; errno_leaf
              | some v1 =>
                try dsimp only
                generalize hw2 : read_bytes_map i.in_wmem buf
                    (len_word (stream_take_z (m_stdin m) (rw_count_clamp count)).1) = w2 at ⊢
                cases w2 with
                | none => try dsimp only; exact unmodeled_intro i m
                | some v2 =>
                  -- THE ONE-BYTE DELIVERY: `bs = [b]`, the head of the
                  -- stream, which the spec's `choose` admits by
                  -- `1 ≤ length ≤ clamp` and `stream_take s 1 = ([b], shift s)`
                  try dsimp only
                  have hzf : w_is0 count = false := by
                    cases h : w_is0 count <;> simp_all
                  have hpos : 0 < count.toNat := w_is0_false_pos count hzf
                  have hclamp : (1 : Int) ≤ rw_count_clamp count :=
                    one_le_rw_count_clamp count hpos
                  have htr : stream_take (m_stdin m) 1 = ([b], shift (m_stdin m)) :=
                    stream_take_one_some hin
                  have hlw : len_word [b] = BitVec.ofInt 64 1 := len_word_singleton b
                  have hP : ((1 : Int) ≤ (([b] : List byte).length : Int) ∧
                      (([b] : List byte).length : Int) ≤ rw_count_clamp count ∧
                      (stream_take (m_stdin m) ([b] : List byte).length).1 = [b] ∧
                      read_bytes_map i.in_wmem buf (len_word ([b] : List byte)) ≠ none) := by
                    refine ⟨by simp, ?_, ?_, ?_⟩
                    · rw [show (([b] : List byte).length : Int) = 1 from rfl]
                      exact hclamp
                    · rw [show (([b] : List byte).length) = 1 from rfl, htr]
                    · rw [hlw, hw1]; simp
                  refine bind_step (choose _) _ i m [b] m _ ⟨[b], ?_, rfl⟩ ?_
                  · dsimp only
                    exact hP
                  · try dsimp only
                    rw [show (([b] : List byte).length) = 1 from rfl]
                    rw [htr, hlw]
                    refine bind_step (set_stdin (shift (m_stdin m))) _ i m ()
                      (with_stdin (shift (m_stdin m)) m) _ rfl ?_
                    exact emit_pure_ok [event.ReadEv ch b]
                      (mkEffect (BitVec.ofInt 64 1) [(buf, [b])] []) i
                      (with_stdin (shift (m_stdin m)) m)
    | FdPipe id w =>
      try dsimp only
      by_cases hw : w = true
      · simp only [hw, ite_true]; errno_leaf
      · simp only [hw, Bool.false_eq_true, ite_false]
        by_cases hrg : (!(modeled_rw_range buf count)) = true
        · simp only [hrg, ite_true]; exact unmodeled_intro i m
        · simp only [hrg, Bool.false_eq_true, ite_false]
          by_cases hz : w_is0 count = true
          · simp only [hz, ite_true]
            exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
          · simp only [hz, Bool.false_eq_true, ite_false]
            generalize hpl : pipe_lookup (m_pipes m) id = pl at ⊢
            cases pl with
            | none => try dsimp only; exact unmodeled_intro i m
            | some pv =>
              obtain ⟨q, used⟩ := pv
              cases q with
              | nil =>
                try dsimp only
                by_cases hlive : pipe_end_live (m_fds m) id true = true
                · simp only [hlive, ite_true]; exact unmodeled_intro i m
                · simp only [hlive, Bool.false_eq_true, ite_false]
                  exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
              | cons b bs0 =>
                try dsimp only
                generalize hdel : pipe_take (b :: bs0) (rw_count_clamp count) = del at ⊢
                generalize hw2 : read_bytes_map i.in_wmem buf (len_word del) = w2 at ⊢
                cases w2 with
                | none =>
                  try dsimp only
                  generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
                  cases w1 with
                  | none => try dsimp only; errno_leaf
                  | some v1 => try dsimp only; exact unmodeled_intro i m
                | some v2 =>
                  try dsimp only
                  refine bind_step (set_pipes (pipe_insert (m_pipes m) id
                      (pipe_consume (b :: bs0, used) del.length))) _ i m ()
                    (with_pipes (pipe_insert (m_pipes m) id
                      (pipe_consume (b :: bs0, used) del.length)) m) _ rfl ?_
                  exact pure_ok _ i _
    | FdSocket sk =>
      try dsimp only
      by_cases hrg : (!(modeled_rw_range buf count)) = true
      · simp only [hrg, ite_true]; exact unmodeled_intro i m
      · simp only [hrg, Bool.false_eq_true, ite_false]
        by_cases hz : w_is0 count = true
        · simp only [hz, ite_true]
          exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
        · simp only [hz, Bool.false_eq_true, ite_false]
          cases sk with
          | SkConnected peer ch rx =>
            try dsimp only
            generalize hrx : rx 0 = st at ⊢
            cases st with
            | fin =>
              try dsimp only
              exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
            | rst =>
              try dsimp only
              simp only [socket_pending_error]
              exact access_ok_zero_witness_ok buf count _ _ i m (by
                refine bind_step (set_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch)))) _ i m ()
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch))) m) _ rfl ?_
                errno_leaf)
            | timedOut =>
              try dsimp only
              simp only [socket_pending_error]
              exact access_ok_zero_witness_ok buf count _ _ i m (by
                refine bind_step (set_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch)))) _ i m ()
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdSocket (SockState.SkReset peer ch))) m) _ rfl ?_
                errno_leaf)
            | cons b =>
              try dsimp only
              generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
              cases w1 with
              | none => try dsimp only; errno_leaf
              | some v1 =>
                try dsimp only
                generalize hw2 : read_bytes_map i.in_wmem buf
                    (len_word (net_take_z rx (rw_count_clamp count)).1) = w2 at ⊢
                cases w2 with
                | none => try dsimp only; exact unmodeled_intro i m
                | some v2 =>
                  try dsimp only
                  have hzf : w_is0 count = false := by
                    cases h : w_is0 count <;> simp_all
                  have hpos : 0 < count.toNat := w_is0_false_pos count hzf
                  have hclamp : (1 : Int) ≤ rw_count_clamp count :=
                    one_le_rw_count_clamp count hpos
                  have htr : net_take rx 1 = ([b], fun n => rx (n + 1)) :=
                    net_take_one_cons hrx
                  have hlw : len_word [b] = BitVec.ofInt 64 1 := len_word_singleton b
                  have hP : ((1 : Int) ≤ (([b] : List byte).length : Int) ∧
                      (([b] : List byte).length : Int) ≤ rw_count_clamp count ∧
                      (net_take rx ([b] : List byte).length).1 = [b] ∧
                      read_bytes_map i.in_wmem buf (len_word ([b] : List byte)) ≠ none) := by
                    refine ⟨by simp, ?_, ?_, ?_⟩
                    · rw [show (([b] : List byte).length : Int) = 1 from rfl]
                      exact hclamp
                    · rw [show (([b] : List byte).length) = 1 from rfl, htr]
                    · rw [hlw, hw1]; simp
                  refine bind_step (choose _) _ i m [b] m _ ⟨[b], ?_, rfl⟩ ?_
                  · dsimp only
                    exact hP
                  · try dsimp only
                    rw [show (([b] : List byte).length) = 1 from rfl]
                    rw [htr, hlw]
                    refine bind_step (set_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdSocket (SockState.SkConnected peer ch
                          (fun n => rx (n + 1)))))) _ i m ()
                      (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdSocket (SockState.SkConnected peer ch
                          (fun n => rx (n + 1))))) m) _ rfl ?_
                    exact emit_pure_ok [event.ReadEv ch b]
                      (mkEffect (BitVec.ofInt 64 1) [(buf, [b])] []) i
                      (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdSocket (SockState.SkConnected peer ch
                          (fun n => rx (n + 1))))) m)
          | SkReset peer ch =>
            try dsimp only
            exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
          | SkFresh =>
            try dsimp only
            exact access_ok_zero_witness_ok buf count _ _ i m (by errno_leaf)
          | SkBound =>
            try dsimp only
            exact access_ok_zero_witness_ok buf count _ _ i m (by errno_leaf)
          | SkListening =>
            try dsimp only
            exact access_ok_zero_witness_ok buf count _ _ i m (by errno_leaf)
    | FdFile p off =>
      try dsimp only
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · simp only [hak, ite_true]; errno_leaf
      · simp only [hak, Bool.false_eq_true, ite_false]
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => try dsimp only; exact unmodeled_intro i m
        | some data =>
          try dsimp only
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs at ⊢
          generalize hw2 : read_bytes_map i.in_wmem buf (len_word bs) = w2 at ⊢
          cases w2 with
          | none =>
            try dsimp only
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
            cases w1 with
            | none => try dsimp only; errno_leaf
            | some v1 => try dsimp only; exact unmodeled_intro i m
          | some v2 =>
            try dsimp only
            refine bind_step (set_fds (fd_insert (m_fds m) fd
                (FdEntry.FdFile p (off + len_word bs)))) _ i m ()
              (with_fds (fd_insert (m_fds m) fd
                (FdEntry.FdFile p (off + len_word bs))) m) _ rfl ?_
            exact pure_ok _ i _
    | FdFileRW p off =>
      try dsimp only
      by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
      · simp only [hak, ite_true]; errno_leaf
      · simp only [hak, Bool.false_eq_true, ite_false]
        generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
        cases lk with
        | none => try dsimp only; exact unmodeled_intro i m
        | some data =>
          try dsimp only
          generalize hbs : Fs.file_read data off (BitVec.ofInt 64 (rw_count_clamp count)) = bs at ⊢
          generalize hw2 : read_bytes_map i.in_wmem buf (len_word bs) = w2 at ⊢
          cases w2 with
          | none =>
            try dsimp only
            generalize hw1 : read_bytes_map i.in_wmem buf (BitVec.ofInt 64 1) = w1 at ⊢
            cases w1 with
            | none => try dsimp only; errno_leaf
            | some v1 => try dsimp only; exact unmodeled_intro i m
          | some v2 =>
            try dsimp only
            refine bind_step (set_fds (fd_insert (m_fds m) fd
                (FdEntry.FdFileRW p (off + len_word bs)))) _ i m ()
              (with_fds (fd_insert (m_fds m) fd
                (FdEntry.FdFileRW p (off + len_word bs))) m) _ rfl ?_
            exact pure_ok _ i _

/- =========================================================================
   `emit` followed by an event-free spec

   `emit_pure_ok` in the witness prelude covers `emit` ;; `pure`, which is
   the shape every read/write delivery ends in.  The `writev` and `write`
   channel arms end in `emit` ;; `record_copyins [(buf, n)] (ret_only …)`
   instead, so the same bind is needed one step more general.  The result's
   event list is `evs ++ []`, which is `evs` by `List.append_nil` — not
   definitionally, hence the `rw`. -/

theorem emit_then_quiet_ok {A : Type} (evs : List event) (c : SysSpec A)
    (i : SyscallInput) (m : Model) (x : A) (m' : Model)
    (H : c i m (.ok x m' [])) :
    bind (emit (M := Model) (I := SyscallInput) (E := event) evs) (fun _ => c)
      i m (.ok x m' evs) := by
  have h := bind_ok (emit (M := Model) (I := SyscallInput) (E := event) evs)
    (fun _ => c) i m () m evs x m' [] (emit_ok evs i m) H
  rw [List.append_nil] at h
  exact h

/- =========================================================================
   write — the full delivery on the channel, mirroring the spec's `choose`
   ========================================================================= -/

theorem write_witness_ok (fd buf count : word) (i : SyscallInput) (m : Model) :
    write_spec fd buf count i m (write_witness fd buf count i m) := by
  unfold write_spec write_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at ⊢
  cases q with
  | none => try dsimp only; errno_leaf
  | some e =>
    cases e with
    | FdFile p off => try dsimp only; errno_leaf
    | FdUrandom => try dsimp only; errno_leaf
    | FdDir => try dsimp only; errno_leaf
    | FdSocket sk => try dsimp only; exact unmodeled_intro i m
    | FdDevNull rd wr =>
      try dsimp only
      by_cases hwr : (!wr) = true
      · simp only [hwr, ite_true]; errno_leaf
      · simp only [hwr, Bool.false_eq_true, ite_false]
        simp only [write_range_gate]
        by_cases hrg : (!(modeled_rw_range buf count)) = true
        · simp only [hrg, ite_true]; exact unmodeled_intro i m
        · simp only [hrg, Bool.false_eq_true, ite_false]
          exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
    | FdChannel ch =>
      try dsimp only
      by_cases hro : w_is0 ch = true
      · simp only [hro, ite_true]; errno_leaf
      · simp only [hro, Bool.false_eq_true, ite_false]
        by_cases hrg : (!(modeled_rw_range buf count)) = true
        · simp only [hrg, ite_true]; exact unmodeled_intro i m
        · simp only [hrg, Bool.false_eq_true, ite_false]
          by_cases hz : w_is0 count = true
          · simp only [hz, ite_true]
            exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
          · simp only [hz, Bool.false_eq_true, ite_false]
            generalize hbs : write_source i.in_mem buf count = bs at ⊢
            by_cases hb0 : (bs.length == 0) = true
            · simp only [hb0, ite_true]; errno_leaf
            · simp only [hb0, Bool.false_eq_true, ite_false]
              -- THE FULL DELIVERY: `ds = bs` is one of the `choose`'s
              -- prefixes, because a prefix of the whole list is the list
              have hne : bs.length ≠ 0 := by
                intro h0; rw [h0] at hb0; simp at hb0
              have hpos : 0 < bs.length := Nat.pos_of_ne_zero hne
              have hle := write_source_length_le i.in_mem buf count
              rw [hbs] at hle
              have hP : ((1 : Int) ≤ (bs.length : Int) ∧
                  (bs.length : Int) ≤ rw_count_clamp count ∧
                  bs = bs.take bs.length) := by
                refine ⟨by exact_mod_cast hpos, hle, ?_⟩
                exact (List.take_length).symm
              refine bind_step (choose _) _ i m bs m _ ⟨bs, ?_, rfl⟩ ?_
              · dsimp only
                exact hP
              · try dsimp only
                exact emit_then_quiet_ok (bs.map (event.WriteEv ch))
                  (record_copyins [(buf, bs.length)]
                    (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                      (len_word bs)))
                  i m _ m (record_copyins_outcome (pure_ok _ i _))
    | FdPipe id w =>
      try dsimp only
      by_cases hw : (!w) = true
      · simp only [hw, ite_true]; errno_leaf
      · simp only [hw, Bool.false_eq_true, ite_false]
        by_cases hrg : (!(modeled_rw_range buf count)) = true
        · simp only [hrg, ite_true]; exact unmodeled_intro i m
        · simp only [hrg, Bool.false_eq_true, ite_false]
          by_cases hz : w_is0 count = true
          · simp only [hz, ite_true]
            exact access_ok_zero_witness_ok buf count _ _ i m (by ret_leaf_w)
          · simp only [hz, Bool.false_eq_true, ite_false]
            by_cases hlive : (!(pipe_end_live (m_fds m) id false)) = true
            · simp only [hlive, ite_true]; exact unmodeled_intro i m
            · simp only [hlive, Bool.false_eq_true, ite_false]
              generalize hpl : pipe_lookup (m_pipes m) id = pl at ⊢
              cases pl with
              | none => try dsimp only; exact unmodeled_intro i m
              | some st =>
                try dsimp only
                by_cases hroom : (!(pipe_write_room st (count.toNat : Int))) = true
                · simp only [hroom, ite_true]; exact unmodeled_intro i m
                · simp only [hroom, Bool.false_eq_true, ite_false]
                  generalize hbs : write_source i.in_mem buf count = bs at ⊢
                  by_cases hshort : (!(bs.length == word_to_nat count)) = true
                  · simp only [hshort, ite_true]; exact unmodeled_intro i m
                  · simp only [hshort, Bool.false_eq_true, ite_false]
                    refine bind_step (set_pipes (pipe_insert (m_pipes m) id
                        (pipe_append st bs))) _ i m ()
                      (with_pipes (pipe_insert (m_pipes m) id
                        (pipe_append st bs)) m) _ rfl ?_
                    exact record_copyins_outcome (pure_ok _ i _)
    | FdFileW p off =>
      try dsimp only
      simp only [write_range_gate]
      by_cases hrg : (!(modeled_rw_range buf count)) = true
      · simp only [hrg, ite_true]; exact unmodeled_intro i m
      · simp only [hrg, Bool.false_eq_true, ite_false]
        simp only [write_file_tail, write_ledger]
        generalize hbs : write_source i.in_mem buf count = bs at ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · simp only [hz, ite_true]; errno_leaf
        · simp only [hz, Bool.false_eq_true, ite_false]
          generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
          cases lk with
          | none =>
            try dsimp only
            by_cases hw : w_is0 count = true
            · simp only [hw, ite_true]
              exact access_ok_zero_witness_ok buf count _ _ i m (unmodeled_intro i m)
            · simp only [hw, Bool.false_eq_true, ite_false]
              exact unmodeled_intro i m
          | some data =>
            try dsimp only
            by_cases hmg : (!(modeled_file_gap data off bs)) = true
            · simp only [hmg, ite_true]
              by_cases hw : w_is0 count = true
              · simp only [hw, ite_true]
                exact access_ok_zero_witness_ok buf count _ _ i m (unmodeled_intro i m)
              · simp only [hw, Bool.false_eq_true, ite_false]
                exact unmodeled_intro i m
            · simp only [hmg, Bool.false_eq_true, ite_false]
              by_cases hw : w_is0 count = true
              · simp only [hw, ite_true]
                exact access_ok_zero_witness_ok buf count _ _ i m (by
                  refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs))) _ i m ()
                    (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                    _ rfl ?_
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileW p (off + len_word bs)))) _
                    i (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m) ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileW p (off + len_word bs)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m)) _ rfl ?_
                  exact pure_ok _ i _)
              · simp only [hw, Bool.false_eq_true, ite_false]
                refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                    (Fs.file_write data off bs))) _ i m ()
                  (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                  _ rfl ?_
                refine bind_step (set_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileW p (off + len_word bs)))) _
                  i (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs)) m) ()
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileW p (off + len_word bs)))
                    (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs)) m)) _ rfl ?_
                exact record_copyins_outcome (pure_ok _ i _)
    | FdFileRW p off =>
      try dsimp only
      simp only [write_range_gate]
      by_cases hrg : (!(modeled_rw_range buf count)) = true
      · simp only [hrg, ite_true]; exact unmodeled_intro i m
      · simp only [hrg, Bool.false_eq_true, ite_false]
        simp only [write_file_tail, write_ledger]
        generalize hbs : write_source i.in_mem buf count = bs at ⊢
        by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
        · simp only [hz, ite_true]; errno_leaf
        · simp only [hz, Bool.false_eq_true, ite_false]
          generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
          cases lk with
          | none =>
            try dsimp only
            by_cases hw : w_is0 count = true
            · simp only [hw, ite_true]
              exact access_ok_zero_witness_ok buf count _ _ i m (unmodeled_intro i m)
            · simp only [hw, Bool.false_eq_true, ite_false]
              exact unmodeled_intro i m
          | some data =>
            try dsimp only
            by_cases hmg : (!(modeled_file_gap data off bs)) = true
            · simp only [hmg, ite_true]
              by_cases hw : w_is0 count = true
              · simp only [hw, ite_true]
                exact access_ok_zero_witness_ok buf count _ _ i m (unmodeled_intro i m)
              · simp only [hw, Bool.false_eq_true, ite_false]
                exact unmodeled_intro i m
            · simp only [hmg, Bool.false_eq_true, ite_false]
              by_cases hw : w_is0 count = true
              · simp only [hw, ite_true]
                exact access_ok_zero_witness_ok buf count _ _ i m (by
                  refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs))) _ i m ()
                    (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                    _ rfl ?_
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileRW p (off + len_word bs)))) _
                    i (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m) ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileRW p (off + len_word bs)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs)) m)) _ rfl ?_
                  exact pure_ok _ i _)
              · simp only [hw, Bool.false_eq_true, ite_false]
                refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                    (Fs.file_write data off bs))) _ i m ()
                  (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                  _ rfl ?_
                refine bind_step (set_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileRW p (off + len_word bs)))) _
                  i (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs)) m) ()
                  (with_fds (fd_insert (m_fds m) fd
                    (FdEntry.FdFileRW p (off + len_word bs)))
                    (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data off bs)) m)) _ rfl ?_
                exact record_copyins_outcome (pure_ok _ i _)
    | FdFileA p off =>
      try dsimp only
      simp only [write_range_gate]
      by_cases hrg : (!(modeled_rw_range buf count)) = true
      · simp only [hrg, ite_true]; exact unmodeled_intro i m
      · simp only [hrg, Bool.false_eq_true, ite_false]
        by_cases hak : (!(access_okb buf (count.toNat : Int))) = true
        · simp only [hak, ite_true]; errno_leaf
        · simp only [hak, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb off (count.toNat : Int) = true
          · simp only [hrp, ite_true]; errno_leaf
          · simp only [hrp, Bool.false_eq_true, ite_false]
            simp only [write_file_tail, write_ledger]
            generalize hbs : write_source i.in_mem buf count = bs at ⊢
            by_cases hz : (!(w_is0 count) && (bs.length == 0)) = true
            · simp only [hz, ite_true]; errno_leaf
            · simp only [hz, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none =>
                try dsimp only
                by_cases hw : w_is0 count = true
                · simp only [hw, ite_true]
                  exact access_ok_zero_witness_ok buf count _ _ i m (unmodeled_intro i m)
                · simp only [hw, Bool.false_eq_true, ite_false]
                  exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hw : w_is0 count = true
                · simp only [hw, ite_true]
                  exact access_ok_zero_witness_ok buf count _ _ i m (by
                    refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs)) m) _ rfl ?_
                    refine bind_step (set_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileA p (append_new_pos data bs off)))) _
                      i (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data (len_word data) bs)) m) ()
                      (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileA p (append_new_pos data bs off)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data (len_word data) bs)) m)) _ rfl ?_
                    exact pure_ok _ i _)
                · simp only [hw, Bool.false_eq_true, ite_false]
                  refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data (len_word data) bs))) _ i m ()
                    (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data (len_word data) bs)) m) _ rfl ?_
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileA p (append_new_pos data bs off)))) _
                    i (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs)) m) ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileA p (append_new_pos data bs off)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs)) m)) _ rfl ?_
                  exact record_copyins_outcome (pure_ok _ i _)

/- =========================================================================
   writev — one byte on the channel, the whole gathering on the file kinds
   ========================================================================= -/

theorem writev_witness_ok (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    writev_spec fd iov iovcnt i m (writev_witness fd iov iovcnt i m) := by
  unfold writev_spec writev_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at ⊢
  cases q with
  | none => try dsimp only; rfl
  | some e =>
    cases e with
    | FdFile p off => try dsimp only; rfl
    | FdDir => try dsimp only; rfl
    | FdUrandom => try dsimp only; rfl
    | FdSocket sk => try dsimp only; exact unmodeled_intro i m
    | FdChannel ch =>
      try dsimp only
      by_cases hro : w_is0 ch = true
      · simp only [hro, ite_true]; rfl
      · simp only [hro, Bool.false_eq_true, ite_false]
        apply record_copyins_outcome
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
        cases imp with
        | ImpFault => try dsimp only; rfl
        | ImpInval => try dsimp only; rfl
        | ImpOk iovs0 =>
          try dsimp only
          generalize hbs : writev_gathered i.in_mem iovs0 = bs at ⊢
          generalize htot : iovs_total (cap_iovecs iovs0) = total at ⊢
          by_cases ht : (total == 0) = true
          · simp only [ht, ite_true]; rfl
          · simp only [ht, Bool.false_eq_true, ite_false]
            by_cases hb0 : (bs.length == 0) = true
            · simp only [hb0, ite_true]; rfl
            · simp only [hb0, Bool.false_eq_true, ite_false]
              by_cases herr : addr_is_error_b (len_word bs) = true
              · simp only [herr, ite_true]; exact unmodeled_intro i m
              · simp only [herr, Bool.false_eq_true, ite_false]
                -- THE ONE-BYTE DELIVERY: `ds = bs.take 1`
                have hne : bs.length ≠ 0 := by
                  intro h0; rw [h0] at hb0; simp at hb0
                have hge : 1 ≤ bs.length := Nat.pos_of_ne_zero hne
                have hlen1 : (bs.take 1).length = 1 := by
                  rw [List.length_take, Nat.min_eq_left hge]
                have hP : ((1 : Int) ≤ ((bs.take 1).length : Int) ∧
                    ((bs.take 1).length : Int) < two_pow_64 ∧
                    addr_is_error_b (len_word (bs.take 1)) = false ∧
                    bs.take 1 = bs.take (bs.take 1).length) := by
                  refine ⟨by rw [hlen1]; decide, ?_,
                    addr_is_error_b_len_word_take_one bs, ?_⟩
                  · rw [hlen1]; unfold two_pow_64; decide
                  · rw [hlen1]
                refine bind_step (choose _) _ i m (bs.take 1) m _
                  ⟨bs.take 1, ?_, rfl⟩ ?_
                · dsimp only
                  exact hP
                · try dsimp only
                  exact emit_then_quiet_ok ((bs.take 1).map (event.WriteEv ch))
                    (record_copyins
                      (iov_prefix_accesses (cap_iovecs iovs0) (bs.take 1).length)
                      (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                        (len_word (bs.take 1))))
                    i m _ m (record_copyins_outcome (pure_ok _ i _))
    | FdPipe id w =>
      try dsimp only
      by_cases hw : (!w) = true
      · simp only [hw, ite_true]; rfl
      · simp only [hw, Bool.false_eq_true, ite_false]
        apply record_copyins_outcome
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
        cases imp with
        | ImpFault => try dsimp only; rfl
        | ImpInval => try dsimp only; rfl
        | ImpOk iovs0 =>
          try dsimp only
          by_cases ht : (iovs_total (cap_iovecs iovs0) == 0) = true
          · simp only [ht, ite_true]; rfl
          · simp only [ht, Bool.false_eq_true, ite_false]
            exact unmodeled_intro i m
    | FdDevNull rd wr =>
      try dsimp only
      by_cases hwr : (!wr) = true
      · simp only [hwr, ite_true]; rfl
      · simp only [hwr, Bool.false_eq_true, ite_false]
        apply record_copyins_outcome
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
        cases imp with
        | ImpFault => try dsimp only; rfl
        | ImpInval => try dsimp only; rfl
        | ImpOk iovs0 => try dsimp only; rfl
    | FdFileW p off =>
      try dsimp only
      apply record_copyins_outcome
      generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
      cases imp with
      | ImpFault => try dsimp only; rfl
      | ImpInval => try dsimp only; rfl
      | ImpOk iovs0 =>
        try dsimp only
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at ⊢
        generalize htot : iovs_total (cap_iovecs iovs0) = total at ⊢
        by_cases ht : (total == 0) = true
        · simp only [ht, ite_true]; rfl
        · simp only [ht, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb off total = true
          · simp only [hrp, ite_true]; rfl
          · simp only [hrp, Bool.false_eq_true, ite_false]
            by_cases hb0 : (bs.length == 0) = true
            · simp only [hb0, ite_true]; rfl
            · simp only [hb0, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · simp only [hmg, ite_true]; exact unmodeled_intro i m
                · simp only [hmg, Bool.false_eq_true, ite_false]
                  by_cases herr : addr_is_error_b (len_word bs) = true
                  · simp only [herr, ite_true]; exact unmodeled_intro i m
                  · simp only [herr, Bool.false_eq_true, ite_false]
                    refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                      _ rfl ?_
                    refine bind_step (set_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileW p (off + len_word bs)))) _
                      i (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m) ()
                      (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m)) _ rfl ?_
                    exact record_copyins_outcome (pure_ok _ i _)
    | FdFileRW p off =>
      try dsimp only
      apply record_copyins_outcome
      generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
      cases imp with
      | ImpFault => try dsimp only; rfl
      | ImpInval => try dsimp only; rfl
      | ImpOk iovs0 =>
        try dsimp only
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at ⊢
        generalize htot : iovs_total (cap_iovecs iovs0) = total at ⊢
        by_cases ht : (total == 0) = true
        · simp only [ht, ite_true]; rfl
        · simp only [ht, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb off total = true
          · simp only [hrp, ite_true]; rfl
          · simp only [hrp, Bool.false_eq_true, ite_false]
            by_cases hb0 : (bs.length == 0) = true
            · simp only [hb0, ite_true]; rfl
            · simp only [hb0, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hmg : (!(modeled_file_gap data off bs)) = true
                · simp only [hmg, ite_true]; exact unmodeled_intro i m
                · simp only [hmg, Bool.false_eq_true, ite_false]
                  by_cases herr : addr_is_error_b (len_word bs) = true
                  · simp only [herr, ite_true]; exact unmodeled_intro i m
                  · simp only [herr, Bool.false_eq_true, ite_false]
                    refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data off bs))) _ i m ()
                      (with_fs (Fs.fs_set (m_fs m) p (Fs.file_write data off bs)) m)
                      _ rfl ?_
                    refine bind_step (set_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileRW p (off + len_word bs)))) _
                      i (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m) ()
                      (with_fds (fd_insert (m_fds m) fd
                        (FdEntry.FdFileRW p (off + len_word bs)))
                        (with_fs (Fs.fs_set (m_fs m) p
                          (Fs.file_write data off bs)) m)) _ rfl ?_
                    exact record_copyins_outcome (pure_ok _ i _)
    | FdFileA p off =>
      try dsimp only
      apply record_copyins_outcome
      generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
      cases imp with
      | ImpFault => try dsimp only; rfl
      | ImpInval => try dsimp only; rfl
      | ImpOk iovs0 =>
        try dsimp only
        generalize hbs : writev_gathered i.in_mem iovs0 = bs at ⊢
        generalize htot : iovs_total (cap_iovecs iovs0) = total at ⊢
        by_cases ht : (total == 0) = true
        · simp only [ht, ite_true]; rfl
        · simp only [ht, Bool.false_eq_true, ite_false]
          by_cases hrp : rw_pos_einvalb off total = true
          · simp only [hrp, ite_true]; rfl
          · simp only [hrp, Bool.false_eq_true, ite_false]
            by_cases hb0 : (bs.length == 0) = true
            · simp only [hb0, ite_true]; rfl
            · simp only [hb0, Bool.false_eq_true, ite_false]
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases herr : addr_is_error_b (len_word bs) = true
                · simp only [herr, ite_true]; exact unmodeled_intro i m
                · simp only [herr, Bool.false_eq_true, ite_false]
                  refine bind_step (set_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data (len_word data) bs))) _ i m ()
                    (with_fs (Fs.fs_set (m_fs m) p
                      (Fs.file_write data (len_word data) bs)) m) _ rfl ?_
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileA p (append_new_pos data bs off)))) _
                    i (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs)) m) ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdFileA p (append_new_pos data bs off)))
                      (with_fs (Fs.fs_set (m_fs m) p
                        (Fs.file_write data (len_word data) bs)) m)) _ rfl ?_
                  exact record_copyins_outcome (pure_ok _ i _)

/- =========================================================================
   readv — one byte scattered on the channel/socket, the whole read on a
   file
   ========================================================================= -/

theorem readv_witness_ok (fd iov iovcnt : word) (i : SyscallInput) (m : Model) :
    readv_spec fd iov iovcnt i m (readv_witness fd iov iovcnt i m) := by
  unfold readv_spec readv_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  try dsimp only
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hq : fd_lookup (m_fds m) fd = q at ⊢
  cases q with
  | none => try dsimp only; rfl
  | some e =>
    try dsimp only
    generalize hrd : readable_fd e = rf at ⊢
    cases rf with
    | none => try dsimp only; rfl
    | some r =>
      try dsimp only
      by_cases hheap : readv_heap_iovecb iovcnt = true
      · simp only [hheap, ite_true]; exact unmodeled_intro i m
      · simp only [hheap, Bool.false_eq_true, ite_false]
        apply record_copyins_outcome
        generalize himp : import_iovecs i.in_mem iov (iovcnt32 iovcnt) = imp at ⊢
        cases imp with
        | ImpFault => try dsimp only; rfl
        | ImpInval => try dsimp only; rfl
        | ImpOk iovs0 =>
          unfold readv_imported
          try dsimp only
          by_cases ht : (iovs_total (cap_iovecs iovs0) == 0) = true
          · simp only [ht, ite_true]; rfl
          · simp only [ht, Bool.false_eq_true, ite_false]
            cases r with
            | RdChannel ch =>
              try dsimp only
              generalize hin : m_stdin m 0 = inp at ⊢
              cases inp with
              | none => try dsimp only; rfl
              | some b =>
                try dsimp only
                generalize h0 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                    [BitVec.ofInt 8 0] = w0 at ⊢
                cases w0 with
                | none => try dsimp only; rfl
                | some v0 =>
                  try dsimp only
                  generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                      (stream_take_z (m_stdin m)
                        (iovs_total (cap_iovecs iovs0))).1 = w1 at ⊢
                  cases w1 with
                  | none => try dsimp only; exact unmodeled_intro i m
                  | some v1 =>
                    try dsimp only
                    have htne : (iovs_total (cap_iovecs iovs0) == 0) = false := by
                      cases h : (iovs_total (cap_iovecs iovs0) == 0) <;> simp_all
                    have hpos : (1 : Int) ≤ iovs_total (cap_iovecs iovs0) := by
                      have hne : iovs_total (cap_iovecs iovs0) ≠ 0 := by
                        intro h0; rw [h0] at htne; simp at htne
                      have hnn : 0 ≤ iovs_total (cap_iovecs iovs0) :=
                        iovs_total_nonneg _
                      omega
                    have htr : stream_take (m_stdin m) 1 = ([b], shift (m_stdin m)) :=
                      stream_take_one_some hin
                    have hlw : len_word [b] = BitVec.ofInt 64 1 := len_word_singleton b
                    -- the one-byte scatter succeeds or fails by the VECTOR,
                    -- not by the byte's value, and the zero-byte probe above
                    -- already succeeded
                    have hne2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                        ([b] : List byte) ≠ none := by
                      obtain ⟨w', hw'⟩ := scatter_iovecs_singleton_some i.in_wmem
                        (cap_iovecs iovs0) (BitVec.ofInt 8 0) v0 b h0
                      intro hcontra
                      rw [hcontra] at hw'
                      simp at hw'
                    have hP : ((1 : Int) ≤ (([b] : List byte).length : Int) ∧
                        (([b] : List byte).length : Int)
                          ≤ iovs_total (cap_iovecs iovs0) ∧
                        (stream_take (m_stdin m) ([b] : List byte).length).1 = [b] ∧
                        scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                          ([b] : List byte) ≠ none) := by
                      refine ⟨by simp, ?_, ?_, hne2⟩
                      · rw [show (([b] : List byte).length : Int) = 1 from rfl]
                        exact hpos
                      · rw [show (([b] : List byte).length) = 1 from rfl, htr]
                    refine bind_step (choose _) _ i m [b] m _ ⟨[b], ?_, rfl⟩ ?_
                    · dsimp only
                      exact hP
                    · try dsimp only
                      generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                          [b] = w2 at ⊢
                      cases w2 with
                      | none => exact absurd h2 hne2
                      | some writes =>
                        try dsimp only
                        rw [show (([b] : List byte).length) = 1 from rfl]
                        rw [htr, hlw]
                        refine bind_step (set_stdin (shift (m_stdin m))) _ i m ()
                          (with_stdin (shift (m_stdin m)) m) _ rfl ?_
                        exact emit_pure_ok [event.ReadEv ch b]
                          (mkEffect (BitVec.ofInt 64 1) writes []) i
                          (with_stdin (shift (m_stdin m)) m)
            | RdSocket sk =>
              try dsimp only
              cases sk with
              | SkConnected peer ch rx =>
                try dsimp only
                generalize hrx : rx 0 = st at ⊢
                cases st with
                | fin => try dsimp only; rfl
                | rst =>
                  try dsimp only
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch)))) _ i m ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch))) m) _ rfl ?_
                  rfl
                | timedOut =>
                  try dsimp only
                  refine bind_step (set_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch)))) _ i m ()
                    (with_fds (fd_insert (m_fds m) fd
                      (FdEntry.FdSocket (SockState.SkReset peer ch))) m) _ rfl ?_
                  rfl
                | cons b =>
                  try dsimp only
                  generalize h0 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                      [BitVec.ofInt 8 0] = w0 at ⊢
                  cases w0 with
                  | none => try dsimp only; rfl
                  | some v0 =>
                    try dsimp only
                    generalize h1 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                        (net_take_z rx (iovs_total (cap_iovecs iovs0))).1 = w1 at ⊢
                    cases w1 with
                    | none => try dsimp only; exact unmodeled_intro i m
                    | some v1 =>
                      try dsimp only
                      have htne : (iovs_total (cap_iovecs iovs0) == 0) = false := by
                        cases h : (iovs_total (cap_iovecs iovs0) == 0) <;> simp_all
                      have hpos : (1 : Int) ≤ iovs_total (cap_iovecs iovs0) := by
                        have hne : iovs_total (cap_iovecs iovs0) ≠ 0 := by
                          intro h0; rw [h0] at htne; simp at htne
                        have hnn : 0 ≤ iovs_total (cap_iovecs iovs0) :=
                          iovs_total_nonneg _
                        omega
                      have htr : net_take rx 1 = ([b], fun n => rx (n + 1)) :=
                        net_take_one_cons hrx
                      have hlw : len_word [b] = BitVec.ofInt 64 1 := len_word_singleton b
                      have hne2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                          ([b] : List byte) ≠ none := by
                        obtain ⟨w', hw'⟩ := scatter_iovecs_singleton_some i.in_wmem
                          (cap_iovecs iovs0) (BitVec.ofInt 8 0) v0 b h0
                        intro hcontra
                        rw [hcontra] at hw'
                        simp at hw'
                      have hP : ((1 : Int) ≤ (([b] : List byte).length : Int) ∧
                          (([b] : List byte).length : Int)
                            ≤ iovs_total (cap_iovecs iovs0) ∧
                          (net_take rx ([b] : List byte).length).1 = [b] ∧
                          scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                            ([b] : List byte) ≠ none) := by
                        refine ⟨by simp, ?_, ?_, hne2⟩
                        · rw [show (([b] : List byte).length : Int) = 1 from rfl]
                          exact hpos
                        · rw [show (([b] : List byte).length) = 1 from rfl, htr]
                      refine bind_step (choose _) _ i m [b] m _ ⟨[b], ?_, rfl⟩ ?_
                      · dsimp only
                        exact hP
                      · try dsimp only
                        generalize h2 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                            [b] = w2 at ⊢
                        cases w2 with
                        | none => exact absurd h2 hne2
                        | some writes =>
                          try dsimp only
                          rw [show (([b] : List byte).length) = 1 from rfl]
                          rw [htr, hlw]
                          refine bind_step (set_fds (fd_insert (m_fds m) fd
                              (FdEntry.FdSocket (SockState.SkConnected peer ch
                                (fun n => rx (n + 1)))))) _ i m ()
                            (with_fds (fd_insert (m_fds m) fd
                              (FdEntry.FdSocket (SockState.SkConnected peer ch
                                (fun n => rx (n + 1))))) m) _ rfl ?_
                          exact emit_pure_ok [event.ReadEv ch b]
                            (mkEffect (BitVec.ofInt 64 1) writes []) i
                            (with_fds (fd_insert (m_fds m) fd
                              (FdEntry.FdSocket (SockState.SkConnected peer ch
                                (fun n => rx (n + 1))))) m)
              | SkReset peer ch => try dsimp only; rfl
              | SkFresh => try dsimp only; rfl
              | SkBound => try dsimp only; rfl
              | SkListening => try dsimp only; rfl
            | RdDir => try dsimp only; rfl
            | RdPipe id => try dsimp only; exact unmodeled_intro i m
            | RdDevNull => try dsimp only; rfl
            | RdUrandom => try dsimp only; exact unmodeled_intro i m
            | RdFile p off =>
              try dsimp only
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hrp : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
                · simp only [hrp, ite_true]; rfl
                · simp only [hrp, Bool.false_eq_true, ite_false]
                  generalize hbs : Fs.file_read data off
                      (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at ⊢
                  generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at ⊢
                  cases sc with
                  | some writes =>
                    try dsimp only
                    by_cases herr : addr_is_error_b (len_word bs) = true
                    · simp only [herr, ite_true]; exact unmodeled_intro i m
                    · simp only [herr, Bool.false_eq_true, ite_false]
                      refine bind_step (set_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFile p (off + len_word bs)))) _ i m ()
                        (with_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFile p (off + len_word bs))) m) _ rfl ?_
                      exact pure_ok _ i _
                  | none =>
                    try dsimp only
                    generalize h0 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                        [BitVec.ofInt 8 0] = w0 at ⊢
                    cases w0 with
                    | none => try dsimp only; rfl
                    | some v0 => try dsimp only; exact unmodeled_intro i m
            | RdFileRW p off =>
              try dsimp only
              generalize hfs : Fs.fs_lookup (m_fs m) p = lk at ⊢
              cases lk with
              | none => try dsimp only; exact unmodeled_intro i m
              | some data =>
                try dsimp only
                by_cases hrp : rw_pos_einvalb off (iovs_total (cap_iovecs iovs0)) = true
                · simp only [hrp, ite_true]; rfl
                · simp only [hrp, Bool.false_eq_true, ite_false]
                  generalize hbs : Fs.file_read data off
                      (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0))) = bs at ⊢
                  generalize hsc : scatter_iovecs i.in_wmem (cap_iovecs iovs0) bs = sc at ⊢
                  cases sc with
                  | some writes =>
                    try dsimp only
                    by_cases herr : addr_is_error_b (len_word bs) = true
                    · simp only [herr, ite_true]; exact unmodeled_intro i m
                    · simp only [herr, Bool.false_eq_true, ite_false]
                      refine bind_step (set_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFileRW p (off + len_word bs)))) _ i m ()
                        (with_fds (fd_insert (m_fds m) fd
                          (FdEntry.FdFileRW p (off + len_word bs))) m) _ rfl ?_
                      exact pure_ok _ i _
                  | none =>
                    try dsimp only
                    generalize h0 : scatter_iovecs i.in_wmem (cap_iovecs iovs0)
                        [BitVec.ofInt 8 0] = w0 at ⊢
                    cases w0 with
                    | none => try dsimp only; rfl
                    | some v0 => try dsimp only; exact unmodeled_intro i m
