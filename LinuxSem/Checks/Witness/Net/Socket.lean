/-
  * LinuxProcessSem.Checks.Witness.Net.Socket — the socket (198), bind (200),
      listen (201), accept (202), getsockname (204), getpeername (205),
      sendto (206), setsockopt (208), getsockopt (209), shutdown (210),
      sendmsg (211), accept4 (242) witnesses, and their proofs

  Answers to Linux [net/socket.c]: this file holds the witnesses for the
  syscalls defined there, and no others.

  [Checks/Progress.lean] keeps the dispatcher and re-exports this module. A
  witness here exhibits one admissible outcome for a spec in the matching
  [Sys] module, which is what progress is proved from.

  A witness answers with `Outcome A Model event`, and the spec monad
  `Sys A` is `SysSpec A`; `ret_outcome` / `witness_errno` /
  `errno_head_witness` are `Checks.Witness.Prelude`'s.  A coinductive
  `NCons _ _` / `NFin` socket-stream pattern is the observation at index
  0, as in `Checks/Sys/Net/Socket.lean`.

  `access_ok_zero_witness` is `Checks/Witness/Fs/ReadWrite.lean`'s; it is
  also stated here, privately, with the same statement,
  so this module does not depend on a file outside its own import cone.
  That copy can go once the witness modules are wired together.

  Each proof walks the spec's readers with `bind_step`, closes each arm
  with `pure_ok` / `unmodeled_intro`, and uses
  `record_copyins_outcome` wherever the arm records a ledger; see the
  checkers' proofs in `Checks/Sys/Net/Socket.lean` for the same case trees.

  PROOF NOTE (the case trees).  `split` peels the scrutinee it can, and
  which one that is is not the written nesting order: on `sendmsg` it is
  the 56-byte header read, then the six field reads, then the `if`s, and
  the `fd_lookup` arm last.  A `SysSpec`-valued match (`fd_lookup`,
  `copy_iovecs_aux`) is the awkward one: what `split` leaves behind is
  `match <constructor> with …` under a metavariable motive, which a
  leaf's `exact` cannot see through, so `sendmsg_witness_ok` takes those
  two by `generalize` + `cases` and forces the iota step with one
  `simp only []` afterwards.  The `if`s have sort-valued arms, so
  `split` peels those directly and on both sides at once, and the `-`
  errno (`ret_outcome_ok`) and ledger (`record_copyins_outcome`) leaves
  then go through unchanged.
-/
import LinuxSem.Checks.Witness.Prelude
import LinuxSem.LinuxProcessSem.Sys.Net.Socket

namespace LinuxSem.Checks.Witness.Net.Socket

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
  (rw_bytes_max modeled_rw_count access_ok_zero)
open LinuxSem.LinuxProcessSem.Sys.Fs.File (z_ldiff)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (UIO_FASTIOV)
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.Checks.Witness.Prelude

/-- The syscall layer's 32-bit argument truncation — see the checker
    file's copy of the same abbreviation. -/
private abbrev abi_low32 (w : word) : word :=
  LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32 w

/-- `Uaccess.access_ok_zero` as a witness: the zero answer where the
    model is sure the range passed `access_ok`, -EFAULT where it is sure
    it did not, and the fail-closed decline in between. -/
private def access_ok_zero_witness (buf count : word) (m : Model)
    (o : Outcome SyscallEffect Model event) : Outcome SyscallEffect Model event :=
  if access_okb buf (count.toNat : Int) then o else ret_outcome (errno_ret EFAULT) m

/- =========================================================================
   socket (198) — witness: the concrete argument errno where the spec has
   one, the environment-failure branch (errno 12) where it succeeds, or
   the fail-closed `Unmodeled`
   ========================================================================= -/

/-- As `openat_witness` does, this takes the ERRNO side of the `alt` on
    every arm that can succeed: `socket_errnos` is headed by ENOMEM, so
    `errno_head_witness` supplies the outcome and the success branch's
    `lowest_fd` never has to be shown inhabited. -/
def socket_witness (domain type protocol : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  let tu : Int := ((abi_low32 type).toNat : Int)
  let flagbits : Int := z_ldiff tu SOCK_TYPE_MASK
  if !(z_ldiff flagbits (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
  then ret_outcome (errno_ret EINVAL) m          -- unknown flag bit
  else if !(z_land flagbits SOCK_NONBLOCK == 0)
  then .unmodeled                                -- SOCK_NONBLOCK: no O_NONBLOCK notion
  else
    let ty : Int := z_land tu SOCK_TYPE_MASK
    let fam : Int := sint32 domain
    let pro : Int := sint32 protocol
    if decide (fam < 0) || decide (NPROTO ≤ fam)
    then ret_outcome (errno_ret EAFNOSUPPORT) m
    else if decide (SOCK_MAX ≤ ty) then ret_outcome (errno_ret EINVAL) m
    else if !(fam == AF_INET) then .unmodeled  -- registration the model cannot know
    else if ty == SOCK_PACKET then .unmodeled  -- rewritten to PF_PACKET above the
                                               -- protocol range — see `socket_spec`
    else if decide (pro < 0) || decide (IPPROTO_MAX ≤ pro)
    then ret_outcome (errno_ret EINVAL) m
    else if ty == SOCK_STREAM then
      if (pro == IPPROTO_SCTP) || (pro == IPPROTO_MPTCP) then .unmodeled
      else if !((pro == IPPROTO_IP) || (pro == IPPROTO_TCP))
      then ret_outcome (errno_ret EPROTONOSUPPORT) m
      else ret_outcome (errno_ret witness_errno) m   -- env-failure branch
    else if (ty == SOCK_DGRAM) || (ty == SOCK_RAW)
    then .unmodeled                     -- SOCK_DGRAM / SOCK_RAW; SOCK_PACKET is above
    else if (ty == SOCK_SEQPACKET) || (ty == SOCK_DCCP)
    then .unmodeled                     -- sctp and dccp register these
    else ret_outcome (errno_ret ESOCKTNOSUPPORT) m

/- =========================================================================
   bind (200) — witness: the concrete argument errno, the -EADDRINUSE
   failure branch where the spec succeeds, or the fail-closed `Unmodeled`
   ========================================================================= -/

def bind_witness (fd addrp addrlen : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdSocket sk) =>
      let al : Int := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al)
      then ret_outcome (errno_ret EINVAL) m
      else if al == 0 then ret_outcome (errno_ret EINVAL) m
      else
      match read_bytes_map i.in_mem addrp (BitVec.ofInt 64 al) with
      | none => ret_outcome (errno_ret EFAULT) m
      | some bs =>
          -- PAST THE COPY: `move_addr_to_kernel` has moved `al` bytes, so
          -- every outcome exhibited below has to carry the ledger
          -- `bind_spec` records there.  `outcome_copyins` attaches it and
          -- leaves an `.unmodeled` alone, which is what `record_copyins`
          -- does on the spec side.
          outcome_copyins [(addrp, al.toNat)]
          (if decide (al < SOCKADDR_IN_SIZE) then ret_outcome (errno_ret EINVAL) m
           else
            if !((sa_family_of bs == AF_INET)
                 || ((sa_family_of bs == AF_UNSPEC)
                       && (sin_addr_of bs == INADDR_ANY)))
            then ret_outcome (errno_ret EAFNOSUPPORT) m
            else if !(sin_addr_of bs == INADDR_ANY) then .unmodeled
            else if !(sin_port_of bs == 0) then .unmodeled
            else
              match sk with
              | .SkFresh => ret_outcome (errno_ret EADDRINUSE) m  -- `get_port` can fail
              | .SkBound | .SkListening => ret_outcome (errno_ret EINVAL) m
              | .SkConnected _ _ rx =>
                  match rx 0 with
                  | .cons _ | .fin => ret_outcome (errno_ret EINVAL) m
                  | .rst | .timedOut => .unmodeled
              | .SkReset _ _ => .unmodeled)
  | some _ => ret_outcome (errno_ret ENOTSOCK) m

/- =========================================================================
   listen (201) — deterministic except on a fresh socket, where the
   autobind's -EADDRINUSE is the witness
   ========================================================================= -/

def listen_witness (fd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdSocket sk) =>
      match sk with
      | .SkConnected _ _ _ => ret_outcome (errno_ret EINVAL) m
      | .SkReset _ _ => ret_outcome (errno_ret EINVAL) m
      | .SkListening => ret_outcome (BitVec.ofInt 64 0) m       -- re-listen
      | .SkBound =>
          ret_outcome (BitVec.ofInt 64 0)
            (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m)
      | .SkFresh => ret_outcome (errno_ret EADDRINUSE) m   -- the autobind's failure
  | some _ => ret_outcome (errno_ret ENOTSOCK) m

/- =========================================================================
   accept4 (242), which accept (202) reaches with flags = 0 — witness:
   the concrete fd/flag errno, the environment-failure branch (errno 12)
   where a connection would be handed over, or the fail-closed `Unmodeled`
   ========================================================================= -/

/-- Taking the errno side of the `alt` is what keeps this cheap: the
    success branch would have to exhibit a free fd AND the accepted
    socket's state, and `accept_errnos` is headed by ENOMEM. -/
def accept4_witness (fd addrp flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      let fl : Int := ((abi_low32 flags).toNat : Int)
      if !(z_ldiff fl (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
      then ret_outcome (errno_ret EINVAL) m
      else if !(z_land fl SOCK_NONBLOCK == 0) then .unmodeled
      else
      match e with
      | .FdSocket sk =>
          if !(w_is0 addrp) then .unmodeled   -- the peer address is not reported
          else
          match sk with
          | .SkListening => ret_outcome (errno_ret witness_errno) m
          | _ => ret_outcome (errno_ret EINVAL) m
      | _ => ret_outcome (errno_ret ENOTSOCK) m

/- =========================================================================
   connect (203) — wholly deterministic: every answered arm is a fixed
   errno or 0, and the attempt itself is declined, so the witness is a
   mirror of the spec rather than a choice among its alternatives
   ========================================================================= -/

def connect_witness (fd addrp addrlen : word) (i : SyscallInput)
    (m : Model) : Outcome SyscallEffect Model event :=
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some e =>
      let al : Int := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al)
      then ret_outcome (errno_ret EINVAL) m
      else
      match read_bytes_map i.in_mem addrp (BitVec.ofInt 64 al) with
      | none => ret_outcome (errno_ret EFAULT) m
      | some bs =>
          outcome_copyins (if al == 0 then [] else [(addrp, bs.length)])
          (match e with
           | .FdSocket sk =>
               if decide (al < SA_FAMILY_SIZE) then ret_outcome (errno_ret EINVAL) m
               else if sa_family_of bs == AF_UNSPEC then
                 match sk with
                 | .SkFresh => ret_outcome (BitVec.ofInt 64 0) m
                 | .SkBound | .SkListening
                 | .SkConnected _ _ _ | .SkReset _ _ => .unmodeled
               else
                 match sk with
                 | .SkListening | .SkConnected _ _ _ | .SkReset _ _ =>
                     ret_outcome (errno_ret EISCONN) m
                 | .SkFresh | .SkBound =>
                     if decide (al < SOCKADDR_IN_SIZE)
                     then ret_outcome (errno_ret EINVAL) m
                     else if !(sa_family_of bs == AF_INET)
                     then ret_outcome (errno_ret EAFNOSUPPORT) m
                     else .unmodeled
           | _ => ret_outcome (errno_ret ENOTSOCK) m)

/- =========================================================================
   getsockname (204), getpeername (205), setsockopt (208), getsockopt
   (209), shutdown (210) — witness: the spec read straight off

   Every arm of every one of the five is an errno, a fixed 0, or
   `.unmodeled` — none draws from an `errno_from` set and none is an
   `alt` — so each witness is its spec read straight off, and none of
   them can get stuck.  The descriptor half is `Net.Socket.sock_fd` in
   all five; what differs is the socket arm, which is the whole point of
   there being five.
   ========================================================================= -/

def getsockname_witness (fd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ => .unmodeled

def getpeername_witness (fd : word) (m : Model) : Outcome SyscallEffect Model event :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl sk =>
      match sk with
      | .SkFresh           => ret_outcome (errno_ret ENOTCONN) m
      | .SkBound           => ret_outcome (errno_ret ENOTCONN) m
      | .SkListening       => ret_outcome (errno_ret ENOTCONN) m
      | .SkReset _ _       => ret_outcome (errno_ret ENOTCONN) m
      | .SkConnected _ _ _ => .unmodeled

def setsockopt_witness (fd level optlen : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ =>
      if int32_neg optlen then ret_outcome (errno_ret EINVAL) m
      else if !(sock_level_known level) then ret_outcome (errno_ret ENOPROTOOPT) m
      else .unmodeled

/-- `outcome_copyins` attaches the `optlen` ledger and leaves an
    `.unmodeled` alone, which is what `record_copyins` does on the spec
    side.  It sits OUTSIDE the level test for the same reason it does
    there: the read precedes the dispatch. -/
def getsockopt_witness (fd level optlenp : word) (i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl _ =>
      outcome_copyins (getsockopt_optlen_read i optlenp)
        (if !(sock_level_known level)
         then ret_outcome (errno_ret EOPNOTSUPP) m
         else .unmodeled)

def shutdown_witness (fd how : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  match sock_fd m fd with
  | .inr e => ret_outcome (errno_ret e) m
  | .inl sk =>
      if !(shut_how_ok how) then ret_outcome (errno_ret EINVAL) m
      else
        match sk with
        | .SkListening =>
            if (how.toNat : Int) == SHUT_WR
            then ret_outcome (BitVec.ofInt 64 0) m
            else .unmodeled
        | _ => .unmodeled

/- =========================================================================
   sendto (206) and sendmsg (211) — witness: the deterministic errno, or
   the ONE-BYTE delivery on a live connection
   ========================================================================= -/

/-- The socket half both calls share, so the send's one `choose` is
    discharged once rather than twice.

    `Net.Socket.SendGoes` is the only arm carrying nondeterminism, and
    the witness takes the SHORTEST admissible send rather than the
    longest: exactly one byte, which is `Fs.ReadWrite.writev_witness`'s
    choice on a channel and for the same reason.  A one-byte prefix needs
    only `count <> 0` to satisfy `Net.Socket.send_bytes`'s
    `1 <= length ds <= total`, where the full prefix would additionally
    need the gathered length bounded by the requested total — true, but a
    lemma `Net.Socket.send_bytes` does not carry and receptivity does not
    need.

    The ledger travels with the outcome: `pre` on every arm, and the one
    delivered byte's ranges on the arm that delivers.

    `Net.Socket.SendErr` consumes the pending error, so its witness
    carries the UPDATED model: the same `fd_insert` the spec performs,
    which is why the arm is a `modify` step and not a `pure` one. -/
def send_on_socket_witness (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState)
    (total : word) (bs : List byte) (m : Model) : Outcome SyscallEffect Model event :=
  match send_state sk with
  | .SendGoes ch =>
      if w_is0 total
      then outcome_copyins pre (ret_outcome (BitVec.ofInt 64 0) m)  -- zero-length request
      else if bs.length == 0
      then outcome_copyins pre (ret_outcome (errno_ret EFAULT) m)   -- nothing readable
      else outcome_copyins (pre ++ acc (bs.take 1).length)
             (.ok (mkEffect (len_word (bs.take 1)) [] []) m
                 ((bs.take 1).map (event.WriteEv ch)))             -- the one-byte send
  | .SendErr e peer ch =>
      outcome_copyins pre
        (ret_outcome (errno_ret e)
           (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m))
  | .SendDead => outcome_copyins pre (ret_outcome (errno_ret EPIPE) m)

/-- `sendto`'s three gates, then `import_ubuf`'s range verdict, then the
    fd — the nesting the spec insists on, mirrored here so that a
    reordering on either side stops matching. -/
def sendto_witness (fd buf count flags addrp : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !(send_flags_modeled flags) then .unmodeled
  else if !(w_is0 addrp) then .unmodeled
  else if !(modeled_rw_count count) then .unmodeled
  else
    access_ok_zero_witness buf count m
      (match fd_lookup (m_fds m) fd with
       | none => ret_outcome (errno_ret EBADF) m
       | some (.FdSocket sk) =>
           send_on_socket_witness [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) m
       | some _ => ret_outcome (errno_ret ENOTSOCK) m)

/-- `sendmsg`'s fd comes FIRST and the header second — the opposite
    nesting to `sendto_witness` above, and deliberately not shared with
    it. -/
def sendmsg_witness (fd msgp flags : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !(send_flags_modeled flags) then .unmodeled
  else
  match fd_lookup (m_fds m) fd with
  | none => ret_outcome (errno_ret EBADF) m
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some .FdDir
  | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some (.FdPipe _ _) | some (.FdDevNull _ _) | some .FdUrandom =>
      ret_outcome (errno_ret ENOTSOCK) m
  | some (.FdSocket sk) =>
      match read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) with
      | none => ret_outcome (errno_ret EFAULT) m
      | some _ =>
          match read_u64 i.in_mem msgp,
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 8),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 16),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 24),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 32),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) with
          | some name, some _, some iov, some iovlen, some _, some ctllen =>
              if !(w_is0 name) then .unmodeled          -- a destination address
              else if decide (IOV_MAX < (iovlen.toNat : Int))
              then outcome_copyins [(msgp, MSGHDR_SIZE.toNat)]
                     (ret_outcome (errno_ret EMSGSIZE) m)  -- __copy_msghdr's own errno
              else if decide (UIO_FASTIOV < (iovlen.toNat : Int)) then .unmodeled
              else
              match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
              | .ImpFault =>
                  outcome_copyins
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (ret_outcome (errno_ret EFAULT) m)
              | .ImpInval =>
                  outcome_copyins
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (ret_outcome (errno_ret EINVAL) m)
              | .ImpOk iovs0 =>
                  if !(w_is0 ctllen) then .unmodeled   -- ancillary data, after
                                                       -- the import: see the spec
                  else if !(decide (iovs_total (cap_iovecs iovs0) ≤ rw_bytes_max))
                  then .unmodeled
                  else
                  send_on_socket_witness
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                    fd sk
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered i.in_mem iovs0) m
          | _, _, _, _, _, _ =>
              outcome_copyins [(msgp, MSGHDR_SIZE.toNat)]
                (ret_outcome (errno_ret EFAULT) m)

/- ---------------- socketpair (199), recvfrom (207), recvmsg (212) ------

   Each witness takes the arm its spec decides first, and on socketpair
   the `alt`s LEFT branch — the reservation errno — so it never has to
   build the two descriptor writes. -/

def socketpair_witness (family type protocol sv : word)
    (i : SyscallInput) (m : Model) : Outcome SyscallEffect Model event :=
  if !(socketpair_flags_ok type) then ret_outcome (errno_ret EINVAL) m
  else if !(socketpair_modeled_b family type protocol) then .unmodeled
  else
  match socketpair_fds (m_fds m) with
  | none => .unmodeled
  | some _ =>
      if socketpair_dest_writable i.in_wmem sv
      then ret_outcome (errno_ret EMFILE) m
      else if !(access_okb sv 4)
      then ret_outcome (errno_ret EMFILE) m
      else .unmodeled

def recvfrom_witness (fd buf size : word) (_i : SyscallInput) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(modeled_rw_count size) then .unmodeled
  else if access_okb buf (size.toNat : Int)
  then (match sockfd_lookup_errno (m_fds m) fd with
        | some e => ret_outcome (errno_ret e) m
        | none => .unmodeled)
  else ret_outcome (errno_ret EFAULT) m

def recvmsg_witness (fd flags : word) (m : Model)
    : Outcome SyscallEffect Model event :=
  if !(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0)
  then .unmodeled
  else match sockfd_lookup_errno (m_fds m) fd with
       | some e => ret_outcome (errno_ret e) m
       | none => .unmodeled

/- =========================================================================
   listen, getsockname, getpeername, setsockopt, shutdown, recvfrom,
   recvmsg, socketpair — every one of these is its spec read straight off:
   each arm is an errno, a fixed 0, or `unmodeled`, so the witness needs no
   `choose` and the proof is the spec's own case tree with `bind_step`
   through the readers.
   ========================================================================= -/

/-- `pure` at one word, in the shape every answered witness arm has:
    `ret_outcome r m` IS `ret_only r`'s outcome at the same word. -/
private theorem ret_outcome_ok (r : word) (i : SyscallInput) (m : Model) :
    ret_only r i m (ret_outcome r m) := by
  unfold ret_only ret_outcome LinuxSem.LinuxProcessSem.pure
  rfl

theorem listen_witness_ok (fd backlog : word) (i : SyscallInput) (m : Model) :
    listen_spec fd backlog i m (listen_witness fd m) := by
  unfold listen_spec listen_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at ⊢
  cases e with
  | none => exact ret_outcome_ok (errno_ret EBADF) i m
  | some e =>
    cases e with
    | FdSocket sk =>
      cases sk <;> try dsimp only at ⊢
      · -- fresh: the autobind's -EADDRINUSE, the LEFT branch of the alt
        refine alt_l _ _ _ _ _ (bind_step (errno_from listen_errnos)
          (fun e => err_ret e) i m EADDRINUSE m _ (errno_head_witness _ _ i m) ?_)
        exact ret_outcome_ok (errno_ret EADDRINUSE) i m
      · -- bound: it already has a port, so `get_port` cannot fail
        refine bind_step (set_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)))
          (fun _ => ret_only (BitVec.ofInt 64 0)) i m ()
          (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m)
          (ret_outcome (BitVec.ofInt 64 0)
            (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m)) ?_ ?_
        · unfold set_fds modifySpec
          exact modify_ok _ i m
        · exact ret_outcome_ok _ i _
      · exact ret_outcome_ok _ i m
      · exact ret_outcome_ok (errno_ret EINVAL) i m
      · exact ret_outcome_ok (errno_ret EINVAL) i m
    | _ => exact ret_outcome_ok (errno_ret ENOTSOCK) i m

theorem getsockname_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    getsockname_spec fd i m (getsockname_witness fd m) := by
  unfold getsockname_spec getsockname_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at ⊢
  cases s with
  | inr e => exact ret_outcome_ok (errno_ret e) i m
  | inl sk => exact unmodeled_intro i m

theorem getpeername_witness_ok (fd : word) (i : SyscallInput) (m : Model) :
    getpeername_spec fd i m (getpeername_witness fd m) := by
  unfold getpeername_spec getpeername_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at ⊢
  cases s with
  | inr e => exact ret_outcome_ok (errno_ret e) i m
  | inl sk =>
    cases sk <;> try dsimp only at ⊢
    · exact ret_outcome_ok (errno_ret ENOTCONN) i m
    · exact ret_outcome_ok (errno_ret ENOTCONN) i m
    · exact ret_outcome_ok (errno_ret ENOTCONN) i m
    · exact unmodeled_intro i m
    · exact ret_outcome_ok (errno_ret ENOTCONN) i m

theorem setsockopt_witness_ok (fd level optlen : word) (i : SyscallInput)
    (m : Model) :
    setsockopt_spec fd level optlen i m (setsockopt_witness fd level optlen m) := by
  unfold setsockopt_spec setsockopt_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at ⊢
  cases s with
  | inr e => exact ret_outcome_ok (errno_ret e) i m
  | inl sk =>
    cases hn : int32_neg optlen
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases hl : (!(sock_level_known level))
      · simp only [Bool.false_eq_true, ite_false] at ⊢
        exact unmodeled_intro i m
      · simp at ⊢
        exact ret_outcome_ok (errno_ret ENOPROTOOPT) i m
    · simp at ⊢
      exact ret_outcome_ok (errno_ret EINVAL) i m

theorem shutdown_witness_ok (fd how : word) (i : SyscallInput) (m : Model) :
    shutdown_spec fd how i m (shutdown_witness fd how m) := by
  unfold shutdown_spec shutdown_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at ⊢
  cases s with
  | inr e => exact ret_outcome_ok (errno_ret e) i m
  | inl sk =>
    cases hh : (!(shut_how_ok how))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases sk <;> try dsimp only at ⊢
      · exact unmodeled_intro i m
      · exact unmodeled_intro i m
      · cases hw : ((how.toNat : Int) == SHUT_WR)
        · simp only [Bool.false_eq_true, ite_false] at ⊢
          exact unmodeled_intro i m
        · simp at ⊢
          exact ret_outcome_ok _ i m
      · exact unmodeled_intro i m
      · exact unmodeled_intro i m
    · simp at ⊢
      exact ret_outcome_ok (errno_ret EINVAL) i m

theorem recvfrom_witness_ok (fd buf size : word) (i : SyscallInput) (m : Model) :
    recvfrom_spec fd buf size i m (recvfrom_witness fd buf size i m) := by
  unfold recvfrom_spec recvfrom_witness
  cases hc : (!(modeled_rw_count size))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    unfold access_ok_zero
    cases hok : access_okb buf (size.toNat : Int)
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      exact ret_outcome_ok (errno_ret EFAULT) i m
    · simp at ⊢
      unfold recv_fd_answer
      generalize hsl : sockfd_lookup_errno (m_fds m) fd = o at ⊢
      cases o with
      | some e => exact ret_outcome_ok (errno_ret e) i m
      | none => exact unmodeled_intro i m
  · simp at ⊢
    exact unmodeled_intro i m

theorem recvmsg_witness_ok (fd flags : word) (i : SyscallInput) (m : Model) :
    recvmsg_spec fd flags i m (recvmsg_witness fd flags m) := by
  unfold recvmsg_spec recvmsg_witness
  cases hf : (!(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    unfold recv_fd_answer
    generalize hsl : sockfd_lookup_errno (m_fds m) fd = o at ⊢
    cases o with
    | some e => exact ret_outcome_ok (errno_ret e) i m
    | none => exact unmodeled_intro i m
  · simp at ⊢
    exact unmodeled_intro i m

theorem accept4_witness_ok (fd addrp addrlenp flags : word) (i : SyscallInput)
    (m : Model) :
    accept4_spec fd addrp addrlenp flags i m (accept4_witness fd addrp flags m) := by
  unfold accept4_spec accept4_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e0 at ⊢
  cases e0 with
  | none => exact ret_outcome_ok (errno_ret EBADF) i m
  | some e =>
    cases h1 : (!(z_ldiff ((abi_low32 flags).toNat : Int)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases h2 : (!(z_land ((abi_low32 flags).toNat : Int) SOCK_NONBLOCK == 0))
      · simp only [Bool.false_eq_true, ite_false] at ⊢
        cases e with
        | FdSocket sk =>
          try dsimp only at ⊢
          cases h3 : (!(w_is0 addrp))
          · simp only [Bool.false_eq_true, ite_false] at ⊢
            cases sk <;> try dsimp only at ⊢
            · exact ret_outcome_ok (errno_ret EINVAL) i m
            · exact ret_outcome_ok (errno_ret EINVAL) i m
            · -- listening: the environment-failure branch of the alt
              refine alt_l _ _ _ _ _ (bind_step (errno_from accept_errnos)
                (fun er => err_ret er) i m ENOMEM m _ (errno_head_witness _ _ i m) ?_)
              exact ret_outcome_ok (errno_ret ENOMEM) i m
            · exact ret_outcome_ok (errno_ret EINVAL) i m
            · exact ret_outcome_ok (errno_ret EINVAL) i m
          · simp at ⊢
            exact unmodeled_intro i m
        | _ => exact ret_outcome_ok (errno_ret ENOTSOCK) i m
      · simp at ⊢
        exact unmodeled_intro i m
    · simp at ⊢
      exact ret_outcome_ok (errno_ret EINVAL) i m

theorem getsockopt_witness_ok (fd level optlenp : word) (i : SyscallInput)
    (m : Model) :
    getsockopt_spec fd level optlenp i m (getsockopt_witness fd level optlenp i m) := by
  unfold getsockopt_spec getsockopt_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at ⊢
  cases s with
  | inr e => exact ret_outcome_ok (errno_ret e) i m
  | inl sk =>
    apply record_copyins_outcome
    cases hl : (!(sock_level_known level))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      exact unmodeled_intro i m
    · simp at ⊢
      exact ret_outcome_ok (errno_ret EOPNOTSUPP) i m

theorem socketpair_witness_ok (family type protocol sv : word) (i : SyscallInput)
    (m : Model) :
    socketpair_spec family type protocol sv i m
      (socketpair_witness family type protocol sv i m) := by
  unfold socketpair_spec socketpair_witness
  cases hfl : (!(socketpair_flags_ok type))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    cases hmo : (!(socketpair_modeled_b family type protocol))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
      refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
      generalize hfds : socketpair_fds (m_fds m) = o at ⊢
      cases o with
      | none => exact unmodeled_intro i m
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        cases hmem : socketpair_dest_writable i.in_wmem sv
        · simp only [Bool.false_eq_true, ite_false] at ⊢
          cases ho : (!(access_okb sv 4))
          · simp at ⊢
            exact unmodeled_intro i m
          · simp at ⊢
            refine alt_l _ _ _ _ _ (bind_step (errno_from socketpair_reserve_errnos)
              (fun e => err_ret e) i m EMFILE m _ (errno_head_witness _ _ i m) ?_)
            exact ret_outcome_ok (errno_ret EMFILE) i m
        · simp at ⊢
          refine alt_l _ _ _ _ _ (bind_step (errno_from socketpair_reserve_errnos)
            (fun e => err_ret e) i m EMFILE m _ (errno_head_witness _ _ i m) ?_)
          exact ret_outcome_ok (errno_ret EMFILE) i m
    · simp at ⊢
      exact unmodeled_intro i m
  · simp at ⊢
    exact ret_outcome_ok (errno_ret EINVAL) i m


theorem socket_witness_ok (domain type protocol : word) (i : SyscallInput) (m : Model) :
    socket_spec domain type protocol i m (socket_witness domain type protocol m) := by
  unfold socket_spec socket_witness
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  try dsimp only
  cases h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
      (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    cases h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain))
      · simp only [Bool.false_eq_true, ite_false] at ⊢
        cases h4 : decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        · simp only [Bool.false_eq_true, ite_false] at ⊢
          cases h5 : (!(sint32 domain == AF_INET))
          · simp only [Bool.false_eq_true, ite_false] at ⊢
            cases h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
            · simp only [Bool.false_eq_true, ite_false] at ⊢
              cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol))
              · simp only [Bool.false_eq_true, ite_false] at ⊢
                cases h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM)
                · simp only [Bool.false_eq_true, ite_false] at ⊢
                  cases h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM) ||
                      (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET) ||
                        (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      exact ret_outcome_ok (errno_ret ESOCKTNOSUPPORT) i m
                    · simp at ⊢
                      exact unmodeled_intro i m
                  · simp at ⊢
                    exact unmodeled_intro i m
                · cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP)))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      refine alt_l _ _ _ _ _ (bind_step (errno_from socket_errnos)
                        (fun e => err_ret e) i m ENOMEM m _ (errno_head_witness _ _ i m) ?_)
                      exact ret_outcome_ok (errno_ret ENOMEM) i m
                    · simp at ⊢
                      exact ret_outcome_ok (errno_ret EPROTONOSUPPORT) i m
                  · simp at ⊢
                    exact unmodeled_intro i m
              · simp at ⊢
                exact ret_outcome_ok (errno_ret EINVAL) i m
            · simp at ⊢
              exact unmodeled_intro i m
          · simp at ⊢
            exact unmodeled_intro i m
        · simp at ⊢
          exact ret_outcome_ok (errno_ret EINVAL) i m
      · simp at ⊢
        exact ret_outcome_ok (errno_ret EAFNOSUPPORT) i m
    · simp at ⊢
      exact unmodeled_intro i m
  · simp at ⊢
    exact ret_outcome_ok (errno_ret EINVAL) i m

theorem bind_witness_ok (fd addrp addrlen : word) (i : SyscallInput) (m : Model) :
    bind_spec fd addrp addrlen i m (bind_witness fd addrp addrlen i m) := by
  unfold bind_spec bind_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  split
  · rename_i heq
    simp only [heq]
    exact ret_outcome_ok (errno_ret EBADF) i m
  · rename_i sk heq
    by_cases h1 : (decide (sint32 addrlen < 0)
        || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) = true
    · simp only [ite_eq_left h1, heq]
      exact ret_outcome_ok (errno_ret EINVAL) i m
    · simp only [ite_eq_right h1]
      by_cases h2 : (sint32 addrlen == 0) = true
      · simp only [ite_eq_left h2, heq]
        exact ret_outcome_ok (errno_ret EINVAL) i m
      · simp only [ite_eq_right h2]
        generalize hrd : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) = rbs
        cases rbs with
        | none =>
          simp only [heq]
          exact ret_outcome_ok (errno_ret EFAULT) i m
        | some bs =>
          by_cases h3 : decide (sint32 addrlen < SOCKADDR_IN_SIZE) = true
          · simp only [ite_eq_left h3, heq]
            exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
          · simp only [ite_eq_right h3]
            by_cases h4 : (!((sa_family_of bs == AF_INET)
                || ((sa_family_of bs == AF_UNSPEC) && (sin_addr_of bs == INADDR_ANY)))) = true
            · simp only [ite_eq_left h4, heq]
              exact record_copyins_outcome (ret_outcome_ok (errno_ret EAFNOSUPPORT) i m)
            · simp only [ite_eq_right h4]
              by_cases h5 : (!(sin_addr_of bs == INADDR_ANY)) = true
              · simp only [ite_eq_left h5, heq]
                exact record_copyins_outcome (unmodeled_intro i m)
              · simp only [ite_eq_right h5]
                by_cases h6 : (!(sin_port_of bs == 0)) = true
                · simp only [ite_eq_left h6, heq]
                  exact record_copyins_outcome (unmodeled_intro i m)
                · simp only [ite_eq_right h6]
                  cases sk with
                  | SkFresh =>
                    simp only [heq]
                    exact record_copyins_outcome
                      (alt_l _ _ _ _ _ (bind_step (errno_from bind_errnos)
                        (fun e => err_ret e) i m EADDRINUSE m _
                        (errno_head_witness _ _ i m) (ret_outcome_ok _ i m)))
                  | SkBound =>
                    simp only [heq]
                    exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                  | SkListening =>
                    simp only [heq]
                    exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                  | SkConnected peer ch rx =>
                    cases hrx : rx 0 with
                    | fin =>
                      simp only [hrx, heq]
                      exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                    | rst =>
                      simp only [hrx, heq]
                      exact record_copyins_outcome (unmodeled_intro i m)
                    | timedOut =>
                      simp only [hrx, heq]
                      exact record_copyins_outcome (unmodeled_intro i m)
                    | cons b =>
                      simp only [hrx, heq]
                      exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                  | SkReset peer ch =>
                    simp only [heq]
                    exact record_copyins_outcome (unmodeled_intro i m)
  · rename_i val hnot heq
    simp only [heq]
    exact ret_outcome_ok (errno_ret ENOTSOCK) i m

theorem connect_witness_ok (fd addrp addrlen : word) (i : SyscallInput) (m : Model) :
    connect_spec fd addrp addrlen i m (connect_witness fd addrp addrlen i m) := by
  unfold connect_spec connect_witness
  refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
  refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
  split
  · rename_i heq
    simp only [heq]
    exact ret_outcome_ok (errno_ret EBADF) i m
  · rename_i e heq
    by_cases h1 : (decide (sint32 addrlen < 0)
        || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) = true
    · simp only [ite_eq_left h1, heq]
      exact ret_outcome_ok (errno_ret EINVAL) i m
    · simp only [ite_eq_right h1]
      generalize hrd : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) = rbs
      cases rbs with
      | none =>
        simp only [heq]
        exact ret_outcome_ok (errno_ret EFAULT) i m
      | some bs =>
        by_cases hs : ∃ sk, e = FdEntry.FdSocket sk
        · obtain ⟨sk, rfl⟩ := hs
          by_cases h3 : decide (sint32 addrlen < SA_FAMILY_SIZE) = true
          · simp only [ite_eq_left h3, heq]
            exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
          · simp only [ite_eq_right h3]
            by_cases h4 : (sa_family_of bs == AF_UNSPEC) = true
            · simp only [ite_eq_left h4]
              cases sk with
              | SkFresh =>
                simp only [heq]
                exact record_copyins_outcome (ret_outcome_ok (BitVec.ofInt 64 0) i m)
              | SkBound =>
                simp only [heq]
                exact record_copyins_outcome (unmodeled_intro i m)
              | SkListening =>
                simp only [heq]
                exact record_copyins_outcome (unmodeled_intro i m)
              | SkConnected peer ch rx =>
                simp only [heq]
                exact record_copyins_outcome (unmodeled_intro i m)
              | SkReset peer ch =>
                simp only [heq]
                exact record_copyins_outcome (unmodeled_intro i m)
            · simp only [ite_eq_right h4]
              cases sk with
              | SkFresh =>
                by_cases h5 : decide (sint32 addrlen < SOCKADDR_IN_SIZE) = true
                · simp only [ite_eq_left h5, heq]
                  exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                · simp only [ite_eq_right h5]
                  by_cases h6 : (!(sa_family_of bs == AF_INET)) = true
                  · simp only [ite_eq_left h6, heq]
                    exact record_copyins_outcome (ret_outcome_ok (errno_ret EAFNOSUPPORT) i m)
                  · simp only [ite_eq_right h6, heq]
                    exact record_copyins_outcome (unmodeled_intro i m)
              | SkBound =>
                by_cases h5 : decide (sint32 addrlen < SOCKADDR_IN_SIZE) = true
                · simp only [ite_eq_left h5, heq]
                  exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                · simp only [ite_eq_right h5]
                  by_cases h6 : (!(sa_family_of bs == AF_INET)) = true
                  · simp only [ite_eq_left h6, heq]
                    exact record_copyins_outcome (ret_outcome_ok (errno_ret EAFNOSUPPORT) i m)
                  · simp only [ite_eq_right h6, heq]
                    exact record_copyins_outcome (unmodeled_intro i m)
              | SkListening =>
                simp only [heq]
                exact record_copyins_outcome (ret_outcome_ok (errno_ret EISCONN) i m)
              | SkConnected peer ch rx =>
                simp only [heq]
                exact record_copyins_outcome (ret_outcome_ok (errno_ret EISCONN) i m)
              | SkReset peer ch =>
                simp only [heq]
                exact record_copyins_outcome (ret_outcome_ok (errno_ret EISCONN) i m)
        · have hne : ∀ sk, e ≠ FdEntry.FdSocket sk := fun sk h => hs ⟨sk, h⟩
          simp only [heq]
          exact record_copyins_outcome (ret_outcome_ok (errno_ret ENOTSOCK) i m)

/-- `emit` then an event-free spec: the shape the delivering send arm has.
    `Prelude.emit_pure_ok` covers only a `pure` continuation; this is the
    same step for an arbitrary `c` whose outcome records no event, which is
    also what `Fs.ReadWrite`'s own copy of the lemma states. -/
private theorem emit_then_quiet_ok {A : Type} (evs : List event) (c : SysSpec A)
    (i : SyscallInput) (m : Model) (x : A) (m' : Model)
    (H : c i m (.ok x m' [])) :
    bind (emit evs) (fun _ => c) i m (.ok x m' evs) := by
  have h := bind_ok (emit evs) (fun _ => c) i m () m evs x m' []
    (emit_ok evs i m) H
  rwa [List.append_nil] at h

/-- The witness for the shared send body: the zero-length request, the
    unreadable buffer, the one-byte delivery, the consumed pending error,
    and -EPIPE, each read straight off `send_on_socket`. -/
theorem send_on_socket_witness_ok (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState)
    (total : word) (bs : List byte) (i : SyscallInput) (m : Model) :
    send_on_socket pre acc fd sk total bs m i m
      (send_on_socket_witness pre acc fd sk total bs m) := by
  unfold send_on_socket send_on_socket_witness
  cases hst : send_state sk with
  | SendGoes ch =>
    unfold send_bytes
    by_cases ht : w_is0 total = true
    · simp only [ht, ite_true]
      apply record_copyins_outcome
      exact ret_outcome_ok _ i m
    · simp only [ht, Bool.false_eq_true, ite_false]
      by_cases hb : (bs.length == 0) = true
      · simp only [hb, ite_true]
        apply record_copyins_outcome
        exact ret_outcome_ok _ i m
      · simp only [hb, Bool.false_eq_true, ite_false]
        have htne : total ≠ 0 := by
          intro h0
          exact ht (by rw [h0]; decide)
        have htpos : 1 ≤ total.toNat := by
          rcases Nat.eq_zero_or_pos total.toNat with h | h
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) htne
          · exact h
        have hne : bs.length ≠ 0 := by
          intro h0; rw [h0] at hb; simp at hb
        have hge : 1 ≤ bs.length := Nat.pos_of_ne_zero hne
        have hlen1 : (bs.take 1).length = 1 := by
          rw [List.length_take, Nat.min_eq_left hge]
        refine bind_step (choose _) _ i m (bs.take 1) m _
          ⟨bs.take 1, ?_, rfl⟩ ?_
        · dsimp only
          refine ⟨?_, ?_, ?_⟩
          · rw [hlen1]; decide
          · rw [hlen1]; exact_mod_cast htpos
          · rw [hlen1]
        · try dsimp only
          exact emit_then_quiet_ok ((bs.take 1).map (event.WriteEv ch))
            (record_copyins (pre ++ acc (bs.take 1).length)
              (LinuxSem.LinuxProcessSem.Sys.Syscall.ret_only
                (len_word (bs.take 1)))) i m _ m
            (record_copyins_ok (pure_ok _ i m))
  | SendErr e peer ch =>
    apply record_copyins_outcome
    refine bind_step (set_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))))
      (fun _ => err_ret e) i m ()
      (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) _ ?_ ?_
    · unfold set_fds modifySpec
      exact modify_ok _ i m
    · exact ret_outcome_ok (errno_ret e) i _
  | SendDead =>
    apply record_copyins_outcome
    exact ret_outcome_ok (errno_ret EPIPE) i m

/-- `sendto`'s three gates, then `import_ubuf`'s range verdict, then the
    fd: the witness is that nesting read straight off, with the socket arm
    handed to `send_on_socket_witness_ok`. -/
theorem sendto_witness_ok (fd buf count flags addrp addrlen : word)
    (i : SyscallInput) (m : Model) :
    sendto_spec fd buf count flags addrp addrlen i m
      (sendto_witness fd buf count flags addrp i m) := by
  unfold sendto_spec sendto_witness
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true]
    exact unmodeled_intro i m
  · simp only [hf, Bool.false_eq_true, ite_false]
    by_cases ha : (!(w_is0 addrp)) = true
    · simp only [ha, ite_true]
      exact unmodeled_intro i m
    · simp only [ha, Bool.false_eq_true, ite_false]
      by_cases hc : (!(modeled_rw_count count)) = true
      · simp only [hc, ite_true]
        exact unmodeled_intro i m
      · simp only [hc, Bool.false_eq_true, ite_false]
        refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
        refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
        unfold access_ok_zero access_ok_zero_witness
        by_cases hok : access_okb buf (count.toNat : Int) = true
        · simp only [hok, ite_true]
          split
          · rename_i heq
            simp only [heq]
            exact ret_outcome_ok (errno_ret EBADF) i m
          · rename_i sk heq
            simp only [heq]
            exact send_on_socket_witness_ok [] (fun n => [(buf, n)]) fd sk count
              (readable_bytes i.in_mem buf count) i m
          · rename_i val hnot heq
            simp only [heq]
            exact ret_outcome_ok (errno_ret ENOTSOCK) i m
        · simp only [hok, Bool.false_eq_true, ite_false]
          exact ret_outcome_ok (errno_ret EFAULT) i m

/-- `sendmsg`'s fd first, then `__copy_msghdr`'s field reads, then the
    import the `writev` gather shares, then the send: the witness is that
    nesting read straight off, with the socket arm handed to
    `send_on_socket_witness_ok` and the -EMSGSIZE, -EFAULT and -EINVAL
    arms carrying the ledger the spec records where it records it. -/
theorem sendmsg_witness_ok (fd msgp flags : word)
    (i : SyscallInput) (m : Model) :
    sendmsg_spec fd msgp flags i m (sendmsg_witness fd msgp flags i m) := by
  unfold sendmsg_spec sendmsg_witness
  by_cases hf : (!(send_flags_modeled flags)) = true
  · simp only [hf, ite_true]
    exact unmodeled_intro i m
  · simp only [hf, Bool.false_eq_true, ite_false]
    refine bind_step inputSpec _ i m i m _ (input_ok i m) ?_
    refine bind_step getModelSpec _ i m m m _ (getModel_ok i m) ?_
    -- the header read: the first scrutinee `split` peels
    split
    · -- the 56-byte header is unreadable: -EFAULT, and no ledger at all
      rename_i hrb
      simp only [hrb]
      generalize hfd : fd_lookup (m_fds m) fd = e
      cases e with
      | none =>
        simp only []
        exact ret_outcome_ok (errno_ret EBADF) i m
      | some ent =>
        cases ent <;>
        (simp only []
         first
          | exact ret_outcome_ok (errno_ret EFAULT) i m
          | exact ret_outcome_ok (errno_ret ENOTSOCK) i m)
    · -- the header read: six of the seven fields
      rename_i bs hrb
      simp only [hrb]
      split
      · -- every field readable
        -- the six field equations, in offset order: `msg_name`,
        -- `msg_namelen`, `msg_iov`, `msg_iovlen`, `msg_control`,
        -- `msg_controllen` (`msg_flags` at 48 is read by nothing)
        rename_i hmsgp h8 h16 h24 h32 h40
        rename_i name namelen iov iovlen ctl ctllen
        simp only [hmsgp, h8, h16, h24, h32, h40]
        generalize hfd : fd_lookup (m_fds m) fd = e
        cases e with
        | none =>
          simp only []
          exact ret_outcome_ok (errno_ret EBADF) i m
        | some ent =>
          cases ent <;>
          (simp only []
           first
            | exact ret_outcome_ok (errno_ret ENOTSOCK) i m
            | (rename_i sock
               -- a non-NULL `msg_name`: a destination address, declined
               -- before any ledger
               split
               · exact unmodeled_intro i m
               · -- `__copy_msghdr`'s own -EMSGSIZE, on the full 64-bit
                 -- `msg_iovlen`, with the header read recorded
                 split
                 · exact record_copyins_outcome (ret_outcome_ok (errno_ret EMSGSIZE) i m)
                 · -- the heap-backed range (see `Fs.ReadWrite`): declined
                   split
                   · exact unmodeled_intro i m
                   · -- `import_iovec`: the descriptors it walked, then
                     -- the payload the send gathers
                     generalize hci : copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) = imp
                     cases imp with
                     | ImpFault =>
                       simp only []
                       exact record_copyins_outcome (ret_outcome_ok (errno_ret EFAULT) i m)
                     | ImpInval =>
                       simp only []
                       exact record_copyins_outcome (ret_outcome_ok (errno_ret EINVAL) i m)
                     | ImpOk iovs0 =>
                       simp only []
                       -- ancillary data: `____sys_sendmsg` reads
                       -- `msg_controllen` only after the import
                       split
                       · exact unmodeled_intro i m
                       · -- the gather above `rw_bytes_max`: declined;
                         -- otherwise the send itself
                         split
                         · exact unmodeled_intro i m
                         · exact send_on_socket_witness_ok _ _ fd sock _ _ i m))
      · -- not every field readable: the arm the spec calls unreachable,
        -- answering -EFAULT with the header alone recorded.  `hnon` is the
        -- excluded all-`some` pattern `split` hands the wildcard arm
        rename_i hnon
        generalize hfd : fd_lookup (m_fds m) fd = e
        cases e with
        | none =>
          simp only []
          exact ret_outcome_ok (errno_ret EBADF) i m
        | some ent =>
          cases ent <;>
          (simp only []
           first
            | exact ret_outcome_ok (errno_ret ENOTSOCK) i m
            | exact record_copyins_outcome (ret_outcome_ok (errno_ret EFAULT) i m))

end LinuxSem.Checks.Witness.Net.Socket
