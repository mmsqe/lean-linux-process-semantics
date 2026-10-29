/-
  * LinuxProcessSem.Checks.Sys.Net.Socket — the socket (198), bind (200),
      listen (201), accept (202), getsockname (204), getpeername (205),
      sendto (206), setsockopt (208), getsockopt (209), shutdown (210),
      sendmsg (211), accept4 (242) checkers, and their proofs

  Answers to Linux [net/socket.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  A word is read UNSIGNED (`(w.toNat : Int)`); a `Bool` test is `==` or
  `decide (· < ·)` / `decide (· ≤ ·)`; the bit operations are `z_ldiff` /
  `Sys.Uapi.z_land` / `z_lor`; list operations are `List.take` / `List.drop`
  / `List.length`; and `.ok` / `.unmodeled` are the constructors of
  `Outcome`, `CheckOk` / `CheckReject` / `CheckUnmodeled` those of
  `check_result` (`Checks.Sys.Prelude`).  `mkEffectU r [] [] [] [] []` is
  the six-field structure literal `⟨r, [], [], [], [], []⟩`, since
  `SyscallEffect` is one structure with `eff_copyins` among its fields.  A
  coinductive `NCons _ _` / `NFin` / `NRst` / `NTimedOut` pattern in the
  *socket state* is the observation at index 0, `match rx 0 with | .cons _
  => … | .fin => … | .rst => … | .timedOut => …` — the same move
  `Sys/Net/Socket.lean` makes for the specs.

  `check_new_fd_result` and `check_new_fd_result_no_unmodeled` below are
  stated here rather than imported: `socket` and `accept4` are their other
  two call sites, `Checks/Sys/Fs/Open.lean` defines both as well, and the
  copies agree statement for statement.  They are kept because this file's
  proofs use the local names, and replacing them with the `Open.*` versions
  is an import-edge change of its own.

  TWO declarations below are PUBLIC and are this file's own: the theorems
  [check_send_on_socket_frame] and [check_recv_fd_answer_frame], stated
  beside the two acceptors they are about.  Both are frame facts
  (`m'.m_vmmaps = m.m_vmmaps`) that [Checks/VmMapsDisjoint.lean] folds into
  its `vm_frame H` line, and they are stated where the helper lives for the
  same reason `Checks/Sys/Fs/Open.lean` states
  [check_ftruncate_file_arm_frame] there: the citing module must be able to
  name them.  Each proof is the checker side of the corresponding
  `Socket/Send.lean` walk with the spec dropped.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Net.Socket

namespace LinuxSem.Checks.Sys.Net.Socket

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
  (rw_bytes_max modeled_rw_count access_ok_zero)
open LinuxSem.LinuxProcessSem.Sys.Fs.File (z_ldiff lowest_fd)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (UIO_FASTIOV)
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess (check_access_ok_zero)

/-- The syscall layer's 32-bit argument truncation.  `Sys.Uapi` carries a
    staging copy of the same function, so the bare name is ambiguous once
    both namespaces are open; the checkers must use the one the specs use,
    so this binds it to `Syscall`'s. -/
private abbrev abi_low32 (w : word) : word :=
  LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32 w

/- =========================================================================
   The fresh-descriptor acceptor
   ========================================================================= -/

/-- The shape every call that hands back a FRESH DESCRIPTOR admits:
    either an error-encoded return drawn from `es`, or the lowest free fd
    (`State.alloc_fd`) with the model `mk` builds from it.  `openat`,
    `socket` and `accept4` differ only in `es` and in `mk`.

    The copy lives here for the reason the file header gives. -/
def check_new_fd_result (es : List Int) (eff : SyscallEffect) (m : Model)
    (mk : word → Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in es ret then .CheckOk m []
      else
        match fd_lookup (m_fds m) ret with
        | some _ => .CheckReject
        | none => if bv_eqb ret (alloc_fd (m_fds m)) then .CheckOk (mk ret) []
                  else .CheckReject
  | _ => .CheckReject

/-- A fresh-descriptor result never declines: every shape it can see is
    either an injected errno, the allocated fd, or a rejection. -/
theorem check_new_fd_result_no_unmodeled (es : List Int) (eff : SyscallEffect)
    (m : Model) (mk : word → Model) :
    check_new_fd_result es eff m mk ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_new_fd_result
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · by_cases h : errno_ret_in es ret = true
    · simp only [h, ite_true]
      intro hh
      exact nomatch hh
    · simp only [h, Bool.false_eq_true, ite_false]
      cases hfd : fd_lookup (m_fds m) ret with
      | some _ => simp
      | none =>
        by_cases h2 : bv_eqb ret (alloc_fd (m_fds m)) = true <;> simp [h2]
  all_goals simp

/- =========================================================================
   The two generic acceptors
   ========================================================================= -/

/-- The other socket shape: an injected errno, or a fixed return with a
    new fd table.  `bind` and `listen` both use it, and both return 0, so
    the success return can never be mistaken for an errno; the
    completeness lemma below takes that as a hypothesis and each call
    site discharges it by evaluation. -/
def check_errno_or_success (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in es ret then .CheckOk m []
      else if bv_eqb ret r then .CheckOk (with_fds fds m) [] else .CheckReject
  | _ => .CheckReject

/-- The acceptor for an `alt` whose SUCCESS SIDE ADMITS NOTHING, leaving
    the injected errno as the only outcome.  `accept` reaches it once
    `Net.Socket.conn_ix_exhausted` holds: the spec's success branch is
    `choose (fun _ => False)` there, so a returned descriptor is not
    admissible however it was allocated.  Note it is not
    `check_new_fd_result` with an empty `mk` — that would still accept
    `alloc_fd`'s value. -/
def check_errno_only (es : List Int) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨ret, [], [], [], [], []⟩ =>
      if errno_ret_in es ret then .CheckOk m [] else .CheckReject
  | _ => .CheckReject

/- =========================================================================
   The per-syscall checkers
   ========================================================================= -/

/-- socket(2).  Every test is a pure function of the arguments and they
    are made in the kernel's order, because the order is what decides
    which errno a doubly-bad call gets; see `Net.Socket.socket_spec`.

    The five `let`s that would read as `tu`, `flagbits`, `ty`, `fam` and
    `pro` are spelled out instead: the checks are identical, but
    zeta-reducing such `let`s in a goal multiplies the `decide` instances
    that scan `sint32`, and the simplifier runs out of steps before it can
    split the first `if` (the proof note below has the details). -/
def check_socket (domain type protocol : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)
  then .CheckUnmodeled                -- SOCK_NONBLOCK: no O_NONBLOCK notion
  else if decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)
  then check_ret_only eff (errno_ret EAFNOSUPPORT) m []
  else if decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(sint32 domain == AF_INET) then .CheckUnmodeled
  else if (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
  then .CheckUnmodeled
    -- above the protocol range: __sock_create rewrites the family to
    -- PF_PACKET, so inet_create's IPPROTO_MAX check never runs — see
    -- `Net.Socket.socket_spec`
  else if decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) then
    if (sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)
    then .CheckUnmodeled
    else if !((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))
    then check_ret_only eff (errno_ret EPROTONOSUPPORT) m []
    else
      check_new_fd_result socket_errnos eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) m)
  else if (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
       || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW)
  then .CheckUnmodeled               -- SOCK_DGRAM / SOCK_RAW; SOCK_PACKET is above
  else if (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
       || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP)
  then .CheckUnmodeled               -- sctp and dccp register these
  else check_ret_only eff (errno_ret ESOCKTNOSUPPORT) m []

/-- bind(2).  -EFAULT precedes the 16-byte minimum, which is why the
    address bytes are read before their length is judged against
    `SOCKADDR_IN_SIZE`. -/
def check_bind (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket sk) =>
      let al : Int := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al)
      then check_ret_only eff (errno_ret EINVAL) m []
      else if al == 0 then check_ret_only eff (errno_ret EINVAL) m []
      else
      match read_bytes_map i.in_mem addrp (BitVec.ofInt 64 al) with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some bs =>
          -- PAST THE COPY, and that is where the ledger starts.
          -- `move_addr_to_kernel` has really moved `al` bytes out of user
          -- memory by the time any of the arms below runs, so each of them
          -- expects `eff_copyins` to be exactly `[(addrp, al)]`, while every
          -- arm ABOVE expects it empty: the two `addrlen`-range -EINVALs
          -- return before the copy is attempted and the -EFAULT arm is the
          -- copy FAILING, which transfers nothing.  This mirrors
          -- `Net.Socket.bind_spec`'s `record_copyins`, and it is what makes
          -- the ledger discriminate rather than decorate — the two -EINVALs
          -- differ in nothing else.
          if decide (al < SOCKADDR_IN_SIZE)
          then check_ret_only_copyins [(addrp, al.toNat)] eff
                 (errno_ret EINVAL) m []
          else
            let fam : Int := sa_family_of bs
            let port : Int := sin_port_of bs
            let a : Int := sin_addr_of bs
            if !((fam == AF_INET)
                 || ((fam == AF_UNSPEC) && (a == INADDR_ANY)))
            then check_ret_only_copyins [(addrp, al.toNat)] eff
                   (errno_ret EAFNOSUPPORT) m []
            else if !(a == INADDR_ANY) then .CheckUnmodeled
            else if !(port == 0) then .CheckUnmodeled
              -- a specific address or port needs tables a one-process
              -- model does not have; decline rather than guess.  No ledger
              -- test here: an `Unmodeled` carries no effect at all, so
              -- there is nothing for a ledger to be right or wrong about
            else
              match sk with
              | .SkFresh =>
                  -- `check_errno_or_success` has no copy-in variant of its
                  -- own, and giving it one would duplicate `check_copyins`
                  -- for a single call site.  So the ledger is tested here
                  -- and the arm's own acceptor sees the effect with the
                  -- ledger stripped, which is exactly what
                  -- `check_ret_only_copyins` does internally.
                  check_copyins [(addrp, al.toNat)] eff
                    (check_errno_or_success bind_errnos
                       (fd_insert (m_fds m) fd (.FdSocket .SkBound))
                       (BitVec.ofInt 64 0) (clear_copyins eff) m)
              | .SkBound | .SkListening => 
                  check_ret_only_copyins [(addrp, al.toNat)] eff
                    (errno_ret EINVAL) m []
              | .SkConnected _ _ rx =>
                  match rx 0 with
                  | .cons _ | .fin =>
                      check_ret_only_copyins [(addrp, al.toNat)] eff
                        (errno_ret EINVAL) m []
                  | .rst | .timedOut => .CheckUnmodeled
              | .SkReset _ _ => .CheckUnmodeled
                  -- a reset connection is unbound again and Linux
                  -- autobinds: see `Net.Socket.bind_spec`
  | some _ => check_ret_only eff (errno_ret ENOTSOCK) m []

/-- listen(2).  The backlog is only clamped, never refused, and nothing
    observes the clamped value. -/
def check_listen (fd backlog : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  let _ := backlog
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdSocket sk) =>
      match sk with
      | .SkConnected _ _ _ => check_ret_only eff (errno_ret EINVAL) m []
      | .SkReset _ _ => check_ret_only eff (errno_ret EINVAL) m []
      | .SkListening => check_ret_only eff (BitVec.ofInt 64 0) m []
      | .SkBound =>
          check_ret_only eff (BitVec.ofInt 64 0)
            (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m) []
      | .SkFresh =>
          -- the only arm that autobinds, and so the only one whose
          -- `get_port` can fail
          check_errno_or_success listen_errnos
            (fd_insert (m_fds m) fd (.FdSocket .SkListening))
            (BitVec.ofInt 64 0) eff m
  | some _ => check_ret_only eff (errno_ret ENOTSOCK) m []

/-- accept4(2), which accept(2) reaches with `flags = 0`.  -EBADF comes
    before the flags are even looked at; the connection is taken off the
    environment's queue only on the success arm. -/
def check_accept4 (fd addrp addrlenp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  let _ := addrlenp                      -- untouched while `addrp` is NULL
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      let fl : Int := ((abi_low32 flags).toNat : Int)
      if !(z_ldiff fl (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)
      then check_ret_only eff (errno_ret EINVAL) m []
      else if !(z_land fl SOCK_NONBLOCK == 0) then .CheckUnmodeled
      else
      match e with
      | .FdSocket sk =>
          if !(w_is0 addrp) then .CheckUnmodeled
            -- `SyscallEffect` cannot express the write of the peer
            -- address; see `Net.Socket.accept4_spec`
          else
          match sk with
          | .SkListening =>
              if conn_ix_exhausted (m_conn_ix m)
              then check_errno_only accept_errnos eff m
              else
              check_new_fd_result accept_errnos eff m
                (fun nfd =>
                   with_accepted
                     (fd_insert (m_fds m) nfd
                        (.FdSocket (.SkConnected (nq_peer (m_net m))
                                               (conn_channel (m_conn_ix m))
                                               (nq_script (m_net m))))) m)
          | _ => check_ret_only eff (errno_ret EINVAL) m []
      | _ => check_ret_only eff (errno_ret ENOTSOCK) m []

/-- connect(2).  The arm order is NOT bind's: the address is copied
    before the file is resolved to a socket, so -ENOTSOCK sits BELOW the
    copy and carries its ledger, while -EBADF, the addrlen -EINVAL and
    -EFAULT sit above it and carry none.  See `Net.Socket.connect_spec`. -/
def check_connect (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some e =>
      let al : Int := sint32 addrlen
      if decide (al < 0) || decide (SOCKADDR_STORAGE_SIZE < al)
      then check_ret_only eff (errno_ret EINVAL) m []
      else
      match read_bytes_map i.in_mem addrp (BitVec.ofInt 64 al) with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some bs =>
          let copied : List (word × Nat) :=
            if al == 0 then [] else [(addrp, bs.length)]
          match e with
          | .FdSocket sk =>
              if decide (al < SA_FAMILY_SIZE)
              then check_ret_only_copyins copied eff (errno_ret EINVAL) m []
              else if sa_family_of bs == AF_UNSPEC then
                match sk with
                | .SkFresh =>
                    check_ret_only_copyins copied eff (BitVec.ofInt 64 0) m []
                | .SkBound | .SkListening
                | .SkConnected _ _ _ | .SkReset _ _ => .CheckUnmodeled
              else
                match sk with
                | .SkListening | .SkConnected _ _ _ | .SkReset _ _ =>
                    check_ret_only_copyins copied eff (errno_ret EISCONN) m []
                | .SkFresh | .SkBound =>
                    if decide (al < SOCKADDR_IN_SIZE)
                    then check_ret_only_copyins copied eff (errno_ret EINVAL) m []
                    else if !(sa_family_of bs == AF_INET)
                    then check_ret_only_copyins copied eff (errno_ret EAFNOSUPPORT) m []
                    else .CheckUnmodeled
          | _ => check_ret_only_copyins copied eff (errno_ret ENOTSOCK) m []

/-- All five of getsockname/getpeername/setsockopt/getsockopt/shutdown
    follow one shape: split on `sock_fd`, whose `inr` side is the errno
    half and whose `inl` side is the socket half, then on whatever that
    call's own socket arm branches on.  The five share nothing else, which
    is why there are five acceptors here and not one — see
    `Net.Socket.getsockname_spec` and its four neighbours for the kernel
    argument behind each arm, and for what each of them declines and
    why. -/
def check_getsockname (fd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ => .CheckUnmodeled

def check_getpeername (fd : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl sk =>
      match sk with
      | .SkFresh           => check_ret_only eff (errno_ret ENOTCONN) m []
      | .SkBound           => check_ret_only eff (errno_ret ENOTCONN) m []
      | .SkListening       => check_ret_only eff (errno_ret ENOTCONN) m []
      | .SkReset _ _       => check_ret_only eff (errno_ret ENOTCONN) m []
      | .SkConnected _ _ _ => .CheckUnmodeled

def check_setsockopt (fd level optlen : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ =>
      if int32_neg optlen then check_ret_only eff (errno_ret EINVAL) m []
      else if !(sock_level_known level)
      then check_ret_only eff (errno_ret ENOPROTOOPT) m []
      else .CheckUnmodeled

/-- The ledger here is the whole of what `check_ret_only` could not say.
    `do_sock_getsockopt` reads four bytes at `optlen` before it dispatches
    on the level, so the -EOPNOTSUPP arm expects `eff_copyins` to be
    exactly that range — and the fd errnos above expect it EMPTY, because
    `__sys_getsockopt` answers them before `do_sock_getsockopt` runs at
    all.  See `Net.Socket.getsockopt_spec` for the kernel argument, the
    backported version window, and why an unreadable `optlen` records
    nothing. -/
def check_getsockopt (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl _ =>
      if !(sock_level_known level)
      then check_ret_only_copyins (getsockopt_optlen_read i optlenp) eff
             (errno_ret EOPNOTSUPP) m []
      else .CheckUnmodeled

def check_shutdown (fd how : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match sock_fd m fd with
  | .inr e => check_ret_only eff (errno_ret e) m []
  | .inl sk =>
      if !(shut_how_ok how) then check_ret_only eff (errno_ret EINVAL) m []
      else
        match sk with
        | .SkFresh           => .CheckUnmodeled
        | .SkBound           => .CheckUnmodeled
        | .SkListening =>
            if (how.toNat : Int) == SHUT_WR
            then check_ret_only eff (BitVec.ofInt 64 0) m []
            else .CheckUnmodeled
        | .SkConnected _ _ _ => .CheckUnmodeled
        | .SkReset _ _       => .CheckUnmodeled

/- ------------------------------------------------------- sendto, sendmsg -/

/-- `Net.Socket.send_on_socket` as an acceptor — the socket half both
    calls share, so the short-send rule is decided in ONE place.

    On `Net.Socket.SendGoes` the claimed return picks the delivered
    prefix, exactly as `Fs.ReadWrite.check_write` does on a channel, with
    one extra conjunct: `ret <= total`.  `check_write` gets that bound for
    free (`readable_bytes_length_le`), but `sendmsg` arrives with a
    GATHERED source whose length is not related to the requested total by
    any lemma this file carries, and `Net.Socket.send_bytes` requires it.
    Testing it here keeps both callers honest and needs no lemma at all.

    THE LEDGER IS TESTED ON EVERY ARM, and `pre` is what makes the two
    callers differ: empty for `sendto`, the header and the descriptors
    for `sendmsg`.  An arm that moves no payload byte expects exactly
    `pre`; the delivering arm expects `pre` followed by the ranges the
    delivered prefix came out of.

    `SendErr` accepts the model with the error CONSUMED — `fd_insert`
    onto `SkReset` — because the spec consumes it, and a checker that
    accepted the unchanged model would let a program read the same reset
    twice. -/
def check_send_on_socket (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState)
    (total : word) (bs : List byte) (eff : SyscallEffect) (m : Model)
    : check_result :=
  match send_state sk with
  | .SendGoes ch =>
      if w_is0 total then check_ret_only_copyins pre eff (BitVec.ofInt 64 0) m []
      else if bs.length == 0
      then check_ret_only_copyins pre eff (errno_ret EFAULT) m []
      else
        match eff with
        | ⟨ret, [], [], [], [], copyins⟩ =>
            if decide (1 ≤ (ret.toNat : Int))
               && decide ((ret.toNat : Int) ≤ (bs.length : Int))
               && decide ((ret.toNat : Int) ≤ (total.toNat : Int))
            then
              -- nested, not a fourth `&&`: `decide` evaluates every
              -- operand, and this one converts `ret` to a unary `Nat` —
              -- see `Fs.ReadWrite.check_write`'s channel arm
              if access_ranges_eqb copyins (pre ++ acc ret.toNat)
              then .CheckOk m ((bs.take ret.toNat).map (event.WriteEv ch))
              else .CheckReject
            else .CheckReject
        | _ => .CheckReject
    | .SendErr e peer ch =>
      check_ret_only_copyins pre eff (errno_ret e)
        (with_fds (fd_insert (m_fds m) fd (.FdSocket (.SkReset peer ch))) m) []
  | .SendDead => check_ret_only_copyins pre eff (errno_ret EPIPE) m []

/-- sendto: the three gates, then `import_ubuf`'s range verdict, then the
    fd — and the fd match stays INSIDE `check_access_ok_zero`, because
    that nesting is what makes `sendto(-1, unmapped, n, …)` -EFAULT
    rather than -EBADF. -/
def check_sendto (i : SyscallInput) (fd buf count flags addrp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(send_flags_modeled flags) then .CheckUnmodeled
  else if !(w_is0 addrp) then .CheckUnmodeled
  else if !(modeled_rw_count count) then .CheckUnmodeled
  else
    check_access_ok_zero buf count eff m
      (match fd_lookup (m_fds m) fd with
       | none => check_ret_only eff (errno_ret EBADF) m []
       | some (.FdSocket sk) =>
           check_send_on_socket [] (fun n => [(buf, n)]) fd sk count
             (readable_bytes i.in_mem buf count) eff m
       | some _ => check_ret_only eff (errno_ret ENOTSOCK) m [])

/-- sendmsg: the fd FIRST and the header second, the opposite nesting to
    `check_sendto` — deliberately not shared with it.  The expected
    ledger is spelled out arm by arm rather than accumulated by a
    wrapper, so that a reader can see at each answer exactly which user
    bytes the kernel had read by the time it gave that answer. -/
def check_sendmsg (i : SyscallInput) (fd msgp flags : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(send_flags_modeled flags) then .CheckUnmodeled
  else
  match fd_lookup (m_fds m) fd with
  | none => check_ret_only eff (errno_ret EBADF) m []
  | some (.FdChannel _) | some (.FdFile _ _)
  | some (.FdFileW _ _) | some .FdDir
  | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some (.FdPipe _ _) | some (.FdDevNull _ _) | some .FdUrandom =>
      check_ret_only eff (errno_ret ENOTSOCK) m []
  | some (.FdSocket sk) =>
      match read_bytes_map i.in_mem msgp (BitVec.ofInt 64 MSGHDR_SIZE) with
      | none => check_ret_only eff (errno_ret EFAULT) m []
      | some _ =>
          match read_u64 i.in_mem msgp,
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 8),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 16),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 24),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 32),
                read_u64 i.in_mem (msgp + BitVec.ofInt 64 40) with
          | some name, some _, some iov, some iovlen, some _, some ctllen =>
              if !(w_is0 name) then .CheckUnmodeled
              else if decide (IOV_MAX < (iovlen.toNat : Int))
              then check_ret_only_copyins [(msgp, MSGHDR_SIZE.toNat)] eff
                     (errno_ret EMSGSIZE) m []
              else if decide (UIO_FASTIOV < (iovlen.toNat : Int)) then .CheckUnmodeled
              else
              match copy_iovecs_aux i.in_mem iov (word_to_nat iovlen) with
              | .ImpFault =>
                  check_ret_only_copyins
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    eff (errno_ret EFAULT) m []
              | .ImpInval =>
                  check_ret_only_copyins
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    eff (errno_ret EINVAL) m []
              | .ImpOk iovs0 =>
                  -- msg_controllen is decided HERE, where ____sys_sendmsg
                  -- decides it: after the descriptors are imported, not
                  -- before.  Ordering is behaviour — a call with a
                  -- non-zero controllen AND iovlen over IOV_MAX answers
                  -- -EMSGSIZE above rather than declining here.
                  if !(w_is0 ctllen) then .CheckUnmodeled
                  else if !(decide (iovs_total (cap_iovecs iovs0) ≤ rw_bytes_max))
                  then .CheckUnmodeled
                  else
                  check_send_on_socket
                    ([(msgp, MSGHDR_SIZE.toNat)]
                     ++ copy_iovecs_accesses i.in_mem iov (word_to_nat iovlen))
                    (fun n => iov_prefix_accesses (cap_iovecs iovs0) n)
                    fd sk
                    (BitVec.ofInt 64 (iovs_total (cap_iovecs iovs0)))
                    (writev_gathered i.in_mem iovs0) eff m
          | _, _, _, _, _, _ =>
              check_ret_only_copyins [(msgp, MSGHDR_SIZE.toNat)] eff
                (errno_ret EFAULT) m []

/- ------------------------------------------------- recvfrom, recvmsg ----
   and the shared descriptor answer both of them delegate to. -/

/-- `Specs.recv_fd_answer` as an acceptor: the errno, or the decline a
    socket fd takes at these two entry points. -/
def check_recv_fd_answer (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match sockfd_lookup_errno fds fd with
  | some e => check_ret_only eff (errno_ret e) m []
  | none => .CheckUnmodeled

/- -------------------------------------------------------------------------
   The two shared acceptors' `m_vmmaps` frames (PUBLIC)

   [Checks/VmMapsDisjoint.lean] must show that each checker leaves
   [m_vmmaps] alone.  Its `vm_frame` loop does that by unfolding the
   checker and casing the result hypothesis, and for the `sendmsg` /
   `sendto` / `recvfrom` / `recvmsg` arms the accepting branch leaves THIS
   module through the two helpers below, whose walks are `send_state sk`
   and `sockfd_lookup_errno` plus a copy-in wrapper — the same situation
   `Checks/Sys/Fs/Open.lean`'s `check_ftruncate_file_arm_frame` and
   `Checks/Sys/Fs/Namei.lean`'s `check_unlinkat_body_frame` answer for
   their helpers, and these are the two facts that loop needs.

   The facts are stated HERE, next to the `*_sound_ok` that already walks
   the same bodies (`Socket/Send.lean`), and PUBLIC because the citing
   module is another one.  Each proof is the checker side of that
   soundness walk with the spec dropped: every accepting branch hands back
   the caller's model or a `with_fds`/`with_copyins` rebuild of it, and a
   projection of a structure update is the old projection by `rfl`.
   ------------------------------------------------------------------------- -/

/-- An accepted [check_ret_only] hands back the model it was
    given, so it leaves [m_vmmaps] alone.  The one-projection corollary of
    `check_ret_only_ok_iff`. -/
private theorem net_ret_only_frame (eff : SyscallEffect) (r : word)
    (m m' : Model) (evs : List event)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨-, rfl, -⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  rfl

/-- The same for the copy-in ledger wrapper — accepted, it
    hands back the model it was given. -/
private theorem net_ret_only_copyins_frame (reads : List (word × Nat))
    (eff : SyscallEffect) (r : word) (m m' : Model) (evs : List event)
    (H : check_ret_only_copyins reads eff r m [] = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  obtain ⟨-, rfl, -⟩ := (check_ret_only_copyins_ok_iff reads eff r m [] m' evs).mp H
  rfl

/-- The socket half `sendto` and `sendmsg` share leaves [m_vmmaps] alone.
    Its one model rebuild is [SendErr]'s `fd_insert` onto `SkReset`; the
    delivering arm hands back `m` itself.  Public because the citing frame
    is in another module. -/
theorem check_send_on_socket_frame (pre : List (word × Nat))
    (acc : Nat → List (word × Nat)) (fd : word) (sk : SockState) (total : word)
    (bs : List byte) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_send_on_socket pre acc fd sk total bs eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_send_on_socket at H
  cases hst : send_state sk with
  | SendDead =>
    simp only [hst] at H
    exact net_ret_only_copyins_frame pre eff (errno_ret EPIPE) m m' evs H
  | SendErr e peer ch =>
    simp only [hst] at H
    exact net_ret_only_copyins_frame pre eff (errno_ret e)
      (with_fds (fd_insert (m_fds m) fd
        (FdEntry.FdSocket (SockState.SkReset peer ch))) m) m' evs H
  | SendGoes ch =>
    simp only [hst] at H
    by_cases ht : w_is0 total = true
    · simp only [ht, ite_true] at H
      exact net_ret_only_copyins_frame pre eff (BitVec.ofInt 64 0) m m' evs H
    · simp only [ht, Bool.false_eq_true, ite_false] at H
      by_cases hb : (bs.length == 0) = true
      · simp only [hb, ite_true] at H
        exact net_ret_only_copyins_frame pre eff (errno_ret EFAULT) m m' evs H
      · simp only [hb, Bool.false_eq_true, ite_false] at H
        obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
        cases ws <;> cases zs <;> cases us <;> cases cs
        · simp only [] at H
          by_cases hg : (decide (1 ≤ (ret.toNat : Int))
              && decide ((ret.toNat : Int) ≤ (bs.length : Int))
              && decide ((ret.toNat : Int) ≤ (total.toNat : Int))) = true
          · simp only [hg, ite_true] at H
            by_cases hr : access_ranges_eqb ks (pre ++ acc ret.toNat) = true
            · simp only [hr, ite_true, check_result.CheckOk.injEq] at H
              obtain ⟨rfl, rfl⟩ := H
              rfl
            · simp only [hr, Bool.false_eq_true, ite_false] at H
              exact nomatch H
          · simp only [hg, Bool.false_eq_true, ite_false] at H
            exact nomatch H
        all_goals (simp only [] at H; exact nomatch H)

/-- The descriptor answer `recvfrom` and `recvmsg` share is a pure
    observation (an errno, or a decline), so it leaves [m_vmmaps] alone.
    Public for the same reason as the lemma above. -/
theorem check_recv_fd_answer_frame (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_recv_fd_answer fds fd eff m = .CheckOk m' evs) :
    m_vmmaps m' = m_vmmaps m := by
  unfold check_recv_fd_answer at H
  generalize hsl : sockfd_lookup_errno fds fd = o at H
  cases o with
  | none => exact nomatch H
  | some e => exact net_ret_only_frame eff (errno_ret e) m m' evs H

/-- socketpair's answer once the 8-byte destination is known writable:
    either a reservation errno with `usockvec` untouched, or the two
    descriptor writes with -EOPNOTSUPP or one of the post-write errnos.
    Two shapes, and the write list is what tells them apart — which is
    the fact this whole arm exists to state.  See `Specs.socketpair_spec`. -/
def check_socketpair_written (sv fd1 fd2 : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  match eff with
  | ⟨r, [], [], [], [], []⟩ =>
      if errno_ret_in socketpair_reserve_errnos r
      then .CheckOk m [] else .CheckReject
  | ⟨r, ws, [], [], [], []⟩ =>
      if writes_eqb ws (socketpair_writes sv fd1 fd2)
         && (bv_eqb r (errno_ret EOPNOTSUPP)
             || errno_ret_in socketpair_create_errnos r)
      then .CheckOk m [] else .CheckReject
  | _ => .CheckReject

/-- The same when the FIRST `put_user`'s own 4-byte range is one every
    riscv64 `access_ok` refuses: that store fails, so nothing is written
    on any path. -/
def check_socketpair_faulted (eff : SyscallEffect) (m : Model)
    : check_result :=
  match eff with
  | ⟨r, [], [], [], [], []⟩ =>
      if errno_ret_in socketpair_reserve_errnos r || bv_eqb r (errno_ret EFAULT)
      then .CheckOk m [] else .CheckReject
  | _ => .CheckReject

def check_socketpair (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(socketpair_flags_ok type)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !(socketpair_modeled_b family type protocol) then .CheckUnmodeled
  else
  match socketpair_fds (m_fds m) with
  | none => .CheckUnmodeled
  | some (fd1, fd2) =>
      if socketpair_dest_writable i.in_wmem sv
      then check_socketpair_written sv fd1 fd2 eff m
      else
        -- 4, not 8, and the walk is guarded by `State.access_okb` before
        -- it is consulted: see `Specs.socketpair_spec`.
        if !(access_okb sv 4)
        then check_socketpair_faulted eff m
        else .CheckUnmodeled

/-- recvfrom: the buffer's range verdict first (the kernel imports it
    before it resolves the descriptor), then -EBADF / -ENOTSOCK.  No byte
    moves on any path, so `check_access_ok_zero` is exactly the right
    acceptor.  See `Specs.recvfrom_spec`. -/
def check_recvfrom (_i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !(modeled_rw_count size) then .CheckUnmodeled
  else check_access_ok_zero buf size eff m
         (check_recv_fd_answer (m_fds m) fd eff m)

/-- recvmsg: MSG_CMSG_COMPAT is fail-closed (its value is a kernel
    configuration), and otherwise the descriptor alone decides — the
    message header is never read.  See `Specs.recvmsg_spec`. -/
def check_recvmsg (fd flags : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if !(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0)
  then .CheckUnmodeled
  else check_recv_fd_answer (m_fds m) fd eff m



/- =========================================================================
   Inverting one monadic step

   Every proof that has to walk *into* a spec's outcome needs the shape of
   that outcome spelled out.  `inv_ok` is deliberately limited (see its
   note in `Checks.Sys.Prelude`) and cannot invert an existential or split
   a second conjunction, so the three shapes this file needs are stated
   once here:
   a `choose` step, a `pure`/`ret_only` step, and the `set_fds` setter.
   Each returns its equations ORIENTED for `rw`, so a caller substitutes
   deliberately instead of relying on `subst`'s variable choice.
   ========================================================================= -/

private theorem choose_ok_inv (es : List Int) (i : SyscallInput) (m : Model)
    (e : Int) (m1 : Model) (evs1 : List event)
    (H : errno_from es i m (.ok e m1 evs1)) :
    e ∈ es ∧ m1 = m ∧ evs1 = [] := by
  unfold errno_from choose at H
  obtain ⟨x, hx, hok⟩ := H
  simp only [Outcome.ok.injEq] at hok
  obtain ⟨rfl, rfl, rfl⟩ := hok
  exact ⟨hx, rfl, rfl⟩

private theorem ret_only_ok_inv (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : ret_only r i m (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  unfold ret_only LinuxSem.LinuxProcessSem.pure at H
  simp only [Outcome.ok.injEq] at H
  exact ⟨H.1, H.2.1, H.2.2⟩

private theorem set_fds_ok_inv (fds : List (word × FdEntry)) (i : SyscallInput)
    (m : Model) (u : Unit) (m1 : Model) (evs1 : List event)
    (H : set_fds fds i m (.ok u m1 evs1)) :
    m1 = with_fds fds m ∧ evs1 = [] := by
  unfold set_fds modifySpec LinuxSem.LinuxProcessSem.modify at H
  simp only [Outcome.ok.injEq] at H
  exact ⟨H.2.1, H.2.2⟩

/-- The introduction form of `ret_only` at its own word — `pure_ok`
    applied through the abbreviation, which `pure_ok` cannot see. -/
private theorem ret_only_ok (r : word) (i : SyscallInput) (m : Model) :
    ret_only r i m (.ok (mkEffect r [] []) m []) := by
  unfold ret_only LinuxSem.LinuxProcessSem.pure
  rfl

/- =========================================================================
   errno-or-nothing acceptors
   ========================================================================= -/

theorem check_errno_only_no_unmodeled (es : List Int) (eff : SyscallEffect)
    (m : Model) : check_errno_only es eff m ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_errno_only
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · by_cases h : errno_ret_in es ret = true <;> simp [h]
  all_goals simp

/-- `check_errno_only` is exact for such an `alt`.  The
    `choose (fun _ => False)` is what makes all three hold: it
    contributes no `Ok` and, being a `choose` rather than `unmodeled`, no
    `Unmodeled` either. -/
theorem check_errno_only_sound_ok (es : List Int) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_errno_only es eff m = .CheckOk m' evs) :
    alt (bind (errno_from es) (fun e => err_ret e)) (choose (fun _ => False))
        i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_errno_only at H
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · by_cases h : errno_ret_in es ret = true
    · simp only [h, ite_true, check_result.CheckOk.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true es ret).mp h
      exact alt_l _ _ _ _ _ (bind_ok0 _ _ i m e m _ m []
        (choose_ok _ e i m hmem) (pure_ok _ i m))
    · simp only [h, Bool.false_eq_true, ite_false] at H
      exact nomatch H
  all_goals simp at H

theorem check_errno_only_complete_ok (es : List Int) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : alt (bind (errno_from es) (fun e => err_ret e)) (choose (fun _ => False))
        i m (.ok eff m' evs)) :
    check_errno_only es eff m = .CheckOk m' evs := by
  rcases H with H | Hno
  · obtain ⟨e, m1, evs1, evs2, Hch, Hret, heq⟩ := H
    obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv es i m e m1 evs1 Hch
    rw [hm1] at Hret
    obtain ⟨heff, hm', hevs2⟩ := ret_only_ok_inv (errno_ret e) i m eff m' evs2 Hret
    rw [hevs2, List.append_nil, hevs1] at heq
    rw [heff, hm', heq]
    simp [check_errno_only, errno_ret_in_intro es e hmem]
  · unfold choose at Hno
    obtain ⟨x, hx, -⟩ := Hno
    exact absurd hx (by simp)

/- --------------------------------------------------- errno-or-success -/

theorem check_errno_or_success_sound_ok (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_errno_or_success es fds r eff m = .CheckOk m' evs) :
    alt (bind (errno_from es) (fun e => err_ret e))
        (bind (set_fds fds) (fun _ => ret_only r)) i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_errno_or_success at H
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · by_cases h : errno_ret_in es ret = true
    · simp only [h, ite_true, check_result.CheckOk.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      obtain ⟨e, hmem, rfl⟩ := (errno_ret_in_true es ret).mp h
      exact alt_l _ _ _ _ _ (bind_ok0 _ _ i m e m _ m []
        (choose_ok _ e i m hmem) (pure_ok _ i m))
    · simp only [h, Bool.false_eq_true, ite_false] at H
      by_cases hr : bv_eqb ret r = true
      · have hret : ret = r := (Fs.bv_eqb_eq ret r).mp hr
        rw [hret] at H ⊢
        simp only [bv_eqb_refl, ite_true, check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        refine alt_r _ _ _ _ _ (bind_ok0 (set_fds fds) (fun _ => ret_only r) i m ()
          (with_fds fds m) _ (with_fds fds m) [] ?_ (ret_only_ok r i (with_fds fds m)))
        unfold set_fds modifySpec
        exact modify_ok _ i m
      · simp only [hr, Bool.false_eq_true, ite_false] at H
        exact nomatch H
  all_goals simp at H

theorem check_errno_or_success_no_unmodeled (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (eff : SyscallEffect) (m : Model) :
    check_errno_or_success es fds r eff m ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, copyins⟩ := eff
  unfold check_errno_or_success
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases copyins
  · by_cases h : errno_ret_in es ret = true <;>
      by_cases hr : bv_eqb ret r = true <;> simp [h, hr]
  all_goals simp

/-- The success return must not read as one of the injectable errnos, or
    the errno arm would swallow it and report the wrong model.  Both call
    sites return 0 and discharge this by evaluation. -/
theorem check_errno_or_success_complete_ok (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (Hne : errno_ret_in es r = false)
    (H : alt (bind (errno_from es) (fun e => err_ret e))
        (bind (set_fds fds) (fun _ => ret_only r)) i m (.ok eff m' evs)) :
    check_errno_or_success es fds r eff m = .CheckOk m' evs := by
  rcases H with Herr | Hok
  · obtain ⟨e, m1, evs1, evs2, Hch, Hret, heq⟩ := Herr
    obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv es i m e m1 evs1 Hch
    rw [hm1] at Hret
    obtain ⟨heff, hm', hevs2⟩ := ret_only_ok_inv (errno_ret e) i m eff m' evs2 Hret
    rw [hevs2, List.append_nil, hevs1] at heq
    rw [heff, hm', heq]
    simp [check_errno_or_success, errno_ret_in_intro es e hmem]
  · obtain ⟨u, m1, evs1, evs2, Hch, Hret, heq⟩ := Hok
    obtain ⟨hm1, hevs1⟩ := set_fds_ok_inv fds i m u m1 evs1 Hch
    rw [hm1] at Hret
    obtain ⟨heff, hm', hevs2⟩ := ret_only_ok_inv r i (with_fds fds m) eff m' evs2 Hret
    rw [hevs2, List.append_nil, hevs1] at heq
    rw [heff, hm', heq]
    simp [check_errno_or_success, Hne, bv_eqb_refl]

theorem errno_or_success_no_unmodeled (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput) (m : Model) :
    ¬ alt (bind (errno_from es) (fun e => err_ret e))
        (bind (set_fds fds) (fun _ => ret_only r)) i m .unmodeled := by
  intro H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with H1 | H2
  · -- the errno half: a `choose` step, then `pure`, neither of which declines
    rcases H1 with Hc | ⟨e, m1, evs1, Hch, Hret⟩
    · unfold errno_from choose at Hc
      obtain ⟨x, hx, hok⟩ := Hc
      simp at hok
    · obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv es i m e m1 evs1 Hch
      rw [hm1] at Hret
      simp [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at Hret
  · -- the success half: a `modify`, then `pure`
    rcases H2 with Hc | ⟨u, m1, evs1, Hch, Hret⟩
    · unfold set_fds modifySpec LinuxSem.LinuxProcessSem.modify at Hc
      cases Hc
    · obtain ⟨hm1, hevs1⟩ := set_fds_ok_inv fds i m u m1 evs1 Hch
      rw [hm1] at Hret
      simp [ret_only, LinuxSem.LinuxProcessSem.pure] at Hret

/-- The premise is unsatisfiable, so the conclusion is free. -/
theorem check_errno_or_success_complete_unmodeled (es : List Int)
    (fds : List (word × FdEntry)) (r : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect)
    (H : alt (bind (errno_from es) (fun e => err_ret e))
        (bind (set_fds fds) (fun _ => ret_only r)) i m .unmodeled) :
    check_errno_or_success es fds r eff m = .CheckUnmodeled := by
  exact absurd H (errno_or_success_no_unmodeled es fds r i m)

/- =========================================================================
   The arm correspondences and the fresh-descriptor bound

   `Checks/Sys/Fs/Open.lean` carries `alloc_fd_aux_le`, `alloc_fd_le`,
   `alloc_fd_not_error_b` and `errno_ret_in_alloc_fd`, and the `socket`
   proofs need the last of them.  That file is not in this module's import
   cone — pulling it in here would drag the whole `Fs` checker tree into
   this arm — so the four are restated here verbatim; they can go with the
   `check_new_fd_result` copy above if that import edge is ever taken.
   ========================================================================= -/

theorem alloc_fd_aux_le (fds : List (word × FdEntry)) (cand : word) (f : Nat)
    (h : cand.toNat + f < 2 ^ 64) :
    (alloc_fd_aux fds cand f).toNat ≤ cand.toNat + f := by
  induction f generalizing cand with
  | zero => simp [alloc_fd_aux]
  | succ f ih =>
    rw [show alloc_fd_aux fds cand (f + 1) =
        (match fd_lookup fds cand with
         | none => cand
         | some _ => alloc_fd_aux fds (cand + 1) f) from rfl]
    split
    · omega
    · have h1 : cand.toNat + 1 < 2 ^ 64 := by omega
      have hsucc : (cand + 1).toNat = cand.toNat + 1 := by
        have hone : ((1 : word)).toNat = 1 := by decide
        rw [BitVec.toNat_add, hone, Nat.mod_eq_of_lt h1]
      have h2 : (cand + 1).toNat + f < 2 ^ 64 := by rw [hsucc]; omega
      have h3 := ih (cand + 1) h2
      rw [hsucc] at h3
      omega

theorem alloc_fd_le (fds : List (word × FdEntry)) : (alloc_fd fds).toNat ≤ 4096 := by
  unfold alloc_fd
  have h0 : (BitVec.ofInt 64 0 : word).toNat = 0 := by decide
  have h1 : (BitVec.ofInt 64 0 : word).toNat + 4096 < 2 ^ 64 := by
    rw [h0]
    decide
  simpa [h0] using alloc_fd_aux_le fds (BitVec.ofInt 64 0) 4096 h1

theorem alloc_fd_not_error_b (fds : List (word × FdEntry)) :
    addr_is_error_b (alloc_fd fds) = false := by
  have h := alloc_fd_le fds
  unfold addr_is_error_b
  rw [decide_eq_false_iff_not]
  unfold two_pow_64
  omega

theorem errno_ret_in_alloc_fd (es : List Int) (fds : List (word × FdEntry))
    (Hok : errnos_ok es = true) : errno_ret_in es (alloc_fd fds) = false := by
  apply errno_ret_in_fd es (alloc_fd fds) Hok
  have h := alloc_fd_le fds
  have h2 : (4096 : Int) < 2147483648 := by decide
  show ((alloc_fd fds).toNat : Int) < 2147483648
  omega

/-- Checker → spec, for one arm answering through `check_ret_only`: an
    accepted `check_ret_only` *is* the spec's `ret_only` at that word,
    with the claimed model and events. -/
private theorem arm_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_ret_only eff r m [] = .CheckOk m' evs) :
    ret_only r i m (.ok eff m' evs) := by
  obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff eff r m [] m' evs).mp H
  rw [heff, hm, hevs]
  exact ret_only_ok r i m

/-- Spec → checker, for one arm: an outcome of the spec's `ret_only` at
    that word is accepted by `check_ret_only` at the same word. -/
private theorem arm_check_ok (r : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : ret_only r i m (.ok eff m' evs)) :
    check_ret_only eff r m [] = .CheckOk m' evs := by
  obtain ⟨heff, hm, hevs⟩ := ret_only_ok_inv r i m eff m' evs H
  rw [heff, hm, hevs]
  simp [check_ret_only, bv_eqb_refl]

/-- Checker → spec, for one arm that answers after installing a new fd
    table: `check_ret_only` at the narrowed model *is* the spec's
    `set_fds … ;; ret_only …`. -/
private theorem arm_set_fds_ok (fds : List (word × FdEntry)) (r : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_ret_only eff r (with_fds fds m) [] = .CheckOk m' evs) :
    bind (set_fds fds) (fun _ => ret_only r) i m (.ok eff m' evs) := by
  obtain ⟨heff, hm, hevs⟩ := (check_ret_only_ok_iff eff r (with_fds fds m) [] m' evs).mp H
  rw [heff, hm, hevs]
  refine bind_ok0 (set_fds fds) (fun _ => ret_only r) i m () (with_fds fds m)
    _ (with_fds fds m) [] ?_ (ret_only_ok r i (with_fds fds m))
  unfold set_fds modifySpec
  exact modify_ok _ i m

/-- Spec → checker for the same arm. -/
private theorem arm_set_fds_check_ok (fds : List (word × FdEntry)) (r : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : bind (set_fds fds) (fun _ => ret_only r) i m (.ok eff m' evs)) :
    check_ret_only eff r (with_fds fds m) [] = .CheckOk m' evs := by
  obtain ⟨u, m1, evs1, evs2, Hch, Hret, heq⟩ := H
  obtain ⟨hm1, hevs1⟩ := set_fds_ok_inv fds i m u m1 evs1 Hch
  rw [hm1] at Hret
  obtain ⟨heff, hm', hevs2⟩ := ret_only_ok_inv r i (with_fds fds m) eff m' evs2 Hret
  rw [hevs1, List.nil_append, hevs2] at heq
  rw [heff, hm', heq]
  simp [check_ret_only, bv_eqb_refl]

/-- `ret_only` — hence `err_ret` — never declines: `pure` has one outcome
    shape. -/
private theorem ret_only_ne_unmodeled (r : word) (i : SyscallInput) (m : Model) :
    ¬ ret_only r i m .unmodeled := by
  intro H
  unfold ret_only LinuxSem.LinuxProcessSem.pure at H
  exact nomatch H

/- =========================================================================
   listen
   ========================================================================= -/

theorem check_listen_sound_ok (fd backlog : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_listen fd backlog eff m = .CheckOk m' evs) :
    listen_spec fd backlog i m (.ok eff m' evs) := by
  unfold check_listen at H
  unfold listen_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdSocket sk =>
      cases sk <;> dsimp only at H ⊢
      · -- fresh: the autobind can fail with -EADDRINUSE
        exact check_errno_or_success_sound_ok listen_errnos _ _ i eff m m' evs H
      · -- bound: `get_port` cannot fail
        exact arm_set_fds_ok _ _ eff m m' evs i H
      · -- re-listen: the backlog only
        exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · exact arm_ok (errno_ret EINVAL) eff m m' evs i H
      · exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    | _ => exact arm_ok (errno_ret ENOTSOCK) eff m m' evs i H

theorem check_listen_sound_unmodeled (fd backlog : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_listen fd backlog eff m = .CheckUnmodeled) :
    listen_spec fd backlog i m .unmodeled := by
  unfold check_listen at H
  unfold listen_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdSocket sk =>
      cases sk <;> dsimp only at H ⊢
      · exact absurd H (check_errno_or_success_no_unmodeled listen_errnos _ _ eff m)
      · exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0)
          (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkListening)) m) [])
      · exact absurd H (check_ret_only_no_unmodeled eff _ m [])
      · exact absurd H (check_ret_only_no_unmodeled eff _ m [])
      · exact absurd H (check_ret_only_no_unmodeled eff _ m [])
    | _ => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTSOCK) m [])

theorem check_listen_complete_ok (fd backlog : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : listen_spec fd backlog i m (.ok eff m' evs)) :
    check_listen fd backlog eff m = .CheckOk m' evs := by
  unfold check_listen
  simp only [listen_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact arm_check_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdSocket sk =>
      cases sk <;> dsimp only at H ⊢
      · exact check_errno_or_success_complete_ok listen_errnos _ _ i eff m m' evs
          (by decide) H
      · exact arm_set_fds_check_ok _ _ eff m m' evs i H
      · exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
      · exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    | _ => exact arm_check_ok (errno_ret ENOTSOCK) eff m m' evs i H

theorem check_listen_complete_unmodeled (fd backlog : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : listen_spec fd backlog i m .unmodeled) :
    check_listen fd backlog eff m = .CheckUnmodeled := by
  unfold check_listen
  simp only [listen_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact absurd H (ret_only_ne_unmodeled (errno_ret EBADF) i m)
  | some e =>
    cases e with
    | FdSocket sk =>
      cases sk <;> dsimp only at H ⊢
      · exact check_errno_or_success_complete_unmodeled listen_errnos _ _ i m eff H
      · exact absurd H (by
          unfold seqSpec LinuxSem.LinuxProcessSem.bind at H
          rcases H with hc | ⟨x, m1, evs1, hc, hk⟩
          · unfold set_fds modifySpec LinuxSem.LinuxProcessSem.modify at hc
            cases hc
          · simp [ret_only, LinuxSem.LinuxProcessSem.pure] at hk)
      · exact absurd H (ret_only_ne_unmodeled (BitVec.ofInt 64 0) i m)
      · exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
      · exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
    | _ => exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m)

/- =========================================================================
   getsockname, getpeername, setsockopt, shutdown

   All four follow one shape: split on `sock_fd`, whose `inr` side is the
   errno half and whose `inl` side is the socket half, then on whatever
   that call's own socket arm branches on.
   ========================================================================= -/

theorem check_getsockname_sound_ok (fd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_getsockname fd eff m = .CheckOk m' evs) :
    getsockname_spec fd i m (.ok eff m' evs) := by
  unfold check_getsockname at H
  unfold getsockname_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inl sk => exact nomatch H
  | inr e => exact arm_ok (errno_ret e) eff m m' evs i H

theorem check_getsockname_sound_unmodeled (fd : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_getsockname fd eff m = .CheckUnmodeled) :
    getsockname_spec fd i m .unmodeled := by
  unfold check_getsockname at H
  unfold getsockname_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inl sk => exact unmodeled_intro i m
  | inr e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])

theorem check_getsockname_complete_ok (fd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : getsockname_spec fd i m (.ok eff m' evs)) :
    check_getsockname fd eff m = .CheckOk m' evs := by
  unfold check_getsockname
  simp only [getsockname_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inl sk => exact nomatch H
  | inr e => exact arm_check_ok (errno_ret e) eff m m' evs i H

theorem check_getsockname_complete_unmodeled (fd : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : getsockname_spec fd i m .unmodeled) :
    check_getsockname fd eff m = .CheckUnmodeled := by
  unfold check_getsockname
  simp only [getsockname_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inl sk => rfl
  | inr e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)

theorem check_getpeername_sound_ok (fd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_getpeername fd eff m = .CheckOk m' evs) :
    getpeername_spec fd i m (.ok eff m' evs) := by
  unfold check_getpeername at H
  unfold getpeername_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases sk
    case inl.SkFresh => try dsimp only at H ⊢; exact arm_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkBound => try dsimp only at H ⊢; exact arm_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkListening => try dsimp only at H ⊢; exact arm_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkConnected => try dsimp only at H ⊢; exact nomatch H
    case inl.SkReset => try dsimp only at H ⊢; exact arm_ok (errno_ret ENOTCONN) eff m m' evs i H

theorem check_getpeername_sound_unmodeled (fd : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_getpeername fd eff m = .CheckUnmodeled) :
    getpeername_spec fd i m .unmodeled := by
  unfold check_getpeername at H
  unfold getpeername_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])
  | inl sk =>
    cases sk
    case inl.SkFresh => try dsimp only at H ⊢; exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
    case inl.SkBound => try dsimp only at H ⊢; exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
    case inl.SkListening => try dsimp only at H ⊢; exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])
    case inl.SkConnected => try dsimp only at H ⊢; exact unmodeled_intro i m
    case inl.SkReset => try dsimp only at H ⊢; exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTCONN) m [])

theorem check_getpeername_complete_ok (fd : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : getpeername_spec fd i m (.ok eff m' evs)) :
    check_getpeername fd eff m = .CheckOk m' evs := by
  unfold check_getpeername
  simp only [getpeername_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_check_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases sk
    case inl.SkFresh => try dsimp only at H ⊢; exact arm_check_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkBound => try dsimp only at H ⊢; exact arm_check_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkListening => try dsimp only at H ⊢; exact arm_check_ok (errno_ret ENOTCONN) eff m m' evs i H
    case inl.SkConnected => try dsimp only at H ⊢; exact nomatch H
    case inl.SkReset => try dsimp only at H ⊢; exact arm_check_ok (errno_ret ENOTCONN) eff m m' evs i H

theorem check_getpeername_complete_unmodeled (fd : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : getpeername_spec fd i m .unmodeled) :
    check_getpeername fd eff m = .CheckUnmodeled := by
  unfold check_getpeername
  simp only [getpeername_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)
  | inl sk =>
    cases sk
    case inl.SkFresh => try dsimp only at H ⊢; exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTCONN) i m)
    case inl.SkBound => try dsimp only at H ⊢; exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTCONN) i m)
    case inl.SkListening => try dsimp only at H ⊢; exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTCONN) i m)
    case inl.SkConnected => rfl
    case inl.SkReset => try dsimp only at H ⊢; exact absurd H (ret_only_ne_unmodeled (errno_ret ENOTCONN) i m)

/-- The `sk` half of `check_setsockopt` is not reached: `sock_fd` already
    collapsed it.  `int32_neg` and `sock_level_known` are `Bool`s, so the
    two tests are `cases` on the value (`by_cases` on `= true` blows the
    recursion budget on these goals). -/
theorem check_setsockopt_sound_ok (fd level optlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_setsockopt fd level optlen eff m = .CheckOk m' evs) :
    setsockopt_spec fd level optlen i m (.ok eff m' evs) := by
  unfold check_setsockopt at H
  unfold setsockopt_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
      cases hl : (!(sock_level_known level))
      · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hl, ite_true] at H ⊢
        exact arm_ok (errno_ret ENOPROTOOPT) eff m m' evs i H
    · simp only [hn, ite_true] at H ⊢
      exact arm_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_setsockopt_sound_unmodeled (fd level optlen : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_setsockopt fd level optlen eff m = .CheckUnmodeled) :
    setsockopt_spec fd level optlen i m .unmodeled := by
  unfold check_setsockopt at H
  unfold setsockopt_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])
  | inl sk =>
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
      cases hl : (!(sock_level_known level))
      · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢
        exact unmodeled_intro i m
      · simp only [hl, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOPROTOOPT) m [])
    · simp only [hn, ite_true] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_setsockopt_complete_ok (fd level optlen : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : setsockopt_spec fd level optlen i m (.ok eff m' evs)) :
    check_setsockopt fd level optlen eff m = .CheckOk m' evs := by
  unfold check_setsockopt
  simp only [setsockopt_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_check_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
      cases hl : (!(sock_level_known level))
      · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hl, ite_true] at H ⊢
        exact arm_check_ok (errno_ret ENOPROTOOPT) eff m m' evs i H
    · simp only [hn, ite_true] at H ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_setsockopt_complete_unmodeled (fd level optlen : word)
    (m : Model) (i : SyscallInput) (eff : SyscallEffect)
    (H : setsockopt_spec fd level optlen i m .unmodeled) :
    check_setsockopt fd level optlen eff m = .CheckUnmodeled := by
  unfold check_setsockopt
  simp only [setsockopt_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)
  | inl sk =>
    cases hn : int32_neg optlen
    · simp only [hn, Bool.false_eq_true, ite_false] at H ⊢
      cases hl : (!(sock_level_known level))
      · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
      · simp only [hl, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret ENOPROTOOPT) i m)
    · simp only [hn, ite_true] at H ⊢
      exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

theorem check_shutdown_sound_ok (fd how : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_shutdown fd how eff m = .CheckOk m' evs) :
    shutdown_spec fd how i m (.ok eff m' evs) := by
  unfold check_shutdown at H
  unfold shutdown_spec
  refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases sk
    case inl.SkFresh =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkBound =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkListening =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        cases hw : ((how.toNat : Int) == SHUT_WR)
        · simp only [hw, Bool.false_eq_true, ite_false] at H ⊢
          exact nomatch H
        · simp only [hw, ite_true] at H ⊢
          exact arm_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · simp only [hh, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkConnected =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkReset =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_shutdown_sound_unmodeled (fd how : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_shutdown fd how eff m = .CheckUnmodeled) :
    shutdown_spec fd how i m .unmodeled := by
  unfold check_shutdown at H
  unfold shutdown_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])
  | inl sk =>
    cases sk
    case inl.SkFresh =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact unmodeled_intro i m
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    case inl.SkBound =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact unmodeled_intro i m
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    case inl.SkListening =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        cases hw : ((how.toNat : Int) == SHUT_WR)
        · simp only [hw, Bool.false_eq_true, ite_false] at H ⊢
          exact unmodeled_intro i m
        · simp only [hw, ite_true] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    case inl.SkConnected =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact unmodeled_intro i m
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
    case inl.SkReset =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact unmodeled_intro i m
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_shutdown_complete_ok (fd how : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : shutdown_spec fd how i m (.ok eff m' evs)) :
    check_shutdown fd how eff m = .CheckOk m' evs := by
  unfold check_shutdown
  simp only [shutdown_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_check_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases sk
    case inl.SkFresh =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkBound =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkListening =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        cases hw : ((how.toNat : Int) == SHUT_WR)
        · simp only [hw, Bool.false_eq_true, ite_false] at H ⊢
          exact nomatch H
        · simp only [hw, ite_true] at H ⊢
          exact arm_check_ok (BitVec.ofInt 64 0) eff m m' evs i H
      · simp only [hh, ite_true] at H ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkConnected =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H
    case inl.SkReset =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        exact nomatch H
      · simp only [hh, ite_true] at H ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_shutdown_complete_unmodeled (fd how : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : shutdown_spec fd how i m .unmodeled) :
    check_shutdown fd how eff m = .CheckUnmodeled := by
  unfold check_shutdown
  simp only [shutdown_spec, getModelSpec, bind_getModel] at H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)
  | inl sk =>
    cases sk
    case inl.SkFresh =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
    case inl.SkBound =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
    case inl.SkListening =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢
        cases hw : ((how.toNat : Int) == SHUT_WR)
        · simp only [hw, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
        · simp only [hw, ite_true] at H ⊢
          exact absurd H (ret_only_ne_unmodeled (BitVec.ofInt 64 0) i m)
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
    case inl.SkConnected =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
    case inl.SkReset =>
      cases hh : (!(shut_how_ok how))
      · simp only [hh, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
      · simp only [hh, ite_true] at H ⊢
        exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

/- =========================================================================
   recv_fd_answer — the descriptor answer recvfrom and recvmsg share
   ========================================================================= -/

theorem check_recv_fd_answer_sound_ok (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_recv_fd_answer fds fd eff m = .CheckOk m' evs) :
    recv_fd_answer fds fd i m (.ok eff m' evs) := by
  unfold check_recv_fd_answer at H
  unfold recv_fd_answer
  generalize hsl : sockfd_lookup_errno fds fd = o at H ⊢
  cases o with
  | none => exact nomatch H
  | some e => exact arm_ok (errno_ret e) eff m m' evs i H

theorem check_recv_fd_answer_complete_ok (fds : List (word × FdEntry)) (fd : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : recv_fd_answer fds fd i m (.ok eff m' evs)) :
    check_recv_fd_answer fds fd eff m = .CheckOk m' evs := by
  unfold check_recv_fd_answer
  unfold recv_fd_answer at H
  generalize hsl : sockfd_lookup_errno fds fd = o at H ⊢
  cases o with
  | none => exact nomatch H
  | some e => exact arm_check_ok (errno_ret e) eff m m' evs i H

theorem check_recv_fd_answer_complete_unmodeled (fds : List (word × FdEntry))
    (fd : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : recv_fd_answer fds fd i m .unmodeled) :
    check_recv_fd_answer fds fd eff m = .CheckUnmodeled := by
  unfold check_recv_fd_answer
  unfold recv_fd_answer at H
  generalize hsl : sockfd_lookup_errno fds fd = o at H ⊢
  cases o with
  | none => rfl
  | some e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)

theorem check_recv_fd_answer_no_ok_unmodeled (fds : List (word × FdEntry))
    (fd : word) (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_recv_fd_answer fds fd eff m = .CheckUnmodeled) :
    recv_fd_answer fds fd i m .unmodeled := by
  unfold check_recv_fd_answer at H
  unfold recv_fd_answer
  generalize hsl : sockfd_lookup_errno fds fd = o at H ⊢
  cases o with
  | none => exact unmodeled_intro i m
  | some e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])

/- =========================================================================
   recvfrom
   ========================================================================= -/

theorem check_recvfrom_sound_ok (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_recvfrom i fd buf size eff m = .CheckOk m' evs) :
    recvfrom_spec fd buf size i m (.ok eff m' evs) := by
  unfold check_recvfrom at H
  unfold recvfrom_spec
  cases hc : (!(modeled_rw_count size))
  · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
    refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
    refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
    unfold access_ok_zero
    unfold check_access_ok_zero at H
    cases hok : access_okb buf (size.toNat : Int)
    · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
      exact arm_ok (errno_ret EFAULT) eff m m' evs i H
    · simp only [hok, ite_true] at H ⊢
      exact check_recv_fd_answer_sound_ok _ _ _ _ _ _ i H
  · simp only [hc, ite_true] at H ⊢ <;> exact nomatch H

theorem check_recvfrom_sound_unmodeled (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_recvfrom i fd buf size eff m = .CheckUnmodeled) :
    recvfrom_spec fd buf size i m .unmodeled := by
  unfold check_recvfrom at H
  unfold recvfrom_spec
  cases hc : (!(modeled_rw_count size))
  · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
    refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
    refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
    unfold access_ok_zero
    unfold check_access_ok_zero at H
    cases hok : access_okb buf (size.toNat : Int)
    · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    · simp only [hok, ite_true] at H ⊢
      exact check_recv_fd_answer_no_ok_unmodeled _ _ _ _ i H
  · simp only [hc, ite_true] at H ⊢
    exact unmodeled_intro i m

theorem check_recvfrom_complete_ok (i : SyscallInput) (fd buf size : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : recvfrom_spec fd buf size i m (.ok eff m' evs)) :
    check_recvfrom i fd buf size eff m = .CheckOk m' evs := by
  unfold check_recvfrom
  unfold recvfrom_spec at H
  cases hc : (!(modeled_rw_count size))
  · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
    have H := bind_input_model_inv
      (fun (_ : SyscallInput) (m0 : Model) => access_ok_zero buf size
        (recv_fd_answer (m_fds m0) fd)) i m (.ok eff m' evs) H
    unfold access_ok_zero at H
    unfold check_access_ok_zero
    cases hok : access_okb buf (size.toNat : Int)
    · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
      exact arm_check_ok (errno_ret EFAULT) eff m m' evs i H
    · simp only [hok, ite_true] at H ⊢
      exact check_recv_fd_answer_complete_ok _ _ _ _ _ _ i H
  · simp only [hc, ite_true] at H ⊢ <;> exact nomatch H

theorem check_recvfrom_complete_unmodeled (i : SyscallInput) (fd buf size : word)
    (m : Model) (eff : SyscallEffect)
    (H : recvfrom_spec fd buf size i m .unmodeled) :
    check_recvfrom i fd buf size eff m = .CheckUnmodeled := by
  unfold check_recvfrom
  unfold recvfrom_spec at H
  cases hc : (!(modeled_rw_count size))
  · simp only [hc, Bool.false_eq_true, ite_false] at H ⊢
    have H := bind_input_model_inv
      (fun (_ : SyscallInput) (m0 : Model) => access_ok_zero buf size
        (recv_fd_answer (m_fds m0) fd)) i m .unmodeled H
    unfold access_ok_zero at H
    unfold check_access_ok_zero
    cases hok : access_okb buf (size.toNat : Int)
    · simp only [hok, Bool.false_eq_true, ite_false] at H ⊢
      exact absurd H (ret_only_ne_unmodeled (errno_ret EFAULT) i m)
    · simp only [hok, ite_true] at H ⊢
      exact check_recv_fd_answer_complete_unmodeled _ _ _ _ i H
  · simp only [hc, ite_true] at H ⊢ <;> rfl

/- =========================================================================
   recvmsg
   ========================================================================= -/

theorem check_recvmsg_sound_ok (fd flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_recvmsg fd flags eff m = .CheckOk m' evs) :
    recvmsg_spec fd flags i m (.ok eff m' evs) := by
  unfold check_recvmsg at H
  unfold recvmsg_spec
  cases hf : (!(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0))
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    refine bind_ok0 getModelSpec _ i m m m eff m' evs rfl ?_
    exact check_recv_fd_answer_sound_ok _ _ _ _ _ _ i H
  · simp only [hf, ite_true] at H ⊢ <;> exact nomatch H

theorem check_recvmsg_sound_unmodeled (fd flags : word) (eff : SyscallEffect)
    (m : Model) (i : SyscallInput)
    (H : check_recvmsg fd flags eff m = .CheckUnmodeled) :
    recvmsg_spec fd flags i m .unmodeled := by
  unfold check_recvmsg at H
  unfold recvmsg_spec
  cases hf : (!(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0))
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
    exact check_recv_fd_answer_no_ok_unmodeled _ _ _ _ i H
  · simp only [hf, ite_true] at H ⊢
    exact unmodeled_intro i m

theorem check_recvmsg_complete_ok (fd flags : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : recvmsg_spec fd flags i m (.ok eff m' evs)) :
    check_recvmsg fd flags eff m = .CheckOk m' evs := by
  unfold check_recvmsg
  unfold recvmsg_spec at H
  cases hf : (!(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0))
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    simp only [getModelSpec, bind_getModel] at H
    exact check_recv_fd_answer_complete_ok _ _ _ _ _ _ i H
  · simp only [hf, ite_true] at H ⊢ <;> exact nomatch H

theorem check_recvmsg_complete_unmodeled (fd flags : word) (m : Model)
    (eff : SyscallEffect) (i : SyscallInput)
    (H : recvmsg_spec fd flags i m .unmodeled) :
    check_recvmsg fd flags eff m = .CheckUnmodeled := by
  unfold check_recvmsg
  unfold recvmsg_spec at H
  cases hf : (!(z_land ((abi_low32 flags).toNat : Int) MSG_CMSG_COMPAT == 0))
  · simp only [hf, Bool.false_eq_true, ite_false] at H ⊢
    simp only [getModelSpec, bind_getModel] at H
    exact check_recv_fd_answer_complete_unmodeled _ _ _ _ i H
  · simp only [hf, ite_true] at H ⊢ <;> rfl

/- =========================================================================
   socketpair
   ========================================================================= -/

/-- The spec side never declines: every arm of the `alt` is an `err_ret` or
    a `pure`. -/
theorem socketpair_written_no_unmodeled (sv fd1 fd2 : word) (i : SyscallInput)
    (m : Model) : ¬ socketpair_written sv fd1 fd2 i m .unmodeled := by
  intro H
  unfold socketpair_written at H
  rcases H with H | H
  · unfold LinuxSem.LinuxProcessSem.bind at H
    rcases H with Hc | ⟨e, m1, evs1, Hc, Hret⟩
    · unfold errno_from choose at Hc
      obtain ⟨x, hx, hok⟩ := Hc
      simp at hok
    · simp [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at Hret
  · rcases H with H | H
    · unfold LinuxSem.LinuxProcessSem.bind at H
      rcases H with Hc | ⟨e, m1, evs1, Hc, Hret⟩
      · unfold errno_from choose at Hc
        obtain ⟨x, hx, hok⟩ := Hc
        simp at hok
      · simp [LinuxSem.LinuxProcessSem.pure] at Hret
    · simp [LinuxSem.LinuxProcessSem.pure] at H

theorem socketpair_faulted_no_unmodeled (i : SyscallInput) (m : Model) :
    ¬ socketpair_faulted i m .unmodeled := by
  intro H
  unfold socketpair_faulted at H
  rcases H with H | H
  · unfold LinuxSem.LinuxProcessSem.bind at H
    rcases H with Hc | ⟨e, m1, evs1, Hc, Hret⟩
    · unfold errno_from choose at Hc
      obtain ⟨x, hx, hok⟩ := Hc
      simp at hok
    · simp [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at Hret
  · simp [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at H

theorem check_socketpair_written_sound_ok (sv fd1 fd2 : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_socketpair_written sv fd1 fd2 eff m = .CheckOk m' evs) :
    socketpair_written sv fd1 fd2 i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold check_socketpair_written at H
  unfold socketpair_written
  cases zs <;> cases us <;> cases cs <;> cases cis
  · cases ws with
    | nil =>
      by_cases he : errno_ret_in socketpair_reserve_errnos ret = true
      · simp only [he, ite_true, check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp he
        exact alt_l _ _ _ _ _ (bind_ok0 _ _ i m e m _ m [] (choose_ok _ e i m hin)
          (pure_ok _ i m))
      · simp only [he, Bool.false_eq_true, ite_false] at H <;> exact nomatch H
    | cons w tl =>
      by_cases hg : (writes_eqb (w :: tl) (socketpair_writes sv fd1 fd2)
          && (bv_eqb ret (errno_ret EOPNOTSUPP)
              || errno_ret_in socketpair_create_errnos ret)) = true
      · simp only [hg, ite_true, check_result.CheckOk.injEq] at H
        obtain ⟨rfl, rfl⟩ := H
        obtain ⟨hws, hr⟩ := (Bool.and_eq_true ..).mp hg
        have hw : (w :: tl) = socketpair_writes sv fd1 fd2 := (writes_eqb_eq _ _).mp hws
        rcases (Bool.or_eq_true ..).mp hr with hr | hr
        · have hret : ret = errno_ret EOPNOTSUPP := (Fs.bv_eqb_eq _ _).mp hr
          rw [hw, hret]
          exact alt_r _ _ _ _ _ (alt_r _ _ _ _ _ (pure_ok _ i m))
        · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp hr
          rw [hw]
          exact alt_r _ _ _ _ _ (alt_l _ _ _ _ _ (bind_ok0 _ _ i m e m _ m []
            (choose_ok _ e i m hin) (pure_ok _ i m)))
      · simp only [hg, Bool.false_eq_true, ite_false] at H <;> exact nomatch H
  all_goals simp at H

theorem check_socketpair_written_complete_ok (sv fd1 fd2 : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : socketpair_written sv fd1 fd2 i m (.ok eff m' evs)) :
    check_socketpair_written sv fd1 fd2 eff m = .CheckOk m' evs := by
  unfold check_socketpair_written
  unfold socketpair_written at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with H | H
  · obtain ⟨e, m1, evs1, evs2, Hch, Hret, heq⟩ := H
    obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv socketpair_reserve_errnos i m e m1 evs1 Hch
    rw [hm1] at Hret
    unfold err_ret ret_only LinuxSem.LinuxProcessSem.pure at Hret
    simp only [Outcome.ok.injEq] at Hret
    obtain ⟨heff, hm', hevs2⟩ := Hret
    rw [hevs1, List.nil_append, hevs2] at heq
    rw [heff, hm', heq]
    try dsimp only
    simp [errno_ret_in_intro socketpair_reserve_errnos e hmem]
  · rcases H with H | H
    · obtain ⟨e, m1, evs1, evs2, Hch, Hret, heq⟩ := H
      obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv socketpair_create_errnos i m e m1 evs1 Hch
      rw [hm1] at Hret
      unfold LinuxSem.LinuxProcessSem.pure at Hret
      simp only [Outcome.ok.injEq] at Hret
      obtain ⟨heff, hm', hevs2⟩ := Hret
      rw [hevs1, List.nil_append, hevs2] at heq
      rw [heff, hm', heq]
      try dsimp only
      simp [mkEffect, socketpair_writes, writes_eqb_eq,
        errno_ret_in_intro socketpair_create_errnos e hmem]
    · unfold LinuxSem.LinuxProcessSem.pure at H
      simp only [Outcome.ok.injEq] at H
      obtain ⟨heff, hm', hevs⟩ := H
      rw [heff, hm', hevs]
      try dsimp only
      simp [mkEffect, socketpair_writes, writes_eqb_eq, bv_eqb_refl]

theorem check_socketpair_written_no_unmodeled (sv fd1 fd2 : word)
    (eff : SyscallEffect) (m : Model) :
    check_socketpair_written sv fd1 fd2 eff m ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold check_socketpair_written
  cases zs <;> cases us <;> cases cs <;> cases cis
  · cases ws with
    | nil =>
      by_cases he : errno_ret_in socketpair_reserve_errnos ret = true <;> simp [he]
    | cons w tl =>
      by_cases hg : (writes_eqb (w :: tl) (socketpair_writes sv fd1 fd2)
          && (bv_eqb ret (errno_ret EOPNOTSUPP)
              || errno_ret_in socketpair_create_errnos ret)) = true <;> simp [hg]
  all_goals simp

theorem check_socketpair_faulted_sound_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : check_socketpair_faulted eff m = .CheckOk m' evs) :
    socketpair_faulted i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold check_socketpair_faulted at H
  unfold socketpair_faulted
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis
  · by_cases hr : (errno_ret_in socketpair_reserve_errnos ret
        || bv_eqb ret (errno_ret EFAULT)) = true
    · simp only [hr, ite_true, check_result.CheckOk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      rcases (Bool.or_eq_true ..).mp hr with hr | hr
      · obtain ⟨e, hin, rfl⟩ := (errno_ret_in_true _ _).mp hr
        exact alt_l _ _ _ _ _ (bind_ok0 _ _ i m e m _ m [] (choose_ok _ e i m hin)
          (pure_ok _ i m))
      · have hret : ret = errno_ret EFAULT := (Fs.bv_eqb_eq _ _).mp hr
        rw [hret]
        exact alt_r _ _ _ _ _ (pure_ok _ i m)
    · simp only [hr, Bool.false_eq_true, ite_false] at H <;> exact nomatch H
  all_goals simp at H

theorem check_socketpair_faulted_complete_ok (eff : SyscallEffect) (m m' : Model)
    (evs : List event) (i : SyscallInput)
    (H : socketpair_faulted i m (.ok eff m' evs)) :
    check_socketpair_faulted eff m = .CheckOk m' evs := by
  unfold check_socketpair_faulted
  unfold socketpair_faulted at H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with H | H
  · obtain ⟨e, m1, evs1, evs2, Hch, Hret, heq⟩ := H
    obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv socketpair_reserve_errnos i m e m1 evs1 Hch
    rw [hm1] at Hret
    unfold err_ret ret_only LinuxSem.LinuxProcessSem.pure at Hret
    simp only [Outcome.ok.injEq] at Hret
    obtain ⟨heff, hm', hevs2⟩ := Hret
    rw [hevs1, List.nil_append, hevs2] at heq
    rw [heff, hm', heq]
    try dsimp only
    simp [errno_ret_in_intro socketpair_reserve_errnos e hmem]
  · unfold err_ret ret_only LinuxSem.LinuxProcessSem.pure at H
    simp only [Outcome.ok.injEq] at H
    obtain ⟨heff, hm', hevs⟩ := H
    rw [heff, hm', hevs]
    try dsimp only
    simp [bv_eqb_refl]

theorem check_socketpair_faulted_no_unmodeled (eff : SyscallEffect) (m : Model) :
    check_socketpair_faulted eff m ≠ .CheckUnmodeled := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold check_socketpair_faulted
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis
  · by_cases hr : (errno_ret_in socketpair_reserve_errnos ret
        || bv_eqb ret (errno_ret EFAULT)) = true <;> simp [hr]
  all_goals simp

/-! ### socketpair, the composite acceptor

  `cases h : b` on a `Bool` yields the `false` case first, so each of the
  four tests below states the continuing branch before the answering one. -/

theorem check_socketpair_sound_ok (i : SyscallInput) (family type protocol sv : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_socketpair i family type protocol sv eff m = .CheckOk m' evs) :
    socketpair_spec family type protocol sv i m (.ok eff m' evs) := by
  unfold check_socketpair at H
  unfold socketpair_spec
  cases hfl : (!(socketpair_flags_ok type))
  · simp only [hfl, Bool.false_eq_true, ite_false] at H ⊢
    cases hmo : (!(socketpair_modeled_b family type protocol))
    · simp only [hmo, Bool.false_eq_true, ite_false] at H ⊢
      refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
      refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
      generalize hfds : socketpair_fds (m_fds m) = o at H ⊢
      cases o with
      | none => exact nomatch H
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        cases hmem : socketpair_dest_writable i.in_wmem sv
        · simp only [hmem, Bool.false_eq_true, ite_false] at H ⊢
          cases ho : (!(access_okb sv 4))
          · simp only [ho, Bool.false_eq_true, ite_false] at H ⊢ <;> exact nomatch H
          · simp only [ho, ite_true] at H ⊢
            exact check_socketpair_faulted_sound_ok eff m m' evs i H
        · simp only [hmem, ite_true] at H ⊢
          exact check_socketpair_written_sound_ok sv fd1 fd2 eff m m' evs i H
    · simp only [hmo, ite_true] at H ⊢ <;> exact nomatch H
  · simp only [hfl, ite_true] at H ⊢
    exact arm_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_socketpair_sound_unmodeled (i : SyscallInput)
    (family type protocol sv : word) (eff : SyscallEffect) (m : Model)
    (H : check_socketpair i family type protocol sv eff m = .CheckUnmodeled) :
    socketpair_spec family type protocol sv i m .unmodeled := by
  unfold check_socketpair at H
  unfold socketpair_spec
  cases hfl : (!(socketpair_flags_ok type))
  · simp only [hfl, Bool.false_eq_true, ite_false] at H ⊢
    cases hmo : (!(socketpair_modeled_b family type protocol))
    · simp only [hmo, Bool.false_eq_true, ite_false] at H ⊢
      refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
      refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
      generalize hfds : socketpair_fds (m_fds m) = o at H ⊢
      cases o with
      | none => exact unmodeled_intro i m
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        cases hmem : socketpair_dest_writable i.in_wmem sv
        · simp only [hmem, Bool.false_eq_true, ite_false] at H ⊢
          cases ho : (!(access_okb sv 4))
          · simp only [ho, Bool.false_eq_true, ite_false] at H ⊢
            exact unmodeled_intro i m
          · simp only [ho, ite_true] at H ⊢
            exact absurd H (check_socketpair_faulted_no_unmodeled eff m)
        · simp only [hmem, ite_true] at H ⊢
          exact absurd H (check_socketpair_written_no_unmodeled sv fd1 fd2 eff m)
    · simp only [hmo, ite_true] at H ⊢
      exact unmodeled_intro i m
  · simp only [hfl, ite_true] at H ⊢
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_socketpair_complete_ok (i : SyscallInput)
    (family type protocol sv : word) (eff : SyscallEffect) (m m' : Model)
    (evs : List event)
    (H : socketpair_spec family type protocol sv i m (.ok eff m' evs)) :
    check_socketpair i family type protocol sv eff m = .CheckOk m' evs := by
  unfold check_socketpair
  unfold socketpair_spec at H
  cases hfl : (!(socketpair_flags_ok type))
  · simp only [hfl, Bool.false_eq_true, ite_false] at H ⊢
    cases hmo : (!(socketpair_modeled_b family type protocol))
    · simp only [hmo, Bool.false_eq_true, ite_false] at H ⊢
      have H := bind_input_model_inv
        (fun (i0 : SyscallInput) (m0 : Model) =>
          match socketpair_fds (m_fds m0) with
          | none => unmodeled
          | some (fd1, fd2) =>
              if socketpair_dest_writable i0.in_wmem sv then
                socketpair_written sv fd1 fd2
              else if !(access_okb sv 4) then socketpair_faulted
              else unmodeled)
        i m (.ok eff m' evs) H
      generalize hfds : socketpair_fds (m_fds m) = o at H ⊢
      cases o with
      | none => exact nomatch H
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        cases hmem : socketpair_dest_writable i.in_wmem sv
        · simp only [hmem, Bool.false_eq_true, ite_false] at H ⊢
          cases ho : (!(access_okb sv 4))
          · simp only [ho, Bool.false_eq_true, ite_false] at H ⊢ <;> exact nomatch H
          · simp only [ho, ite_true] at H ⊢
            exact check_socketpair_faulted_complete_ok eff m m' evs i H
        · simp only [hmem, ite_true] at H ⊢
          exact check_socketpair_written_complete_ok sv fd1 fd2 eff m m' evs i H
    · simp only [hmo, ite_true] at H ⊢ <;> exact nomatch H
  · simp only [hfl, ite_true] at H ⊢
    exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H

theorem check_socketpair_complete_unmodeled (i : SyscallInput)
    (family type protocol sv : word) (m : Model) (eff : SyscallEffect)
    (H : socketpair_spec family type protocol sv i m .unmodeled) :
    check_socketpair i family type protocol sv eff m = .CheckUnmodeled := by
  unfold check_socketpair
  unfold socketpair_spec at H
  cases hfl : (!(socketpair_flags_ok type))
  · simp only [hfl, Bool.false_eq_true, ite_false] at H ⊢
    cases hmo : (!(socketpair_modeled_b family type protocol))
    · simp only [hmo, Bool.false_eq_true, ite_false] at H ⊢
      have H := bind_input_model_inv
        (fun (i0 : SyscallInput) (m0 : Model) =>
          match socketpair_fds (m_fds m0) with
          | none => unmodeled
          | some (fd1, fd2) =>
              if socketpair_dest_writable i0.in_wmem sv then
                socketpair_written sv fd1 fd2
              else if !(access_okb sv 4) then socketpair_faulted
              else unmodeled)
        i m .unmodeled H
      generalize hfds : socketpair_fds (m_fds m) = o at H ⊢
      cases o with
      | none => rfl
      | some p =>
        obtain ⟨fd1, fd2⟩ := p
        cases hmem : socketpair_dest_writable i.in_wmem sv
        · simp only [hmem, Bool.false_eq_true, ite_false] at H ⊢
          cases ho : (!(access_okb sv 4))
          · simp only [ho, Bool.false_eq_true, ite_false] at H
            rfl
          · simp only [ho, ite_true] at H
            exact absurd H (socketpair_faulted_no_unmodeled i m)
        · simp only [hmem, ite_true] at H ⊢
          exact absurd H (socketpair_written_no_unmodeled sv fd1 fd2 i m)
    · simp only [hmo, ite_true] at H ⊢ <;> rfl
  · simp only [hfl, ite_true] at H ⊢
    exact absurd H (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

/-- `record_copyins` propagates a declining body: it only wraps the `ok`
    shape. -/
private theorem record_copyins_unmodeled_intro (reads : List (word × Nat))
    (spec : SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (H : spec i m .unmodeled) :
    record_copyins reads spec i m .unmodeled := by
  unfold record_copyins LinuxSem.LinuxProcessSem.bind
  exact Or.inl H

/- =========================================================================
   getsockopt

   The fd errnos sit ABOVE the `optlen` read, so they carry no ledger; the
   -EOPNOTSUPP arm sits below it and carries exactly the four bytes
   `do_sock_getsockopt` copies before it looks at the level.
   ========================================================================= -/

theorem check_getsockopt_sound_ok (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_getsockopt i fd level optlenp eff m = .CheckOk m' evs) :
    getsockopt_spec fd level optlenp i m (.ok eff m' evs) := by
  unfold check_getsockopt at H
  unfold getsockopt_spec
  refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
  refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases hl : (!(sock_level_known level))
    · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢ <;> exact nomatch H
    · simp only [hl, ite_true] at H ⊢
      obtain ⟨hreads, hm, hevs⟩ :=
        (check_ret_only_copyins_ok_iff (getsockopt_optlen_read i optlenp) eff
          (errno_ret EOPNOTSUPP) m [] m' evs).mp H
      rw [hreads, hm, hevs]
      refine record_copyins_clear_ok (getsockopt_optlen_read i optlenp)
        (ret_only (errno_ret EOPNOTSUPP)) i m _ m [] rfl ?_
      exact ret_only_ok _ i m

theorem check_getsockopt_sound_unmodeled (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_getsockopt i fd level optlenp eff m = .CheckUnmodeled) :
    getsockopt_spec fd level optlenp i m .unmodeled := by
  unfold check_getsockopt at H
  unfold getsockopt_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  try dsimp only
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret e) m [])
  | inl sk =>
    cases hl : (!(sock_level_known level))
    · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢
      exact record_copyins_unmodeled_intro (getsockopt_optlen_read i optlenp)
        _ i m (unmodeled_intro i m)
    · simp only [hl, ite_true] at H ⊢
      exact absurd H (check_ret_only_copyins_no_unmodeled
        (getsockopt_optlen_read i optlenp) eff (errno_ret EOPNOTSUPP) m [])

set_option maxHeartbeats 1000000 in
theorem check_getsockopt_complete_ok (i : SyscallInput) (fd level optlenp : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : getsockopt_spec fd level optlenp i m (.ok eff m' evs)) :
    check_getsockopt i fd level optlenp eff m = .CheckOk m' evs := by
  unfold check_getsockopt
  unfold getsockopt_spec at H
  have H := bind_input_model_inv
    (fun (i0 : SyscallInput) (m0 : Model) =>
      match sock_fd m0 fd with
      | .inr e => err_ret e
      | .inl _ => record_copyins (getsockopt_optlen_read i0 optlenp)
          (if !(sock_level_known level) then err_ret EOPNOTSUPP else unmodeled))
    i m (.ok eff m' evs) H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact arm_check_ok (errno_ret e) eff m m' evs i H
  | inl sk =>
    cases hl : (!(sock_level_known level))
    · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢ <;> exact nomatch H
    · simp only [hl, ite_true] at H ⊢
      obtain ⟨core, Hcore, hEff⟩ := record_copyins_ok_inv
        (getsockopt_optlen_read i optlenp) (err_ret EOPNOTSUPP) i m eff m' evs H
      obtain ⟨hcoreEff, hm', hevs⟩ :=
        ret_only_ok_inv (errno_ret EOPNOTSUPP) i m core m' evs Hcore
      rw [hcoreEff] at hEff
      rw [hEff, hm', hevs]
      refine (check_ret_only_copyins_ok_iff (getsockopt_optlen_read i optlenp) _
        (errno_ret EOPNOTSUPP) m [] m []).mpr ⟨?_, rfl, rfl⟩
      simp [with_copyins]

set_option maxHeartbeats 1000000 in
theorem check_getsockopt_complete_unmodeled (i : SyscallInput) (fd level optlenp : word)
    (m : Model) (eff : SyscallEffect)
    (H : getsockopt_spec fd level optlenp i m .unmodeled) :
    check_getsockopt i fd level optlenp eff m = .CheckUnmodeled := by
  unfold check_getsockopt
  unfold getsockopt_spec at H
  have H := bind_input_model_inv
    (fun (i0 : SyscallInput) (m0 : Model) =>
      match sock_fd m0 fd with
      | .inr e => err_ret e
      | .inl _ => record_copyins (getsockopt_optlen_read i0 optlenp)
          (if !(sock_level_known level) then err_ret EOPNOTSUPP else unmodeled))
    i m .unmodeled H
  try dsimp only at H
  generalize hsf : sock_fd m fd = s at H ⊢
  cases s with
  | inr e => exact absurd H (ret_only_ne_unmodeled (errno_ret e) i m)
  | inl sk =>
    cases hl : (!(sock_level_known level))
    · simp only [hl, Bool.false_eq_true, ite_false] at H ⊢ <;> rfl
    · simp only [hl, ite_true] at H ⊢
      exact absurd (record_copyins_unmodeled_inv _ _ i m H)
        (ret_only_ne_unmodeled (errno_ret EOPNOTSUPP) i m)



/- =========================================================================
   socket

   Every test is a pure function of the arguments and they are made in the
   kernel's order.  A tactic note: these tests are `if`s at FUNCTION
   type, and both `cases h : guard` and `by_cases h : guard = true` blow
   the recursion budget when the guard is a compound `Bool` (the
   `decide`-bearing ones expand `sint32` under the instance search).
   `split at H` does the same split without generalising the guard, and
   the hypothesis it hands back is exactly what `ite_eq_left` / `ite_eq_right` need
   to reduce the spec's matching test.  This is the idiom the whole
   cascade below uses.
   ========================================================================= -/

/- =========================================================================
   bind — the ledger bridge, then the four lemmas
   ========================================================================= -/

/-- `record_copyins_of_cleared`: `record_copyins` APPENDS its
    ranges to whatever the wrapped spec already recorded, and on every arm
    reached here the wrapped spec records nothing, so an observed effect is
    admissible exactly when its own ledger is the recorded range and the
    rest of it is what the arm produced.  This is
    `record_copyins_clear_ok` under the name the bind proofs cite. -/
private theorem record_copyins_of_cleared (reads : List (word × Nat))
    (spec : SysSpec SyscallEffect) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hr : eff.eff_copyins = reads)
    (H : spec i m (.ok (clear_copyins eff) m' evs)) :
    record_copyins reads spec i m (.ok eff m' evs) :=
  record_copyins_clear_ok reads spec i m eff m' evs Hr H

/-- The other direction of the same bridge, for the completeness proofs:
    an effect whose ledger is the recorded range passes the test, so what
    is left to decide is the arm's own answer. -/
private theorem check_copyins_same (reads : List (word × Nat))
    (eff : SyscallEffect) (res : check_result) (H : eff.eff_copyins = reads) :
    check_copyins reads eff res = res := by
  unfold check_copyins
  rw [H, access_ranges_eqb_refl]
  simp

/-- Checker → spec, for one arm that answers after recording a ledger:
    `check_ret_only_copyins` at `r` *is* the spec's `record_copyins` of
    `ret_only r` at the same word. -/
private theorem arm_copyins_ok (reads : List (word × Nat)) (r : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_ret_only_copyins reads eff r m [] = .CheckOk m' evs) :
    record_copyins reads (ret_only r) i m (.ok eff m' evs) := by
  obtain ⟨heff, hm, hevs⟩ :=
    (check_ret_only_copyins_ok_iff reads eff r m [] m' evs).mp H
  rw [heff, hm, hevs]
  exact record_copyins_clear_ok reads (ret_only r) i m _ m [] rfl (ret_only_ok r i m)

/-- Spec → checker for the same arm. -/
private theorem arm_copyins_check_ok (reads : List (word × Nat)) (r : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : record_copyins reads (ret_only r) i m (.ok eff m' evs)) :
    check_ret_only_copyins reads eff r m [] = .CheckOk m' evs := by
  obtain ⟨core, Hcore, hEff⟩ := record_copyins_ok_inv reads (ret_only r) i m eff m' evs H
  obtain ⟨hcore, hm', hevs⟩ := ret_only_ok_inv r i m core m' evs Hcore
  rw [hcore] at hEff
  rw [hEff, hm', hevs]
  refine (check_ret_only_copyins_ok_iff reads _ r m [] m []).mpr ⟨?_, rfl, rfl⟩
  simp [with_copyins]

/- =========================================================================
   The "fresh descriptor" success arm, read back

   `socket` and `accept4` both succeed through
   `bind (lowest_fd (m_fds m)) (fun nfd => seqSpec (modifySpec (mk nfd))
   (ret_only nfd))`, with `mk` the only difference between them.  This
   lemma reads such an outcome back: the fd is `alloc_fd`, the model is
   `mk` at that fd, the effect carries no payload, and the ledger is empty.
   ========================================================================= -/

private theorem lowest_fd_arm_inv (fds : List (word × FdEntry))
    (mk : word → Model → Model)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event)
    (H : bind (lowest_fd fds)
        (fun nfd => seqSpec (modifySpec (mk nfd)) (ret_only nfd))
        i m (.ok eff m' evs)) :
    fd_lookup fds (alloc_fd fds) = none ∧ eff = mkEffect (alloc_fd fds) [] [] ∧
      m' = mk (alloc_fd fds) m ∧ evs = [] := by
  unfold LinuxSem.LinuxProcessSem.bind at H
  obtain ⟨nfd, m1, evs1, evs2, Hch, Hk, heq⟩ := H
  obtain ⟨x, hpred, hok⟩ := Hch
  obtain ⟨hlookup, hnfd⟩ := hpred
  cases hok
  simp only [List.nil_append] at heq
  unfold seqSpec LinuxSem.LinuxProcessSem.bind at Hk
  obtain ⟨u, m2, ev1, ev2, hc, hk, heq2⟩ := Hk
  unfold modifySpec LinuxSem.LinuxProcessSem.modify at hc
  simp only [Outcome.ok.injEq] at hc
  obtain ⟨-, hm2, hev1⟩ := hc
  rw [hm2] at hk
  unfold ret_only LinuxSem.LinuxProcessSem.pure at hk
  simp only [Outcome.ok.injEq] at hk
  obtain ⟨heff0, hm'0, hevs2⟩ := hk
  rw [hev1, List.nil_append, hevs2] at heq2
  rw [heq2] at heq
  subst hnfd
  exact ⟨hlookup, heff0, hm'0, heq⟩

private theorem lowest_fd_arm (fds : List (word × FdEntry))
    (mk : word → Model → Model) (i : SyscallInput) (m : Model)
    (hfr : fd_lookup fds (alloc_fd fds) = none) :
    bind (lowest_fd fds)
      (fun fd => seqSpec (modifySpec (mk fd)) (ret_only fd))
      i m (.ok (mkEffect (alloc_fd fds) [] []) (mk (alloc_fd fds) m) []) := by
  refine bind_ok0 _ _ i m (alloc_fd fds) m
    (mkEffect (alloc_fd fds) [] []) (mk (alloc_fd fds) m) [] ?_ ?_
  · exact choose_ok
      (fun fd => fd_lookup fds fd = none ∧ fd = alloc_fd fds)
      _ i m ⟨hfr, rfl⟩
  · refine bind_ok (modifySpec (mk (alloc_fd fds)))
      (fun _ => ret_only (alloc_fd fds)) i m ()
      (mk (alloc_fd fds) m) [] (mkEffect (alloc_fd fds) [] [])
      (mk (alloc_fd fds) m) [] ?_ ?_
    · exact modify_ok _ i m
    · exact pure_ok _ i _

private theorem lowest_fd_arm_ne_unmodeled (fds : List (word × FdEntry))
    (mk : word → Model → Model) (i : SyscallInput) (m : Model) :
    ¬ bind (lowest_fd fds)
        (fun nfd => seqSpec (modifySpec (mk nfd)) (ret_only nfd)) i m .unmodeled := by
  intro H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with Hc | ⟨x, m1, evs1, Hc, Hk⟩
  · unfold lowest_fd choose at Hc
    obtain ⟨y, hy, hok⟩ := Hc
    simp at hok
  · unfold seqSpec LinuxSem.LinuxProcessSem.bind at Hk
    rcases Hk with Hc2 | ⟨u, m2, ev1, Hc2, Hk2⟩
    · unfold modifySpec LinuxSem.LinuxProcessSem.modify at Hc2
      simp at Hc2
    · unfold ret_only LinuxSem.LinuxProcessSem.pure at Hk2
      simp at Hk2


private theorem errno_arm_ne_unmodeled (es : List Int) (i : SyscallInput) (m : Model) :
    ¬ bind (errno_from es) (fun e => err_ret e) i m .unmodeled := by
  intro H
  unfold LinuxSem.LinuxProcessSem.bind at H
  rcases H with Hc | ⟨e, m1, evs1, Hc, Hret⟩
  · unfold errno_from choose at Hc
    obtain ⟨x, hx, hok⟩ := Hc
    simp at hok
  · unfold err_ret ret_only LinuxSem.LinuxProcessSem.pure at Hret
    exact nomatch Hret


/- =========================================================================
   accept4
   ========================================================================= -/

theorem check_accept4_sound_ok (fd addrp addrlenp flags : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_accept4 fd addrp addrlenp flags eff m = .CheckOk m' evs) :
    accept4_spec fd addrp addrlenp flags i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold check_accept4 at H
  unfold accept4_spec
  refine bind_ok0 getModelSpec _ i m m m _ m' evs rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e0 at H ⊢
  cases e0 with
  | none => exact arm_ok (errno_ret EBADF) _ m m' evs i H
  | some e =>
    cases h1 : (!(z_ldiff ((abi_low32 flags).toNat : Int)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
    · simp only [h1, Bool.false_eq_true, ite_false] at H ⊢
      cases h2 : (!(z_land ((abi_low32 flags).toNat : Int) SOCK_NONBLOCK == 0))
      · simp only [h2, Bool.false_eq_true, ite_false] at H ⊢
        cases e with
        | FdSocket sk =>
          try dsimp only at H ⊢
          cases h3 : (!(w_is0 addrp))
          · simp only [h3, Bool.false_eq_true, ite_false] at H ⊢
            cases sk with
            | SkListening =>
              cases hx : conn_ix_exhausted (m_conn_ix m)
              · simp only [hx, Bool.false_eq_true, ite_false] at H ⊢
                unfold check_new_fd_result at H
                cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis
                · cases h11 : errno_ret_in accept_errnos ret
                  · simp only [h11, Bool.false_eq_true, ite_false] at H
                    cases hf : fd_lookup (m_fds m) ret
                    · simp only [hf] at H
                      cases heq : bv_eqb ret (alloc_fd (m_fds m))
                      · simp only [heq, Bool.false_eq_true, ite_false] at H
                        cases H
                      · have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq _ _).mp heq
                        simp only [heq, ite_true, check_result.CheckOk.injEq] at H
                        obtain ⟨rfl, rfl⟩ := H
                        rw [hret] at hf ⊢
                        exact alt_r _ _ _ _ _ (lowest_fd_arm (m_fds m)
                          (fun nfd mm => with_accepted (fd_insert (m_fds m) nfd
                            (.FdSocket (.SkConnected (nq_peer (m_net m))
                              (conn_channel (m_conn_ix m))
                              (nq_script (m_net m))))) mm) i m hf)
                    · simp only [hf] at H
                      cases H
                  · simp only [h11, ite_true, check_result.CheckOk.injEq] at H
                    obtain ⟨rfl, rfl⟩ := H
                    obtain ⟨e', hmem, rfl⟩ := (errno_ret_in_true _ _).mp h11
                    exact alt_l _ _ _ _ _ (bind_ok0 _ _ i m e' m _ m []
                      (choose_ok _ e' i m hmem) (pure_ok _ i m))
                all_goals simp at H
              · simp only [hx, ite_true] at H ⊢
                exact check_errno_only_sound_ok accept_errnos i _ m m' evs H
            | SkFresh =>
              try dsimp only at H ⊢
              exact arm_ok (errno_ret EINVAL) _ m m' evs i H
            | SkBound =>
              try dsimp only at H ⊢
              exact arm_ok (errno_ret EINVAL) _ m m' evs i H
            | SkConnected peer chan rx =>
              try dsimp only at H ⊢
              exact arm_ok (errno_ret EINVAL) _ m m' evs i H
            | SkReset peer chan =>
              try dsimp only at H ⊢
              exact arm_ok (errno_ret EINVAL) _ m m' evs i H
          · simp only [h3, ite_true] at H ⊢
            exact absurd H (by simp)
        | _ => exact arm_ok (errno_ret ENOTSOCK) _ m m' evs i H
      · simp only [h2, ite_true] at H ⊢
        exact absurd H (by simp)
    · simp only [h1, ite_true] at H ⊢
      exact arm_ok (errno_ret EINVAL) _ m m' evs i H

theorem check_accept4_sound_unmodeled (fd addrp addrlenp flags : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_accept4 fd addrp addrlenp flags eff m = .CheckUnmodeled) :
    accept4_spec fd addrp addrlenp flags i m .unmodeled := by
  unfold check_accept4 at H
  unfold accept4_spec
  refine bind_unmodeled2 getModelSpec _ i m m m [] rfl ?_
  try dsimp only
  generalize hfd : fd_lookup (m_fds m) fd = e0 at H ⊢
  cases e0 with
  | none => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases h1 : (!(z_ldiff ((abi_low32 flags).toNat : Int)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
    · simp only [h1, Bool.false_eq_true, ite_false] at H ⊢
      cases h2 : (!(z_land ((abi_low32 flags).toNat : Int) SOCK_NONBLOCK == 0))
      · simp only [h2, Bool.false_eq_true, ite_false] at H ⊢
        cases e with
        | FdSocket sk =>
          try dsimp only at H ⊢
          cases h3 : (!(w_is0 addrp))
          · simp only [h3, Bool.false_eq_true, ite_false] at H ⊢
            cases sk with
            | SkListening =>
              cases hx : conn_ix_exhausted (m_conn_ix m)
              · simp only [hx, Bool.false_eq_true, ite_false] at H ⊢
                exact absurd H (check_new_fd_result_no_unmodeled accept_errnos eff m _)
              · simp only [hx, ite_true] at H ⊢
                exact absurd H (check_errno_only_no_unmodeled accept_errnos eff m)
            | SkFresh =>
              try dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | SkBound =>
              try dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | SkConnected peer chan rx =>
              try dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            | SkReset peer chan =>
              try dsimp only at H ⊢
              exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
          · simp only [h3, ite_true] at H ⊢
            exact unmodeled_intro i m
        | _ => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTSOCK) m [])
      · simp only [h2, ite_true] at H ⊢
        exact unmodeled_intro i m
    · simp only [h1, ite_true] at H ⊢
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_accept4_complete_ok (fd addrp addrlenp flags : word)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : accept4_spec fd addrp addrlenp flags i m (.ok eff m' evs)) :
    check_accept4 fd addrp addrlenp flags eff m = .CheckOk m' evs := by
  unfold check_accept4
  unfold accept4_spec at H
  have H1 := (bind_getModel _ i m (.ok eff m' evs)).mp H
  try dsimp only at H1
  generalize hfd : fd_lookup (m_fds m) fd = e0 at H1 ⊢
  cases e0 with
  | none => exact arm_check_ok (errno_ret EBADF) eff m m' evs i H1
  | some e =>
    cases h1 : (!(z_ldiff ((abi_low32 flags).toNat : Int)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
    · simp only [h1, Bool.false_eq_true, ite_false] at H1 ⊢
      cases h2 : (!(z_land ((abi_low32 flags).toNat : Int) SOCK_NONBLOCK == 0))
      · simp only [h2, Bool.false_eq_true, ite_false] at H1 ⊢
        cases e with
        | FdSocket sk =>
          try dsimp only at H1 ⊢
          cases h3 : (!(w_is0 addrp))
          · simp only [h3, Bool.false_eq_true, ite_false] at H1 ⊢
            cases sk with
            | SkListening =>
              cases hx : conn_ix_exhausted (m_conn_ix m)
              · simp only [hx, Bool.false_eq_true, ite_false] at H1 ⊢
                rcases H1 with He | Hs
                · obtain ⟨er, m1, evs1, evs2, Hch, Hret, heq⟩ := He
                  obtain ⟨hmem, hm1, hevs1⟩ :=
                    choose_ok_inv accept_errnos i m er m1 evs1 Hch
                  rw [hm1] at Hret
                  obtain ⟨heff, hm', hevs2⟩ :=
                    ret_only_ok_inv (errno_ret er) i m eff m' evs2 Hret
                  rw [hevs2, List.append_nil, hevs1] at heq
                  rw [heff, hm', heq]
                  simp [check_new_fd_result, errno_ret_in_intro accept_errnos er hmem]
                · obtain ⟨hlookup, heff, hm', hevs⟩ :=
                    lowest_fd_arm_inv (m_fds m) _ i m eff m' evs Hs
                  rw [heff, hm', hevs]
                  simp [check_new_fd_result, hlookup,
                    errno_ret_in_alloc_fd accept_errnos (m_fds m) (by decide),
                    bv_eqb_refl]
              · simp only [hx, ite_true] at H1 ⊢
                exact check_errno_only_complete_ok accept_errnos i eff m m' evs H1
            | SkFresh =>
              try dsimp only at H1 ⊢
              exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H1
            | SkBound =>
              try dsimp only at H1 ⊢
              exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H1
            | SkConnected peer chan rx =>
              try dsimp only at H1 ⊢
              exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H1
            | SkReset peer chan =>
              try dsimp only at H1 ⊢
              exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H1
          · simp only [h3, ite_true] at H1 ⊢
            exact absurd H1 (by simp [unmodeled])
        | _ => exact arm_check_ok (errno_ret ENOTSOCK) eff m m' evs i H1
      · simp only [h2, ite_true] at H1 ⊢
        exact absurd H1 (by simp [unmodeled])
    · simp only [h1, ite_true] at H1 ⊢
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i H1

theorem check_accept4_complete_unmodeled (fd addrp addrlenp flags : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (H : accept4_spec fd addrp addrlenp flags i m .unmodeled) :
    check_accept4 fd addrp addrlenp flags eff m = .CheckUnmodeled := by
  unfold check_accept4
  unfold accept4_spec at H
  have H1 := (bind_getModel _ i m .unmodeled).mp H
  try dsimp only at H1
  generalize hfd : fd_lookup (m_fds m) fd = e0 at H1 ⊢
  cases e0 with
  | none => exact absurd H1 (ret_only_ne_unmodeled (errno_ret EBADF) i m)
  | some e =>
    cases h1 : (!(z_ldiff ((abi_low32 flags).toNat : Int)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
    · simp only [h1, Bool.false_eq_true, ite_false] at H1 ⊢
      cases h2 : (!(z_land ((abi_low32 flags).toNat : Int) SOCK_NONBLOCK == 0))
      · simp only [h2, Bool.false_eq_true, ite_false] at H1 ⊢
        cases e with
        | FdSocket sk =>
          try dsimp only at H1 ⊢
          cases h3 : (!(w_is0 addrp))
          · simp only [h3, Bool.false_eq_true, ite_false] at H1 ⊢
            cases sk with
            | SkListening =>
              cases hx : conn_ix_exhausted (m_conn_ix m)
              · simp only [hx, Bool.false_eq_true, ite_false] at H1 ⊢
                rcases H1 with He | Hs
                · exact absurd He (errno_arm_ne_unmodeled accept_errnos i m)
                · exact absurd Hs (lowest_fd_arm_ne_unmodeled (m_fds m) _ i m)
              · simp only [hx, ite_true] at H1 ⊢
                rcases H1 with He | Hno
                · exact absurd He (errno_arm_ne_unmodeled accept_errnos i m)
                · unfold choose at Hno
                  obtain ⟨x, hx', -⟩ := Hno
                  exact absurd hx' (by simp)
            | SkFresh =>
              try dsimp only at H1 ⊢
              exact absurd H1 (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
            | SkBound =>
              try dsimp only at H1 ⊢
              exact absurd H1 (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
            | SkConnected peer chan rx =>
              try dsimp only at H1 ⊢
              exact absurd H1 (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
            | SkReset peer chan =>
              try dsimp only at H1 ⊢
              exact absurd H1 (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
          · simp only [h3, ite_true] at H1 ⊢
        | _ => exact absurd H1 (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m)
      · simp only [h2, ite_true] at H1 ⊢
    · simp only [h1, ite_true] at H1 ⊢
      exact absurd H1 (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

/- ---------------- bind ---------------- -/

theorem check_bind_sound_ok (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_bind i fd addrp addrlen eff m = .CheckOk m' evs) :
    bind_spec fd addrp addrlen i m (.ok eff m' evs) := by
  unfold check_bind at H
  unfold bind_spec
  refine bind_ok0 inputSpec _ i m i m _ m' evs (input_ok i m) ?_
  refine bind_ok0 getModelSpec _ i m m m eff m' evs (getModel_ok i m) ?_
  generalize hal : sint32 addrlen = av at H ⊢
  simp only [] at H ⊢
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact arm_ok (errno_ret EBADF) eff m m' evs i H
  | some e =>
    cases e with
    | FdSocket sk =>
      simp only [] at H ⊢
      by_cases hp : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true
      · simp only [hp, ite_true] at H ⊢
        exact arm_ok (errno_ret EINVAL) eff m m' evs i H
      · simp only [hp, Bool.false_eq_true, ite_false] at H ⊢
        by_cases hz : (av == 0) = true
        · simp only [hz, ite_true] at H ⊢
          exact arm_ok (errno_ret EINVAL) eff m m' evs i H
        · simp only [hz, Bool.false_eq_true, ite_false] at H ⊢
          cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) with
          | none =>
            simp only [hrb] at H ⊢
            exact arm_ok (errno_ret EFAULT) eff m m' evs i H
          | some bs =>
            simp only [hrb] at H ⊢
            by_cases hs : decide (av < SOCKADDR_IN_SIZE) = true
            · simp only [hs, ite_true] at H ⊢
              exact arm_copyins_ok _ _ eff m m' evs i H
            · simp only [hs, Bool.false_eq_true, ite_false] at H ⊢
              by_cases hfam : (!(sa_family_of bs == AF_INET
                    || (sa_family_of bs == AF_UNSPEC
                        && sin_addr_of bs == INADDR_ANY))) = true
              · simp only [hfam, ite_true] at H ⊢
                exact arm_copyins_ok _ _ eff m m' evs i H
              · simp only [hfam, Bool.false_eq_true, ite_false] at H ⊢
                by_cases ha : (!(sin_addr_of bs == INADDR_ANY)) = true
                · simp only [ha, ite_true] at H
                  exact nomatch H
                · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hpo : (!(sin_port_of bs == 0)) = true
                  · simp only [hpo, ite_true] at H
                    exact nomatch H
                  · simp only [hpo, Bool.false_eq_true, ite_false] at H ⊢
                    cases sk with
                    | SkFresh =>
                      simp only [check_copyins] at H
                      by_cases hck : access_ranges_eqb eff.eff_copyins
                          [(addrp, av.toNat)] = true
                      · simp only [hck, ite_true] at H
                        exact record_copyins_of_cleared _ _ i m eff m' evs
                          ((access_ranges_eqb_eq _ _).mp hck)
                          (check_errno_or_success_sound_ok bind_errnos _ _ i
                            (clear_copyins eff) m m' evs H)
                      · simp only [hck, Bool.false_eq_true, ite_false] at H
                        exact nomatch H
                    | SkBound => exact arm_copyins_ok _ _ eff m m' evs i H
                    | SkListening => exact arm_copyins_ok _ _ eff m m' evs i H
                    | SkConnected peer chan rx =>
                      cases hrx : rx 0 with
                      | cons b =>
                        simp only [hrx] at H ⊢
                        exact arm_copyins_ok _ _ eff m m' evs i H
                      | fin =>
                        simp only [hrx] at H ⊢
                        exact arm_copyins_ok _ _ eff m m' evs i H
                      | rst =>
                        simp only [hrx] at H
                        exact nomatch H
                      | timedOut =>
                        simp only [hrx] at H
                        exact nomatch H
                    | SkReset peer chan => exact nomatch H
    | _ => exact arm_ok (errno_ret ENOTSOCK) eff m m' evs i H

theorem check_bind_sound_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_bind i fd addrp addrlen eff m = .CheckUnmodeled) :
    bind_spec fd addrp addrlen i m .unmodeled := by
  unfold check_bind at H
  unfold bind_spec
  refine bind_unmodeled2 inputSpec _ i m i m [] (input_ok i m) ?_
  refine bind_unmodeled2 getModelSpec _ i m m m [] (getModel_ok i m) ?_
  generalize hal : sint32 addrlen = av at H ⊢
  simp only [] at H ⊢
  generalize hfd : fd_lookup (m_fds m) fd = e at H ⊢
  cases e with
  | none => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases e with
    | FdSocket sk =>
      simp only [] at H ⊢
      by_cases hp : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true
      · simp only [hp, ite_true] at H ⊢
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      · simp only [hp, Bool.false_eq_true, ite_false] at H ⊢
        by_cases hz : (av == 0) = true
        · simp only [hz, ite_true] at H ⊢
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
        · simp only [hz, Bool.false_eq_true, ite_false] at H ⊢
          cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) with
          | none =>
            simp only [hrb] at H ⊢
            exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
          | some bs =>
            simp only [hrb] at H ⊢
            by_cases hs : decide (av < SOCKADDR_IN_SIZE) = true
            · simp only [hs, ite_true] at H ⊢
              exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
            · simp only [hs, Bool.false_eq_true, ite_false] at H ⊢
              by_cases hfam : (!(sa_family_of bs == AF_INET
                    || (sa_family_of bs == AF_UNSPEC
                        && sin_addr_of bs == INADDR_ANY))) = true
              · simp only [hfam, ite_true] at H ⊢
                exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
              · simp only [hfam, Bool.false_eq_true, ite_false] at H ⊢
                by_cases ha : (!(sin_addr_of bs == INADDR_ANY)) = true
                · simp only [ha, ite_true] at H ⊢
                  exact record_copyins_unmodeled_intro _ _ i m (unmodeled_intro i m)
                · simp only [ha, Bool.false_eq_true, ite_false] at H ⊢
                  by_cases hpo : (!(sin_port_of bs == 0)) = true
                  · simp only [hpo, ite_true] at H ⊢
                    exact record_copyins_unmodeled_intro _ _ i m (unmodeled_intro i m)
                  · simp only [hpo, Bool.false_eq_true, ite_false] at H ⊢
                    cases sk with
                    | SkFresh =>
                      simp only [check_copyins] at H
                      by_cases hck : access_ranges_eqb eff.eff_copyins
                          [(addrp, av.toNat)] = true
                      · simp only [hck, ite_true] at H
                        exact absurd H (check_errno_or_success_no_unmodeled bind_errnos
                          _ _ (clear_copyins eff) m)
                      · simp only [hck, Bool.false_eq_true, ite_false] at H
                        exact nomatch H
                    | SkBound =>
                      exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
                    | SkListening =>
                      exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
                    | SkConnected peer chan rx =>
                      cases hrx : rx 0 with
                      | cons b =>
                        simp only [hrx] at H ⊢
                        exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
                      | fin =>
                        simp only [hrx] at H ⊢
                        exact absurd H (check_ret_only_copyins_no_unmodeled _ eff _ m [])
                      | rst =>
                        simp only [hrx] at H ⊢
                        exact record_copyins_unmodeled_intro _ _ i m (unmodeled_intro i m)
                      | timedOut =>
                        simp only [hrx] at H ⊢
                        exact record_copyins_unmodeled_intro _ _ i m (unmodeled_intro i m)
                    | SkReset peer chan =>
                      exact record_copyins_unmodeled_intro _ _ i m (unmodeled_intro i m)
    | _ => exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ENOTSOCK) m [])

theorem check_bind_complete_ok (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : bind_spec fd addrp addrlen i m (.ok eff m' evs)) :
    check_bind i fd addrp addrlen eff m = .CheckOk m' evs := by
  unfold check_bind
  unfold bind_spec at H
  obtain ⟨i0, m1, e1, e2, hi, hrest, hevs⟩ := H
  simp only [inputSpec, LinuxSem.LinuxProcessSem.input,
    Outcome.ok.injEq] at hi
  obtain ⟨hi1, hi2, hi3⟩ := hi
  subst i0
  subst m1
  subst e1
  obtain ⟨m0, m2, e3, e4, hm, hbody, hevs2⟩ := hrest
  simp only [getModelSpec, LinuxSem.LinuxProcessSem.getModel,
    Outcome.ok.injEq] at hm
  obtain ⟨hm1, hm2, hm3⟩ := hm
  subst m0
  subst m2
  subst e3
  rw [hevs, hevs2]
  simp only [List.nil_append]
  generalize hal : sint32 addrlen = av at hbody ⊢
  simp only [] at hbody ⊢
  generalize hfd : fd_lookup (m_fds m) fd = e at hbody ⊢
  cases e with
  | none => exact arm_check_ok (errno_ret EBADF) eff m m' e4 i hbody
  | some e =>
    cases e with
    | FdSocket sk =>
      simp only [] at hbody ⊢
      by_cases hp : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true
      · simp only [hp, ite_true] at hbody ⊢
        exact arm_check_ok (errno_ret EINVAL) eff m m' e4 i hbody
      · simp only [hp, Bool.false_eq_true, ite_false] at hbody ⊢
        by_cases hz : (av == 0) = true
        · simp only [hz, ite_true] at hbody ⊢
          exact arm_check_ok (errno_ret EINVAL) eff m m' e4 i hbody
        · simp only [hz, Bool.false_eq_true, ite_false] at hbody ⊢
          cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) with
          | none =>
            simp only [hrb] at hbody ⊢
            exact arm_check_ok (errno_ret EFAULT) eff m m' e4 i hbody
          | some bs =>
            simp only [hrb] at hbody ⊢
            by_cases hs : decide (av < SOCKADDR_IN_SIZE) = true
            · simp only [hs, ite_true] at hbody ⊢
              exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
            · simp only [hs, Bool.false_eq_true, ite_false] at hbody ⊢
              by_cases hfam : (!(sa_family_of bs == AF_INET
                    || (sa_family_of bs == AF_UNSPEC
                        && sin_addr_of bs == INADDR_ANY))) = true
              · simp only [hfam, ite_true] at hbody ⊢
                exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
              · simp only [hfam, Bool.false_eq_true, ite_false] at hbody ⊢
                by_cases ha : (!(sin_addr_of bs == INADDR_ANY)) = true
                · simp only [ha, ite_true] at hbody ⊢
                  obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv _ _ i m eff m' e4 hbody
                  exact absurd Hcore (by simp [unmodeled])
                · simp only [ha, Bool.false_eq_true, ite_false] at hbody ⊢
                  by_cases hpo : (!(sin_port_of bs == 0)) = true
                  · simp only [hpo, ite_true] at hbody ⊢
                    obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv _ _ i m eff m' e4 hbody
                    exact absurd Hcore (by simp [unmodeled])
                  · simp only [hpo, Bool.false_eq_true, ite_false] at hbody ⊢
                    cases sk with
                    | SkFresh =>
                      simp only [] at ⊢
                      obtain ⟨core, Hcore, hEff⟩ :=
                        record_copyins_ok_inv [(addrp, av.toNat)]
                          (alt (bind (errno_from bind_errnos) (fun e => err_ret e))
                            (seqSpec (set_fds (fd_insert (m_fds m) fd
                                (.FdSocket .SkBound))) (ret_only (BitVec.ofInt 64 0))))
                          i m eff m' e4 hbody
                      have Halt := Hcore
                      rcases Hcore with Herr | Hok
                      · obtain ⟨er, q1, f1, f2, hch, hret, heq⟩ := Herr
                        obtain ⟨hmem, hq1, hevs1⟩ :=
                          choose_ok_inv bind_errnos i m er q1 f1 hch
                        rw [hq1] at hret
                        obtain ⟨hcore, hm', hevs2⟩ :=
                          ret_only_ok_inv (errno_ret er) i m core m' f2 hret
                        rw [hevs2, List.append_nil, hevs1] at heq
                        rw [hcore] at hEff
                        have hce : core.eff_copyins = [] := by simp [hcore]
                        have heffc : eff.eff_copyins = [(addrp, av.toNat)] := by
                          rw [hEff]; simp [with_copyins]
                        have hcle : clear_copyins eff = core := by
                          rw [hEff, hcore]; simp [clear_copyins, with_copyins]
                        have h1 := check_errno_or_success_complete_ok bind_errnos
                          (fd_insert (m_fds m) fd (.FdSocket .SkBound))
                          (BitVec.ofInt 64 0) i (clear_copyins eff) m m' e4
                          (by decide) (hcle ▸ Halt)
                        rw [hm', heq] at h1 ⊢
                        rw [h1]
                        exact check_copyins_same _ _ _ heffc
                      · obtain ⟨u, q1, g1, g2, hset, hret, heq⟩ := Hok
                        obtain ⟨hq1, hevs1⟩ := set_fds_ok_inv _ i m u q1 g1 hset
                        rw [hq1] at hret
                        obtain ⟨hcore, hm', hevs2⟩ :=
                          ret_only_ok_inv (BitVec.ofInt 64 0) i
                            (with_fds (fd_insert (m_fds m) fd (.FdSocket .SkBound)) m)
                            core m' g2 hret
                        rw [hevs2, List.append_nil, hevs1] at heq
                        rw [hcore] at hEff
                        have hce : core.eff_copyins = [] := by simp [hcore]
                        have heffc : eff.eff_copyins = [(addrp, av.toNat)] := by
                          rw [hEff]; simp [with_copyins]
                        have hcle : clear_copyins eff = core := by
                          rw [hEff, hcore]; simp [clear_copyins, with_copyins]
                        have h1 := check_errno_or_success_complete_ok bind_errnos
                          (fd_insert (m_fds m) fd (.FdSocket .SkBound))
                          (BitVec.ofInt 64 0) i (clear_copyins eff) m m' e4
                          (by decide) (hcle ▸ Halt)
                        rw [hm', heq] at h1 ⊢
                        rw [h1]
                        exact check_copyins_same _ _ _ heffc
                    | SkBound =>
                      exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
                    | SkListening =>
                      exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
                    | SkConnected peer chan rx =>
                      cases hrx : rx 0 with
                      | cons b =>
                        simp only [hrx] at hbody ⊢
                        exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
                      | fin =>
                        simp only [hrx] at hbody ⊢
                        exact arm_copyins_check_ok _ _ eff m m' e4 i hbody
                      | rst =>
                        simp only [hrx] at hbody ⊢
                        obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv _ _ i m eff m' e4 hbody
                        exact absurd Hcore (by simp [unmodeled])
                      | timedOut =>
                        simp only [hrx] at hbody ⊢
                        obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv _ _ i m eff m' e4 hbody
                        exact absurd Hcore (by simp [unmodeled])
                    | SkReset peer chan =>
                      obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv _ _ i m eff m' e4 hbody
                      exact absurd Hcore (by simp [unmodeled])
    | _ => exact arm_check_ok (errno_ret ENOTSOCK) eff m m' e4 i hbody

theorem check_bind_complete_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) (eff : SyscallEffect)
    (H : bind_spec fd addrp addrlen i m .unmodeled) :
    check_bind i fd addrp addrlen eff m = .CheckUnmodeled := by
  unfold check_bind
  unfold bind_spec at H
  rcases H with hi | ⟨i0, m1, e1, hi, hrest⟩
  · -- the input step declines: impossible
    simp [inputSpec, LinuxSem.LinuxProcessSem.input] at hi
  · simp only [inputSpec, LinuxSem.LinuxProcessSem.input,
      Outcome.ok.injEq] at hi
    obtain ⟨hi1, hi2, hi3⟩ := hi
    subst i0
    subst m1
    subst e1
    rcases hrest with hm0 | ⟨m0, m2, e3, hm, hbody⟩
    · simp [getModelSpec, LinuxSem.LinuxProcessSem.getModel] at hm0
    · simp only [getModelSpec, LinuxSem.LinuxProcessSem.getModel,
        Outcome.ok.injEq] at hm
      obtain ⟨hm1, hm2, hm3⟩ := hm
      subst m0
      subst m2
      subst e3
      generalize hal : sint32 addrlen = av at hbody ⊢
      simp only [] at hbody ⊢
      generalize hfd : fd_lookup (m_fds m) fd = e at hbody ⊢
      cases e with
      | none => exact absurd hbody (ret_only_ne_unmodeled (errno_ret EBADF) i m)
      | some e =>
        cases e with
        | FdSocket sk =>
          simp only [] at hbody ⊢
          by_cases hp : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true
          · simp only [hp, ite_true] at hbody ⊢
            exact absurd hbody (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
          · simp only [hp, Bool.false_eq_true, ite_false] at hbody ⊢
            by_cases hz : (av == 0) = true
            · simp only [hz, ite_true] at hbody ⊢
              exact absurd hbody (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
            · simp only [hz, Bool.false_eq_true, ite_false] at hbody ⊢
              cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) with
              | none =>
                simp only [hrb] at hbody ⊢
                exact absurd hbody (ret_only_ne_unmodeled (errno_ret EFAULT) i m)
              | some bs =>
                simp only [hrb] at hbody ⊢
                by_cases hs : decide (av < SOCKADDR_IN_SIZE) = true
                · simp only [hs, ite_true] at hbody ⊢
                  exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                    (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
                · simp only [hs, Bool.false_eq_true, ite_false] at hbody ⊢
                  by_cases hfam : (!(sa_family_of bs == AF_INET
                        || (sa_family_of bs == AF_UNSPEC
                            && sin_addr_of bs == INADDR_ANY))) = true
                  · simp only [hfam, ite_true] at hbody ⊢
                    exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                      (ret_only_ne_unmodeled (errno_ret EAFNOSUPPORT) i m)
                  · simp only [hfam, Bool.false_eq_true, ite_false] at hbody ⊢
                    by_cases ha : (!(sin_addr_of bs == INADDR_ANY)) = true
                    · simp only [ha, ite_true] at hbody ⊢
                    · simp only [ha, Bool.false_eq_true, ite_false] at hbody ⊢
                      by_cases hpo : (!(sin_port_of bs == 0)) = true
                      · simp only [hpo, ite_true] at hbody ⊢
                      · simp only [hpo, Bool.false_eq_true, ite_false] at hbody ⊢
                        cases sk with
                        | SkFresh =>
                          simp only [] at ⊢
                          exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                            (errno_or_success_no_unmodeled bind_errnos
                              (fd_insert (m_fds m) fd (.FdSocket .SkBound))
                              (BitVec.ofInt 64 0) i m)
                        | SkBound =>
                          exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                            (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
                        | SkListening =>
                          exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                            (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
                        | SkConnected peer chan rx =>
                          cases hrx : rx 0 with
                          | cons b =>
                            simp only [hrx] at hbody ⊢
                            exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                              (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
                          | fin =>
                            simp only [hrx] at hbody ⊢
                            exact absurd (record_copyins_unmodeled_inv _ _ i m hbody)
                              (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
                          | rst =>
                            simp only [hrx] at hbody ⊢
                          | timedOut =>
                            simp only [hrx] at hbody ⊢
                        | SkReset peer chan => rfl
        | _ => exact absurd hbody (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m)
