/-
  * LinuxProcessSem.Checks.Sys.Net.Socket.Socket — the `socket` (198)
      checker's four agreement lemmas

  The four agreement lemmas — `check_socket_sound_ok`,
  `check_socket_sound_unmodeled`, `check_socket_complete_ok`,
  `check_socket_complete_unmodeled` — stated on the parent module's
  `check_socket` and on `Net.Socket.socket_spec`.  The rest of the socket
  family (`bind`, `accept4`, `listen`, `sendto`, ...) keeps its proofs in
  the parent file; `socket` is split out for the reason the next paragraph
  records.

  WHY THIS FILE EXISTS (a MEASURED Lean kernel limit, not a taste call).
  `check_socket` and `socket_spec` are the longest straight-line guard
  chains in the tree: twelve boolean tests, thirteen arms, and the spec
  hides five `let`-bound words (`tu`, `flagbits`, `ty`, `fam`, `pro`) and an
  `alt` behind them.  Unfolding BOTH the checker (in the hypothesis) and the
  spec (in the goal) and then walking the guards with one `cases` per guard
  puts both unfolded bodies into a single proof term.  The Lean kernel then
  rejects the term with

      (kernel) deep recursion detected

  while elaborating, and `set_option maxRecDepth` does NOT raise that limit
  (measured: the one-piece `check_socket_sound_ok` is rejected at every
  setting tried).  A proof confined to ONE arm — one leaf of the guard tree,
  with every guard replaced by a hypothesis — compiles in well under a
  second.  So the file is organized that way:

    * `socket_spec_<arm>` states ONE arm of the spec as an `↔`, with the
      guards that select it taken as hypotheses.  Both directions of the
      agreement lemma for that arm are then one `.mp`/`.mpr` away, which is
      why there is one and not two lemmas per scalar arm.
    * the four public theorems are pure DISPATCHERS: they `cases` on the
      cheap guard scrutinees only, and hand the reduced hypothesis to the
      arm lemma for that leaf.  No dispatcher unfolds `socket_spec`.

  A word is read UNSIGNED (`(w.toNat : Int)`); a `Bool` test is `==` or
  `decide (· < ·)` / `decide (· ≤ ·)`; the bit operations are
  `z_ldiff`/`z_land`/`z_lor`; and `.ok` / `.unmodeled` are the constructors
  of `Outcome`, `CheckOk` / `CheckReject` / `CheckUnmodeled` those of
  `check_result`.  `bv_eqb ret (alloc_fd (m_fds m))` is the word equality
  here, with `Fs.bv_eqb_eq` as its reflection.

  The arm correspondence is stated per arm rather than re-derived inside
  each of the four proofs: `simp only [<the arm's guards>,
  Bool.false_eq_true, ite_false, ite_true]` on `socket_spec` with
  `bind_getModel` applied at the head.

  `ret_only_ok_inv`, `choose_ok_inv`, `ret_only_ne_unmodeled`,
  `lowest_fd_arm`, `lowest_fd_arm_inv` and `lowest_fd_arm_ne_unmodeled`
  are `private` in the parent file, so a sibling module cannot cite them;
  they are restated here verbatim (`socket_lowest_fd_*`) or in the form
  this file needs.  When the parent's are made public, the copies below can
  go — their statements are unchanged.  `arm_ok` / `arm_check_ok` are no
  longer restated: `LinuxSem.Checks.Sys.Prelude` states them publicly, and
  the `open` below is what reaches them.
-/
import LinuxSem.Checks.Sys.Net.Socket

namespace LinuxSem.Checks.Sys.Net.Socket

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Uaccess
  (rw_bytes_max modeled_rw_count access_ok_zero)
open LinuxSem.LinuxProcessSem.Sys.Fs.File (lowest_fd)
open LinuxSem.LinuxProcessSem.Sys.Fs.ReadWrite (UIO_FASTIOV)
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Uaccess (check_access_ok_zero)

/- The syscall layer's 32-bit argument truncation.  `Sys.Uapi` carries a
   staging alias of the same function, so the bare name is ambiguous once
   both namespaces are open; the checkers must use the one the specs use, so
   the `local notation` below binds it to `Syscall`'s (the same binding the
   parent file makes).  It declares nothing — unlike the `private abbrev` it
   replaces — and expands to the canonical name. -/
local notation "abi_low32" => LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32

/- =========================================================================
   The restated leaves (the parent file's `private` helpers)
   ========================================================================= -/

/- The one-arm checker ↔ spec bridge (`arm_ok` for checker → spec,
   `arm_check_ok` for spec → checker) is stated publicly in
   `LinuxSem.Checks.Sys.Prelude`, opened above. -/

/- =========================================================================
   One arm of `socket_spec` per lemma

   Each states: under these guards, the spec IS this arm.  The
   guards are the checker's own tests (the spec's `let`-bound `ty`,
   `fam`, `pro` are zeta-reduced by the `simp only` below, so both
   spellings meet at the same term).  Both directions of the
   agreement lemma for the arm are then one `.mp`/`.mpr`.

   The hypotheses are named after the guard they decide (`h8` is
   the `SOCK_STREAM` test), so the two arms below that test skip
   `h9`/`h10` — they are decided under `h11`/`h12` instead.
   ========================================================================= -/

/-- The `flags` arm: an unknown flag bit in `type`, ahead of every other test.  The
    spec is `err_ret EINVAL`. -/
private theorem socket_spec_flags (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret EINVAL i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, ite_true]

/-- The `nonblock` arm: `SOCK_NONBLOCK`, which the model has no `O_NONBLOCK` notion
    for, so the spec declines. -/
private theorem socket_spec_nonblock (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true]

/-- The `family_range` arm: `domain` outside `[0, NPROTO)`, which is judged before the
    type.  The spec is `err_ret EAFNOSUPPORT`. -/
private theorem socket_spec_family_range (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret EAFNOSUPPORT i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, Bool.false_eq_true, ite_false, ite_true]

/-- The `type_range` arm: a type word at or above `SOCK_MAX`.  The spec is
    `err_ret EINVAL`. -/
private theorem socket_spec_type_range (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret EINVAL i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, Bool.false_eq_true, ite_false, ite_true]

/-- The `family` arm: an in-range family that is not `AF_INET`; its registration is
    a property of the kernel build, so the spec declines. -/
private theorem socket_spec_family (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false, ite_true]

/-- The `packet` arm: `SOCK_PACKET` under `AF_INET`, which `__sock_create` rewrites
    to `PF_PACKET` above `inet_create`.  The spec declines. -/
private theorem socket_spec_packet (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_false, ite_true]

/-- The `protocol_range` arm: `protocol` outside `[0, IPPROTO_MAX)`.  The spec is
    `err_ret EINVAL`. -/
private theorem socket_spec_protocol_range (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret EINVAL i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ite_false, ite_true]

/-- The `stream_runtime` arm: `SOCK_STREAM` with `IPPROTO_SCTP` or `IPPROTO_MPTCP`,
    both of which join `inetsw` at module load, so the spec
    declines. -/
private theorem socket_spec_stream_runtime (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = true)
    (h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.false_eq_true, ite_false, ite_true]

/-- The `protocol` arm: `SOCK_STREAM` with a protocol other than the wildcard
    `IPPROTO_IP` or `IPPROTO_TCP`.  The spec is
    `err_ret EPROTONOSUPPORT`. -/
private theorem socket_spec_protocol (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = true)
    (h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = false)
    (h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret EPROTONOSUPPORT i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ite_false, ite_true]

/-- The `dgram` arm: `SOCK_DGRAM` or `SOCK_RAW`, which keep `AF_INET` to
    `inet_create`, and which the model has no protocol for.  The
    spec declines. -/
private theorem socket_spec_dgram (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = false)
    (h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h11, Bool.false_eq_true, ite_false, ite_true]

/-- The `seqpacket` arm: `SOCK_SEQPACKET` or `SOCK_DCCP`, which sctp and dccp
    register at module load, so the spec declines. -/
private theorem socket_spec_seqpacket (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = false)
    (h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW)) = false)
    (h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP)) = true)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ unmodeled i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, Bool.false_eq_true, ite_false, ite_true]

/-- The `esocktnosupport` arm: a type `inetsw` has no entry for.  The spec is
    `err_ret ESOCKTNOSUPPORT`. -/
private theorem socket_spec_esocktnosupport (domain type protocol : word)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = false)
    (h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW)) = false)
    (h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP)) = false)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event) :
    socket_spec domain type protocol i m o ↔ err_ret ESOCKTNOSUPPORT i m o := by
  unfold socket_spec
  simp only [getModelSpec, bind_getModel]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, Bool.false_eq_true, ite_false]

/- =========================================================================
   arm 10 of 13 — `SOCK_STREAM` under `AF_INET` with an in-range protocol:
   `alt` of the injectable errnos and the lowest free descriptor.

   The other twelve arms are pure `err_ret`/`unmodeled`, so one `↔` each
   (`socket_spec_<arm>`) serves both directions; this one carries an `alt`
   and needs both directions spelled out.
   ========================================================================= -/

/-- The success arm, checker -> spec.  `accept4`'s fresh-fd step: the
    rejected `check_new_fd_result` shapes cannot produce `CheckOk`, and the
    two accept shapes are exactly the spec's `alt` halves. -/
private theorem socket_arm_stream_sound_ok (domain type protocol : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = true)
    (h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = false)
    (h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))) = false)
    (H : check_new_fd_result socket_errnos eff m
        (fun fd => with_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) m)
          = .CheckOk m' evs) :
    socket_spec domain type protocol i m (.ok eff m' evs) := by
  obtain ⟨ret, ws, zs, us, cs, cis⟩ := eff
  unfold socket_spec
  refine bind_ok0 getModelSpec _ i m m m _ m' evs rfl ?_
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    Bool.false_eq_true, ite_false, ite_true] at H ⊢
  unfold check_new_fd_result at H
  cases ws <;> cases zs <;> cases us <;> cases cs <;> cases cis
  · by_cases h11 : errno_ret_in socket_errnos ret = true
    · simp only [h11, ite_true, check_result.CheckOk.injEq] at H
      obtain ⟨rfl, rfl⟩ := H
      obtain ⟨e', hmem, rfl⟩ := (errno_ret_in_true _ _).mp h11
      refine alt_l _ _ _ _ _ (bind_ok0 (errno_from socket_errnos) (fun e => err_ret e)
        i m e' m _ m [] (choose_ok _ e' i m hmem) (pure_ok _ i m))
    · simp only [h11, Bool.false_eq_true, ite_false] at H
      cases hf : fd_lookup (m_fds m) ret
      · simp only [hf] at H
        cases heq : bv_eqb ret (alloc_fd (m_fds m))
        · simp only [heq, Bool.false_eq_true, ite_false] at H
          exact absurd H (by intro hh; exact nomatch hh)
        · have hret : ret = alloc_fd (m_fds m) := (Fs.bv_eqb_eq _ _).mp heq
          simp only [heq, ite_true, check_result.CheckOk.injEq] at H
          obtain ⟨rfl, rfl⟩ := H
          rw [hret] at hf ⊢
          exact alt_r _ _ _ _ _ (lowest_fd_arm (m_fds m)
            (fun nfd mm => with_fds (fd_insert (m_fds m) nfd (.FdSocket .SkFresh)) mm)
            i m hf)
      · simp only [hf] at H
        exact absurd H (by intro hh; exact nomatch hh)
  all_goals (exact absurd H (by intro hh; exact nomatch hh))

/-- The success arm, spec -> checker.  The two halves of the spec's `alt`,
    each read back into `check_new_fd_result`'s accepting shape. -/
private theorem socket_arm_stream_complete_ok (domain type protocol : word)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = true)
    (h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = false)
    (h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))) = false)
    (H : socket_spec domain type protocol i m (.ok eff m' evs)) :
    check_new_fd_result socket_errnos eff m
      (fun fd => with_fds (fd_insert (m_fds m) fd (.FdSocket .SkFresh)) m)
        = .CheckOk m' evs := by
  unfold socket_spec at H
  have H1 := (bind_getModel _ i m (.ok eff m' evs)).mp H
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ite_false, ite_true] at H1
  rcases H1 with He | Hs
  · obtain ⟨er, m1, evs1, evs2, Hch, Hret, heq⟩ := He
    obtain ⟨hmem, hm1, hevs1⟩ := choose_ok_inv socket_errnos i m er m1 evs1 Hch
    rw [hm1] at Hret
    obtain ⟨heff, hm', hevs2⟩ := ret_only_ok_inv (errno_ret er) i m eff m' evs2 Hret
    rw [hevs2, List.append_nil, hevs1] at heq
    rw [heff, hm', heq]
    simp [check_new_fd_result, errno_ret_in_intro socket_errnos er hmem]
  · obtain ⟨hlookup, heff, hm', hevs⟩ :=
      lowest_fd_arm_inv (m_fds m) _ i m eff m' evs Hs
    rw [heff, hm', hevs]
    simp [check_new_fd_result, hlookup,
      errno_ret_in_alloc_fd socket_errnos (m_fds m) (by decide), bv_eqb_refl]

/-- The success arm cannot decline: neither half of the `alt` has an
    `unmodeled` outcome. -/
private theorem socket_arm_stream_ne_unmodeled (domain type protocol : word)
    (i : SyscallInput) (m : Model)
    (h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0)) = false)
    (h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0)) = false)
    (h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain)) = false)
    (h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)) = false)
    (h5 : (!(sint32 domain == AF_INET)) = false)
    (h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET) = false)
    (h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol)) = false)
    (h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM) = true)
    (h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP)) = false)
    (h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP))) = false)
    (H : socket_spec domain type protocol i m .unmodeled) :
    False := by
  unfold socket_spec at H
  have H1 := (bind_getModel _ i m .unmodeled).mp H
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ite_false, ite_true] at H1
  rcases H1 with He | Hs
  · exact absurd He (errno_arm_ne_unmodeled socket_errnos i m)
  · exact absurd Hs (lowest_fd_arm_ne_unmodeled (m_fds m) _ i m)

/- =========================================================================
   The four agreement lemmas (pure dispatchers)

   Each walks the checker's guard chain with one `cases` per test and
   hands the reduced hypothesis to that leaf's arm lemma.  `Bool`'s
   constructor order is `false`, `true`, so every `cases` writes the
   continuation branch first — the same order the parent file's
   `accept4` dispatch uses.
   ========================================================================= -/

theorem check_socket_sound_ok (domain type protocol : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_socket domain type protocol eff m = .CheckOk m' evs) :
    socket_spec domain type protocol i m (.ok eff m' evs) := by
  unfold check_socket at H
  cases h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
      (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
  · simp only [h1, Bool.false_eq_true, ite_false] at H
    cases h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0))
    · simp only [h2, Bool.false_eq_true, ite_false] at H
      cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain))
      · simp only [h3, Bool.false_eq_true, ite_false] at H
        cases h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK))
        · simp only [h4, Bool.false_eq_true, ite_false] at H
          cases h5 : (!(sint32 domain == AF_INET))
          · simp only [h5, Bool.false_eq_true, ite_false] at H
            cases h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
            · simp only [h6, Bool.false_eq_true, ite_false] at H
              cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol))
              · simp only [h7, Bool.false_eq_true, ite_false] at H
                cases h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM)
                · simp only [h8, Bool.false_eq_true, ite_false] at H
                  cases h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
                      || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW))
                  · simp only [h11, Bool.false_eq_true, ite_false] at H
                    cases h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
                        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP))
                    · simp only [h12, Bool.false_eq_true, ite_false] at H
                      exact (socket_spec_esocktnosupport domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 h12 i m _).mpr
                        (arm_ok (errno_ret ESOCKTNOSUPPORT) eff m m' evs i H)
                    · simp only [h12, ite_true] at H
                      exact absurd H (by intro hh; exact nomatch hh)
                  · simp only [h11, ite_true] at H
                    exact absurd H (by intro hh; exact nomatch hh)
                · simp only [h8, ite_true] at H
                  cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP))
                  · simp only [h9, Bool.false_eq_true, ite_false] at H
                    cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP)))
                    · simp only [h10, Bool.false_eq_true, ite_false] at H
                      exact socket_arm_stream_sound_ok domain type protocol eff m m' evs i
                        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 H
                    · simp only [h10, ite_true] at H
                      exact (socket_spec_protocol domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 i m _).mpr
                        (arm_ok (errno_ret EPROTONOSUPPORT) eff m m' evs i H)
                  · simp only [h9, ite_true] at H
                    exact absurd H (by intro hh; exact nomatch hh)
              · simp only [h7, ite_true] at H
                exact (socket_spec_protocol_range domain type protocol h1 h2 h3 h4 h5 h6 h7 i m _).mpr
                  (arm_ok (errno_ret EINVAL) eff m m' evs i H)
            · simp only [h6, ite_true] at H
              exact absurd H (by intro hh; exact nomatch hh)
          · simp only [h5, ite_true] at H
            exact absurd H (by intro hh; exact nomatch hh)
        · simp only [h4, ite_true] at H
          exact (socket_spec_type_range domain type protocol h1 h2 h3 h4 i m _).mpr
            (arm_ok (errno_ret EINVAL) eff m m' evs i H)
      · simp only [h3, ite_true] at H
        exact (socket_spec_family_range domain type protocol h1 h2 h3 i m _).mpr
          (arm_ok (errno_ret EAFNOSUPPORT) eff m m' evs i H)
    · simp only [h2, ite_true] at H
      exact absurd H (by intro hh; exact nomatch hh)
  · simp only [h1, ite_true] at H
    exact (socket_spec_flags domain type protocol h1 i m _).mpr
      (arm_ok (errno_ret EINVAL) eff m m' evs i H)

theorem check_socket_sound_unmodeled (domain type protocol : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_socket domain type protocol eff m = .CheckUnmodeled) :
    socket_spec domain type protocol i m .unmodeled := by
  unfold check_socket at H
  cases h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
      (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
  · simp only [h1, Bool.false_eq_true, ite_false] at H
    cases h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0))
    · simp only [h2, Bool.false_eq_true, ite_false] at H
      cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain))
      · simp only [h3, Bool.false_eq_true, ite_false] at H
        cases h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK))
        · simp only [h4, Bool.false_eq_true, ite_false] at H
          cases h5 : (!(sint32 domain == AF_INET))
          · simp only [h5, Bool.false_eq_true, ite_false] at H
            cases h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
            · simp only [h6, Bool.false_eq_true, ite_false] at H
              cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol))
              · simp only [h7, Bool.false_eq_true, ite_false] at H
                cases h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM)
                · simp only [h8, Bool.false_eq_true, ite_false] at H
                  cases h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
                      || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW))
                  · simp only [h11, Bool.false_eq_true, ite_false] at H
                    cases h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
                        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP))
                    · simp only [h12, Bool.false_eq_true, ite_false] at H
                      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret ESOCKTNOSUPPORT) m [])
                    · simp only [h12, ite_true] at H
                      exact (socket_spec_seqpacket domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 h12 i m .unmodeled).mpr
                        (unmodeled_intro i m)
                  · simp only [h11, ite_true] at H
                    exact (socket_spec_dgram domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 i m .unmodeled).mpr
                      (unmodeled_intro i m)
                · simp only [h8, ite_true] at H
                  cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP))
                  · simp only [h9, Bool.false_eq_true, ite_false] at H
                    cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP)))
                    · simp only [h10, Bool.false_eq_true, ite_false] at H
                      exact absurd H (check_new_fd_result_no_unmodeled socket_errnos eff m _)
                    · simp only [h10, ite_true] at H
                      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EPROTONOSUPPORT) m [])
                  · simp only [h9, ite_true] at H
                    exact (socket_spec_stream_runtime domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h9 i m .unmodeled).mpr
                      (unmodeled_intro i m)
              · simp only [h7, ite_true] at H
                exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
            · simp only [h6, ite_true] at H
              exact (socket_spec_packet domain type protocol h1 h2 h3 h4 h5 h6 i m .unmodeled).mpr
                (unmodeled_intro i m)
          · simp only [h5, ite_true] at H
            exact (socket_spec_family domain type protocol h1 h2 h3 h4 h5 i m .unmodeled).mpr
              (unmodeled_intro i m)
        · simp only [h4, ite_true] at H
          exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
      · simp only [h3, ite_true] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EAFNOSUPPORT) m [])
    · simp only [h2, ite_true] at H
      exact (socket_spec_nonblock domain type protocol h1 h2 i m .unmodeled).mpr
        (unmodeled_intro i m)
  · simp only [h1, ite_true] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_socket_complete_ok (domain type protocol : word)
    (i : SyscallInput) (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : socket_spec domain type protocol i m (.ok eff m' evs)) :
    check_socket domain type protocol eff m = .CheckOk m' evs := by
  unfold check_socket
  cases h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
      (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    cases h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain))
      · simp only [Bool.false_eq_true, ite_false] at ⊢
        cases h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK))
        · simp only [Bool.false_eq_true, ite_false] at ⊢
          cases h5 : (!(sint32 domain == AF_INET))
          · simp only [Bool.false_eq_true, ite_false] at ⊢
            cases h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
            · simp only [Bool.false_eq_true, ite_false] at ⊢
              cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol))
              · simp only [Bool.false_eq_true, ite_false] at ⊢
                cases h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM)
                · simp only [Bool.false_eq_true, ite_false] at ⊢
                  cases h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
                      || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
                        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      exact arm_check_ok (errno_ret ESOCKTNOSUPPORT) eff m m' evs i
                        ((socket_spec_esocktnosupport domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 h12 i m (.ok eff m' evs)).mp H)
                    · simp only [ite_true] at ⊢
                      exact absurd ((socket_spec_seqpacket domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 h12 i m (.ok eff m' evs)).mp H)
                        (by intro hh; exact nomatch hh)
                  · simp only [ite_true] at ⊢
                    exact absurd ((socket_spec_dgram domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 i m (.ok eff m' evs)).mp H)
                      (by intro hh; exact nomatch hh)
                · simp only [ite_true] at ⊢
                  cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP)))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      exact socket_arm_stream_complete_ok domain type protocol i eff m m' evs
                        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 H
                    · simp only [ite_true] at ⊢
                      exact arm_check_ok (errno_ret EPROTONOSUPPORT) eff m m' evs i
                        ((socket_spec_protocol domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 i m (.ok eff m' evs)).mp H)
                  · simp only [ite_true] at ⊢
                    exact absurd ((socket_spec_stream_runtime domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h9 i m (.ok eff m' evs)).mp H)
                      (by intro hh; exact nomatch hh)
              · simp only [ite_true] at ⊢
                exact arm_check_ok (errno_ret EINVAL) eff m m' evs i
                  ((socket_spec_protocol_range domain type protocol h1 h2 h3 h4 h5 h6 h7 i m (.ok eff m' evs)).mp H)
            · simp only [ite_true] at ⊢
              exact absurd ((socket_spec_packet domain type protocol h1 h2 h3 h4 h5 h6 i m (.ok eff m' evs)).mp H)
                (by intro hh; exact nomatch hh)
          · simp only [ite_true] at ⊢
            exact absurd ((socket_spec_family domain type protocol h1 h2 h3 h4 h5 i m (.ok eff m' evs)).mp H)
              (by intro hh; exact nomatch hh)
        · simp only [ite_true] at ⊢
          exact arm_check_ok (errno_ret EINVAL) eff m m' evs i
            ((socket_spec_type_range domain type protocol h1 h2 h3 h4 i m (.ok eff m' evs)).mp H)
      · simp only [ite_true] at ⊢
        exact arm_check_ok (errno_ret EAFNOSUPPORT) eff m m' evs i
          ((socket_spec_family_range domain type protocol h1 h2 h3 i m (.ok eff m' evs)).mp H)
    · simp only [ite_true] at ⊢
      exact absurd ((socket_spec_nonblock domain type protocol h1 h2 i m (.ok eff m' evs)).mp H)
        (by intro hh; exact nomatch hh)
  · simp only [ite_true] at ⊢
    exact arm_check_ok (errno_ret EINVAL) eff m m' evs i
      ((socket_spec_flags domain type protocol h1 i m (.ok eff m' evs)).mp H)

theorem check_socket_complete_unmodeled (domain type protocol : word)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (H : socket_spec domain type protocol i m .unmodeled) :
    check_socket domain type protocol eff m = .CheckUnmodeled := by
  unfold check_socket
  cases h1 : (!(z_ldiff (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
      (z_lor SOCK_CLOEXEC SOCK_NONBLOCK) == 0))
  · simp only [Bool.false_eq_true, ite_false] at ⊢
    cases h2 : (!(z_land (z_ldiff ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK)
        SOCK_NONBLOCK == 0))
    · simp only [Bool.false_eq_true, ite_false] at ⊢
      cases h3 : (decide (sint32 domain < 0) || decide (NPROTO ≤ sint32 domain))
      · simp only [Bool.false_eq_true, ite_false] at ⊢
        cases h4 : (decide (SOCK_MAX ≤ z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK))
        · simp only [Bool.false_eq_true, ite_false] at ⊢
          cases h5 : (!(sint32 domain == AF_INET))
          · simp only [Bool.false_eq_true, ite_false] at ⊢
            cases h6 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_PACKET)
            · simp only [Bool.false_eq_true, ite_false] at ⊢
              cases h7 : (decide (sint32 protocol < 0) || decide (IPPROTO_MAX ≤ sint32 protocol))
              · simp only [Bool.false_eq_true, ite_false] at ⊢
                cases h8 : (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_STREAM)
                · simp only [Bool.false_eq_true, ite_false] at ⊢
                  cases h11 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DGRAM)
                      || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_RAW))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h12 : ((z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_SEQPACKET)
                        || (z_land ((abi_low32 type).toNat : Int) SOCK_TYPE_MASK == SOCK_DCCP))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      exact absurd ((socket_spec_esocktnosupport domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h11 h12 i m .unmodeled).mp H)
                        (ret_only_ne_unmodeled (errno_ret ESOCKTNOSUPPORT) i m)
                    · simp only [ite_true] at ⊢
                  · simp only [ite_true] at ⊢
                · simp only [ite_true] at ⊢
                  cases h9 : ((sint32 protocol == IPPROTO_SCTP) || (sint32 protocol == IPPROTO_MPTCP))
                  · simp only [Bool.false_eq_true, ite_false] at ⊢
                    cases h10 : (!((sint32 protocol == IPPROTO_IP) || (sint32 protocol == IPPROTO_TCP)))
                    · simp only [Bool.false_eq_true, ite_false] at ⊢
                      exfalso
                      exact socket_arm_stream_ne_unmodeled domain type protocol i m h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 H
                    · simp only [ite_true] at ⊢
                      exact absurd ((socket_spec_protocol domain type protocol h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 i m .unmodeled).mp H)
                        (ret_only_ne_unmodeled (errno_ret EPROTONOSUPPORT) i m)
                  · simp only [ite_true] at ⊢
              · simp only [ite_true] at ⊢
                exact absurd ((socket_spec_protocol_range domain type protocol h1 h2 h3 h4 h5 h6 h7 i m .unmodeled).mp H)
                  (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
            · simp only [ite_true] at ⊢
          · simp only [ite_true] at ⊢
        · simp only [ite_true] at ⊢
          exact absurd ((socket_spec_type_range domain type protocol h1 h2 h3 h4 i m .unmodeled).mp H)
            (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
      · simp only [ite_true] at ⊢
        exact absurd ((socket_spec_family_range domain type protocol h1 h2 h3 i m .unmodeled).mp H)
          (ret_only_ne_unmodeled (errno_ret EAFNOSUPPORT) i m)
    · simp only [ite_true] at ⊢
  · simp only [ite_true] at ⊢
    exact absurd ((socket_spec_flags domain type protocol h1 i m .unmodeled).mp H)
      (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

end LinuxSem.Checks.Sys.Net.Socket







