/-
  * LinuxSem.Checks.Sys.Net.Socket.Connect — connect(2)

  The four agreement lemmas — `check_connect_sound_ok`,
  `check_connect_sound_unmodeled`, `check_connect_complete_ok`,
  `check_connect_complete_unmodeled` — for the `(* ---- connect *)` section
  of `Net/Socket.lean`.

  The checker (`check_connect`) and the spec it is related to
  (`Net.Socket.connect_spec`) are both in the parent module; nothing new
  is *defined* here, only proved, which is why this is a separate file.

  WHY THIS FILE IS SPLIT (a measured kernel limit, not a taste call).
  Unfolding both definitions at once puts the whole arm cascade into one
  goal:

      unfold check_connect in H; unfold connect_spec; dsimp only in H
      …

  In Lean that single term carries EVERY specialization of the unfolded
  `connect_spec` body (10 `FdEntry` cases × 5 `SockState` cases × the
  addrlen/read_bytes_map guards — on the order of a hundred copies of a
  body that itself holds `record_copyins` and two nested `SockState`
  matches), and the kernel rejects it with `(kernel) deep recursion
  detected`; `maxRecDepth` does not help.  A proof confined to ONE arm —
  `H` folded, the branch facts as hypotheses — does compile, so the file is
  organized the way `Socket/Socket.lean` is:

    * `connect_spec_<arm>` states ONE arm of the spec as an `↔`, with the
      guards that select it taken as hypotheses.  Both directions of the
      agreement lemma for that arm are then one `.mp`/`.mpr` away, which is
      why there is one and not two lemmas per arm.
    * `connect_chk_<arm>` is the same arm on the CHECKER's side: at the
      same guards, `check_connect` *is* that one arm.  It exists because of
      a SECOND measured kernel limit — a dispatcher that unfolds
      `check_connect` into its hypothesis and then nests thirteen `cases`
      over the unfolded body is rejected with the same `(kernel) deep
      recursion detected`, while a term that only ever holds one arm's
      `check_ret_only[_copyins] … = …` checks.  So the reduction lives in
      these equations, and each holds one arm.
    * the four public theorems are pure DISPATCHERS: they `cases` on the
      cheap scrutinees only (`fd_lookup`, the addrlen guard, the byte map,
      the `FdEntry`, the `SockState`), `rw` that branch's two equations
      into H (sound) or the goal (complete), and apply the arm lemma.  No
      dispatcher unfolds either definition.

  The spec writes `err_ret EINVAL` where the checker writes
  `check_ret_only eff (errno_ret EINVAL) m []`.  Each spec arm below is
  stated in the form the spec itself uses, and the bridge lemmas
  (`arm_ok`, `arm_copyins_ok`, …) cross from the checker
  form at the `errno_ret` word, which is definitionally the same effect.

  In the spec the `-ENOTSOCK` arm sits BELOW the copy, so it is
  `record_copyins … (err_ret ENOTSOCK)`, and the checker answers it through
  `check_ret_only_copyins`.  The arm above it — `fd_lookup` `none`, the
  addrlen test, the `read_bytes_map` failure — carries no ledger and answers
  through `check_ret_only`.  That asymmetry is the one thing `connect` does
  not share with `bind`, and it is why the ledger is threaded through five
  of the seven arm shapes below.

  `bind_inputSpec` (from `LinuxProcessSem`) and `arm_ok` / `arm_check_ok`
  (from `Checks.Sys.Prelude`) are public, so this file cites them directly.
  `ret_only_ok_inv`, `ret_only_ne_unmodeled`,
  `arm_copyins_ok`, `arm_copyins_check_ok` and
  `record_copyins_unmodeled_intro` are `private` in the parent file
  (or in `Checks/Sys/Fs/Pipe.lean`), so a sibling module cannot cite them;
  they are restated here verbatim under a `connect_` prefix, as
  `Socket/Socket.lean` did with `socket_lowest_fd_*`.  When the parent's are
  made public, the copies below can go — their statements are unchanged.

  Every arm but `-EBADF` takes `av : Int` with `hal : sint32 addrlen = av` in
  place of `sint32 addrlen`.  That is not cosmetic: with the raw
  `sint32 addrlen` in the `decide`-bearing tests, the kernel has to
  normalise the `Int` comparison instance of a compound term and dies of
  `(kernel) deep recursion detected` even on a single arm; at an opaque `av`
  the same proof goes through.  The dispatchers instantiate `av` with
  `sint32 addrlen` and `hal` with `rfl`, which only has to typecheck the
  instance, not rerun the proof.

  `o` is a `{…}` binder in every arm: the goal (complete) or `.mpr`'s
  argument (sound) fixes it, so the dispatchers pass only the guards
  positionally.  The stated form is still `connect_spec … i m o ↔ <the
  arm>`, and `.mp` / `.mpr` still serve the two directions.
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

/- =========================================================================
   The arm bridges
   ========================================================================= -/

/- The prologue peel — the `simp` form of the `bind_step` + `input_ok` +
   `get_model_ok` sequence — is `LinuxSem.LinuxProcessSem.bind_inputSpec`,
   opened above; the same lemma that `Checks/Sys/Fs/Pipe.lean` states
   privately. -/

/- The two arm bridges that used to sit here — `connect_arm_ok` and
   `connect_arm_check_ok` — are now the public `arm_ok` / `arm_check_ok` in
   `Checks.Sys.Prelude`, opened above; the statements are identical, so this
   file cites them directly. -/

/-- A ledger over a declining body declines, and conversely: `record_copyins`
    only wraps the `ok` shape, so an arm whose body is `unmodeled` is the
    spec's `unmodeled` at every outcome.  This is what lets the two
    declining arms below be stated as `↔ unmodeled` like the `socket`
    file's. -/
private theorem connect_record_copyins_unmodeled_iff (reads : List (word × Nat))
    (i : SyscallInput) (m : Model) {o : Outcome SyscallEffect Model event} :
    record_copyins reads unmodeled i m o ↔ unmodeled i m o := by
  cases o with
  | ok eff m' evs =>
      constructor
      · intro H
        obtain ⟨core, Hcore, -⟩ := record_copyins_ok_inv reads unmodeled i m eff m' evs H
        exact nomatch Hcore
      · intro H
        exact nomatch H
  | unmodeled =>
      exact ⟨fun H => record_copyins_unmodeled_inv reads unmodeled i m H,
        fun H => record_copyins_unmodeled_intro reads unmodeled i m H⟩

/- =========================================================================
   One arm of `connect_spec` per lemma

   Order follows the checker: the descriptor, the addrlen test, the
   `read_bytes_map` read, then the `FdEntry` dispatch and, under it, the
   `SockState` fan-out.  Each states: under these guards, the spec IS this
   arm, so both directions of the agreement lemma for the arm are one
   `.mp`/`.mpr`.

   The arms whose outcome depends on the `SockState` still name the
   constructor they answer for: the `SockState` fan-out is part of the
   arm's guard, not of its outcome, and taking it as a hypothesis keeps
   the `↔` form (which is what makes one lemma serve both directions).
   ========================================================================= -/

/-- `fd_lookup` found nothing: -EBADF, above the copy, no ledger. -/
private theorem connect_spec_ebadf (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event}
    (hfd : fd_lookup (m_fds m) fd = none) :
    connect_spec fd addrp addrlen i m o ↔ err_ret EBADF i m o := by
  simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hfd]

/-- `addrlen` is negative or larger than `sockaddr_storage`: -EINVAL,
    above the copy and above the `FdEntry` dispatch, so it is generic in
    the descriptor's kind and carries no ledger. -/
private theorem connect_spec_guard (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (e : FdEntry) (av : Int)
    (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true) :
    connect_spec fd addrp addrlen i m o ↔ err_ret EINVAL i m o := by
  simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
    ite_true]

/-- `copy_from_user` of the address failed: -EFAULT, still above the
    `FdEntry` dispatch, so no ledger. -/
private theorem connect_spec_efault (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (e : FdEntry) (av : Int)
    (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = none) :
    connect_spec fd addrp addrlen i m o ↔ err_ret EFAULT i m o := by
  simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
    Bool.false_eq_true, ite_false, hrb]

/-- A socket descriptor whose `addrlen` does not even cover the address
    family: -EINVAL, BELOW the copy, so it carries the ledger. -/
private theorem connect_spec_family (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = true) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)]) (err_ret EINVAL) i m o := by
  simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
    Bool.false_eq_true, ite_false, hrb, hs, ite_true]

/-- `sa_family == AF_UNSPEC`: `tcp_disconnect` on a fresh socket is a
    no-op returning 0 and changes nothing modeled. -/
private theorem connect_spec_unspec_fresh (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket .SkFresh))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = true) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)])
        (ret_only (BitVec.ofInt 64 0)) i m o := by
  simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
    Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam, ite_true]

/-- `sa_family == AF_UNSPEC` on any socket that is not fresh: a REAL
    disconnect (port release, accept-queue teardown, or an RST), which the
    model declines. -/
private theorem connect_spec_unspec_other (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = true)
    (hsk : sk ≠ .SkFresh) :
    connect_spec fd addrp addrlen i m o ↔ unmodeled i m o := by
  cases sk with
  | SkFresh => exact absurd rfl hsk
  | _ =>
      simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
        Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam, ite_true,
        connect_record_copyins_unmodeled_iff]

/-- A concrete address on an already-connected socket: -EISCONN — NOT
    -EINVAL.  Listening is SS_UNCONNECTED with `sk_state == TCP_LISTEN`,
    which the `SS_UNCONNECTED` arm's pre-loaded -EISCONN catches; accepted
    and reset sockets are SS_CONNECTED. -/
private theorem connect_spec_eisconn (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk1 : sk ≠ .SkFresh) (hsk2 : sk ≠ .SkBound) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)]) (err_ret EISCONN) i m o := by
  cases sk with
  | SkFresh => exact absurd rfl hsk1
  | SkBound => exact absurd rfl hsk2
  | _ =>
      simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
        Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam,
        Bool.false_eq_true, ite_false]

/-- A fresh or bound socket with an address shorter than a `sockaddr_in`:
    `__inet_stream_connect`'s first test answers -EINVAL. -/
private theorem connect_spec_inet_einval (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = true) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)]) (err_ret EINVAL) i m o := by
  rcases hsk with rfl | rfl <;>
    simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
      Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam,
      Bool.false_eq_true, ite_false, hi, ite_true]

/-- A fresh or bound socket whose address is not `AF_INET`:
    `tcp_v4_connect`, NOT -EINVAL. -/
private theorem connect_spec_inet_eafnosupport (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = false)
    (hf : (!(sa_family_of bs == AF_INET)) = true) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)])
        (err_ret EAFNOSUPPORT) i m o := by
  rcases hsk with rfl | rfl <;>
    simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
      Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam,
      Bool.false_eq_true, ite_false, hi, Bool.false_eq_true, ite_false, hf, ite_true]

/-- A fresh or bound socket, a full `sockaddr_in`, `AF_INET`: the attempt
    itself is the environment's, so the model declines. -/
private theorem connect_spec_inet_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = false)
    (hf : (!(sa_family_of bs == AF_INET)) = false) :
    connect_spec fd addrp addrlen i m o ↔ unmodeled i m o := by
  rcases hsk with rfl | rfl <;>
    simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
      Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false, hfam,
      Bool.false_eq_true, ite_false, hi, Bool.false_eq_true, ite_false, hf,
      Bool.false_eq_true, ite_false, connect_record_copyins_unmodeled_iff]

/-- `sock_from_file` rejected the descriptor: -ENOTSOCK.  BELOW the copy —
    the ledger is carried, and each of the nine non-socket `FdEntry`
    constructors reaches this same arm. -/
private theorem connect_spec_enotsock (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) {o : Outcome SyscallEffect Model event} {e : FdEntry}
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hns : ∀ s, e ≠ .FdSocket s)
    (av : Int) (hal : sint32 addrlen = av)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (bs : List byte)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs) :
    connect_spec fd addrp addrlen i m o ↔
      record_copyins (if av == 0 then [] else [(addrp, bs.length)])
        (err_ret ENOTSOCK) i m o := by
  cases e with
  | FdSocket sk => exact absurd rfl (hns sk)
  | _ =>
      simp only [connect_spec, bind_inputSpec, getModelSpec, bind_getModel, hal, hfd, hg,
        Bool.false_eq_true, ite_false, hrb]

/- =========================================================================
   The checker's arm equations

   One per arm, mirroring the spec arms above: at the same guards, the
   checker IS this arm.  They exist for a second measured kernel reason.
   A dispatcher that unfolds `check_connect` in its hypothesis and then
   nests thirteen `cases` over it puts the whole unfolded body — 10
   `FdEntry` × 5 `SockState` specializations — into every branch's
   context, and the kernel answers `(kernel) deep recursion detected` on
   the finished term.  With the checker folded and these equations doing
   the reduction, each dispatcher branch only ever holds
   `check_ret_only[_copyins] … = …`: the term stays small and checks.

   `av` is opaque here for the reason the header gives: a
   `decide`-bearing test over a compound `Int` term does not normalise
   inside the kernel's budget.  A dispatcher instantiates `av` with
   `sint32 addrlen` and `hal` with `rfl`.
   ========================================================================= -/

/-- The `-EBADF` arm. -/
theorem connect_chk_ebadf (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (hfd : fd_lookup (m_fds m) fd = none) :
    check_connect i fd addrp addrlen eff m = check_ret_only eff (errno_ret EBADF) m [] := by
  unfold check_connect
  simp only [hfd]

/-- The `addrlen` out-of-range arm. -/
theorem connect_chk_guard (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (e : FdEntry) (av : Int)
    (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = true) :
    check_connect i fd addrp addrlen eff m = check_ret_only eff (errno_ret EINVAL) m [] := by
  unfold check_connect
  simp only [hal, hfd, hg, ite_true]

/-- The `-EFAULT` arm. -/
theorem connect_chk_efault (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (e : FdEntry) (av : Int)
    (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = none) :
    check_connect i fd addrp addrlen eff m = check_ret_only eff (errno_ret EFAULT) m [] := by
  unfold check_connect
  simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb]

/-- The short-`addrlen` socket arm. -/
theorem connect_chk_family (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = true) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (errno_ret EINVAL) m [] := by
  unfold check_connect
  simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, ite_true]

/-- The `AF_UNSPEC` fresh-socket arm. -/
theorem connect_chk_unspec_fresh (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket .SkFresh))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = true) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (BitVec.ofInt 64 0) m [] := by
  unfold check_connect
  simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
    hfam, ite_true]

/-- The `AF_UNSPEC` declining arm. -/
theorem connect_chk_unspec_other (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = true)
    (hsk : sk ≠ .SkFresh) :
    check_connect i fd addrp addrlen eff m = .CheckUnmodeled := by
  unfold check_connect
  cases sk with
  | SkFresh => exact absurd rfl hsk
  | _ =>
      simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
        hfam, ite_true]

/-- The `-EISCONN` arm. -/
theorem connect_chk_eisconn (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk1 : sk ≠ .SkFresh) (hsk2 : sk ≠ .SkBound) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (errno_ret EISCONN) m [] := by
  unfold check_connect
  cases sk with
  | SkFresh => exact absurd rfl hsk1
  | SkBound => exact absurd rfl hsk2
  | _ =>
      simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
        hfam, Bool.false_eq_true, ite_false]

/-- The `-EINVAL` short-`sockaddr_in` arm. -/
theorem connect_chk_inet_einval (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = true) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (errno_ret EINVAL) m [] := by
  unfold check_connect
  rcases hsk with rfl | rfl <;>
    simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
      hfam, Bool.false_eq_true, ite_false, hi, ite_true]

/-- The `-EAFNOSUPPORT` arm. -/
theorem connect_chk_inet_eafnosupport (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = false)
    (hf : (!(sa_family_of bs == AF_INET)) = true) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (errno_ret EAFNOSUPPORT) m [] := by
  unfold check_connect
  rcases hsk with rfl | rfl <;>
    simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
      hfam, Bool.false_eq_true, ite_false, hi, Bool.false_eq_true, ite_false, hf, ite_true]

/-- The declining `tcp_v4_connect` arm. -/
theorem connect_chk_inet_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (sk : SockState) (bs : List byte)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some (.FdSocket sk))
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs)
    (hs : decide (av < SA_FAMILY_SIZE) = false)
    (hfam : (sa_family_of bs == AF_UNSPEC) = false)
    (hsk : sk = .SkFresh ∨ sk = .SkBound)
    (hi : decide (av < SOCKADDR_IN_SIZE) = false)
    (hf : (!(sa_family_of bs == AF_INET)) = false) :
    check_connect i fd addrp addrlen eff m = .CheckUnmodeled := by
  unfold check_connect
  rcases hsk with rfl | rfl <;>
    simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb, hs, Bool.false_eq_true, ite_false,
      hfam, Bool.false_eq_true, ite_false, hi, Bool.false_eq_true, ite_false, hf,
      Bool.false_eq_true, ite_false]

/-- The `-ENOTSOCK` arm. -/
theorem connect_chk_enotsock (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model) (e : FdEntry)
    (hns : ∀ s, e ≠ .FdSocket s)
    (av : Int) (hal : sint32 addrlen = av)
    (hfd : fd_lookup (m_fds m) fd = some e)
    (hg : (decide (av < 0) || decide (SOCKADDR_STORAGE_SIZE < av)) = false)
    (bs : List byte)
    (hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 av) = some bs) :
    check_connect i fd addrp addrlen eff m =
      check_ret_only_copyins (if av == 0 then [] else [(addrp, bs.length)]) eff
        (errno_ret ENOTSOCK) m [] := by
  unfold check_connect
  cases e with
  | FdSocket sk => exact absurd rfl (hns sk)
  | _ => simp only [hal, hfd, hg, Bool.false_eq_true, ite_false, hrb]

/- =========================================================================
   The four agreement lemmas (pure dispatchers)

   Each walks the checker's guard chain with one `cases` per cheap
   scrutinee and hands the branch's equation to `rw`, which turns H
   (sound) or the goal (complete) into the arm's own shape; the arm lemma
   then supplies the spec side.  `Bool`'s constructor order is `false`,
   `true`, so every `cases` writes the continuation branch first.  No
   dispatcher unfolds either definition.
   ========================================================================= -/

theorem check_connect_sound_ok (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_connect i fd addrp addrlen eff m = .CheckOk m' evs) :
    connect_spec fd addrp addrlen i m (.ok eff m' evs) := by
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [connect_chk_ebadf i fd addrp addrlen eff m hfd] at H
    exact (connect_spec_ebadf i fd addrp addrlen m hfd).mpr
      (arm_ok (errno_ret EBADF) eff m m' evs i H)
  | some e =>
    cases hg : (decide (sint32 addrlen < 0) || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) with
    | false =>
      cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) with
      | none =>
        rw [connect_chk_efault i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg hrb] at H
        exact (connect_spec_efault i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg hrb).mpr
          (arm_ok (errno_ret EFAULT) eff m m' evs i H)
      | some bs =>
        cases e with
        | FdSocket sk =>
          cases hs : decide (sint32 addrlen < SA_FAMILY_SIZE) with
          | false =>
            cases hfam : (sa_family_of bs == AF_UNSPEC) with
            | false =>
              cases sk with
              | SkFresh =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inl rfl) hi hf] at H
                    exact nomatch H
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf] at H
                    exact (connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf).mpr
                      (arm_copyins_ok _ (errno_ret EAFNOSUPPORT) eff m m' evs i H)
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inl rfl) hi] at H
                  exact (connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inl rfl) hi).mpr
                    (arm_copyins_ok _ (errno_ret EINVAL) eff m m' evs i H)
              | SkBound =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inr rfl) hi hf] at H
                    exact nomatch H
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf] at H
                    exact (connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf).mpr
                      (arm_copyins_ok _ (errno_ret EAFNOSUPPORT) eff m m' evs i H)
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inr rfl) hi] at H
                  exact (connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inr rfl) hi).mpr
                    (arm_copyins_ok _ (errno_ret EINVAL) eff m m' evs i H)
              | _ =>
                rw [connect_chk_eisconn i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam (by intro h; cases h) (by intro h; cases h)] at H
                exact (connect_spec_eisconn i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam (by intro h; cases h) (by intro h; cases h)).mpr
                  (arm_copyins_ok _ (errno_ret EISCONN) eff m m' evs i H)
            | true =>
              cases sk with
              | SkFresh =>
                rw [connect_chk_unspec_fresh i fd addrp addrlen eff m bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam] at H
                exact (connect_spec_unspec_fresh i fd addrp addrlen m bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam).mpr
                  (arm_copyins_ok _ (BitVec.ofInt 64 0) eff m m' evs i H)
              | _ =>
                rw [connect_chk_unspec_other i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl hfd
                  hg hrb hs hfam (by intro h; cases h)] at H
                exact nomatch H
          | true =>
            rw [connect_chk_family i fd addrp addrlen eff m sk bs (sint32 addrlen) rfl hfd hg hrb
              hs] at H
            exact (connect_spec_family i fd addrp addrlen m sk bs (sint32 addrlen) rfl hfd hg hrb
              hs).mpr (arm_copyins_ok _ (errno_ret EINVAL) eff m m' evs i H)
        | _ =>
          rw [connect_chk_enotsock i fd addrp addrlen eff m _ (by rintro s h; cases h)
            (sint32 addrlen) rfl hfd hg bs hrb] at H
          exact (connect_spec_enotsock i fd addrp addrlen m hfd (by rintro s h; cases h)
            (sint32 addrlen) rfl hg bs hrb).mpr
            (arm_copyins_ok _ (errno_ret ENOTSOCK) eff m m' evs i H)
    | true =>
      rw [connect_chk_guard i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg] at H
      exact (connect_spec_guard i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg).mpr
        (arm_ok (errno_ret EINVAL) eff m m' evs i H)

theorem check_connect_sound_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_connect i fd addrp addrlen eff m = .CheckUnmodeled) :
    connect_spec fd addrp addrlen i m .unmodeled := by
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [connect_chk_ebadf i fd addrp addrlen eff m hfd] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EBADF) m [])
  | some e =>
    cases hg : (decide (sint32 addrlen < 0) || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) with
    | false =>
      cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) with
      | none =>
        rw [connect_chk_efault i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg hrb] at H
        exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
      | some bs =>
        cases e with
        | FdSocket sk =>
          cases hs : decide (sint32 addrlen < SA_FAMILY_SIZE) with
          | false =>
            cases hfam : (sa_family_of bs == AF_UNSPEC) with
            | false =>
              cases sk with
              | SkFresh =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    exact (connect_spec_inet_unmodeled i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inl rfl) hi hf).mpr (unmodeled_intro i m)
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf] at H
                    exact absurd H
                      (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EAFNOSUPPORT) m [])
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inl rfl) hi] at H
                  exact absurd H
                    (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EINVAL) m [])
              | SkBound =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    exact (connect_spec_inet_unmodeled i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inr rfl) hi hf).mpr (unmodeled_intro i m)
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf] at H
                    exact absurd H
                      (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EAFNOSUPPORT) m [])
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inr rfl) hi] at H
                  exact absurd H
                    (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EINVAL) m [])
              | _ =>
                rw [connect_chk_eisconn i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam (by intro h; cases h) (by intro h; cases h)] at H
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EISCONN) m [])
            | true =>
              cases sk with
              | SkFresh =>
                rw [connect_chk_unspec_fresh i fd addrp addrlen eff m bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam] at H
                exact absurd H
                  (check_ret_only_copyins_no_unmodeled _ eff (BitVec.ofInt 64 0) m [])
              | _ =>
                exact (connect_spec_unspec_other i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd
                  hg hrb hs hfam (by intro h; cases h)).mpr (unmodeled_intro i m)
          | true =>
            rw [connect_chk_family i fd addrp addrlen eff m sk bs (sint32 addrlen) rfl hfd hg hrb
              hs] at H
            exact absurd H
              (check_ret_only_copyins_no_unmodeled _ eff (errno_ret EINVAL) m [])
        | _ =>
          rw [connect_chk_enotsock i fd addrp addrlen eff m _ (by rintro s h; cases h)
            (sint32 addrlen) rfl hfd hg bs hrb] at H
          exact absurd H
            (check_ret_only_copyins_no_unmodeled _ eff (errno_ret ENOTSOCK) m [])
    | true =>
      rw [connect_chk_guard i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])

theorem check_connect_complete_ok (i : SyscallInput) (fd addrp addrlen : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : connect_spec fd addrp addrlen i m (.ok eff m' evs)) :
    check_connect i fd addrp addrlen eff m = .CheckOk m' evs := by
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    rw [connect_chk_ebadf i fd addrp addrlen eff m hfd]
    exact arm_check_ok (errno_ret EBADF) eff m m' evs i
      ((connect_spec_ebadf i fd addrp addrlen m hfd).mp H)
  | some e =>
    cases hg : (decide (sint32 addrlen < 0) || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) with
    | false =>
      cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) with
      | none =>
        rw [connect_chk_efault i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg hrb]
        exact arm_check_ok (errno_ret EFAULT) eff m m' evs i
          ((connect_spec_efault i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg hrb).mp H)
      | some bs =>
        cases e with
        | FdSocket sk =>
          cases hs : decide (sint32 addrlen < SA_FAMILY_SIZE) with
          | false =>
            cases hfam : (sa_family_of bs == AF_UNSPEC) with
            | false =>
              cases sk with
              | SkFresh =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    exact nomatch ((connect_spec_inet_unmodeled i fd addrp addrlen m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf).mp H)
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf]
                    exact arm_copyins_check_ok _ (errno_ret EAFNOSUPPORT) eff m m' evs i
                      ((connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                        hfd hg hrb hs hfam (Or.inl rfl) hi hf).mp H)
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inl rfl) hi]
                  exact arm_copyins_check_ok _ (errno_ret EINVAL) eff m m' evs i
                    ((connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg
                      hrb hs hfam (Or.inl rfl) hi).mp H)
              | SkBound =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    exact nomatch ((connect_spec_inet_unmodeled i fd addrp addrlen m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf).mp H)
                  | true =>
                    rw [connect_chk_inet_eafnosupport i fd addrp addrlen eff m _ bs
                      (sint32 addrlen) rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf]
                    exact arm_copyins_check_ok _ (errno_ret EAFNOSUPPORT) eff m m' evs i
                      ((connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs (sint32 addrlen) rfl
                        hfd hg hrb hs hfam (Or.inr rfl) hi hf).mp H)
                | true =>
                  rw [connect_chk_inet_einval i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                    hfd hg hrb hs hfam (Or.inr rfl) hi]
                  exact arm_copyins_check_ok _ (errno_ret EINVAL) eff m m' evs i
                    ((connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg
                      hrb hs hfam (Or.inr rfl) hi).mp H)
              | _ =>
                rw [connect_chk_eisconn i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam (by intro h; cases h) (by intro h; cases h)]
                exact arm_copyins_check_ok _ (errno_ret EISCONN) eff m m' evs i
                  ((connect_spec_eisconn i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg hrb
                    hs hfam (by intro h; cases h) (by intro h; cases h)).mp H)
            | true =>
              cases sk with
              | SkFresh =>
                rw [connect_chk_unspec_fresh i fd addrp addrlen eff m bs (sint32 addrlen) rfl hfd hg
                  hrb hs hfam]
                exact arm_copyins_check_ok _ (BitVec.ofInt 64 0) eff m m' evs i
                  ((connect_spec_unspec_fresh i fd addrp addrlen m bs (sint32 addrlen) rfl hfd hg hrb
                    hs hfam).mp H)
              | _ =>
                exact nomatch ((connect_spec_unspec_other i fd addrp addrlen m _ bs (sint32 addrlen)
                  rfl hfd hg hrb hs hfam (by intro h; cases h)).mp H)
          | true =>
            rw [connect_chk_family i fd addrp addrlen eff m sk bs (sint32 addrlen) rfl hfd hg hrb hs]
            exact arm_copyins_check_ok _ (errno_ret EINVAL) eff m m' evs i
              ((connect_spec_family i fd addrp addrlen m sk bs (sint32 addrlen) rfl hfd hg hrb hs).mp H)
        | _ =>
          rw [connect_chk_enotsock i fd addrp addrlen eff m _ (by rintro s h; cases h)
            (sint32 addrlen) rfl hfd hg bs hrb]
          exact arm_copyins_check_ok _ (errno_ret ENOTSOCK) eff m m' evs i
            ((connect_spec_enotsock i fd addrp addrlen m hfd (by rintro s h; cases h)
              (sint32 addrlen) rfl hg bs hrb).mp H)
    | true =>
      rw [connect_chk_guard i fd addrp addrlen eff m e (sint32 addrlen) rfl hfd hg]
      exact arm_check_ok (errno_ret EINVAL) eff m m' evs i
        ((connect_spec_guard i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg).mp H)

theorem check_connect_complete_unmodeled (i : SyscallInput) (fd addrp addrlen : word)
    (m : Model) (eff : SyscallEffect)
    (H : connect_spec fd addrp addrlen i m .unmodeled) :
    check_connect i fd addrp addrlen eff m = .CheckUnmodeled := by
  cases hfd : fd_lookup (m_fds m) fd with
  | none =>
    exact absurd ((connect_spec_ebadf i fd addrp addrlen m hfd).mp H)
      (ret_only_ne_unmodeled (errno_ret EBADF) i m)
  | some e =>
    cases hg : (decide (sint32 addrlen < 0) || decide (SOCKADDR_STORAGE_SIZE < sint32 addrlen)) with
    | false =>
      cases hrb : read_bytes_map i.in_mem addrp (BitVec.ofInt 64 (sint32 addrlen)) with
      | none =>
        exact absurd ((connect_spec_efault i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg hrb).mp H)
          (ret_only_ne_unmodeled (errno_ret EFAULT) i m)
      | some bs =>
        cases e with
        | FdSocket sk =>
          cases hs : decide (sint32 addrlen < SA_FAMILY_SIZE) with
          | false =>
            cases hfam : (sa_family_of bs == AF_UNSPEC) with
            | false =>
              cases sk with
              | SkFresh =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inl rfl) hi hf]
                  | true =>
                    exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EAFNOSUPPORT))
                      i m ((connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs (sint32 addrlen)
                        rfl hfd hg hrb hs hfam (Or.inl rfl) hi hf).mp H))
                      (ret_only_ne_unmodeled (errno_ret EAFNOSUPPORT) i m)
                | true =>
                  exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EINVAL)) i m
                    ((connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg
                      hrb hs hfam (Or.inl rfl) hi).mp H))
                    (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
              | SkBound =>
                cases hi : decide (sint32 addrlen < SOCKADDR_IN_SIZE) with
                | false =>
                  cases hf : (!(sa_family_of bs == AF_INET)) with
                  | false =>
                    rw [connect_chk_inet_unmodeled i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl
                      hfd hg hrb hs hfam (Or.inr rfl) hi hf]
                  | true =>
                    exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EAFNOSUPPORT))
                      i m ((connect_spec_inet_eafnosupport i fd addrp addrlen m _ bs (sint32 addrlen)
                        rfl hfd hg hrb hs hfam (Or.inr rfl) hi hf).mp H))
                      (ret_only_ne_unmodeled (errno_ret EAFNOSUPPORT) i m)
                | true =>
                  exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EINVAL)) i m
                    ((connect_spec_inet_einval i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg
                      hrb hs hfam (Or.inr rfl) hi).mp H))
                    (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
              | _ =>
                exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EISCONN)) i m
                  ((connect_spec_eisconn i fd addrp addrlen m _ bs (sint32 addrlen) rfl hfd hg hrb hs
                    hfam (by intro h; cases h) (by intro h; cases h)).mp H))
                  (ret_only_ne_unmodeled (errno_ret EISCONN) i m)
            | true =>
              cases sk with
              | SkFresh =>
                exact absurd (record_copyins_unmodeled_inv _ (ret_only (BitVec.ofInt 64 0)) i m
                  ((connect_spec_unspec_fresh i fd addrp addrlen m bs (sint32 addrlen) rfl hfd hg hrb
                    hs hfam).mp H))
                  (ret_only_ne_unmodeled (BitVec.ofInt 64 0) i m)
              | _ =>
                rw [connect_chk_unspec_other i fd addrp addrlen eff m _ bs (sint32 addrlen) rfl hfd
                  hg hrb hs hfam (by intro h; cases h)]
          | true =>
            exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret EINVAL)) i m
              ((connect_spec_family i fd addrp addrlen m sk bs (sint32 addrlen) rfl hfd hg hrb hs).mp H))
              (ret_only_ne_unmodeled (errno_ret EINVAL) i m)
        | _ =>
          exact absurd (record_copyins_unmodeled_inv _ (ret_only (errno_ret ENOTSOCK)) i m
            ((connect_spec_enotsock i fd addrp addrlen m hfd (by rintro s h; cases h)
              (sint32 addrlen) rfl hg bs hrb).mp H))
            (ret_only_ne_unmodeled (errno_ret ENOTSOCK) i m)
    | true =>
      exact absurd ((connect_spec_guard i fd addrp addrlen m e (sint32 addrlen) rfl hfd hg).mp H)
        (ret_only_ne_unmodeled (errno_ret EINVAL) i m)

end LinuxSem.Checks.Sys.Net.Socket

















