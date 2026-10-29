/-
  * LinuxSem.Checks.DispatchSurface — the modeled syscall list is
    exactly the dispatched set

  [Specs.modeled_sysnos] is the list that documents which syscall
  numbers this model covers.  Nothing in the trace semantics consults
  it, so on its own it is a comment that happens to be typed, and
  [Checks/ProcessCreation] says so where it names this file.

  WHAT IS ALREADY IMPOSSIBLE, and therefore not what this file is for.
  The list and the dispatcher are read off ONE table:
  [modeled_sysnos = arm_numbers spec_table] and
  [syscall_spec = dispatch spec_table].  A number cannot be in
  one and missing from the other, whatever anybody edits.  What this
  file adds is
  two facts the shared table does not give, and one that it does but
  that nothing else states.

  - EXCLUSION, which the table gives cheaply but nothing else states.
    [Sys/Dispatch]'s [dispatch_unmodeled] is stated over
    [lookup_arm t n = none], not over [~ n ∈ arm_numbers t], so
    it does not bridge "absent from the LIST" and "declined".
    [syscall_spec_number_modeled] is that bridge, and it holds for ANY
    table rather than for one dispatcher: the work is in
    [lookup_arm_in], seven lines by induction.

  - THE CONVERSE, which the table does NOT give: every number the list
    names is answered on SOME input ([modeled_sysnos_dispatched]).  An
    arm can sit in [spec_table] and be [unmodeled] on every input, and
    the table identity cannot see it — [dispatch_arm] says the
    dispatcher equals that arm's spec and nothing about the spec
    answering anything.  This is proved by running the computable
    witness of [Progress.syscall_spec_witness] on one probe input per
    number and checking by computation that none falls through;
    [Progress.receptive] carries that back to [syscall_spec].  READ IT
    AS A FLOOR, NOT AS COVERAGE: it says each number has an answer
    somewhere, not that it answers the argument shape any particular
    program uses.  A listed number still declines the shapes its own
    spec rejects, which is the whole point of [Monad.unmodeled].

  - NO REPEATS, which the table does not give either.  [lookup_arm] is
    first-match-wins, so a number listed twice silently shadows the
    second arm, and exactness — stated with [∈] — is blind to it.
    [modeled_sysnos_nodup] rules it out separately, and it is the only
    mechanism anywhere in the tree that would: there is no [Nodup], no
    length and no sortedness lemma over either table.  Two changes
    that each add the same arm merge clean, build green, and leave a
    second arm that nothing will ever reach.

  Both checked facts fail the BUILD rather than a linter.  Adding a
  syscall means adding the arm and, if the number needs arguments the
  default probe does not supply, a [probe_args] entry; get either out
  of step and this file does not compile.

  Spelling.

  [Z] is [Int], `Z_to_bv 64 z` is `BitVec.ofInt 64 z`, `Z.eqb a b` is
  `a == b`, `forallb`/`existsb` are [List.all]/[List.any] (the two
  bridging lemmas are [List.all_eq_true] and [List.any_eq_true]), and
  `In` is [List.Mem].  [bv_unsigned] is not a global abbreviation in this
  tree; it is declared here exactly as the other [Checks] files declare
  it, so the statements below read in one vocabulary.

  THE TWO COMPUTED CHECKS ARE [`decide`], and they are the file's whole
  cost.  The evaluation they would otherwise want is a COMPILED one
  (a compiled evaluator), and compiled-versus-kernel
  reduction is a real difference on a super-linear computation.  Here the
  kernel manages, and it is worth recording: the whole 90-entry probe
  sweep of [modeled_sysnos_probes_answer] elaborates in about a second,
  because each arm's witness is shallow.  A future arm whose witness
  ranges over a whole page is the case where this stops being true, and
  the remedy then is per-entry lemmas rather than a bigger heartbeat
  budget.  The `fail "…"` diagnostics the same checks would emit are kept
  as prose: a `decide` that goes [false] fails the build too, only
  without the sentence.

  [count_occ Z.eq_dec] has no Lean counterpart: [List.count] counts with
  `==`, and the standard library's [List.nodup_iff_count] is stated over
  it, so [count_occ_filter_eqb] is the one-line bridge — see there for
  the argument order.
-/
import LinuxSem.Checks.Progress
import LinuxSem.Common.RocqSpelling
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.Specs
import LinuxSem.LinuxProcessSem.Sys.Dispatch
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
import LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
import LinuxSem.LinuxProcessSem.Sys.Net.Socket

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.Sys.Net.Socket
open LinuxSem.Checks.Progress

namespace LinuxSem.Checks.DispatchSurface

open LinuxSem.Common.RocqSpelling

/- `bv_unsigned w` is `w`'s value as an integer, from the one shared
   declaration in `LinuxSem.Common.RocqSpelling` (imported and opened
   here).  Being an abbreviation it is definitionally `(w.toNat : Int)` —
   the spelling `Sys.Dispatch.dispatch` itself uses, so nothing below
   needs to rewrite between the two. -/

/- =========================================================================
   Small helpers
   ========================================================================= -/

/-- Membership decided by computation, so the side conditions below can be
    discharged by computation against whatever [modeled_sysnos] currently
    holds — no proof edit when an entry is added.

    [List.all] is [forallb], and
    [List.all_eq_true] is the bridge to [∈]. -/
theorem forallb_In (f : Int → Bool) (l : List Int) (x : Int)
    (H : l.all f = true) (Hin : x ∈ l) : f x = true :=
  (List.all_eq_true.mp H) x Hin

/-- ... and the `existsb` one: a hit under `n == ·` is a member. -/
theorem in_of_existsb_eqb (n : Int) (l : List Int)
    (H : l.any (fun x => n == x) = true) : n ∈ l := by
  obtain ⟨x, Hx, Heq⟩ := List.any_eq_true.mp H
  have hnx : n = x := beq_iff_eq.mp Heq
  subst hnx
  exact Hx

/- =========================================================================
   Direction 1: nothing outside [modeled_sysnos] is dispatched
   ========================================================================= -/

/-- The whole of it, and it is a fact about [lookup_arm] rather than about
    any particular table: if the lookup finds an arm, the number it was
    given is one of the table's own.  The [if] that decides each step is
    exactly the equality the conclusion needs. -/
theorem lookup_arm_in (t : List SpecArm) (n : Int) (a : SpecArm)
    (H : lookup_arm t n = some a) : n ∈ arm_numbers t := by
  induction t with
  | nil => simp [lookup_arm] at H
  | cons b r ih =>
      have H' : (if b.sa_no == n then some b else lookup_arm r n) = some a := H
      by_cases hb : (b.sa_no == n) = true
      · rw [ite_eq_left hb] at H'
        have hbn : b.sa_no = n := beq_iff_eq.mp hb
        simp only [arm_numbers, List.map_cons, List.mem_cons]
        exact Or.inl hbn.symm
      · rw [ite_eq_right hb] at H'
        simp only [arm_numbers, List.map_cons, List.mem_cons]
        exact Or.inr (ih H')

/-- An [Ok] outcome pins the syscall number into the list.  A number with
    no arm reaches [Monad.unmodeled], which admits no [Ok] at all. -/
theorem syscall_spec_number_modeled (i : SyscallInput) (m : Model)
    (x : SyscallEffect) (m' : Model) (evs : List event)
    (H : syscall_spec i m (.ok x m' evs)) :
    bv_unsigned i.in_sysno ∈ modeled_sysnos := by
  unfold syscall_spec dispatch modeled_sysnos at *
  cases h : lookup_arm spec_table (i.in_sysno.toNat : Int) with
  | none =>
      rw [h] at H
      exact absurd H (by simp [unmodeled])
  | some a => exact lookup_arm_in _ _ _ h

/-- The same fact read as fail-closed behaviour, with
    `bv_unsigned i.in_sysno` written the way `Sys.Dispatch.dispatch` reads
    it. -/
theorem syscall_spec_unmodeled_outside (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event)
    (Hnin : bv_unsigned i.in_sysno ∉ modeled_sysnos)
    (H : syscall_spec i m o) : o = .unmodeled := by
  cases o with
  | ok x m' evs => exact absurd (syscall_spec_number_modeled i m x m' evs H) Hnin
  | unmodeled => rfl

/-- The fail-closed direction stated as an INTRODUCTION lemma: outside the
    list, [Unmodeled] is an admissible outcome.  That is a strictly weaker
    claim than [syscall_spec_unmodeled_outside] — it says the dispatcher
    ADMITS [Unmodeled], not that it admits nothing else, and [Sys] is a
    relation, so a spec can admit both — but it is the shape a proof that
    needs to CONSTRUCT the declined outcome wants.  It follows from the
    exclusion direction and [Progress.receptive] (which supplies an
    admissible outcome for every input) in two steps, so there is no reason
    for anything else in the tree to prove it separately. -/
theorem syscall_spec_declines_outside (i : SyscallInput) (m : Model)
    (Hnin : bv_unsigned i.in_sysno ∉ modeled_sysnos) :
    syscall_spec i m .unmodeled := by
  rw [← syscall_spec_unmodeled_outside i m (syscall_spec_witness i m) Hnin
        (receptive i m)]
  exact receptive i m

/- =========================================================================
   Direction 2: every number in [modeled_sysnos] is answered somewhere
   ========================================================================= -/

/-- A model with no files, no mappings and only the three standard fds, so a
    probe fd of AT_FDCWD (which is not a valid fd) reliably answers -EBADF. -/
def probe_model : Model :=
  init_model [] (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) (BitVec.ofInt 64 sp_window_lo)
    0x40000000
    (mkProcInput [] [] [] IEof (BitVec.ofInt 64 1000) (BitVec.ofInt 64 1002) []
                 net_silent default_nofile (BitVec.ofInt 64 0) hwcap_rv64gc false .Sv48)

/-- THE ONE EXCEPTION TO ONE MODEL FOR EVERY NUMBER, and it is worth
    reading before the table below rather than after.

    [tkill] (130) and [tgkill] (131) answer only where the task DECLARED
    the abort path ([State.in_abort_terminal]) and only for the caller's
    own tid, so no choice of argument registers reaches an answer from
    [probe_model]: the declaration is a property of the run, not of the
    call.  That is the arms' whole design — with the declaration clear
    they decline every shape, which is what the numbers did when they had
    no arm — so the probe for those two numbers runs against a model that
    declares it and pins a tid, and every other number keeps
    [probe_model].

    What this check therefore says about 130 and 131 is "answers under a
    declaration", which is the strongest true statement about them.  The
    other half — that they decline WITHOUT one — is
    [Checks.Cases.Kernel.Signal]'s [tkill_off_declined], which runs the
    answering shape against a model with the declaration clear. -/
def probe_tid : word := BitVec.ofInt 64 4242

def probe_model_abort : Model :=
  with_tid probe_tid
    (init_model [] (BitVec.ofInt 64 0) (BitVec.ofInt 64 0) (BitVec.ofInt 64 sp_window_lo)
       0x40000000
       (mkProcInput [] [] [] IEof (BitVec.ofInt 64 1000) (BitVec.ofInt 64 1002) []
                    net_silent default_nofile (BitVec.ofInt 64 0) hwcap_rv64gc
                    true .Sv48))

/-- The model a probe of [n] runs against. -/
def probe_model_for (n : Int) : Model :=
  if n == 130 || n == 131 then probe_model_abort else probe_model

/-- Where [clone3]'s probe finds a FORK-SHAPED [struct clone_args].  Far
    from 0 and from AT_FDCWD, the two addresses every other probe uses. -/
def clone3_probe_uargs : word := BitVec.ofInt 64 0x10000

/-- Every address readable and writable, holding a NUL byte — openat's
    probe path is then the empty string (-ENOENT) and no buffer is
    unreadable — EXCEPT the one byte that makes [clone3]'s struct
    fork-shaped.

    [clone3_spec] declines every size but [CLONE_ARGS_SIZE] and then every
    struct but the one [Fork.clone3_fork_args_b] admits: all eleven fields
    zero except [exit_signal] = SIGCHLD, which [Fork.clone_args_field]
    reads from offset 32.  An all-NUL memory therefore gives
    [exit_signal = 0] and the arm declines, so unlike every other entry
    below this one cannot be fixed by choosing arguments — the fixture
    has to carry the struct.  Only that byte changes; every other address
    still reads NUL. -/
def probe_mem : word → Option byte :=
  fun a => some (if bv_eqb a (clone3_probe_uargs + BitVec.ofInt 64 32)
                 then BitVec.ofInt 8 SIGCHLD
                 else BitVec.ofInt 8 0)

/-- Arguments for the probe of syscall number [n].

    The default answers every modeled number except the ones listed
    below.  Deliberately not a COUNT: a number here is checked by
    nobody and goes stale when the next arm is added, while the list
    below is at least read by whoever adds an arm.

    [a0] is AT_FDCWD, which is
    three useful things at once: the dirfd that openat and readlinkat
    model, an fd that no open-file table holds (so fd-taking arms answer
    -EBADF), and — as an address, `2^64 - 100` — a value no page boundary
    can equal, so the arms that gate on alignment answer -EINVAL there.
    The remaining registers are zero, which is a modeled flag word for
    openat and getrandom and a zero length for munmap and the transfer
    calls.

    mprotect is one of the alignment-gated arms: [mprotect_spec] reaches
    [addr mod page_size] before it consults [mprotect_modeled_b prot],
    and the one gate ahead of the alignment test reads only [prot]'s two
    grows bits, which answers -EINVAL rather than declining.  So the
    default probe answers 226 whatever [prot] holds and it needs no entry
    here.

    The exceptions are the arms that DECLINE what the default registers
    hold rather than answering with it, so none of them reaches an error
    gate without help:

    - mmap (222) and mremap (216) decline the default FLAG WORD.
      [mmap_spec] at zero length answers only for an anonymous mapping
      and is [unmodeled] otherwise, and [mremap_spec] models only
      MREMAP_MAYMOVE.
    - prlimit64 (261) declines the default PID: [Specs.prlimit64_spec]
      answers only for pid 0 (no other task exists), only for
      RLIMIT_CORE, and only when exactly one of the two rlimit pointers
      is NULL — three gates the default registers fail at the first.
    - clock_gettime (113) declines the default CLOCKID: [a0] is a clock
      id here rather than an fd, and AT_FDCWD truncated to 32 bits is no
      modeled clock, so the arm declines before it reaches an answer.
    - clone (220) declines the default FLAG WORD: [clone_fork_flags_b]
      admits the single word SIGCHLD and nothing else.
    - clone3 (435) declines the default SIZE and the default STRUCT: it
      answers only [CLONE_ARGS_SIZE] bytes at a readable address holding
      the fork-shaped [struct clone_args], which is why [probe_mem] above
      carries one.
    - wait4 (260) declines the default ARGUMENT WORDS, before anything
      else: [Kernel.Exit.wait4_spec] answers only when [upid] is the
      32-bit -1 [Kernel.Exit.WAIT_ANY32] and [options] is exactly
      [WNOHANG].
    - sendto (206) and sendmsg (211) decline the default FLAG WORD, and
      for a stricter reason than mmap's: [Net.Socket.send_flags_modeled]
      is a [Z.eqb] against MSG_NOSIGNAL, not a mask test, so zero is not
      a permissive default here but a value the arm refuses.  The flag
      sits in a DIFFERENT REGISTER for the two: sendto's arguments are
      (fd, buf, count, flags, addr, addrlen) so it is [a3], and
      sendmsg's are (fd, msg, flags) so it is [a2].

      THIS COUNT AND THESE BULLETS ARE HAND-MAINTAINED AND NOTHING
      CHECKS THEM.  [probe_args] below is gated by
      [modeled_sysnos_probes_answer], which fails the build if an entry
      is missing; the sentence and the list up here are gated by nobody,
      so adding another entry without editing them leaves a paragraph
      that is wrong by one and compiles clean.
    - socketpair (199) declines the default FAMILY.  [a0] IS the family,
      so there is no -EBADF to fall back on the way recvfrom (207) and
      recvmsg (212) have one, and [Net.Socket.socketpair_modeled_b]
      admits only AF_INET.  That is the general rule the entries above
      follow — an arm that resolves an fd first answers -EBADF before the
      gated argument matters, and an arm that gates on an ARGUMENT VALUE
      declines and needs an entry.

    THE RULE HAS AN EXCEPTION, and it is worth naming so that the next
    arm-that-reads-a0-as-a-value is not given an entry it does not need.
    getgroups (158) reads [a0] as a value too — it is [gidsetsize], not
    an fd — and it needs no entry, because AT_FDCWD is -100 and
    [Kernel.Groups.getgroups_spec]'s FIRST test is [gidsetsize < 0].  The
    default probe therefore reaches its -EINVAL rather than declining.
    What decides the question is not whether [a0] is an fd but whether
    the arm has an ERROR GATE the default value trips, which is the same
    thing mprotect's paragraph above says about alignment.

    Add an entry when a newly listed syscall needs something else;
    leaving it out makes [modeled_sysnos_probes_answer] below fail to
    compute to [true], which fails the build. -/
def probe_args (n : Int) : List word :=
  let z := BitVec.ofInt 64 0
  if n == 19 then
    -- eventfd2 reads a1 as the FLAG WORD and a0 as an initial counter it
    -- never judges, so the default probe -- whose a1 is 0 -- hands it an
    -- ACCEPTED flag word and the arm declines the descriptor it would
    -- have to mint.  [O_LARGEFILE] is a bit outside [EFD_FLAGS_SET], so
    -- the arm reaches the -EINVAL that is its only answer.  a0 stays 0
    -- because no [count] changes the verdict.
    [z, BitVec.ofInt 64 O_LARGEFILE, z, z, z, z]
  else if n == 222 then
    -- mmap answers -EINVAL on a zero length only for an anonymous mapping
    [AT_FDCWD, z, z, BitVec.ofInt 64 (MAP_PRIVATE + MAP_ANONYMOUS), z, z]
  else if n == 216 then
    -- mremap models only MREMAP_MAYMOVE; the misaligned a0 is then -EINVAL
    [AT_FDCWD, z, z, BitVec.ofInt 64 MREMAP_MAYMOVE, z, z]
  else if n == 261 then
    -- prlimit64 READING RLIMIT_CORE: pid 0, and exactly one of the two
    -- rlimit pointers NULL -- new_rlim = 0 with old_rlim writable is
    -- the read path, and [probe_mem] makes a3 writable
    [z, BitVec.ofInt 64 RLIMIT_CORE, z, BitVec.ofInt 64 4096, z, z]
  else if n == 199 then
    -- socketpair gates on the FAMILY and has no descriptor to resolve
    -- first, so the default [AT_FDCWD] in a0 is read as a family no
    -- [Net.Socket.socketpair_modeled_b] accepts and the arm declines.
    -- With AF_INET/SOCK_STREAM at protocol 0 it reaches [socketpair_fds]
    -- and then the [usockvec] store, which [probe_mem] makes writable at
    -- 0, so it answers.  a3 stays 0 for that reason.
    [BitVec.ofInt 64 AF_INET, BitVec.ofInt 64 SOCK_STREAM, z, z, z, z]
  else if n == 113 then
    -- clock_gettime dispatches on a CLOCKID, not an fd: AT_FDCWD truncated
    -- to 32 bits is no modeled clock, so the arm declines before it reaches
    -- an answer.  [CLOCK_REALTIME] is 0, so this reads like the default --
    -- named anyway, because a bare [z] in the one position that carries the
    -- entry is indistinguishable from a don't-care.  Chosen over
    -- [CLOCK_MONOTONIC] because that arm also gates on
    -- [m_clock m <? CLOCK_NS_ENVELOPE], which would make whether the probe
    -- answers depend on [probe_model]'s clock; the realtime arm gates only
    -- on the destination, which [probe_mem] makes writable.
    [BitVec.ofInt 64 CLOCK_REALTIME, z, z, z, z, z]
  else if n == 98 then
    -- futex dispatches on the OP WORD, and the default a1 of 0 is
    -- [FUTEX_WAIT] without [FUTEX_PRIVATE_FLAG] -- a shared wait, which
    -- [Kernel.Futex.Syscalls.futex_spec] declines.  The private wake is
    -- the arm with an answer that needs nothing of the model: a0 of 0 is
    -- 4-byte aligned and passes [access_okb], so the arm returns 0
    -- waiters woken.  a0 is named rather than left at [AT_FDCWD]
    -- because that address is aligned too and would answer -EFAULT --
    -- an answer, so the probe would pass, but on the gate rather than
    -- on the operation.
    [z, BitVec.ofInt 64 FUTEX_WAKE_PRIVATE, z, z, z, z]
  else if n == 167 then
    -- prctl dispatches on an OPTION, not an fd: [AT_FDCWD] narrowed to 32
    -- bits is 0xffffff9c, which is no prctl option, so the arm declines
    -- before it reaches an answer.  [PR_CAPBSET_READ] is the one option
    -- [Kernel.Sys.prctl_modeled_options] carries, and a1 is the capability
    -- number -- 0 is a capability at or below [CAP_LAST_CAP], so the arm
    -- answers 1 rather than -EINVAL.  Which of the two answers this probe
    -- reaches does not matter to the check, only that it reaches one.
    [BitVec.ofInt 64 PR_CAPBSET_READ, z, z, z, z, z]
  else if n == 220 then
    -- clone declines the default FLAG WORD: [clone_fork_flags_b] admits
    -- the single word SIGCHLD and nothing else, so [AT_FDCWD] there is
    -- [unmodeled] rather than an answer.
    [BitVec.ofInt 64 SIGCHLD, z, z, z, z, z]
  else if n == 435 then
    -- clone3 reaches [kernel_clone] through a struct in user memory
    -- rather than through registers, and declines every size but
    -- [CLONE_ARGS_SIZE] and every struct but the fork-shaped one.  No
    -- choice of registers alone reaches an answer; the struct lives in
    -- [probe_mem] at [clone3_probe_uargs].
    [clone3_probe_uargs, BitVec.ofInt 64 CLONE_ARGS_SIZE, z, z, z, z]
  else if n == 260 then
    -- wait4 decides on the ARGUMENT WORDS before it decides anything else:
    -- [Kernel.Exit.wait4_spec] declines unless [upid] is the 32-bit -1
    -- [Kernel.Exit.WAIT_ANY32], [options] is exactly [WNOHANG], and
    -- [rusage] is NULL.  The default probe's a0 is [AT_FDCWD] = -100,
    -- which is not -1, so the arm would fail closed before reaching the
    -- -ECHILD that is its only answer.  a1 ([stat_addr]) is left at the
    -- default: at a negative return [kernel_wait4] never dereferences it,
    -- so no property of it changes the verdict.
    [BitVec.ofInt 64 WAIT_ANY32, z, BitVec.ofInt 64 WNOHANG, z, z, z]
  else if n == 132 then
    -- sigaltstack reads its [stack_t] out of user memory, and [probe_mem]
    -- is all-NUL, so the default probe's a0 ([AT_FDCWD] read as an
    -- address) presents a struct whose [ss_sp] and [ss_size] are both
    -- zero under a mode of 0 -- the one shape
    -- [Kernel.Signal.sigaltstack_spec] declines, because there the
    -- kernel's answer turns on the [sas_ss_flags] word execve did not
    -- reset.  Unlike clone3, no struct is needed to get past it: BOTH
    -- pointers NULL is a real call that [do_sigaltstack] answers 0 for,
    -- having done nothing, so zeros in a0 and a1 reach an answer.
    [z, z, z, z, z, z]
  else if n == 206 then
    -- sendto gates on the FLAG WORD BEING EXACTLY [MSG_NOSIGNAL] --
    -- [Net.Socket.send_flags_modeled] is a [Z.eqb], not a mask test -- so
    -- the default probe's flags 0 declines before the arm reaches any
    -- answer.  With the flag set the order is the spec's own: the flag
    -- word, then [import_ubuf]'s range verdict on a zero-length buffer at
    -- 0, then the descriptor -- and [AT_FDCWD] is not an open fd, so the
    -- arm answers -EBADF.  a4 stays 0 because a non-NULL destination
    -- address is [unmodeled].
    [AT_FDCWD, z, z, BitVec.ofInt 64 MSG_NOSIGNAL, z, z]
  else if n == 73 then
    -- ppoll's default probe would be an INFINITE WAIT: a0 is unread at
    -- [nfds = 0], and a NULL [tsp] with a zero count is the one shape
    -- [poll_select_finish] cannot describe, since [do_poll]'s
    -- [timed_out] flag is never set and the call never returns.  So the
    -- probe passes a non-NULL [tsp] instead, and [probe_mem]'s all-zero
    -- bytes make it a requested {0,0} — [poll_select_set_timeout]'s own
    -- zero-timeout case, which polls once, returns 0 and writes nothing
    -- back.  Any address serves; AT_FDCWD is reused so the entry names
    -- no new constant.  a1 stays 0, so [ufds] is never dereferenced.
    [AT_FDCWD, z, AT_FDCWD, z, z, z]
  else if n == 130 then
    -- tkill answers only for the caller's own tid, which
    -- [probe_model_abort] pins; the signal is SIGABRT, the only one any
    -- arm sends.  The default [AT_FDCWD] in a0 is negative and would
    -- reach the -EINVAL gate, so the entry is what makes the probe
    -- measure the DELIVERY rather than the argument check.
    [probe_tid, BitVec.ofInt 64 SIGABRT, z, z, z, z]
  else if n == 131 then
    -- tgkill, the same call with the thread-group id in front.
    [probe_tid, probe_tid, BitVec.ofInt 64 SIGABRT, z, z, z]
  else if n == 211 then
    -- sendmsg, for the same reason and with the flag in a different
    -- position: its arguments are (fd, msg, flags), so the flag word is a2
    -- where sendto's is a3.  Unlike sendto, sendmsg resolves the
    -- descriptor BEFORE it copies the 56-byte header, so [AT_FDCWD]
    -- answers -EBADF without [probe_mem] needing to hold a readable
    -- [struct user_msghdr] at 0.
    [AT_FDCWD, z, BitVec.ofInt 64 MSG_NOSIGNAL, z, z, z]
  else [AT_FDCWD, z, z, z, z, z]

def probe_input (n : Int) : SyscallInput :=
  ⟨BitVec.ofInt 64 n, probe_args n, probe_mem, probe_mem⟩

/-- Does the dispatcher answer number [n] at all? -/
def probe_answers (n : Int) : Bool :=
  match syscall_spec_witness (probe_input n) (probe_model_for n) with
  | .ok _ _ _ => true
  | .unmodeled => false

/-- THE CHECK.  Every listed number has an arm that answers.  A number added
    to [modeled_sysnos] without a dispatch arm falls through to the final
    [unmodeled] and turns this into [false = true].

    The diagnostic is kept as prose because a `decide` that goes
    [false] fails here too, only without the sentence: "a number in
    Specs.modeled_sysnos has no answering dispatch arm -- add the arm, or
    give the number a probe_args entry if the default probe cannot reach
    its answer". -/
theorem modeled_sysnos_probes_answer : modeled_sysnos.all probe_answers = true := by
  decide

/-- The list holds genuine unsigned 64-bit syscall numbers, so a probe input
    really does carry the number it was built from. -/
theorem modeled_sysnos_in_range :
    modeled_sysnos.all (fun n => decide (0 ≤ n) && decide (n < 2 ^ 64)) = true := by
  decide

theorem modeled_sysnos_dispatched (n : Int) (Hin : n ∈ modeled_sysnos) :
    ∃ (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event),
      bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ .unmodeled := by
  refine ⟨probe_input n, probe_model_for n,
    syscall_spec_witness (probe_input n) (probe_model_for n), ?_, receptive _ _, ?_⟩
  · -- the probe carries the number it was built from
    have Hr := forallb_In _ _ _ modeled_sysnos_in_range Hin
    rw [Bool.and_eq_true] at Hr
    obtain ⟨Hlo, Hhi⟩ := Hr
    have hlo : (0 : Int) ≤ n := of_decide_eq_true Hlo
    have hhi : n < two_pow_64 := by
      have := of_decide_eq_true Hhi
      simpa [two_pow_64] using this
    show bv_unsigned (probe_input n).in_sysno = n
    unfold bv_unsigned
    exact bv_unsigned_Z_to_bv_u64 n ⟨hlo, hhi⟩
  · have Ha := forallb_In _ _ _ modeled_sysnos_probes_answer Hin
    unfold probe_answers at Ha
    cases h : syscall_spec_witness (probe_input n) (probe_model_for n) with
    | ok x m' evs => simp
    | unmodeled => rw [h] at Ha; exact absurd Ha (by simp)

/-- Both directions in one statement: [modeled_sysnos] is EXACTLY the set of
    syscall numbers the dispatcher answers. -/
theorem modeled_sysnos_exact (n : Int) :
    n ∈ modeled_sysnos ↔
    (∃ (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect Model event),
      bv_unsigned i.in_sysno = n ∧ syscall_spec i m o ∧ o ≠ .unmodeled) := by
  constructor
  · exact modeled_sysnos_dispatched n
  · intro ⟨i, m, o, Hn, Hspec, Ho⟩
    cases o with
    | ok x m' evs =>
        rw [← Hn]
        exact syscall_spec_number_modeled i m x m' evs Hspec
    | unmodeled => exact absurd rfl Ho

/- =========================================================================
   The list itself: no number listed twice

   Exactness above is stated with [∈], which cannot see a repeat: a list
   holding 62 twice satisfies both directions exactly as one holding it
   once, and every proof in this file still closes.  Nor does the shared
   table help, because the repeat is IN the table: [modeled_sysnos] is
   [arm_numbers spec_table], so a duplicated arm duplicates the number
   too, and [Sys.Dispatch.lookup_arm] then resolves it first-match-wins —
   the second arm is dead and nothing says so.  [checked_table_arms] does
   not see it either: it compares the two tables to each other, and a
   merge that duplicates an arm in [spec_table] and its mirror in
   [checked_table] keeps them equal.  That pair is exactly what two
   independent additions at the same sorted position produce.  State the
   absence of repeats as its own checked fact rather than leave it to a
   reader counting entries.
   ========================================================================= -/

/-- [n] occurs exactly once in [l].  Counted with `==` rather than with a
    decision procedure that returns equality PROOFS, because the
    computation below would normalize those too.
    [count_occ_filter_eqb] bridges the two to [List.count] once,
    symbolically.

    The comparison here is `Z.eqb n` — `n =? x` — and `==` on
    the filtered element is `x == n`.  The two differ in argument order
    only, and [Int]'s is a [LawfulBEq], so the filter is the same list;
    writing it in that order is what makes [count_occ_filter_eqb] the
    one-line bridge. -/
def listed_once (l : List Int) (n : Int) : Bool :=
  (l.filter (fun x => x == n)).length == 1

/-- The bridge to the count [List.nodup_iff_count] reads.  It is stated
    against `count_occ Z.eq_dec`; [List.count] counts with
    `==`, so this is [List.count_eq_countP] and
    [List.countP_eq_length_filter] — and because both sides already use
    the same comparison, it takes no argument-order step. -/
theorem count_occ_filter_eqb (l : List Int) (n : Int) :
    l.count n = (l.filter (fun x => x == n)).length := by
  rw [List.count_eq_countP, List.countP_eq_length_filter]

/-- Stated over an ABSTRACT [l]: proved directly about [modeled_sysnos]
    instead, its close spends seconds unfolding every entry of the list
    through the counter's decider, and the cost grows with the list.  With
    [l] a variable the kernel has nothing to unfold, and the instance below
    is free at any length.

    This closes with `NoDup_count_occ'`; Lean core's
    counterpart is [List.nodup_iff_count], so the argument is the same one
    line for the membership case. -/
theorem nodup_of_listed_once (l : List Int)
    (H : l.all (listed_once l) = true) : l.Nodup := by
  rw [List.nodup_iff_count]
  intro n
  by_cases hn : n ∈ l
  · have Hn : (l.filter (fun x => x == n)).length = 1 := by
      have := forallb_In (listed_once l) l n H hn
      unfold listed_once at this
      exact beq_iff_eq.mp this
    rw [count_occ_filter_eqb, Hn]
    exact Nat.le_refl 1
  · rw [List.count_eq_zero_of_not_mem hn]
    exact Nat.zero_le 1

/-- THE CHECK.

    The diagnostic is prose, for the reason [modeled_sysnos_probes_answer]
    gives: "a number appears more than once in Specs.modeled_sysnos -- a
    merge or a replay duplicated an entry; delete the repeat". -/
theorem modeled_sysnos_listed_once :
    modeled_sysnos.all (listed_once modeled_sysnos) = true := by
  decide

theorem modeled_sysnos_nodup : modeled_sysnos.Nodup :=
  nodup_of_listed_once _ modeled_sysnos_listed_once

end LinuxSem.Checks.DispatchSurface
