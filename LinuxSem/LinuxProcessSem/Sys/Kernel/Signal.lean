/-
  * LinuxProcessSem.Sys.Kernel.Signal — rt_sigaction (134), rt_sigprocmask (135), tkill (130), tgkill (131)


  This file answers to Linux [kernel/signal.c]: it holds what the
  kernel defines there, and nothing else.  Which file a spec belongs
  in is therefore not a judgement call — look up where the kernel
  defines the syscall.  [Specs.v] carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  [Specs.v] holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.

  What each dependency supplies:

  - `MonadInstances` fixes the concrete `Sys Model SyscallInput event`, so
    a spec's type is `SysSpec SyscallEffect`, and
    `getModelSpec`/`modifySpec`/`seqSpec` are the monad's state, update and
    sequencing steps;
  - `StateLedger` carries the `ProcState` accessors
    and setters this file reads and writes (`m_sigmask`, `with_sigmask`,
    `m_sigaltstack_installed`, `with_sigaltstack_installed`,
    `m_sigabrt_pending`, `with_sigabrt_pending`, `with_killed`,
    `m_abort_terminal`, `m_tid`, `m_vmmaps`);
  - `Sys.Syscall` supplies `ret_only`, `err_ret`, `w_is0`, `abi_low32`
    (the word-level helpers) and `int32`/`how32`;
  - `Sys.Uaccess` (through `StateMemory`) supplies `access_okb`,
    `read_bytes_map`, `readable_bytes`, `read_u64`; `Sys.Uapi` supplies
    `SIG_BLOCK`/`SIG_UNBLOCK`/`SIG_SETMASK`, `NSIG_BYTES`,
    `SS_ONSTACK`/`SS_DISABLE`/`SS_AUTODISARM`, `SS_FLAGS_OFF`/`SS_SIZE_OFF`,
    `SIGALTSTACK_BYTES`, `MINSIGSTKSZ`, `sig_kernel_only_mask`, `SIGABRT`
    and `sigabrt_mask`;
  - `State` supplies the errno constants (`EINVAL`, `EFAULT`, `ENOMEM`,
    `ESRCH`), `errno_ret`, `mkEffect`, `with_copyins`, `SyscallInput`,
    `SyscallEffect` and `le_bytes_to_word`'s companion `Z_to_le_bytes`
    (from `BvBase`).

  MONAD NOTATION.  `x <- c ;; k` is `bind c (fun x => k)`, and the `;;`
  that discards a `unit` result is `seqSpec`.  `Z_to_bv 64 z` is
  `BitVec.ofInt 64 z`, `bv_unsigned w` is `(w.toNat : Int)`, `bv_and` is
  `&&&`, `bv_or` is `|||`, `bv_not` is `~~~`, `negb` is `!`, `bv_eqb` is
  `==`, and `Z.eqb a b` is `a == b`.

  `Z` BITWISE OPERATIONS.  Lean's core library has no bitwise operations
  on `Int` at all (`BvBase.bytes_le_to_Nat`'s note records the same gap for
  `Z.land`), so the three predicates whose kernel form uses `Z.ldiff` are
  stated on the UNSIGNED reading of the word, in `Nat`, where the values
  always live:

  - `sa_flags_ok` — `Z.ldiff x m = 0` is "every set bit of `x` is in `m`",
    which is `x &&& m = x` for finite `x`;
  - `ss_mode` — `Z.ldiff x SS_AUTODISARM` is `x` with the one flag bit
    cleared, which is `x &&& ~~~SS_AUTODISARM`.

  Both `x` and the mask are below 2^64, so the `Nat` reading is exact.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uaccess
import LinuxSem.LinuxProcessSem.Sys.Uapi

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Signal

/-! ## The `Monad.lean` setters this file calls

    NOTE.  `Monad.lean` carries no state setters — each spec file declares
    the handful it calls (`set_fds` in `Sys/Fs/Open.lean`, `set_statpin` in
    `Sys/Fs/Stat.lean`, …) — so the four this file needs are declared here.
    Each is `modify` applied to its `with_*`: `set_sigmask sm` is
    `modify (with_sigmask sm)`, `set_sigaltstack_installed` is
    `modify with_sigaltstack_installed`, `set_sigabrt_pending` is
    `modify with_sigabrt_pending`, and `set_killed sig` is
    `modify (with_killed sig)`.
-/

def set_sigmask (sm : word) : SysSpec Unit := modifySpec (with_sigmask sm)

def set_sigaltstack_installed : SysSpec Unit :=
  modifySpec with_sigaltstack_installed

def set_sigabrt_pending : SysSpec Unit := modifySpec with_sigabrt_pending

def set_killed (sig : word) : SysSpec Unit := modifySpec (with_killed sig)

/-! ## rt_sigaction (134) — dispositions no modeled operation can consult -/

/-! WHY THIS IS SOUND, AND WHAT WOULD BREAK IT.

    The model has no signal delivery.  [Run.sstep] has no asynchronous
    transition, [State.event] has no signal constructor, and
    [State.Model] carries no disposition, mask or pending queue.  What it
    does have is [RiscvSemantics.MachineFault], which [Run.unmodeled_at]
    deliberately EXCLUDES from the coverage predicate on the grounds that
    "a real Linux process dies there too".  That justification is a claim
    about DISPOSITIONS: it holds only while no handler is installed for
    the signal the fault stands for.

    So a spec that lets [rt_sigaction] SUCCEED for a fault signal
    falsifies it, and the damage is not local.  A source could install a
    SIGSEGV handler, fault deliberately, and reach [Run.SError] on every
    execution; [Equivalence.bh_all_errors] would hold, the escape in
    [Equivalence.equiv] would admit an ARBITRARY target, and
    [Equivalence.modeled] would still be satisfied, because a fault is
    not [unmodeled].  The theorem would be true and say nothing, and
    nothing would notice.  On real Linux the handler runs and the
    process keeps going.

    This spec closes that by construction rather than by bookkeeping.
    Nothing is recorded, and the accepted set is chosen so that nothing
    NEEDS to be.  What that takes is two things, and only one of them is
    the list below.

    WHAT SOUNDNESS ACTUALLY REQUIRES.  A no-op install is sound only if
    REALITY CANNOT RAISE THE SIGNAL AT ALL — not merely if no MODELED
    OPERATION can raise it.  Those are different conditions and the gap
    between them is exactly the accepted set: SIGINT and SIGTERM arrive
    only from outside the process, so both pass the operational test
    while reality could still deliver either.  If reality did, this spec
    would be wrong about a signal it ACCEPTS.  [State.event] is [ReadEv]/[WriteEv]/[ExitEv] only and
    the accepting arm is [ret_only 0], recording neither an event nor
    model state, so a source calling [sigaction(SIGTERM, &h, NULL, 8)]
    and a target that never calls [rt_sigaction] AT ALL have identical
    [Equivalence.bh_traces], both satisfy [Equivalence.modeled], and
    [Equivalence.strong_equiv] holds — while under a real SIGTERM the
    source runs [h] and continues and the target dies.

    THE OTHER HALF IS A PREMISE OF THE THEOREM, NOT A DERIVED FACT: THE
    ENVIRONMENT THE THEOREM QUANTIFIES OVER DELIVERS NO SIGNALS.
    [State.ProcInput] quantifies argv, envp, the file system and stdin
    and quantifies no signal source, and [Run.sstep] has no transition a
    signal could arrive on — so the premise is not stated as a hypothesis
    anywhere; it is built into the shape of the state machine, which is
    why it has to be written down in prose.  Without this spec it would be
    HARMLESS: if 134 fell through to [unmodeled], every covered
    binary would carry its inherited dispositions unchanged, and
    two such binaries would react identically to any outside signal whether
    the premise held or not.  Accepting an install is what
    makes the premise LOAD-BEARING.

    That tension is visible elsewhere in the model:
    [Random.getrandom_errnos] is [[EINTR]], justified there by a signal
    arriving while blocked on a large request — and an OBSERVABLE -EINTR
    requires a CAUGHT signal whose disposition lacks SA_RESTART, which is
    precisely what an accepted install here may be.  The two coexist
    only under the premise above.

    THE LIST BELOW IS THE OPERATIONAL HALF, AND IT IS NOT THE WHOLE
    ARGUMENT.  Read it as a necessary condition rather than a sufficient
    one: a disposition is accepted only for a signal that no modeled
    operation — machine step or syscall — can cause REALITY to raise.
    That test is about reality, not about the model: it is not enough
    that the model never raises the signal, because the model's silence
    is exactly what would be wrong.  A future reader widening the set is
    the person this warning is for — passing this test is not on its own
    grounds to add a signal, because a signal reality can deliver from
    outside still needs the premise, and the premise is only as good as
    the environments the theorem is applied to.

    Excluded, and the operation that excludes each — except the last,
    which is excluded ahead of the operation rather than by it:

      - SIGSEGV (11), SIGBUS (7), SIGILL (4), SIGTRAP (5) — every
        [MachineFault] site in [RiscvSemantics]: [EEbreak], the
        misaligned-atomic [EFault] and the defined-illegal
        [Sem.EDefinedIllegal] in [interp_eff], [ELoad]/[EStore]
        outside the view, [DecodeC.is_defined_illegal] in [decode_exec],
        and the odd-pc / unmapped / non-executable arms of
        [fetch_failure].
      - SIGPIPE (13) — a modeled [write].  [ReadWrite.write_spec]
        classifies fds 1 and 2 as [FdChannel] without knowing whether the
        far end is a pipe, so a real channel with a closed reader raises
        SIGPIPE at a call the model answers.  The model has no EPIPE arm
        and assumes a live reader; that assumption is what makes
        SIGPIPE's disposition unobservable HERE, which is not the same as
        unraisable, so it stays out.
      - SIGXFSZ (25) — a modeled [write], and a modeled [ftruncate] as
        well: neither [ReadWrite.write_spec] nor [Open.ftruncate_spec]
        consults RLIMIT_FSIZE, where Linux raises SIGXFSZ alongside
        -EFBIG (the write path's [generic_write_check_limits],
        fs/read_write.c, when the position is already at or past the
        limit; [inode_newsize_ok], fs/attr.c, for a truncate).  Both
        skip that arm on exactly RLIM_INFINITY, which is a premise of
        the run rather than of the model: both calls that could lower it
        fail closed — prlimit64 because [Kernel.Sys.prlimit64_spec]
        covers RLIMIT_CORE and nothing else, setrlimit (164) because it
        has no arm.  The model itself cannot observe the limit that
        decides this, let alone rule it out.
      - SIGCHLD (17) — a child's exit.
        [Kernel.Fork.clone_resolve] has a succeeding arm, so a modeled
        syscall can make a child; the paragraph after the accepted
        list says more.

    Accepted: SIGINT (2), SIGTERM (15).  Both arrive only from outside
    the process, and nothing modeled sends a signal — [kill] (129) and
    [tgkill] (131) are both outside [modeled_sysnos], so a process
    cannot even signal itself.  [rt_sigprocmask] (135) IS modeled and
    does not disturb that: a mask decides DELIVERY, not sending, and
    what the premise below rules out is a signal arriving at all.

    SIGCHLD (17) IS NOT ACCEPTED, AND THAT IS THE INVARIANT BELOW
    BEING DISCHARGED.  That invariant says the
    change which GIVES THE MODEL A CHILD must take SIGCHLD out of this
    set.  A modeled [clone]/[clone3] parent side is
    that change — it is an admission that a child can exist — and so
    would be a modeled [wait4], which is an admission that one can be
    reaped.  An accepted set NARROWER than the operational test demands
    costs coverage and cannot cost soundness.

    What it costs is one install the model
    declines: [sigaction(SIGCHLD, &act, NULL, 8)], the shape dropbear
    uses to reap its children.  A decline is not a wrong answer — it puts
    such a program outside the theorem's coverage rather than making a
    false claim about it.

    WHAT THE OPERATIONAL RULE NEVER ESTABLISHED IS THAT REALITY HAS NO
    SENDER.  This model begins AT [execve]: [State.ProcInput] carries
    argv, envp, the file system and stdin and nothing about the process
    that launched this one, so a source the theorem covers may already
    have a child, a parent or a terminal.  SIGINT and SIGTERM are in the
    accepted set on the strength of the PREMISE above — the environment
    delivers no signals — and not on the strength of the operational
    rule, which only narrows who could send it: "arrives only from
    outside the process" says the model cannot raise it, not that it is
    never raised.  That gap matters most for SIGCHLD, since
    a child survives [execve] and could raise a real one at any moment;
    the decline closes that instance rather than leaving it to the
    premise, and SIGINT and SIGTERM still need the premise in full.

    THE INVARIANT TO KEEP: this list is a claim about the REST of the
    model.  If a later change gives [ReadWrite.write_spec] an EPIPE arm,
    or gives the model a timer, a controlling terminal, or any
    [kill]-shaped syscall, the corresponding signal must leave
    [sigaction_accepted] in the SAME commit — or better, in a commit
    AHEAD of it, so that no ordering of the
    two can open the window.  Adding delivery of any kind reopens the
    hole above outright.  And the premise is an invariant too: giving
    [State.ProcInput] a signal source, or [Run.sstep] a transition to
    deliver on, invalidates the accepted set WITHOUT touching a single
    modeled operation, so the operational list is not where such a change
    would announce itself. -/
/-- The signal number is [int] ([SYSCALL_DEFINE4(rt_sigaction, int, sig,
    ...)], Linux v6.10-v6.15, kernel/signal.c, byte-identical across the
    window), so the kernel sees only the low half of the register — the
    same ABI truncation [fd32], [cmd32] and [whence32] apply, at the same
    boundary, in the arm that reads this syscall's arguments. -/
def sig32 (sig : word) : word := Syscall.abi_low32 sig

/-- The signals whose disposition no modeled operation can consult AND
    which the theorem's signal-free environment therefore never delivers.
    BOTH halves are load-bearing, and the second is a premise rather than
    a fact about [rt_sigaction]: read the note above before touching this
    list.  Every other signal — the four fault signals above all, and
    SIGCHLD, because the model can have a child —
    fails closed at an install. -/
def sigaction_accepted (sig : word) : Bool :=
  let s := (sig.toNat : Int)
  s == 2 || s == 15

/-- [do_sigaction] rejects a signal outside 1..[_NSIG]: [valid_signal]
    widens the [int] to [unsigned long], so a negative one becomes a huge
    value and fails the [sig <= _NSIG] bound, and an explicit [sig < 1]
    catches 0.  [_NSIG] is 64 on riscv64 (include/uapi/asm-generic/signal.h),
    which is what this model needs — it is not universal, mips defines
    128 — and the bound is INCLUSIVE: 64 is a valid signal, 65 is
    -EINVAL.  Applied to the
    already-truncated low half, an unsigned 1..64 test is exactly that
    predicate.  Note [rt_sigaction] differs from [kill] here: [kill]
    accepts signal 0 as a permission probe — [group_send_sig_info] runs
    the permission check and then skips delivery under [if (!ret && sig)]
    — while [rt_sigaction]'s [sig < 1] refuses it. -/
def sig_valid (sig : word) : Bool :=
  let s := (sig.toNat : Int)
  decide (1 ≤ s ∧ s ≤ 64)

/-- [sig_kernel_only] (include/linux/signal.h): SIGKILL and SIGSTOP can
    be neither caught nor ignored, so [do_sigaction] answers -EINVAL for
    them — but only when [act] is non-NULL.  With nothing to install the
    same call is a plain 0. -/
def sig_kernel_only (sig : word) : Bool :=
  let s := (sig.toNat : Int)
  s == 9 || s == 19

/-- The [sa_flags] bits whose entire meaning is HOW a signal reaches a
    handler, or how a child's stop is reported.  Neither can happen, so
    an install carrying them is still a no-op:

      SA_NOCLDSTOP      0x00000001   SA_NOCLDWAIT 0x00000002
      SA_SIGINFO        0x00000004   SA_EXPOSE_TAGBITS 0x00000800
      SA_ONSTACK        0x08000000   SA_NODEFER   0x40000000
      SA_RESETHAND      0x80000000

    That is [UAPI_SA_FLAGS] (include/linux/signal_types.h), which is
    0xD8000807, minus SA_RESTART, on an architecture whose
    [__ARCH_UAPI_SA_FLAGS] is 0: riscv defines no SA_RESTORER, so it has
    neither that flag nor an [sa_restorer] field.

    SA_RESETHAND is accepted here but IS NOT REACHABLE THROUGH MUSL, so
    do not read its presence as coverage of a musl caller.  musl's
    [struct sigaction] declares [sa_flags] as an [int] (include/signal.h)
    and [__libc_sigaction] (src/signal/sigaction.c) assigns it straight
    into the [unsigned long] flags of [struct k_sigaction] —
    [ksa.flags = sa->sa_flags] — so the bit-31 value SIGN-EXTENDS and
    the kernel is handed 0xFFFFFFFF80000000.

    THE MUSL WINDOW IS v1.2.4-v1.2.6, and it is a bound rather than a
    formality.  Before v1.2.4, arch/riscv64/bits/signal.h defined
    SA_RESTORER as 0x04000000 and musl OR'd it into every [sigaction]
    call; that bit is outside [UAPI_SA_FLAGS], so [sa_flags_ok] would
    decline EVERY musl sigaction on those versions — a plain
    [sigaction(SIGTERM, &act, NULL)] — the modeled shape — included.
    musl commit 269d1938 (2023-02-09, "fix wrong sigaction syscall ABI
    on mips*, or1k, microblaze, riscv64") deleted the define, and v1.2.4
    is the first release carrying it.  src/signal/sigaction.c is identical
    at v1.2.4, v1.2.5 and v1.2.6.
    Linux answers 0 to that ([sa_flags &= UAPI_SA_FLAGS] drops bits
    32-63, leaving exactly SA_RESETHAND), while this spec sees those bits
    and fails closed, which is the SAFE direction: a decline where the
    kernel gives an answer.  The flag is therefore reachable only from a
    raw [syscall(SYS_rt_sigaction, ...)].

    Deliberately NOT here, each for its own reason:

      - SA_RESTART 0x10000000 is the one retained flag that changes a
        SYSCALL's return value rather than a delivery — it asks for an
        interrupted call to be restarted instead of returning -EINTR —
        and the model HAS a syscall that can return -EINTR:
        [Random.getrandom_errnos], whose short-delivery arm is justified
        by a signal arriving mid-request.  The model has no notion of
        restart, so SA_RESTART is unmodeled: fail closed.
      - every bit outside [UAPI_SA_FLAGS].  [do_sigaction] silently MASKS
        those away ([act->sa.sa_flags &= UAPI_SA_FLAGS]) rather than
        rejecting them, so answering 0 WOULD be sound — and not only
        today: [UAPI_SA_FLAGS] arrived in v5.11 already containing
        SA_EXPOSE_TAGBITS, together with the masking line, and its body
        is byte-identical from v5.11 to v6.17.  So this is NOT an
        argument about a moving constant.  The model declines anyway,
        because fail-closed is the default for a shape nothing needs:
        no real caller sets a bit outside the mask, so nothing is lost
        by not deciding what Linux does with it, and deciding would put
        a kernel constant the model otherwise never consults inside the
        modeled surface.

    musl's [signal()] wrapper sets SA_RESTART and passes a non-NULL
    [oldact], so it fails closed here twice over.  A direct
    [sigaction(sig, &act, NULL)] is the shape that is modeled, for a
    signal in [sigaction_accepted].  dropbear's install has that shape
    and names SIGCHLD, so it fails closed on the SIGNAL instead. -/
def sa_flags_accepted : Int := 0xC8000807

/-- [sa_flags_ok]: every bit of [fl] lies inside [sa_flags_accepted].
    This is the `x &&& m = x` containment test on the unsigned reading, in
    `Nat`, where both operands live; the header records why it replaces a
    `Z` bit-difference test. -/
def sa_flags_ok (fl : word) : Bool :=
  decide (fl.toNat &&& sa_flags_accepted.toNat = fl.toNat)

/-- The kernel's [struct sigaction] on riscv64 is [sa_handler](8) at 0,
    [sa_flags](8) at 8, [sa_mask](8) at 16 — 24 bytes, with NO
    [sa_restorer] field.  The struct the kernel compiles is the one in
    include/linux/signal_types.h (the [struct sigaction] in
    include/uapi/asm-generic/signal.h sits under [#ifndef __KERNEL__] and
    is not it), and its [sa_restorer] member is guarded by
    __ARCH_HAS_SA_RESTORER, which include/uapi/asm-generic/signal.h
    defines only under a SA_RESTORER that asm-generic never defines.
    riscv ships neither an [asm/signal.h] nor a [uapi/asm/signal.h] of
    its own, so it defines no SA_RESTORER, and both the field and
    [__ARCH_UAPI_SA_FLAGS] vanish.

    The size is load-bearing rather than incidental — musl's own
    [struct k_sigaction] for this architecture is 32 bytes, so a spec
    that read 32 would answer -EFAULT where Linux answers 0.  The extra 8
    bytes are TRAILING SLACK ONLY FROM musl v1.2.4.  Before that the 32
    bytes were handler, flags, [sa_restorer], mask, and the kernel read
    the restorer pointer at offset 16 as [sa_mask] — the very bug musl
    269d1938 fixed.  The -EFAULT argument survives either way, since
    32 >= 24; the characterisation does not, so it is bounded to the
    window the rest of this note uses.

    [SYSCALL_DEFINE4(rt_sigaction)] copies the whole struct with one
    [copy_from_user] before [do_sigaction] runs, so readability is
    all-or-nothing and -EFAULT precedes every -EINVAL [do_sigaction]
    would raise.  It does NOT precede the [sigsetsize] -EINVAL, which the
    syscall entry raises before the copy — arm 1 below — and the [oact]
    [copy_to_user] runs after [do_sigaction], so a bad [oact] with a bad
    [sig] is -EINVAL rather than -EFAULT.  This returns [sa_flags]
    exactly when all 24 bytes are readable.

    NO [State.access_okb] GUARD, and that is not an omission.  The
    delivering syscalls need one because they answer for ranges they do
    not require to be mapped; here all 24 bytes must be mapped before
    anything is answered, and a mapping cannot sit above the address
    space it was made in — so a readable range is below [TASK_SIZE],
    which is the limit [__access_ok] tests (include/asm-generic/access_ok.h;
    riscv overrides [access_ok] for pointer masking but not
    [__access_ok]; see [State.TASK_SIZE]).
    The word addition in [readable_bytes] cannot manufacture one either:
    wrapping needs [act] within 24 bytes of 2^64, and no model state has
    a mapping there ([alloc_top] and [sp_window_hi] both sit at or
    below 2^47 for any [Run.valid_sp]), so the walk stops on its first unmapped byte and the
    answer is -EFAULT.

    The flags word is the only field the model consults.  The handler
    (SIG_DFL, SIG_IGN or an address) and [sa_mask] describe delivery,
    which cannot occur, so their values change nothing — and for the same
    reason the kernel's two silent side effects here are unobservable:
    [sigdelsetmask] clearing SIGKILL and SIGSTOP from the stored mask,
    and the POSIX 3.3.1.3 flush of pending signals ([sig_handler_ignored]
    then [flush_sigqueue_mask]) when the new disposition ignores them.
    The model has neither a stored mask nor a pending queue, and [oact] —
    declined below — is the only window onto either. -/
def sigaction_flags (mp : word → Option byte) (act : word) : Option word :=
  if (readable_bytes mp act (BitVec.ofInt 64 24)).length == 24
  then read_u64 mp (act + BitVec.ofInt 64 8)
  else none

/-- [rt_sigaction sig act oact sigsetsize].  [sig] arrives already
    truncated (see [sig32]).  The arms follow the kernel's own order
    (Linux v6.10-v6.15, kernel/signal.c, [SYSCALL_DEFINE4(rt_sigaction)]
    then [do_sigaction]).  The syscall body is byte-identical across that
    window.  [do_sigaction] changes TWICE in it, both in v6.13, and
    neither moves an answer here: the [posixtimer_sig_unignore] path is
    reachable only through POSIX timers, which are not modeled, and
    [flush_sigqueue_mask] gains a task argument and frees through
    [sigqueue_free_ignored], which diverges from [__sigqueue_free] only
    for preallocated POSIX-timer sigqueue entries.

    NO STABLE-BRANCH EXCLUSIONS.  Both functions are byte-identical
    between each mainline tag and the head of its stable branch across
    linux-6.10.y through linux-6.15.y, and no backport crosses the
    window.  Stated because other windows in this model do have such
    exclusions, so silence here would be ambiguous.

    The arms:

      1. [sigsetsize != sizeof(sigset_t)] is -EINVAL before anything else
         is looked at, and [sizeof(sigset_t)] is 8 on a 64-bit kernel
         ([_NSIG] 64 over a 64-bit [_NSIG_BPW], one word).  So a bad size
         beats a wild [act] pointer.
      2. a non-NULL [oact] is UNMODELED.  The kernel writes the PREVIOUS
         disposition there, and the model stores none — nor could it
         honestly answer from a fixed initial state, since [execve]'s
         [flush_signal_handlers] preserves an inherited SIG_IGN, making
         the initial disposition a choice of the launching environment
         rather than a constant.  [State.ProcInput] quantifies argv,
         envp, the file system and stdin; it does not quantify that.
         Declining is the only sound arm, and it also removes the
         kernel's nastiest corner here: a [copy_to_user] fault on [oact]
         returns -EFAULT with the new disposition ALREADY installed and
         not rolled back.
      3. with [act] NULL nothing is installed, so the call is a pure
         no-op for EVERY valid signal, fault signals included: 0, or
         -EINVAL outside 1..64.  This is also why SIGKILL and SIGSTOP are
         only rejected in arm 4.
      4. with [act] non-NULL: -EFAULT unless all 24 bytes are readable;
         then -EINVAL for an out-of-range signal and for SIGKILL/SIGSTOP;
         then fail closed on SA_RESTART and on any bit outside
         [sa_flags_accepted]; then 0 for a signal in
         [sigaction_accepted], recording nothing, and UNMODELED for every
         other signal.

    Arm 4's last case is the one that matters: it is what keeps a
    SIGSEGV, SIGILL, SIGBUS or SIGTRAP handler out of the modeled
    surface, and with it the [MachineFault] vacuity described above.

    One -EINVAL the model does not reproduce: [do_sigaction] also
    refuses when the EXISTING action carries SA_IMMUTABLE.  That bit is
    set only by [force_sig_info_to_task] under HANDLER_EXIT — a path
    that terminates the process — so no surviving process can present it,
    and a fresh process starts with every FLAG WORD zero, which is the
    half this argument needs.  Not every disposition: [execve]'s
    [flush_signal_handlers] (called as [flush_signal_handlers(me, 0)]
    from [begin_new_exec], fs/exec.c) resets caught handlers to SIG_DFL
    but PRESERVES an inherited SIG_IGN, which is exactly why the [oact]
    arm above declines rather than answering from a fixed initial
    state. -/
def rt_sigaction_spec (sig act oact ss : word) : SysSpec SyscallEffect :=
  if !(ss == BitVec.ofInt 64 8) then err_ret EINVAL
  else if !(w_is0 oact) then unmodeled
  else if w_is0 act then
    (if sig_valid sig then ret_only (BitVec.ofInt 64 0) else err_ret EINVAL)
  else
    bind inputSpec fun i =>
      match sigaction_flags i.in_mem act with
      | none => err_ret EFAULT   -- the struct is not wholly readable: real -EFAULT
      | some fl =>
          if !(sig_valid sig) then err_ret EINVAL
          else if sig_kernel_only sig then err_ret EINVAL
          else if !(sa_flags_ok fl) then unmodeled
          else if sigaction_accepted sig then ret_only (BitVec.ofInt 64 0)
          else unmodeled         -- a signal a modeled operation can raise: fail closed

/-! ## rt_sigprocmask (135) - a mask no modeled operation can observe -/

/-! WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name rather than by line number.  Every function
    named here is BYTE-IDENTICAL across v6.1 - v6.17:

      kernel/signal.c         [SYSCALL_DEFINE4(rt_sigprocmask, ...)],
                              [sigprocmask], [__set_current_blocked],
                              [__set_task_blocked]
      include/linux/signal.h  [sigdelsetmask]

    NO STABLE-BRANCH EXCLUSIONS, and that is CHECKED rather than
    assumed: all five are byte-identical at the heads of linux-6.1.y,
    linux-6.6.y, linux-6.12.y and linux-6.17.y as well as at the release
    tags.

    The constants are in [Uapi.v] with their own citations: [SIG_BLOCK],
    [SIG_UNBLOCK], [SIG_SETMASK] and [NSIG_BYTES], the last of which is
    why this call reads exactly eight bytes.

    THE MASK IS STATE, AND ITS INITIAL VALUE IS AN INPUT.

    [State.ProcState] carries [procst_sigmask], and it has to, because
    this spec answers [oset]: the kernel writes the mask the process had
    ON ENTRY there, and a spec that invented a value would be inventing
    the one thing the call exists to report.

    WHERE THE ENTRY VALUE COMES FROM IS THE WHOLE DIFFICULTY, and the
    answer is that the model cannot derive it — so it does not.  Unlike
    a disposition the mask is not even partly reset at [execve]:
    [begin_new_exec] (fs/exec.c) calls [flush_signal_handlers], which
    walks [sighand->action] and touches [current->blocked] nowhere, and
    fs/exec.c does not mention [blocked] at all.  The starting mask is
    entirely a choice of the launching environment, so it arrives the
    way every other such choice does — as a field of
    [State.ProcInput], [in_sigmask], quantified once in
    [Equivalence.strong_universal_T] and SHARED between source and
    target.  That sharing is what keeps the equivalence intact: both
    binaries read the same entry mask back, so a read-back cannot
    separate two programs the relation should call equal.

    [Run.valid_sigmask] is the one constraint on it — SIGKILL and
    SIGSTOP clear — and the argument for it is an enumeration of the
    kernel's writers, not the one-liner it looks like; see that
    definition, which also says why the enumeration is the fragile
    kind.

    WHAT THE MASK IS STILL NOT: OBSERVABLE IN THE TRACE.  [State.event]
    is [ReadEv] / [WriteEv] / [ExitEv] only and [Run.sstep] has no
    asynchronous transition, so the mask reaches a trace exactly one
    way — through the eight bytes this call copies to [oset], like any
    other syscall's answer.  It adds nothing to the trace alphabet.

    QUANTIFY THAT OVER THE SPECS, NOT OVER THE SYSCALL NUMBERS.  The
    claim "no modeled syscall sends a
    signal" is FALSE, and falsely in the direction that matters:
    three numbers in [Sys.SyscallTable.spec_table] name kernel paths
    that really do send one.  [write] (64) and [writev] (66) reach
    [anon_pipe_write] (fs/pipe.c:431, v6.18.46), whose two
    [send_sig(SIGPIPE, current, 0)] calls (:462, :503) answer a pipe with
    no reader, and both also reach
    [generic_write_check_limits] (fs/read_write.c), which sends SIGXFSZ
    past RLIMIT_FSIZE; [ftruncate] (46) reaches [inode_newsize_ok]
    (fs/attr.c), which sends SIGXFSZ on the same limit before returning
    -EFBIG.  What is true is the weaker and sufficient claim: NO SPEC IN
    THIS MODEL RAISES A SIGNAL, because [write_spec] assumes a live
    reader and neither it nor [ftruncate_spec] carries a file-size
    limit.  The live reader is an assumption nothing checks.  The
    RLIMIT_FSIZE half of the limit is a premise of the run —
    RLIM_INFINITY at exec, and the set fails closed, see
    [Open.ftruncate_spec] — and the [s_maxbytes] half, which the model
    does not carry either, raises no signal:
    [inode_newsize_ok]'s [out_big] and [generic_write_check_limits]'s
    [s_maxbytes] arm both return -EFBIG without a [send_sig].

    That distinction is not pedantry, because this spec WIDENS what
    those assumptions cost.  Blocking SIGXFSZ succeeds here and is
    RECORDED, and the model still gives one answer to two source
    programs whose real behaviour at the next over-limit [ftruncate]
    differs:
    unblocked the process dies on the signal, blocked it takes -EFBIG
    and runs on.  Under the RLIM_INFINITY premise no run reaches
    that ftruncate, but the model does not carry the premise.  So this
    file adds no wrong answer — the missing limit owns it, with or
    without this file — but it is a pair the
    equivalence relation cannot separate.  The obligation the invariant below states
    therefore binds those three specs too: an -EPIPE arm in
    [ReadWrite.write_spec], or a file-size limit in [ftruncate_spec],
    turns a blocked mask into something the model reads, and must give
    this spec state in the same commit.

    With that stated, [oset] is the ONLY window onto the mask that is
    open, and this spec is the only thing that writes one.  The list
    below is what stays shut, and it is worth keeping precisely because
    the mask is real: each of these, on landing, has to move
    [procst_sigmask] rather than merely answer, and the value [oset]
    hands back goes stale the moment one of them does not.

      - EVERY SYSCALL THAT READS [->blocked], INSTALLS A MASK, OR
        CAN DELIVER OR SEND A SIGNAL — the three above excepted, since
        their SPECS raise nothing — is outside [Specs.modeled_sysnos]
        entirely, so the dispatcher declines it before any of this is
        reached.  That is the claim; the numbers are examples of it, not
        the claim itself — [rt_sigsuspend] (133),
        [rt_sigpending] (136), [rt_sigtimedwait]
        (137), [rt_sigreturn] (139), [ptrace] (117), whose
        PTRACE_GETSIGMASK / PTRACE_SETSIGMASK read and write [->blocked]
        outright,
        [epoll_pwait2] (441), [io_pgetevents] (292) and
        [io_uring_enter] (426), which really do install a temporary
        [->blocked] — [set_user_sigmask] on the way in and
        [restore_saved_sigmask_unless] on the way out, in fs/select.c,
        fs/eventpoll.c, fs/aio.c and io_uring/io_uring.c.
        [set_user_sigmask] both READS the mask (it saves
        [current->blocked] into [current->saved_sigmask]) and installs
        one, so each is a read-back window and not merely a writer.
        [pselect6] (72), [ppoll] (73) and [epoll_pwait] (22) belong to
        that family and are handled in the bullet below instead, because
        they have arms.
        Then [signalfd4] (74), which does NOT:
        [do_signalfd4] (fs/signalfd.c) stores the set in the fd's own
        [ctx->sigmask], and fs/signalfd.c does not name [blocked]
        anywhere.  It is on this list as a DELIVERY window instead,
        because [signalfd_dequeue] calls [dequeue_signal] against that
        [ctx->sigmask], so a read of the fd hands back exactly the
        signals a blocked mask left pending.  Sampled at v6.1, v6.6,
        v6.12 and v6.17, not diffed across the whole window:
        [do_signalfd4] is NOT identical over those four — the fd lookup
        and the anon-inode call both changed — but the two statements
        this rests on are, with only [dequeue_signal]'s leading
        [current] argument dropped at v6.12.  Then [kill] (129),
        [tgkill] (131), [rt_sigqueueinfo] (138), [rt_tgsigqueueinfo] (240) and
        [pidfd_send_signal] (424), so a process cannot even signal
        itself.  Checked against [Sys.SyscallTable.spec_table]: none of
        them has an arm.
      - [rt_sigaction] (134), [pselect6] (72), [ppoll] (73),
        [epoll_pwait] (22) and [sigaltstack] (132) ARE on the modeled
        surface, and their windows are shut one level down instead.
        132 is the easy one, and is called out separately so the others
        are not read as the pattern: it has NO window to shut.
        [do_sigaltstack] (kernel/signal.c) reads and writes
        [sas_ss_sp], [sas_ss_size] and [sas_ss_flags] and names
        [blocked] nowhere, and [SYSCALL_DEFINE2(sigaltstack)] calls no
        [set_user_sigmask]; it is listed here only because it sits in
        this file's kernel source, which is not the same thing.  Checked
        by [sigaltstack_leaves_the_mask_alone] in
        `Checks/Cases/Kernel/Signal.lean` rather than by absence, so the
        reading below has a witness beside it.
        134's is [oact], the only way to read an [sa_mask] back, and
        [rt_sigaction_spec] declines a non-NULL [oact] outright; the
        [sa_mask] an accepted install carries is not stored either —
        that spec answers [ret_only 0] and records nothing — so there is
        no second window behind the first.  72's is [set_user_sigmask]
        itself, and it is a real read-back: it saves [current->blocked]
        into [current->saved_sigmask] on the way in.  [Fs.Select]'s
        [pselect_sigpack] classifies a call that would install a mask as
        [PsSigReal] and [pselect6_outcome] answers [None] for it, and
        the error arms decided ahead of that are decided before
        [set_user_sigmask] runs in the kernel too, so no admitted
        pselect6 installs a mask.  22's window is the SAME
        [set_user_sigmask], reached from [do_epoll_pwait]
        (fs/eventpoll.c) rather than from [do_pselect], and
        [Fs.EventPoll]'s [epoll_sigmask] classifies a call that would
        install a mask as [EpSigReal], for which [epoll_pwait_outcome]
        answers [None].  Its error arms are decided ahead of that in the
        same sense: [set_user_sigmask] is the FIRST fallible step of
        [do_epoll_pwait], so the only errnos this model admits before it
        are the two that function itself returns, -EINVAL on a wrong
        [sigsetsize] and -EFAULT on an unreadable mask, neither of which
        installs anything.  73's is that same [set_user_sigmask] a third
        time, reached from [SYSCALL_DEFINE5(ppoll, ...)] with the mask
        pointer and its size as two arguments rather than through an
        argpack; [Fs.Select]'s [ppoll_sigmask] classifies an install as
        [PpSigReal] and [ppoll_outcome] answers [None] for it, and the
        only errnos admitted ahead of that are the timeout's, which the
        kernel raises before [set_user_sigmask] runs.  Every
        number on this bullet is checked rather than asserted, by
        [rt_sigaction_oact_read_back_declined],
        [pselect6_real_mask_declined],
        [epoll_pwait_real_mask_declined],
        [ppoll_real_mask_declined] and
        [sigaltstack_leaves_the_mask_alone] — all five in
        `Checks/Cases/Kernel/Signal.lean`.
        Do not move any of these
        numbers back into the bullet above, where the check is absence
        from [spec_table] and every one of them would fail it.  There is
        no count here on purpose: a written total is what goes stale
        when the bullet grows.
      - [clone] (220) and [clone3] (435) are deliberately NOT on that
        list, because their window is not closed by the same fact and
        stating it that way would rot.  A child inherits the mask, so an
        arm for either WOULD be a read-back window — if the child ran.
        It never does: [Run.sstep] has no transition that starts a
        second task, and a parent-side arm for these numbers does not
        add one, so there is no child to read the mask back whether or
        not 220 and 435 have an arm.  Do not derive this one from
        [spec_table]: both numbers have arms there, and the argument
        does not depend on them.

    So this spec is the sole reader and the sole writer of the mask it
    keeps, which is what makes a single field enough.

    WHY THERE IS NO ACCEPTED-SIGNAL LIST.  This is the question to ask
    of a spec that answers every mask, because the obvious worry is a
    program that blocks SIGSEGV and then executes a wild jump: if
    blocking made the fault survivable, [Run.unmodeled_at]'s exclusion
    of [RiscvSemantics.MachineFault] — which rests on a real process
    dying there too — would be wrong, and this spec would have to
    refuse the mask.

    BLOCKING CANNOT DO THAT.  A synchronous fault is delivered by
    [force_sig_info_to_task] (kernel/signal.c), which reads
    [blocked = sigismember(&t->blocked, sig)] and, when the signal is
    blocked, resets the disposition — [action->sa.sa_handler = SIG_DFL]
    — and removes the signal from the mask — [sigdelset(&t->blocked,
    sig)] — BEFORE calling [send_signal_locked].  A process that blocks
    SIGSEGV and then faults dies exactly as one that never blocked it.
    Those three statements are byte-identical across the whole
    v6.1 - v6.17 window even though the enclosing function is not:
    v6.8 deleted [recalc_sigpending_and_wake] and moved the wake-up out
    of the [if (blocked)] arm into a [task_sigpending] test after
    [send_signal_locked] (commit b454ec29225cda, "kernel/signal.c:
    simplify force_sig_info_to_task(), kill
    recalc_sigpending_and_wake()"), changing nothing any of the three
    does.

    THE PREMISE THIS SHARES WITH THE THEOREM: THE ENVIRONMENT DELIVERS
    NO SIGNALS.  Because this spec answers [oset], the premise costs
    an ANSWER and not only coverage: Linux has two writers of [->blocked] that no
    program calls, [signal_delivered] (kernel/signal.c), which ORs in
    [sa_mask] and adds the signal itself unless SA_NODEFER before
    [set_current_blocked], and riscv's [SYSCALL_DEFINE0(rt_sigreturn)]
    (arch/riscv/kernel/signal.c), which restores the mask from the
    sigframe.  Under a delivered signal the value this spec copies to
    [oset] would be the wrong number, not merely an unmodeled
    distinction.  The premise is written down above [Run.unmodeled_at].

    One tension this neither creates nor closes: [getrandom_errnos] is
    [[EINTR]], and a program that blocks every signal makes that errno
    unreachable in reality while the model still admits it.  Same
    premise, seen from the other side.

    THE INVARIANT TO KEEP.  It is a property rather than a list
    because a list only catches what someone thought to write down:
    THE MOMENT A SECOND READER OR WRITER OF THE MASK LANDS, IT MUST
    MOVE [procst_sigmask] IN THE SAME COMMIT — because this spec
    commits to a VALUE, and a writer that does not update the field
    makes that value silently wrong rather than merely incomplete.
    Signal delivery of any kind is the obvious one.  So is any of the
    numbers enumerated above, and so is relaxing [Fs.Select]'s
    [PsSigReal] decline, which is the only such window inside
    [Specs.modeled_sysnos] today.  The one that would not announce
    itself is an -EPIPE arm in [ReadWrite.write_spec]: SIGPIPE blocked
    turns a write to a channel with a closed reader from process death
    into a return of -EPIPE, which is a mask READ at a call this model
    already answers.  WHAT KEEPS THAT SHUT: the model has real pipes
    ([Fs.Pipe]), so it HAS
    a notion of a live reader, and a pipe whose reader is gone is [unmodeled] —
    [ReadWrite.write_spec]'s [pipe_end_live] arm — because SIGPIPE's
    default disposition terminates the process and this model has no
    death that is not [exit].  So the -EPIPE arm is held off by a
    DECLINE, not by an absence, which is the stronger of the two;
    the live-reader assumption holds only for [FdChannel], where the model
    cannot see whether the far end is closed. -/

/-- [how] is [int] ([SYSCALL_DEFINE4(rt_sigprocmask, int, how, ...)]),
    so the kernel sees only the low half of the register and
    [sigprocmask]'s [switch (how)] compares that half against
    [SIG_BLOCK], [SIG_UNBLOCK] and [SIG_SETMASK].  Signedness does not
    enter: the switch tests equality against three non-negative
    constants, so an unsigned reading of the truncated half decides them
    identically.

    The narrowing itself is [Syscall.how32], beside [fd32], [whence32]
    and [cmd32] — the dispatcher applies it, as it does for those. -/
def how_valid (how : word) : Bool :=
  let h := (how.toNat : Int)
  h == SIG_BLOCK || h == SIG_UNBLOCK || h == SIG_SETMASK

/-- [copy_from_user(&new_set, nset, sizeof(sigset_t))] is all-or-nothing
    at the syscall boundary: any shortfall is -EFAULT and nothing is
    installed.  [sizeof(sigset_t)] is [Uapi.NSIG_BYTES] = 8, so this is
    readability of eight bytes and no more.

    NO [State.access_okb] GUARD.  All eight bytes must be mapped
    before anything is answered, and a mapping cannot sit above the
    address space it was made in, so a wholly readable range is below
    [TASK_SIZE].  The word addition inside
    [State.read_bytes_map] cannot manufacture one either — but NAME THE
    RIGHT REASON, because the obvious one is incomplete.
    [State.alloc_top] and [State.sp_window_hi] bound the mmap, brk
    and stack sources and sit far below 2^64; they say nothing about
    the third source [in_mem] merges in, which is the ELF ROM image,
    whose [MemImageType.Segment] carries [seg_base] and [seg_size] as
    unbounded [N] with no side condition in the trusted tree.  What
    actually excludes a byte in the last page is
    [Equivalence.image_brk_satisfiable], a hypothesis of the IMAGE_WF
    module type each example's generated Checker ascribes — so
    completing a wrap would need two segments, one supplying the byte
    at 2^64-1 and one at 0, and that hypothesis forbids it.  Outside
    that ascription the specs quantify over an arbitrary
    [mp : word -> option byte], so this is a property of the
    well-formedness the equivalence theorem is stated under and not of
    the syscall layer.

    THE CONTENTS ARE READ: the value
    decides what gets installed, so the test and the read are one
    [option].  This helper lives in this file rather than in
    [Sys/Uaccess.v]: it is the [sigset_t] ABI shape, not a uaccess
    policy, and one syscall uses it. -/
def sigset_at (mp : word → Option byte) (p : word) : Option word :=
  match read_bytes_map mp p (BitVec.ofInt 64 NSIG_BYTES) with
  | some bs => some (le_bytes_to_word bs)
  | none => none

/-! [rt_sigprocmask how nset oset ss].  [how] arrives already truncated
    (see [Syscall.how32]).  The arms follow the kernel's own order
    ([SYSCALL_DEFINE4(rt_sigprocmask)] then [sigprocmask],
    kernel/signal.c, the window above):

      1. [sigsetsize != sizeof(sigset_t)] is -EINVAL before anything else
         is looked at — so a bad size BEATS A WILD [nset] POINTER, which
         is the pair a naive implementation gets backwards.  [sigsetsize]
         is [size_t] and is compared full-width: unlike [how] it does
         NOT truncate, so a register whose low half is 8 is still wrong.
      2. [old_set = current->blocked] is snapshotted HERE, before
         anything is installed, and it is this value — not the mask the
         call leaves behind — that [oset] receives.  The kernel takes it
         on the line after the size check and passes NULL as
         [sigprocmask]'s own [oldset], so the syscall never uses
         [sigprocmask]'s copy.  Reporting the post-install mask is the
         mistake a reimplementation makes, and
         [Checks.Cases.Kernel.Signal.rt_sigprocmask_oldset_is_not_the_new_mask]
         is what fails when someone makes it — it is proved here
         (`Checks/Cases/Kernel/Signal.lean`), so something DOES fail.
      3. with [nset] NULL nothing is installed — and, because
         [sigprocmask] is reached only from inside [if (nset)], [how] IS
         NEVER LOOKED AT.  An out-of-range [how] with a NULL [nset]
         therefore returns 0, not -EINVAL.  That is the ordering, not an
         oversight, and it is pinned by
         [Checks.Cases.Kernel.Signal], **which IS ported** as
         `Checks/Cases/Kernel/Signal.lean` — the notes's "not
         ported" note on it is stale — so the ordering is BOTH read off
         [rt_sigprocmask_spec]'s body AND pinned there.
         The call is
         not a no-op even so: arm 5 still runs, so a query WRITES.
      4. with [nset] non-NULL: -EFAULT unless all 8 bytes are readable,
         then SIGKILL and SIGSTOP are stripped from the new set
         ([sigmask_strip], silently — the call succeeds), then -EINVAL
         for a [how] outside {0, 1, 2}, then the install
         ([sigmask_apply]).
      5. with [oset] non-NULL the entry mask is copied out, LAST.  Two
         things follow that arms 1-4 do not prepare you for.  A bad
         [how] returns before this runs, so a rejected call leaves
         [oset] untouched.  And a fault HERE returns -EFAULT with the
         new mask already installed and NOT rolled back — the kernel's
         nastiest corner in this syscall, and the one obligation
         [Kernel.Sys.prlimit64_spec] avoids by declining both pointers
         at once.  This spec takes it on because here the install IS the
         call.  See [write_oset] for the three-way split of that arm and
         why the middle case declines.

    Every arm past the copy records the COPY-FROM-USER RANGE, and that is not
    bookkeeping: [Syscall.record_copyins] exists to distinguish two paths
    that return the same errno before and after a user-memory read, and
    this syscall has exactly such a pair — arm 1's -EINVAL is answered
    before [nset] is looked at, arm 4b's is answered after eight bytes
    have been copied.  An empty ledger on 4b would be a false claim that
    the call read no user memory, and [State.materialize_model_accesses]
    charges those ranges' lazy anonymous backing against
    [State.vm_limit], so omitting them also diverges from Linux at the
    allocation budget.  Arm 4a records nothing because the copy FAILED —
    the same convention as [Kernel.Sys.prlimit64_spec], whose -EFAULT
    arm is likewise outside its [record_copyins].  Say what that
    convention costs, since "the copy failed, so it read nothing" is not
    literally what the kernel does: with [nset] straddling a page
    boundary, riscv's [raw_copy_from_user] copies forward with exception
    fixups and really does fault in the first page before failing, so
    Linux charges it and this model does not.  The return value is
    -EFAULT either way; the divergence is one page of budget, in the
    under-charging direction [State.v] already names as the one that
    lets the model grant an allocation the kernel refuses, and it would
    show up at a later [mmap] or [brk], never here.  It is the
    established convention rather than anything this spec chose —
    [prlimit64_spec] and [Kernel.Time.Hrtimer.nanosleep_spec] have the
    same shape — so it is named here and not re-argued.

    Arm 4's success records the installed mask, so the two kernel
    side effects it touches part company.
    [sigdelsetmask]'s silent strip of SIGKILL and SIGSTOP IS modeled:
    the call still SUCCEEDS rather than answering -EINVAL — no
    [sig_kernel_only] test belongs in this spec, which is the opposite
    of [rt_sigaction] — but the stripped bits are observable at the
    next read-back, so dropping them is a wrong answer rather than an
    unobservable one.  [__set_task_blocked]'s [retarget_shared_pending]
    is not represented, and needs no representation: it has
    no second thread to retarget in a single-threaded model. -/
/-- [sigdelsetmask(&new_set, sigmask(SIGKILL)|sigmask(SIGSTOP))]
    (kernel/signal.c, [SYSCALL_DEFINE4(rt_sigprocmask)]).  Applied to the
    set the caller supplied and to nothing else — the [old_set] snapshot
    taken one line earlier goes out through [oset] unfiltered, which is
    why this is a separate function rather than a filter on the field.

    Blocking SIGKILL is not an error.  The call returns 0 having quietly
    dropped the bits, and a later read-back through [oset] is the only
    way a program can tell.  Because this spec answers [oset], the
    strip needs modeling. -/
def sigmask_strip (w : word) : word :=
  w &&& ~~~ (BitVec.ofNat 64 sig_kernel_only_mask.toNat)

/-- [sigprocmask]'s [switch (how)], kernel/signal.c: [sigorsets] for
    SIG_BLOCK, [sigandnsets] for SIG_UNBLOCK, plain assignment for
    SIG_SETMASK.  [how] has already been checked by [how_valid], so the
    default arm here is unreachable rather than a fall-through — it
    repeats SIG_SETMASK's answer, and the guard is what makes that
    choice inert.  A reader tempted to widen [how_valid] must fix this
    together with it. -/
def sigmask_apply (how old new : word) : word :=
  if (how.toNat : Int) == SIG_BLOCK then old ||| new
  else if (how.toNat : Int) == SIG_UNBLOCK then old &&& ~~~new
  else new

/-- THE WHOLE-RUN HALF OF [Run.valid_sigmask], AS A CHECK RATHER THAN A
    SENTENCE.  That predicate constrains the mask a process is LAUNCHED
    with; what makes it a property of the whole run is that nothing this
    spec does can put either bit back, and that is a claim about this
    file's contents, so it is stated here and proved rather than
    asserted in prose.

    It is what the second of this development's three priorities rests
    on for this syscall: [oset] copies the mask out verbatim, so a
    reachable state with SIGKILL or SIGSTOP set would be a trace Linux
    cannot produce. -/
def mask_launchable (w : word) : Prop :=
  w &&& BitVec.ofNat 64 sig_kernel_only_mask.toNat = BitVec.ofInt 64 0

/-- `BitVec.ofInt 64 0` is the zero word; the two spellings agree. -/
private theorem ofInt64_zero : BitVec.ofInt 64 0 = (0 : word) := by decide

/-- [sigmask_strip] clears both unblockable bits, whatever the input: the
    whole-run half of [Run.valid_sigmask] for the strip.  This is the
    strip's launchable-mask lemma; the `Z`/`bv` arithmetic goes
    through `BitVec`'s own `and`/`not` lemmas here rather than through
    `bv_and_unsigned` and `Z.land_assoc`, which is the same calculation
    one level down. -/
theorem sigmask_strip_launchable (w : word) : mask_launchable (sigmask_strip w) := by
  unfold mask_launchable sigmask_strip
  rw [ofInt64_zero, BitVec.and_assoc, BitVec.not_and_self]
  exact BitVec.and_zero

/-- …and so does the install: [SIG_BLOCK] ORs two clean masks, [SIG_UNBLOCK]
    only CLEARS bits, and [SIG_SETMASK] installs a clean one.  This is the
    apply's launchable-mask lemma, with the same case annotation:
    the second arm's proof does not look at the second operand at all. -/
theorem sigmask_apply_launchable (how old new : word)
    (Hold : mask_launchable old) (Hnew : mask_launchable new) :
    mask_launchable (sigmask_apply how old new) := by
  unfold mask_launchable at *
  unfold sigmask_apply
  rw [ofInt64_zero] at *
  by_cases hb : ((how.toNat : Int) == SIG_BLOCK) = true
  · -- SIG_BLOCK: [sigorsets] -- neither operand carries the bits
    rw [ite_eq_left hb, BitVec.and_comm (old ||| new) _, BitVec.and_or_distrib_left,
      BitVec.and_comm _ old, BitVec.and_comm _ new, Hold, Hnew]
    decide
  · rw [ite_eq_right hb]
    by_cases hu : ((how.toNat : Int) == SIG_UNBLOCK) = true
    · -- SIG_UNBLOCK: [sigandnsets] only CLEARS, so the second operand is
      -- irrelevant and the proof does not look at it
      rw [ite_eq_left hu, BitVec.and_assoc, BitVec.and_comm (~~~new) _,
        ← BitVec.and_assoc, Hold]
      exact BitVec.zero_and
    · -- SIG_SETMASK: the value installed is the caller's, already stripped
      rw [ite_eq_right hu]
      exact Hnew

/-- The [oset] copy-out, which is the LAST thing the syscall does:

      if (oset) { if (copy_to_user(oset, &old_set, sizeof(sigset_t)))
                          return -EFAULT; }
      return 0;

    [old] is the mask the process had ON ENTRY, snapshotted before any
    install, so this is called with the entry mask on every arm that
    reaches it — including the one that has already changed the mask.

    [access_ok] IS TESTED BEFORE THE MEMORY WALK, AND THE ORDER IS THE
    POINT.  [copy_to_user] is [access_ok] then [raw_copy_to_user]
    (include/linux/uaccess.h), and [State.access_okb] is written as a
    subtraction in [Z] rather than a sum in 64-bit words, so it is the
    only thing here that sees a range wrapping the top of the address
    space.
    [State.read_bytes_map] walks in WORD arithmetic and wraps: an [oset]
    of 2^64-4 would find four bytes below the top and four at address 0
    and call the range writable, and the model would answer 0 with a
    write where [__access_ok] refuses outright.  Testing the walk first
    and [access_ok] second is a real bug wearing this arm's shape.

    THE THIRD CASE IS WHY THIS IS NOT JUST TWO ARMS.  A destination that
    passes [access_ok] but is not wholly writable is DECLINED, not
    -EFAULT, because Linux's answer there is not only an errno: riscv's
    [raw_copy_to_user] copies forward with exception fixups, so an
    [oset] straddling a page boundary with only the first page writable
    really does store those bytes before faulting.  The return is
    -EFAULT either way, but the memory is not, and unlike the
    copy-from-user shortfall this spec already tolerates (arm 4a, whose
    cost is one page of allocation BUDGET) a partial copy-out is
    USER-VISIBLE STATE.  Answering -EFAULT with no write would be a
    plausible-looking answer Linux need not give.  So the arm fails
    closed and says so.

    This is the same shape as [Kernel.Sys.prlimit64_spec]'s read arm,
    with one difference worth naming because it reads as an
    inconsistency otherwise: [prlimit64_spec] declines BOTH pointers
    non-NULL precisely to avoid a failed call that has already mutated
    state, and this spec takes that obligation on instead.  The reason
    they differ is that here the mutation is the whole point of the
    call — declining it would decline [sigprocmask] itself — whereas
    there it was avoidable. -/
def write_oset (oset old : word) : SysSpec SyscallEffect :=
  if !(access_okb oset NSIG_BYTES) then err_ret EFAULT
  else
    bind inputSpec fun i =>
      match read_bytes_map i.in_wmem oset (BitVec.ofInt 64 NSIG_BYTES) with
      | some _ =>
          pure (mkEffect (BitVec.ofInt 64 0)
                 [(oset, Z_to_le_bytes NSIG_BYTES.toNat (old.toNat : Int))] [])
      | none => unmodeled

/-- WHERE THE ABORT ACTUALLY KILLS THE PROCESS, and it is not at the
    [tkill].

    musl's [abort] calls [raise(SIGABRT)], and [raise] blocks the
    application signals before it sends anything: [__block_app_sigs]
    (src/signal/block.c, musl 1.2.6) is
    [rt_sigprocmask(SIG_BLOCK, &app_mask, &oldset, 8)] with an
    [app_mask] of 0xfffffffc7fffffff, whose low half sets bits 0..30 --
    signals 1..31, SIGABRT among them.  So by the time [tkill] runs,
    SIGABRT is BLOCKED, and a blocked signal is added to the task's
    pending set and left there: [send_signal_locked] does the add and
    [recalc_sigpending] leaves TIF_SIGPENDING clear for a signal the
    mask covers, so the return to user space takes no signal
    (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).  [raise]
    then restores the old mask with
    [rt_sigprocmask(SIG_SETMASK, &oldset, 0, 8)], and THAT call is the
    one the process does not come back from: [set_current_blocked] ->
    [__set_current_blocked] -> [__set_task_blocked] ends with
    [recalc_sigpending], which now finds an unblocked pending SIGABRT,
    so [get_signal] runs on the way out, finds SIG_DFL, and takes the
    default action for a coredumping signal -- [do_coredump] then
    [do_group_exit] (kernel/signal.c).

    So the fatal step belongs to THIS syscall, and it is conditional on
    the mask the call installs rather than on the mask it was handed.
    [set_sigmask_deliver] is [Monad.set_sigmask] plus that condition, and
    the two coincide whenever nothing is pending
    ([set_sigmask_deliver_no_pending]), which is every state a run with
    the declaration off can reach.

    THE ORDER IS THE KERNEL'S.  The mask is installed first and the
    process dies afterwards, so a [tkill] that becomes fatal here does so
    against the NEW mask; and the [oset] copy-out below still happens,
    because [sys_rt_sigprocmask] finishes before the return path takes
    the signal.  What it wrote is never read by anybody -- the process is
    gone and the memory is its own -- so the effect this spec produces is
    discarded by [Run.sstep_killed] exactly as [Kernel.Exit.exit_spec]'s
    is by [Run.sstep_exit].

    A LAUNCH MASK THAT ALREADY BLOCKS SIGABRT IS A DECLINE, NOT A DEATH.
    [oldset] is then a mask with bit 5 set, the restore does not unblock
    anything, [raise] RETURNS, and musl's [abort] goes on to its second
    path -- [rt_sigaction(SIGABRT, {SIG_DFL}, 0, 8)] -- which
    [rt_sigaction_spec] declines, because [sigaction_accepted] admits
    SIGINT and SIGTERM and nothing else.  [State.valid_sigmask] does not
    forbid such a launch and should not: it is a launch Linux really
    performs.  The run simply leaves the modeled surface, which is the
    honest answer. -/
def sigabrt_blocked (mask : word) : Bool :=
  !(w_is0 (mask &&& BitVec.ofNat 64 sigabrt_mask.toNat))

/-- ONE [State] FUNCTION AND ONE [Monad.modify], rather than a branch
    over two monadic steps, because that is what the checker and the
    witness can follow: [Checks.Sys.Kernel.Signal] and
    [Checks.Witness.Kernel.Signal] discharge this call with the same
    [modify_ok] they discharged the plain [set_sigmask] with, and the
    branch moves into the model function they compute. -/
def sigmask_deliver_model (new : word) (m : Model) : Model :=
  if m_sigabrt_pending m && !(sigabrt_blocked new)
  then with_killed (BitVec.ofInt 64 SIGABRT) (with_sigmask new m)
  else with_sigmask new m

def set_sigmask_deliver (new : word) : SysSpec Unit :=
  modifySpec (sigmask_deliver_model new)

/-- MEANING PRESERVED: with nothing pending -- every state a run whose
    task did not declare the abort path can reach, since
    [State.with_sigabrt_pending]'s only caller is [tkill_spec] and that
    spec declines outright with the declaration off -- installing a mask
    is plain [with_sigmask]. -/
theorem sigmask_deliver_model_no_pending (new : word) (m : Model)
    (Hp : m_sigabrt_pending m = false) :
    sigmask_deliver_model new m = with_sigmask new m := by
  unfold sigmask_deliver_model
  rw [Hp]
  rfl

/-- The two projections the checker and the witness need through the
    delivery: the mask installed is the mask asked for, and the address
    space is untouched.  Both branches of [sigmask_deliver_model] go
    through [State.with_sigmask], and [State.with_killed] on top of it
    rebuilds [ProcState] alone. -/
theorem m_sigmask_sigmask_deliver_model (new : word) (m : Model) :
    m_sigmask (sigmask_deliver_model new m) = new := by
  unfold sigmask_deliver_model
  split <;> rfl

theorem m_vmmaps_sigmask_deliver_model (new : word) (m : Model) :
    m_vmmaps (sigmask_deliver_model new m) = m_vmmaps m := by
  unfold sigmask_deliver_model
  split <;> rfl

theorem set_sigmask_deliver_no_pending (new : word) (i : SyscallInput) (m : Model)
    (o : Outcome Unit Model event) (Hp : m_sigabrt_pending m = false) :
    set_sigmask_deliver new i m o ↔ set_sigmask new i m o := by
  have h : sigmask_deliver_model new m = with_sigmask new m :=
    sigmask_deliver_model_no_pending new m Hp
  show (o = .ok () (sigmask_deliver_model new m) [] : Prop) ↔
    (o = .ok () (with_sigmask new m) [] : Prop)
  rw [h]

def rt_sigprocmask_spec (how nset oset ss : word) : SysSpec SyscallEffect :=
  if !(ss == BitVec.ofInt 64 NSIG_BYTES) then err_ret EINVAL
  else
    bind getModelSpec fun m =>
      let old := m_sigmask m
      if w_is0 nset then
        (if w_is0 oset then ret_only (BitVec.ofInt 64 0) else write_oset oset old)
      else
        bind inputSpec fun i =>
          match sigset_at i.in_mem nset with
          | none => err_ret EFAULT
          | some raw =>
              record_copyins [(nset, NSIG_BYTES.toNat)]
                (if !(how_valid how) then err_ret EINVAL
                 else
                   seqSpec (set_sigmask_deliver (sigmask_apply how old (sigmask_strip raw)))
                     (if w_is0 oset then ret_only (BitVec.ofInt 64 0)
                      else write_oset oset old))

/-! ## sigaltstack (132) — a stack that is recorded as installed and never used -/

/-! WHICH KERNEL THIS IS A MODEL OF, AND WHAT IT COSTS TO ANSWER AT ALL.

    Linux v6.18.46, commit 1f99e9ab748f.  The whole call is
    [SYSCALL_DEFINE2(sigaltstack)] and [do_sigaltstack], both
    kernel/signal.c, over four helpers: [on_sig_stack], [__on_sig_stack]
    and [sas_ss_flags] (include/linux/sched/signal.h) and
    [sigaltstack_size_valid] (arch/riscv/kernel/signal.c under
    CONFIG_DYNAMIC_SIGFRAME, include/linux/signal.h without it).

    WHY AN INSTALLED STACK IS INVISIBLE HERE.  An alternate stack is
    consulted at ONE place, [sigsp] (include/linux/sched/signal.h), on
    the way into a handler for a disposition carrying SA_ONSTACK.  This
    model delivers no signal — [Run.sstep] has no asynchronous
    transition and [State.event] has no signal constructor — so nothing
    it admits ever reads the stack it records.  That is the same premise
    [rt_sigaction_spec] above rests on, not a second one.

    THE STATE IS ONE BIT, AND THE BIT IS NOT THE RECORD.  What the model
    keeps is [State.m_sigaltstack_installed]: whether a [sigaltstack] has
    left [sas_ss_size] NON-ZERO.  It does not keep [ss_sp] or [ss_size],
    and storing them would buy no answer, because BOTH READERS OF THE
    RECORD TAKE THE USER STACK POINTER AS AN ARGUMENT and
    [State.SyscallInput] carries a0..a5 and no sp:

      - [on_sig_stack(sp)] decides -EPERM;
      - [sas_ss_flags(sp)] is the [ss_flags] an [oss] answer reports.

    ZERO SIZE IS WHAT MAKES THEM ANSWERABLE, and it is the size and not
    the age of the record that does it.  While [sas_ss_size] is zero both
    are constant in sp — [__on_sig_stack] reduces to
    [sp > sas_ss_sp && sp - sas_ss_sp <= 0], whose two conjuncts
    contradict each other for every sp, and [sas_ss_flags] returns
    SS_DISABLE on its first line before it consults anything else.  A
    size of at least [Uapi.MINSIGSTKSZ] ends that, and -EPERM becomes a
    fact about a stack pointer this model cannot see.

    SO THE BIT IS SET BY ARM 9 AND NOT BY ARM 6.  [do_sigaltstack]
    reaches its three assignments on both, but the SS_DISABLE arm runs
    [ss_size = 0; ss_sp = NULL] first, so the record it leaves is
    (NULL, 0, [ss_flags]) — the same zero-size shape execve's is, with
    the same two constant readers.  Declining after it would give up an
    answer the model still has.  What a disable does change is the third
    field, from the inherited word to the caller's, and the spec buys
    nothing by that: the two arms that would need a flags word (2 and 7)
    decline whether it is known or not.

    THE INVARIANT THE OTHER ARMS REST ON: while the bit is false the
    record is (NULL, 0, F) for a flags word F the model does not track.
    It holds at [mkModel] (begin_new_exec), and each arm preserves it —
    2, 3, 4, 5, 7 and 8 store nothing at all, arm 6 stores
    (NULL, 0, [ss_flags]), and arm 9 breaks it and sets the bit in the
    same step.  Every answer below is therefore correct for EVERY F,
    which is what makes not tracking it sound rather than merely
    convenient.

    THE STARTING RECORD IS execve's, AND IT IS NOT WHOLLY KNOWN.
    [begin_new_exec] (fs/exec.c) clears TWO of the three fields —
    [me->sas_ss_sp = me->sas_ss_size = 0] — and leaves
    [me->sas_ss_flags] alone; the three-field reset [sas_ss_reset]
    (include/linux/sched/signal.h) is called from [copy_process]
    (kernel/fork.c) for a CLONE_VM child and from nowhere on the exec
    path.  So the starting flags word is INHERITED from whatever process
    called [execve], which makes it a choice of the launching
    environment in the way [State.in_sigmask] is, and
    [State.ProcInput] does not quantify it.  Two things follow, and they
    are the reason this spec has arms 2 and 7 rather than answering
    everything the kernel answers:

      - a non-NULL [uoss] is declined, because [do_sigaltstack] writes
        [sas_ss_flags(sp) | (current->sas_ss_flags & SS_FLAG_BITS)]
        there and the second half is the inherited bit.  This is
        [rt_sigaction_spec]'s [oact] decline with a sharper citation:
        there the unknown is a disposition execve only partly resets,
        here it is a field execve does not reset at all.
      - the no-change fast path is decided by comparing the caller's
        whole [ss_flags] word against the stored one — that inherited
        word, or whatever a previous SS_DISABLE put in its place — so a
        call that would take it is declined too, see arm 7.

    THE SUCCESS ARM CARRIES A PREMISE ABOUT THE ISA, AND IT IS WORTH
    STATING BECAUSE -ENOMEM IS NOT [MINSIGSTKSZ] ALONE ON THIS
    ARCHITECTURE.  [do_sigaltstack] applies a second lower bound,
    [sigaltstack_size_valid], and RISCV_ISA_V selects DYNAMIC_SIGFRAME
    (arch/riscv/Kconfig), under which riscv's implementation
    (arch/riscv/kernel/signal.c) is [ss_size > get_rt_frame_size(false)].
    That function adds [riscv_v_sc_size] — a size derived from the
    hardware's VLEN — whenever the calling task's vector state is not
    OFF, so on a vector-enabled task the boundary moves with the machine
    and this model could not state it.

    IT IS OFF FOR EVERY RUN THIS MODEL ADMITS.  [flush_thread]
    (arch/riscv/kernel/process.c) turns it off at [execve], and exactly
    one thing turns it back on: [riscv_v_first_use_handler]
    (arch/riscv/kernel/vector.c), the trap taken when the task executes a
    vector instruction, which is also the only caller of
    [riscv_v_vstate_on] (arch/riscv/include/asm/vector.h).  The modeled
    ISA is RV64IMAFD_Zicsr_Zifencei plus C (the decoders in `Riscv/`)
    and contains no vector instruction at all,
    so no run this model admits reaches that handler.  With the state
    off, [get_rt_frame_size(false)] is
    [round_up(sizeof(struct rt_sigframe), 16)] = 1088 — [struct siginfo]
    128 plus [struct ucontext] 960, the latter being 176 bytes up to
    [uc_mcontext] and a [struct sigcontext] of 784 — which is below
    [Uapi.MINSIGSTKSZ] = 2048, so the second bound never decides a case
    the first has not.  Under RISCV_ISA_V=n the same conclusion holds for
    a second reason: [sigaltstack_size_valid] is then the trivial
    [return true] (include/linux/signal.h).

    WHAT WOULD BREAK THAT: a vector instruction in the decoder.  The day
    [`Riscv/Decode.lean`] gains one, a run can turn the vector state
    on, and this spec's arm 9 starts admitting a 0 where a real kernel on
    a wide-VLEN hart answers -ENOMEM.  The fix is not a wider envelope but
    a narrower one — decline arm 9 outright, since no [ss_size] is large
    enough for every VLEN.

    WHAT IS DELIBERATELY NOT MODELED, beyond the two declines above:
    every [sigaltstack] after the first size-raising install (arm 1), and
    [restore_altstack]'s path into the same function, which belongs to
    [rt_sigreturn] (139) and has no arm.

    A NOTE FOR [rt_sigprocmask_spec] ABOVE: this arm opens no window onto
    the blocked mask.  [do_sigaltstack] reads and writes [sas_ss_sp],
    [sas_ss_size] and [sas_ss_flags] and names [blocked] nowhere, and
    [SYSCALL_DEFINE2(sigaltstack)] calls no [set_user_sigmask].  132 is
    not on [sig_mask_windows], the list `Checks/Cases/Kernel/Signal.lean`
    carries; as for
    134, 72, 73 and 22, the
    fact that actually shuts it is checked in that same file instead —
    [sigaltstack_leaves_the_mask_alone] — so the shutdown here is both
    read by inspection and pinned there. -/

/-- The three fields of the [stack_t] the kernel copied in, decoded from
    its 24 bytes.  [ss_flags] is an [int]: the kernel reads it as
    [unsigned ss_flags = ss->ss_flags], four bytes at offset 8, and the
    four padding bytes above it are copied and never looked at.

     `firstn n l` is `l.take n`, `skipn n l` is `l.drop n`, and
    `Z.to_nat SS_FLAGS_OFF` is `SS_FLAGS_OFF.toNat`. -/
def ss_sp_of (bs : List byte) : word :=
  le_bytes_to_word (bs.take 8)

def ss_flags_of (bs : List byte) : word :=
  le_bytes_to_word ((bs.drop SS_FLAGS_OFF.toNat).take 4)

def ss_size_of (bs : List byte) : word :=
  le_bytes_to_word (bs.drop SS_SIZE_OFF.toNat)

/-- [ss_mode = ss_flags & ~SS_FLAG_BITS] — the flags word with the one
    bit that is not a mode masked away.

    is [Z.ldiff (bv_unsigned fl) SS_AUTODISARM], which
    is the unsigned reading with bit 31 cleared; see the header's note on
    `Z` bitwise operations for why it is stated with `BitVec`'s `~~~` and
    `&&&`. -/
def ss_mode (fl : word) : Int :=
  ((fl &&& ~~~ (BitVec.ofNat 64 SS_AUTODISARM.toNat)).toNat : Int)

/-- [do_sigaltstack] answers -EINVAL for a mode outside {SS_DISABLE,
    SS_ONSTACK, 0}.  SS_ONSTACK is ACCEPTED as an input mode — the
    kernel does not refuse a caller that claims to be on the stack it is
    installing — and is not the same thing as the SS_ONSTACK [oss]
    reports back. -/
def ss_mode_ok (fl : word) : Bool :=
  let md := ss_mode fl
  md == 0 || md == SS_ONSTACK || md == SS_DISABLE

def ss_disabling (fl : word) : Bool := ss_mode fl == SS_DISABLE

/-- The [stack_t] at [uss], or [None] if any of its 24 bytes is
    unreadable.  All-or-nothing because [SYSCALL_DEFINE2(sigaltstack)]
    fetches the struct with ONE [copy_from_user] before [do_sigaltstack]
    runs, so -EFAULT precedes every other answer this call has.

    NO [State.access_okb] GUARD, for the reason [sigaction_flags] gives
    above and by the same argument: all 24 bytes must be readable before
    anything is answered, and the word addition cannot manufacture a
    readable range across 2^64 because no model state maps one there. -/
def sigaltstack_at (mp : word → Option byte) (uss : word) : Option (List byte) :=
  read_bytes_map mp uss (BitVec.ofInt 64 SIGALTSTACK_BYTES)

/-- [sigaltstack uss uoss].  The arms follow the kernel's own order:

      1. a stack is installed — [sas_ss_size] is non-zero — so nothing
         below can be decided from a stack pointer this model does not
         have: UNMODELED.  This is the arm that makes one bit enough.
      2. a non-NULL [uoss] is UNMODELED — the inherited SS_AUTODISARM
         bit is part of the answer.
      3. with both pointers NULL [do_sigaltstack] runs and does nothing:
         0.
      4. -EFAULT unless all 24 bytes at [uss] are readable.
      5. -EINVAL for a mode outside {0, SS_ONSTACK, SS_DISABLE}.  It is
         decided AFTER the copy and BEFORE the fast path, exactly where
         the kernel decides it, and after an -EPERM that cannot fire —
         [on_sig_stack] is false for every sp while the recorded size is
         zero, which arm 1 guarantees it is.
      6. SS_DISABLE succeeds whatever [ss_sp] and [ss_size] say: the
         kernel zeroes both before storing, so no size check applies.
         The record moves to (NULL, 0, [ss_flags]) — or was already
         exactly that and the fast path returned first, which is the same
         record, since that path is taken only when all three fields
         already match.  Either way the answer is 0 and the size stays
         zero, so the bit is NOT set and the arms below keep answering.
      7. a zero [ss_sp] AND a zero [ss_size] under a non-disabling mode
         is UNMODELED, and this is the only arm that is not a kernel
         answer.  It is the fast path's shadow: the kernel returns 0 when
         all three fields equal the stored ones and -ENOMEM otherwise
         (the size is zero, so the bound below refuses it), and which of
         the two it is turns on the stored flags word — execve's
         inherited one, or the one arm 6 wrote over it.  Neither is
         tracked, so both decline.
      8. -ENOMEM below [Uapi.MINSIGSTKSZ].  The fast path cannot have
         fired above it: it needs [ss_sp] and [ss_size] to equal a
         stored pair that the invariant makes (NULL, 0), and that shape
         is arm 7's, already declined.
      9. otherwise the install succeeds: 0, and the bit is set — this is
         the only arm that raises [sas_ss_size] above zero, and the
         [Uapi.MINSIGSTKSZ] bound arm 8 just applied is why.

    No arm writes user memory, and none records a copy-in: the 24 bytes
    are read into a kernel local ([stack_t new] on the syscall's own
    stack), the same shape [rt_sigaction_spec] has above. -/
def sigaltstack_spec (uss uoss : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if m_sigaltstack_installed m then unmodeled
    else if !(w_is0 uoss) then unmodeled
    else if w_is0 uss then ret_only (BitVec.ofInt 64 0)
    else
      bind inputSpec fun i =>
        match sigaltstack_at i.in_mem uss with
        | none => err_ret EFAULT
        | some bs =>
            let fl := ss_flags_of bs
            if !(ss_mode_ok fl) then err_ret EINVAL
            else if ss_disabling fl then ret_only (BitVec.ofInt 64 0)
            else if w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs) then unmodeled
            else if ((ss_size_of bs).toNat : Int) < MINSIGSTKSZ then err_ret ENOMEM
            else seqSpec set_sigaltstack_installed (ret_only (BitVec.ofInt 64 0))

/-! ## tkill (130) and tgkill (131) — the abort path, and only under a
    task's declaration -/

/-! WHY THESE TWO NUMBERS HAVE AN ARM AT ALL.

    A dataset whose
    reference must not abort wants "the reference can abort" to be a
    PROOF OBLIGATION — proving the abort unreachable is proving the
    program's property — and leaving 130 and 131 unmodeled is what makes
    it one: the run leaves the modeled surface, [Run.reaches_unmodeled]
    holds, and [Equivalence.modeled] is false.  That is not right for
    every dataset.  A reference whose abort is EXPECTED on some inputs —
    a parser that rejects malformed input by aborting — is then
    unprovable for a reason that has nothing to do with the property
    being checked.

    So the stance is the task's, and it is declared in the INPUT:
    [State.in_abort_terminal], pinned [false] by [Run.valid_input] and
    [true] by [Run.valid_input_abort].  With the declaration off this
    arm answers [unmodeled] for every argument shape, which is what the
    dispatcher does for a number with no arm — the decline is the FIRST
    test below for exactly that reason, ahead of the -EINVAL a real
    kernel would answer first, because a coverage gate is not a kernel
    test and putting it anywhere else would leave a shape that answers
    with the declaration off.

    ** WHAT abort() ISSUES, WHICH IS NOT WHAT THE NAME SUGGESTS

    musl 1.2.6 on riscv64, static and single-threaded
    (src/exit/abort.c, src/signal/raise.c, src/signal/block.c):

      rt_sigprocmask(SIG_BLOCK, app_mask, &oldset, 8)
      tkill(tid, SIGABRT)
      rt_sigprocmask(SIG_SETMASK, &oldset, 0, 8)

    [raise] issues TKILL, not tgkill, and it issues no [gettid]: the tid
    comes from [__pthread_self()->tid], which [__init_tp]
    (src/env/__init_tls.c) seeded from the return value of
    [set_tid_address] (96) at start-up — the same number
    [Kernel.Sys.gettid_spec] and [Kernel.Sys.getpid_spec] answer, and the
    same [State.m_tid] this spec compares against.  tgkill is here
    anyway because it is the same kernel path with one more test, and
    other libcs raise through it.

    ** THE MODELED ENVELOPE

    Answered:

    - [pid] <= 0 (and, for tgkill, [tgid] <= 0): -EINVAL, tested before
      anything else looks at a task.  [SYSCALL_DEFINE2(tkill)] refuses
      [pid <= 0] and [SYSCALL_DEFINE3(tgkill)] refuses either being
      <= 0 (kernel/signal.c, Linux v6.18.46, commit 1f99e9ab748f).
    - tgkill with [pid] the caller's own tid but [tgid] something else:
      -ESRCH.  [do_send_specific] finds the task and then requires
      [task_tgid_vnr(p) == tgid] before it will deliver, leaving the
      seeded -ESRCH when it does not match (kernel/signal.c, same
      version).  In this model the caller's tgid IS its tid — one
      thread, one group, which is the same fact
      [State.procst_tid] rests on — so a mismatch is decidable here.
    - [sig] above 64, which after the [int] truncation is also every
      negative one: -EINVAL from [check_kill_permission]'s
      [valid_signal] test, which the caller reaches because the task
      lookup succeeded (kernel/signal.c, same version).
    - [sig] = SIGABRT to the caller's own tid: the abort path, below.

    Unmodeled, each because the answer is not this model's to give:

    - [pid] positive and NOT the caller's tid.  [find_task_by_vpid]
      searches the whole pid namespace, and this model knows about one
      task; -ESRCH would be a guess about every other process on the
      machine.
    - [sig] = 0, the permission-and-existence probe.  [valid_signal(0)]
      is true and delivery is skipped under [if (!error && sig)], so the
      answer is whatever [security_task_kill] says, which is an LSM
      question rather than a kernel one.
    - any other signal in 1..64.  The model has a disposition for
      SIGABRT and for no other signal: [rt_sigaction_spec] declines
      every install outside SIGINT and SIGTERM, so what SIGKILL or
      SIGUSR1 would do to this process is not something the model can
      read off its own state.
    - [State.m_tid] not yet pinned.  Nothing has made the tid
      observable, so there is no value to compare [pid] against.

    ** WHY SIGABRT'S DISPOSITION IS SIG_DFL, BY CONSTRUCTION

    The whole arm rests on it, and it is not an assumption: SIGABRT's
    disposition cannot be changed inside the modeled surface.
    [rt_sigaction_spec] answers an install only when
    [sigaction_accepted] holds, and that predicate admits signals 2 and
    15.  Signal 6 with a non-NULL [act] is [unmodeled], whatever handler
    it carries — including musl's own SIG_DFL install on abort's second
    path.  So in any run this model covers, SIGABRT still has its
    boot-time disposition, which is SIG_CORE: terminate, and dump core
    (kernel/signal.c, SIG_KERNEL_COREDUMP_MASK; the core dump is a file
    the process never sees, so nothing of it reaches the trace).

    That is the sentence [sigaction_accepted]'s own note has to be read
    against: its list is "the signals whose disposition no modeled
    operation can consult AND which the environment therefore never
    delivers", and this arm is a modeled operation that DOES
    deliver one.  It delivers SIGABRT alone, and SIGABRT is not on that
    list, so the list's second half still holds for the two signals on
    it.

    ** THE LSM GAP

    [check_kill_permission] ends with [security_task_kill], which an
    enabled LSM can answer -EPERM to even for a signal to oneself.  This
    spec answers rather than declining, so it does not admit that
    -EPERM.  That is a known gap, of the same shape as [getdents64]'s
    LSM and fanotify denial gap. -/

/-- [pid] and [tgid] arrive as [pid_t], an [int]: [Syscall.pid32] has
    already truncated to 32 bits, so "positive" is 1..2^31-1 and every
    negative value has become something at or above 2^31. -/
def pid_positive (p : word) : Bool :=
  let v := (p.toNat : Int)
  decide (1 ≤ v ∧ v < 2 ^ 31)

/-- [valid_signal(sig)] widens the [int] to [unsigned long] and tests
    [sig <= _NSIG], with [_NSIG] 64 on riscv64.  A negative [int] widens
    to something enormous and fails; so does anything above 64.  Applied
    to the already-truncated low half, an unsigned [<= 64] test is that
    predicate — and unlike [sig_valid], which [rt_sigaction] uses, 0
    PASSES it: [rt_sigaction]'s [sig < 1] is its own test, and the
    signal-sending paths keep 0 as the permission probe. -/
def tkill_sig_valid (sig : word) : Bool :=
  decide ((sig.toNat : Int) ≤ 64)

/-- The delivery, once every check has passed and the target is the
    caller itself.  BLOCKED means pending: [send_signal_locked] adds the
    signal to [task->pending] and [recalc_sigpending] leaves it there
    while the mask covers it, so the syscall returns 0 and the process
    runs on — see [set_sigmask_deliver] for where it is taken.
    UNBLOCKED means the process does not come back: [get_signal] runs on
    the return to user space, finds SIG_DFL for a coredumping signal, and
    reaches [do_group_exit] (kernel/signal.c, Linux v6.18.46, commit
    1f99e9ab748f).  The 0 this returns on that branch is never observed,
    for [Kernel.Exit.exit_spec]'s reason: [Run.sstep_killed] ends the
    trace with a [State.KillEv] and discards the effect. -/
def send_sigabrt : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    seqSpec
      (if sigabrt_blocked (m_sigmask m)
       then set_sigabrt_pending
       else set_killed (BitVec.ofInt 64 SIGABRT))
      (ret_only (BitVec.ofInt 64 0))

/-- Everything [tkill] and [tgkill] share: the caller has named a
    positive [pid], and what remains is whether it is this process and
    what signal it is. -/
def tkill_self (pid sig : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if !(m_abort_terminal m) then unmodeled
    else
      match m_tid m with
      | none => unmodeled
      | some t =>
          if !(pid == t) then unmodeled
          else if !(tkill_sig_valid sig) then err_ret EINVAL
          else if sig == BitVec.ofInt 64 SIGABRT then send_sigabrt
          else unmodeled

def tkill_spec (pid sig : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if !(m_abort_terminal m) then unmodeled
    else if !(pid_positive pid) then err_ret EINVAL
    else tkill_self pid sig

def tgkill_spec (tgid pid sig : word) : SysSpec SyscallEffect :=
  bind getModelSpec fun m =>
    if !(m_abort_terminal m) then unmodeled
    else if !(pid_positive pid && pid_positive tgid) then err_ret EINVAL
    else
      match m_tid m with
      | none => unmodeled
      | some t =>
          if !(pid == t) then unmodeled
          else if !(tgid == t) then err_ret ESRCH
          else tkill_self pid sig

/-- WITH THE DECLARATION OFF, BOTH ARMS ARE UNMODELED.  Both specs test it
    first, so with it clear the only outcome either admits is
    [Unmodeled] — which is what [Sys.Dispatch.dispatch] produces for a
    number with no arm.  This is the half of the compatibility
    claim that lives at the spec; the other half is
    [set_sigmask_deliver_no_pending], and the step-level half is
    [Run.sstep_off_no_kill]. -/
theorem tkill_spec_off_unmodeled (pid sig : word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hoff : m_abort_terminal m = false)
    (H : tkill_spec pid sig i m o) : o = .unmodeled := by
  unfold tkill_spec getModelSpec at H
  rw [bind_getModel] at H
  simp [Hoff, unmodeled] at H
  exact H

theorem tgkill_spec_off_unmodeled (tgid pid sig : word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hoff : m_abort_terminal m = false)
    (H : tgkill_spec tgid pid sig i m o) : o = .unmodeled := by
  unfold tgkill_spec getModelSpec at H
  rw [bind_getModel] at H
  simp [Hoff, unmodeled] at H
  exact H

/-! ## Sanity checks on the computable parts

    There is no closed computation to re-use in this file.  These pin the
    arms its prose makes claims about, one per claim: a bad `sigsetsize` is
    -EINVAL before anything else is looked at, for BOTH syscalls; a bad
    `how` is -EINVAL after the copy and `how` is never looked at when
    `nset` is NULL; `SIGKILL`/`SIGSTOP` are -EINVAL at an install and are
    STRIPPED — not refused — by the mask install; `sigaltstack`'s
    SS_DISABLE arm answers 0 without setting the installed bit; and
    `rt_sigaction` declines SA_RESTART and every bit outside
    `sa_flags_accepted`.

    They are port checks, not reused lemmas. -/

/-- A memory view in which every address is mapped: `bs` from `base`
    upward, zero bytes elsewhere.  The checks below read only `bs.length`
    bytes at `base`; defining the tail everywhere keeps
    `read_bytes_map`'s walk from stopping early, so the checks exercise
    the byte decoding rather than an unreadable page. -/
private def all_mem (base : word) (bs : List byte) : word → Option byte :=
  fun a => bs.getD (a.toNat - base.toNat) 0

/-- A syscall input with no argument registers and no mapped memory. -/
private def check_input : SyscallInput :=
  { in_sysno := 0, in_args := [], in_mem := fun _ => none, in_wmem := fun _ => none }

/-- The same, with `mem` as BOTH the readable and the writable view. -/
private def check_input_at (mem : word → Option byte) : SyscallInput :=
  { in_sysno := 0, in_args := [], in_mem := mem, in_wmem := mem }

/-- `mkModel`'s default: no fds, no mappings, no halt, no tid, an empty
    file system and an empty launch mask (`procst_sigmask` is 0), which
    is the state `rt_sigprocmask` reads as `old_set`. -/
private def check_model : Model :=
  mkModel [] (mkVmMaps [] [] 0 0 0) IEof [] none none none

/-- The literal 0: a NULL `act`, `oact`, `uss`, `uoss`, `nset` or
    `oset`, depending on the arm. -/
private def zero_w : word := BitVec.ofInt 64 0

/-- The `sigsetsize` both syscalls accept: `NSIG_BYTES` = 8. -/
private def eight_w : word := BitVec.ofInt 64 8

/-- A `sigsetsize` that is one byte too large — 9, not 8. -/
private def bad_ss : word := BitVec.ofInt 64 9

/-- `SIG_BLOCK` (0) as it reaches `rt_sigprocmask`, post-`how32`. -/
private def sig_block_w : word := BitVec.ofInt 64 0

/-- `SIG_UNBLOCK` (1). -/
private def sig_unblock_w : word := BitVec.ofInt 64 1

/-- `SIG_SETMASK` (2). -/
private def sig_setmask_w : word := BitVec.ofInt 64 2

/-- `how = 3`, outside `{SIG_BLOCK, SIG_UNBLOCK, SIG_SETMASK}`. -/
private def bad_how : word := BitVec.ofInt 64 3

/-- SIGKILL's number, 9 (include/uapi/asm-generic/signal.h). -/
private def sigkill_w : word := BitVec.ofInt 64 9

/-- SIGSTOP's number, 19. -/
private def sigstop_w : word := BitVec.ofInt 64 19

/-- SIGTERM's number, 15 — in `sigaction_accepted`. -/
private def sigterm_w : word := BitVec.ofInt 64 15

/-- SIGSEGV's number, 11 — a `MachineFault` signal, so NOT accepted. -/
private def sigsegv_w : word := BitVec.ofInt 64 11

/-- An address inside the model's address space, where the checks put
    their user buffers. -/
private def buf_w : word := BitVec.ofInt 64 4096

/-- `SA_RESTART` (0x10000000): the one retained `sa_flags` bit outside
    `sa_flags_accepted`. -/
private def sa_restart_w : word := BitVec.ofInt 64 0x10000000

/-- A bit outside `UAPI_SA_FLAGS` altogether (bit 40). -/
private def sa_stray_w : word := BitVec.ofInt 64 0x10000000000

/-- The all-ones mask: every bit of a `sigset_t` set, SIGKILL's and
    SIGSTOP's included. -/
private def all_ones : word := BitVec.ofInt 64 (-1)

/-- The 24 bytes of a riscv64 `struct sigaction` with
    `sa_flags = fl` and the handler and `sa_mask` zero — the layout
    `Riscv`'s and musl's `sigaction` share for the first 24 bytes. -/
private def sa_bytes (fl : word) : List byte :=
  Z_to_le_bytes 8 (0 : Int) ++ Z_to_le_bytes 8 (fl.toNat : Int) ++
    Z_to_le_bytes 8 (0 : Int)

/-- The 24 bytes of a `stack_t` with `ss_sp = sp`, `ss_flags = fl` and
    `ss_size = sz`. -/
private def ss_bytes (sp fl sz : word) : List byte :=
  Z_to_le_bytes 8 (sp.toNat : Int) ++ Z_to_le_bytes 4 (fl.toNat : Int) ++
    Z_to_le_bytes 4 (0 : Int) ++ Z_to_le_bytes 8 (sz.toNat : Int)

/-- `sig_valid` is the INCLUSIVE 1..64 test: 64 is a signal, 65 is not,
    and 0 is not (`rt_sigaction`'s `sig < 1`, unlike `kill`'s probe). -/
example : sig_valid zero_w = false := by decide
example : sig_valid (BitVec.ofInt 64 1) = true := by decide
example : sig_valid (BitVec.ofInt 64 64) = true := by decide
example : sig_valid (BitVec.ofInt 64 65) = false := by decide
example : sig_valid (BitVec.ofInt 64 (-1)) = false := by decide

/-- `sig_kernel_only` names exactly SIGKILL (9) and SIGSTOP (19) — and
    SIGTERM, which the spec accepts, is neither. -/
example : sig_kernel_only sigkill_w = true := by decide
example : sig_kernel_only sigstop_w = true := by decide
example : sig_kernel_only sigterm_w = false := by decide

/-- `sigaction_accepted` admits SIGINT (2) and SIGTERM (15) and nothing
    else: not SIGSEGV, not SIGCHLD (17). -/
example : sigaction_accepted (BitVec.ofInt 64 2) = true := by decide
example : sigaction_accepted sigterm_w = true := by decide
example : sigaction_accepted sigsegv_w = false := by decide
example : sigaction_accepted (BitVec.ofInt 64 17) = false := by decide

/-- `sa_flags_accepted` is 0xC8000807 — `UAPI_SA_FLAGS` (0xD8000807)
    minus SA_RESTART — and `sa_flags_ok` accepts exactly its submasks. -/
example : sa_flags_accepted = 0xC8000807 := by decide
example : sa_flags_ok zero_w = true := by decide
example : sa_flags_ok (BitVec.ofInt 64 0xC8000807) = true := by decide
example : sa_flags_ok sa_restart_w = false := by decide
example : sa_flags_ok sa_stray_w = false := by decide

/-- **rt_sigaction, arm 1: a bad `sigsetsize` is -EINVAL before anything
    else** — a wild `act` pointer, a bad `oact` and a bad `sig` included,
    since none of them is looked at. -/
example :
    rt_sigaction_spec sigterm_w buf_w buf_w bad_ss check_input check_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) check_model []) := by
  have h1 : (!(bad_ss == BitVec.ofInt 64 8)) = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_left h1]
  rfl

/-- -EINVAL is -22, in two's complement — the arm above returns it. -/
example : (mkEffect (errno_ret EINVAL) [] []).eff_ret = BitVec.ofInt 64 (-22) := by
  decide

/-- **rt_sigaction, arm 4, accepted: SIGTERM with a readable `struct
    sigaction` carrying no flags installs nothing and answers 0** — the
    one shape the spec accepts (a direct `sigaction(SIGTERM, &act, NULL)`). -/
example :
    rt_sigaction_spec sigterm_w buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (sa_bytes zero_w))) check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) check_model []) := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : ¬ (w_is0 buf_w = true) := by decide
  have hfl : sigaction_flags (all_mem buf_w (sa_bytes zero_w)) buf_w
      = some zero_w := by decide
  have hs : ¬ ((!(sig_valid sigterm_w)) = true) := by decide
  have hk : ¬ (sig_kernel_only sigterm_w = true) := by decide
  have hf : ¬ ((!(sa_flags_ok zero_w)) = true) := by decide
  have hac : sigaction_accepted sigterm_w = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_right hact]
  refine ⟨check_input_at (all_mem buf_w (sa_bytes zero_w)), check_model, [], [],
    rfl, ?_, rfl⟩
  simp only [check_input_at, hfl]
  rw [ite_eq_right hs, ite_eq_right hk, ite_eq_right hf, ite_eq_left hac]
  rfl

/-- **rt_sigaction, arm 4: SIGKILL and SIGSTOP are -EINVAL** — but only
    with a non-NULL `act`; a NULL `act` is the no-op arm 3.  This is the
    check for `sig_kernel_only`. -/
example :
    rt_sigaction_spec sigkill_w buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (sa_bytes zero_w))) check_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) check_model []) := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : ¬ (w_is0 buf_w = true) := by decide
  have hfl : sigaction_flags (all_mem buf_w (sa_bytes zero_w)) buf_w
      = some zero_w := by decide
  have hs : ¬ ((!(sig_valid sigkill_w)) = true) := by decide
  have hk : sig_kernel_only sigkill_w = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_right hact]
  refine ⟨check_input_at (all_mem buf_w (sa_bytes zero_w)), check_model, [], [],
    rfl, ?_, rfl⟩
  simp only [check_input_at, hfl]
  rw [ite_eq_right hs, ite_eq_left hk]
  rfl

/-- …and the same call with `act` NULL answers 0 for SIGKILL: arm 3
    precedes `sig_kernel_only`, which is what makes the pair "only
    rejected in arm 4". -/
example :
    rt_sigaction_spec sigkill_w zero_w zero_w eight_w check_input check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) check_model []) := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : w_is0 zero_w = true := by decide
  have hs : sig_valid sigkill_w = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_left hact, ite_eq_left hs]
  rfl

/-- **rt_sigaction declines SA_RESTART** — the flag that would need a
    restart in the interrupted syscall's return value, which the model
    does not have. -/
example :
    rt_sigaction_spec sigterm_w buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (sa_bytes sa_restart_w))) check_model
      .unmodeled := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : ¬ (w_is0 buf_w = true) := by decide
  have hfl : sigaction_flags (all_mem buf_w (sa_bytes sa_restart_w)) buf_w
      = some sa_restart_w := by decide
  have hs : ¬ ((!(sig_valid sigterm_w)) = true) := by decide
  have hk : ¬ (sig_kernel_only sigterm_w = true) := by decide
  have hf : (!(sa_flags_ok sa_restart_w)) = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_right hact]
  refine Or.inr ⟨check_input_at (all_mem buf_w (sa_bytes sa_restart_w)),
    check_model, [], rfl, ?_⟩
  simp only [check_input_at, hfl]
  rw [ite_eq_right hs, ite_eq_right hk, ite_eq_left hf]
  rfl

/-- …and every bit outside `sa_flags_accepted`, here bit 40: Linux MASKS
    such a bit away and answers 0, which the spec declines rather than
    decides. -/
example :
    rt_sigaction_spec sigterm_w buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (sa_bytes sa_stray_w))) check_model
      .unmodeled := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : ¬ (w_is0 buf_w = true) := by decide
  have hfl : sigaction_flags (all_mem buf_w (sa_bytes sa_stray_w)) buf_w
      = some sa_stray_w := by decide
  have hs : ¬ ((!(sig_valid sigterm_w)) = true) := by decide
  have hk : ¬ (sig_kernel_only sigterm_w = true) := by decide
  have hf : (!(sa_flags_ok sa_stray_w)) = true := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_right hact]
  refine Or.inr ⟨check_input_at (all_mem buf_w (sa_bytes sa_stray_w)),
    check_model, [], rfl, ?_⟩
  simp only [check_input_at, hfl]
  rw [ite_eq_right hs, ite_eq_right hk, ite_eq_left hf]
  rfl

/-- **rt_sigaction declines SIGSEGV even with clean flags**: a disposition
    for a signal a modeled operation can raise is exactly what would make
    the `MachineFault` exclusion say nothing. -/
example :
    rt_sigaction_spec sigsegv_w buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (sa_bytes zero_w))) check_model
      .unmodeled := by
  have hss : ¬ ((!(eight_w == BitVec.ofInt 64 8)) = true) := by decide
  have hoact : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have hact : ¬ (w_is0 buf_w = true) := by decide
  have hfl : sigaction_flags (all_mem buf_w (sa_bytes zero_w)) buf_w
      = some zero_w := by decide
  have hs : ¬ ((!(sig_valid sigsegv_w)) = true) := by decide
  have hk : ¬ (sig_kernel_only sigsegv_w = true) := by decide
  have hf : ¬ ((!(sa_flags_ok zero_w)) = true) := by decide
  have hac : ¬ (sigaction_accepted sigsegv_w = true) := by decide
  simp only [rt_sigaction_spec]
  rw [ite_eq_right hss, ite_eq_right hoact, ite_eq_right hact]
  refine Or.inr ⟨check_input_at (all_mem buf_w (sa_bytes zero_w)),
    check_model, [], rfl, ?_⟩
  simp only [check_input_at, hfl]
  rw [ite_eq_right hs, ite_eq_right hk, ite_eq_right hf, ite_eq_right hac]
  rfl

/-- **rt_sigprocmask, arm 1: a bad `sigsetsize` is -EINVAL before anything
    else** — before the mask is read, before `nset` is looked at, and
    before `how`.  A register whose LOW HALF is 8 is still the wrong size,
    because `sigsetsize` is `size_t` and does not truncate. -/
example :
    rt_sigprocmask_spec bad_how buf_w buf_w bad_ss check_input check_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) check_model []) := by
  have h1 : (!(bad_ss == BitVec.ofInt 64 NSIG_BYTES)) = true := by decide
  simp only [rt_sigprocmask_spec]
  rw [ite_eq_left h1]
  rfl

/-- …while a register whose low half IS 8 is accepted: `eight_w` is
    `ofInt 64 8`, i.e. the value the kernel compares. -/
example : (eight_w == BitVec.ofInt 64 NSIG_BYTES) = true := by decide

/-- **rt_sigprocmask, arm 3: with `nset` NULL the call is a QUERY, and
    `how` is NEVER LOOKED AT.**  `bad_how` = 3 is outside the accepted
    set, and the call still answers 0 because `sigprocmask` is reached
    only from inside `if (nset)`.  This is the ordering the spec pins. -/
example :
    rt_sigprocmask_spec bad_how zero_w zero_w eight_w check_input check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) check_model []) := by
  have h1 : ¬ ((!(eight_w == BitVec.ofInt 64 NSIG_BYTES)) = true) := by decide
  have hn : w_is0 zero_w = true := by decide
  have ho : w_is0 zero_w = true := by decide
  simp only [rt_sigprocmask_spec]
  rw [ite_eq_right h1]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hn, ite_eq_left ho]
  rfl

/-- **rt_sigprocmask, arm 3 with a non-NULL `oset`: a query still WRITES.**
    `nset` is NULL, so nothing is installed and `how` is not read; `oset`
    receives the ENTRY mask (`check_model`'s `procst_sigmask`, 0), eight
    little-endian bytes of it. -/
example :
    rt_sigprocmask_spec bad_how zero_w buf_w eight_w
        (check_input_at (all_mem buf_w [])) check_model
      (.ok (mkEffect (BitVec.ofInt 64 0)
              [(buf_w, Z_to_le_bytes NSIG_BYTES.toNat (0 : Int))] [])
        check_model []) := by
  have h1 : ¬ ((!(eight_w == BitVec.ofInt 64 NSIG_BYTES)) = true) := by decide
  have hn : w_is0 zero_w = true := by decide
  have ho : ¬ (w_is0 buf_w = true) := by decide
  have hao : ¬ ((!(access_okb buf_w NSIG_BYTES)) = true) := by decide
  have hrd : read_bytes_map (all_mem buf_w []) buf_w (BitVec.ofInt 64 NSIG_BYTES)
      = some [0, 0, 0, 0, 0, 0, 0, 0] := by decide
  simp only [rt_sigprocmask_spec]
  rw [ite_eq_right h1]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hn, ite_eq_right ho]
  simp only [write_oset]
  rw [ite_eq_right hao]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w []), check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hrd]
  rfl

/-- **`write_oset`'s first arm: an out-of-range destination is -EFAULT**
    before the memory walk — the range test `access_okb` exists for, and
    the reason it is asked BEFORE `read_bytes_map`.  Here `oset` is just
    below 2^64, so the range wraps and nothing is written. -/
example :
    write_oset (BitVec.ofInt 64 (-8)) zero_w
        (check_input_at (all_mem (BitVec.ofInt 64 (-8)) [])) check_model
      (.ok (mkEffect (errno_ret EFAULT) [] []) check_model []) := by
  have h : (!(access_okb (BitVec.ofInt 64 (-8)) NSIG_BYTES)) = true := by decide
  simp only [write_oset]
  rw [ite_eq_left h]
  rfl

/-- **rt_sigprocmask, arm 4: a bad `how` is -EINVAL AFTER the copy**, and
    the copy's range is RECORDED — the difference from arm 1's -EINVAL,
    which read no user memory and so carries an empty ledger. -/
example :
    rt_sigprocmask_spec bad_how buf_w zero_w eight_w
        (check_input_at (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (0 : Int))))
        check_model
      (.ok (with_copyins [(buf_w, NSIG_BYTES.toNat)]
              (mkEffect (errno_ret EINVAL) [] []))
        check_model []) := by
  have h1 : ¬ ((!(eight_w == BitVec.ofInt 64 NSIG_BYTES)) = true) := by decide
  have hn : ¬ (w_is0 buf_w = true) := by decide
  have hsig : sigset_at (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (0 : Int)))
      buf_w = some zero_w := by decide
  have hhow : (!(how_valid bad_how)) = true := by decide
  simp only [rt_sigprocmask_spec]
  rw [ite_eq_right h1]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hn]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (0 : Int))),
    check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hsig]
  simp only [record_copyins]
  rw [ite_eq_left hhow]
  simp only [bind]
  exact ⟨mkEffect (errno_ret EINVAL) [] [], check_model, [], [], rfl, rfl, rfl⟩

/-- **rt_sigprocmask, arm 4: the install applies `sigmask_strip`** — the
    SIGKILL/SIGSTOP strip — and answers 0.  With `how = SIG_SETMASK` the
    installed mask is the stripped caller's set, `old_set` and all. -/
example :
    rt_sigprocmask_spec sig_setmask_w buf_w zero_w eight_w
        (check_input_at
          (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (all_ones.toNat : Int))))
        check_model
      (.ok (with_copyins [(buf_w, NSIG_BYTES.toNat)]
              (mkEffect (BitVec.ofInt 64 0) [] []))
        (sigmask_deliver_model (sigmask_apply sig_setmask_w zero_w
          (sigmask_strip all_ones)) check_model) []) := by
  have h1 : ¬ ((!(eight_w == BitVec.ofInt 64 NSIG_BYTES)) = true) := by decide
  have hn : ¬ (w_is0 buf_w = true) := by decide
  have hsig : sigset_at
      (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (all_ones.toNat : Int))) buf_w
      = some all_ones := by decide
  have hhow : ¬ ((!(how_valid sig_setmask_w)) = true) := by decide
  have ho : w_is0 zero_w = true := by decide
  simp only [rt_sigprocmask_spec]
  rw [ite_eq_right h1]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hn]
  simp only [bind]
  refine ⟨check_input_at
      (all_mem buf_w (Z_to_le_bytes NSIG_BYTES.toNat (all_ones.toNat : Int))),
    check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hsig]
  simp only [record_copyins]
  rw [ite_eq_right hhow]
  simp only [bind, seqSpec]
  refine ⟨mkEffect (BitVec.ofInt 64 0) [] [],
    sigmask_deliver_model (sigmask_apply sig_setmask_w zero_w
      (sigmask_strip all_ones)) check_model, [], [], ?_, ?_, rfl⟩
  · refine ⟨(), sigmask_deliver_model (sigmask_apply sig_setmask_w zero_w
        (sigmask_strip all_ones)) check_model, [], [], rfl, ?_, rfl⟩
    rw [ite_eq_left ho]
    rfl
  · rfl

/-- **THE SIGKILL/SIGSTOP MASKING, as a number**: the mask the arm above
    installs is the all-ones set with bits 8 and 18 cleared —
    `2^64 - 1 - 262400`, i.e. SIGKILL's and SIGSTOP's `sigmask` bits
    removed — and NOT the caller's `0xFFFFFFFFFFFFFFFF`.  A spec that
    installed the caller's set verbatim would report `2^64 - 1` here,
    which is a mask Linux cannot produce. -/
example :
    (m_sigmask (sigmask_deliver_model (sigmask_apply sig_setmask_w zero_w
      (sigmask_strip all_ones)) check_model)).toNat = 2 ^ 64 - 1 - 262400 := by
  rw [m_sigmask_sigmask_deliver_model]
  decide

/-- …and the whole-run half: that mask is LAUNCHABLE, so the strip plus
    the install cannot put either bit back.  `sigmask_apply_launchable`
    at the concrete mask the arm installs. -/
example :
    mask_launchable (m_sigmask (sigmask_deliver_model (sigmask_apply
      sig_setmask_w zero_w (sigmask_strip all_ones)) check_model)) := by
  have hzero : mask_launchable zero_w := by
    unfold mask_launchable
    rw [show zero_w = (0 : word) from by decide, ofInt64_zero]
    exact BitVec.zero_and
  rw [m_sigmask_sigmask_deliver_model]
  exact sigmask_apply_launchable _ zero_w _ hzero (sigmask_strip_launchable _)

/-- `SS_DISABLE` (2), `SS_ONSTACK` (1) and `SS_AUTODISARM` (0x80000000) are
    the values `Uapi` carries, and `ss_mode` clears the last of them. -/
example : SS_DISABLE = 2 := by decide
example : SS_ONSTACK = 1 := by decide
example : ss_mode (BitVec.ofInt 64 0x80000000) = 0 := by decide
example : ss_mode (BitVec.ofInt 64 0x80000002) = SS_DISABLE := by decide
example : ss_mode_ok (BitVec.ofInt 64 0x80000002) = true := by decide
example : ss_mode_ok (BitVec.ofInt 64 3) = false := by decide

/-- The flag word of a `stack_t` is read from bytes 8..11 and the size from
    bytes 16..23 — the ABI layout `sigaltstack_at` decodes. -/
example : ss_flags_of (ss_bytes zero_w (BitVec.ofInt 64 2) (BitVec.ofInt 64 4096))
    = BitVec.ofInt 64 2 := by decide
example : ss_size_of (ss_bytes zero_w (BitVec.ofInt 64 2) (BitVec.ofInt 64 4096))
    = BitVec.ofInt 64 4096 := by decide
example : ss_sp_of (ss_bytes (BitVec.ofInt 64 8192) zero_w zero_w)
    = BitVec.ofInt 64 8192 := by decide

/-- **sigaltstack, arm 6: the SS_DISABLE arm answers 0** and does NOT set
    the installed bit — the kernel zeroes `ss_sp` and `ss_size` before it
    stores, so the record stays in the zero-size shape the rest of the
    spec can still answer from. -/
example :
    sigaltstack_spec buf_w zero_w
        (check_input_at (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w)))
        check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) check_model []) := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have huss : ¬ (w_is0 buf_w = true) := by decide
  have hat : sigaltstack_at
      (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w)) buf_w
      = some (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w) := by decide
  have hmode : ¬ ((!(ss_mode_ok (ss_flags_of
      (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w)))) = true) := by decide
  have hdis : ss_disabling (ss_flags_of
      (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w)) = true := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_right huoss, ite_eq_right huss]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 2) zero_w)),
    check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hat]
  rw [ite_eq_right hmode, ite_eq_left hdis]
  rfl

/-- …and the DISABLE arm ignores `ss_sp` and `ss_size` entirely: the same
    call with an enormous size still answers 0, because both are zeroed
    before storing and no size check applies. -/
example :
    sigaltstack_spec buf_w zero_w
        (check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192)
          (BitVec.ofInt 64 2) (BitVec.ofInt 64 0x100000)))) check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) check_model []) := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have huss : ¬ (w_is0 buf_w = true) := by decide
  have hat : sigaltstack_at
      (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) (BitVec.ofInt 64 2)
        (BitVec.ofInt 64 0x100000))) buf_w
      = some (ss_bytes (BitVec.ofInt 64 8192) (BitVec.ofInt 64 2)
          (BitVec.ofInt 64 0x100000)) := by decide
  have hmode : ¬ ((!(ss_mode_ok (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) (BitVec.ofInt 64 2)
        (BitVec.ofInt 64 0x100000))))) = true) := by decide
  have hdis : ss_disabling (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) (BitVec.ofInt 64 2)
        (BitVec.ofInt 64 0x100000))) = true := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_right huoss, ite_eq_right huss]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192)
      (BitVec.ofInt 64 2) (BitVec.ofInt 64 0x100000))),
    check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hat]
  rw [ite_eq_right hmode, ite_eq_left hdis]
  rfl

/-- **sigaltstack, arm 5: a mode outside {0, SS_ONSTACK, SS_DISABLE} is
    -EINVAL** — decided after the copy and before the fast path. -/
example :
    sigaltstack_spec buf_w zero_w
        (check_input_at (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 3) zero_w)))
        check_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) check_model []) := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have huss : ¬ (w_is0 buf_w = true) := by decide
  have hat : sigaltstack_at
      (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 3) zero_w)) buf_w
      = some (ss_bytes zero_w (BitVec.ofInt 64 3) zero_w) := by decide
  have hmode : (!(ss_mode_ok (ss_flags_of
      (ss_bytes zero_w (BitVec.ofInt 64 3) zero_w)))) = true := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_right huoss, ite_eq_right huss]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (ss_bytes zero_w (BitVec.ofInt 64 3) zero_w)),
    check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hat]
  rw [ite_eq_left hmode]
  rfl

/-- **sigaltstack, arm 8: -ENOMEM below `MINSIGSTKSZ`** — here 2047, one
    byte short, with a non-zero `ss_sp` and `ss_size`, the shape arm 7
    does not take. -/
example :
    sigaltstack_spec buf_w zero_w
        (check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
          (BitVec.ofInt 64 2047)))) check_model
      (.ok (mkEffect (errno_ret ENOMEM) [] []) check_model []) := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have huss : ¬ (w_is0 buf_w = true) := by decide
  have hat : sigaltstack_at
      (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
        (BitVec.ofInt 64 2047))) buf_w
      = some (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2047)) := by
    decide
  have hmode : ¬ ((!(ss_mode_ok (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2047))))) = true) := by
    decide
  have hdis : ¬ (ss_disabling (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2047))) = true) := by
    decide
  have hz : ¬ (w_is0 (ss_sp_of (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2047))) && w_is0 (ss_size_of
        (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2047)))) := by
    decide
  have hsmall : ((ss_size_of (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2047))).toNat : Int) < MINSIGSTKSZ := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_right huoss, ite_eq_right huss]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2047))), check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hat]
  rw [ite_eq_right hmode, ite_eq_right hdis, ite_eq_right hz, ite_eq_left hsmall]
  rfl

/-- **sigaltstack, arm 9: the install succeeds and SETS THE BIT** — the
    only arm that does, and `MINSIGSTKSZ` exactly is accepted (2048). -/
example :
    sigaltstack_spec buf_w zero_w
        (check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
          (BitVec.ofInt 64 2048)))) check_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_sigaltstack_installed check_model) []) := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : ¬ ((!(w_is0 zero_w)) = true) := by decide
  have huss : ¬ (w_is0 buf_w = true) := by decide
  have hat : sigaltstack_at
      (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
        (BitVec.ofInt 64 2048))) buf_w
      = some (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2048)) := by
    decide
  have hmode : ¬ ((!(ss_mode_ok (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2048))))) = true) := by
    decide
  have hdis : ¬ (ss_disabling (ss_flags_of
      (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2048))) = true) := by
    decide
  have hz : ¬ (w_is0 (ss_sp_of (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2048))) && w_is0 (ss_size_of
        (ss_bytes (BitVec.ofInt 64 8192) zero_w (BitVec.ofInt 64 2048)))) := by
    decide
  have hsmall : ¬ (((ss_size_of (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2048))).toNat : Int) < MINSIGSTKSZ) := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_right huoss, ite_eq_right huss]
  simp only [bind]
  refine ⟨check_input_at (all_mem buf_w (ss_bytes (BitVec.ofInt 64 8192) zero_w
      (BitVec.ofInt 64 2048))), check_model, [], [], rfl, ?_, rfl⟩
  simp only [check_input_at, hat]
  rw [ite_eq_right hmode, ite_eq_right hdis, ite_eq_right hz, ite_eq_right hsmall]
  simp only [bind, seqSpec]
  exact ⟨(), with_sigaltstack_installed check_model, [], [], rfl, rfl, rfl⟩

/-- …and the bit it leaves is what arm 1 reads: the NEXT `sigaltstack` is
    UNMODELED, because a recorded non-zero size makes `on_sig_stack` a
    question about a stack pointer the model does not carry. -/
example :
    sigaltstack_spec zero_w zero_w check_input
        (with_sigaltstack_installed check_model) .unmodeled := by
  have hinst : m_sigaltstack_installed (with_sigaltstack_installed check_model)
      = true := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hinst]
  rfl

/-- **sigaltstack, arm 2: a non-NULL `uoss` is declined** — the `ss_flags`
    it would report carries the bit execve does not reset, so no state of
    this model can answer it. -/
example :
    sigaltstack_spec zero_w buf_w check_input check_model .unmodeled := by
  have hinst : ¬ (m_sigaltstack_installed check_model = true) := by decide
  have huoss : (!(w_is0 buf_w)) = true := by decide
  simp only [sigaltstack_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hinst, ite_eq_left huoss]
  rfl

/-- **`sigabrt_blocked` reads bit 5** — `sigmask(SIGABRT)` is 32 — so a
    mask with every bit but SIGABRT's set is "not blocked". -/
example : sigabrt_blocked all_ones = true := by decide
example : sigabrt_blocked zero_w = false := by decide
example : sigabrt_blocked (BitVec.ofInt 64 32) = true := by decide
example : sigabrt_blocked (BitVec.ofInt 64 31) = false := by decide

/-- The tid `send_sigabrt`'s checks pin in these examples. -/
private def five_w : word := BitVec.ofInt 64 5

/-- A second tid, for tgkill's `tgid` mismatch. -/
private def seven_w : word := BitVec.ofInt 64 7

/-- `SIGABRT` as it reaches the spec, post-`int32`: 6. -/
private def sigabrt_w : word := BitVec.ofInt 64 SIGABRT

/-- A model whose task HAS declared the abort terminal. -/
private def abort_model : Model := with_abort_terminal true check_model

/-- …and whose tid is pinned to 5, the tid `__init_tp` seeds from
    `set_tid_address`. -/
private def tid_model : Model := with_tid five_w abort_model

/-- **tkill: with the declaration OFF the only outcome is `unmodeled`**,
    for every argument shape — the source half of
    `tkill_spec_off_unmodeled`, at concrete arguments. -/
example : tkill_spec five_w six_w check_input check_model .unmodeled := by
  have hoff : (!(m_abort_terminal check_model)) = true := by decide
  simp only [tkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hoff]
  rfl

/-- …and `tgkill` likewise. -/
example : tgkill_spec five_w five_w six_w check_input check_model .unmodeled := by
  have hoff : (!(m_abort_terminal check_model)) = true := by decide
  simp only [tgkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hoff]
  rfl

/-- **tkill: `pid <= 0` is -EINVAL** once the declaration is on, tested
    before the task is looked at. -/
example :
    tkill_spec zero_w zero_w check_input abort_model
      (.ok (mkEffect (errno_ret EINVAL) [] []) abort_model []) := by
  have ha : ¬ ((!(m_abort_terminal abort_model)) = true) := by decide
  have hp : (!(pid_positive zero_w)) = true := by decide
  simp only [tkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha, ite_eq_left hp]
  rfl

/-- **tkill: signal 0 is the permission probe, and it is UNMODELED** — it
    passes `tkill_sig_valid` and is not SIGABRT, so the answer would be
    whatever `security_task_kill` says. -/
example : tkill_spec five_w zero_w check_input tid_model .unmodeled := by
  have ha : ¬ ((!(m_abort_terminal tid_model)) = true) := by decide
  have hp : ¬ ((!(pid_positive five_w)) = true) := by decide
  have htid : m_tid tid_model = some five_w := by decide
  have hpe : ¬ ((!(five_w == five_w)) = true) := by decide
  have hsv : ¬ ((!(tkill_sig_valid zero_w)) = true) := by decide
  have hab : ¬ ((zero_w == BitVec.ofInt 64 SIGABRT) = true) := by decide
  simp only [tkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha, ite_eq_right hp]
  simp only [tkill_self]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha]
  simp only [htid]
  rw [ite_eq_right hpe, ite_eq_right hsv, ite_eq_right hab]
  rfl

/-- **tkill: an UNBLOCKED SIGABRT kills** — `send_sigabrt`'s second branch,
    which is the process's death: the model's `procst_killed` is set and
    the 0 the spec returns is never observed. -/
example :
    tkill_spec five_w sigabrt_w check_input tid_model
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_killed (BitVec.ofInt 64 SIGABRT) tid_model) []) := by
  have ha : ¬ ((!(m_abort_terminal tid_model)) = true) := by decide
  have hp : ¬ ((!(pid_positive five_w)) = true) := by decide
  have htid : m_tid tid_model = some five_w := by decide
  have hpe : ¬ ((!(five_w == five_w)) = true) := by decide
  have hsv : ¬ ((!(tkill_sig_valid sigabrt_w)) = true) := by decide
  have hab : (sigabrt_w == BitVec.ofInt 64 SIGABRT) = true := by decide
  have hblk : ¬ (sigabrt_blocked (m_sigmask tid_model) = true) := by decide
  simp only [tkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha, ite_eq_right hp]
  simp only [tkill_self]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha]
  simp only [htid]
  rw [ite_eq_right hpe, ite_eq_right hsv, ite_eq_left hab]
  simp only [send_sigabrt]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right hblk]
  simp only [seqSpec, bind]
  exact ⟨(), with_killed (BitVec.ofInt 64 SIGABRT) tid_model, [], [], rfl, rfl, rfl⟩

/-- …and the DEATH it produces is readable as such: `m_killed` is
    `some 6`, which is what `Run.sstep_killed` consumes. -/
example : m_killed (with_killed (BitVec.ofInt 64 SIGABRT) tid_model)
    = some (BitVec.ofInt 64 SIGABRT) := rfl

/-- **tkill: a BLOCKED SIGABRT is pending, not fatal** — `send_sigabrt`'s
    first branch: the model is not killed, and the bit
    `with_sigabrt_pending` sets is what `rt_sigprocmask`'s delivery
    (`sigmask_deliver_model`) reads later. -/
example :
    tkill_spec five_w sigabrt_w check_input
        (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model)
      (.ok (mkEffect (BitVec.ofInt 64 0) [] [])
        (with_sigabrt_pending
          (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model)) []) := by
  have ha : ¬ ((!(m_abort_terminal
      (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model))) = true) := by
    decide
  have hp : ¬ ((!(pid_positive five_w)) = true) := by decide
  have htid : m_tid (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model)
      = some five_w := by decide
  have hpe : ¬ ((!(five_w == five_w)) = true) := by decide
  have hsv : ¬ ((!(tkill_sig_valid sigabrt_w)) = true) := by decide
  have hab : (sigabrt_w == BitVec.ofInt 64 SIGABRT) = true := by decide
  have hblk : sigabrt_blocked (m_sigmask
      (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model)) = true := by
    decide
  simp only [tkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha, ite_eq_right hp]
  simp only [tkill_self]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha]
  simp only [htid]
  rw [ite_eq_right hpe, ite_eq_right hsv, ite_eq_left hab]
  simp only [send_sigabrt]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_left hblk]
  simp only [seqSpec, bind]
  exact ⟨(), with_sigabrt_pending
      (with_sigmask (BitVec.ofInt 64 sigabrt_mask.toNat) tid_model),
    [], [], rfl, rfl, rfl⟩

/-- **tgkill: a `tgid` that is not the caller's own is -ESRCH** — one
    thread, one group, so the mismatch is decidable here. -/
example :
    tgkill_spec seven_w five_w sigabrt_w check_input tid_model
      (.ok (mkEffect (errno_ret ESRCH) [] []) tid_model []) := by
  have ha : ¬ ((!(m_abort_terminal tid_model)) = true) := by decide
  have hp : ¬ ((!(pid_positive five_w && pid_positive seven_w)) = true) := by decide
  have htid : m_tid tid_model = some five_w := by decide
  have hpe : ¬ ((!(five_w == five_w)) = true) := by decide
  have hte : (!(seven_w == five_w)) = true := by decide
  simp only [tgkill_spec]
  simp only [getModelSpec, bind_getModel]
  rw [ite_eq_right ha, ite_eq_right hp]
  simp only [htid]
  rw [ite_eq_right hpe, ite_eq_left hte]
  rfl

/-- **`how_valid` accepts exactly `{SIG_BLOCK, SIG_UNBLOCK, SIG_SETMASK}`** —
    0, 1 and 2 — and `how` is read as the low half of the register
    (`Syscall.how32`), so the comparison is against the low-half values. -/
example : how_valid sig_block_w = true := by decide
example : how_valid sig_unblock_w = true := by decide
example : how_valid sig_setmask_w = true := by decide
example : how_valid bad_how = false := by decide
example : how_valid (BitVec.ofInt 64 (-1)) = false := by decide

/-- `sigmask_apply` is `sigorsets` for SIG_BLOCK and `sigandnsets` for
    SIG_UNBLOCK: blocking adds bits, unblocking removes them, SETMASK
    replaces the mask outright. -/
example : sigmask_apply sig_block_w (BitVec.ofInt 64 3) (BitVec.ofInt 64 4)
    = BitVec.ofInt 64 7 := by decide
example : sigmask_apply sig_unblock_w (BitVec.ofInt 64 7) (BitVec.ofInt 64 3)
    = BitVec.ofInt 64 4 := by decide
example : sigmask_apply sig_setmask_w (BitVec.ofInt 64 7) (BitVec.ofInt 64 3)
    = BitVec.ofInt 64 3 := by decide

/-- **`sigmask_strip` clears bits 8 and 18 and NOTHING ELSE**: the all-ones
    mask comes back as `2^64 - 1 - 262400`, i.e. SIGKILL's and SIGSTOP's
    bits gone and every other bit kept.  `sigmask(SIGKILL)` is bit 8 and
    `sigmask(SIGSTOP)` bit 18, so `262400 = 2^8 + 2^18`. -/
example : (sigmask_strip all_ones).toNat = 2 ^ 64 - 1 - 262400 := by decide
example : (sigmask_strip (BitVec.ofInt 64 256)).toNat = 0 := by decide
example : (sigmask_strip (BitVec.ofInt 64 262144)).toNat = 0 := by decide
example : (sigmask_strip (BitVec.ofInt 64 255)).toNat = 255 := by decide

/-- …so the strip is NOT what `rt_sigaction` does, which REFUSES the two
    signals: blocking SIGKILL succeeds and drops the bit, installing a
    disposition for it is -EINVAL. -/
example : sig_kernel_only sigkill_w = true := by decide
example : sig_valid sigkill_w = true := by decide

/-- **`fs`'s `w_is0` gate on a NULL `nset` is `w_is0`, not a pointer
    test**: the value the dispatcher hands a spec is the register, and
    only the literal 0 is NULL. -/
example : w_is0 zero_w = true := by decide
example : w_is0 buf_w = false := by decide

/-- `Z_to_le_bytes` gives the little-endian encoding `write_oset` stores:
    8 bytes of 0, least significant first. -/
example : Z_to_le_bytes NSIG_BYTES.toNat (0 : Int) = [0, 0, 0, 0, 0, 0, 0, 0] := by
  decide
example : (Z_to_le_bytes NSIG_BYTES.toNat (0 : Int)).length = 8 := by decide

/-! ### The lemmas, re-read as checks

    `sigmask_strip_launchable` and `sigmask_apply_launchable` are proved
    above, so these are instantiations rather than new arguments: the
    whole-run half of `Run.valid_sigmask` holds for the strip and for
    every `how`. -/

/-- The strip of ANY word is launchable. -/
example (w : word) : mask_launchable (sigmask_strip w) :=
  sigmask_strip_launchable w

/-- …and so is an install over two launchable masks, for every `how` —
    including the undefined ones, which is inert rather than wrong
    because `how_valid` refuses them before the install runs. -/
example (how old new : word) (ho : mask_launchable old) (hn : mask_launchable new) :
    mask_launchable (sigmask_apply how old new) :=
  sigmask_apply_launchable how old new ho hn

/-- The delivery is plain `with_sigmask` when nothing is pending — the
    compatibility claim `set_sigmask_deliver_no_pending` states, at a
    concrete mask. -/
example (new : word) : m_sigmask (with_sigmask new check_model) = new := rfl

/-- The entry mask `oset` reports is the mask the call STARTED with, not
    the one it installs: `check_model`'s is 0, and the masking example
    above installs `2^64 - 1 - 262400` — the pair the arm-2 note names as
    the mistake a reimplementation makes. -/
example : m_sigmask check_model = zero_w := rfl

end LinuxSem.LinuxProcessSem.Sys.Kernel.Signal
