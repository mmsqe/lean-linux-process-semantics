/-
  * LinuxProcessSem.Checks.ProcessCreation — process creation, pinned

  The case for this file, at length:

  > Not part of the trusted specification: this file is QA on the
  > definitions, in the sense of [Checks.Examples]'s header.  It earns
  > its place under that file's FIRST reason — every statement here is
  > UNIVERSALLY QUANTIFIED over models, arguments and memories, which no
  > finite set of traces can establish.  One run can show
  > that ONE flag word was declined, or that ONE forged zero was
  > refused; only a [forall] can say that every one is.
  >
  > ** What this pins, and why it is not decoration
  >
  > Three arguments in this development are load-bearing and rest on
  > something stated here.  Two rest on a syscall NUMBER being outside
  > the modeled surface; the middle one rests on a FLAG WORD:
  >
  > - [State.access_okb] is claimed EXACT rather than an
  >   under-approximation — a claim scoped to a build with [CONFIG_MMU]
  >   and without [CONFIG_ALTERNATE_USER_ADDRESS_SPACE], for reasons
  >   this file does not pin and the note below records.  What it does
  >   pin: riscv64's [access_ok] wraps its address in [untagged_addr],
  >   which is the identity exactly when [PMLEN = 0].  [PMLEN] is zeroed
  >   on every [execve] and is written
  >   afterwards only by [set_tagged_addr_ctrl]
  >   (arch/riscv/kernel/process.c), which has TWO callers:
  >   [prctl(PR_SET_TAGGED_ADDR_CTRL, ...)] (kernel/sys.c, [SYSCALL_DEFINE5(prctl)])
  >   and [PTRACE_SETREGSET] with [NT_RISCV_TAGGED_ADDR_CTRL]
  >   (arch/riscv/kernel/ptrace.c, [tagged_addr_ctrl_set]).  Declining
  >   option 55 of 167, and all of 117, rules out both routes FROM
  >   INSIDE the model: the traced process cannot enable masking on
  >   itself.  An external tracer is a separate matter, below.  The
  >   prctl half is one OPTION, not the whole NUMBER; why
  >   the weaker-looking statement carries the same weight is at
  >   [prctl_option_unmodeled] below.
  > - [Fork.set_tid_address_spec] accepts and ignores its [tidptr], and
  >   NOT for any reason on this list.  [set_tid_address] records the
  >   pointer in the CALLER's [current->clear_child_tid], while
  >   [copy_process] sets a different task's [p->clear_child_tid] under
  >   [CLONE_CHILD_CLEARTID]; the two share only a field name.  The
  >   caller's write fires from [mm_release] when the CALLER exits or
  >   execs, gated on [mm_users > 1], so what rules it out is that this
  >   model admits no second holder of an mm — a closed-world statement
  >   about the environment, not a flag test.  See that spec's header;
  >   do not re-derive it from the bit below.
  > - [Fork.clone_spec]'s header argues that the SIGCHLD the admitted
  >   flag word requests, and which the child's exit sends to this
  >   process, comes to nothing.  The argument has two halves — a
  >   [SIG_DFL] SIGCHLD is discarded, a blocked one is queued but sets
  >   no [TIF_SIGPENDING].  NEITHER half is a statement about a
  >   declined number: 134 and 135 are both modeled.  What
  >   carries the whole argument is [Signal.sigaction_accepted], which
  >   excludes SIGCHLD, so an install for it fails closed at the SIGNAL
  >   rather than at the number.  A changeable mask does not reopen
  >   anything: unblocking a queued SIGCHLD hands it to [get_signal],
  >   which finds [SIG_DFL] and [sig_kernel_ignore] and discards it, so
  >   the blocked case funnels into the unblocked one rather than into
  >   a third.  The exclusion is pinned in
  >   [Checks.Cases.Kernel.Signal.rt_sigaction_sigchld_unmodeled].
  >
  > Not everything in the neighbourhood is.  [State.access_okb]'s note
  > ALSO relies on there being no second process to be the tracer, and
  > nothing about 220 gives it that — not its parent-side model, and
  > not a decline either.  A tracer is an
  > independently started process, and a child this model does not step
  > could equally attach to its parent and [PTRACE_POKEDATA] it with
  > [CLONE_VM] clear.  That half is a closed-world assumption about the
  > ENVIRONMENT (Yama's [ptrace_scope], uid separation) — undischarged.
  > What this file pins for it is the IN-MODEL half: [prctl]'s tagging
  > option and all of 117 are declined, so the traced process cannot
  > enable masking on itself.
  >
  > And the tagging argument is not the only precondition that note has.
  > [__access_ok] returns true for every range, ahead of the comparison
  > [access_okb] transcribes, under [CONFIG_ALTERNATE_USER_ADDRESS_SPACE]
  > or with [CONFIG_MMU] off; on such a build [access_okb] declines
  > ranges the kernel accepts and is an under-approximation whatever
  > [PMLEN] is.  riscv cannot select the first (arch/Kconfig, [config
  > ALTERNATE_USER_ADDRESS_SPACE]: no prompt, and selected only by
  > parisc, s390, [SPARC64] and m68k, v6.9 through v6.17), so that half
  > is closed by the architecture.  The second is a real choice —
  > arch/riscv/Kconfig's [config MMU] is a prompted bool with no [depends
  > on], and arch/riscv/configs/nommu_virt_defconfig ships an RV64 build
  > with it off — so the claim holds by BUILD CONFIGURATION, which no
  > decline proved here touches and no syscall number can rule out.
  >
  > Prose alone does not protect these arguments: adding an arm for
  > [prctl] would leave every one of those comments false with a
  > green build.  The corollaries below are proved DIRECTLY against
  > [syscall_spec] rather than through [Specs.modeled_sysnos] and its
  > companion file, so each one is a tripwire: give any of these numbers
  > an arm and its proof stops closing.
  >
  > ** What it does NOT claim
  >
  > Nothing here says these syscalls SHOULD stay unmodeled, and nothing
  > here is a model of them.  Declining is what the dispatcher
  > does; this file states it, in the one place a future change would
  > have to look at.

  PROOF ROUTE.  The clone-resolution group — [clone_never_returns_zero]
  and its clone3 twin, [clone_resolve_declines_or_sets_children],
  [clone_success_sets_children], [check_clone_success_sets_children],
  [clone_open_file_unmodeled], [clone3_sharing_flags_unmodeled] — the
  [wait4] pair, [setsid_not_unmodeled], and the concrete `Example`
  companions of all four numbers are all `Ok`-inversions through
  [clone_resolve]'s `bind`/`alt`/`choose` chain.  They go through the
  CHECKER, whose completeness lemmas are that inversion already staged,
  and each says at its own site which step of the route it takes.  Eight
  local helper declarations carry what they share — the five inversion
  steps [clone_resolve_ok_inv], [clone_ret_ne_zero],
  [clone_spec_ok_resolve], [clone3_spec_ok_resolve],
  [wait4_is_wait4_spec]; two one-line facts,
  [m_has_children_with_children] and [word_eq_zero_of_w_is0]; and the
  model [pc_model_setsid_succeeded], beside the `pc_model` /
  `pc_model_open_file` scaffolding — so that a reader counting
  declarations does not mistake them for arms.

  The tripwires this tree's prose cites are all here: [clone_sharing_bits]
  and [clone_sharing_flags_unmodeled] (`State.lean`,
  `Sys/Kernel/Sys.lean`, `StateMemory.lean`), [prctl_modeled_options_are],
  [prctl_option_unmodeled] and [prctl_tagged_addr_ctrl_unmodeled]
  (`StateMemory.lean`, `Sys/Kernel/Sys.lean`), [ptrace_unmodeled]
  (`StateMemory.lean`, `Sys/Kernel/Exit.lean`), [execve_unmodeled],
  [execveat_unmodeled], [getrlimit_unmodeled] and [setrlimit_unmodeled]
  (`Sys/Fs/File.lean`), and the three `is_*_spec` characterizations plus
  the run-level section.

  Spelling.  `Z` is `Int`, `bv_unsigned w` is
  `(w.toNat : Int)`, `Z_to_bv n z` is `BitVec.ofInt n z`, `Z.land` /
  `Z.lor` are `Sys.Uapi.z_land` / `Sys.Uapi.z_lor` (Lean core's `Int`
  has no bitwise and/or; these are through `Nat`, and every operand here
  is a literal or a `bv_unsigned`, so the two agree on every operand this
  file has), `fold_left` is `List.foldl` with the list and the
  accumulator in the same order, `In` is `∈`, and
  `mkSpecArm n f` is `arm n f`.  `outcome` is
  `Outcome SyscallEffect Model event`, `Ok` / `Unmodeled` are `.ok` /
  `.unmodeled`, `Some` is `some`, and the record projections take the
  record as their argument (`eff_ret e` for `e.eff_ret`), which is what
  makes `eff_ret eff` read as written.
-/
import LinuxSem.Checks.ExecutableSpecs
import LinuxSem.Checks.Sys.DispatchCompute
import LinuxSem.LinuxProcessSem.Run
import LinuxSem.LinuxProcessSem.StackLayout
import LinuxSem.LinuxProcessSem.MemImageType
import LinuxSem.LinuxProcessSem.StateMemory

set_option autoImplicit false

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.Specs (syscall_spec)
open LinuxSem.LinuxProcessSem.Sys.Dispatch
open LinuxSem.LinuxProcessSem.Sys.SyscallTable
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Kernel.Fork
open LinuxSem.LinuxProcessSem.Sys.Kernel.Exit
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Fork
open LinuxSem.Checks.Sys.Kernel.Exit
open LinuxSem.Checks.Sys.Kernel.Sys

namespace LinuxSem.Checks.ProcessCreation

/-! ## The local shims

    Transparent aliases, so no statement below changes meaning. -/

/-- `bv_unsigned`: the unsigned value of a bitvector, in
    `Int` so that range arithmetic does not wrap. -/
abbrev bv_unsigned {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)

/-- `Z_to_bv`: an `Int` re-wrapped at width `n`. -/
abbrev Z_to_bv (n : Nat) (z : Int) : BitVec n := BitVec.ofInt n z

/-- `in_sysno` as a function (a `SyscallInput` field projection). -/
abbrev in_sysno (i : SyscallInput) : word := i.in_sysno

/-- `eff_ret` as a function. -/
abbrev eff_ret (e : SyscallEffect) : word := e.eff_ret

/-- `mkCfg`: a run-level configuration is the machine state and the
    model, and nothing else (`Run.config`'s two fields). -/
abbrev mkCfg (ms : machine_state) (model : Model) : config := ⟨ms, model⟩

/- =========================================================================
   Where the general list-to-dispatcher link belongs, and what it says

   [Checks.DispatchSurface] is a companion QA file.  Neither file
   [Require]s the other — this one sits over [Checks.ExecutableSpecs]
   and that one over [Checks.Progress] — and this one names it rather
   than importing it because the tripwires below would be WEAKER if
   they went through it, not because it is missing.

   [Specs.modeled_sysnos] is documentation: the trace semantics never
   consults it, so on its own it is a comment that happens to be typed.
   The general link to [Specs.syscall_spec] is what that companion file
   proves, in BOTH directions.  Neither direction is used below — the
   tripwires are deliberately independent of both — but which statements
   are and are not true about that list is what the arguments above rest
   on, so it is worth being exact about them here.

   - FAIL-CLOSED: outside the list the dispatcher admits nothing but
     [Unmodeled] ([syscall_spec_unmodeled_outside] there), with the
     introduction form — outside the list [Unmodeled] IS an admissible
     outcome — derived from it in two steps via [Progress.receptive]
     ([syscall_spec_declines_outside]).  The introduction form alone
     would be strictly weaker: [Sys] is a relation, so "admits
     [Unmodeled]" does not by itself rule out a number that both
     declines and answers.  This is the direction the coverage argument
     needs.

   - THE CONVERSE: every number the list DOES name is answered on SOME
     input ([modeled_sysnos_dispatched] there).  That is a theorem, and
     together with the first direction it makes [modeled_sysnos] exactly
     the dispatched set ([modeled_sysnos_exact]).

   What is NOT true is the universally quantified reading — "a number
   the list names never yields [Unmodeled]".  That is not the converse
   of anything above: a listed number still declines the argument
   shapes its own spec rejects, which is the whole point of
   [Monad.unmodeled].

   `Checks/DispatchSurface.lean` states `modeled_sysnos_exact`, which makes
   the list exactly the dispatched set, so the names above are citations of
   a present companion.
   ========================================================================= -/

/- =========================================================================
   The tripwires — one per number, proved against the dispatcher itself

   Deliberately NOT proved via the companion file's
   [syscall_spec_declines_outside].  Going through
   the list would make each of these a statement about
   [modeled_sysnos], and a change that added an arm without touching
   the list would leave them all provable.  Proved against
   [syscall_spec], adding an arm for the number breaks the proof, which
   is the point.
   ========================================================================= -/

/-- The number is not in `Sys.SyscallTable.spec_table`, so the lookup is
    `none` and the dispatcher declines.  This is one computation over the
    table, and it breaks, as it should, the moment someone gives the
    number an arm.

    The five decline lemmas below would be one line of a single tactic.
    Lean has no `Ltac`, so the computation is written out per number:
    `lookup_arm spec_table N` is `none` because no arm in the table
    answers to `N`, which `simp` reads off the list the same way
    `Checks/Common/MmapSim.lean` reads off the arm that DOES answer. -/
theorem lookup_arm_none_221 : lookup_arm spec_table 221 = none := by
  simp [lookup_arm, spec_table, arm]

theorem lookup_arm_none_281 : lookup_arm spec_table 281 = none := by
  simp [lookup_arm, spec_table, arm]

theorem lookup_arm_none_163 : lookup_arm spec_table 163 = none := by
  simp [lookup_arm, spec_table, arm]

theorem lookup_arm_none_164 : lookup_arm spec_table 164 = none := by
  simp [lookup_arm, spec_table, arm]

theorem lookup_arm_none_117 : lookup_arm spec_table 117 = none := by
  simp [lookup_arm, spec_table, arm]

/-- [clone] (220) and [clone3] (435) — MODELED, parent-side, and stated
    here in the negative.  The model does not cover all of clone: its
    spec answers exactly one flag word, [SIGCHLD], and the
    three statements below say what it still declines.

    [Fork.clone_spec]'s header has the reasoning.  In short: the model
    creates no second process, so a child's effect on the PARENT is the
    only thing that can make ignoring it unsound.  The flag bits that
    carry such an effect are outside the admitted word — but flag bits
    are not the only carrier, and that header names five channels no
    flag test can close.  What a lemma buys over a comment is that
    widening the flag test breaks the build. -/
def CLONE_VM             : Int := 0x00000100
def CLONE_FS             : Int := 0x00000200
def CLONE_FILES          : Int := 0x00000400
def CLONE_SIGHAND        : Int := 0x00000800
def CLONE_PIDFD          : Int := 0x00001000
def CLONE_VFORK          : Int := 0x00004000
def CLONE_THREAD         : Int := 0x00010000
def CLONE_SYSVSEM        : Int := 0x00040000
def CLONE_SETTLS         : Int := 0x00080000
def CLONE_PARENT_SETTID  : Int := 0x00100000
def CLONE_CHILD_CLEARTID : Int := 0x00200000
def CLONE_CHILD_SETTID   : Int := 0x01000000
def CLONE_IO             : Int := 0x80000000

/-- The bits [Fork.clone_fork_flags_b] has to keep out.  Most are bits
    whose absence something elsewhere in this development STATES;
    [CLONE_SYSVSEM] and [CLONE_IO] are here with nothing in this
    development resting on them, so the list is not merely the bits some
    argument happens to cite.  It is not the complete set of bits a
    child could share either — [CLONE_PARENT], which redirects the exit
    signal to the GRANDparent, is absent, and so is the ptrace pair —
    and it does not need to be: the gate is the [clone_fork_flags_b]
    allowlist and this lemma is a sufficient condition over it, not the
    thing doing the refusing.  Five kinds:

    - the child reaches back into the parent — a shared address space
      ([CLONE_VM], and [CLONE_VFORK] which suspends the parent inside
      one), a shared descriptor table ([CLONE_FILES]), a shared
      [fs_struct] whose [chdir] moves the parent's [AT_FDCWD]
      ([CLONE_FS]), a shared System V semaphore undo list
      ([CLONE_SYSVSEM]) and a shared [io_context] ([CLONE_IO]) — the two
      this development states nothing about, since it models neither
      semaphores nor io priorities;
    - the call itself touches the parent — a new descriptor installed in
      the parent's own table and an int written through its
      [parent_tidptr] ([CLONE_PIDFD]), and the child tid written through
      the same pointer ([CLONE_PARENT_SETTID]);
    - a THREAD GROUP with more than one member ([CLONE_THREAD], and
      [CLONE_SIGHAND] which it requires).  Not because the CALLER would
      stop leading it — it would not — but because
      [Sys.getpid_spec = Fork.set_tid_address_spec] needs every task
      the model describes to be its own group leader, and a task created
      with [CLONE_THREAD] whose leader later exits is not.  See
      [Fork.set_tid_address_spec] and [State.m_tid]'s note;
    - a write fires when a CHILD exits ([CLONE_CHILD_CLEARTID]).  This
      is a reason to decline the BIT; it is NOT what
      [Fork.set_tid_address_spec] rests on, which is a different writer
      into a same-named field — see the note above;
    - the call would use an argument this spec does not fetch.
      [CLONE_CHILD_SETTID] gates the read of [child_tidptr]; on riscv64
      [CLONE_SETTLS] copies nothing — [copy_thread] assigns
      [childregs->tp = args->tls] — but it is the bit that makes [tls]
      mean anything.  TWO comments say in so many words that neither
      argument is read: [Fork.clone_spec]'s header and the dispatcher's own
      note at the [clone] arm.

    Every citation of the lemma below names a bit in THIS list, which is
    the point of listing more than the address-space pair: widening
    [Fork.clone_fork_flags_b] to accept any of them stops the proof
    closing rather than silently falsifying the comment that cites it. -/
def clone_sharing_bits : Int :=
  [CLONE_VM, CLONE_FS, CLONE_FILES, CLONE_SIGHAND, CLONE_PIDFD,
   CLONE_VFORK, CLONE_THREAD, CLONE_SYSVSEM, CLONE_SETTLS,
   CLONE_PARENT_SETTID, CLONE_CHILD_CLEARTID, CLONE_CHILD_SETTID,
   CLONE_IO].foldl z_lor 0

theorem clone_sharing_flags_unmodeled (flags : word) (i : SyscallInput) (m : Model)
    (Hbit : z_land (bv_unsigned flags) clone_sharing_bits ≠ 0) :
    clone_spec flags i m .unmodeled := by
  unfold clone_spec
  by_cases hf : clone_fork_flags_b flags = true
  · simp only [hf, ite_true]
    exfalso
    have hflags : flags = Z_to_bv 64 SIGCHLD := by
      simpa only [clone_fork_flags_b, bv_eqb, beq_iff_eq] using hf
    rw [hflags] at Hbit
    exact Hbit (by decide)
  · simp only [hf]
    exact unmodeled_intro i m

/-- No admitted errno encodes 0. -/
theorem clone_errno_ret_nonzero (e : Int) (Hin : e ∈ clone_errnos) :
    errno_ret e ≠ Z_to_bv 64 0 := by
  simp only [clone_errnos, List.mem_cons, List.not_mem_nil, or_false] at Hin
  rcases Hin with h | h | h | h <;> (subst h; decide)

/-- THE ARM IS THE ONE IT CLAIMS TO BE.  Every lemma above pins what
    [clone] and [clone3] REFUSE, and a refusal lemma characterises its
    number completely only because [Unmodeled] is the whole answer.  The
    positive direction needs saying too: that 220 and 435 reach
    [Fork.clone_spec] and [Fork.clone3_spec] and not some other total
    spec that happens to refuse the same inputs.  [Sys.Dispatch.dispatch_arm]
    already states that biconditional for any table and arm, so this
    costs a lookup and a [reflexivity]. -/
theorem clone_is_clone_spec (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hno : bv_unsigned (in_sysno i) = 220) :
    (syscall_spec i m o ↔ clone_spec (in_arg i 0) i m o) := by
  unfold syscall_spec
  apply dispatch_arm spec_table i m o (arm 220 (fun i => clone_spec (in_arg i 0)))
  rw [show ((in_sysno i).toNat : Int) = 220 from Hno]
  simp [lookup_arm, spec_table, arm]

theorem clone3_is_clone3_spec (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hno : bv_unsigned (in_sysno i) = 435) :
    (syscall_spec i m o ↔ clone3_spec (in_arg i 0) (in_arg i 1) i m o) := by
  unfold syscall_spec
  apply dispatch_arm spec_table i m o
    (arm 435 (fun i => clone3_spec (in_arg i 0) (in_arg i 1)))
  rw [show ((in_sysno i).toNat : Int) = 435 from Hno]
  simp [lookup_arm, spec_table, arm]

/-- [execve] (221).  A successful exec replaces the address space, which
    this development cannot express at all: the loaded segments are a
    SECTION PARAMETER of [Run.WithMemImage], fixed for the whole run, so
    no step can replace them.  [begin_new_exec] (fs/exec.c) also resets
    signal dispositions, closes the close-on-exec descriptors
    ([do_close_on_exec]) and — on riscv64 — zeroes the pointer-masking
    length through [activate_mm] and [flush_thread].  The failure returns
    are not separable either: [do_open_execat] opens with [MAY_EXEC], and
    [Fs.Fs] records no file modes, so a spec that answered [-EFAULT] for
    a bad argv would be REJECTING the [-EACCES] a real kernel returns for
    the same call on a non-executable file. -/
theorem execve_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 221) : syscall_spec i m .unmodeled := by
  have h : ((in_sysno i).toNat : Int) = 221 := Hno
  unfold syscall_spec
  apply dispatch_unmodeled
  rw [h]
  exact lookup_arm_none_221

/-- [execveat] (281).  [execve] plus a dirfd and [AT_EMPTY_PATH] /
    [AT_SYMLINK_NOFOLLOW]; [execveat(AT_FDCWD, p, a, e, 0)] is
    [execve(p, a, e)].  Everything said of 221 applies, over a resolution
    base the model would additionally have to carry. -/
theorem execveat_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 281) : syscall_spec i m .unmodeled := by
  have h : ((in_sysno i).toNat : Int) = 281 := Hno
  unfold syscall_spec
  apply dispatch_unmodeled
  rw [h]
  exact lookup_arm_none_281

/-- [getrlimit] (163) and [setrlimit] (164), registered because
    arguments rest on each of them having no arm, and the two
    arguments are different ones.

    164 WRITES.  [State.limst_nofile] holds ONE soft RLIMIT_NOFILE for a
    whole run and [Fs.File.dup3_spec] compares [newfd] against it, which
    are both claims that nothing modeled can change the limit.  Three
    system calls reach [do_prlimit] with a [new_rlim] (kernel/sys.c,
    Linux v6.18.46, commit 1f99e9ab748f): 164, its compat twin, and
    [prlimit64] (261).  261 IS inside [Specs.modeled_sysnos], and is
    closed by an arm rather than by this register —
    [Kernel.Sys.prlimit64_spec] declines every resource but RLIMIT_CORE
    — which is why only 164 needs an entry here.  Everything else that
    writes [signal->rlim] runs at exec, at boot or on a core dump, and
    is out of reach for the same reason 221 is; [Run.valid_nofile]
    enumerates those.

    163 READS, and passes [NULL] for [new_rlim] (kernel/sys.c,
    [SYSCALL_DEFINE2(getrlimit)]), so it changes nothing.  Its decline
    is load-bearing on the other side: no modeled syscall reads the
    limit back.

    Neither is modeled, and neither is merely undone work: they enter
    [do_prlimit] DIRECTLY, skipping [check_prlimit_permission] and the
    [security_task_prlimit] hook (kernel/sys.c, Linux v6.18.46, commit
    1f99e9ab748f), so they are a different call from [prlimit64] and
    would need their own argument.  musl reaches the limits through
    [prlimit64] regardless — [Kernel.Sys.prlimit64_spec] says why. -/
theorem getrlimit_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 163) : syscall_spec i m .unmodeled := by
  have h : ((in_sysno i).toNat : Int) = 163 := Hno
  unfold syscall_spec
  apply dispatch_unmodeled
  rw [h]
  exact lookup_arm_none_163

theorem setrlimit_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 164) : syscall_spec i m .unmodeled := by
  have h : ((in_sysno i).toNat : Int) = 164 := Hno
  unfold syscall_spec
  apply dispatch_unmodeled
  rw [h]
  exact lookup_arm_none_164

/-- [ptrace] (117).  The OTHER caller of [set_tagged_addr_ctrl], through
    [PTRACE_SETREGSET] with [NT_RISCV_TAGGED_ADDR_CTRL]
    (arch/riscv/kernel/ptrace.c).  Both routes arrived in v6.13 in one
    series, so there is no version window in which 167 alone would have
    sufficed — which is why this number is pinned beside it rather than
    left to the argument about there being no second task. -/
theorem ptrace_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 117) : syscall_spec i m .unmodeled := by
  have h : ((in_sysno i).toNat : Int) = 117 := Hno
  unfold syscall_spec
  apply dispatch_unmodeled
  rw [h]
  exact lookup_arm_none_117

/-- [prctl] (167).  Load-bearing as an ABSENCE, and the ABSENCE IS
    AN OPTION RATHER THAN A NUMBER.  This is the first of the two callers
    of riscv's [set_tagged_addr_ctrl], and so one half of why
    [State.access_okb] is exact.  Modeling any option has a cost: the
    fact moves from membership in [Specs.modeled_sysnos] — a closed
    list — to the body of a multiplexer, where the next option added
    silently decides whether [readv]'s address check is still exact.

    THE ANSWER TO THAT COST IS ANOTHER CLOSED
    LIST.  [Kernel.Sys.prctl_modeled_options] is the set of options the
    arm answers, written as a definition rather than left implicit in a
    [match], and [prctl_modeled_options_are] pins it EXACTLY — not that
    55 is absent from it, which a widening could preserve, but that the
    list is [[PR_CAPBSET_READ]] and nothing else.  So the tripwire keeps
    its shape: an edit that teaches [prctl] a second
    option fails a named proof in this file, and whoever makes that edit
    has to come back here and say what it does to the tagging argument.
    The three statements below are that argument, from the general to
    the particular.
    [PR_SET_TAGGED_ADDR_CTRL] is option 55; the sign-extending shift it
    enables lives in [__untagged_addr_remote]
    (arch/riscv/include/asm/uaccess.h) and is
    applied per uaccess primitive, not once at the syscall boundary, so
    it could not be modeled by masking registers on entry either. -/
theorem prctl_modeled_options_are :
    prctl_modeled_options = [PR_CAPBSET_READ] := rfl

/-- Every option outside that list falls through [prctl_spec]'s first
    test.  Stated over [Syscall.int32] of a0 because that is what the
    dispatcher's arm passes: [prctl]'s [option] is an [int] in
    [SYSCALL_DEFINE5(prctl)], so the kernel never sees the register's
    high half either. -/
theorem prctl_option_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 167)
    (Hopt : bv_unsigned (int32 (in_arg i 0)) ∉ prctl_modeled_options) :
    syscall_spec i m .unmodeled := by
  unfold syscall_spec
  refine (dispatch_arm spec_table i m .unmodeled
    (arm 167 (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1))) ?_).mpr ?_
  · rw [show ((in_sysno i).toNat : Int) = 167 from Hno]
    simp [lookup_arm, spec_table, arm]
  · show prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i m .unmodeled
    unfold prctl_spec
    by_cases ho : ((int32 (in_arg i 0)).toNat : Int) = PR_CAPBSET_READ
    · exfalso
      apply Hopt
      simp only [prctl_modeled_options, List.mem_cons, List.not_mem_nil, or_false]
      exact ho
    · rw [ite_eq_left ho]
      exact unmodeled_intro i m

/-- The particular case the tagging argument needs. -/
theorem prctl_tagged_addr_ctrl_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 167)
    (Hopt : bv_unsigned (int32 (in_arg i 0)) = 55) :
    syscall_spec i m .unmodeled := by
  apply prctl_option_unmodeled i m Hno
  intro hmem
  rw [Hopt] at hmem
  simp only [prctl_modeled_options, PR_CAPBSET_READ, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  exact absurd hmem (by decide)

/-- AND THE FULL CHARACTERIZATION, which is what makes 157's entry as
    strong as its neighbours rather than merely non-vacuous.

    Every other number here is pinned by a decline lemma, and a decline
    lemma says EVERYTHING about that number: [Unmodeled] is the whole
    answer.  [setsid_not_unmodeled] below says much less — it rules out
    one answer, and would still hold if 157 dispatched to some other
    total spec that never declines.  This closes that gap: at 157 the
    dispatcher is [Kernel.Sys.setsid_spec] and nothing else, for every
    input, model and outcome.  Replace the arm and this breaks; remove
    it and [setsid_not_unmodeled] breaks.

    It is free because [Sys.Dispatch.dispatch_arm] already states the
    biconditional for any table and any arm — the table-driven
    dispatcher is what makes a per-number characterization a lookup
    rather than a case analysis over a chain.

    The number is MODELED, so this is the lemma that pins it;
    `setsid_not_unmodeled` — the negative form — is proved further down,
    across the dispatcher.  Neither is the other's corollary: this one
    says what 157 IS, that one says what it is NOT. -/
theorem setsid_is_setsid_spec (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hno : bv_unsigned (in_sysno i) = 157) :
    (syscall_spec i m o ↔ setsid_spec i m o) := by
  unfold syscall_spec
  apply dispatch_arm spec_table i m o (arm 157 (fun _ => setsid_spec))
  rw [show ((in_sysno i).toNat : Int) = 157 from Hno]
  simp [lookup_arm, spec_table, arm]

/- =========================================================================
   What a declined syscall does to a RUN
   ========================================================================= -/

/-- The syscall counterpart of [Run.reaches_unmodeled_intro], which
    covers only the INSTRUCTION arm.  Stated at the configuration level
    so the numbers above compose with it. -/
theorem unmodeled_at_syscall (segs : List Segment) (ms : machine_state) (model : Model)
    (x8 : word) (Hh : m_halted model = none) (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : syscall_spec (sys_input segs ms x8) model .unmodeled) :
    unmodeled_at segs (mkCfg ms model) := by
  refine ⟨Hh, Or.inr ?_⟩
  exact ⟨x8, Hsvc, Hspec⟩

/-- …and what that costs a source binary: reaching such a configuration
    on ANY execution refutes [Equivalence.modeled], so no equivalence
    theorem can be proved about it.  This is the coverage cost of
    declining, stated once and precisely.  It is NOT a soundness risk and
    NOT a vacuous pass: [modeled] is a conjunct of
    [Equivalence.strong_equiv] that the proof must DISCHARGE, so a
    forking source makes the theorem unprovable rather than free. -/
theorem reaches_unmodeled_syscall (segs : List Segment) (c0 : config) (tr : List event)
    (ms : machine_state) (model : Model) (x8 : word)
    (Hstar : star segs c0 tr (mkCfg ms model)) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8)
    (Hspec : syscall_spec (sys_input segs ms x8) model .unmodeled) :
    reaches_unmodeled segs c0 := by
  refine ⟨tr, mkCfg ms model, Hstar, ?_⟩
  exact unmodeled_at_syscall segs ms model x8 Hh Hsvc Hspec

/-- The two composed, at a declined number: a run that reaches a pending
    [execve] is a run this model does not cover.  [clone] (220) is
    modeled parent-side, and 221 is the number a forked child reaches
    immediately afterwards. -/
theorem execve_refutes_coverage (segs : List Segment) (c0 : config) (tr : List event)
    (ms : machine_state) (model : Model) (x8 : word)
    (Hstar : star segs c0 tr (mkCfg ms model)) (Hh : m_halted model = none)
    (Hsvc : ms.ms_svc_pending = some x8) (Hno : bv_unsigned x8 = 221) :
    reaches_unmodeled segs c0 := by
  refine reaches_unmodeled_syscall segs c0 tr ms model x8 Hstar Hh Hsvc ?_
  exact execve_unmodeled (sys_input segs ms x8) model Hno

/- =========================================================================
   The checker agrees — the other half of every statement above
   ========================================================================= -/

/-! The lemmas above are about [Specs.syscall_spec], the definition.  The
    extracted acceptor is [ExecutableSpecs.check_syscall].  These close
    the loop for each number, so the definition and the checker are
    pinned to the same verdict rather than to two independent claims.

    The `Example`s close by `rfl`, not `decide`: `check_result` carries a
    `Model`, so there is no
    `DecidableEq` to `decide` with, and the two sides are closed terms —
    kernel reduction closes them, exactly as `Checks/Cases/Prelude.lean`'s
    header records for the same situation.  `mkEffect` is the
    three-argument form. -/

/- None of the process input's fields reaches the checks below — every
   syscall number here is outside `Specs.modeled_sysnos` and is declined
   before any model state is read — so the ids are an ordinary
   unprivileged pair rather than a claim. -/
def pc_model : Model :=
  init_model [] 0 0 (Z_to_bv 64 sp_window_lo) 0x40000000
    (mkProcInput [] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
                 net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false .Sv48)

def pc_input (n : Int) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 n) [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-- [clone] and [clone3] are modeled, so their examples run the other way
    round: the checker must DECLINE the flag words the spec does not
    accept, and answer the one it does.  [pc_input] passes zero in every
    argument register, which is a flag word of 0 — not [SIGCHLD] — and a
    [clone3] whose [size] is 0. -/
theorem clone_checker_declines_flags_zero :
    check_syscall (pc_input 220) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

theorem clone3_checker_declines_size_zero :
    check_syscall (pc_input 435) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

/-- [clone(SIGCHLD, 0, 0, 0, 0)] against the same model, which has no
    open regular file: a pid inside the envelope is accepted, so is one
    of the four admitted errnos, and 0 — the CHILD's answer — is not.
    These are the concrete companions this section exists for: the
    statements above are about [Specs.syscall_spec], and these run the
    same facts through [ExecutableSpecs.check_syscall], the extracted
    checker. -/
def pc_clone_input : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 220) [Z_to_bv 64 SIGCHLD, 0, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- The success arm records the child: [Kernel.Fork.clone_resolve] calls
    [State.with_children] on this branch, so the post-model is not
    [pc_model].  That is what [Kernel.Exit.wait4_spec]'s -ECHILD gate
    reads, and pinning it here is what makes the two compose. -/
theorem clone_checker_admits_a_pid :
    check_syscall pc_clone_input (mkEffect (Z_to_bv 64 4242) [] []) pc_model
      = .CheckOk (with_children pc_model) [] := rfl

theorem clone_checker_admits_eagain :
    check_syscall pc_clone_input (mkEffect (errno_ret EAGAIN) [] []) pc_model
      = .CheckOk pc_model [] := rfl

theorem clone_checker_refuses_zero :
    check_syscall pc_clone_input (mkEffect 0 [] []) pc_model = .CheckReject := rfl

theorem clone_checker_refuses_the_envelope_bound :
    check_syscall pc_clone_input
      (mkEffect (Z_to_bv 64 PID_MAX_ENVELOPE) [] []) pc_model = .CheckReject := rfl

/-- [ENFILE] is 23 and [EMFILE], which IS admitted, is 24 — so this
    refuses the nearest neighbour of an admitted errno rather than a
    distant one. -/
theorem clone_checker_refuses_another_errno :
    check_syscall pc_clone_input (mkEffect (errno_ret ENFILE) [] []) pc_model
      = .CheckReject := rfl

/-- THE SHARED FILE OFFSET.  The quantified statement is
    [clone_open_file_unmodeled] below; this is its concrete checker
    companion, over one model and one descriptor shape. -/
def pc_model_open_file : Model :=
  with_fds ((Z_to_bv 64 3, FdEntry.FdFile [] (Z_to_bv 64 0)) :: m_fds pc_model) pc_model

theorem clone_checker_declines_with_a_file_open :
    check_syscall pc_clone_input (mkEffect (Z_to_bv 64 4242) [] [])
      pc_model_open_file = .CheckUnmodeled := rfl

/-- Every number below has its quantified statement above; if one of
    these ever has to go, check that the statement went first. -/
theorem execve_checker_unmodeled :
    check_syscall (pc_input 221) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

theorem execveat_checker_unmodeled :
    check_syscall (pc_input 281) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

theorem getrlimit_checker_unmodeled :
    check_syscall (pc_input 163) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

theorem setrlimit_checker_unmodeled :
    check_syscall (pc_input 164) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

theorem ptrace_checker_unmodeled :
    check_syscall (pc_input 117) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

/-- The concrete companions for [prctl].  [pc_input] leaves a0 at 0, which
    is no prctl option at all; [pc_prctl_input 55] is
    [PR_SET_TAGGED_ADDR_CTRL], the option the tagging argument names. -/
def pc_prctl_input (opt : Int) : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 167) [Z_to_bv 64 opt, 0, 0, 0, 0, 0]
    (fun _ => none) (fun _ => none)

theorem prctl_checker_tagged_addr_ctrl_unmodeled :
    check_syscall (pc_prctl_input 55) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

/-- NAMED FOR THE OPTION, NOT THE NUMBER, and deliberately: an
    `Example <syscall>_checker_unmodeled` asserts that the NUMBER has no
    dispatcher arm, and 167 has one. -/
theorem prctl_checker_option_zero_unmodeled :
    check_syscall (pc_input 167) (mkEffect 0 [] []) pc_model = .CheckUnmodeled := rfl

/-- And the other side of the multiplexer, so the two examples above are
    not satisfied by an arm that declines everything: [PR_CAPBSET_READ] on
    a valid capability is 1, and the model is left alone. -/
theorem prctl_checker_capbset_read :
    check_syscall (pc_prctl_input 23) (mkEffect (Z_to_bv 64 1) [] []) pc_model
      = .CheckOk pc_model [] := rfl

/- =========================================================================
   The clone resolution, inverted
   ========================================================================= -/

/-! ### Reading an `Ok` back out of `clone_resolve`

    `clone_resolve` is a `bind`/`alt`/`choose` chain, four levels down.
    This file walks it through the CHECKER instead — the staged-evaluator
    route — and the stage that matters is already built:
    `Checks/Sys/Kernel/Fork.lean`'s `check_clone_resolve_complete_ok` is
    exactly "an `Ok` of the resolution is an `Ok` of the checker", so the
    inversion is that lemma followed by the checker's own `if`-chain at
    one literal return.

    What the walk reconstructs is the disjunction of the two arms that
    survive, plus the model each leaves behind — which is all that the
    statements below read.  The file gate is reported as well, because
    `clone_open_file_unmodeled` reads it from the other side.

    It is stated over the resolution rather than over `clone_spec`
    because BOTH entry points reach it: [clone3_resolve_inv] carries the
    same return, model and events across the ledger, and
    `clone3_spec_ok_resolve` below strips `clone3_spec`'s size and read
    gates, which are `match`es and touch no model state. -/

theorem clone_resolve_ok_inv (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : clone_resolve i m (.ok eff m' evs)) :
    clone_no_shared_file_b (m_fds m) = true ∧ evs = [] ∧
      ((errno_ret_in clone_errnos (eff_ret eff) = true ∧ m' = m) ∨
       (errno_ret_in clone_errnos (eff_ret eff) = false ∧
        clone_pid_ok_b m (eff_ret eff) = true ∧ m' = with_children m)) := by
  have hc : check_clone_resolve eff m = .CheckOk m' evs :=
    check_clone_resolve_complete_ok eff m m' evs i H
  obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
  simp only [check_clone_resolve] at hc
  by_cases hg : clone_no_shared_file_b (m_fds m) = true
  · rw [ite_eq_right (by simp [hg])] at hc
    cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
      simp only [check_clone_answer] at hc
    case nil.nil.nil.nil.nil =>
      by_cases he : errno_ret_in clone_errnos ret = true
      · rw [ite_eq_left he] at hc
        obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj hc
        subst hm'; subst hevs
        exact ⟨hg, rfl, Or.inl ⟨he, rfl⟩⟩
      · rw [ite_eq_right he] at hc
        by_cases hok : clone_pid_ok_b m ret = true
        · rw [ite_eq_left hok] at hc
          obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj hc
          subst hm'; subst hevs
          have hef : errno_ret_in clone_errnos ret = false := by simpa using he
          exact ⟨hg, rfl, Or.inr ⟨hef, hok, rfl⟩⟩
        · rw [ite_eq_right hok] at hc
          exact nomatch hc
    all_goals exact nomatch hc
  · have hb : clone_no_shared_file_b (m_fds m) = false := by simpa using hg
    rw [ite_eq_left (by simp [hb])] at hc
    exact nomatch hc

/-- The success branch is the only writer of `State.m_has_children`, which
    is what makes the read below a rewrite rather than a case. -/
theorem m_has_children_with_children (m : Model) :
    m_has_children (with_children m) = true := rfl

/-- `clone_spec`'s allowlist gate is a gate: an `Ok` went through the
    `then` branch. -/
theorem clone_spec_ok_resolve (flags : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : clone_spec flags i m (.ok eff m' evs)) : clone_resolve i m (.ok eff m' evs) := by
  by_cases hf : clone_fork_flags_b flags = true
  · unfold clone_spec at H
    rw [ite_eq_left hf] at H
    exact H
  · unfold clone_spec at H
    rw [ite_eq_right hf] at H
    simp only [unmodeled] at H
    exact nomatch H

/-- …and so are `clone3_spec`'s two: a `size` that is not the full struct
    and a struct that does not read back both answer `unmodeled`, so an
    `Ok` is past them.  The two `match`es are on the read, which carries
    no model state, so the resolution's own outcome is reached unchanged —
    the same argument `[clone3_resolve_inv]` makes for the ledger. -/
theorem clone3_spec_ok_resolve (uargs size : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : clone3_spec uargs size i m (.ok eff m' evs)) :
    clone3_resolve uargs i m (.ok eff m' evs) := by
  unfold clone3_spec at H
  by_cases hs : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · rw [ite_eq_left hs] at H
    simp only [unmodeled] at H
    exact nomatch H
  · rw [ite_eq_right hs] at H
    simp only [LinuxSem.LinuxProcessSem.bind] at H
    obtain ⟨x, m1, evs1, evs2, hi, hk, hevs⟩ := H
    simp only [inputSpec, input, Outcome.ok.injEq] at hi
    obtain ⟨hx, hm1, hevs1⟩ := hi
    subst hx
    subst hm1
    subst hevs1
    simp only [List.nil_append] at hevs hk
    subst hevs
    cases hread : read_bytes_map x.in_mem uargs (BitVec.ofInt 64 CLONE_ARGS_SIZE) with
    | none =>
      rw [hread] at hk
      dsimp only at hk
      simp only [unmodeled] at hk
      exact nomatch hk
    | some bs =>
      rw [hread] at hk
      dsimp only at hk
      by_cases hb : clone3_fork_args_b bs = true
      · rw [ite_eq_left hb] at hk
        exact hk
      · rw [ite_eq_right hb] at hk
        simp only [unmodeled] at hk
        exact nomatch hk

/-! ### `clone3_sharing_flags_unmodeled`

    Because the caller's struct is read out of USER MEMORY, the statement
    is gated on the read.  Past that read the argument is the `w_is0` on
    the struct's `flags` field that `clone3_fork_args_b` requires: a word
    that is zero has no bit set, so the sharing test is zero too. -/

/-- `w_is0 w` reads as "`w` is the zero word".  Recorded separately
    because the sharing argument below needs the VALUE, not the test. -/
theorem word_eq_zero_of_w_is0 {w : word} (h : w_is0 w = true) : w = 0 := by
  unfold w_is0 at h
  rw [show BitVec.ofInt 64 0 = (0 : word) from by decide] at h
  exact beq_iff_eq.mp h

theorem clone3_sharing_flags_unmodeled (uargs size : word) (i : SyscallInput) (m : Model)
    (bs : List byte)
    (Hread : read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) = some bs)
    (Hbit : z_land (bv_unsigned (clone_args_field bs 0)) clone_sharing_bits ≠ 0) :
    clone3_spec uargs size i m .unmodeled := by
  by_cases hs : (!(bv_eqb size (BitVec.ofInt 64 CLONE_ARGS_SIZE))) = true
  · unfold clone3_spec
    rw [ite_eq_left hs]
    exact unmodeled_intro i m
  · unfold clone3_spec
    rw [ite_eq_right hs]
    simp only [LinuxSem.LinuxProcessSem.bind]
    refine Or.inr ⟨i, m, [], rfl, ?_⟩
    have hb : clone3_fork_args_b bs = false := by
      by_cases h : clone3_fork_args_b bs = true
      · exfalso
        unfold clone3_fork_args_b at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
        have hz : clone_args_field bs 0 = 0 := word_eq_zero_of_w_is0 h0
        rw [hz] at Hbit
        exact Hbit (by simp [bv_unsigned, z_land])
      · simpa using h
    simp only [Hread, hb, Bool.false_eq_true, ite_false]
    exact unmodeled_intro i m

/-! ### `clone_open_file_unmodeled`

    THE FILE OFFSET is the one thing a plain fork still shares:
    `copy_files` duplicates the descriptor table while both tables point at
    the same `struct file`, and `State.FdEntry` inlines the offset into the
    descriptor, so the sharing is not expressible.  The spec declines
    rather than pretending otherwise, and the lemma below says so.

    The proof is `clone_resolve`'s own decline: the gate is tested first
    and answers `unmodeled` on this side, so the `bind`'s `Ok` case never
    comes up — one `ite_eq_left` past `bind_getModel`. -/

theorem clone_open_file_unmodeled (flags : word) (i : SyscallInput) (m : Model)
    (Hf : clone_no_shared_file_b (m_fds m) = false) : clone_spec flags i m .unmodeled := by
  by_cases hf : clone_fork_flags_b flags = true
  · unfold clone_spec
    rw [ite_eq_left hf]
    unfold clone_resolve
    simp only [getModelSpec, bind_getModel]
    rw [ite_eq_left (by simp [Hf])]
    exact unmodeled_intro i m
  · unfold clone_spec
    rw [ite_eq_right hf]
    exact unmodeled_intro i m

/-! ### `clone_never_returns_zero`, `clone3_never_returns_zero`

    ZERO IS NEVER AN ANSWER.  Zero is what the CHILD sees returned from
    `clone`; following it would run the child's branch of the caller's own
    code inside a model that has no child.  `Fork.clone_spec`'s header
    states that as a design decision; the result below records it, and
    `Sys/Kernel/Fork.lean` cites it as one.

    One case per surviving arm: the errno arm closes
    on `clone_errno_ret_nonzero` (proved above, with the membership read
    back off `errno_ret_in`), the pid arm on `clone_pid_ok_b`'s `0 < r`.
    The clone3 twin goes through `clone3_resolve_inv`, which carries the
    return across the ledger, so it is the same argument and not a second
    copy of it. -/

theorem clone_ret_ne_zero (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (H : clone_resolve i m (.ok eff m' evs)) : eff_ret eff ≠ Z_to_bv 64 0 := by
  obtain ⟨-, -, he | hpid⟩ := clone_resolve_ok_inv i m eff m' evs H
  · obtain ⟨e, hmem, heq⟩ := (errno_ret_in_true clone_errnos (eff_ret eff)).mp he.1
    rw [heq]
    exact clone_errno_ret_nonzero e hmem
  · have hpk : clone_pid_ok_b m (eff_ret eff) = true := hpid.2.1
    unfold clone_pid_ok_b at hpk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpk
    obtain ⟨⟨hpos, -⟩, -⟩ := hpk
    intro h0
    rw [h0] at hpos
    exact absurd hpos (by simp)

theorem clone_never_returns_zero (flags : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : clone_spec flags i m (.ok eff m' evs)) : eff_ret eff ≠ Z_to_bv 64 0 :=
  clone_ret_ne_zero i m eff m' evs (clone_spec_ok_resolve flags i m eff m' evs H)

theorem clone3_never_returns_zero (uargs size : word) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : clone3_spec uargs size i m (.ok eff m' evs)) : eff_ret eff ≠ Z_to_bv 64 0 := by
  obtain ⟨e0, hres, hret⟩ :=
    clone3_resolve_inv uargs i m eff m' evs (clone3_spec_ok_resolve uargs size i m eff m' evs H)
  have heff : eff_ret eff = e0.eff_ret := hret
  rw [heff]
  exact clone_ret_ne_zero i m e0 m' evs hres

/-! ### `clone_resolve_declines_or_sets_children`

    EITHER IT DECLINES, OR IT RECORDS THE CHILD.  `Kernel.Exit.wait4_spec`'s
    -ECHILD is correct only for a caller with nothing to reap, and what it
    reads to decide that is `State.m_has_children`.  The two specs
    therefore compose on a claim no single model can carry: that every
    resolution of 220 and 435 which returns a PID leaves that field set.

    THE TWO ARMS ARE SEPARATED, NOT MERELY COVERED.  The statement is a
    pair of implications keyed on the observed return rather than a
    disjunction, and that is what it buys over "declines or sets it": an
    inclusive disjunction is satisfied by an implementation that applies
    `State.with_children` on the ERRNO arm as well, which is a real
    mistake — a `clone` that answered -EAGAIN made no child, and a `wait4`
    after it must still answer -ECHILD, so a model that recorded one would
    decline a call Linux answers.

    Both halves are the disjunction above read at one arm: the errno arm
    is the one that leaves the model alone, the pid arm the one that calls
    `State.with_children`. -/

theorem clone_resolve_declines_or_sets_children (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : clone_resolve i m (.ok eff m' evs)) :
    (errno_ret_in clone_errnos (eff_ret eff) = true → m' = m) ∧
    (errno_ret_in clone_errnos (eff_ret eff) = false → m_has_children m' = true) := by
  obtain ⟨-, -, he | hpid⟩ := clone_resolve_ok_inv i m eff m' evs H
  · exact ⟨fun _ => he.2, fun h => by rw [he.1] at h; exact absurd h (by simp)⟩
  · exact ⟨fun h => by rw [hpid.1] at h; exact absurd h (by simp),
      fun _ => by rw [hpid.2.2]; exact m_has_children_with_children m⟩

/-! ### `clone_success_sets_children`,
    `check_clone_success_sets_children`

    The same claim at the dispatcher, over both entry points at once, and
    then for the executable checker.  `clone3` adds a copy-in ledger and
    nothing else — `clone3_resolve` hands back the very `clone_resolve`
    outcome, with the same post-model — so one lemma covers 220 and 435 and
    the two cannot drift apart.  The checker half is a corollary rather
    than a second proof: `check_syscall_sound_ok` says every `CheckOk` is
    an admissible outcome.

    Both are read off `clone_resolve_declines_or_sets_children`: the
    `is_clone_spec` / `is_clone3_spec` characterizations above say which
    spec the number reaches, and `clone_spec_ok_resolve` /
    `clone3_spec_ok_resolve` say an `Ok` is past their gates. -/

theorem clone_success_sets_children (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : bv_unsigned (in_sysno i) = 220 ∨ bv_unsigned (in_sysno i) = 435)
    (H : syscall_spec i m (.ok eff m' evs)) :
    (errno_ret_in clone_errnos (eff_ret eff) = true → m' = m) ∧
    (errno_ret_in clone_errnos (eff_ret eff) = false → m_has_children m' = true) := by
  rcases Hno with h | h
  · exact clone_resolve_declines_or_sets_children i m eff m' evs
      (clone_spec_ok_resolve (in_arg i 0) i m eff m' evs
        ((clone_is_clone_spec i m _ h).mp H))
  · obtain ⟨e0, hres, hret⟩ := clone3_resolve_inv (in_arg i 0) i m eff m' evs
      (clone3_spec_ok_resolve (in_arg i 0) (in_arg i 1) i m eff m' evs
        ((clone3_is_clone3_spec i m _ h).mp H))
    have heff : eff_ret eff = e0.eff_ret := hret
    rw [heff]
    exact clone_resolve_declines_or_sets_children i m e0 m' evs hres

theorem check_clone_success_sets_children (i : SyscallInput) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : List event)
    (Hno : bv_unsigned (in_sysno i) = 220 ∨ bv_unsigned (in_sysno i) = 435)
    (H : check_syscall i eff m = .CheckOk m' evs) :
    (errno_ret_in clone_errnos (eff_ret eff) = true → m' = m) ∧
    (errno_ret_in clone_errnos (eff_ret eff) = false → m_has_children m' = true) :=
  clone_success_sets_children i m eff m' evs Hno (check_syscall_sound_ok i eff m m' evs H)

/- =========================================================================
   `wait4`, `setsid`, and the concrete companions
   ========================================================================= -/

/-! ### `wait4_not_unmodeled`, `wait4_answers_only_echild`

    `wait4` (260) — MODELED, and stated here in the negative.  A file of
    tripwires is only worth reading if it stops being one when the fact
    changes.

    A faithful `wait4` at a caller WITH a child needs a child to wait for
    and a status ENCODING the model cannot produce — the signal-death half,
    `WIFSIGNALED` / `WTERMSIG` and the core-dump bit, which
    `Monad.outcome`'s two constructors cannot tell apart from a voluntary
    exit.  BOTH HALVES OF THAT ARGUMENT ARE ABOUT MODELING THE CHILD.  A
    caller with NO child has a complete, decidable answer that needs
    neither: -ECHILD.  `Exit.wait4_spec` gives that answer and nothing
    else — no pid, no status word, no encoding, so `Monad.outcome` never
    has to widen.

    The first lemma below adds the dispatcher step, because the
    statement is about `syscall_spec` and the spec's own decline chain is
    what says "not unmodeled": `wait4_is_wait4_spec` is that step
    and is the 260 twin of `clone_is_clone_spec` / `setsid_is_setsid_spec`.
    Once at `wait4_spec`, the first lemma is the four gate rewrites and
    `err_ret`'s `pure` — there is no `unmodeled` left to produce — and the
    second is the same walk at an `Ok`, one `if` per gate.

    The second goes through the CHECKER
    (`check_syscall_complete_ok` then `check_wait4`, the staged-evaluator
    route), because each of the four gates answers
    `unmodeled` and an `Ok` is therefore past all of them; the effect
    shape then leaves exactly one return.

    Note what this does NOT claim: the lists must also have STARTED empty,
    and that is a property of the LAUNCHER.  Linux's `execve` empties
    neither, so a process that forked a grandchild or attached a tracee
    before exec'ing this image hands it something to wait for.  That is a
    closed-world assumption about the environment, undischarged here. -/

/-- The number is `Exit.wait4_spec`, for every input, model and outcome:
    the 260 twin of `clone_is_clone_spec`.  `Sys.Dispatch.dispatch_arm`
    states the biconditional for any table and arm, so this is a lookup
    and a `simp`. -/
theorem wait4_is_wait4_spec (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect Model event) (Hno : bv_unsigned (in_sysno i) = 260) :
    (syscall_spec i m o ↔
      wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i m o) := by
  unfold syscall_spec
  apply dispatch_arm spec_table i m o
    (arm 260 (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)))
  rw [show ((in_sysno i).toNat : Int) = 260 from Hno]
  simp [lookup_arm, spec_table, arm]

theorem wait4_not_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 260)
    (Hpid : bv_unsigned (pid32 (in_arg i 0)) = WAIT_ANY32)
    (Hopt : bv_unsigned (waitopts32 (in_arg i 2)) = WNOHANG)
    (Hrus : w_is0 (in_arg i 3) = true)
    (Hch : m_has_children m = false) :
    ¬ syscall_spec i m .unmodeled := by
  intro H
  have hw := (wait4_is_wait4_spec i m .unmodeled Hno).mp H
  unfold wait4_spec at hw
  rw [ite_eq_right (by simp [Hpid]), ite_eq_right (by simp [Hopt]), ite_eq_right (by simp [Hrus])] at hw
  simp only [getModelSpec, bind_getModel] at hw
  rw [ite_eq_right (by simp [Hch])] at hw
  simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at hw
  exact nomatch hw

theorem wait4_answers_only_echild (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : List event)
    (Hno : bv_unsigned (in_sysno i) = 260)
    (H : syscall_spec i m (.ok eff m' evs)) :
    eff = mkEffect (errno_ret ECHILD) [] [] ∧ m' = m ∧ evs = [] := by
  have hc : check_wait4 i (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2))
      (in_arg i 3) eff m = .CheckOk m' evs := by
    rw [← LinuxSem.Checks.Sys.DispatchCompute.check_syscall_wait4 i eff m Hno]
    exact check_syscall_complete_ok i eff m m' evs H
  simp only [check_wait4] at hc
  by_cases h1 : (!((pid32 (in_arg i 0)).toNat : Int) == WAIT_ANY32) = true
  · rw [ite_eq_left h1] at hc
    exact nomatch hc
  · rw [ite_eq_right h1] at hc
    by_cases h2 : (!((waitopts32 (in_arg i 2)).toNat : Int) == WNOHANG) = true
    · rw [ite_eq_left h2] at hc
      exact nomatch hc
    · rw [ite_eq_right h2] at hc
      by_cases h3 : (!(w_is0 (in_arg i 3))) = true
      · rw [ite_eq_left h3] at hc
        exact nomatch hc
      · rw [ite_eq_right h3] at hc
        by_cases h4 : m_has_children m = true
        · rw [ite_eq_left h4] at hc
          exact nomatch hc
        · rw [ite_eq_right h4] at hc
          obtain ⟨ret, ws, zs, us, cs, ks⟩ := eff
          cases ws <;> cases zs <;> cases us <;> cases cs <;> cases ks <;>
            dsimp only at hc
          case nil.nil.nil.nil.nil =>
            by_cases hr : bv_eqb ret (errno_ret ECHILD) = true
            · rw [ite_eq_left hr] at hc
              obtain ⟨hm', hevs⟩ := check_result.CheckOk.inj hc
              subst hm'; subst hevs
              have hret : ret = errno_ret ECHILD :=
                (Fs.bv_eqb_eq ret (errno_ret ECHILD)).mp hr
              subst hret
              exact ⟨rfl, rfl, rfl⟩
            · rw [ite_eq_right hr] at hc
              exact nomatch hc
          all_goals exact nomatch hc

/-! ### `setsid_not_unmodeled`

    `setsid` (157) — MODELED, and stated here in the negative.  A file of
    tripwires is only worth reading if it stops being one when the fact
    changes: the statement fails to compile the moment 157 loses its arm,
    exactly as its neighbours fail the moment one of theirs gains one.

    The proof is the checker's own no-decline lemma, pulled back across
    the dispatcher: a `syscall_spec … Unmodeled` at 157 would be a
    `check_syscall = .CheckUnmodeled` at that arm
    (`check_syscall_complete_unmodeled`), which is
    `check_setsid_no_unmodeled` in `Checks/Sys/Kernel/Sys.lean` — the
    lemma is stated over the CHECKER there and over the spec here, and
    this is the step between them.  No `cbn` over the arm table is
    needed: `check_syscall_setsid` is the same lookup
    `Checks/Sys/Dispatch.lean` §4 performs, already discharged. -/

theorem setsid_not_unmodeled (i : SyscallInput) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 157) : ¬ syscall_spec i m .unmodeled := by
  intro H
  have hc := check_syscall_complete_unmodeled i m (mkEffect 0 [] []) H
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid i _ m Hno] at hc
  exact check_setsid_no_unmodeled (mkEffect 0 [] []) m hc

/-! ### The concrete companions

    `wait4_input_any` and the six `setsid_checker_*` examples, plus
    `modeled_number_is_not_unmodeled` — the `Example`s that push the
    dispatcher through `check_syscall` at ONE input each, one per branch
    the prose above names.

    They do not close by `rfl`: the arms read `decide` over a `Nat → Int`
    cast, and `rfl` cannot unwind `Int.decLt` while `decide` can.  So each
    is the staged evaluator instead — `check_syscall_<name>` to the arm,
    the arm unfolded at a literal effect, then one `ite_eq_left`/`ite_eq_right` per
    gate with the gate fact discharged by `decide` at that input.  No
    model reflection is needed anywhere here: none of these branches
    moves the model except `setsid`'s success, and that one names its
    post-model.

    These are stated in this file's own form: each states the
    branch its own name describes, at an input and model built the way
    `pc_input` / `pc_clone_input` above build them.  The quantified
    statements they accompany are the ones proved above, so the pairing
    the file's header asks for — every number has its `syscall_spec`
    statement first and its checker companion second — is intact. -/

/-- The `wait4` input: `wait4(-1, NULL, WNOHANG, NULL)`, the one call
    `Exit.wait4_spec` answers completely.  `WAIT_ANY32` is `pid32` of a
    `-1` register, and a `rusage` of 0 is the `NULL` the `w_is0` gate
    wants. -/
def wait4_input_any : SyscallInput :=
  SyscallInput.mkInput (Z_to_bv 64 260)
    [Z_to_bv 64 WAIT_ANY32, 0, Z_to_bv 64 WNOHANG, 0, 0, 0]
    (fun _ => none) (fun _ => none)

/-- -ECHILD, and the model is left alone: the failure created nothing. -/
theorem wait4_checker_echild :
    check_syscall wait4_input_any (mkEffect (errno_ret ECHILD) [] []) pc_model
      = .CheckOk pc_model [] := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_wait4 _ _ _ (by decide)]
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]

/-- A REAPED PID is rejected, not admitted: answering one would need a
    status word this model cannot produce, so the checker refuses rather
    than approximates. -/
theorem wait4_checker_rejects_a_reap :
    check_syscall wait4_input_any (mkEffect (Z_to_bv 64 4242) [] []) pc_model
      = .CheckReject := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_wait4 _ _ _ (by decide)]
  simp only [check_wait4]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [ite_eq_right (by decide)]

/-- The FIRST call: -EPERM is admissible — an untracked environment
    condition — and it records NOTHING, which is the half the `Ok pc_model`
    below pins: a kernel that refused one call can allow the next, so a
    failure must not leave the sticky bit behind. -/
theorem setsid_checker_first_call_eperm :
    check_syscall (pc_input 157) (mkEffect (errno_ret EPERM) [] []) pc_model
      = .CheckOk pc_model [] := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_left (by decide)]

/-- …and the SUCCESS arm, which writes both the tid it reports and the
    sticky bit.  On the `setsid` side the post-model is
    `with_setsid_succeeded (with_tid …)`; on `clone`'s it is
    `with_children`, and the two fields are different ones. -/
theorem setsid_checker_first_call_session_id :
    check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 4242) [] []) pc_model
      = .CheckOk (with_setsid_succeeded (with_tid (Z_to_bv 64 4242) pc_model)) [] := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- Zero is the CHILD's answer and no session id: below `0 < r`, so the
    envelope test refuses it. -/
theorem setsid_checker_rejects_zero :
    check_syscall (pc_input 157) (mkEffect 0 [] []) pc_model = .CheckReject := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

/-- The model a SUCCESSFUL `setsid` leaves: the tid it reported, and the
    sticky bit.  `m_has_children`, which `wait4` reads, is a different
    field and is not touched. -/
def pc_model_setsid_succeeded : Model :=
  with_setsid_succeeded (with_tid (Z_to_bv 64 4242) pc_model)

/-- AFTER A SUCCESS, a second success is refused — the bit is sticky, and
    this is the branch that reads it.  A different tid, so the refusal is
    the bit's and not the tid agreement's. -/
theorem setsid_checker_after_success_rejects_success :
    check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 4243) [] [])
      pc_model_setsid_succeeded = .CheckReject := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- …and -EPERM is STILL admissible then, which is what makes the pair a
    branch test rather than an arm that refuses everything.  It leaves the
    bit alone: a refusal cannot clear a sticky success. -/
theorem setsid_checker_after_success_eperm :
    check_syscall (pc_input 157) (mkEffect (errno_ret EPERM) [] [])
      pc_model_setsid_succeeded = .CheckOk pc_model_setsid_succeeded [] := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_left (by decide)]

/-- THE BIT ALONE is the refusal: the same input and the same return as
    [setsid_checker_first_call_session_id], at a model that differs from
    `pc_model` only in `m_setsid_succeeded`.  So the two examples pin the
    branch to that field and to nothing else. -/
theorem setsid_checker_bit_alone_rejects_success :
    check_syscall (pc_input 157) (mkEffect (Z_to_bv 64 4242) [] [])
      (with_setsid_succeeded pc_model) = .CheckReject := by
  rw [LinuxSem.Checks.Sys.DispatchCompute.check_syscall_setsid _ _ _ (by decide)]
  simp only [check_setsid]
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- THE DUAL OF EVERY TRIPWIRE ABOVE: a number the dispatcher DOES answer
    is one the checker never declines — for every input, effect and model.

    The deferral note expected this to need
    `Checks/Cases/CheckToolkit.lean`'s reflection, since `check_result` has
    no `DecidableEq`.  It does not: `check_syscall_err_iff` already says
    the checker declines EXACTLY where the spec does, so the fact is
    `setsid_not_unmodeled` seen through the checker — one line, and one
    fewer `Cases/` dependency than the note assumed.  `157` is the
    modeled number it is stated at; the same one-liner works for any
    number with a no-decline lemma. -/
theorem modeled_number_is_not_unmodeled (i : SyscallInput) (eff : SyscallEffect) (m : Model)
    (Hno : bv_unsigned (in_sysno i) = 157) :
    check_syscall i eff m ≠ .CheckUnmodeled := by
  intro h
  exact setsid_not_unmodeled i m Hno ((check_syscall_err_iff i eff m).mp h)

end LinuxSem.Checks.ProcessCreation
