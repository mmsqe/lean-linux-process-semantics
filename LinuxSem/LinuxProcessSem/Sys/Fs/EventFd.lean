/-
  * LinuxProcessSem.Sys.Fs.EventFd — eventfd2 (19)

  This file answers to Linux `fs/eventfd.c`: it holds what the kernel
  defines there, and nothing else.  Which file a spec belongs in is
  therefore not a judgement call — look up where the kernel defines the
  syscall.  `Specs.lean` carries the whole map.

  TRUST BOUNDARY: this file is part of the trusted specification.
  `Specs.lean` holds the dispatcher and re-exports this module; see that
  file's header for the representation and fail-closed conventions
  every spec here follows.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.LinuxProcessSem.StateFd
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.Sys.Fs.File

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Fs.File
  (lowest_fd lowest_fd_ok lowest_fd_occupied)

namespace LinuxSem.LinuxProcessSem.Sys.Fs.EventFd

/- WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name.  Every body quoted below was read from the
    pinned tree itself — stable v6.18.46, commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, this repository's kernel
    of record.  The tags named in the windows WERE fetched, and only to
    bound them: every text that is CITED is the pinned commit's.

      fs/eventfd.c                `do_eventfd`,
                                  `SYSCALL_DEFINE2(eventfd2, ...)`,
                                  `SYSCALL_DEFINE1(eventfd, ...)`,
                                  `eventfd_fops`
      include/linux/eventfd.h     `EFD_SHARED_FCNTL_FLAGS`,
                                  `EFD_FLAGS_SET`
      include/uapi/linux/eventfd.h
                                  `EFD_SEMAPHORE`, `EFD_CLOEXEC`,
                                  `EFD_NONBLOCK`
      fs/file.c                   `get_unused_fd_flags`,
                                  `__get_unused_fd_flags`, `alloc_fd`,
                                  `expand_files`
      fs/anon_inodes.c            `anon_inode_getfile_fmode`,
                                  `__anon_inode_getfile`
      init/Kconfig                `config EVENTFD`
      kernel/sys_ni.c             `COND_SYSCALL(eventfd2)`
      include/uapi/asm-generic/unistd.h
                                  `__NR_eventfd2`

    WINDOWS, per function, ending at the pinned commit.  Each was read
    by fetching the file at the tag and comparing the function's own
    text; the bound given is the earliest tag that matches AND whose
    successors all match, so a later regression cannot hide inside one.

      v6.15 - v6.18.46      `do_eventfd`, byte-for-byte.  v6.12 differs,
                            and only past the gate this file models:
                            it calls `anon_inode_getfile` and then sets
                            `FMODE_NOWAIT` by hand where the pinned text
                            calls `anon_inode_getfile_fmode`.  Both of
                            those sit below the `return -EINVAL`, so the
                            difference is invisible to every answer here
                            — but the TEXT is not identical, and this
                            repository pins text.
      at least v5.10        `SYSCALL_DEFINE2(eventfd2, ...)` and
                            `SYSCALL_DEFINE1(eventfd, ...)`, and the
                            gate itself: `if (flags & ~EFD_FLAGS_SET)
                            return -EINVAL;` is the same statement in
                            the same place in every tag fetched down to
                            v5.10.
      at least v5.10        `EFD_SHARED_FCNTL_FLAGS` and
                            `EFD_FLAGS_SET` in include/linux/eventfd.h,
                            and `EFD_SEMAPHORE` at `(1 << 0)` — the
                            latter in include/linux/eventfd.h through
                            v6.1 and in include/uapi/linux/eventfd.h
                            from at least v6.6.  Same value either side
                            of that move; see `Uapi.EFD_SEMAPHORE`.

    "AT LEAST" IS NOT "UNCHANGED SINCE".  v5.10 is the floor of the
    probe set, not an established boundary: the texts are identical at
    every tag fetched down to it and may well go back further; nobody
    looked.  A reader who needs a real lower bound has to fetch it, and
    this sentence is what tells them the number here will not answer the
    question.

    ON riscv64 THERE IS NO `eventfd`, ONLY `eventfd2`.  The generic
    64-bit syscall table carries `__NR_eventfd2 19` and no `__NR_eventfd`
    at all (include/uapi/asm-generic/unistd.h), so
    `SYSCALL_DEFINE1(eventfd, unsigned int, count)` — which is
    `do_eventfd(count, 0)` — is unreachable here.  It is named in the
    citation list anyway because it is the OTHER caller of the function
    this file models, and a reader checking that `do_eventfd`'s gate is
    the whole of the argument rejection needs to see both callers to
    know that neither adds a check of its own.  Neither does: each is a
    one-line forward.

    THIS ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE, exactly as
    `Fs.Timerfd` does, and for the same reason: every input that
    survives the gate CREATES A FILE DESCRIPTOR, and this model has no
    descriptor kind to put an eventfd counter behind — none of
    `State.FdEntry`'s constructors is an eventfd.  Adding one is not a
    local change: every `FdEntry` match in the tree is exhaustive on
    purpose, so the read, write, stat, sync, ioctl, select, epoll and
    socket specs, their acceptors, their witnesses and the example
    proofs would each have to decide the new case.

    WHAT THAT COSTS is priority 3 and nothing else: a program that
    successfully creates an eventfd leaves the modeled surface at the
    `eventfd2` itself, so `Equivalence.strong_universal` is vacuous over
    it rather than wrong about it.  Source and target are judged against
    the same model, so no pair of programs is separated by this.  The
    condition that would let this arm grow a success is a single one,
    and it is worth writing down because it is one step to check rather
    than an argument to re-derive: a descriptor kind in `State.FdEntry`
    carrying the 64-bit counter and the `EFD_SEMAPHORE` bit, which is
    also what a `read` or a `write` on an eventfd needs, and what
    `Fs.EventPoll` would need before `epoll_ctl` could record interest
    in one.

    THE GATE IS ONE `if`, AND IT IS THE FIRST THING `do_eventfd` DOES
    that can fail.  Linux writes

      static int do_eventfd(unsigned int count, int flags)
      {...
              /* Check the EFD_* constants for consistency.  */
              BUILD_BUG_ON(EFD_CLOEXEC != O_CLOEXEC);
              BUILD_BUG_ON(EFD_NONBLOCK != O_NONBLOCK);
              BUILD_BUG_ON(EFD_SEMAPHORE != (1 << 0));

              if (flags & ~EFD_FLAGS_SET)
                      return -EINVAL;

              ctx = kmalloc(sizeof( *ctx ), GFP_KERNEL);

    (the quoted `sizeof` is written with a space after its parenthesis
  because `(` followed by `*` opens a nested  comment; the kernel
    text has no space there.  The space is kept here so the quotation
    stays a quotation; Lean's comment delimiters are a different pair
  and nest only on themselves, so the spacing is inert in this tree.)

    (Linux v6.18.46, fs/eventfd.c, `do_eventfd`).  The three
    `BUILD_BUG_ON`s are compile-time assertions and cost the call
    nothing at run time, so the `if` is the first statement with a
    verdict.  ORDER IS BEHAVIOR here in the strongest possible sense:
    the flag word is judged BEFORE the `kmalloc` and before any
    descriptor is reserved, so a rejected `eventfd2` allocates nothing,
    consumes no fd number, and cannot answer -ENOMEM or -EMFILE — those
    two are unreachable on this path rather than merely unmodeled.

    `count` IS NOT READ BY ANY MODELED PATH.  It is the initial value of
    the counter and is stored by `ctx->count = count`, which sits below
    the gate; nothing above the gate looks at it.  So no arm below takes
    it as an argument, and `eventfd2(count, flags)` answers -EINVAL for
    EVERY `count` when `flags` is refused — including counts a reader
    might expect to be rejected, such as `(unsigned int)-1`.  There is
    no `count` the kernel refuses: the type is `unsigned int`, so the
    64-bit register's high half is discarded and every remaining value
    is a legal initial counter.

    THE FLAG WORD ARRIVES ALREADY TRUNCATED TO 32 BITS, and that is
    load-bearing rather than incidental.  `flags` is declared `int` in
    `SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)`, and
    riscv64's wrapper narrows it at the boundary: `__SYSCALL_DEFINEx`
    calls `__do_sys##name` through `__SC_CAST`, which is `(__force t) a`
    (Linux v6.18.46, arch/riscv/include/asm/syscall_wrapper.h and
    include/linux/syscalls.h), while `SC_RISCV_REGS_TO_ARGS` hands over
    the registers full-width.  So the high half of the register is
    DISCARDED before the mask is applied, and `eventfd2(0, 2^32)` is
    `eventfd2(0, 0)` — which Linux answers with a descriptor, not with
    the -EINVAL a full-register test would give.  `Sys.SyscallTable`
    applies `flag32` at the arm, which is where the kernel does it and
    where `timerfd_create`'s and `epoll_create1`'s flag words are
    already narrowed; this spec receives the word narrowed and must not
    narrow it again.

    THE TEST IS A TRUTHINESS TEST, not a sign test, and that is what
    makes `Z.ldiff` the faithful spelling.  `flags & ~EFD_FLAGS_SET` is
    used directly as the `if` condition, so a residue of 0x80000000 —
    negative as an `int` — takes the -EINVAL just as 1 does.  An
    implementation that compared the residue against 0 with `>` rather
    than `<>` would admit `flags = 1 << 31`; this one does not.
    `Fs.Timerfd` carries the identical argument for the identical
    reason.

    WHAT THE DECLINE COVERS, walked from the source so the gap is a
    named list rather than "the rest": -ENOMEM from the `kmalloc` of the
    `eventfd_ctx`; -EMFILE from `get_unused_fd_flags`; -ENOENT or
    -ENODEV from `anon_inode_getfile_fmode`; and the success, which is
    the descriptor number.

    NO -EINVAL IS REACHABLE ON ANY OF THEM, which is what makes this a
    decline that loses coverage WITHOUT losing precision: the errno the
    arm commits to is exactly the errno Linux commits to, and there is
    no input where the model answers -EINVAL and Linux answers something
    else.  The claim is checkable rather than rhetorical — these are the
    returns of the functions `do_eventfd` reaches after the gate, each
    read at v6.18.46:

    - `do_eventfd` itself (fs/eventfd.c) has exactly one
      `return -EINVAL` in its body, the gate's;
    - `get_unused_fd_flags` (fs/file.c) forwards
      `__get_unused_fd_flags` to `alloc_fd`, whose only errno is
      -EMFILE, and `expand_files` beneath it carries -EMFILE too;
    - `__anon_inode_getfile` (fs/anon_inodes.c), under
      `anon_inode_getfile_fmode`, yields -ENOENT when the fops' module
      cannot be pinned and -ENODEV when the shared anon inode is an
      error pointer, and otherwise forwards `alloc_file_pseudo`, which
      is an allocation failure;
    - `ida_alloc` cannot contribute one, because `do_eventfd` does not
      TEST its result: it writes `ctx->id = ida_alloc(...)` and reads on.

    That is the walk, not a claim about the whole tree: a caller
    reaching `do_eventfd` through some path not enumerated here is
    outside what was checked.

    CONFIG_EVENTFD IS ASSUMED ON.  fs/Makefile builds eventfd.c under
    `obj-$(CONFIG_EVENTFD)` and kernel/sys_ni.c carries
    `COND_SYSCALL(eventfd2)`, so a kernel built without it answers
    -ENOSYS to every input this arm calls -EINVAL.  init/Kconfig gives
    `config EVENTFD` a `default y` and hides its prompt behind EXPERT.
    It is the same class of assumption every arm whose syscall carries a
    `COND_SYSCALL` makes — kernel/sys_ni.c has one for `timerfd_create`
    and one for `socket` too — and it is stated here rather than tested
    because no syscall argument distinguishes the two builds.  It is the
    ONE premise outside this call's own arguments that the -EINVAL rests
    on. -/

/- The imports this file leans on are the state layer's (`BvBase`, `Fs`,
  `State`, `Monad`) plus `Sys.Syscall` and `Sys.Uapi`, whose names are used
  unqualified below.

  `MonadInstances` fixes the concrete `Sys Model SyscallInput event`,
  so a spec's type is `SysSpec SyscallEffect`.
  `Sys.Syscall` supplies `err_ret` and the `flag32` truncation the checks
  use; `Sys.Uapi` supplies `EFD_FLAGS_SET` and `EFD_SEMAPHORE`; `State`
  supplies the errno constants (`EINVAL`, `EMFILE`) and `mkEffect`;
  `Monad` supplies `unmodeled`; `StateLedger`/`StateFd` supply `m_fds`,
  `mkModel`, `fd_lookup` and `alloc_fd`, and `Sys.Fs.File` supplies
  `z_ldiff` (`Z.ldiff`) and `lowest_fd` — imported, never redefined.
  `Sys.Uaccess` is deliberately NOT imported: no user buffer is touched by
  this spec.

  `bv_unsigned w` is `(w.toNat: Int)`
  here — the same function on the same carrier, spelled out because the
  Lean tree has no `bv_unsigned` (`StateVm.lean` records the same
  identification).  `Z.eqb _ 0` is `_ == 0`, and `negb` is `!`.

  `Z.ldiff a b` is `a & ~b`.  Lean has no
  such constant; `Sys/Uapi.lean` ports `Z.lor`, `Z.land` and `Z.ldiff`
  together, and `Sys.Uapi.z_ldiff` is imported and reused rather than
  copied a second time (`Fs.File.z_ldiff` is a transparent alias to it).
  The operand
  here is non-negative (`flags.toNat` is), which is the condition under
  which `a - (a & b)` is `a & ~b`; its docstring carries that argument.

  A spec that narrowed internally would agree with itself rather than with the
  kernel.

  `eventfd2_spec` takes the flag word
  ALONE, and this tree keeps that arity: `count` is not read above the
  gate, so the type says what the prose says.  There is nothing to check
  about `count` beyond the arity itself.

  Nothing below produces a descriptor or an errno other than -EINVAL.
  The checks
  at the end of the file therefore pin the descriptor number and the
  -EMFILE limit on `File.lowest_fd`/`alloc_fd` — the machinery the
  docstring's gap list names — rather than on an arm this spec does not
  have; the note above them spells that out.
-/

/-- The flag mask `eventfd2` admits, written out of the kernel's own
    `if`.  RESTATED rather than shared with the acceptor and the
    witness, and deliberately so: this predicate decides WHICH ARM RUNS,
    and a gate the three layers imported from one definition would agree
    with itself however wrong it was.  The soundness and completeness
    lemmas are what force the three statements to coincide, which is the
    same reason `Fs.Timerfd` and `Kernel.Time.PosixTimers` restate their
    envelope bounds in each layer instead of sharing them. -/
def eventfd2_einval_b (flags : word) : Bool :=
  !(z_ldiff (flags.toNat : Int) EFD_FLAGS_SET == 0)

/-- `eventfd2 count flags`: create a descriptor holding a 64-bit counter.

    No `get_model` and no `count`: the answer is a function of the flag
    word alone.  The -EINVAL arm touches no memory, emits no event and
    changes no state, which is what the kernel does on that path too —
    it returns before the `kmalloc`. -/
def eventfd2_spec (flags : word) : SysSpec SyscallEffect :=
  if eventfd2_einval_b flags
  then err_ret EINVAL      -- real -EINVAL, decided before anything is allocated
  else unmodeled           -- ENOMEM / EMFILE / ENOENT / ENODEV / the descriptor: fail closed

/-! ## Sanity checks

  It is the two definitions above and their prose. The checks below are PORT CHECKS,
    and they pin the three things the prose argues for:

    1. **The gate**: the mask is exactly `EFD_FLAGS_SET` (bit 0 included,
       which is what separates it from `TFD_CREATE_FLAGS`), the residue
       is a truthiness test (`1 << 31` included), and the flag word is
       read at the width the dispatcher hands it — so `2^32` is rejected
       full-width and admitted after `flag32`.
    2. **The two arms**, at the spec: -EINVAL is an `ok` outcome carrying
       the errno word, and every admitted input is `unmodeled` — the
       `EFD_SEMAPHORE`-only word included, since `eventfd2(0, 1)` hands
       back a descriptor and answering -EINVAL to it would be a
       confidently wrong errno (it is `timerfd_create`'s -EINVAL, not
       this call's).
    3. **The two things the decline stands in for** — the descriptor
       number and the -EMFILE at the table's limit.  They are NOT arms of
       this spec, so they are pinned where the kernel
       takes them: `File.lowest_fd` over a small fixture, and the
       allocator's fuel-exhaustion branch, whose freeness conjunct is
       what leaves only the -EMFILE alternative.

    `FdEntry` has no `DecidableEq` (its `FdSocket` arm reaches the
    coinductive `SockState`), so lookup equations are stated as equations
    between `Option FdEntry` and proved by `simp` on the tables' keys
    rather than by `decide`; everything `Bool`- or `word`-valued
    (`eventfd2_einval_b`, `z_ldiff`, `alloc_fd`, the errno constants) is
    `by decide`. -/

/-! ### The gate -/

/-- The residue test is `Z.ldiff` (`a & ~b`), `Sys.Uapi.z_ldiff`:
    it clears exactly the mask's bits. -/
example : z_ldiff EFD_FLAGS_SET EFD_FLAGS_SET = 0 := by decide
example : z_ldiff (EFD_FLAGS_SET + 8) EFD_FLAGS_SET = 8 := by decide
example : z_ldiff 0 EFD_FLAGS_SET = 0 := by decide

/-- `EFD_FLAGS_SET` is the shared-fcntl mask WIDENED BY ONE BIT, and bit 0
    is `EFD_SEMAPHORE`: 524288 (`O_CLOEXEC`) + 2048 (`O_NONBLOCK`) + 1. -/
example : EFD_FLAGS_SET = 526337 := by decide
example : EFD_FLAGS_SET = 526336 + EFD_SEMAPHORE := by decide

/-- The word the kernel admits, and each of its three bits on its own. -/
example : eventfd2_einval_b 0 = false := by decide
example : eventfd2_einval_b EFD_FLAGS_SET = false := by decide
example : eventfd2_einval_b O_CLOEXEC = false := by decide
example : eventfd2_einval_b O_NONBLOCK = false := by decide

/-- `EFD_SEMAPHORE` IS ADMITTED — the one input that separates this gate
    from `timerfd_create`'s, whose bit 0 is `TFD_TIMER_ABSTIME` and is
    -EINVAL.  `eventfd2(0, 1)` hands back a descriptor. -/
example : eventfd2_einval_b EFD_SEMAPHORE = false := by decide

/-- …and every other bit is refused, alone or on top of the mask. -/
example : eventfd2_einval_b 2 = true := by decide
example : eventfd2_einval_b 8 = true := by decide
example : eventfd2_einval_b (EFD_FLAGS_SET + 1) = true := by decide
example : eventfd2_einval_b (EFD_FLAGS_SET + 8) = true := by decide

/-- THE FLAG TEST IS TRUTHINESS, NOT SIGN: `1 << 31` is 0x80000000, which
    is negative as a 32-bit `int`, and it is still -EINVAL — as is the
    full 64-bit word `-1`, every bit set.  A `> 0` comparison would admit
    both. -/
example : eventfd2_einval_b (BitVec.ofInt 64 2147483648) = true := by decide
example : eventfd2_einval_b (BitVec.ofInt 64 (-1)) = true := by decide
example : eventfd2_einval_b (flag32 (BitVec.ofInt 64 2147483648)) = true := by
  decide

/-- …stated once for every word, so it is not a fact about the examples:
    the gate is exactly "the residue is nonzero", with no ordering test
    that could read a negative residue as small. -/
theorem eventfd2_einval_b_iff (flags : word) :
    eventfd2_einval_b flags = true ↔ z_ldiff (flags.toNat : Int) EFD_FLAGS_SET ≠ 0 := by
  simp [eventfd2_einval_b]

/-- THE FLAG WORD ARRIVES NARROWED AND IS NOT NARROWED AGAIN.  Read at
    full width, `eventfd2(0, 2^32)` has bit 32 set and is -EINVAL; the
    kernel, narrowing at the boundary through `__SC_CAST` to `int`, sees
    `eventfd2(0, 0)` and hands back a descriptor.  The dispatcher applies
    `flag32`; applied, the gate admits the call. -/
example : eventfd2_einval_b (BitVec.ofInt 64 4294967296) = true := by decide
example : flag32 (BitVec.ofInt 64 4294967296) = 0 := by decide
example : eventfd2_einval_b (flag32 (BitVec.ofInt 64 4294967296)) = false := by
  decide
example : eventfd2_einval_b (flag32 (BitVec.ofInt 64 4294967297)) = false := by
  decide

/-! ### The two arms -/

/-- THE -EINVAL ARM: a `true` gate answers the errno word, leaving the
    model untouched and emitting nothing — the kernel returns before the
    `kmalloc`. -/
theorem eventfd2_einval (flags : word) (i : SyscallInput) (m : Model)
    (h : eventfd2_einval_b flags = true) :
    eventfd2_spec flags i m (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  simp only [eventfd2_spec]
  rw [ite_eq_left h]
  simp only [err_ret, ret_only, pure]

/-- THE DECLINE: every input that survives the gate is `unmodeled`,
    whatever it is — the `EFD_SEMAPHORE` word included, since -EINVAL is
    an errno Linux does not produce for it. -/
theorem eventfd2_declines (flags : word) (i : SyscallInput) (m : Model)
    (h : eventfd2_einval_b flags = false) :
    eventfd2_spec flags i m .unmodeled := by
  have h' : eventfd2_einval_b flags ≠ true := by
    rw [h]
    decide
  simp only [eventfd2_spec, ite_eq_right h', unmodeled]

/-- Bad flags are -EINVAL. -/
example (i : SyscallInput) (m : Model) :
    eventfd2_spec 8 i m (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  eventfd2_einval 8 i m (by decide)

/-- An unknown bit alongside the admitted ones is -EINVAL too. -/
example (i : SyscallInput) (m : Model) :
    eventfd2_spec (EFD_FLAGS_SET + 8) i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  eventfd2_einval _ i m (by decide)

/-- Bit 31 takes the -EINVAL — the sign of the residue decides nothing. -/
example (i : SyscallInput) (m : Model) :
    eventfd2_spec (BitVec.ofInt 64 2147483648) i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) :=
  eventfd2_einval _ i m (by decide)

/-- With the gate passed, the answer is the DECLINE, not an errno: the
    admitted flag words. -/
example (i : SyscallInput) (m : Model) : eventfd2_spec 0 i m .unmodeled :=
  eventfd2_declines _ i m (by decide)

example (i : SyscallInput) (m : Model) :
    eventfd2_spec EFD_FLAGS_SET i m .unmodeled :=
  eventfd2_declines _ i m (by decide)

/-- `EFD_SEMAPHORE` alone DECLINES rather than rejects: `eventfd2(0, 1)`
    is a descriptor, not -EINVAL. -/
example (i : SyscallInput) (m : Model) :
    eventfd2_spec EFD_SEMAPHORE i m .unmodeled :=
  eventfd2_declines _ i m (by decide)

/-- …and so does the narrowed `2^32`, which the kernel reads as `0`. -/
example (i : SyscallInput) (m : Model) :
    eventfd2_spec (flag32 (BitVec.ofInt 64 4294967296)) i m .unmodeled :=
  eventfd2_declines _ i m (by decide)

/-! ### The descriptor number (the success this arm declines)

    A surviving call reaches `get_unused_fd_flags`, which takes the
  LOWEST free descriptor — `File.lowest_fd`, this tree's `choose` over
    `State.alloc_fd`.  That number is what the kernel returns, and it is
    pinned here rather than in an arm of `eventfd2_spec`, which by
    construction has none. -/

/-- A syscall input for `eventfd2`.  The spec does not read it — the
    answer is a function of the flag word alone — but a `SysSpec` is a
    relation on an input and a model as well, so the checks name one. -/
private def demoInput : SyscallInput :=
  { in_sysno := 19, in_args := [0, 0],
    in_mem := fun _ => none, in_wmem := fun _ => none }

/-- A tiny fd table for the checks: 0, 1 and 2 are the three standard
    descriptors, so the next descriptor a create call would hand out is
    3. -/
private def demoFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdChannel 8),
   (2, FdEntry.FdChannel 9)]

/-- The model the checks run in: the table above, an empty VM ledger, an
    empty file system, EOF on stdin, no halt and the default
    RLIMIT_NOFILE (1024). -/
private def demoModel : Model :=
  mkModel demoFds (mkVmMaps [] [] 0 0 0) IEof []

/-- The same table with fd 1 closed — after `close(1)` the next
    descriptor handed out is 1 again, not 3. -/
private def demoHoleFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (2, FdEntry.FdChannel 9)]

private def demoHoleModel : Model :=
  mkModel demoHoleFds (mkVmMaps [] [] 0 0 0) IEof []

/-- The allocator hands out the first free descriptor — 3 here. -/
example : alloc_fd demoFds = 3 := by decide

/-- …and after `close(1)` it hands out 1 again. -/
example : alloc_fd demoHoleFds = 1 := by decide

/-- THE SUCCESS ARM OF A SURVIVING CALL, at the machinery that owns it:
    the lowest free descriptor is 3, and it is free. -/
example : lowest_fd demoFds demoInput demoModel (.ok 3 demoModel []) := by
  rw [lowest_fd_ok demoFds 3 demoInput demoModel]
  exact ⟨by simp [demoFds, fd_lookup], by decide⟩

/-- …and with fd 1 closed it is 1 — the lowest, not the next in some
    other order. -/
example : lowest_fd demoHoleFds demoInput demoHoleModel (.ok 1 demoHoleModel []) := by
  rw [lowest_fd_ok demoHoleFds 1 demoInput demoHoleModel]
  exact ⟨by simp [demoHoleFds, fd_lookup], by decide⟩

/-! ### -EMFILE at the table's limit

    `get_unused_fd_flags` answers -EMFILE when the descriptor table has no
    free slot below `sysctl_nr_open`.  The model's allocator is
    fuel-bounded at 4096 candidates, and its last branch returns the
    candidate UNCONDITIONALLY; `File.lowest_fd`'s freeness conjunct then
    empties the success set, which is the -EMFILE alternative.  The
    4096-candidate instance is not evaluated — a 4097-entry table costs
    millions of kernel reduction steps on every build of this file, the
    cost `Fs/File.lean` declines for its own fixture — so the mechanism
    is pinned on a miniature with explicit fuel, and the general fact is
    stated as `lowest_fd_at_limit`. -/

/-- THE EXHAUSTION BRANCH OF `alloc_fd`, in miniature: a table holding
    0..5 and fuel for five candidates stops on 5, which is TAKEN — the
    state the freeness conjunct rejects. -/
private def demoSixFds : List (word × FdEntry) :=
  [(0, FdEntry.FdChannel 7), (1, FdEntry.FdChannel 8),
   (2, FdEntry.FdChannel 9), (3, FdEntry.FdChannel 10),
   (4, FdEntry.FdChannel 11), (5, FdEntry.FdChannel 12)]

example : alloc_fd_aux demoSixFds (BitVec.ofInt 64 0) 5 = 5 := by decide

/-- …and 5 really is occupied there. -/
example : fd_lookup demoSixFds 5 = some (FdEntry.FdChannel 12) := by
  simp [demoSixFds, fd_lookup]

/-- The two errno words this file's prose names. -/
example : EINVAL = 22 := by decide
example : EMFILE = 24 := by decide

end LinuxSem.LinuxProcessSem.Sys.Fs.EventFd

