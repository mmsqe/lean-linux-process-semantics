/-
  * LinuxProcessSem.Sys.Kernel.Futex.Syscalls — futex (98)

    This file answers to Linux [kernel/futex/syscalls.c]: it holds what
    the kernel defines there, and nothing else.  Which file a spec
    belongs in is therefore not a judgement call — look up where the
    kernel defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows.


  NOTES (deviations, all notation only):
  - `Z` → `Int`; `word` stays `word` (`BitVec 64`); `Z_to_bv n z` →
    `BitVec.ofInt n z`; `bv_unsigned w` → `(w.toNat : Int)`; `Z.eqb` →
    `==`; `negb b` → `!b` (`Bool.not`); `Z.of_nat n` → `(n : Int)`.
  - `Sys SyscallEffect` → `SysSpec SyscallEffect` (see `MonadInstances`).
    `x <- c ;; k` has no notation in this monad: it is
    `bind c (fun x => k)`.
  - `ret_only`/`err_ret`/`w_is0`/`record_copyins`/`abi_low32` are
    `Sys.Syscall`'s, the `FUTEX_*` words are `Sys.Uapi`'s, and
    `read_bytes_map`/`access_okb`/`le_bytes_to_word` are the state
    layer's.  All of them are put into unqualified scope,
    all in unqualified scope; the `open`s below do the same.
  - `abi_low32` is QUALIFIED as `Sys.Syscall.abi_low32` at its one use
    site, because `Sys/Uapi.lean` still carries a local copy of the same
    name (see the note in `Sys/Syscall.lean`); only one should remain.
-/
import LinuxSem.LinuxProcessSem.MonadInstances
import LinuxSem.LinuxProcessSem.Sys.Syscall
import LinuxSem.LinuxProcessSem.Sys.Uapi
import LinuxSem.LinuxProcessSem.StateMemory

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi

namespace LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

/-! ## The waiter set, and what this spec may therefore answer

    THE WAITER SET OF A PRIVATE FUTEX KEY IS EMPTY IN THIS MODEL, and
    everything below rests on it.  Citations are torvalds/linux read at
    v6.18.46, commit 1f99e9ab748f.

    A waiter is a `struct futex_q` on the plist of a hash bucket, put
    there by `futex_queue` (kernel/futex/core.c) and matched by
    `futex_match` on the `union futex_key` the queueing task computed.
    For an op carrying `FUTEX_PRIVATE_FLAG`, `get_futex_key`
    (kernel/futex/core.c) builds that key from the caller's own mm:

        if (!fshared) { key->private.mm = mm;
                        key->private.address = address; return 0; }

    so only a task whose `current->mm` is the SAME POINTER can produce a
    key that `futex_match` accepts.  The hash bucket is global and holds
    other processes' waiters; the key is what excludes them.

    This model steps one task and can reach no second one that shares
    its mm.  The only entry points to `copy_process` (kernel/fork.c) are
    `clone` (220) and `clone3` (435), and neither ever grants `CLONE_VM`:
    `Kernel.Fork.clone_fork_flags_b` admits the single flag word
    `SIGCHLD` and `Kernel.Fork.clone3_fork_args_b` the same word in a
    struct, and every other word declines or fails.  A forked child gets
    a COPY of the mm
    (`copy_mm` calls `dup_mm` when `CLONE_VM` is clear), so its private
    keys are different keys — and it is not a configuration this
    development can be in anyway.

    THAT PREMISE IS CHECKED RATHER THAN ASSERTED.
    `Checks/Cases/Kernel/Futex/Syscalls.lean` proves, over both gates,
    that neither admits a word with
    `CLONE_VM` set — [clone_fork_gate_grants_no_shared_mm] and
    [clone3_fork_gate_grants_no_shared_mm] — so widening either one
    breaks that build beside the
    prose saying why it matters.  An
    argument that spans two files is
    the kind that rots quietly, and this one is load-bearing for every
    answer below.

    So the count `futex_wake` returns is 0 by construction rather than by
    luck, and a FUTEX_WAIT whose value still matches would park forever.
    THE SECOND HALF IS WHY THIS SPEC IS NARROW: an operation whose answer
    depends on a waiter EXISTING is unanswerable here, and declines.

    WHAT THE EMPTY WAITER SET IS NOT AN ARGUMENT ABOUT.  It says nothing
    about a SHARED futex, whose key `get_futex_key` resolves through the
    page and can name an inode any process on the machine may hold; and
    nothing about `FUTEX_WAKE_OP` or the requeue and PI commands, which
    touch `uaddr2` or a lock word before they look at a waiter at all.
    Every one of those is outside the two op words below. -/

/-- The address a futex operation names must be naturally aligned.

    `get_futex_key` (kernel/futex/core.c) is the first thing both
    modeled commands reach, and its first decision is

        key->both.offset = address % PAGE_SIZE;
        if (unlikely((address % size) != 0))
                return -EINVAL;

    with `size = futex_size(flags)`, which is `FUTEX_WORD_SIZE` for
    every call this spec can see (see that constant).  The test is on
    the address the caller passed, before any page is resolved, so it
    outranks every other answer either command has. -/
def futex_aligned_b (uaddr : word) : Bool :=
  (uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0

/-- `get_futex_key`'s two refusals, in its own order, and then the
    command's own answer.

    After the alignment test comes

        if (unlikely(!access_ok(uaddr, size)))
                return -EFAULT;

    (`get_futex_key`, kernel/futex/core.c) — the RANGE verdict
    `State.access_okb` decides, and the same `__access_ok` every other
    spec here goes through.  It is a range test and not a page lookup:
    on the private path `get_futex_key` returns as soon as it has the mm
    and the address, before any `get_user_pages_fast`, so an address
    that is in range and has NOTHING MAPPED AT IT passes this and
    reaches the command.  That is the one shape where the natural
    implementation of a futex spec — resolve the buffer against the
    model's memory and answer -EFAULT when it is not there — would be
    wrong.  The wake
    on such an address answers 0, not
    -EFAULT; the WAIT on the same address, which does resolve the page,
    really is -EFAULT, and declines here.  The difference between them
    is the whole content of this paragraph.

    The third `get_futex_key` error, `should_fail_futex(fshared)`, is
    reachable only with CONFIG_FAIL_FUTEX built in — and even then only
    for a SHARED key, because `fail_futex.ignore_private` starts true
    and short-circuits the private case.  Both modeled ops are private,
    so the fault injector cannot reach them from either of its two
    sites: the other, in `SYSCALL_DEFINE6(futex)`
    (kernel/futex/syscalls.c), is guarded by `!(op & FUTEX_PRIVATE_FLAG)`
    outright.  This is the rare environment obligation that the op gate
    discharges rather than states. -/
def futex_key_check (uaddr : word) (k : SysSpec SyscallEffect)
    : SysSpec SyscallEffect :=
  if !futex_aligned_b uaddr then err_ret EINVAL
  else if !access_okb uaddr FUTEX_WORD_SIZE then err_ret EFAULT
  else k

/-- FUTEX_WAKE with FUTEX_PRIVATE_FLAG: the number of waiters woken,
    which is 0.

    `futex_wake` (kernel/futex/waitwake.c) reaches its count through
    three gates and this spec answers past all three:

    - `if (!bitset) return -EINVAL;` cannot fire.  `do_futex`
      (kernel/futex/syscalls.c) overwrites `val3` with
      `FUTEX_BITSET_MATCH_ANY` on the `FUTEX_WAKE` arm before falling
      through to `FUTEX_WAKE_BITSET`, so the bitset this command is
      given is never the caller's.  `FUTEX_WAKE_BITSET` is a DIFFERENT
      op word and is declined, which is what keeps that distinction from
      being a coincidence.
    - `if ((flags & FLAGS_STRICT) && !nr_wake) return 0;` cannot fire
      either, and would be harmless if it did: `futex_to_flags`
      (kernel/futex/futex.h) never sets `FLAGS_STRICT` — only
      `futex2_to_flags`, for syscalls 454 and 455 — and the answer it
      guards is the same 0.
    - `if (!futex_hb_waiters_pending(hb)) return ret;` with `ret = 0` is
      the answer, by the empty-waiter-set argument at the top of this
      file.

    THE COUNT ARGUMENT IS NOT READ, deliberately.  `nr_wake` bounds a
    loop that runs zero times, so 0 is the answer for `INT_MAX` (what
    musl's `__wake` passes for a broadcast, src/thread/__wait.c) and for
    0 and for a negative alike.  A spec that gated on it would decline
    calls Linux answers and would be claiming the count mattered. -/
def futex_wake_private_spec (uaddr : word) : SysSpec SyscallEffect :=
  futex_key_check uaddr (ret_only (BitVec.ofInt 64 0))

/-- `FUTEX_WORD_SIZE` as a `Nat`, for the copy-in ledger.  The mirror is
    `Kernel.Fork.CLONE_ARGS_SIZE_nat`, and the lemma below is what keeps
    the two spellings from drifting. -/
def FUTEX_WORD_SIZE_nat : Nat := 4

theorem futex_word_size_nat_ok : (FUTEX_WORD_SIZE_nat : Int) = FUTEX_WORD_SIZE :=
  rfl

/-- FUTEX_WAIT with FUTEX_PRIVATE_FLAG and no timeout: -EAGAIN when the
    word does not hold `val`, and a decline when it does.

    `futex_wait_setup` (kernel/futex/waitwake.c) reads the word AFTER
    `get_futex_key` and compares it before it queues anything:

        ret = futex_get_value_locked(&uval, uaddr);
        ...
        if (uval != val) { futex_q_unlock(hb); return -EWOULDBLOCK; }

    and -EWOULDBLOCK IS -EAGAIN.  Every caller between that and the
    syscall boundary passes the value through unchanged — `__futex_wait`
    returns it before `futex_do_wait`, and `futex_wait` returns it
    untouched when `to` is NULL.  So this arm is not an approximation of
    a wait: it is the branch on which Linux never waits, and the value
    test is what separates it.

    THE MATCHING CASE DECLINES, and that is the honest answer rather
    than a gap grudgingly left.  Once `uval == val` the caller is queued
    and `futex_do_wait` blocks in `schedule()`; the two things that
    could end it are a wake from another task and a timer, and the model
    has neither (the header argues the first, and this arm requires a
    NULL timeout).  There is no step that resumes it, so no outcome to
    admit — including the "returns 0 spuriously" one, which
    `__futex_wait` reaches only after `futex_unqueue` finds the entry
    gone, i.e. after some task really did wake it.

    A NON-NULL TIMEOUT IS DECLINED BEFORE ANY OF THIS, at `futex_spec`.

    THE READ IS A COPY-IN.  `futex_get_value_locked`
    (kernel/futex/waitwake.c) is a `get_user`-class fetch of the four
    bytes at `uaddr`, and it has happened on both the -EAGAIN arm and
    the declining one, so `record_copyins` wraps the whole `some uval`
    arm.  The `none` arm carries no ledger and answers no errno: a word
    the model cannot read is one Linux would fault on
    (`futex_wait_setup` retries through `get_user` and returns its
    error), but the model's memory is a partial map rather than the
    kernel's page tables, so an absent byte is an absent FACT and this
    fails closed — the convention `Kernel.Time.Hrtimer.nanosleep_spec`
    states for its own request buffer. -/
def futex_wait_private_spec (uaddr val : word) : SysSpec SyscallEffect :=
  futex_key_check uaddr
    (bind inputSpec fun i =>
     match read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
     | none => unmodeled   -- the word is not readable: fail closed
     | some uval =>
         record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
           (if bv_eqb (le_bytes_to_word uval) val
            then unmodeled   -- the caller would block, and nothing wakes it
            else err_ret EAGAIN))

/-- The op word decides everything, and it is tested WHOLE.

    THE TEST IS ON THE FULL 64-BIT REGISTER, which is stricter than the
    kernel's own reading and deliberately so, exactly as
    `Kernel.Fork.clone_fork_flags_b` is.  `SYSCALL_DEFINE6(futex)`
    declares `int, op` (kernel/futex/syscalls.c), so Linux discards
    everything above bit 31 and a register of 0x1_00000081 is a private
    wake to it.  Declining is the fail-closed direction: the model
    refuses a call it could have answered rather than answering one it
    should not.  Nothing musl issues sets those bits — `__wake` and
    `__wait` (src/thread/__wait.c) build the word from
    `FUTEX_WAKE`/`FUTEX_WAIT` and `FUTEX_PRIVATE` alone.

    WHAT THE TWO WORDS EXCLUDE, and why each exclusion is a decline
    rather than an omission:

    - THE SHARED SPELLINGS, `FUTEX_WAKE` and `FUTEX_WAIT` with the
      private bit clear.  `futex_to_flags` (kernel/futex/futex.h) then
      sets `FLAGS_SHARED` and `get_futex_key` takes the page-resolving
      path, whose key can be one another process holds — so neither the
      empty waiter set nor the "-EFAULT is only the range verdict" claim
      survives, and both are load-bearing above.
    - `FUTEX_CLOCK_REALTIME` on either word.  `do_futex` tests
      `FLAGS_CLOCKRT` BEFORE its switch and permits the bit on only
      `FUTEX_WAIT_BITSET`, `FUTEX_WAIT_REQUEUE_PI` and `FUTEX_LOCK_PI2`,
      so a wake carrying it is -ENOSYS however well-formed the rest of
      the call is.  A spec that masked the op with `FUTEX_CMD_MASK` and
      threw the residue away would answer 0 there.
    - EVERY OTHER COMMAND.  The bitset forms take the caller's `val3`
      and so have an -EINVAL this spec does not model; `FUTEX_WAKE_OP`
      WRITES to `uaddr2` through `futex_atomic_op_inuser` before it
      looks at a waiter; the requeue and PI families need a second key,
      a lock word, or a waiter that exists.  All fall to `unmodeled`,
      which is where `do_futex`'s own `default: return -ENOSYS;` also
      lives — and the model does not answer -ENOSYS for them, because
      the number IS in the kernel's table and the decline is this
      model's, not Linux's.

    THE TIMEOUT ARGUMENT IS ONLY READ FOR A WAIT, which is the kernel's
    asymmetry rather than a shortcut.  `SYSCALL_DEFINE6(futex)` fetches
    it under `if (utime && futex_cmd_has_timeout(cmd))`, and
    `futex_cmd_has_timeout` (kernel/futex/syscalls.c) lists
    `FUTEX_WAIT`, `FUTEX_LOCK_PI`, `FUTEX_LOCK_PI2`,
    `FUTEX_WAIT_BITSET` and `FUTEX_WAIT_REQUEUE_PI` — not `FUTEX_WAKE`.
    So for a wake the third argument is dead, and gating on it would
    decline the very calls this arm exists for: musl's `__wake` and
    glib's uncontended broadcast both issue a three-argument
    `__syscall`, leaving argument 3 whatever the register held.  A
    non-NULL `utime` on a WAIT reaches `get_timespec64` and
    `futex_init_timeout`, which have an -EFAULT and an -EINVAL of their
    own AHEAD of everything above, and then arms a timer whose
    -ETIMEDOUT this model has no clock to produce; so it declines.

    Arguments 4 and 5 (`uaddr2` and `val3`) are read for neither word:
    `do_futex` overwrites `val3` on both arms and passes `uaddr2` only
    to commands outside them. -/
def futex_spec (uaddr op val utime : word) : SysSpec SyscallEffect :=
  if bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE)
  then futex_wake_private_spec uaddr
  else if bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE)
  then (if !w_is0 utime then unmodeled
        else futex_wait_private_spec uaddr (Sys.Syscall.abi_low32 val))
  else unmodeled

/-- WHEN THE CALL READS USER MEMORY, as a predicate on the arguments
    alone.

    The copy-in ledger is not decoration: `Run.sstep_syscall` charges
    lazy anonymous backing against `vm_limit` for the ranges in it, and
    an empty ledger is independently a CLAIM — that the syscall read no
    user memory.

    This predicate answers the same question for `futex` as a
    definition, and
    `Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact` proves it
    describes the ledger every answered call really carries.  So the
    tie is a theorem instead of a coincidence, which is what the mmap
    and mremap shape predicates buy with a shared definition and no
    lemma.

    IT IS A CONJUNCTION where the spec is a nest of ordered tests, and
    that costs nothing here because it is only ever read on an ANSWERED
    call: the two orderings differ on which of -EINVAL and -EFAULT wins,
    and neither of those arms reads anything. -/
def futex_wait_reads_b (uaddr op utime : word) : Bool :=
  bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) && w_is0 utime
  && futex_aligned_b uaddr && access_okb uaddr FUTEX_WORD_SIZE

/-- The two admitted op words are different words, so no call is both a
    wake and a wait.  Written out because the ledger argument below
    needs it and nothing else in this file does. -/
theorem futex_wake_not_wait (op : word)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = true) :
    bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = false := by
  have h' : op = BitVec.ofInt 64 FUTEX_WAKE_PRIVATE := beq_iff_eq.mp h
  subst h'
  decide

/-! ## Port checks

    There is no closed computation to re-use in this file and exactly one
    lemma (`futex_wake_not_wait`, ported above).  What follows is the
    port's own check on the computable part (AGENTS.md, "definition of
    done"): the alignment arithmetic, the three answers of
    `futex_key_check` in the kernel's own order, the dispatch's
    whole-word test and private-flag masking, and the copy-in ledger the
    -EAGAIN arm carries.  None of these is a reused lemma.

    The arm lemmas below are stated at an arbitrary input and model
    because the futex specs read NO model state — the model comes back
    unchanged on every answered arm, which is what lets the concrete
    checks use a universally quantified `m`. -/

/-! ### Inversion helpers for the monad (port scaffolding)

    `bind`/`inputSpec`/`pure` have no inversion lemmas at the concrete
    types, and the arm checks below need to read an outcome backwards.
    Each iff is definitional (`Iff.rfl`), so nothing is assumed: they
    only name the unfoldings `bind`'s and `pure`'s bodies already give. -/

private theorem bind_ok_iff {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) (y : B) (m2 : Model) (evs : List event) :
    bind c k i m (.ok y m2 evs) ↔
      ∃ x m1 evs1 evs2,
        c i m (.ok x m1 evs1) ∧ k x i m1 (.ok y m2 evs2) ∧ evs = evs1 ++ evs2 :=
  Iff.rfl

private theorem bind_unmodeled_iff {A B : Type} (c : SysSpec A) (k : A → SysSpec B)
    (i : SyscallInput) (m : Model) :
    bind c k i m .unmodeled ↔
      c i m .unmodeled ∨
        ∃ x m1 evs1, c i m (.ok x m1 evs1) ∧ k x i m1 .unmodeled :=
  Iff.rfl

private theorem input_iff (i : SyscallInput) (m : Model)
    (o : Outcome SyscallInput Model event) :
    inputSpec i m o ↔ o = .ok i m [] :=
  Iff.rfl

private theorem pure_iff {A : Type} (x : A) (i : SyscallInput) (m : Model)
    (o : Outcome A Model event) :
    pure x i m o ↔ o = .ok x m [] :=
  Iff.rfl

/-! ### The two `get_futex_key` refusals, in order

    EINVAL outranks EFAULT because `get_futex_key` tests the alignment
    before the range: a misaligned address PAST `TASK_SIZE` is -EINVAL,
    not -EFAULT, and the checks below pin both the answers and the
    order. -/

/-- A misaligned address is `-EINVAL`, decided before the range test. -/
theorem futex_key_check_einval (uaddr : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (h : futex_aligned_b uaddr = false) :
    futex_key_check uaddr k i m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  unfold futex_key_check err_ret ret_only
  simp [h]
  rfl

/-- An aligned address the range test refuses is `-EFAULT`. -/
theorem futex_key_check_efault (uaddr : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = false) :
    futex_key_check uaddr k i m
      (.ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  unfold futex_key_check err_ret ret_only
  simp [hal, hok]
  rfl

/-- Past both gates the command's own answer stands, untouched. -/
theorem futex_key_check_pass (uaddr : word) (k : SysSpec SyscallEffect)
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true) :
    futex_key_check uaddr k = k := by
  unfold futex_key_check
  simp [hal, hok]

/-! ### The wake arm

    A private wake answers 0 on every address that passes the two gates
    — and the count, the expected value and the timeout are read by
    nothing. -/

/-- The count a private wake returns is 0, with an inert effect. -/
theorem futex_wake_private_spec_ok (uaddr : word) (i : SyscallInput)
    (m : Model) (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true) :
    futex_wake_private_spec uaddr i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  unfold futex_wake_private_spec
  rw [futex_key_check_pass uaddr (ret_only (BitVec.ofInt 64 0)) hal hok]
  unfold ret_only
  rfl

/-! ### The wait arm's three non-gate answers -/

/-- A readable word that does not hold `val` is `-EAGAIN`, and the call
    has READ: the four bytes are in the copy-in ledger. -/
theorem futex_wait_private_spec_eagain (uaddr val : word) (i : SyscallInput)
    (m : Model) {uval : List byte}
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true)
    (hread : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = some uval)
    (hval : bv_eqb (le_bytes_to_word uval) val = false) :
    futex_wait_private_spec uaddr val i m
      (.ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
             (mkEffect (errno_ret EAGAIN) [] [])) m []) := by
  unfold futex_wait_private_spec
  rw [futex_key_check_pass uaddr _ hal hok]
  simp only [bind_ok_iff]
  refine ⟨i, m, [], [], rfl, ?_, rfl⟩
  simp only [hread, hval, record_copyins, bind_ok_iff]
  refine ⟨mkEffect (errno_ret EAGAIN) [] [], m, [], [], ?_, ?_, rfl⟩
  · unfold err_ret ret_only
    rfl
  · simp [with_copyins, pure_iff]

/-- A word the model cannot read is an absent FACT, and the call fails
    closed with no ledger and no errno. -/
theorem futex_wait_private_spec_unreadable (uaddr val : word)
    (i : SyscallInput) (m : Model)
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true)
    (hread : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = none) :
    futex_wait_private_spec uaddr val i m .unmodeled := by
  unfold futex_wait_private_spec
  rw [futex_key_check_pass uaddr _ hal hok]
  simp only [bind_unmodeled_iff, input_iff]
  refine Or.inr ⟨i, m, [], rfl, ?_⟩
  simp [hread, unmodeled]

/-- THE MATCHING CASE DECLINES: a readable word that DOES hold `val`
    would block, and nothing in this model wakes it. -/
theorem futex_wait_private_spec_would_block (uaddr val : word)
    (i : SyscallInput) (m : Model) {uval : List byte}
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true)
    (hread : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = some uval)
    (hval : bv_eqb (le_bytes_to_word uval) val = true) :
    futex_wait_private_spec uaddr val i m .unmodeled := by
  unfold futex_wait_private_spec
  rw [futex_key_check_pass uaddr _ hal hok]
  simp only [bind_unmodeled_iff, input_iff]
  refine Or.inr ⟨i, m, [], rfl, ?_⟩
  simp only [hread, hval]
  exact record_copyins_unmodeled (reads := [(uaddr, FUTEX_WORD_SIZE_nat)]) rfl

/-! ### The dispatch -/

/-- A private wake answers 0 whatever `val` and `utime` hold: neither
    argument is read on this arm. -/
theorem futex_spec_wake (uaddr op val utime : word) (i : SyscallInput)
    (m : Model)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = true)
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true) :
    futex_spec uaddr op val utime i m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  unfold futex_spec
  simp only [h, ite_true]
  exact futex_wake_private_spec_ok uaddr i m hal hok

/-- A private wait with a NULL timeout and a non-matching word is
    `-EAGAIN`, through the `abi_low32` narrowing of `val`. -/
theorem futex_spec_wait_eagain (uaddr op val utime : word)
    (i : SyscallInput) (m : Model) {uval : List byte}
    (hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = false)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = true)
    (ht : w_is0 utime = true)
    (hal : futex_aligned_b uaddr = true)
    (hok : access_okb uaddr FUTEX_WORD_SIZE = true)
    (hread : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = some uval)
    (hval : bv_eqb (le_bytes_to_word uval) (Sys.Syscall.abi_low32 val)
      = false) :
    futex_spec uaddr op val utime i m
      (.ok (with_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
             (mkEffect (errno_ret EAGAIN) [] [])) m []) := by
  unfold futex_spec
  simp only [hw, h, ht, Bool.not_true, ite_true]
  exact futex_wait_private_spec_eagain uaddr (Sys.Syscall.abi_low32 val) i m
    hal hok hread hval

/-- A NON-NULL timeout is declined before any of the wait's own gates is
    reached. -/
theorem futex_spec_wait_timeout (uaddr op val utime : word)
    (i : SyscallInput) (m : Model)
    (hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = false)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = true)
    (ht : w_is0 utime = false) :
    futex_spec uaddr op val utime i m .unmodeled := by
  unfold futex_spec
  simp [hw, h, ht, unmodeled]

/-- EVERY OTHER OP WORD FALLS TO `unmodeled`.  The model does not answer
    `-ENOSYS` there: the number IS in the kernel's table, and the
    decline is the model's, so the disjoint statement below says there
    is no answered outcome at all. -/
theorem futex_spec_other (uaddr op val utime : word) (i : SyscallInput)
    (m : Model)
    (hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = false)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = false) :
    futex_spec uaddr op val utime i m .unmodeled := by
  unfold futex_spec
  simp [hw, h, unmodeled]

/-- The same, stated as the ABSENCE OF AN ANSWER: on an unmodeled op word
    no effect, no model and no event list is admitted, so in particular
    none of them is `-ENOSYS`. -/
theorem futex_spec_other_no_answer (uaddr op val utime : word)
    (i : SyscallInput) (m : Model)
    (hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = false)
    (h : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = false) :
    ¬ ∃ eff m' evs, futex_spec uaddr op val utime i m (.ok eff m' evs) := by
  rintro ⟨eff, m', evs, hok⟩
  unfold futex_spec at hok
  simp [hw, h, unmodeled] at hok

/-! ### Concrete checks

    One input: syscall 98 with four readable bytes at address 0 holding
    the little-endian word `1`.  `sanityMem` is `StateMemory`'s test
    memory; no part of the model refers to it. -/

private def demoInput : SyscallInput :=
  { in_sysno := 98, in_args := [], in_mem := sanityMem [1, 0, 0, 0],
    in_wmem := fun _ => none }

private theorem demo_read :
    read_bytes_map demoInput.in_mem 0 (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = some [1, 0, 0, 0] := by
  decide

private theorem demo_word : le_bytes_to_word [1, 0, 0, 0] = (1 : word) := by
  decide

/-! #### The alignment test -/

/-- A page-aligned address passes; `0x1000` is 4096. -/
example : futex_aligned_b (BitVec.ofInt 64 0x1000) = true := by decide

/-- The next three bytes fail: the test is `address % 4`, not `% PAGE_SIZE`. -/
example : futex_aligned_b (BitVec.ofInt 64 0x1001) = false := by decide
example : futex_aligned_b (BitVec.ofInt 64 0x1002) = false := by decide
example : futex_aligned_b (BitVec.ofInt 64 0x1003) = false := by decide

/-- Zero is aligned. -/
example : futex_aligned_b 0 = true := by decide

/-- A top-of-address-space address whose low two bits are clear is
    aligned even though it is far outside `TASK_SIZE`: the alignment test
    says nothing about range, which is the next gate. -/
example : futex_aligned_b (BitVec.ofInt 64 0x800000000000) = true := by decide

/-! #### EINVAL for a bad address, EFAULT for a refused range, 0 for a wake

    The three answers of `futex_wake_private_spec`, in the kernel's
    order. -/

/-- A misaligned address is -EINVAL. -/
example (m : Model) :
    futex_wake_private_spec 1 demoInput m
      (.ok (mkEffect (errno_ret EINVAL) [] []) m []) := by
  exact futex_key_check_einval 1 _ demoInput m (by decide)

/-- An aligned address past `TASK_SIZE` is -EFAULT, the range verdict. -/
example (m : Model) :
    futex_wake_private_spec (BitVec.ofInt 64 0x800000000000) demoInput m
      (.ok (mkEffect (errno_ret EFAULT) [] []) m []) := by
  exact futex_key_check_efault _ _ demoInput m (by decide) (by decide)

/-- An address in range that has NOTHING MAPPED at it still wakes: the
    answer is 0, not -EFAULT, because the private path never resolves the
    page.  `demoInput`'s memory is empty at `0x2000`. -/
example (m : Model) :
    futex_wake_private_spec (BitVec.ofInt 64 0x2000) demoInput m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  exact futex_wake_private_spec_ok _ demoInput m (by decide) (by decide)

/-- And the same call through the dispatcher, on the private wake word. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 0 demoInput m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  exact futex_spec_wake 0 _ 0 0 demoInput m (by decide) (by decide) (by decide)

/-- THE COUNT ARGUMENT IS NOT READ: `INT_MAX` (what musl's broadcast
    passes) answers 0 exactly as 0 does. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 2147483647 0 demoInput m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  exact futex_spec_wake 0 _ 2147483647 0 demoInput m (by decide) (by decide)
    (by decide)

/-- NOR IS THE TIMEOUT ARGUMENT, for a wake: a non-NULL `utime` (7) leaves
    the answer at 0. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 7 demoInput m
      (.ok (mkEffect (BitVec.ofInt 64 0) [] []) m []) := by
  exact futex_spec_wake 0 _ 0 7 demoInput m (by decide) (by decide) (by decide)

/-! #### The private-flag masking

    `FUTEX_WAKE_PRIVATE` is `FUTEX_WAKE | FUTEX_PRIVATE_FLAG` = 129 and
    `FUTEX_WAIT_PRIVATE` is `FUTEX_WAIT | FUTEX_PRIVATE_FLAG` = 128, and
    the dispatch tests those WORDS rather than a masked command: the
    shared spellings, a `FUTEX_CLOCK_REALTIME` decoration, and anything
    above bit 31 are all declined. -/

/-- The two admitted words. -/
example : BitVec.ofInt 64 FUTEX_WAKE_PRIVATE = 129 := by decide
example : BitVec.ofInt 64 FUTEX_WAIT_PRIVATE = 128 := by decide
example : BitVec.ofInt 64 FUTEX_WAKE = 1 := by decide

/-- The SHARED wake (`FUTEX_WAKE`, private bit CLEAR) is `unmodeled`: a
    shared key can be one another process holds. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAKE) 0 0 demoInput m .unmodeled := by
  exact futex_spec_other 0 _ 0 0 demoInput m (by decide) (by decide)

/-- …and the shared WAIT is declined too, before any address is looked
    at. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAIT) 0 0 demoInput m .unmodeled := by
  exact futex_spec_other 0 _ 0 0 demoInput m (by decide) (by decide)

/-- A private wake carrying `FUTEX_CLOCK_REALTIME` (256) is 385: the model
    admits NO answer for it, so it does not answer the 0 a
    `FUTEX_CMD_MASK`-masking spec would, nor `do_futex`'s -ENOSYS. -/
example (m : Model) :
    ¬ ∃ eff m' evs,
      futex_spec 0 (BitVec.ofInt 64 385) 0 0 demoInput m (.ok eff m' evs) := by
  exact futex_spec_other_no_answer 0 _ 0 0 demoInput m (by decide) (by decide)

/-- THE TEST IS ON THE FULL 64-BIT REGISTER: the private wake word with
    bit 32 set (0x1_00000081) is declined, where Linux — declaring `int
    op` — would see FUTEX_WAKE_PRIVATE.  Fail closed. -/
example (m : Model) :
    ¬ ∃ eff m' evs,
      futex_spec 0 (BitVec.ofInt 64 0x100000081) 0 0 demoInput m (.ok eff m' evs) := by
  exact futex_spec_other_no_answer 0 _ 0 0 demoInput m (by decide) (by decide)

/-- An unimplemented command word (`FUTEX_WAKE_BITSET` is 10) is declined
    rather than answered with -ENOSYS: no answered outcome exists at
    all. -/
example (m : Model) :
    ¬ ∃ eff m' evs,
      futex_spec 0 (BitVec.ofInt 64 10) 0 0 demoInput m (.ok eff m' evs) := by
  exact futex_spec_other_no_answer 0 _ 0 0 demoInput m (by decide) (by decide)

/-! #### The wait arm

    `demoInput` holds the word 1 at address 0, so `val = 1` matches (and
    the call declines: nothing would wake it) and `val = 2` does not (and
    the call is -EAGAIN with the four-byte read recorded). -/

/-- The word does not hold `val`: -EAGAIN, with `(uaddr, 4)` in the
    copy-in ledger. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 2 0 demoInput m
      (.ok (with_copyins [(0, FUTEX_WORD_SIZE_nat)]
             (mkEffect (errno_ret EAGAIN) [] [])) m []) := by
  exact futex_spec_wait_eagain 0 _ 2 0 demoInput m (by decide) (by decide)
    (by decide) (by decide) (by decide) demo_read (by decide)

/-- The word DOES hold `val`: the caller would block, and the model
    declines — there is no answer on this address, not even the spurious
    0 that a wake would produce. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 1 0 demoInput m
      .unmodeled := by
  have hw : bv_eqb (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE)
      (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) = false := by decide
  have h : bv_eqb (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE)
      (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = true := by decide
  have hval : bv_eqb (le_bytes_to_word [1, 0, 0, 0])
      (Sys.Syscall.abi_low32 1) = true := by
    rw [demo_word]
    decide
  unfold futex_spec
  simp only [hw, h, w_is0, ite_true]
  exact futex_wait_private_spec_would_block 0 1 demoInput m (by decide)
    (by decide) demo_read hval

/-- A non-NULL timeout on a wait is declined before the value is ever
    read — `demoInput`'s word would otherwise have made this -EAGAIN. -/
example (m : Model) :
    futex_spec 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 2 0x1000 demoInput m
      .unmodeled := by
  exact futex_spec_wait_timeout 0 _ 2 0x1000 demoInput m (by decide)
    (by decide) (by decide)

/-- A wait on a word the model cannot read fails closed, with no ledger
    and no errno.  `0x2000` is in range but unmapped; the WAIT resolves
    the page where the wake does not. -/
example (m : Model) :
    futex_wait_private_spec (BitVec.ofInt 64 0x2000) 0 demoInput m
      .unmodeled := by
  exact futex_wait_private_spec_unreadable _ 0 demoInput m (by decide)
    (by decide) (by decide)

/-! #### `futex_wait_reads_b`, the ledger predicate -/

/-- A private wait with a NULL timeout on an aligned, in-range address
    reads: that is the only answered arm that does. -/
example : futex_wait_reads_b 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 0 = true := by
  decide

/-- A wake reads nothing, whatever its address. -/
example :
    futex_wait_reads_b 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 = false := by
  decide

/-- Nor does a wait with a timeout (which declines), or one at an address
    the alignment test refuses. -/
example : futex_wait_reads_b 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 1 = false := by
  decide
example : futex_wait_reads_b 1 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 0 = false := by
  decide

/-- The predicate is on the ARGUMENTS ALONE: it is `true` even where the
    memory holds nothing at all, because it describes the ledger of an
    ANSWERED call and an unreadable word is not one. -/
example : futex_wait_reads_b (BitVec.ofInt 64 0x2000)
    (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 0 = true := by
  decide

/-! #### The disjointness lemma -/

/-- `futex_wake_not_wait`, applied: the wake word is not the wait word. -/
example :
    bv_eqb (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE)
      (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = false :=
  futex_wake_not_wait _ (by decide)

/-- …and the size mirror: the `Nat` ledger width is the `Int` ABI width. -/
example : FUTEX_WORD_SIZE_nat = 4 := rfl

end LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
