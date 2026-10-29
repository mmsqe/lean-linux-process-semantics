/-
  * LinuxSem.Checks.Cases.Kernel.Sched.Syscalls — worked examples over sched_getaffinity (123), sched_setscheduler (119), sched_yield (124)

  Worked cases over `Sys.Kernel.Sched.Syscalls`, which answers to Linux
  [kernel/sched/syscalls.c]: the examples for the syscalls defined there,
  and no others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  `Z` is `Int`, `Z_to_bv 64 z` is `BitVec.ofInt 64 z`,
  `bv_unsigned w` is `(w.toNat : Int)`, `mkInput` is the `SyscallInput`
  constructor and `CheckOk`/`CheckReject`/`CheckUnmodeled` are the
  `check_result` constructors.  The local `infix` notations restore the
  `Z` comparisons verbatim, and the `In` alias below restores the
  membership spelling for the one `modeled_sysnos` example.

  The `demo_model` fixture.  It is defined beside the id calls that
  mutate it, in [Checks/Cases/Kernel/Sys], and shared rather than
  redefined — `Checks.Examples` re-exports every Cases module into one
  namespace, so two definitions of a name would shadow each other.  The
  fixture here is that `demo_model`, imported and not restated.

  Proofs.  Every example here is a conjunction of closed equations, so it
  is `(try dsimp only); (repeat constructor) <;> rfl`.  The two
  singletons are `rfl` and, for the `modeled_sysnos` membership, `decide`
  (membership in a literal list of `Int` is decidable).  `rfl` rather
  than `decide` for the equations: `check_result` carries a `Model` and
  has no `DecidableEq`.

  THE EXCEPTION is the six `sched_setscheduler` examples: their arm reads
  the priority out of user memory through an `Int` quotient of a
  `BitVec.toNat`, which the kernel cannot reduce, so `rfl` cannot convert
  the goal to the checker at all.  They are proved by the two-lemma route
  under "How the `sched_setscheduler` examples are proved" below — one
  `by decide` per conjunct plus a lemma that the accepted answer IS the
  input model — and every conjunct is still checked separately.

  The machinery here.  Seven declarations in this file are this file's
  own bridge, not statements about the model: `isOkR`/`isRejectR` and
  their reflection lemmas, the dispatch bridge
  `check_syscall_sched_setscheduler`, and
  `sched_setscheduler_ok_is_self`/`sched_ok_self`.  They state nothing
  about the model that the examples do not, and they are named as
  machinery rather than as lemmas to cite.

  `sched_param_mem`'s shift.  The priority field sits at `8 * off` bits
  with `off : Int`.  Lean has no `HPow Int Int Int`, so the exponent is
  spelled `(8 * off).toNat` — the same value on the only branch that is
  taken (`0 ≤ off < 4`, so `8 * off` is a non-negative `Nat`) and a
  truncation to `0` elsewhere, where the byte is not selected at all.
  Nothing is weakened: the examples below are `rfl`, so the definition is
  judged by the bytes it produces.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.CheckToolkit
import LinuxSem.Checks.Cases.Kernel.Sys
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
import LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Specs
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Sched.Syscalls
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Kernel.Sys

namespace LinuxSem.Checks.Cases.Kernel.Sched.Syscalls

open LinuxSem.Common.RocqSpelling

/-! `bv_unsigned`, `Z_to_bv`, `zleb`/`zltb` come from
    `LinuxSem.Common.RocqSpelling`, opened above. -/

/-- `<=?` on `Z`. -/
local infix:50 " <=? " => zleb
/-- `<?` on `Z`. -/
local infix:50 " <? " => zltb

/-- `In a l`, which Lean spells `a ∈ l`. -/
abbrev In (a : Int) (l : List Int) : Prop := a ∈ l

def sched_getaffinity_in (pid len user_mask_ptr : word) : SyscallInput :=
  SyscallInput.mkInput 123 [pid, len, user_mask_ptr, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! THE WRAPPING LENGTHS.  [len] is an [unsigned int] and
    [BITS_PER_BYTE] is a plain [8], so [len * BITS_PER_BYTE] is computed
    in 32 bits.  The product is zero exactly on the multiples of 2^29,
    and [nr_cpu_ids] is at least 1, so every one of them is -EINVAL —
    the large ones included, which read as obviously-big-enough to a
    model that did the multiplication over the integers.  The pid and
    the mask pointer are garbage throughout: both gates run before
    either is looked at. -/
theorem sched_getaffinity_wrapping_lengths_are_einval :
  let einval := mkEffect (errno_ret EINVAL) [] [] ;
  check_syscall (sched_getaffinity_in 0 0 3735928559) einval demo_model
    = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 1073741824 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 1610612736 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 2147483648 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 2684354560 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 3221225472 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 3758096384 3735928559) einval demo_model
       = .CheckOk demo_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE LENGTHS CONGRUENT TO 4 MOD 8 are what tell the native gate's
    [& 7] from the compat gate's [& 3], and they are the sharpest
    available mistake: a spec written from kernel/compat.c's
    [COMPAT_SYSCALL_DEFINE3(sched_getaffinity)] instead of
    kernel/sched/syscalls.c's would call these MODELED-OUT and still
    answer -EINVAL for every other length in this file.  They are
    -EINVAL for an LP64 caller, which is the only kind this model
    loads. -/
theorem sched_getaffinity_compat_aligned_lengths_are_einval :
  let einval := mkEffect (errno_ret EINVAL) [] [] ;
  check_syscall (sched_getaffinity_in 0 4 3735928559) einval demo_model
    = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 12 3735928559) einval demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (sched_getaffinity_in 0 4294967292 3735928559) einval demo_model
       = .CheckOk demo_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! …and the boundary is exactly where the wrap puts it.  The two
    neighbours of 2^29 are eight-aligned like it, differ from it by one
    machine word, and are NOT refused: their bit counts are 2^32 - 64
    and 64, neither of which is below every [nr_cpu_ids].  So the model
    declines them rather than guess, and that is the discrimination this
    file exists for — an arm that refused every large length, or every
    length above some cap, would answer -EINVAL here too, and only these
    cases tell it apart. -/
theorem sched_getaffinity_wrap_neighbours_are_unmodeled :
  let einval := mkEffect (errno_ret EINVAL) [] [] ;
  check_syscall (sched_getaffinity_in 0 536870904 3735928559) einval demo_model
    = .CheckUnmodeled
  ∧ check_syscall (sched_getaffinity_in 0 536870920 3735928559) einval demo_model
       = .CheckUnmodeled
  /- AND THE WRAP ITSELF, STILL ANSWERED, between them.  The two
     declines are both [CheckUnmodeled], so on their own they stay green
     under any change that declines MORE -- the wrapping-length arm
     going unmodeled along with its neighbours, which erases the very
     discrimination the paragraph above claims.  2^29 is the point the
     two neighbours are neighbours OF; pinning it here is what makes
     this lemma fail when the boundary moves rather than merely say
     where it is. -/
  ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559) einval demo_model
       = .CheckOk demo_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE NEGATIVE DIRECTION, which no real run can produce: a kernel
    that answered a wrapping length with a plausible byte count, with
    the -EFAULT its untouched pointer cannot produce, or with the errno 3
    (-ESRCH) its unreached task lookup cannot produce, is REJECTED.  So is
    one that answered -EINVAL and wrote to the mask anyway: nothing is
    stored before either gate.  -ESRCH is spelled as the number because
    `State` has no constant for it. -/
theorem sched_getaffinity_wrapping_length_lies_rejected :
  check_syscall (sched_getaffinity_in 0 536870912 3735928559)
    (mkEffect 8 [] []) demo_model = .CheckReject
  ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) demo_model = .CheckReject
  ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret 3) [] []) demo_model = .CheckReject
  ∧ check_syscall (sched_getaffinity_in 0 536870912 3735928559)
       (mkEffect (errno_ret EINVAL) [(3735928559, [Z_to_bv 8 0])] []) demo_model
       = .CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/- -------------------------------------------------------------------------
   sched_setscheduler (119)

   These are here for the FOURTH of the four reasons listed at the top of
   `Checks.Examples` for the [CheckReject]s — a lying kernel is the only
   thing that produces them — and for the SECOND for the pairs below that
   separate two -EINVALs a real run cannot tell apart.  The kernel
   answers -EINVAL by four different routes and by the same number, so
   a real run cannot say WHICH route a model took; the discriminations that need saying are
   made here, against the checker.
   ------------------------------------------------------------------------- -/

def sched_setscheduler_in (pid policy param : word)
    (mem : word → Option byte) : SyscallInput :=
  SyscallInput.mkInput 119 [pid, policy, param, 0, 0, 0] mem (fun _ => none)

/-! Four readable bytes at address 4096 holding a little-endian [int],
    which is the whole of a [struct sched_param].  Nothing else in the
    address space is readable, which is what makes the -EFAULT and
    decline cases below reachable at all. -/
def sched_param_mem (v : Int) : word → Option byte :=
  fun a =>
    let off := (bv_unsigned a - 4096) ;
    if ((0 <=? off) && (off <? 4))
    then some (Z_to_bv 8 ((v / 2 ^ ((8 * off).toNat)) % 256))
    else none

def sched_param_ptr : word := Z_to_bv 64 4096

/-! ### How the `sched_setscheduler` examples are proved: `isOkR` + `sched_ok_self`

    The `rfl` wall — MEASURED, and the route out of it.  A
    `sched_setscheduler` call reads its priority out of user memory, and
    `sched_param_mem`'s byte at offset `off` is
    `(v / 2 ^ (8 * off)) % 256`: an `Int` quotient of an `Int.ofNat` of a
    `BitVec.toNat`.  Asking the KERNEL for that reduction —
    `rfl`/`change`/`show` — does not terminate (`maxRecDepth` at 10^6; the
    kernel stack overflows well before 10^7), while `by decide` closes the
    same fact.  Since a `check_syscall … = …` goal must be CONVERTED to the
    checker before any rewriting applies, and `check_result` carries a
    `Model` (so there is no `DecidableEq`), no `rfl` reaches these goals at
    all.  That is the wall this section is about.

    The route below is NOT route B (staged evaluation): it needs no
    per-branch `ite_eq_left`/`ite_eq_right`, and that matters here because the six
    examples pin a different argument set per conjunct — fourteen of them.
    It is route A with the payload carried by a LEMMA instead of by the
    reflection:

    - `isOkR` projects `check_result` to a `Bool` on constructors only, so
      `by decide` can compute it.  That is the same device as
      `Checks.Cases.CheckToolkit`'s `isUnmodeledR`, and it works for
      the same reason: the projection never touches `Model`.
    - `sched_setscheduler_ok_is_self` is the one piece of real proof: an
      accepted `sched_setscheduler` answer leaves the model EXACTLY as it
      found it and emits no event.  It is a `split` walk over the checker's
      leaves, and each leaf is read off the `…_ok_iff` lemmas of
      `Checks/Sys/Prelude.lean`, which pin `m' = m` and `evs = []` for
      `check_ret_only` and `check_ret_only_copyins`.  Note what it does NOT
      need: no `by decide`, and no knowledge of any argument.
    - `sched_ok_self` composes the two: "the constructor is `CheckOk`"
      (decidable, hence `by decide`) plus "an accepted answer is the input
      model" (the lemma) gives `r = .CheckOk m []` — the payload IS the
      input model, which is what every `CheckOk` conjunct below claims.

    With that, each conjunct is ONE tactic application: `by decide` for the
    projection (0.1-0.3 s) and `sched_ok_self` for the payload.  A
    `CheckReject` conjunct needs even less: `isRejectR` projects it and
    `isRejectR_eq_true` reflects it, again with `by decide`.
    `CheckUnmodeled` conjuncts go through the toolkit's `check_unmodeled`.
    None of this is `native_decide`: every proof is an ordinary proof term,
    so no extra postulate enters the library. -/

/-- `check_result`'s constructor as a `Bool`, `true` at every `CheckOk`.
    Constructor-only ON PURPOSE — it must not touch the `Model` payload,
    which is what lets `by decide` compute it. -/
def isOkR : check_result → Bool
  | .CheckOk _ _ => true
  | _ => false

/-- Route A's reflection for `CheckOk`, with an existential payload: what
    `by decide` can see is only the constructor. -/
theorem isOkR_eq_true (r : check_result) :
    isOkR r = true ↔ ∃ m evs, r = .CheckOk m evs := by
  cases r <;> simp [isOkR]

/-- …and the same for `CheckReject`, whose payload is nullary, so this one
    reflection alone settles a whole class of conjuncts. -/
def isRejectR : check_result → Bool
  | .CheckReject => true
  | _ => false

theorem isRejectR_eq_true (r : check_result) :
    isRejectR r = true ↔ r = .CheckReject := by
  cases r <;> simp [isRejectR]

/-- The dispatch, resolved once: sysno 119 is
    `Dispatch.arm_sched_setscheduler`, which passes `in_arg i 0/1/2` as
    `pid`/`policy`/`param`.  The kernel resolves the `checked_table` lookup
    because `lookup_ca` at a literal number is a closed computation over
    arms whose `ca_no` is `rfl`-known. -/
theorem check_syscall_sched_setscheduler (pid policy param : word)
    (mem : word → Option byte) (eff : SyscallEffect) (m : Model) :
    check_syscall (sched_setscheduler_in pid policy param mem) eff m
      = check_sched_setscheduler (sched_setscheduler_in pid policy param mem)
          pid policy param eff m := by
  simp only [LinuxSem.Checks.ExecutableSpecs.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.CheckedTable.check_syscall,
    LinuxSem.Checks.Sys.Dispatch.check_syscall, sched_setscheduler_in]
  exact Sys.Dispatch.ca_check_arm_sched_setscheduler _ _ _

/-- AN ACCEPTED `sched_setscheduler` ANSWER IS THE INPUT MODEL, with no
    event: the checker's only accepted forms are
    `check_ret_only eff r m []` and `check_ret_only_copyins reads eff r m []`,
    and both return the model they were handed.

    Proved for ARBITRARY arguments — no `by decide`, nothing about any
    particular call — which is what lets the fourteen examples below spend
    one `by decide` each instead of replaying this walk. -/
theorem sched_setscheduler_ok_is_self (i : SyscallInput) (pid policy param : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_sched_setscheduler i pid policy param eff m = .CheckOk m' evs) :
    m' = m ∧ evs = [] := by
  unfold check_sched_setscheduler at H
  repeat' split at H
  all_goals
    first
    | exact ((check_ret_only_ok_iff _ _ _ _ _ _).mp H).2
    | exact ((check_ret_only_copyins_ok_iff _ _ _ _ _ _ _).mp H).2
    | exact nomatch H

/-- Route A plus that lemma: a `check_syscall` whose constructor is
    `CheckOk` answers `.CheckOk m []` — the input model, no events.  This
    is the whole closer for the `CheckOk` conjuncts below. -/
theorem sched_ok_self (pid policy param : word) (mem : word → Option byte)
    (eff : SyscallEffect) (m : Model)
    (h : isOkR (check_syscall (sched_setscheduler_in pid policy param mem) eff m) = true) :
    check_syscall (sched_setscheduler_in pid policy param mem) eff m
      = .CheckOk m [] := by
  obtain ⟨m', evs, he⟩ := (isOkR_eq_true _).mp h
  have hb : check_sched_setscheduler (sched_setscheduler_in pid policy param mem)
      pid policy param eff m = .CheckOk m' evs := by
    rw [← check_syscall_sched_setscheduler]; exact he
  obtain ⟨rfl, rfl⟩ := sched_setscheduler_ok_is_self _ _ _ _ _ _ _ _ hb
  exact he

/-! THE PRIORITY IS A [__u32] AT THE RANGE GATE, and this is the pair
    that says so.  [struct sched_param] holds an [int], and
    [_sched_setscheduler] copies it into [struct sched_attr]'s [__u32
    sched_priority], so -1 meets [attr->sched_priority > MAX_RT_PRIO-1]
    as 4294967295 and is refused THERE — by the same gate that refuses
    100, and before the [rt_policy(policy) != (sched_priority != 0)]
    comparison ever runs.  Both answers are -EINVAL, so no real run can
    separate them; what CAN be separated is 99, which the range gate
    admits, from -1, which it does not.  A model that read the field
    signed would put -1 on the far side of the range gate and reach the
    same -EINVAL through the RT-agreement test for SCHED_IDLE — and
    would then have to answer SCHED_FIFO at priority -1 with a success,
    which is the case that fails here. -/

/-! PROVED by the route at the head of this group: one `by decide` per
    conjunct (route A's constructor projection), plus `sched_ok_self` for
    the payload — the accepted answer is the INPUT model, which is the
    claim these three conjuncts make.

    The claim: the range gate is `> MAX_RT_PRIO - 1`, so `2^32 - 1`
    (that is, -1 read as a signed int) and 100 both sit past it and answer
    -EINVAL — with the four copied-in parameter bytes recorded, since the
    range test runs after the copy-in.  99 is INSIDE the range, where the
    model declines the call as unmodeled rather than pretend it
    rescheduled anything.
-/
theorem sched_setscheduler_negative_priority_is_out_of_range :
  let einval := mkEffect (errno_ret EINVAL) [] [] ;
  let einval_c := with_copyins [(sched_param_ptr, 4)] einval ;
  check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                   (sched_param_mem 4294967295)) einval_c demo_model
    = .CheckOk demo_model []
  /- AND 99 AT THE SAME POLICY IS NOT OUT OF RANGE, while 100 is: the gate
     is `> MAX_RT_PRIO - 1`, so the boundary sits between them. -/
  ∧ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                       (sched_param_mem 99)) einval_c demo_model
       = .CheckUnmodeled
  ∧ check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                       (sched_param_mem 100)) einval_c demo_model
       = .CheckOk demo_model []
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/-! THE ORDER OF THE TWO PRE-COPY -EINVALS, on a call that is wrong in
    three ways at once.  [policy < 0] is decided in
    [SYSCALL_DEFINE3(sched_setscheduler)] itself, before
    [do_sched_setscheduler] is entered, so a negative policy beats the
    null [param] and the negative pid beside it — and beats the -EFAULT
    an unreadable [param] would raise, which is the discrimination the
    unreadable pointer here makes.  A model that tested the pointer
    first would answer -EFAULT to the second of these. -/

/-! PROVED by the route at the head of this group.  The first two conjuncts
    pin WHICH -EINVAL route the model takes — each accepts an `einval`
    effect, so the answer names the branch — and the third pins the
    positive half of the same call.  Three different argument words, so
    they are checked one by one rather than by a single evaluation.

    The claim: the policy word is read as a signed int, so `2^64 - 1` is
    a NEGATIVE policy and the policy test rejects it before the pid and
    the param word are looked at — an unreadable null param and a negative
    pid sit beside it in the second conjunct and neither is what decides.
    Conversely `2^32 + 5` has low half 5, i.e. SCHED_IDLE, and that call
    succeeds with the copy-in recorded.
-/
theorem sched_setscheduler_negative_policy_wins :
  let einval := mkEffect (errno_ret EINVAL) [] [] ;
  check_syscall (sched_setscheduler_in (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) 0 (fun _ => none))
    einval demo_model = .CheckOk demo_model []
  /- …and here the POLICY is what is negative, with an unreadable null
     [param] and a negative pid beside it: both of those would also be
     -EINVAL, and the policy test runs first. -/
  ∧ check_syscall (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 64 - 1))
                      (Z_to_bv 64 (2 ^ 63)) (fun _ => none))
       einval demo_model = .CheckOk demo_model []
  /- …and the low half alone decides: 2^32 + 5 is `sint32` 5, so this call
     is SCHED_IDLE and succeeds, with the copy-in recorded. -/
  ∧ check_syscall (sched_setscheduler_in 0 (Z_to_bv 64 (2 ^ 32 + 5))
                       sched_param_ptr (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4)] (mkEffect (Z_to_bv 64 0) [] []))
       demo_model = .CheckOk demo_model []
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/-! -EFAULT IS THE RANGE VERDICT AND NOTHING ELSE, and it records no
    copy-in.  [access_ok] refuses four bytes whose last one is at
    [State.TASK_SIZE], and refuses them before a load, so the answer
    carries an empty ledger; a range [access_ok] ADMITS that memory does
    not back is declined instead, because Linux answers -EFAULT there
    too and the ledger cannot say which bytes it read first.  The two
    addresses below are three bytes apart and land on opposite sides of
    that line. -/

/-! PROVED by the route at the head of this group: `CheckOk` and
    `CheckReject` conjuncts through the projections, the declined one
    through the toolkit's `check_unmodeled`.

    The claim: an unreadable parameter word answers -EFAULT from the
    range verdict, records no copy-in, and the model is untouched.
-/
theorem sched_setscheduler_fault_is_the_range_verdict :
  let efault := mkEffect (errno_ret EFAULT) [] [] ;
  check_syscall (sched_setscheduler_in 0 5
                   (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => none))
    efault demo_model = .CheckOk demo_model []
  /- …and the neighbour three bytes lower, whose LAST byte is at TASK_SIZE,
     is outside `access_ok`: it is declined rather than guessed. -/
  ∧ check_syscall (sched_setscheduler_in 0 5
                      (Z_to_bv 64 (TASK_SIZE - 4)) (fun _ => none))
       efault demo_model = .CheckUnmodeled
  /- …and a copy-in ledger on the -EFAULT answer is a lie: nothing is
     stored before `access_ok`. -/
  ∧ check_syscall (sched_setscheduler_in 0 5
                      (Z_to_bv 64 (TASK_SIZE - 3)) (fun _ => none))
       (with_copyins [(Z_to_bv 64 (TASK_SIZE - 3), 4)] efault) demo_model
       = .CheckReject
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/-! THE DECLINES, each on the exact argument that makes it one.  Every
    call here is one Linux ANSWERS — SCHED_FIFO at priority 1 and
    SCHED_NORMAL at 0 are ordinary requests, and SCHED_IDLE with
    SCHED_RESET_ON_FORK is a 0 — so each is a claim about the model
    alone, which is why they are here. -/

/-! PROVED by the toolkit's `check_unmodeled`, one `by decide` per
    conjunct: all six answers are the nullary `CheckUnmodeled`, so no
    payload has to be reached — which is exactly the case `check_unmodeled`
    settles on its own.

    The claim: six argument sets each answer the nullary
    `CheckUnmodeled` — the model says nothing about them, and each is
    named by the argument that makes it one.
-/
theorem sched_setscheduler_declines :
  let ok := with_copyins [(sched_param_ptr, 4)]
              (mkEffect (Z_to_bv 64 0) [] []) ;
  check_syscall (sched_setscheduler_in 0 1 sched_param_ptr
                   (sched_param_mem 1)) ok demo_model = .CheckUnmodeled
  /- SCHED_NORMAL at 0 is an ordinary request, and it is declined: the model
     answers 0 to a call that CHANGES policy and it cannot say it did. -/
  ∧ check_syscall (sched_setscheduler_in 0 0 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = .CheckUnmodeled
  ∧ check_syscall (sched_setscheduler_in 0 3 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = .CheckUnmodeled
  ∧ check_syscall (sched_setscheduler_in 0 7 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = .CheckUnmodeled
  /- …SCHED_RESET_ON_FORK is the high-bit flag and not a policy of its own,
     so 5 + 2^30 is still SCHED_IDLE. -/
  ∧ check_syscall (sched_setscheduler_in 0
                      (Z_to_bv 64 (5 + 2 ^ 30)) sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = .CheckUnmodeled
  /- …and pid 4096 names a task this model has no representation of. -/
  ∧ check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr
                      (sched_param_mem 0)) ok demo_model = .CheckUnmodeled
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/-! THE ONE ANSWER PAST THE TASK LOOKUP, and the lies a kernel would
    have to tell to make it something else.  -EPERM is the sharpest of
    them: it is what the call really returns when
    [p->sched_reset_on_fork] is set or when a capability is missing, so
    a model that had made the SCHED_IDLE answer depend on a credential
    it does not carry would ACCEPT it here and agree with this file
    everywhere else. -/

/-! PROVED by the route at the head of this group.  Four of the five
    conjuncts are `CheckReject`s, i.e. the lies a kernel would have to tell
    to make this answer something other than 0.

    The claim: SCHED_IDLE at a valid param word answers 0 with the model
    unchanged, and four other answers are rejected — -EPERM (a capability
    the caller may lack), -EINVAL, a 0 that claims to have written the
    struct back, and a 0 that forgets the copy-in it did make.
-/
theorem sched_setscheduler_idle_is_zero :
  let ok := with_copyins [(sched_param_ptr, 4)]
              (mkEffect (Z_to_bv 64 0) [] []) ;
  check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                   (sched_param_mem 0)) ok demo_model = .CheckOk demo_model []
  /- …and -EPERM in its place is a lie a kernel CAN tell (missing capability,
     `sched_reset_on_fork`), which is the point of pinning it out. -/
  ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4)]
          (mkEffect (errno_ret EPERM) [] [])) demo_model = .CheckReject
  ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4)]
          (mkEffect (errno_ret EINVAL) [] [])) demo_model = .CheckReject
  /- …as is a 0 that claims to have written the struct back. -/
  ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (with_copyins [(sched_param_ptr, 4)]
          (mkEffect (Z_to_bv 64 0) [(sched_param_ptr, [Z_to_bv 8 0])] []))
       demo_model = .CheckReject
  /- …and one that forgets the copy-in it did make. -/
  ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0))
       (mkEffect (Z_to_bv 64 0) [] []) demo_model = .CheckReject
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/-! THE PID THE PINNED TID NAMES, against one it does not, on the SAME
    model.  This is the shape musl's [pthread_setschedparam] issues — it
    passes [t->tid], never 0 — so the pair matters: an arm that answered
    only pid 0 leaves every real caller outside the modeled surface, and
    an arm that answered any positive pid would be claiming to know
    about a task it has no representation of. -/

/-! PROVED by the route at the head of this group; the model here is
    `with_tid (Z_to_bv 64 4096) demo_model`, and the `CheckOk`s answer THAT
    model, so the pair also pins that a successful call does not move it.

    The claim: `4096` names the pinned tid — and so do `2^32 + 4096`
    through its low half and `0`, which resolves to that tid — while
    `4097` names a task the model has no representation of and declines
    unmodeled.  All of it on the SAME model, and the answered model IS the
    input model, which pins that a successful call does not move it.
-/
theorem sched_setscheduler_pid_is_the_pinned_tid :
  let m := with_tid (Z_to_bv 64 4096) demo_model ;
  let ok := with_copyins [(sched_param_ptr, 4)]
              (mkEffect (Z_to_bv 64 0) [] []) ;
  check_syscall (sched_setscheduler_in 4096 5 sched_param_ptr
                   (sched_param_mem 0)) ok m = .CheckOk m []
  /- …the same tid through the low half of a wider value. -/
  ∧ check_syscall (sched_setscheduler_in (Z_to_bv 64 (2 ^ 32 + 4096)) 5
                      sched_param_ptr (sched_param_mem 0)) ok m = .CheckOk m []
  /- …one it does NOT name, which is declined rather than guessed. -/
  ∧ check_syscall (sched_setscheduler_in 4097 5 sched_param_ptr
                      (sched_param_mem 0)) ok m = .CheckUnmodeled
  /- …and 0, the calling thread, which `_sched_setscheduler` resolves to the
     pinned tid. -/
  ∧ check_syscall (sched_setscheduler_in 0 5 sched_param_ptr
                      (sched_param_mem 0)) ok m = .CheckOk m []
:= by
  (repeat' apply And.intro) <;>
    first
    | exact sched_ok_self _ _ _ _ _ _ (by decide)
    | exact (isRejectR_eq_true _).mp (by decide)
    | check_unmodeled

/- -------------------------------------------------------------------------
   sched_yield (124)

   These are here for the last of the four reasons at the top of
   `Checks.Examples`: a [CheckReject] needs a kernel answering
   something no kernel answers.  The accepting half is reachable by a
   real run.  What no real run can show at all is the refusing
   half: that the model rejects the answers Linux never gives, and that
   it accepts 0 for every argument word rather than for the ones a run
   happened to pass.
   ------------------------------------------------------------------------- -/

def sched_yield_in (a0 a1 a2 a3 a4 a5 : word) : SyscallInput :=
  SyscallInput.mkInput 124 [a0, a1, a2, a3, a4, a5] (fun _ => none) (fun _ => none)

def sched_yield_zeros : SyscallInput := sched_yield_in 0 0 0 0 0 0

/-! 124 is dispatched at all: without an arm, a target that called it
    would reach the error transition. -/
theorem sched_yield_is_modeled : In 124 modeled_sysnos
:= by decide

/-! THE ANSWER IS 0 AND NOTHING ELSE MOVES.  [SYSCALL_DEFINE0(sched_yield)]
    is [do_sched_yield(); return 0;] (kernel/sched/syscalls.c, Linux
    v6.12.1), and everything [do_sched_yield] touches is per-run-queue
    scheduler bookkeeping this model has no representation of. -/
theorem sched_yield_answers_zero :
  check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 0) [] []) demo_model
  = .CheckOk demo_model []
:= by rfl

/-! EVERY ARGUMENT WORD IS IGNORED, and that is the kernel's own shape
    rather than this spec's convenience: riscv64's [SYSCALL_DEFINE0]
    (arch/riscv/include/asm/syscall_wrapper.h) takes
    [const struct pt_regs *__unused] and expands without
    [SC_RISCV_REGS_TO_ARGS], so no argument register reaches the body.
    A spec that refused some argument shape would decline a call Linux
    answers 0.  Three shapes a typical caller would not pass: all bits
    set, a mix of addresses and errno-looking words, and the all-ones
    word in the last register alone. -/
theorem sched_yield_ignores_every_argument_word :
  let ok := mkEffect (Z_to_bv 64 0) [] [] ;
  check_syscall (sched_yield_in (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1))
                   (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (2 ^ 64 - 1)))
    ok demo_model = .CheckOk demo_model []
  ∧ check_syscall (sched_yield_in 4096 (errno_ret EINVAL) (Z_to_bv 64 0x7fff80000000)
                     (Z_to_bv 64 (2 ^ 32)) 1 0) ok demo_model = .CheckOk demo_model []
  ∧ check_syscall (sched_yield_in 0 0 0 0 0 (Z_to_bv 64 (2 ^ 64 - 1)))
       ok demo_model = .CheckOk demo_model []
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! THE REFUSALS.  No kernel answers this call anything but 0, so each
    of these is an answer the checker must reject rather than record:
    the two nearest integers, an errno, and the -EPERM
    [ALLOW_ERROR_INJECTION] would make reachable on a kernel running a
    [bpf_override_return] program — which [Kernel.Sched.Syscalls.sched_yield_spec]
    names as the residual this model does not describe.  A
    [CheckUnmodeled] is impossible here and no case asserts one: the arm
    has no fail-closed branch at all. -/
theorem sched_yield_nonzero_answers_rejected :
  check_syscall sched_yield_zeros (mkEffect (Z_to_bv 64 1) [] []) demo_model
    = .CheckReject
  ∧ check_syscall sched_yield_zeros
       (mkEffect (Z_to_bv 64 (2 ^ 64 - 1)) [] []) demo_model = .CheckReject
  ∧ check_syscall sched_yield_zeros
       (mkEffect (errno_ret EINTR) [] []) demo_model = .CheckReject
  ∧ check_syscall sched_yield_zeros
       (mkEffect (errno_ret EPERM) [] []) demo_model = .CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

/-! ...and a 0 that claims to have written user memory, freed a
    mapping, or read one is rejected too: the call has no output
    parameter, no argument to fetch, and nothing to unmap. -/
theorem sched_yield_effect_shape_is_bare :
  check_syscall sched_yield_zeros
    (mkEffect (Z_to_bv 64 0) [(Z_to_bv 64 4096, [Z_to_bv 8 0])] []) demo_model
    = .CheckReject
  ∧ check_syscall sched_yield_zeros
       (with_copyins [(Z_to_bv 64 4096, 4)] (mkEffect (Z_to_bv 64 0) [] []))
       demo_model = .CheckReject
  ∧ check_syscall sched_yield_zeros
       (SyscallEffect.mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 4096, Z_to_bv 64 4096)] [] [])
       demo_model = .CheckReject
:= by (try dsimp only); (repeat constructor) <;> rfl

end LinuxSem.Checks.Cases.Kernel.Sched.Syscalls
