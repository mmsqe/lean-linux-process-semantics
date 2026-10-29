/-
  * LinuxSem.Checks.Cases.Kernel.Groups — worked examples over getgroups (158) and setgroups (159)

  Worked cases over `Sys.Kernel.Groups`, which answers to Linux
  [kernel/groups.c]: the examples for the syscalls defined there, and no
  others.

  `Checks.Examples` keeps what is not per-syscall and re-exports this
  module.  Each case is read off the specs and checkers of the matching
  `Sys` module, without running a binary.

  Spelling.  Statements keep their names, and the few spellings Lean does
  not have come from `LinuxSem.Common.RocqSpelling`, transparent
  `abbrev`s DEFINITIONALLY EQUAL to what they stand for:
  - `bv_unsigned w` is `(w.toNat : Int)` and `Z_to_bv n z` is
    `BitVec.ofInt n z`;
  - `zeqb`/`zleb`/`zltb` are `Z.eqb`/`Z.leb`/`Z.ltb` on `Int`.

  The two credential fixtures this file's examples run on — [demo_model]
  and [root_model] — live in [Cases.Kernel.Sys], which is where the id
  calls that mutate them are defined; they are imported, not redefined,
  because `Checks.Examples` re-exports every Cases module into one
  namespace and two definitions of a name would shadow each other.

  Proofs.  Every concrete example is a closed goal and closes by `rfl` —
  kernel reduction.  A conjunction of closed equations is
  `(repeat constructor) <;> rfl`, and the parentheses are load-bearing:
  without them Lean parses `repeat (constructor <;> rfl)` and silently
  leaves a ≥3-way conjunction untouched.  `decide` cannot be the rule:
  `check_result` carries a `Model` and so has no `DecidableEq`.

  The `match` statement.  [setgid_keeps_the_supplementary_group_list]
  states its claim as a `match` on the checker's verdict.  Lean's arms
  are greedy, so the whole `match` is parenthesised, and the constructor
  is written QUALIFIED inside the pattern (`check_result.CheckOk`) rather
  than with dot notation.
-/
import LinuxSem.Checks.Cases.Prelude
import LinuxSem.Checks.Cases.Kernel.Sys
import LinuxSem.LinuxProcessSem.Sys.Kernel.Groups
import LinuxSem.Checks.Sys.Kernel.Groups
import LinuxSem.LinuxProcessSem.StateLedger
import LinuxSem.Common.RocqSpelling

set_option autoImplicit false
set_option maxRecDepth 1000000

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Fs
open LinuxSem.LinuxProcessSem.Run
open LinuxSem.LinuxProcessSem.StackLayout
open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics
open LinuxSem.LinuxProcessSem.Sys.Uapi
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Kernel.Sys
open LinuxSem.Checks
open LinuxSem.Checks.ExecutableSpecs
open LinuxSem.Checks.Sys.Prelude
open LinuxSem.Checks.Sys.Kernel.Groups
open LinuxSem.Checks.Cases.Prelude
open LinuxSem.Checks.Cases.Kernel.Sys

namespace LinuxSem.Checks.Cases.Kernel.Groups

open LinuxSem.Common.RocqSpelling

/-! Rocq spellings (`bv_unsigned`, `Z_to_bv`, `zeqb`/`zleb`/`zltb`) come from
    `LinuxSem.Common.RocqSpelling`, opened above. -/

/-! * LinuxProcessSem.Checks.Cases.Kernel.Groups — worked examples over getgroups (158) and setgroups (159)

    Worked cases over `Sys.Kernel.Groups`, which answers to Linux
    [kernel/groups.c]: the examples for the syscalls defined there, and
    no others.

    `Checks.Examples` keeps what is not per-syscall and re-exports this
    module.  Each case is read off the specs and checkers of the matching
    `Sys` module, without running a binary. -/

/- [demo_model] and [root_model] are the credential fixtures; they are
   defined beside the id calls that mutate them, and shared rather than
   redefined — `Checks.Examples` re-exports every Cases module into one
   namespace, so two definitions of a name would shadow each other. -/

/- -------------------------------------------------------------------------
   getgroups (158)

   Every example below is here for the LAST of the four reasons listed
   at the top of `Checks.Examples` — the environment cannot be made to
   produce it — and for two separate readings of it.  A user program
   cannot choose how many supplementary groups its own process has:
   [setgroups] needs privilege the run does not have, and the model
   declines it anyway, so the branches that turn on that number are only
   conditionally reachable from a run and the fixtures below choose it
   instead.  And a [CheckReject] needs a kernel answering something no
   kernel answers.
   ------------------------------------------------------------------------- -/

/-! A process with NO supplementary groups.  [Cases.Prelude.demo_groups]
    gives [demo_model] three, so the empty list needs its own fixture —
    and it is the one that reaches the zero-length arm, where a nonzero
    size writes nothing and cannot fault. -/
def no_groups_model : Model :=
  with_creds (Creds.mkCreds demo_uid demo_uid demo_uid demo_gid demo_gid demo_gid [])
             demo_model

def getgroups_in (gidsetsize grouplist : word) : SyscallInput :=
  SyscallInput.mkInput 158 [gidsetsize, grouplist, 0, 0, 0, 0] (fun _ => none) (fun _ => none)

/-! ## A bridge to the arm

    `check_syscall` dispatches by syscall NUMBER, and the dispatch is what
    makes the arm's own branch chain reachable.  In Lean that trip is a
    `whnf` of the checker, which does not terminate on `sint32` (the
    symptom, its cause and the general recipe are on
    `Checks.Sys.Kernel.Groups`'s own note): reducing
    `sint32 gidsetsize` needs a decision procedure on a still-opaque
    `Int` and the reducer recurses without bottoming out.  So the bridge
    below does the dispatch ONCE, by rewriting with the equational
    lemmas — which never `whnf`s the arm — and each example then works on
    `check_getgroups` at its literal size.  It is this file's own
    machinery rather than a statement about the model, and nothing here
    is assumed: the `lookup_ca` equation is closed by
    `rfl`, and the `in_arg`/`getD` step it leaves behind by three
    standard `List`/`Option` lemmas. -/
theorem check_syscall_getgroups_in (gidsetsize grouplist : word)
    (eff : SyscallEffect) (m : Model) :
    check_syscall (getgroups_in gidsetsize grouplist) eff m
      = check_getgroups gidsetsize eff m := by
  have hl : Sys.Dispatch.lookup_ca Sys.Dispatch.checked_table ((158 : word).toNat : Int)
      = some Sys.Dispatch.arm_getgroups := by rfl
  simp only [check_syscall, Sys.Dispatch.CheckedTable.check_syscall,
    Sys.Dispatch.check_syscall, hl, Sys.Dispatch.arm_getgroups, in_arg, getgroups_in,
    List.getD, List.getElem?_cons_zero, Option.getD_some]

/-! THE COUNT, and it is the LENGTH of the list rather than any id in
    it: [demo_groups] holds 27, 1002 and 4000, and the answer is 3.  The
    [grouplist] pointer is not read at size 0 — the same call with a
    garbage pointer gives the same answer, which is what
    [SYSCALL_DEFINE2(getgroups)]'s [if (gidsetsize)] guard buys. -/
theorem getgroups_size_zero_reports_the_count :
  check_syscall (getgroups_in 0 0) (mkEffect 3 [] []) demo_model
    = .CheckOk demo_model []
  ∧ check_syscall (getgroups_in 0 3735928559) (mkEffect 3 [] []) demo_model
       = .CheckOk demo_model []
:= by
  refine ⟨?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! …and no other count is admissible.  A kernel that reported one more,
    one fewer, or a member of the list instead of its length is
    REJECTED.  This is the negative direction no real run can produce: a
    real kernel always answers truthfully. -/
theorem getgroups_wrong_count_rejected :
  check_syscall (getgroups_in 0 0) (mkEffect 4 [] []) demo_model = .CheckReject
  ∧ check_syscall (getgroups_in 0 0) (mkEffect 2 [] []) demo_model = .CheckReject
  ∧ check_syscall (getgroups_in 0 0) (mkEffect 1002 [] []) demo_model
       = .CheckReject
:= by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! A NEGATIVE SIZE is -EINVAL, decided before the credentials are read,
    so it does not depend on the list at all: the same answer on a model
    with three groups and on one with none.  The size is an [int], so
    the register's high half is discarded first — a0 = 2^32 - 1 is
    [gidsetsize = -1]. -/
theorem getgroups_negative_size_is_einval :
  check_syscall (getgroups_in 4294967295 3735928559)
    (mkEffect (errno_ret EINVAL) [] []) demo_model = .CheckOk demo_model []
  ∧ check_syscall (getgroups_in 4294967295 3735928559)
       (mkEffect (errno_ret EINVAL) [] []) no_groups_model
       = .CheckOk no_groups_model []
  ∧ check_syscall (getgroups_in 18446744073709551615 0)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = .CheckOk demo_model []
:= by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! THE TRUNCATION IS THE BEHAVIOR, in the other direction: a0 = 2^32
    has a zero low half, so it is [gidsetsize = 0] and asks for the
    count.  A model that compared the full 64-bit register would call
    this a huge positive size and answer down the writing path. -/
theorem getgroups_size_truncates_to_int :
  check_syscall (getgroups_in 4294967296 0) (mkEffect 3 [] []) demo_model
    = .CheckOk demo_model []
:= by
  rw [check_syscall_getgroups_in]
  simp only [check_getgroups]
  repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! A SIZE TOO SMALL is -EINVAL and NOTHING IS WRITTEN, even though the
    call named a size the kernel would otherwise fill: the [i >
    gidsetsize] test fires before [groups_to_user] runs.  So -EFAULT is
    not admissible here however bad the pointer is. -/
theorem getgroups_size_too_small_is_einval_not_efault :
  check_syscall (getgroups_in 2 3735928559)
    (mkEffect (errno_ret EINVAL) [] []) demo_model = .CheckOk demo_model []
  ∧ check_syscall (getgroups_in 2 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) demo_model = .CheckReject
:= by
  refine ⟨?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! THE ZERO-LENGTH ARM.  With no supplementary groups and a nonzero
    size, [groups_to_user]'s loop runs zero times: the call returns 0,
    touches no memory, and cannot fault — there is no up-front
    [access_ok] over the array, so a garbage pointer is never
    dereferenced.  A model that faulted here would be modeling an
    [access_ok] the kernel does not do. -/
theorem getgroups_empty_list_returns_zero_without_touching_the_array :
  check_syscall (getgroups_in 64 3735928559) (mkEffect 0 [] []) no_groups_model
    = .CheckOk no_groups_model []
  ∧ check_syscall (getgroups_in 64 3735928559)
       (mkEffect (errno_ret EFAULT) [] []) no_groups_model = .CheckReject
:= by
  refine ⟨?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! THE WRITING PATH IS DECLINED.  A size big enough to hold three
    groups reaches [groups_to_user], which stores three 4-byte [gid_t]s
    and can fault part-way through; [Kernel.Groups.getgroups_spec] says
    why that is left [unmodeled] rather than guessed at.  Declining is
    the whole answer, so no observation of it is accepted either. -/
theorem getgroups_writing_path_fails_closed :
  check_syscall (getgroups_in 3 4096) (mkEffect 3 [] []) demo_model
    = .CheckUnmodeled
  ∧ check_syscall (getgroups_in 64 4096) (mkEffect 3 [] []) demo_model
       = .CheckUnmodeled
/- AND THE TWO SIZES ON THE OTHER SIDE OF THE WRITING PATH, at the
     SAME pointer, so the declines above are a boundary rather than a
     description of one.  Both are [CheckUnmodeled] and would survive
     [getgroups] declining MORE -- the counting arm or the -EINVAL arm
     going unmodeled with the writing one -- which is the change this
     lemma exists to notice.  Size 0 asks for the count and never
     reaches [groups_to_user]; size 2 is too small for three groups and
     is refused before it does. -/
  ∧ check_syscall (getgroups_in 0 4096) (mkEffect 3 [] []) demo_model
       = .CheckOk demo_model []
  ∧ check_syscall (getgroups_in 2 4096)
       (mkEffect (errno_ret EINVAL) [] []) demo_model = .CheckOk demo_model []
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [check_syscall_getgroups_in]
    simp only [check_getgroups]
    repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! THE ID SETTERS DO NOT DROP THE LIST.  [setgid] rebuilds the
    credentials, and the kernel's [prepare_creds] carries the same
    [struct group_info] over; a [State.set_cred_gids] that forgot
    [cr_groups] would make this [getgroups] answer 0.  [ENVIRONMENT]:
    the setter needs a privileged caller to reach an arbitrary gid, so
    this runs on [root_model], whose group list is [demo_groups] too. -/
theorem setgid_keeps_the_supplementary_group_list :
  (match check_syscall (SyscallInput.mkInput 144 [4242, 0, 0, 0, 0, 0] (fun _ => none)
                         (fun _ => none))
          (mkEffect 0 [] []) root_model with
   | check_result.CheckOk m' _ => check_syscall (getgroups_in 0 0) (mkEffect 3 [] []) m'
                      = .CheckOk m' []
   | _ => False)
:= by
  rw [show check_syscall (SyscallInput.mkInput 144 [4242, 0, 0, 0, 0, 0] (fun _ => none)
            (fun _ => none)) (mkEffect 0 [] []) root_model = .CheckOk _ [] from rfl]
  simp only []
  rw [check_syscall_getgroups_in]
  simp only [check_getgroups]
  repeat' (first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)] | rfl)

/-! [setgroups] refuses an unprivileged caller BEFORE it looks at either
    argument, so a size past NGROUPS_MAX, a negative size and an
    unreadable list are all -EPERM. -/
theorem setgroups_refuses_before_it_reads_an_argument :
  check_syscall (SyscallInput.mkInput 159 [18446744073709551615, 4096, 0, 0, 0, 0]
                   (fun _ => none) (fun _ => none))
    (mkEffect (errno_ret EPERM) [] []) demo_model = .CheckOk demo_model []
  ∧ check_syscall (SyscallInput.mkInput 159 [1, 4096, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EINVAL) [] []) demo_model = .CheckReject
  ∧ check_syscall (SyscallInput.mkInput 159 [1, 4096, 0, 0, 0, 0]
                     (fun _ => none) (fun _ => none))
       (mkEffect (errno_ret EFAULT) [] []) demo_model = .CheckReject
:= by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    rfl

/-! A PRIVILEGED [setgroups] would write the supplementary group list
    that [getgroups] above reports the length of, so accepting the call
    and discarding what it wrote would make the next [getgroups] answer
    for a list nobody set; the model declines instead.  [ENVIRONMENT]:
    needs uid 0. -/
theorem privileged_setgroups_fails_closed :
  check_syscall (SyscallInput.mkInput 159 [0, 0, 0, 0, 0, 0] (fun _ => none) (fun _ => none))
    (mkEffect 0 [] []) root_model = .CheckUnmodeled
:= by
  rfl

end LinuxSem.Checks.Cases.Kernel.Groups
