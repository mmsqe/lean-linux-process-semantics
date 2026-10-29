/-
  * LinuxProcessSem.Checks.Sys.Kernel.Futex.Syscalls — the futex (98) checker, and its proofs

  Answers to Linux [kernel/futex/syscalls.c]: this file holds the checkers for the
  syscalls defined there, and no others.

  [Checks/ExecutableSpecs.lean] keeps the dispatcher
  and the four top-level theorems and re-exports this module. The
  checkers here are executable, and their proofs relate them to the
  relational specs in the matching [Sys] module.

  The checker answers with `.CheckOk` / `.CheckReject` / `.CheckUnmodeled`;
  a word is read UNSIGNED (`(uaddr.toNat : Int)`); the `FUTEX_*` words are
  `Sys.Uapi`'s; `read_bytes_map` / `access_okb` / `le_bytes_to_word` are the
  state layer's; and `check_ret_only` / `check_ret_only_copyins` are
  `Checks.Sys.Prelude`'s.

  The two `get_futex_key` tests are WRITTEN OUT rather than shared with
  [Sys.Kernel.Futex.Syscalls.futex_aligned_b], and the repetition is worth
  its cost: the checkers below spell
  `!((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)`, which is the DEFINITION
  of `futex_aligned_b`, not a separate test.  The two are therefore
  interchangeable by `rfl`, and the proofs use that: they case-split on the
  raw `%` test (the checker's spelling, which is what `cases` needs
  syntactically) and hand the resulting equation to the spec as
  `futex_aligned_b uaddr = …`, definitionally.  So the four lemmas below
  still force the two statements to coincide — here by `rfl` rather than by
  a rewrite step — and the file's warning stands unchanged: an identical
  MISTAKE in both files would still close every proof, since these proofs do
  not show that the alignment really is the kernel's, or that -EFAULT really
  is the range verdict and not a page lookup.

  The two booleans of the checker and the spec are split with `cases` on one
  test at a time, named by the branch it takes (`cases hmod : …`, then
  `cases hok : …`), with the equation in hand so the other side can be
  rewritten by it.  `dsimp only` performs the iota reduction, `sys_unfold` /
  `inv_ok` keep their names (macros in `Checks.Sys.Prelude`), a
  `CheckUnmodeled = CheckOk` equation is eliminated by `exact nomatch H`,
  and `simp only [err_ret, ret_only, …pure, Outcome.ok.injEq] at H` is what
  the outcome equation `o = .ok x m []` needs.  Where the monad has to be
  peeled by hand the proofs use the spec file's own arm lemmas for the
  introduction side (`futex_key_check_einval`/`_efault`/`_pass`,
  `futex_wait_private_spec_eagain`/`_unreadable`/`_would_block`) and the
  Prelude's `input_bind_ok_inv`/`record_copyins_ok_inv` for the inversion
  side.

  The post-`input` command of `futex_wait_private_spec` is named once
  ([futex_wait_body]) so that the `bind input` peel is a single application
  of `input_bind_ok_inv` instead of a lambda restated — and re-typechecked —
  four times.  The term is the spec's own, unchanged;
  `futex_wait_private_spec` is definitionally
  `futex_key_check uaddr (bind input (futex_wait_body uaddr val))`.

  `Checks.Sys.Kernel.Groups` records that `by_cases`/`cases` normalise the
  goal, which on a function-type `if` can set out to decide the test and not
  terminate.  The tests here are `%`/`==` on an opaque word, so reduction
  gets STUCK rather than recursing, and no `generalize` step is required.
  The proofs still never unfold `futex_spec`/`futex_key_check` in a goal
  except when they are about to rewrite its test: the checker-side direction
  closes with the spec file's arm lemmas, and the spec-side direction
  unfolds the HYPOTHESIS and peels it.
-/
import LinuxSem.Checks.Sys.Prelude
import LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls

namespace LinuxSem.Checks.Sys.Kernel.Futex.Syscalls

open LinuxSem.Riscv
open LinuxSem.LinuxProcessSem
open LinuxSem.LinuxProcessSem.Sys.Syscall
open LinuxSem.LinuxProcessSem.Sys.Uapi (FUTEX_WAKE FUTEX_WAIT FUTEX_PRIVATE_FLAG
  FUTEX_WAKE_PRIVATE FUTEX_WAIT_PRIVATE FUTEX_WORD_SIZE)
open LinuxSem.LinuxProcessSem.Sys.Kernel.Futex.Syscalls
open LinuxSem.Checks.Sys.Prelude

/-- Two declarations named `abi_low32` are in scope here (see the note in
    `Sys/Syscall.lean`), so the checker pins the `Syscall` one — the same
    term `Sys.Kernel.Futex.Syscalls.futex_spec` applies to `val`. -/
local notation "abi_low32" => LinuxSem.LinuxProcessSem.Sys.Syscall.abi_low32

/-- The two [get_futex_key] gates are WRITTEN OUT rather than taken from
    [Sys.Kernel.Futex.Syscalls.futex_aligned_b], and the four lemmas
    below are what make the repetition worth its cost: they force this
    statement and the spec's to coincide.  [Checks/Sys/Fs/Timerfd] says
    why the layers restate a gate instead of sharing one predicate, and
    what the repetition does NOT buy — an identical MISTAKE in both
    files still closes every proof.  These proofs do not show that the
    alignment really is the kernel's, or that -EFAULT really is the
    range verdict and not a page lookup. -/
def check_futex_wake_private (uaddr : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if !((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !access_okb uaddr FUTEX_WORD_SIZE
  then check_ret_only eff (errno_ret EFAULT) m []
  else check_ret_only eff (BitVec.ofInt 64 0) m []

/-- The wait arm's accepting answer carries the four-byte ledger the
    spec records, so it is [check_ret_only_copyins] rather than
    [check_ret_only]: plain [check_ret_only] would insist the ledger be
    empty and reject the truthful effect.  The two gate answers use the
    plain form, because nothing was read on either. -/
def check_futex_wait_private (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if !((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if !access_okb uaddr FUTEX_WORD_SIZE
  then check_ret_only eff (errno_ret EFAULT) m []
  else
    match read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
    | none => .CheckUnmodeled
    | some uval =>
        if bv_eqb (le_bytes_to_word uval) val then .CheckUnmodeled
        else check_ret_only_copyins [(uaddr, FUTEX_WORD_SIZE_nat)] eff
               (errno_ret EAGAIN) m []

def check_futex (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE)
  then check_futex_wake_private uaddr eff m
  else if bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE)
  then (if !w_is0 utime then .CheckUnmodeled
        else check_futex_wait_private i uaddr (abi_low32 val) eff m)
  else .CheckUnmodeled

/-! ## Inversion of the two `get_futex_key` gates

    Both sides of every proof below branch on the same two booleans, in
    the same order.  Splitting them rather
    than the assembled condition keeps the proof from depending on the
    two files spelling the gate the same way, which is the coincidence
    the restatement exists to avoid relying on.

    The spec's own arm lemmas ([futex_key_check_einval] and friends)
    carry the introduction direction.  The two lemmas here carry the
    INVERSE direction, which the spec-side proofs need: the ok direction
    is a three-way
    split over the gates (the ledger argument below reads the effect back
    out of it), and the decline direction collapses to the command's own
    arm, because neither refusal is [unmodeled].

    Reading the ok direction back needs one remark on the proof: `cases`
    on a gate test generalises the test in the GOAL as well, so the
    disjunct being proved has that gate already replaced by `false`/`true`
    — which is why its first component is `rfl` there and the effect
    components come straight from the hypothesis. -/

/-- The gate prefix answered: a misaligned address is refused -EINVAL
    before anything else, an aligned address outside the range -EFAULT,
    and past both the command's own spec stands. -/
theorem futex_key_check_ok_iff (uaddr : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model)
    (evs : List event) :
    futex_key_check uaddr k i m (.ok eff m' evs) ↔
      (futex_aligned_b uaddr = false ∧ eff = mkEffect (errno_ret EINVAL) [] [] ∧
          m' = m ∧ evs = []) ∨
      (futex_aligned_b uaddr = true ∧ access_okb uaddr FUTEX_WORD_SIZE = false ∧
          eff = mkEffect (errno_ret EFAULT) [] [] ∧ m' = m ∧ evs = []) ∨
      (futex_aligned_b uaddr = true ∧ access_okb uaddr FUTEX_WORD_SIZE = true ∧
          k i m (.ok eff m' evs)) := by
  constructor
  · intro H
    unfold futex_key_check at H
    cases hal : futex_aligned_b uaddr with
    | false =>
      simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | true =>
      simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H
      cases hok : access_okb uaddr FUTEX_WORD_SIZE with
      | false =>
        simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
          LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
        obtain ⟨rfl, rfl, rfl⟩ := H
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)
      | true =>
        simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
        exact Or.inr (Or.inr ⟨rfl, rfl, H⟩)
  · rintro (⟨hal, heff, hm, hevs⟩ | ⟨hal, hok, heff, hm, hevs⟩ | ⟨hal, hok, H⟩)
    · rw [heff, hm, hevs]
      exact futex_key_check_einval uaddr k i m hal
    · rw [heff, hm, hevs]
      exact futex_key_check_efault uaddr k i m hal hok
    · rw [futex_key_check_pass uaddr k hal hok]
      exact H

/-- An [unmodeled] outcome of the gate prefix can only be the command's
    own decline: both refusals answer an errno, so neither is
    [unmodeled]. -/
theorem futex_key_check_unmodeled_iff (uaddr : word) (k : SysSpec SyscallEffect)
    (i : SyscallInput) (m : Model) :
    futex_key_check uaddr k i m .unmodeled ↔
      (futex_aligned_b uaddr = true ∧ access_okb uaddr FUTEX_WORD_SIZE = true ∧
          k i m .unmodeled) := by
  constructor
  · intro H
    unfold futex_key_check at H
    cases hal : futex_aligned_b uaddr with
    | false =>
      simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    | true =>
      simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H
      cases hok : access_okb uaddr FUTEX_WORD_SIZE with
      | false =>
        simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
          LinuxSem.LinuxProcessSem.pure] at H
        exact nomatch H
      | true =>
        simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
        exact ⟨rfl, rfl, H⟩
  · rintro ⟨hal, hok, H⟩
    rw [futex_key_check_pass uaddr k hal hok]
    exact H

/-- The wait arm's post-`input` command, named so the `bind input` peel
    below is one application of [input_bind_ok_inv] (see the note on the
    body of [futex_wait_private_spec]). -/
private def futex_wait_body (uaddr val : word) (i : SyscallInput) : SysSpec SyscallEffect :=
  match read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
  | none => unmodeled
  | some uval =>
      record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
        (if bv_eqb (le_bytes_to_word uval) val then unmodeled else err_ret EAGAIN)

/-! ## The wake arm -/

/-- A private wake answers 0 past both gates, and each gate answers its
    own errno — so all three answers are [CheckOk]-shaped and the checker
    can only accept exactly the effect the spec predicts. -/
theorem check_futex_wake_private_sound_ok (uaddr : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : check_futex_wake_private uaddr eff m = .CheckOk m' evs) :
    futex_wake_private_spec uaddr i m (.ok eff m' evs) := by
  unfold check_futex_wake_private at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    simp only [hmod, Bool.not_false, ite_true] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact futex_key_check_einval uaddr _ _ _ hmod
  | true =>
    simp only [hmod, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
      exact futex_key_check_efault uaddr _ _ _ hmod hok
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mp H
      unfold futex_wake_private_spec
      rw [futex_key_check_pass uaddr (ret_only (BitVec.ofInt 64 0)) hmod hok]
      exact pure_ok _ _ _

/-- Neither refusal is [unmodeled], so neither can be accepted as one. -/
theorem check_futex_wake_private_sound_unmodeled (uaddr : word)
    (eff : SyscallEffect) (m : Model) (i : SyscallInput)
    (H : check_futex_wake_private uaddr eff m = .CheckUnmodeled) :
    futex_wake_private_spec uaddr i m .unmodeled := by
  unfold check_futex_wake_private at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    simp only [hmod, Bool.not_false, ite_true] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  | true =>
    simp only [hmod, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      exact absurd H (check_ret_only_no_unmodeled eff (BitVec.ofInt 64 0) m [])

/-- Completeness on the wake arm: the spec's three answers are the
    checker's three answers, in the same gate order. -/
theorem check_futex_wake_private_complete_ok (uaddr : word) (eff : SyscallEffect)
    (m m' : Model) (evs : List event) (i : SyscallInput)
    (H : futex_wake_private_spec uaddr i m (.ok eff m' evs)) :
    check_futex_wake_private uaddr eff m = .CheckOk m' evs := by
  unfold futex_wake_private_spec at H
  unfold futex_key_check at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    have hal : futex_aligned_b uaddr = false := hmod
    simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
    unfold check_futex_wake_private
    simp only [hmod, Bool.not_false, ite_true]
    exact (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mpr H
  | true =>
    have hal : futex_aligned_b uaddr = true := hmod
    simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H
      unfold check_futex_wake_private
      simp only [hmod, hok, Bool.not_true, Bool.false_eq_true, ite_false,
        Bool.not_false, ite_true]
      exact (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mpr H
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at H
      unfold check_futex_wake_private
      simp only [hmod, hok, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (check_ret_only_ok_iff eff (BitVec.ofInt 64 0) m [] m' evs).mpr H

/-- The wake arm adds no decline the checker does not have. -/
theorem check_futex_wake_private_complete_unmodeled (uaddr : word) (m : Model)
    (i : SyscallInput) (eff : SyscallEffect)
    (H : futex_wake_private_spec uaddr i m .unmodeled) :
    check_futex_wake_private uaddr eff m = .CheckUnmodeled := by
  unfold futex_wake_private_spec at H
  unfold futex_key_check at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    have hal : futex_aligned_b uaddr = false := hmod
    simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure] at H
    exact nomatch H
  | true =>
    have hal : futex_aligned_b uaddr = true := hmod
    simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      simp only [ret_only, LinuxSem.LinuxProcessSem.pure] at H
      exact nomatch H

/-! ## The wait arm -/

/-- The wait arm's accepting answer is the -EAGAIN effect WITH the
    four-byte ledger, and nothing else is accepted: an unreadable word
    and a matching one are both declines. -/
theorem check_futex_wait_private_sound_ok (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_futex_wait_private i uaddr val eff m = .CheckOk m' evs) :
    futex_wait_private_spec uaddr val i m (.ok eff m' evs) := by
  unfold check_futex_wait_private at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    simp only [hmod, Bool.not_false, ite_true] at H
    obtain ⟨rfl, rfl, rfl⟩ :=
      (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mp H
    exact futex_key_check_einval uaddr _ _ _ hmod
  | true =>
    simp only [hmod, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true] at H
      obtain ⟨rfl, rfl, rfl⟩ :=
        (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mp H
      exact futex_key_check_efault uaddr _ _ _ hmod hok
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      cases hr : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
      | none =>
        simp only [hr] at H
        exact nomatch H
      | some uval' =>
        cases hv : bv_eqb (le_bytes_to_word uval') val with
        | false =>
          simp only [hr, hv] at H
          obtain ⟨rfl, rfl, rfl⟩ :=
            (check_ret_only_copyins_ok_iff [(uaddr, FUTEX_WORD_SIZE_nat)] eff
              (errno_ret EAGAIN) m [] m' evs).mp H
          exact futex_wait_private_spec_eagain uaddr val i _ hmod hok hr hv
        | true =>
          simp only [hr, hv] at H
          exact nomatch H

/-- The two declines are exactly the unreadable word and the word that
    still matches [val]; the gate answers are errnos, not declines. -/
theorem check_futex_wait_private_sound_unmodeled (i : SyscallInput)
    (uaddr val : word) (eff : SyscallEffect) (m : Model)
    (H : check_futex_wait_private i uaddr val eff m = .CheckUnmodeled) :
    futex_wait_private_spec uaddr val i m .unmodeled := by
  unfold check_futex_wait_private at H
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    simp only [hmod, Bool.not_false, ite_true] at H
    exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EINVAL) m [])
  | true =>
    simp only [hmod, Bool.not_true, Bool.false_eq_true, ite_false] at H
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true] at H
      exact absurd H (check_ret_only_no_unmodeled eff (errno_ret EFAULT) m [])
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H
      cases hr : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
      | none =>
        simp only [hr] at H
        exact futex_wait_private_spec_unreadable uaddr val i m hmod hok hr
      | some uval' =>
        cases hv : bv_eqb (le_bytes_to_word uval') val with
        | false =>
          simp only [hr, hv] at H
          exact absurd H
            (check_ret_only_copyins_no_unmodeled [(uaddr, FUTEX_WORD_SIZE_nat)] eff
              (errno_ret EAGAIN) m [])
        | true =>
          simp only [hr, hv] at H
          exact futex_wait_private_spec_would_block uaddr val i m hmod hok hr hv

/-- Completeness on the wait arm: once the model has read the word, the
    ledger and the return value are the two things the checker can
    insist on, and both are the spec's own. -/
theorem check_futex_wait_private_complete_ok (i : SyscallInput) (uaddr val : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : futex_wait_private_spec uaddr val i m (.ok eff m' evs)) :
    check_futex_wait_private i uaddr val eff m = .CheckOk m' evs := by
  have H' : futex_key_check uaddr (bind input (futex_wait_body uaddr val)) i m
      (.ok eff m' evs) := by
    unfold futex_wait_private_spec at H
    exact H
  unfold futex_key_check at H'
  cases hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
  | false =>
    have hal : futex_aligned_b uaddr = false := hmod
    simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
      LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H'
    unfold check_futex_wait_private
    simp only [hmod, Bool.not_false, ite_true]
    exact (check_ret_only_ok_iff eff (errno_ret EINVAL) m [] m' evs).mpr H'
  | true =>
    have hal : futex_aligned_b uaddr = true := hmod
    simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H'
    cases hok : access_okb uaddr FUTEX_WORD_SIZE with
    | false =>
      simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
        LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H'
      unfold check_futex_wait_private
      simp only [hmod, hok, Bool.not_true, Bool.false_eq_true, ite_false,
        Bool.not_false, ite_true]
      exact (check_ret_only_ok_iff eff (errno_ret EFAULT) m [] m' evs).mpr H'
    | true =>
      simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H'
      unfold check_futex_wait_private
      simp only [hmod, hok, Bool.not_true, Bool.false_eq_true, ite_false]
      have hb := input_bind_ok_inv (futex_wait_body uaddr val) i m eff m' evs H'
      unfold futex_wait_body at hb
      cases hr : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
      | none =>
        rw [hr] at hb
        try dsimp only at hb
        simp only [unmodeled] at hb
        exact nomatch hb
      | some uval' =>
        rw [hr] at hb
        try dsimp only at hb
        cases hv : bv_eqb (le_bytes_to_word uval') val with
        | false =>
          rw [hv] at hb
          try dsimp only at hb
          obtain ⟨core, Hcore, heff⟩ :=
            record_copyins_ok_inv [(uaddr, FUTEX_WORD_SIZE_nat)] (err_ret EAGAIN)
              i m eff m' evs hb
          simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure,
            Outcome.ok.injEq] at Hcore
          obtain ⟨rfl, rfl, rfl⟩ := Hcore
          dsimp only
          simp only [hv]
          rw [heff]
          exact check_ret_only_copyins_refl [(uaddr, FUTEX_WORD_SIZE_nat)]
            (errno_ret EAGAIN) _ []
        | true =>
          rw [hv] at hb
          try dsimp only at hb
          obtain ⟨core, Hcore, -⟩ :=
            record_copyins_ok_inv [(uaddr, FUTEX_WORD_SIZE_nat)] unmodeled
              i m eff m' evs hb
          simp only [unmodeled] at Hcore
          dsimp only
          simp only [hv, ite_true]
          exact nomatch Hcore

/-- The wait arm adds no decline the checker does not have: the spec
    declines exactly where the checker does, for the same two reasons. -/
theorem check_futex_wait_private_complete_unmodeled (i : SyscallInput)
    (uaddr val : word) (m : Model) (eff : SyscallEffect)
    (H : futex_wait_private_spec uaddr val i m .unmodeled) :
    check_futex_wait_private i uaddr val eff m = .CheckUnmodeled := by
  have H' : futex_key_check uaddr (bind input (futex_wait_body uaddr val)) i m .unmodeled := by
    unfold futex_wait_private_spec at H
    exact H
  obtain ⟨hal, hok, Hbody⟩ := (futex_key_check_unmodeled_iff uaddr _ i m).mp H'
  have hmod : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) = true := hal
  unfold check_futex_wait_private
  simp only [hmod, hok, Bool.not_true, Bool.false_eq_true, ite_false]
  have hb := input_bind_unmodeled_inv (futex_wait_body uaddr val) i m Hbody
  unfold futex_wait_body at hb
  cases hr : read_bytes_map i.in_mem uaddr (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
  | none => rfl
  | some uval' =>
    rw [hr] at hb
    try dsimp only at hb
    cases hv : bv_eqb (le_bytes_to_word uval') val with
    | false =>
      rw [hv] at hb
      try dsimp only at hb
      have h2 := record_copyins_unmodeled_inv [(uaddr, FUTEX_WORD_SIZE_nat)]
        (err_ret EAGAIN) i m hb
      simp only [err_ret, ret_only, LinuxSem.LinuxProcessSem.pure] at h2
      exact nomatch h2
    | true =>
      dsimp only
      simp only [hv, ite_true]

/-! ## The dispatcher -/

/-- The op word is tested WHOLE, so the three arms are disjoint by
    construction and each of the four lemmas is one case split over the
    two equalities followed by the matching arm's lemma. -/
theorem check_futex_sound_ok (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : check_futex i uaddr op val utime eff m = .CheckOk m' evs) :
    futex_spec uaddr op val utime i m (.ok eff m' evs) := by
  unfold check_futex at H
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    simp only [hw, ite_true] at H
    unfold futex_spec
    simp only [hw, ite_true]
    exact check_futex_wake_private_sound_ok uaddr eff m m' evs i H
  | false =>
    simp only [hw, Bool.false_eq_true, ite_false] at H
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      simp only [hwt, Bool.false_eq_true, ite_false] at H
      exact nomatch H
    | true =>
      simp only [hwt, ite_true] at H
      cases ht : w_is0 utime with
      | true =>
        simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at H
        unfold futex_spec
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_true]
        exact check_futex_wait_private_sound_ok i uaddr (abi_low32 val) eff m m' evs H
      | false =>
        simp only [ht, Bool.not_false, ite_true] at H
        exact nomatch H

theorem check_futex_sound_unmodeled (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m : Model)
    (H : check_futex i uaddr op val utime eff m = .CheckUnmodeled) :
    futex_spec uaddr op val utime i m .unmodeled := by
  unfold check_futex at H
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    simp only [hw, ite_true] at H
    unfold futex_spec
    simp only [hw, ite_true]
    exact check_futex_wake_private_sound_unmodeled uaddr eff m i H
  | false =>
    simp only [hw, Bool.false_eq_true, ite_false] at H
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      simp only [hwt, Bool.false_eq_true, ite_false] at H
      unfold futex_spec
      simp only [hw, hwt, Bool.false_eq_true, ite_false, unmodeled]
    | true =>
      simp only [hwt, ite_true] at H
      cases ht : w_is0 utime with
      | true =>
        simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at H
        unfold futex_spec
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_true]
        exact check_futex_wait_private_sound_unmodeled i uaddr (abi_low32 val) eff m H
      | false =>
        simp only [ht, Bool.not_false, ite_true] at H
        unfold futex_spec
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_false, ite_true, unmodeled]

theorem check_futex_complete_ok (i : SyscallInput) (uaddr op val utime : word)
    (eff : SyscallEffect) (m m' : Model) (evs : List event)
    (H : futex_spec uaddr op val utime i m (.ok eff m' evs)) :
    check_futex i uaddr op val utime eff m = .CheckOk m' evs := by
  unfold futex_spec at H
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    simp only [hw, ite_true] at H
    unfold check_futex
    simp only [hw, ite_true]
    exact check_futex_wake_private_complete_ok uaddr eff m m' evs i H
  | false =>
    simp only [hw, Bool.false_eq_true, ite_false] at H
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      simp only [hwt, Bool.false_eq_true, ite_false, unmodeled] at H
      exact nomatch H
    | true =>
      simp only [hwt, ite_true] at H
      cases ht : w_is0 utime with
      | true =>
        simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at H
        unfold check_futex
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_true]
        exact check_futex_wait_private_complete_ok i uaddr (abi_low32 val) eff m m' evs H
      | false =>
        simp only [ht, Bool.not_false, ite_true, unmodeled] at H
        exact nomatch H

theorem check_futex_complete_unmodeled (i : SyscallInput) (uaddr op val utime : word)
    (m : Model) (eff : SyscallEffect)
    (H : futex_spec uaddr op val utime i m .unmodeled) :
    check_futex i uaddr op val utime eff m = .CheckUnmodeled := by
  unfold futex_spec at H
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    simp only [hw, ite_true] at H
    unfold check_futex
    simp only [hw, ite_true]
    exact check_futex_wake_private_complete_unmodeled uaddr m i eff H
  | false =>
    simp only [hw, Bool.false_eq_true, ite_false] at H
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      simp only [hwt, Bool.false_eq_true, ite_false, unmodeled] at H
      unfold check_futex
      simp only [hw, hwt, Bool.false_eq_true, ite_false]
    | true =>
      simp only [hwt, ite_true] at H
      cases ht : w_is0 utime with
      | true =>
        simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false] at H
        unfold check_futex
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_true]
        exact check_futex_wait_private_complete_unmodeled i uaddr (abi_low32 val) m eff H
      | false =>
        simp only [ht, Bool.not_false, ite_true] at H
        unfold check_futex
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_false, ite_true]

/-! ## The ledger predicate -/

/-- Every answered [futex] carries the ledger [futex_wait_reads_b]
    predicts, and no other.

    Stated over [Ok] outcomes only, which is exactly the question a
    user of the checker asks: it builds an effect for a call the kernel
    really made and asks which ranges to claim.  The one shape where the
    two could still part company is a WAIT whose word the model cannot
    read — the predicate is true and the spec answers [Unmodeled] — and
    there the verdict does not depend on the effect at all, because
    [Checks.Sys.Kernel.Futex.Syscalls.check_futex] answers
    [CheckUnmodeled] before it looks at one. -/
theorem futex_copyins_exact (uaddr op val utime : word) (i : SyscallInput)
    (m : Model) (eff : SyscallEffect) (m' : Model) (evs : List event)
    (H : futex_spec uaddr op val utime i m (.ok eff m' evs)) :
    eff.eff_copyins =
      (if futex_wait_reads_b uaddr op utime then [(uaddr, FUTEX_WORD_SIZE_nat)] else []) := by
  cases hw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) with
  | true =>
    -- a private WAKE reads nothing, whatever else is in the word
    have hnw : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) = false :=
      futex_wake_not_wait op hw
    have hreads : futex_wait_reads_b uaddr op utime = false := by
      unfold futex_wait_reads_b
      simp only [hnw, Bool.false_and]
    simp only [hreads, Bool.false_eq_true, ite_false]
    have Hw : futex_wake_private_spec uaddr i m (.ok eff m' evs) := by
      unfold futex_spec at H
      simp only [hw, ite_true] at H
      exact H
    unfold futex_wake_private_spec at Hw
    rcases (futex_key_check_ok_iff uaddr (ret_only (BitVec.ofInt 64 0)) i m eff m' evs).mp
      Hw with ⟨-, heff, -, -⟩ | ⟨-, -, heff, -, -⟩ | ⟨-, -, Hcore⟩
    · rw [heff]
    · rw [heff]
    · simp only [ret_only, LinuxSem.LinuxProcessSem.pure,
        Outcome.ok.injEq] at Hcore
      obtain ⟨heff, -, -⟩ := Hcore
      rw [heff]
  | false =>
    cases hwt : bv_eqb op (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) with
    | false =>
      -- neither modelled word: the spec answers no outcome at all
      unfold futex_spec at H
      simp only [hw, hwt, Bool.false_eq_true, ite_false, unmodeled] at H
      exact nomatch H
    | true =>
      cases ht : w_is0 utime with
      | false =>
        -- a non-NULL timeout declines before the word is read
        have hreads : futex_wait_reads_b uaddr op utime = false := by
          unfold futex_wait_reads_b
          simp only [hwt, ht, Bool.true_and, Bool.false_and]
        simp only [hreads, Bool.false_eq_true, ite_false]
        unfold futex_spec at H
        simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
          Bool.not_false, ite_true, unmodeled] at H
        exact nomatch H
      | true =>
        -- a private WAIT with a NULL timeout
        have Hw : futex_wait_private_spec uaddr (abi_low32 val) i m (.ok eff m' evs) := by
          unfold futex_spec at H
          simp only [hw, hwt, Bool.false_eq_true, ite_false, ite_true, ht,
            Bool.not_true, Bool.false_eq_true, ite_false] at H
          exact H
        have H' : futex_key_check uaddr (bind input (futex_wait_body uaddr (abi_low32 val)))
            i m (.ok eff m' evs) := by
          unfold futex_wait_private_spec at Hw
          exact Hw
        unfold futex_key_check at H'
        cases ha : ((uaddr.toNat : Int) % FUTEX_WORD_SIZE == 0) with
        | false =>
          have hal : futex_aligned_b uaddr = false := ha
          have hreads : futex_wait_reads_b uaddr op utime = false := by
            unfold futex_wait_reads_b
            simp only [hwt, ht, hal, Bool.true_and, Bool.false_and]
          simp only [hreads, Bool.false_eq_true, ite_false]
          simp only [hal, Bool.not_false, ite_true, err_ret, ret_only,
            LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H'
          obtain ⟨heff, -, -⟩ := H'
          rw [heff]
        | true =>
          have hal : futex_aligned_b uaddr = true := ha
          simp only [hal, Bool.not_true, Bool.false_eq_true, ite_false] at H'
          cases hok : access_okb uaddr FUTEX_WORD_SIZE with
          | false =>
            have hreads : futex_wait_reads_b uaddr op utime = false := by
              unfold futex_wait_reads_b
              simp only [hwt, ht, hal, hok, Bool.true_and]
            simp only [hreads, Bool.false_eq_true, ite_false]
            simp only [hok, Bool.not_false, ite_true, err_ret, ret_only,
              LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at H'
            obtain ⟨heff, -, -⟩ := H'
            rw [heff]
          | true =>
            have hreads : futex_wait_reads_b uaddr op utime = true := by
              unfold futex_wait_reads_b
              simp only [hwt, ht, hal, hok, Bool.true_and]
            simp only [hreads, ite_true]
            simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false] at H'
            have hb := input_bind_ok_inv (futex_wait_body uaddr (abi_low32 val))
              i m eff m' evs H'
            unfold futex_wait_body at hb
            cases hr : read_bytes_map i.in_mem uaddr
                (BitVec.ofInt 64 FUTEX_WORD_SIZE) with
            | none =>
              rw [hr] at hb
              try dsimp only at hb
              simp only [unmodeled] at hb
              exact nomatch hb
            | some uval' =>
              rw [hr] at hb
              try dsimp only at hb
              cases hv : bv_eqb (le_bytes_to_word uval') (abi_low32 val) with
              | false =>
                rw [hv] at hb
                try dsimp only at hb
                obtain ⟨core, Hcore, heff⟩ :=
                  record_copyins_ok_inv [(uaddr, FUTEX_WORD_SIZE_nat)] (err_ret EAGAIN)
                    i m eff m' evs hb
                simp only [err_ret, ret_only,
                  LinuxSem.LinuxProcessSem.pure, Outcome.ok.injEq] at Hcore
                obtain ⟨rfl, -, -⟩ := Hcore
                rw [heff]
                rfl
              | true =>
                rw [hv] at hb
                try dsimp only at hb
                obtain ⟨core, Hcore, -⟩ :=
                  record_copyins_ok_inv [(uaddr, FUTEX_WORD_SIZE_nat)] unmodeled
                    i m eff m' evs hb
                simp only [unmodeled] at Hcore
                exact nomatch Hcore

/-! ## Sanity checks (not library lemmas)

    The module's proofs contain no `vm_compute` goal.  These pin the branch
    order the proofs above follow, one per claim the matching spec's prose
    makes: -EINVAL outranks -EFAULT; an aligned, in-range address with
    nothing mapped still wakes; the WAIT's -EAGAIN carries the four-byte
    ledger; a matching word declines; a non-NULL timeout is declined
    before anything is read; and every other op word declines. -/

/-- One input: syscall 98 with four readable bytes at address 0 holding
    the little-endian word `1`.  `sanityMem` is the state layer's test
    memory; the futex specs and checkers read no other model state. -/
private def port_input : SyscallInput :=
  { in_sysno := 98, in_args := [], in_mem := sanityMem [1, 0, 0, 0],
    in_wmem := fun _ => none }

private theorem port_read :
    read_bytes_map port_input.in_mem 0 (BitVec.ofInt 64 FUTEX_WORD_SIZE)
      = some [1, 0, 0, 0] := by
  decide

/-- A misaligned address is -EINVAL, and it is decided BEFORE the range
    test: this address is also outside any range. -/
example (eff : SyscallEffect) (m : Model) :
    check_futex_wake_private 1 eff m = check_ret_only eff (errno_ret EINVAL) m [] := by
  simp only [check_futex_wake_private]
  rw [ite_eq_left (by decide)]

/-- An aligned address past the range is -EFAULT. -/
example (eff : SyscallEffect) (m : Model) :
    check_futex_wake_private (BitVec.ofInt 64 0x800000000000) eff m
      = check_ret_only eff (errno_ret EFAULT) m [] := by
  simp only [check_futex_wake_private]
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]

/-- An in-range address with NOTHING mapped at it still wakes: the private
    path never resolves the page, so the answer is 0 and not -EFAULT. -/
example (eff : SyscallEffect) (m : Model) :
    check_futex_wake_private (BitVec.ofInt 64 0x2000) eff m
      = check_ret_only eff (BitVec.ofInt 64 0) m [] := by
  simp only [check_futex_wake_private]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

/-- The wait arm's -EAGAIN carries the four-byte ledger. -/
example (eff : SyscallEffect) (m : Model) :
    check_futex_wait_private port_input 0 2 eff m
      = check_ret_only_copyins [(0, FUTEX_WORD_SIZE_nat)] eff
          (errno_ret EAGAIN) m [] := by
  simp only [check_futex_wait_private, port_read]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

/-- A word that DOES hold `val` declines: the caller would block. -/
example (eff : SyscallEffect) (m : Model) :
    check_futex_wait_private port_input 0 1 eff m = .CheckUnmodeled := by
  simp only [check_futex_wait_private, port_read]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]

/-- A wake with a non-NULL timeout answers 0: the third argument is dead
    for a wake. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_futex i 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0 7 eff m
      = check_ret_only eff (BitVec.ofInt 64 0) m [] := by
  simp only [check_futex, check_futex_wake_private]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]

/-- A WAIT with a non-NULL timeout declines before it looks at the word. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_futex i 0 (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 2 0x1000 eff m
      = .CheckUnmodeled := by
  simp only [check_futex]
  rw [ite_eq_right (by decide), ite_eq_left (by decide), ite_eq_left (by decide)]

/-- Every other op word declines — including the SHARED spellings, whose
    key can be one another process holds. -/
example (i : SyscallInput) (eff : SyscallEffect) (m : Model) :
    check_futex i 0 (BitVec.ofInt 64 FUTEX_WAKE) 0 0 eff m = .CheckUnmodeled := by
  simp only [check_futex]
  rw [ite_eq_right (by decide), ite_eq_right (by decide)]

/-- The ledger predicate, applied: an answered private wake with a NULL
    timeout reads nothing, and the theorem agrees. -/
example (i : SyscallInput) (m : Model) :
    (mkEffect (BitVec.ofInt 64 0) [] [] : SyscallEffect).eff_copyins
      = (if futex_wait_reads_b 0 (BitVec.ofInt 64 FUTEX_WAKE_PRIVATE) 0
         then [(0, FUTEX_WORD_SIZE_nat)] else []) := by
  have h := futex_copyins_exact (uaddr := 0) (op := BitVec.ofInt 64 FUTEX_WAKE_PRIVATE)
    (val := 0) (utime := 0) i m (mkEffect (BitVec.ofInt 64 0) [] []) m []
    (futex_spec_wake 0 _ 0 0 i m (by decide) (by decide) (by decide))
  simpa using h

/-- …and a private wait with a NULL timeout on an aligned, in-range
    address reads, whatever the memory holds: the predicate is on the
    arguments alone. -/
example : futex_wait_reads_b (BitVec.ofInt 64 0x2000)
    (BitVec.ofInt 64 FUTEX_WAIT_PRIVATE) 0 = true := by
  decide

end LinuxSem.Checks.Sys.Kernel.Futex.Syscalls
